 (*specs/proofs of /root/fv-workspace/monad/proofs/demo2.cpp *)

Require Import monad.tutorials.demo3.
Require Import bedrock.auto.invariants.
Require Import bedrock.auto.cpp.proof.
Require Import bedrock.auto.cpp.tactics4.
Require Import monad.proofs.misc.
Require Import monad.tutorials.demomisc.
Require Import monad.tutorials.atomic_specs.
Require Import monad.tutorials.demoprf.
Require Import monad.proofs.stsg.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Z.
Import cQp_compat.
Import Verbose.
Import linearity.
  Ltac slauto := (slautot ltac:(autorewrite with syntactic; try solveRefereceTo)); try iPureIntro.

  (* TODO: upstream? *)
    Opaque coPset_difference.

(* Agnostic to how many producers/consumers there are *)
Module QueueModel.
  Section Cap. Variable (capacity: nat).

  Record State :=
    {
      produced: list Z;
      consumedPrefixLen: nat;
    }.

  Definition full (s: State) : Prop :=
    length (produced s) - consumedPrefixLen s < capacity.
  
  Definition empty (s: State) : Prop :=
    length (produced s) = consumedPrefixLen s.

  Inductive step : State -> State -> Prop :=
  | produce: forall (newItem:Z) (prev: State),
      (¬ full prev) -> step prev
                            {| produced := newItem::(produced prev);
                                    consumedPrefixLen := consumedPrefixLen prev |}
  | consume: forall (newItem:Z) (prev: State),
      (¬ empty prev) -> step prev
                             {| produced := produced prev;
                                 consumedPrefixLen := 1+ consumedPrefixLen prev |}.
    
(* when we do MPSC queues, the simulation will become the main spec *)

  Definition sts : stsT :=
    @stsg.Sts State Empty_set 
      (fun keys_owned_by_transition_initiator init_state final_state =>
         step init_state final_state).

  
  End Cap.
End QueueModel.
      

Section with_Sigma.
  Context `{Sigma:cpp_logic}  {CU: genv}.
  Context  {MODd : demo3.module ⊧ CU}.

  Context (capacity:nat) `{sss: !stsG (QueueModel.sts capacity)}.
  Notation qsts := (QueueModel.sts capacity).
  Notation "a |--> r" := (own a r) (at level 80).
  Definition auth (g:gname) (s: sts.state qsts): mpred:=
    g |--> sts_auth s ∅.
  
  Definition ProducerR (l: list Z) : Rep. Admitted.
  Definition ConsumerR (l: list Z) : Rep. Admitted.
  
  cpp.spec "SPSCQueue::push(int)" as pushq with (fun (this:ptr)=>
    \arg{value} "value" (Vint value)
    \pre{prodHistory: list Z} this |-> ProducerR prodHistory
    \post{retb:bool} [Vbool retb]
                  if retb
                  then this |-> ProducerR (value::prodHistory)
                  else this |-> ProducerR prodHistory).
  
  cpp.spec "SPSCQueue::pop(int&)" as popq with (fun (this:ptr)=>
    \arg{valuep} "value" (Vptr valuep)
    \pre{consumeHistory: list Z} this |-> ConsumerR consumeHistory
    \pre valuep |-> anyR "int" 1  
    \post Exists value:Z, valuep |-> primR "int" 1 value ** this |-> ConsumerR (value::consumeHistory)
    ).

  (* transfer extra resource. only cover this if we have time *)
  Definition ProducerRg (l: list Z) (R: Z -> list Z-> mpred) : Rep. Admitted.
  Definition ConsumerRg (l: list Z) (R: Z -> list Z-> mpred) : Rep. Admitted.
  
  cpp.spec "SPSCQueue::push(int)" as pushqg with (fun (this:ptr)=>
    \arg{value} "value" (Vint value)
    \pre{(prodHistory: list Z) (R: Z -> list Z-> mpred)} this |-> ProducerRg prodHistory R
    \pre R value prodHistory
    \post{retb:bool} [Vbool retb]
                  if retb
                  then this |-> ProducerRg (value::prodHistory) R
                  else R value prodHistory ** this |-> ProducerRg prodHistory R).
  Locate sts.
  cpp.spec "SPSCQueue::pop(int&)" as popqg with (fun (this:ptr)=>
    \arg{valuep} "value" (Vptr valuep)
    \pre{(consumeHistory: list Z) (R: Z -> list Z-> mpred)} this |-> ConsumerRg consumeHistory R
    \pre valuep |-> anyR "int" 1  
    \post Exists value:Z,
         R value consumeHistory
         ** valuep |-> primR "int" 1 value
         ** this |-> ConsumerRg (value::consumeHistory) R
    ).

  (* roles of logical locations:
     - track info not in c++ variables, e.g. progress towards an op (typicall more abstract that program counter)
     - expose a higher-level state to the client
     - enforce complex protocols.

so far in spscqueue, consumer has authorirative ownership of head and frag of tail , producer has authorirative over tail, fragmentary over head. same as last time.
we can control what current values are.
we cannot control how the values are updated: e.g numConsumed can only be incremented by the consumer  
   *)
  Record qlptr :=
    {
      invId : gname;
      producedListLoc: gname;
      numConsumedLoc: gname;
      inProduceLoc: gname;
      inConsumeLoc: gname;
    }.
  Notation logicalR := (to_frac_ag).
  Context {hsssb: fracG bool _}.
  Context {hssslz: fracG (list Z) _}.
  Context {hsssln: fracG N _}.

  Definition boolZ (b: bool) : Z := if b then 1 else 0.

  Notation cap := (256).
  Definition SPSCQueueInv1 (cid: qlptr) : Rep :=
    Exists (producedL: list Z) (numConsumed: N) (inProduce inConsume: bool),
      let numProduced : N  := lengthN producedL in
      let numConsumedAll: Z := (numConsumed + boolZ inConsume) in
      let numProducedAll: Z := (numProduced + boolZ inProduce) in
      let numConsumable : Z := (lengthN producedL - numConsumed) in
      let numFreeSlotsInCinv: Z := (cap- numConsumable - boolZ inProduce) in
      let currItems := dropN (Z.to_N numConsumedAll) producedL in
      pureR (inProduceLoc cid |--> logicalR (1/2) inProduce)
         (* actual capacity is 1 less than cap (the size of the array) because we need to distinguish empty and full *)
      ** [| numConsumedAll <= numProduced /\ numProducedAll - numConsumed <= cap - 1 |]
      ** pureR (inConsumeLoc cid |--> logicalR (1/2) inConsume)
      ** pureR (producedListLoc cid |--> logicalR (1/2) producedL)
      ** pureR (numConsumedLoc cid |--> logicalR (1/2) numConsumed)
      ** _field "SPSCQueue::head_" |-> atomicR uint 1 (numConsumed `mod` cap)
      ** _field "SPSCQueue::tail_" |-> atomicR uint 1 (numProduced `mod` cap)
      **
      (* ownership of active cells *)
      ([∗ list] i↦  item ∈ currItems,  _field "SPSCQueue::buffer_".["int" ! ((numConsumedAll + i) `mod` cap)] |-> primR "int"  1 (Vint item))
      (* ownership of inactive cells *)
      ** ([∗ list] i↦  _ ∈ (seqN 0 (Z.to_N numFreeSlotsInCinv)),  _field "SPSCQueue::buffer_".["int" ! (numProducedAll + i) `mod` cap ] |-> anyR "int" 1)
      ** _field "SPSCQueue::buffer_".[ "int" ! cap ] |-> validR .
   
  Notation cinvr invId q R:=
    (as_Rep (fun this:ptr => cinv invId q (this |-> R))).

  
  Definition ProducerRw (cid: qlptr) (produced: list Z): Rep :=
    cinvr (invId cid) (1/2) (SPSCQueueInv1 cid)
      ** pureR (inProduceLoc cid |--> logicalR (1/2) false)
      ** pureR (producedListLoc cid |--> logicalR (1/2) produced).
  
  Definition ConsumerRw (cid: qlptr) (numConsumed:N): Rep :=
    cinvr (invId cid) (1/2) (SPSCQueueInv1 cid)
      ** pureR (inConsumeLoc cid |--> logicalR (1/2) false)
      ** pureR (numConsumedLoc cid |--> logicalR (1/2) numConsumed).
  
  cpp.spec "SPSCQueue::push(int)" as pushqw with (fun (this:ptr)=>
    \arg{value} "value" (Vint value)
    \pre{(lpp: qlptr) (produced: list Z)} this |-> ProducerRw lpp produced
    \post{retb:bool} [Vbool retb]
           if retb
           then this |-> ProducerRw lpp (produced++[value])
           else this |-> ProducerRw lpp produced).
  
  cpp.spec "SPSCQueue::pop(int&)" as popqw with (fun (this:ptr)=>
    \arg{valuep} "value" (Vptr valuep)
    \pre{(lpp: qlptr) (numConsumed: N)} this |-> ConsumerRw lpp numConsumed
    \pre valuep |-> anyR "int" 1
    \post{retb:bool} [Vbool retb]
        if retb
        then this |-> ConsumerRw lpp (1+numConsumed)
             ** Exists popv:Z, valuep |-> primR "int" 1 popv
        else valuep |-> anyR "int" 1 ** this |-> ConsumerRw lpp numConsumed).

  Opaque atomicR.
  Opaque Nat.modulo.

  Section Hints.
    Context {T:Type} {ff : fracG T _}. (* {fff: fracG T   _Σ} *)
  (* Move and generalize colocate with [fgptsto_update]*)
  Lemma half_combine  (m1 m2:T) g q:
((g |--> logicalR (q / 2) m1):mpred) ∗ g |--> logicalR (q / 2) m2 ⊢ (g |--> logicalR q m1) ∗ [| m2 = m1 |].    
  Proof.
  Admitted.
  Lemma half_split  (m:T) g q:
    g |--> logicalR q m |-- ((g |--> logicalR (q / 2) m):mpred) ** ((g |--> logicalR (q / 2) m)).
  Proof.
  Admitted.
  Lemma logicalR_update (l : gname) (v' v : T) : l |--> logicalR 1 v |-- |==> l |--> logicalR 1 v'.
  Proof. apply @own_update; try exact _. apply cmra_update_exclusive. done. Qed.
  
  #[global] Instance learn_logicalR (l : gname) (v1 v2 : T) q q1 :
    Learnable (l |--> logicalR q1 v1)  (l |--> logicalR q v2) [v1=v2] := ltac:(solve_learnable).

  Definition  learn_logicalR_unsafe (l : gname) (v1 v2 : T) q1 q2 :
    Learnable (l |--> logicalR q1 v1)  (l |--> logicalR q2 v2) [v1=v2; q1=q2] := ltac:(solve_learnable).
  

  Definition ownhalf_combineF := [FWD->] half_combine.
  Definition ownhalf_splitC := [CANCEL] half_split.
  End Hints.
  Hint Resolve ownhalf_combineF : br_opacity.
  Hint Resolve ownhalf_splitC : br_opacity.
    Existing Instance learn_atomic_val_UNSAFE.
    Definition qFull (producedL: list Z) (numConsumed: N) :=
      lengthN producedL = Z.to_N (numConsumed + (cap-1)).

      Import ZifyClasses.
      Set Nested Proofs Allowed.
Lemma zifyModNat: ∀ x y : nat, True →  y ≠ 0%nat → (x `mod` y < y)%nat.
Proof using.
  intros.
  apply Nat.mod_upper_bound.
  assumption.
Qed.
        
#[global]
Instance SatMod : Saturate Nat.modulo :=
  {|
    PArg1 := fun x => True;
    PArg2 := fun y => y ≠ 0%nat;
    PRes  := fun _ y r => (r <y)%nat;
    SatOk := zifyModNat
  |}.

Lemma add_mod_both_sides (c a b d:Z) :
  0 < d
  -> a `mod` d = b `mod` d
  -> (a+c) `mod` d = (b+c) `mod` d.
Proof using.
  intros Ha Hb.
  rewrite Zplus_mod.
  symmetry.
  rewrite Zplus_mod.
  rewrite Hb.
  reflexivity.
Qed.
          
Hint Rewrite Z2N.id using lia: syntactic.
Lemma spsc_mod_iff (len numConsumed:N):
  (numConsumed <= len /\ len - numConsumed <= cap - 1) ->
  len = Z.to_N (Z.of_N numConsumed + 255)
  <-> (len `mod` 256 + 1) `mod` 256 = Z.of_N numConsumed `mod` 256.
Proof using.
  intros.
  split; intros Hyp.
  -  subst. autorewrite with syntactic. Arith.arith_solve.
  -   apply (add_mod_both_sides 255) in Hyp; try lia.
      replace (len `mod` 256 + 1 + 255) with (len `mod` 256 + 256) in Hyp by lia.
      revert Hyp.
      mod_simpl_aux faster_lia.
      intros Hyp.
      apply modulo.zmod_inj in Hyp; try nia.
Qed.
Lemma spsc_mod_iff1 (len numConsumed:N) bl bc:
  (numConsumed + boolZ bc <= len /\ len + boolZ bl  - numConsumed <= cap - 1) ->
  len = Z.to_N (Z.of_N numConsumed + 255)
  <-> (len `mod` 256 + 1) `mod` 256 = Z.of_N numConsumed `mod` 256.
Proof using.
  intros.
  apply spsc_mod_iff.
  destruct bc, bl;  simpl in *; try nia.
Qed.

Lemma seqN_shift: ∀ start len : N, map N.succ (seqN start len) = seqN (N.succ start) len.
Proof using.
  intros.
  unfold seqN.
  rewrite map_fmap.
  rewrite N2Nat.inj_succ.
  rewrite <- seq_shift.
  rewrite map_fmap.
  repeat rewrite <- list_fmap_compose.
  unfold compose.
  f_equiv.
  hnf. intros. lia.
Qed.

  Lemma pushqprf: denoteModule module
                    ** uint_store_spec
                    ** uint_load_spec
                    |-- pushqw.
  Proof using MODd with (fold cQpc; normalize_ptrs).
    verify_spec'.
    slauto.
    unfold ProducerRw. go.
    unfold SPSCQueueInv1. go.
    callAtomicCommitCinv.
    ren_hyp producedL (list Z).
    ren_hyp numConsumed N.
    normalize_ptrs. go.
    pose proof (spsc_mod_iff1 (lengthN producedL) numConsumed false v ltac:(auto)).
    destruct (decide (lengthZ producedL = (numConsumed + (cap-1)))).
    { (* overflow . TODO: move the load of tail up so that both cases can share more proof *)
      closeCinvqs.
      go.
      ego...
      go.
      iModIntro.
      go.
      callAtomicCommitCinv.
      go.
      closeCinvqs.
      go.
      iModIntro.
      name_locals.
      slauto.
    }
    {
      go.
      wapply (logicalR_update (inProduceLoc lpp) true). eagerUnifyU. go.
      closeCinvqs.
      go...
      go.
      IPM.perm_left ltac:(fun L n =>
        match L with
        | context [seqN 0 ?l] => 
            IPM.perm_right ltac:(fun R n =>
                 match R with
                 | context [seqN 0 ?r] => assert (l=1+r)%N as Heq
                                                 by Arith.arith_solve
                 end
                 )
        end).
      rewrite Heq.
      rewrite N.add_1_l.
      rewrite seqN_S_start.
      go.
      closed.norm closed.numeric_types.
      rewrite <- (seqN_shift 0).
      work.
      rewrite big_opL_map.
      icancel (cancel_at this).
      {
        do 7 (f_equiv; intros; hnf).
        lia.
      }
      Arguments cinvq {_} {_} {_} {_} {_} {_} {_}.
      go...
      autorewrite with syntactic.
      iModIntro.
      go.
      callAtomicCommitCinv.
      go.
      closeCinvqs.
      go.
      ego.
      iModIntro.
      slauto.
      callAtomicCommitCinv.
      go.
      wapply (logicalR_update (inProduceLoc lpp) false). eagerUnifyU. go.
      wapply (logicalR_update (producedListLoc lpp) (_v_3++[value])). eagerUnifyU. go.
      closeCinvqs.
      go.
      Hint Rewrite @lengthN_app @lengthN_one: syntactic.
      slauto.
      simpl.
      rename _v_4 into numConsumedAtStore.
      rename _v_3 into producedL.
      rename numConsumed into numConsumedHeadAtLoad.
      go.
      Hint Rewrite @dropN_app: syntactic.
      autorewrite with syntactic.
      rewrite big_opL_app. go.
      assert (Z.to_N(numConsumedAtStore + boolZ v) - lengthN producedL = 0)%N as Hle.
      destruct v; simpl; try (Arith.arith_solve; fail).
      rewrite Hle.
      simpl.
      go.
      normalize_ptrs.
      go.
      go.
      autorewrite with syntactic.
      rewrite length_dropN.
      autorewrite with syntactic.
      assert ((numConsumedAtStore + boolZ v +
                                                      (length producedL -
                                                         N.to_nat (Z.to_N (numConsumedAtStore + boolZ v)))%nat) = lengthZ producedL) as Hew by ( unfold lengthN in *; simpl in *;destruct v; try Arith.arith_solve).
      rewrite Hew. go.

      icancel (cancel_at this);[
          (repeat (try f_equiv; intros; hnf; try lia)) |].
      go.
      iModIntro.
      go.
    }
  Qed.
  Set Default Goal Selector "!".
Lemma skipnaddle {T} (def: T) (l: list T) (a:nat):
  (1+a <= length l) -> skipn a l = (nth a l def)::(skipn (1+a) l).
Proof using.
  intros Hl.
  rewrite <- skipn_skipn.
  rewrite <- tail_drop.
  erewrite -> drop_nth_head; try reflexivity.
  apply nth_error_nth'.
  lia.
Qed.
Lemma dropNaddle {T} (def: T) (l: list T) (i:N):
  (1+i <= lengthN l) -> dropN i l = (nth (N.to_nat i) l def)::(dropN (i+1)%N l).
Proof using.
  unfold dropN.
  intros.
  unfold lengthN in *.
  erewrite skipnaddle by lia.
  do 2 f_equal.
  lia.
Qed.
Lemma big_sepL_monoeq :
∀ {PROP : bi} {A : Type} (Φ Ψ : nat → A → bi_car PROP) (l lb : list A) (p: l=lb),
  (∀ (k : nat) (y : A), l !! k = Some y → Φ k y ⊢ Ψ k y) → ([∗ list] k↦y ∈ lb, Φ k y) ⊢ [∗ list] k↦y ∈ lb, Ψ k y.
Proof using. intros. subst. apply big_sepL_mono. auto. Qed.

Definition xxx:= [CANCEL] @big_sepL_monoeq.
Lemma seqN_app (len1 len2 start : N): seqN start (len1 + len2) = seqN start len1 ++ seqN (start + len1)%N len2.
Proof using.
  unfold seqN.
  repeat rewrite N2Nat.inj_add.
  rewrite seq_app.
  rewrite fmap_app.
  reflexivity.
Qed.
Lemma add_mod_lhsc (a b d:Z) :
  0 < d
  -> (a+d) `mod` d = b `mod` d
  -> (a) `mod` d = (b) `mod` d.
Proof using.
  intros Ha Hb.
  rewrite <- Hb.
  Arith.arith_solve.
Qed.
         Hint Rewrite length_seq: syntactic.

  
  Lemma popqprf: denoteModule module
                    ** uint_store_spec
                    ** uint_load_spec
                    |-- popqw.
  Proof using MODd with (fold cQpc; normalize_ptrs).
    verify_spec'.
    slauto.
    unfold ConsumerRw. go.
    unfold SPSCQueueInv1. go.
    callAtomicCommitCinv.
    ren_hyp producedL (list Z).
    ren_hyp numConsumed N.
    progress normalize_ptrs. go.
    destruct (decide (lengthZ producedL = (numConsumed))).
    { (* queue is empty: exact same proof as before  *)
      closeCinvqs.
      go.
      ego...
      go.
      iModIntro.
      go.
      callAtomicCommitCinv.
      go.
      closeCinvqs.
      go.
      iModIntro.
      name_locals.
      slauto.
    }
    {
      go.
      wapply (logicalR_update (inConsumeLoc lpp) true). eagerUnifyU. go.
      closeCinvqs.
      go...
      go.
      autorewrite with syntactic.
      rewrite Z2N.inj_add; try nia.
      simpl.
      autorewrite with syntactic.
      simpl in *.
      assert (numConsumed + 1 <= lengthN producedL) by lia.
      rewrite (dropNaddle 0); try nia.
      simpl. go.
      icancel (cancel_at this).
      {
        do 7 (f_equiv; intros; hnf).
        lia.
      }
      go...
      progress autorewrite with syntactic.
      iModIntro.
      go.
      callAtomicCommitCinv.
      go.
      closeCinvqs.
      go.
      iModIntro.
      slauto.
      wp_if.
      1:{ intros. apply False_rect.
          apply n.
          apply modulo.zmod_inj in p; try nia.
          destruct _v_1; simpl in *; try nia.
      }
      slauto.
      callAtomicCommitCinv.
      go.
      wapply (logicalR_update (inConsumeLoc lpp) false). eagerUnifyU. go.
      wapply (logicalR_update (numConsumedLoc lpp) (1+_v_4)%N). eagerUnifyC. go.
      closeCinvqs.
      go.
      slauto.
      simpl.
      normalize_ptrs.
      replace ((Z.to_N (Z.of_N _v_4 + 1))) with (1 + _v_4)%N by lia.
      repeat rewrite _at_big_sepL.
      icancel (@big_sepL_mono).
      {
        repeat (f_equiv; intros; hnf; try lia).
      }
      go.
      IPM.perm_left ltac:(fun L n =>
        match L with
        | context [seqN 0 ?l] => 
            IPM.perm_right ltac:(fun R n =>
                 match R with
                 | context [seqN 0 ?r] => assert (l+1=r)%N as Heq by lia
                 end
                 )
        end).
      {
        rewrite <- Heq.
        simpl.
        go.
        autorewrite with syntactic.
         rewrite seqN_app.
         go.
         rewrite big_opL_app. go.
         unfold seqN. simpl.
         unfold fmap.
         simpl.
         unfold lengthN in *.
         autorewrite with syntactic.
      IPM.perm_left_spatial ltac:(fun L n =>
        match L with
        | context [.["int"! ?li]] => 
            IPM.perm_right ltac:(fun R n =>
                 match R with
                 | context [_ .["int"! ?ri] |-> anyR _ _] => assert (li=ri) as Heqq
                 end
                 )
        end);
        [| repeat rewrite <- Heqq; slauto; iModIntro; go].
         apply add_mod_lhsc; try lia.
         f_equiv.
         lia.
      }
    }
   Qed.
  
End with_Sigma.
(* TODO:
add P value to the spsc specs
do bitset.
maybe do specs invariant of MPSCQueue
*)

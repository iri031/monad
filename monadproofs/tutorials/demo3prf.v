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
Notation stable := valid. 
Import linearity.
Ltac slauto := (slautot ltac:(autorewrite with syntactic; try solveRefereceTo)); try iPureIntro.
Hint Rewrite @lengthN_app @lengthN_one: syntactic.
Hint Rewrite @dropN_app: syntactic.
Notation bufsize := 256.
Opaque atomicR.
Opaque Nat.modulo.
Existing Instance learn_atomic_val_UNSAFE.


(* TODO: upstream? *)
Opaque coPset_difference.

(* Agnostic to how many producers/consumers there are *)
Module QueueModel.
  Import sts.
  Notation capacity := 255.
  Record State :=
    {
      produced: list Z;
      numConsumed: N;
    }.

  Definition full (s: State) : Prop :=
    lengthZ (produced s) - numConsumed s = capacity.
  
  Definition empty (s: State) : Prop :=
    lengthZ (produced s) = numConsumed s.

  Inductive Token := Producer | Consumer.
  
  Inductive step : State -> Token -> State -> Prop :=
  | produce: forall (newItem:Z) (prev: State),
      (¬ full prev) -> step
                         prev
                         Producer
                         {| produced := (produced prev) ++ [newItem];
                           numConsumed := numConsumed prev |}
  | consume: forall (prev: State),
      (¬ empty prev) -> step
                          prev
                          Consumer
                          {| produced := produced prev;
                            numConsumed := 1+ numConsumed prev |}.
    
(* when we do MPSC queues, the simulation will become the main spec *)

  Definition spsc : stsT :=
    @stsg.Sts State Token
      (fun tokens_owned init_state final_state =>
         ∃ role, role ∈ tokens_owned /\  step init_state role final_state).

  Lemma closed_if (S: states spsc) (mytoks: tokens spsc):
    (∀ (s1 s2 : State) otherTok, otherTok ∉ mytoks → s1 ∈ S → step s1 otherTok s2 ->  s2 ∈ S)
    -> closed S mytoks.
  Proof.
    clear.
    intros Hp.
    apply closed_iff.
    intros.
    hnf in H1.
    forward_reason.
    hnf in H1l.
    forward_reason.
    specialize (Hp s1 s2 role ltac:(set_solver) ltac:(set_solver) ltac:(auto)).
    auto.
  Qed.

End QueueModel.
      

Module t1.
Section with_Sigma.
  Context `{Sigma:cpp_logic}  {CU: genv}.
  Context  {MODd : demo3.module ⊧ CU}.
  Context {hsssb: fracG bool _}.
  Context {hssslz: fracG (list Z) _}.
  Context {hsssln: fracG N _}.
  Context `{sss: !stsG (QueueModel.spsc)}.

  (* todo: upstream *)
  Notation cinvr invId q R:=
    (as_Rep (fun this:ptr => cinv invId q (this |-> R))).

  
  (* roles of logical locations:
     - track info not in c++ variables, e.g. progress towards an op (typicall more abstract that program counter)
     - expose a higher-level state to the client
     - enforce complex protocols.

so far in spscqueue, consumer has authoritative ownership of head and frag of tail , producer has authorirative over tail, fragmentary over head. same as last time.
we can control what current values are.
we cannot control how the values are updated: e.g numConsumed can only be incremented by the consumer


   *)
  Record spscid :=
    {
      invId : gname;
      producedListLoc: gname;
      numConsumedLoc: gname;
      inProduceLoc: gname;
      inConsumeLoc: gname;
    }.

  Definition boolZ (b: bool) : Z := if b then 1 else 0.
  
Definition SPSCInv (cid: spscid) (P: Z -> mpred) : Rep :=
  Exists (producedL: list Z) (numConsumed: N) (inProduce inConsume: bool),
    let numProduced : N  := lengthN producedL in
    let numConsumedAll: Z := (numConsumed + boolZ inConsume) in
    let numProducedAll: Z := (numProduced + boolZ inProduce) in
    let numConsumable : Z := (lengthN producedL - numConsumed) in
    let numFreeSlotsInCinv: Z := (bufsize- numConsumable - boolZ inProduce) in
    let currItems := dropN (Z.to_N numConsumedAll) producedL in
    pureR (inProduceLoc cid |--> logicalR (1/2) inProduce)
       (* actual capacity is 1 less than bufsize (the size of the array) because we need to distinguish empty and full *)
    ** [| numConsumedAll <= numProduced /\ numProducedAll - numConsumed <= bufsize - 1 |]
    ** pureR (inConsumeLoc cid |--> logicalR (1/2) inConsume)
    ** pureR (producedListLoc cid |--> logicalR (1/2) producedL)
    ** pureR (numConsumedLoc cid |--> logicalR (1/2) numConsumed)
    ** _field "SPSCQueue::head_" |-> atomicR uint 1 (numConsumed `mod` bufsize)
    ** _field "SPSCQueue::tail_" |-> atomicR uint 1 (numProduced `mod` bufsize)
    **
    (* ownership of active cells *)
    ([∗ list] i↦  item ∈ currItems,
      pureR (P item) **
      _field "SPSCQueue::buffer_".["int" ! ((numConsumedAll + i) `mod` bufsize)] |-> primR "int"  1 (Vint item))
    (* ownership of inactive cells *)
    ** ([∗ list] i↦  _ ∈ (seqN 0 (Z.to_N numFreeSlotsInCinv)),  _field "SPSCQueue::buffer_".["int" ! (numProducedAll + i) `mod` bufsize ] |-> anyR "int" 1)
    ** _field "SPSCQueue::buffer_".[ "int" ! bufsize ] |-> validR .
 
Definition ProducerR (cid: spscid) (P: Z -> mpred) (produced: list Z): Rep :=
  cinvr (invId cid) (1/2) (SPSCInv cid P)
    ** pureR (inProduceLoc cid |--> logicalR (1/2) false)
    ** pureR (producedListLoc cid |--> logicalR (1/2) produced).

Definition ConsumerR (cid: spscid) (P: Z -> mpred) (numConsumed:N): Rep :=
  cinvr (invId cid) (1/2) (SPSCInv cid P)
    ** pureR (inConsumeLoc cid |--> logicalR (1/2) false)
    ** pureR (numConsumedLoc cid |--> logicalR (1/2) numConsumed).

cpp.spec "SPSCQueue::push(int)" as pushqw with (fun (this:ptr)=>
  \arg{value} "value" (Vint value)
  \pre{(lpp: spscid) (produced: list Z) (P: Z -> mpred)} this |-> ProducerR lpp P produced
  \pre [| Timeless1 P |]
  \pre P value
  \post{retb:bool} [Vbool retb]
         if retb
         then this |-> ProducerR lpp P (produced++[value])
         else this |-> ProducerR lpp P produced ** P value).

cpp.spec "SPSCQueue::pop(int&)" as popqw with (fun (this:ptr)=>
  \arg{valuep} "value" (Vptr valuep)
  \pre{(lpp: spscid) (P: Z -> mpred) (numConsumed: N) } this |-> ConsumerR lpp P numConsumed
  \pre [| Timeless1 P |]
  \pre valuep |-> anyR "int" 1
  \post{retb:bool} [Vbool retb]
      if retb
      then this |-> ConsumerR lpp P (1+numConsumed)
           ** Exists popv:Z, valuep |-> primR "int" 1 popv ** P popv
      else valuep |-> anyR "int" 1 ** this |-> ConsumerR lpp P numConsumed).


Lemma spsc_mod_iff (len numConsumed:N):
  (numConsumed <= len /\ len - numConsumed <= bufsize - 1) ->
  len = Z.to_N (Z.of_N numConsumed + 255)
  <-> (len `mod` 256 + 1) `mod` 256 = Z.of_N numConsumed `mod` 256.
Proof using.
  clear.
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
  (numConsumed + boolZ bc <= len /\ len + boolZ bl  - numConsumed <= bufsize - 1) ->
  len = Z.to_N (Z.of_N numConsumed + 255)
  <-> (len `mod` 256 + 1) `mod` 256 = Z.of_N numConsumed `mod` 256.
Proof using.
  intros.
  apply spsc_mod_iff.
  destruct bc, bl;  simpl in *; try nia.
Qed.

(*
Hint Resolve ownhalf_combineF : br_opacity.
Hint Resolve ownhalf_splitC : br_opacity.
*)
Lemma pushqprf: denoteModule module
                  ** uint_store_spec
                  ** uint_load_spec
                  |-- pushqw.
Proof using MODd with (fold cQpc; normalize_ptrs).
  verify_spec'.
  slauto.
  unfold ProducerR. go.
  unfold SPSCInv. go.
  callAtomicCommitCinv.
  ren_hyp producedL (list Z).
  ren_hyp numConsumed N.
  normalize_ptrs. go.
  pose proof (spsc_mod_iff1 (lengthN producedL) numConsumed false v ltac:(auto)).
  destruct (decide (lengthZ producedL = (numConsumed + (bufsize-1)))).
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
    slauto.
    simpl.
    rename _v_4 into numConsumedAtStore.
    rename _v_3 into producedL.
    rename numConsumed into numConsumedHeadAtLoad.
    go.
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
Lemma popqprf: denoteModule module
                  ** uint_store_spec
                  ** uint_load_spec
                  |-- popqw.
Proof using MODd with (fold cQpc; normalize_ptrs).
  verify_spec'.
  slauto.
  unfold ConsumerR. go.
  unfold SPSCInv. go.
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
      repeat (f_equiv; intros; hnf; try lia).
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

cpp.spec "SPSCQueue::pop(int&)" as popqw2 with (fun (this:ptr)=>
  \arg{valuep} "value" (Vptr valuep)
  \pre{(lpp: spscid) (P: Z -> mpred) (numConsumed: N) } this |-> ConsumerR lpp P numConsumed
  \pre [| Timeless1 P |]
  \pre valuep |-> anyR "int" 1
  (* despite ∃, the value remains constant during the call unless the callee chooses to change it *)
  \pre ∃ (producedL: list Z),
          (producedListLoc lpp |--> logicalR (1/4) producedL)
          ** [| numConsumed < length producedL  |]
  \post [Vbool true]
        this |-> ConsumerR lpp P (1+numConsumed)
           ** Exists popv:Z, valuep |-> primR "int" 1 popv ** P popv).

(** need a way for even the consumer to make "stable assertions about producedL, the produced list"
     current producedL = [1,2,3] : not stable for consumer
      [1,2,3] is a prefix of current producedL  : stable for everyone
      4< length current producedL  : stable for everyone
      current numConsumed < length of current producedL  : stable for the consumer 
 *)

(** ownership of ghost locations can be custom-defined: CMRA (commutative monoid resource algebra)

Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning
 *)

End with_Sigma.
End t1.
Module stsSpsc.
Section with_Sigma.
  Context `{Sigma:cpp_logic}  {CU: genv}.
  Context  {MODd : demo3.module ⊧ CU}.
  Context {hsssb: fracG bool _}.
  Context `{sss: !stsG (QueueModel.spsc)}.

  (* todo: upstream *)
  Notation cinvr invId q R:=
    (as_Rep (fun this:ptr => cinv invId q (this |-> R))).

Locate "|-->".
Check @own.
Print cmra. (** Commutative Monoid Resource Algebra *)
Check @logicalR. (** iris paper, section 3.2. TODO: copy annottated pdf to mac *)

Print sts.car.

Import sts.
Import QueueModel.
Compute (state spsc).
Notation sts_auth := (@sts_auth spsc).
Notation sts_frag := (@sts_frag spsc).

Lemma closed_if (S: states spsc) (mytoks: tokens spsc):
  (∀ s1 s2 otherTok, otherTok ∉ mytoks → s1 ∈ S → step s1 otherTok s2 ->  s2 ∈ S)
  -> closed S mytoks.
Proof.
  clear.
  intros Hp.
  apply closed_iff.
  intros.
  hnf in H1.
  forward_reason.
  hnf in H1l.
  forward_reason.
  specialize (Hp s1 s2 role ltac:(set_solver) ltac:(set_solver) ltac:(auto)).
  auto.
Qed.
  
(* goes into the invariant. *)
Example e0auth (g:gname) (s: State) (toks: tokens spsc): mpred :=
  g |--> sts_auth s toks. (* says: current state of g is s and ownership of toks *)
Example e0frag (g:gname) (S: propset State) (toks: tokens spsc): mpred :=
  g |--> sts_frag S toks. (* says: current state of g is ∈ S and ownership of toks *)

Example e1 (g:gname) : mpred :=
  g |--> sts_auth {| produced := [4]; numConsumed:= 0 |} ∅.

Check logicalR_update.

Corollary update_lloc_1step (g:gname) (s sf: State) (toks: tokens spsc) tok:
  step s tok sf -> tok ∈ toks ->
    g |--> sts_auth s  toks |-- |==>
    g |--> sts_auth sf toks.
Proof using.
  intros.
  apply update_lloc.
  eapply rtc_l;[| apply rtc_refl].
  hnf. eexists _; split; [| reflexivity].
  hnf. eexists _.
  eauto.
Qed.

Example update_lloc2 (g:gname) :
    g |--> sts_auth {| produced:= [];  numConsumed :=0 |}  {[ Producer ]} |-- |==>
    g |--> sts_auth {| produced:= [9]; numConsumed :=0 |}  {[ Producer ]}.
Proof using.
  apply update_lloc_1step with (tok:=Producer);[| set_solver].
  apply: produce. unfold full. simpl. lia.
Qed.

Example update_lloc_unprovable (g:gname) :
   g |--> sts_auth {| produced:= [9]; numConsumed :=0 |}  ⊤ |-- |==>
   g |--> sts_auth {| produced:= [];  numConsumed :=0 |}  ⊤.
Abort.


(* stable is formalized as closed *)
Lemma closedb lp nc : closed {[ s : state spsc | lp <= lengthN (produced s) /\ nc<= numConsumed s ]} ∅.
Proof using.
  apply closed_if.
  intros ? ? ? Hdis Hin Hstep.
  rewrite -> elem_of_PropSet in *.
  inverts Hstep; simpl; try lia.
  autorewrite with syntactic.
  lia.
Qed.

(** example of frag: *)
Example gen_frag_out_of_thin_air toks g:
  (g |--> sts_auth {| produced:= [9;8]; numConsumed :=1 |} toks) |--
  (g |--> sts_auth {| produced:= [9;8]; numConsumed :=1 |} toks)
  ** (g |--> sts_frag {[ s | 2<= lengthN (produced s) /\ 1<= numConsumed s ]} ∅).
Proof using.
  iIntrosDestructs.
  hideRhs.
  assert (toks ≡ ∅  ∪ toks) as Heq by (set_solver +).
  rewrite Heq.
  rewrite <- sts_op_auth_fragg; [ | try set_solver + | | ].
  {
    unhideAllFromWork.
    rewrite own_op.
    go.
    eagerUnifyU.
    go.
  }
  {
    rewrite -> elem_of_PropSet in *.
    simpl. lia.
  }
  simpl...
  apply closedb.
Qed.

Example dupl_tokenfree_frag g:
  let m:= (g |--> sts_frag {[ s | 2<= lengthN (produced s) /\ 1<= numConsumed s ]} ∅) in
  m |-- m ** m.
Proof using.
  simpl.
  rewrite frag_frag_combine2.
  go.
  iPureIntro.
  apply closedb.
Qed.

(* general form:*)
Check auth_frag_together.
(* -> opening inv, <- closing inv  *)
Check auth_frag_together2.

Example  unstable_prod1: stable (sts_frag
                              {[s: state spsc | produced s =[] ]}
                              {[Consumer]}
                       )
                     -> False.
Proof.
  clear.
  intros Hc.
  hnf in Hc.
  apply proj1 in Hc.
  rewrite <- closed_iff in Hc.
  setoid_rewrite elem_of_PropSet in Hc.
  (* conterexample: *)
  specialize (Hc
                {| produced :=[]; numConsumed := 0 |}
                {| produced :=[2]; numConsumed := 0 |}
                {[Producer ]}
                ltac:(set_solver)
                ltac:(auto)
             ).
  lapply Hc.
  { set_solver. }
  {
    hnf.
    exists {[Producer ]}.
    split; try set_solver.
    hnf.
    exists Producer.
    split; try set_solver.
    apply (produce 2).
    unfold full. simpl in *. lia.
  }
Qed.

Example closed2: closed {[ s : state spsc | produced s =  [9;8] ]} {[ Producer ]}.
Proof using.
  clear.
  apply closed_if.
  intros ? ? ? Hdis Hin Hstep.
  rewrite -> elem_of_PropSet in *.
  inverts Hstep; simpl; try lia; try set_solver.
Qed.
  
(** example of frag: *)
Example gen_frag2 g:
  (g |--> sts_auth {| produced:= [9;8]; numConsumed :=1 |} {[ Producer ]}) |--
  (g |--> sts_auth {| produced:= [9;8]; numConsumed :=1 |} ∅)
  ** (g |--> sts_frag {[ s | produced s =  [9;8] ]} {[ Producer ]}).
Proof using.
  rewrite auth_frag_together2.
  go.
  rewrite -> elem_of_PropSet. simpl.
  iPureIntro.
  split; auto.
  apply closed2.
Qed.
  
Example gen_frag3 g:
  (g |--> sts_auth {| produced:= [9;8]; numConsumed :=1 |} {[ Producer ]}) |--
  (g |--> sts_auth {| produced:= [9;8]; numConsumed :=1 |} ∅)
  ** (g |--> sts_frag {[ s | produced s =  [9;8] ]} {[ Producer ]})
  ** (g |--> sts_frag {[ s | 2<= lengthN (produced s) /\ 1<= numConsumed s ]} ∅).
Proof using.
  rewrite gen_frag2.
  rewrite -> gen_frag_out_of_thin_air at 1.
  go.
Qed.

Example consumer_open_cinv g s:
  (g |--> sts_auth s ∅)
  ** (g |--> sts_frag {[ s | numConsumed s  =  1%N ]} {[ Consumer ]})
  ** (g |--> sts_frag {[ s | 2<= lengthN (produced s) /\ 1<= numConsumed s ]} ∅)
  |--
    (g |--> sts_auth s {[ Consumer ]}) ** [| numConsumed s = 1%N /\ 2<= lengthN (produced s)|].
Proof using.
  rewrite frag_frag_combine.
  go.
  iStopProof.
  rewrite auth_frag_together.
  repeat rewrite right_id.
  repeat rewrite elem_of_intersection.
  repeat rewrite -> elem_of_PropSet. simpl.
  go.
Qed.
(* the consumer can now guarantee success as now it knows there is atleast 1 consumed element *)  

(* update during the store to head in consumer, before closing inv *)
Example consumer_upd g s (learned: numConsumed s = 1%N /\ 2<= length (produced s)):
  (g |--> sts_auth s {[ Consumer ]}) |-- |==>
  (g |--> sts_auth
            {| produced := produced s;
               numConsumed := 2 |}
            {[ Consumer ]}).
Proof using.
  intros.
  apply update_lloc_1step with (tok := Consumer);[|set_solver].
  destruct s; simpl in *.
  forward_reason.
  subst.
  constructor.
  unfold empty.
  unfold lengthN.
  simpl.
  lia.
Qed.

Example gen_frag4 g p (learned: 2<= lengthN p):
(g |--> sts_auth {| produced := p; numConsumed := 2 |} {[ Consumer ]})  |--
(g |--> sts_auth {| produced := p; numConsumed := 2 |} ∅)
  ** (g |--> sts_frag {[ s | numConsumed s =  2%N ]} {[ Consumer ]})
  ** (g |--> sts_frag {[ s | 2<= lengthN (produced s) /\ 2 <= numConsumed s ]} ∅).
Proof using.
  clear MODd.
  rewrite assoc.
  rewrite auth_frag_together2.
  rewrite -> auth_frag_together_dupl2 at 1.
  {
    go.
    eagerUnifyC.
    rewrite -> elem_of_PropSet. simpl.
    iPureIntro.
    split; auto.
    apply closed_if.
    intros.
    rewrite -> elem_of_PropSet in *. simpl in *.
    inverts H1; auto; set_solver.
  }
  {
    rewrite -> elem_of_PropSet. simpl.
    lia.
  }
  {
    apply closedb.
  }
Qed.

Example e2 (g:gname) : mpred :=
  g |--> sts_frag
          {[ s | numConsumed s = 0%N ]} (* produced can be anything *)
          {[ Consumer ]}.

Example eFalse (g:gname) : mpred :=
  g |--> sts_frag {[ s | 4 = length (produced s) ]} ∅.

Example eFalse2 (g:gname) : mpred :=
  g |--> sts_frag {[ s | 4 = length (produced s) ]} {[ Consumer ]}.

Example e4 (g:gname) : mpred :=
  g |--> sts_frag {[ s | 4 = length (produced s) ]} {[ Producer ]}.

Example  stable_prod1:
  stable (sts_frag
           {[s: state spsc | produced s = [] ]}
           {[Producer]}
    ).
Proof.
  clear.
  hnf.
  split;[ | exists {| produced :=[]; numConsumed := 0 |}; set_solver].
  apply closed_if.
  intros ? ? ? Hdisj Hc Hstep.
  rewrite -> elem_of_PropSet in *.
  inverts Hstep...
  (* in cas1: new item added to produced. in case 2, numConsumed incremented *)
  {
    simpl.
    set_solver.
  }
  {
    simpl.
    assumption.
  }
Qed.

(* TODO: move to top *)
Set Nested Proofs Allowed.

Example  stable_prod3:
  stable (sts_frag
           {[s: state spsc | produced s = [] ]}
           {[Producer]}
    ).
Proof.
  clear.
  hnf.
  split;[ | exists {| produced :=[]; numConsumed := 0 |}; set_solver].
  hnf.
  intros ? ? Hc.
  rewrite elem_of_PropSet in Hc.
  intros Hf.
  hnf in Hf.
  forward_reason.
  inverts Hfl.
  inverts H.
  inverts H0.
  forward_reason.
  inverts Hr; try set_solver.
Qed.

Example  stable_prod2:
  stable (sts_frag
           {[s: state spsc | head (produced s) = Some 2  ]}
           {[Consumer]}
    ).
Proof.
  clear.
  hnf.
  split;[ | exists {| produced :=[2]; numConsumed := 0 |}; set_solver].
  hnf.
  intros ? ? Hc.
  rewrite elem_of_PropSet in Hc.
  intros Hf.
  hnf in Hf.
  forward_reason.
  inverts Hfl.
  inverts H.
  inverts H0.
  forward_reason.
  inverts Hr; try set_solver.
  simpl.
  apply elem_of_PropSet.
  simpl...
  erewrite head_app; eauto.
Qed.

Example  stable_prod38:
  stable (sts_frag
           {[s: state spsc | 1<= numConsumed s ]}
           {[Producer]}
    ).
Proof.
  clear.
  hnf.
  split;[ | exists {| produced :=[2]; numConsumed := 1 |}; set_solver].
  hnf.
  intros ? ? Hc.
  rewrite elem_of_PropSet in Hc.
  intros Hf.
  hnf in Hf.
  forward_reason.
  inverts Hfl.
  inverts H.
  inverts H0.
  forward_reason.
  inverts Hr; try set_solver.
  simpl.
  apply elem_of_PropSet.
  simpl...
  lia.
Qed.

(* closed S T := ∀ s∈S, if s can transition to s' using a token NOT in T, s' ∈ S *)
Lemma stable_frag34 (g: gname) (S: sts.states spsc) (T: sts.tokens spsc):
  g |--> sts_frag S T |-- [| sts.closed S T |] ** [| ∃ s, s ∈ S|] ** (g |--> sts_frag S T).
Proof using.
  iIntrosDestructs.
  wapplyObserve observePure.
  eagerUnifyU. go.
  hnf in H.
  forward_reason.
  go.
  iPureIntro.
  eauto.
Qed.

Import t1.
  Record spscid :=
    {
      invId : gname;
      stsLoc: gname;
      inProduceLoc: gname;
      inConsumeLoc: gname;
    }.

  (*
Definition SPSCInv2 (cid: spscid) (P: Z -> mpred) : Rep :=
  Exists (producedL: list Z) (numConsumed: N) (inProduce inConsume: bool),
    let numProduced : N  := lengthN producedL in
    let numConsumedAll: Z := (numConsumed + boolZ inConsume) in
    let numProducedAll: Z := (numProduced + boolZ inProduce) in
    let numConsumable : Z := (lengthN producedL - numConsumed) in
    let numFreeSlotsInCinv: Z := (bufsize- numConsumable - boolZ inProduce) in
    let currItems := dropN (Z.to_N numConsumedAll) producedL in
    pureR (inProduceLoc cid |--> logicalR (1/2) inProduce)
       (* actual capacity is 1 less than bufsize (the size of the array) because we need to distinguish empty and full *)
    ** [| numConsumedAll <= numProduced /\ numProducedAll - numConsumed <= bufsize - 1 |]
    ** pureR (inConsumeLoc cid |--> logicalR (1/2) inConsume)
    ** pureR (producedListLoc cid |--> logicalR (1/2) producedL)
    ** pureR (numConsumedLoc cid |--> logicalR (1/2) numConsumed)
    ** _field "SPSCQueue::head_" |-> atomicR uint 1 (numConsumed `mod` bufsize)
    ** _field "SPSCQueue::tail_" |-> atomicR uint 1 (numProduced `mod` bufsize)
    **
    (* ownership of active cells *)
    ([∗ list] i↦  item ∈ currItems,
      pureR (P item) **
      _field "SPSCQueue::buffer_".["int" ! ((numConsumedAll + i) `mod` bufsize)] |-> primR "int"  1 (Vint item))
    (* ownership of inactive cells *)
    ** ([∗ list] i↦  _ ∈ (seqN 0 (Z.to_N numFreeSlotsInCinv)),  _field "SPSCQueue::buffer_".["int" ! (numProducedAll + i) `mod` bufsize ] |-> anyR "int" 1)
    ** _field "SPSCQueue::buffer_".[ "int" ! bufsize ] |-> validR .
  *)
Definition SPSCInv (cid: spscid) (P: Z -> mpred) : Rep :=
  Exists (s: State) (inProduce inConsume: bool),
    let producedL := produced s in
    let numConsumed := numConsumed s in
    let numProduced : N  := lengthN producedL in
    let numConsumedAll: Z := (numConsumed + boolZ inConsume) in
    let numProducedAll: Z := (numProduced + boolZ inProduce) in
    let numConsumable : Z := (lengthN producedL - numConsumed) in
    let numFreeSlotsInCinv: Z := (bufsize- numConsumable - boolZ inProduce) in
    let currItems := dropN (Z.to_N numConsumedAll) producedL in
    pureR (inProduceLoc cid |--> logicalR (1/2) inProduce)
       (* actual capacity is 1 less than bufsize (the size of the array) because we need to distinguish empty and full *)
    ** [| numConsumedAll <= numProduced /\ numProducedAll - numConsumed <= bufsize - 1 |]
    ** pureR (inConsumeLoc cid |--> logicalR (1/2) inConsume)
    ** pureR (stsLoc cid |--> sts_auth s ∅ )
    ** _field "SPSCQueue::head_" |-> atomicR uint 1 (numConsumed `mod` bufsize)
    ** _field "SPSCQueue::tail_" |-> atomicR uint 1 (numProduced `mod` bufsize)
    **
    (* ownership of active cells *)
    ([∗ list] i↦  item ∈ currItems,
      pureR (P item) **
      _field "SPSCQueue::buffer_".["int" ! ((numConsumedAll + i) `mod` bufsize)] |-> primR "int"  1 (Vint item))
    (* ownership of inactive cells *)
    ** ([∗ list] i↦  _ ∈ (seqN 0 (Z.to_N numFreeSlotsInCinv)),  _field "SPSCQueue::buffer_".["int" ! (numProducedAll + i) `mod` bufsize ] |-> anyR "int" 1)
    ** _field "SPSCQueue::buffer_".[ "int" ! bufsize ] |-> validR.

(*
Definition ProducerR (cid: spscid) (P: Z -> mpred) (produced: list Z): Rep :=
  cinvr (invId cid) (1/2) (SPSCInv cid P)
    ** pureR (inProduceLoc cid |--> logicalR (1/2) false)
    ** pureR (producedListLoc cid |--> logicalR (1/2) produced).
    *)

Definition ProducerR (cid: spscid) (P: Z -> mpred) (producedL: list Z): Rep :=
  cinvr (invId cid) (1/2) (SPSCInv cid P)
    ** pureR (inProduceLoc cid |--> logicalR (1/2) false)
    ** pureR (stsLoc cid |--> sts_frag {[ s | produced s = producedL ]} {[ Producer ]}). (** equiv *)

Definition ConsumerR (cid: spscid) (P: Z -> mpred) (nmConsumed:N): Rep :=
  cinvr (invId cid) (1/2) (SPSCInv cid P)
    ** pureR (inConsumeLoc cid |--> logicalR (1/2) false)
    ** pureR (stsLoc cid |--> sts_frag {[ s | nmConsumed = numConsumed s ]} {[ Consumer ]}).

cpp.spec "SPSCQueue::pop(int&)" as popqw with (fun (this:ptr)=>
  \arg{valuep} "value" (Vptr valuep)
  \pre{(lpp: spscid) (P: Z -> mpred) (numConsumed: N) }
    this |-> ConsumerR lpp P numConsumed
  \pre{numProducedLb: N}
    stsLoc lpp |--> sts_frag {[ s | numProducedLb <= lengthZ (produced s)]} ∅

  \pre [| Timeless1 P |]
  \pre valuep |-> anyR "int" 1
  \post{retb:bool} [Vbool retb]
    [| if decide (numConsumed < numProducedLb) then retb =true else Logic.True |] **
    if retb
    then this |-> ConsumerR lpp P (1+numConsumed)
         ** Exists popv:Z, valuep |-> primR "int" 1 popv ** P popv
    else valuep |-> anyR "int" 1
         ** this |-> ConsumerR lpp P numConsumed).

cpp.spec "SPSCQueue::push(int)" as pushqw with (fun (this:ptr)=>
  \arg{value} "value" (Vint value)
  \pre{(lpp: spscid) (P: Z -> mpred) (produced: list Z)}
            this |-> ProducerR lpp P produced
  \pre{numConsumedLb: N}
    stsLoc lpp |--> sts_frag {[ s | numConsumedLb <= numConsumed s ]} ∅
  \pre [| Timeless1 P |]
  \pre P value
  \post{retb:bool} [Vbool retb]
    [| if decide (lengthN produced < numConsumedLb + capacity) then retb =true else Logic.True |] **
    if retb
    then this |-> ProducerR lpp P (produced++[value])
    else this |-> ProducerR lpp P produced ** P value ).

Definition combineAuthFragFwd:= [FWD->](@auth_frag_together2).
Hint Resolve combineAuthFragFwd: br_opacity.
Hint Rewrite @elem_of_PropSet: iff.

Ltac bwdRev L :=
  wapplyRev L; last (iSplitFrameL; [| iIntrosDestructs; eagerUnifyC ; maximallyInstantiateLhsEvar_nonpers]).

Ltac solveClosed:=
  apply closed_if;
  intros ? ? ? Hdis Hin Hstep;
  rewrite -> elem_of_PropSet in *;
  inverts Hstep; simpl in *; autorewrite with syntactic in *; simpl in *; try lia; try set_solver.

Lemma auth_close_inv_producer (g: gname) s:
  (g |--> sts_auth s {[Producer]})
    |-- ((g |--> sts_frag {[ sf | produced sf = produced s]} {[ Producer ]})
           ** (g |--> sts_frag {[ sf | numConsumed s <= numConsumed sf]} ∅))
        ** (g |--> sts_auth s ∅) .
Proof using.
  clear.
  go.
  bwdRev auth_frag_together2.
  bwdRev auth_frag_together.
  rewrite left_id. go.
  iPureIntro.
  split_and !; try lia; try auto; try set_solver;
  solveClosed.
Qed.

Definition close_invstsg_C := [CANCEL] auth_close_inv_producer. 
Hint Resolve close_invstsg_C: br_opacity.

Lemma spsc_mod_iff1 (s:State) bl bc:
  let len := lengthN (produced s) in
  (numConsumed s + boolZ bc <= len /\ len + boolZ bl  - numConsumed s <= bufsize - 1) ->
  len = Z.to_N (Z.of_N (numConsumed s) + 255)
  <-> (len `mod` 256 + 1) `mod` 256 = Z.of_N (numConsumed s) `mod` 256.
Proof using.
  intros.
  eapply spsc_mod_iff1; eauto.
Qed.
Lemma spsc_mod_iff2 (s:State) bl bc:
  let len := lengthZ (produced s) in
  (numConsumed s + boolZ bc <= len /\ len + boolZ bl  - numConsumed s <= bufsize - 1) ->
  len = (Z.of_N (numConsumed s) + 255)
  <-> (len `mod` 256 + 1) `mod` 256 = Z.of_N (numConsumed s) `mod` 256.
Proof using.
  simpl.
  intros.
  pose proof (spsc_mod_iff1 s bl bc H) as Hx.
  simpl in Hx.
  lia.
Qed.

  Ltac hideEmptyTokenFrag :=
  IPM.perm_left ltac:(fun L n =>
                        match L with
                        | _ |--> sts_frag ?S ∅ => hideFromWork L
                        end
                     ).
#[global] Instance ll g s1 s2 t1 t2: Learnable (g |--> sts_auth s1 t1) (g |--> sts_auth s2 t2) [s1=s2]
                                                   := ltac:(solve_learnable).
      Ltac closedN := closed.norm closed.numeric_types .

Lemma hideWandL (L C: mpred) E:
  (forall  (Lh:mpred), Hide.Hidden (Lh=L) ->  environments.envs_entails E (Lh -* C)) -> environments.envs_entails E (L -* C).
  intros Hl.
  specialize (Hl L).
  apply Hl.
  constructor.
  reflexivity.
Qed.

Lemma hideDuplWandL (L C: mpred) E:
  (L|--L**L) ->
  (forall  (Lh:mpred), Hide.Hidden (Lh=L) ->  environments.envs_entails E (Lh ** L -* C)) -> environments.envs_entails E (L -* C).
  intros Hd Hl.
  specialize (Hl L).
  rewrite Hd.
  apply Hl.
  constructor.
  reflexivity.
Qed.

Lemma forget_empty_frag (g: gname) S:
  (g |--> sts_frag S ∅) |-- (emp:mpred).
Proof using Sigma. apply lose_resources. Qed.

(*
Ltac hideDuplFrag :=
  IPM.perm_left ltac:(fun L n =>
                        match L with
                        | _ |--> sts_frag _ ∅  => iRevert n
                        end
                     );
  apply hideDuplWandL; try apply: frag_dupl.
*)
Arguments cinvq {_} {_} {_} {_} {_} {_} {_}.

Set Default Goal Selector "!".

Lemma pushqprf: denoteModule module
                  ** uint_store_spec
                  ** uint_load_spec
                  |-- pushqw.
Proof using MODd with (fold cQpc; normalize_ptrs).
  verify_spec'.
  slauto.
  unfold ProducerR. go.
  unfold SPSCInv. go.
  go.
  callAtomicCommitCinv.
  go.
  rewrite -> elem_of_PropSet in *.
  normalize_ptrs. go.
  subst.
  ren_hyp slh State.
  simpl in *.
  pose proof (spsc_mod_iff2 slh false v ltac:(simpl; lia)). simpl in *.
  destruct (decide (lengthZ (produced slh) = (numConsumed slh + (bufsize-1)))).
  { (* overflow . TODO: move the load of tail up so that both cases can share more proof *)
    closeCinvqs.
    go.
    ego...
    go.
    iModIntro.
    go.
    callAtomicCommitCinv.
    go.
    rewrite -> elem_of_PropSet in *.
    closeCinvqs.
    go.
    iModIntro.
    closedN.
    name_locals.
    unhideAllFromWork.
    repeat rewrite -> forget_empty_frag.
    repeat  match goal with
            | H: State |- _ => destruct H
            end; simpl in *; forward_reason; subst; simpl in *.
    slauto.
    case_decide; auto;    try Arith.arith_solve.
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
    rewrite -> elem_of_PropSet in *.
    closeCinvqs.
    go.
    ego.
    iModIntro.
      repeat  match goal with
            | H: State |- _ => destruct H
              end; simpl in *; forward_reason; subst; simpl in *.
    slauto.
    callAtomicCommitCinv.
    go.
    rewrite -> elem_of_PropSet in *.
    go.
    wapply (logicalR_update (inProduceLoc lpp) false). eagerUnifyU. go.
    wapply (update_lloc_1step);[ | | eagerUnifyU];
        [reflexivity | apply (produce value) ; unfold full; Arith.arith_solve|].
    go.
    closeCinvqs.
    go.
    slauto.
    simpl.
    ren_hyp stAtStore State.
    destruct stAtStore as  [producedL numConsumedAtStore].
    simpl in *.
    rename numConsumed0 into numConsumedHeadAtLoad.
    go.
    autorewrite with syntactic.
    rewrite big_opL_app. go.
    assert (Z.to_N(numConsumedAtStore + boolZ v) - lengthN producedL = 0)%N as Hle by
      (destruct v; simpl; try (Arith.arith_solve; fail)).
    rewrite Hle.
    simpl.
    go.
    normalize_ptrs.
    go.
    go.
    autorewrite with syntactic.
    rewrite length_dropN.
    autorewrite with syntactic.
    assert ((numConsumedAtStore + boolZ v + (length producedL -
                                                       N.to_nat (Z.to_N (numConsumedAtStore + boolZ v)))%nat) = lengthZ producedL) as Hew by ( unfold lengthN in *; simpl in *;destruct v; try Arith.arith_solve).
    rewrite Hew. go.

    icancel (cancel_at this);[
        (repeat (try f_equiv; intros; hnf; try lia)) |].
    go.
    iModIntro.
    go.
    rewrite forget_empty_frag.
    case_decide; auto.
  }
Qed.

Lemma auth_close_inv_consumer (g: gname) s:
  (g |--> sts_auth s {[Consumer]})
    |-- ((g |--> sts_frag {[ sf | numConsumed s = numConsumed sf]} {[ Consumer ]})
           ** (g |--> sts_frag {[ sf | lengthZ (produced s) <= lengthZ (produced sf)]} ∅))
        ** (g |--> sts_auth s ∅) .
Proof using.
  clear.
  go.
  bwdRev auth_frag_together2.
  bwdRev auth_frag_together.
  rewrite left_id. go.
  iPureIntro.
  split_and !; try lia; try auto; try set_solver;
    solveClosed.
Qed.

Ltac destructStates :=
    repeat  match goal with
            | H: State |- _ => destruct H
      end; simpl in *; forward_reason; subst; simpl in *.

Definition close_invstsgc_C := [CANCEL] auth_close_inv_consumer. 
Hint Resolve close_invstsgc_C: br_opacity.

Ltac callAtomicCommitCinv := misc.callAtomicCommitCinv;  rewrite -> elem_of_PropSet in *.

Lemma popqprf: denoteModule module
                  ** uint_store_spec
                  ** uint_load_spec
                  |-- popqw.
Proof using MODd with (fold cQpc; normalize_ptrs).
  verify_spec'.
  slauto.
  unfold ConsumerR. go.
  unfold SPSCInv. go.
  callAtomicCommitCinv.
  ren_hyp slh State.
  progress normalize_ptrs. go.
  rename numConsumed into nmConsumed.
  destruct (decide (lengthZ (produced slh) = (numConsumed slh))).
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
    destructStates. simpl in *.
    repeat rewrite -> forget_empty_frag.
    slauto.
    case_decide; auto;    try Arith.arith_solve.
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
    destructStates.
    rename numConsumed0 into numConsumed.
    assert (numConsumed + 1 <= lengthN produced0) by lia.
    rewrite (dropNaddle 0); try nia.
    simpl. go.
    icancel (cancel_at this).
    {
      repeat (f_equiv; intros; hnf; try lia).
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
    destructStates.
    callAtomicCommitCinv.
    go.
    ren_hyp stAtStore State.
    destruct stAtStore as  [numConsumed producedAtStore]. simpl in *.
    wapply (logicalR_update (inConsumeLoc lpp) false). eagerUnifyU. go.
    wapply (update_lloc_1step);[ | | eagerUnifyU];
      [reflexivity | apply (consume) ; unfold empty; try Arith.arith_solve|].
    go.
    closeCinvqs.
    go.
    slauto.
    simpl.
    normalize_ptrs.
    match goal with
      [ |- context[((Z.to_N (Z.of_N ?v + 1)))]] =>
        replace ((Z.to_N (Z.of_N v + 1))) with (1 + v)%N by lia
    end.
(*    replace ((Z.to_N (Z.of_N _v_4 + 1))) with (1 + _v_4)%N by lia. *)
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
    repeat rewrite forget_empty_frag.
    IPM.perm_left_spatial ltac:(fun L n =>
      match L with
      | context [.["int"! ?li]] => 
          IPM.perm_right ltac:(fun R n =>
               match R with
               | context [_ .["int"! ?ri] |-> anyR _ _] => assert (li=ri) as Heqq
               end
               )
      end);
      [| repeat rewrite <- Heqq; slauto; iModIntro; case_decide; go].
    apply add_mod_lhsc; try lia.
    f_equiv.
    lia.
  }
 Qed.

Record mpmcid :=
  {
    lockId : gname;
    stateLoc: gname; 
  }.

Definition MPMCLockContent (cid: mpmcid) (P: Z -> mpred) : Rep :=
  Exists (s: State),
    let producedL := produced s in
    let numConsumed := numConsumed s in
    let numProduced : N  := lengthN producedL in
    let numConsumable : Z := (lengthN producedL - numConsumed) in
    let numFreeSlotsInCinv: Z := (bufsize- numConsumable) in
    let currItems := dropN (Z.to_N numConsumed) producedL in
       (* actual capacity is 1 less than bufsize (the size of the array) because we need to distinguish empty and full *)
    [| numConsumed <= numProduced /\ numProduced - numConsumed <= bufsize - 1 |]
    ** pureR (stateLoc cid  |--> sts_auth s ⊤)
    ** _field "SPSCQueue::head_" |-> atomicR uint 1 (numConsumed `mod` bufsize)
    ** _field "SPSCQueue::tail_" |-> atomicR uint 1 (numProduced `mod` bufsize)
    **
    (* ownership of active cells *)
    ([∗ list] i↦  item ∈ currItems,
      pureR (P item) **
      _field "SPSCQueue::buffer_".["int" ! ((numConsumed + i) `mod` bufsize)] |-> primR "int"  1 (Vint item))
    (* ownership of inactive cells *)
    ** ([∗ list] i↦  _ ∈ (seqN 0 (Z.to_N numFreeSlotsInCinv)),  _field "SPSCQueue::buffer_".["int" ! (numProduced + i) `mod` bufsize ] |-> anyR "int" 1)
    ** _field "SPSCQueue::buffer_".[ "int" ! bufsize ] |-> validR.

Require Import monad.tutorials.demo2prf.

(* no separate producerR or consumerR because they have the same limited knowledge/rights *)
Definition mpmcR (cid: mpmcid) (q:Qp) (P: Z -> mpred): Rep :=
  as_Rep( fun (this:ptr) =>
 this |-> _field "lock" |-> LockR q (lockId cid) (this |-> MPMCLockContent cid P)).

(* like blockchain: all the specs says that my transaction was recorded in the history *)
cpp.spec "SPSCQueue::push(int)" as mpmcpush with (fun (this:ptr)=>
  \arg{value} "value" (Vint value)
  \prepost{(lpp: mpmcid) (P: Z -> mpred) (q:Qp)}
    this |-> mpmcR lpp q P
  \pre{producedPrefix: list Z}
    stateLoc lpp |--> sts_frag {[ s | producedPrefix `prefix_of` (produced s) ]} ∅
  \pre [| Timeless1 P |]
  \pre P value
  \post{retb:bool} [Vbool retb]
    if retb
    then Exists (newItems: list Z),
      (stateLoc lpp |--> sts_frag
         {[ s | producedPrefix++newItems++[value] `prefix_of` (produced s) ]} ∅)
    else emp).

cpp.spec "SPSCQueue::pop(int&)" as mpmcpop with (fun (this:ptr)=>
  \arg{valuep} "value" (Vptr valuep)
  \prepost{(lpp: mpmcid) (P: Z -> mpred) (q:Qp)}
    this |-> mpmcR lpp q P
  \pre{numConsumedLb: N}
    stateLoc lpp |--> sts_frag {[ s | numConsumedLb <= numConsumed s]} ∅
  \pre [| Timeless1 P |]
  \pre valuep |-> anyR "int" 1
  \post{retb:bool} [Vbool retb]
    if retb
    then (Exists popv:Z, valuep |-> primR "int" 1 popv ** P popv)
         ** (stateLoc lpp |--> sts_frag {[ s | 1+numConsumedLb <= numConsumed s]} ∅)
    else valuep |-> anyR "int" 1).

(* the above spec is ok for clients who use push/pop in a maximallyy concurrent way and
   follow no additional discipline.
  what if a client wants to use it sequentially? postcond too weak !
  next spec: grants the flexibility:
  - can allow multiple threads to call push/pop concurrently
  - yet, if the client chooses to not race, they get stronger postconditions
  - almost anything in between

Logical atomic triples
 *)
Context {hsssst: fracG State _}.


Definition MPMCLockContentLa (cid: mpmcid) (P: Z -> mpred) : Rep :=
  Exists (s: State),
    let producedL := produced s in
    let numConsumed := numConsumed s in
    let numProduced : N  := lengthN producedL in
    let numConsumable : Z := (lengthN producedL - numConsumed) in
    let numFreeSlotsInCinv: Z := (bufsize- numConsumable) in
    let currItems := dropN (Z.to_N numConsumed) producedL in
    [| numConsumed <= numProduced /\ numProduced - numConsumed <= bufsize - 1 |]
    ** pureR (stateLoc cid  |--> logicalR (1/2) s)
    ** _field "SPSCQueue::head_" |-> atomicR uint 1 (numConsumed `mod` bufsize)
    ** _field "SPSCQueue::tail_" |-> atomicR uint 1 (numProduced `mod` bufsize)
    **
    (* ownership of active cells *)
    ([∗ list] i↦  item ∈ currItems,
      pureR (P item) **
      _field "SPSCQueue::buffer_".["int" ! ((numConsumed + i) `mod` bufsize)] |-> primR "int"  1 (Vint item))
    (* ownership of inactive cells *)
    ** ([∗ list] i↦  _ ∈ (seqN 0 (Z.to_N numFreeSlotsInCinv)),  _field "SPSCQueue::buffer_".["int" ! (numProduced + i) `mod` bufsize ] |-> anyR "int" 1)
    ** _field "SPSCQueue::buffer_".[ "int" ! bufsize ] |-> validR.

Definition mpmcRla (cid: mpmcid) (q:Qp) (P: Z -> mpred): Rep :=
  as_Rep( fun (this:ptr) =>
  this |-> _field "lock" |-> LockR q (lockId cid) (this |-> MPMCLockContentLa cid P)).

Definition pushFinalState (s: State)  (newItem: Z): State :=
  if decide (full s) then s else {| produced := (produced s) ++ [newItem];
                                   numConsumed := numConsumed s |}.
cpp.spec "SPSCQueue::push(int)" as mpmcpushla with (fun (this:ptr)=>
  \arg{value} "value" (Vint value)
  \prepost{(lpp: mpmcid) (P: Z -> mpred) (q:Qp)}
    this |-> mpmcRla lpp q P
  \pre{s: State}
    stateLoc lpp |--> logicalR (1/2) s
  \pre [| Timeless1 P |]
  \pre P value
  \post [Vbool (bool_decide (full s))]
     (stateLoc lpp |--> logicalR (1/2) (pushFinalState s value))).

End with_Sigma.
(* TODO:
proof of pop

animation of resource transfer of SPSCqueue. emphasize how the picture is trickly to encode in logic. ask GPT to draw a circular Q tikz. then nmanually add overlays

just the code (locked imp) and specs of MPMC queue (emphasize specs same):
- frag ∅ spec
- logatom specs (optional, if time permits and people ask questions)
try to compare the spes in terms of strength and usabulity: frag specs force MPMC concurrency.
logatom allows sequential ownership.
illustrate with 2 example wrappers



sequence:
- recap of cinv: cinv box asciiart, Ruth/Rfrag setup, 2 specs of get U, lock spec
- spscqueue code
- spscqueue proof animation
- spsc inv
- spsc proof: new things: ghost update before closing invariant. 1-2 array/mod manip steps
- weakness in pop spec : return false
- iris monoids: paper
- sts setup
- new specs and proofs.
- maybe: MPSCqueue specs  with lock for producer: nice exercise on stability
- review no || execute block proof animation from last time
- ask folks for promise specs
- discuss promise specs
- discuss execute_transaction specs


done
add P value to the spsc specs


broad goals:
- how specs make it precise what kind of concurrency is allowed
- set expectations for concurrent spec
- rich vocabulary for writing concurrent specs 
*)


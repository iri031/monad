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


  (* TODO: upstream? *)
    Opaque coPset_difference.

(* Agnostic to how many producers/consumers there are *)
Module QueueModel.
  Section Cap. Variable (capacity: nat).

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
  | consume: forall (newItem:Z) (prev: State),
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

  End Cap.
End QueueModel.
      

Section with_Sigma.
  Context `{Sigma:cpp_logic}  {CU: genv}.
  Context  {MODd : demo3.module ⊧ CU}.
  Notation cinvr invId q R:=
    (as_Rep (fun this:ptr => cinv invId q (this |-> R))).

  Context `{sss: !stsG (QueueModel.spsc 255)}.
  Notation spsc255 := (QueueModel.spsc 255).
  Definition auth (g:gname) (s: sts.state spsc255): mpred:=
    g |--> sts_auth s ∅.
  Locate only_provable.

  
  (* roles of logical locations:
     - track info not in c++ variables, e.g. progress towards an op (typicall more abstract that program counter)
     - expose a higher-level state to the client
     - enforce complex protocols.

so far in spscqueue, consumer has authoritative ownership of head and frag of tail , producer has authorirative over tail, fragmentary over head. same as last time.
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
  Context {hsssb: fracG bool _}.
  Context {hssslz: fracG (list Z) _}.
  Context {hsssln: fracG N _}.

  Definition boolZ (b: bool) : Z := if b then 1 else 0.

  Notation bufsize := (255).
  Definition SPSCQueueInv1 (cid: qlptr) (P: Z -> mpred) : Rep :=
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
   

  
  Definition ProducerR (cid: qlptr) (P: Z -> mpred) (produced: list Z): Rep :=
    cinvr (invId cid) (1/2) (SPSCQueueInv1 cid P)
      ** pureR (inProduceLoc cid |--> logicalR (1/2) false)
      ** pureR (producedListLoc cid |--> logicalR (1/2) produced).
  
  Definition ConsumerR (cid: qlptr) (P: Z -> mpred) (numConsumed:N): Rep :=
    cinvr (invId cid) (1/2) (SPSCQueueInv1 cid P)
      ** pureR (inConsumeLoc cid |--> logicalR (1/2) false)
      ** pureR (numConsumedLoc cid |--> logicalR (1/2) numConsumed).
  
  cpp.spec "SPSCQueue::push(int)" as pushqw with (fun (this:ptr)=>
    \arg{value} "value" (Vint value)
    \pre{(lpp: qlptr) (produced: list Z) (P: Z -> mpred)} this |-> ProducerR lpp P produced
    \pre [| Timeless1 P |]
    \pre P value
    \post{retb:bool} [Vbool retb]
           if retb
           then this |-> ProducerR lpp P (produced++[value])
           else this |-> ProducerR lpp P produced ** P value).
  
  cpp.spec "SPSCQueue::pop(int&)" as popqw with (fun (this:ptr)=>
    \arg{valuep} "value" (Vptr valuep)
    \pre{(lpp: qlptr) (P: Z -> mpred) (numConsumed: N) } this |-> ConsumerR lpp P numConsumed
    \pre [| Timeless1 P |]
    \pre valuep |-> anyR "int" 1
    \post{retb:bool} [Vbool retb]
        if retb
        then this |-> ConsumerR lpp P (1+numConsumed)
             ** Exists popv:Z, valuep |-> primR "int" 1 popv ** P popv
        else valuep |-> anyR "int" 1 ** this |-> ConsumerR lpp P numConsumed).

  cpp.spec "SPSCQueue::pop(int&)" as popqw2 with (fun (this:ptr)=>
    \arg{valuep} "value" (Vptr valuep)
    \pre{(lpp: qlptr) (P: Z -> mpred) (numConsumed: N) } this |-> ConsumerR lpp P numConsumed
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
  Locate "|-->".
  Check @own.
  Print cmra. (* Commutative Monoid Resource Algebra *)
  Check @logicalR. (* iris paper, section 3.2. TODO: copy annottated pdf to mac *)

  Print sts.car.
  Check sts_frag_valid.

  Import sts.
  Compute (state spsc255).
  Import QueueModel.
  Notation sts_auth := (@sts_auth spsc255).
  Notation sts_frag := (@sts_frag spsc255).

  (* move, generalize over spsc*)
  Lemma closed_iff (S: states spsc255) (mytoks: tokens spsc255):
    (∀ s1 s2 otherToks, mytoks ## otherToks → s1 ∈ S → sts.step otherToks s1 s2 ->  s2 ∈ S)
    <-> closed S mytoks.
  Proof using.
    unfold closed, frame_step.
    intuition; forward_reason; eauto.
  Qed.
  (* move, generalize over spsc*)
  Lemma closed_if (S: states spsc255) (mytoks: tokens spsc255):
    (∀ s1 s2 otherTok, otherTok ∉ mytoks → s1 ∈ S → step 255 s1 otherTok s2 ->  s2 ∈ S)
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
  Example e0auth (g:gname) (s: State) (toks: tokens spsc255): mpred :=
    g |--> sts_auth s toks. (* says: current state of g is s and ownership of toks *)
  Example e0frag (g:gname) (S: propset State) (toks: tokens spsc255): mpred :=
    g |--> sts_frag S toks. (* says: current state of g is ∈ S and ownership of toks *)

  Example e1 (g:gname) : mpred :=
    g |--> sts_auth {| produced := [4]; numConsumed:= 0 |} ∅.

  Check logicalR_update.

  (* move *)
  Notation step := (step 255).
  
  Lemma update_lloc (g:gname) (s sf: State) (toks: tokens spsc255) :
    rtc (sts.step toks) s sf ->
      g |--> sts_auth s  toks |-- |==>
      g |--> sts_auth sf toks.
  Proof using.
    intros.
    forward_reason.
    apply own_update.
    apply sts_update_auth.
    assumption.
  Qed.

  Example update_lloc2 (g:gname) :
      g |--> sts_auth {| produced:= [];  numConsumed :=0 |}  {[ Producer ]} |-- |==>
      g |--> sts_auth {| produced:= [9]; numConsumed :=0 |}  {[ Producer ]}.
  Proof using.
    apply update_lloc.
    eapply rtc_l;[| apply rtc_refl].
    hnf. eexists _; split; [| reflexivity].
    hnf. eexists _.
    split.
    2:{ apply: produce. unfold full. simpl. lia. }
    set_solver.
  Qed.
  
  Example update_lloc_false (g:gname) :
     g |--> sts_auth {| produced:= [9]; numConsumed :=0 |}  ⊤ |-- |==>
     g |--> sts_auth {| produced:= [];  numConsumed :=0 |}  ⊤.
  Abort.
  
  Lemma closede3 : closed {[ s : state spsc255 | 2<= length (produced s) /\ 1<= numConsumed s ]} ∅.
  Proof using.
    apply closed_if.
    intros ? ? ? Hdis Hin Hstep.
    rewrite -> elem_of_PropSet in *.
    inverts Hstep; simpl; try lia.
    autorewrite with syntactic. lia.
  Qed.

  (** example of frag: *)
  Example gen_frag_out_of_thin_air toks g:
    (g |--> sts_auth {| produced:= [9;8]; numConsumed :=1 |} toks) |--
    (g |--> sts_auth {| produced:= [9;8]; numConsumed :=1 |} toks)
    ** (g |--> sts_frag {[ s | 2<= length (produced s) /\ 1<= numConsumed s ]} ∅).
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
    apply closede3.
  Qed.

  (* general form: *)
  Check auth_frag_together.

    
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

  
  

  (* move *)
  Lemma observePure g (a: (stsR spsc255)) : Observe [| ✓ a |] (own g a).
  Proof.  apply observe_intro. exact _. go. Qed.
  
  Lemma stable_frag (g: gname) (S: states spsc255) (T: tokens spsc255):
    (g |--> sts_frag S T)
|-- (g |--> sts_frag S T) ** [|stable (sts_frag S T) |].
  Proof using. go. Qed.

  Lemma stable_if S mytoks: stable (sts_frag S mytoks).
  Proof using.
    hnf.
    split...
    2:{ admit. }
    {
      apply closed_iff.
      intros.
  Abort.
    
  Example  stable_prod1:
    stable (sts_frag
             {[s: state spsc255 | produced s = [] ]}
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

  Example  unstable_prod1: stable (sts_frag
                                {[s: state spsc255 | produced s =[] ]}
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
      apply (produce 255 2).
      unfold full. simpl in *. lia.
    }
  Qed.
  Example  stable_prod2:
    stable (sts_frag
             {[s: state spsc255 | firstn 3 (produced s) =[4;5;6] /\ 2<=numConsumed s]}
             ∅).
  Proof 
Set Nested Proofs Allowed.
Lemma head_app {T} (l lb: list T) (t:T) :
  head l = Some t -> head (l++lb) = head l.
Proof.
  clear.
  destruct l; simpl;  auto.
  intros. discriminate.
Qed.

  Example  stable_prod1:
    stable (sts_frag
             {[s: state spsc255 | produced s = [] ]}
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
             {[s: state spsc255 | head (produced s) = Some 2  ]}
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

  Example  stable_prod3:
    stable (sts_frag
             {[s: state spsc255 | 1<= numConsumed s ]}
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

  Search sts_auth.
  Locate "⋅".
  Search op cmra bi_sep.
(** closed S T := ∀ s∈S, if s can transition to s' using a token NOT in T, s' ∈ S *)
  Lemma stable_frag (g: gname) (S: sts.states spsc) (T: sts.tokens spsc):
    g |--> sts_frag S T |-- [| sts.closed S T |] ** [| ∃ s, s ∈ S|] ** (g |--> sts_frag S T).
  Proof using.
    iIntrosDestructs.
    wapplyObserve test.
    eagerUnifyU. go.
    hnf in H.
    forward_reason.
    go.
    iPureIntro.
    eauto.
  Qed.

  
  (* need tokens so that each party can assert the authorirative parts of their state:

   next : +ve and -ve examples of sts_frag/validity
   3 valid facts- 2 auth parts, 1 non-tokem frag: show it is duplicable 

   *)
  
  Definition ProducerRbad (cid: qlptr) (P: Z -> mpred) (producedL: list Z): Rep :=
    cinvr (invId cid) (1/2) (SPSCQueueInv1 cid P)
      ** pureR (inProduceLoc cid |--> logicalR (1/2) false)
      ** pureR (producedListLoc cid |--> logicalR (1/4) producedL).
  
  Definition ConsumerRbad (cid: qlptr) (P: Z -> mpred) (numConsumed:N): Rep :=
    cinvr (invId cid) (1/2) (SPSCQueueInv1 cid P)
      ** pureR (inConsumeLoc cid |--> logicalR (1/2) false)
      ** pureR (numConsumedLoc cid |--> logicalR (1/2) numConsumed).
  
  Opaque atomicR.
  Opaque Nat.modulo.

    Existing Instance learn_atomic_val_UNSAFE.
    Definition qFull (producedL: list Z) (numConsumed: N) :=
      lengthN producedL = Z.to_N (numConsumed + (bufsize-1)).

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
  (numConsumed <= len /\ len - numConsumed <= bufsize - 1) ->
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
  (numConsumed + boolZ bc <= len /\ len + boolZ bl  - numConsumed <= bufsize - 1) ->
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
    unfold ProducerR. go.
    unfold SPSCQueueInv1. go.
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
    unfold ConsumerR. go.
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
  
End with_Sigma.
(* TODO:
animation of resource transfer of SPSCqueue.
emphasize how the picture is trickly to encode in logic
ask GPT to draw a circular Q tikz. then nmanually add overlays

do bitset.
maybe do specs invariant of MPSCQueue: just put the ProducerR in a spinlock

done
add P value to the spsc specs

*)

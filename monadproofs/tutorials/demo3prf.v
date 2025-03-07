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
     - enforce complex protocols
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

  Definition bool_to_nat (b: bool) : Z := if b then 1 else 0.

  Notation cap := (256).
  Definition SPSCQueueInv1 (cid: qlptr) : Rep :=
    Exists (producedL: list Z) (numConsumed: N) (inProduce inConsume: bool),
      let numProduced : N  := lengthN producedL in
      let numConsumedAll: Z := (numConsumed + bool_to_nat inConsume) in
      let numProducedAll: Z := (numProduced + bool_to_nat inProduce) in
      let numNotFullyConsumed : Z := (lengthN producedL - numConsumed) in
      let numFullyFree: Z := (cap- numNotFullyConsumed- bool_to_nat inProduce) in
      let currItems := dropN (Z.to_N numConsumedAll) producedL in
      pureR (inProduceLoc cid |--> logicalR (1/2) inProduce)
         (* actual capacity is 1 less than cap (the size of the array) because we need to distinguish empty and full *)
      ** [| numConsumed <= numProduced /\ numProduced - numConsumed <= cap - 1 |]
      ** pureR (inConsumeLoc cid |--> logicalR (1/2) inConsume)
      ** pureR (producedListLoc cid |--> logicalR (1/2) producedL)
      ** pureR (numConsumedLoc cid |--> logicalR (1/2) numConsumed)
      ** _field "SPSCQueue::head_" |-> atomicR uint 1 (numConsumed `mod` cap)
      ** _field "SPSCQueue::tail_" |-> atomicR uint 1 (numProduced `mod` cap)
      **
      (* ownership of active cells *)
      ([∗ list] i↦  item ∈ currItems,  _field "buffer".["int" ! ((numConsumedAll + i) `mod` cap)] |-> primR "int"  1 (Vint item))
      (* ownership of inactive cells *)
      ** ([∗ list] i↦  _ ∈ (seqN 0 (Z.to_N numFullyFree)),  _field "buffer".["int" ! (numProducedAll + i) `mod` cap ] |-> anyR "int" 1).
   
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
    
      Hint Rewrite Z2N.id using lia: syntactic.
  Lemma pushqprf: denoteModule module
                    ** uint_store_spec
                    ** uint_load_spec
                    |-- pushqw.
  Proof using.
    verify_spec'.
    slauto.
    unfold ProducerRw. go.
    unfold SPSCQueueInv1. go.
    callAtomicCommitCinv.
    ren_hyp producedL (list Z).
    ren_hyp numConsumed N.
    normalize_ptrs. go.
    destruct (decide (lengthN producedL = Z.to_N (numConsumed + (cap-1)))).
    { (* overflow *)
      closeCinvqs.
      go.
      ego.
      iModIntro.
      go.
      callAtomicCommitCinv.
      go.
      closeCinvqs.
      go.
      ego.
      eagerUnifyU.
      iModIntro.
      name_locals.
      slauto.
      wp_if;[go|].
      intros.
      apply False_rect.
      rewrite e in q.
      apply q.
      Set Printing Coercions.
      autorewrite with syntactic.
      Arith.arith_solve.
    }
    {
      go.
      wapply (logicalR_update (inProduceLoc lpp) true). eagerUnifyU. go.
      closeCinvqs.
      go.
      ego.
      IPM.perm_left ltac:(fun L n =>
                            match L with
                            | context [seqN 0 ?l] => 
                                IPM.perm_right ltac:(fun R n =>
                                     match R with
                                     | context [seqN 0 ?r] => assert (l=1+r)%N as Heq
                                                                     by Arith.arith_solve
                                     end
                                     )
                            end
                         ).
      rewrite Heq.
      rewrite N.add_1_l.
      rewrite seqN_S_start.
      go.
      closed.norm closed.numeric_types.
      Search seq map.
      Lemma seqN_shift: ∀ start len : N, map N.succ (seqN start len) = seqN (N.succ start) len.
      Proof using.
        intros.
        unfold seqN.
        rewrite map_fmap.
        rewrite N2Nat.inj_succ.
        rewrite <- seq_shift.
        Search list_fmap map.
        rewrite map_fmap.
        Search fmap.
        repeat rewrite <- list_fmap_compose.
        unfold compose.
        f_equiv.
        hnf. intros. lia.
      Qed.
      rewrite <- (seqN_shift 0).
      rewrite big_opL_map.
      go.
      simpl.
      icancel (cancel_at this).
      {
        do 7 (f_equiv; intros; hnf).
        lia.
      }
      autorewrite with syntactic.
      go...
      iModIntro.
      go.
      callAtomicCommitCinv.
      go.
      closeCinvqs.
      go.
      ego.
      iModIntro.
      slauto.
      wp_if.
      autorewrite with syntactic in *.
      2:{ intros. apply False_rect.
          apply q.
          revert n.
          Lemma foo (len:N):
              len ≠ Z.to_N (Z.of_N numConsumed + 255)
  → (lengthZ _v_0 `mod` 256 + 1) `mod` 256 = Z.of_N numConsumed `mod` 256
      
        
      simpl
      Search seqN.
      autorewrite with syntactic.
      Set Printing Coercions.
      Print lengthZ.
      nia.
      lia.
      Arith.arith_solve.
     eagerUnifyU.
    fracG bool
  Qed.

fgptsto
lia.
go.
work.
Opaque has_type_prop.
go.
unfold bitsize.bound. simpl.
go.
Opaque valid..
go.
Locate zify_saturate.
      Saturate
      Arith.arith_solve
      go.
    wapply (half_half_update (inProduceLoc lpp)). unfold fgptsto. eagerUnifyC.
    Set Printing Coercions.
    eagerUnifyUC.
    Search fgptsto.
    
    
    
    go.
    Set Printing Coercions.
    instantiate (1:=1%Qp).
    go.
    Set Nested Proofs Allowed.
    
    #[global] Instance bool_0_refine2 y x : Refine1 true true (Vint (Z.of_nat x) = Vint y) [y = Z.to_nat x].
    Proof using.
      split; auto; intros; repeat constructor; try lia;
        inversion H; try lia.
      f_equal. lia.
    Qed.
    go.
    go.
    Search atomicR Learnable.

    
    
    Search Refine1.
    
    work.
    go.
    
      Search Forall.
      - constructor.
      aot
      go.
  Proof.

    Search 
    Locate "`mod`".
    
    go.
    
  cpp.spec "SPSCQueue::pop(int&)" as popq with (fun (this:ptr)=>
    \arg{valuep} "value" (Vptr valuep)
    \pre{consumeHistory: list Z} this |-> ConsumerR consumeHistory
    \pre valuep |-> anyR "int" 1  
    \post Exists value:Z, valuep |-> primR "int" 1 value ** this |-> ConsumerR (value::consumeHistory)
    ).
  Definition SPSCQProducerR  (sid: spscqid) : Rep :=
    
    as_Rep (fun this => 
              cinv (invId sid) (1/2)
            )
  cpp.spec ""
  Set Nested Proofs Allowed.

  
  Lemma setGetU_prf:
    denoteModule module
      ** int_store_spec
      ** int_load_spec
    |-- setGetU_spec_wrong.
  Proof using MODd with (fold cQpc; normalize_ptrs).
    verify_spec... (* [g340,371] [g551,558] *)
    slauto.
    repeat (iExists _); callAtomicCommit.
    repeat openCinvq.
    removeLater... (* [g590,627] cinv gone*)
    work.
    rename uv into uvcur... (* [g671,676]*)
    
    work using fwd_later_exist, fwd_later_sep;
      repeat removeLater;
      iApply fupd_mask_intro;[set_solver |];
      iIntrosDestructs... (* [g749,780; g642,675] [g749,751; g671,676] *)
    Existing Instance learn_atomic_val.
    go... (* w post [g704,709; c4067,4072] [g749,755]  must close*)
    closeCinvqs... (* [g676,708] [g673,711; g613,651] [g613,652; g539,573] [g539,573]*)
    work... (* lost that and got [g534,582] [g546,548; g580,582], [c4067,4072] *)
    iModIntro.
    Existing Instance learn_atomic_val_UNSAFE.
    go.
    repeat (iExists _); callAtomicCommit.
    repeat openCinvq.
    removeLater... (* [c4098,4104] [g664,666; g698,700]*)
    go.
    iApply fupd_mask_intro;[set_solver |];
      iIntrosDestructs.
    go.
    go...
    closeCinvqs.
    go.
    iModIntro.
    go.
  Abort.

  (* correct: spec: *)
  cpp.spec "setThenGetU(int)" as setGetU_spec with (
      \prepost{q invId} cinv q invId (∃ zv:Z, _global "u" |-> atomicR "int" 1 zv)
      \arg{uv} "value" (Vint uv)
      \post{any:Z} [Vint any] emp
      ).

  Lemma setGetU_prf: denoteModule module ** int_store_spec  ** int_load_spec |-- setGetU_spec.
  Proof using MODd with (fold cQpc; normalize_ptrs).
    verify_spec'.
    slauto.
    callAtomicCommitCinv.
    go... go.
    closeCinvqs.
    go.
    iModIntro.
    go.
    callAtomicCommitCinv.
    go... go.
    closeCinvqs.
    go.
    iModIntro.
    go.
  Qed.

cpp.spec "setThenGetU(int)" as setGetU_spec2 with (
   \prepost{q invId}
     cinv q invId
       (∃ uv:Z, _global "u" |-> atomicR "int" 1 uv
                ** [| isPrime uv |])
   \arg{uvnew:Z} "uvnew" (Vint uvnew)
   \post{any:Z} [Vint any] emp
      ).
  (** why is the above spec unprovable (for the code) *)

  
  Lemma setGetU_prf_prime: denoteModule module ** int_store_spec  ** int_load_spec |-- setGetU_spec2.
  Proof using MODd with (fold cQpc; normalize_ptrs).
    verify_spec'.
    slauto.
    callAtomicCommitCinv.
    go... go.
    rename a into uvBeforeWrite.
    (* close inv at the end of u.exchange *)
    closeCinvqs... (* [g651,653 ; g604,609] [g651,653 ; g604,609; g690,701] *)
    go. 
  Abort.
  
  cpp.spec "setThenGetU(int)" as setGetU_spec_prime with (
      \prepost{q invId} cinv q invId (∃ zv:Z, _global "u" |-> atomicR "int" 1 zv ** [| isPrime zv |])
      \arg{uvnew} "uvnew" (Vint uvnew)
      \pre [| isPrime uvnew |] 
      \post{any:Z} [Vint any (* not uvnew *)] [| isPrime any |]
      ).

  Lemma setGetU_prf_prime: denoteModule module ** int_store_spec  ** int_load_spec |-- setGetU_spec_prime.
  Proof using MODd with (fold cQpc; normalize_ptrs).
    verify_spec'.
    slauto...
    callAtomicCommitCinv.
    go.
    closeCinvqs.
    go.
    iModIntro.
    go...
    callAtomicCommitCinv.
    go.
    rename a into uvAtLoad.
    closeCinvqs.
    go.
    iModIntro.
    go.
  Qed.
  
  Lemma duplPrime (i:Z) :
    ([| isPrime i |]:mpred) |-- [| isPrime i |] ** [| isPrime i |] .
  Proof using. go. Qed.
    
  Lemma duplPrime2 (i:Z) (this:ptr) :
    let p := this ,, _field "v" |-> atomicR "int" 1 i ** [| isPrime i |] in
    p |-- p ** [| isPrime i |].
  Proof using. go. Qed.

  (** * heart of concurrency proofs
main challenge:
sequential proofs: loop invariants
concurrency proofs: cinv

cinv more difficult:
- loopinv:  beginning/end of loop body
- concurrency invariants: always hold. all code points in all methods

7 conditions, 20 functions in codebase. weeks tweaking the cinv so that the proofs of all 20 functions go though

next .. examples of more interesting cinv
   *)
  
Definition LockR (q: Qp) (invId: gname) (lockProtectedResource: mpred) : Rep :=
  structR "::SpinLock" q
  ** cinvr invId q
      (∃ locked:bool,
      _field "::SpinLock::locked" |-> atomicR "bool" 1 (Vbool locked)
      ** if locked then emp else pureR lockProtectedResource).

Lemma lockReq (l:ptr) (q: Qp) (invId: gname)
  (lockProtectedResource: mpred):
  l |-> LockR q invId lockProtectedResource
  -|-
  l |-> structR "SpinLock" q
  ** cinv invId q
       (∃ locked : bool,
           l ,, _field "SpinLock::locked"
             |-> atomicR "bool" 1%Qp (Vbool locked) **
             (if locked then emp else lockProtectedResource)).
  Proof using.
    unfold LockR.
    rewrite _at_sep.
    f_equiv.
    unfold cinvq.
    rewrite _at_as_Rep.
    f_equiv.
    apply cinv_proper.
    iSplit; go; ren_hyp locked bool;
      destruct locked; go.
   Qed.

  cpp.spec "SpinLock::SpinLock()" as lock_constr_spec with
    (fun this:ptr =>
       \pre{lockProtectedResource:mpred} lockProtectedResource
       \post Exists invId, this |-> LockR 1 invId lockProtectedResource
     ).
  
  cpp.spec "SpinLock::lock()" as lock_spec with
    (fun this:ptr =>
       \prepost{q invId lockProtectedResource}
           this |-> LockR q invId lockProtectedResource
       \post lockProtectedResource (* non-atomics *)
    ).
  
  cpp.spec "SpinLock::unlock()" as unlock_spec with
    (fun this:ptr =>
       \prepost{q invId lockProtectedResource}
           this |-> LockR q  invId lockProtectedResource
       \pre lockProtectedResource
       \post emp
     ).

Definition ConcLListR (q:Qp) (invId: gname) (base:ptr) : mpred :=
  base |-> structR "ConcLList" q 
  ** base,, _field "ConcLList::lock"
     |-> LockR q invId
           (∃ (l:list Z), base,, _field "ConcLList::head" |-> ListR 1 l).
  
  (** * BlockState analog: *)

  Definition ucinv (q:Qp) (invId: gname): mpred
    := cinv invId q (∃ uv:Z, _global "u" |-> atomicR "int" (1/2) uv
                             ** [| isPrime uv |]).
  (** only half in cinv *)


  Definition uAuthR (invId: gname) (uv: Z): mpred
    := ucinv (1/2) invId
       ** _global "u" |-> atomicR "int" (1/2) uv.

  (* no fraction argument in uAuthR:
     p1: ucinv (1/4) invId ** _global "u" |-> atomicR "int" (1/4) uv.
     p2: ucinv (1/4) invId ** _global "u" |-> atomicR "int" (1/4) uv.
   *)
  
  Definition uFragR (q:Qp) (invId: gname) : mpred
    := ucinv (q/2) invId.
  (* different from fractional ownership:
          [_global "u" |-> atomicR "int" q 3],
          [_global "x" |-> primR "int" q 3] *)

  Lemma uFragRsplit q invId :
    uFragR q invId |--    uFragR (q/2) invId
                       ** uFragR (q/2) invId.
  Proof.
    unfold uFragR,ucinv.
    rewrite splitcinvq.
    go.
  Qed.

  Hint Resolve atomicrC : br_opacity.
  Existing Instance lcinvqg_unsafe.
  Hint Resolve cinvqC : br_opacity.
  
  Lemma init (initv:Z) E:
    _global "u" |-> atomicR "int" 1 initv ** [| isPrime initv |]
      |-- |={E}=> Exists invId, uAuthR invId initv ** uFragR 1 invId.
  Proof.
    unfold uAuthR, uFragR, ucinv. go.
    match goal with
      |- context[cinvq ?ns _ _ ?P] => wapply (cinvq_alloc_no_shared_pages _ ns P)
    end.
    iFrame.
    rewrite <- bi.later_intro.
    go.
    iModIntro.
    go.
  Qed.
            
  cpp.spec "setU(int)" as setU_spec2 with (
      \pre{(uv:Z) invId} uAuthR invId uv
      \arg{newvalue} "value" (Vint newvalue)
      \post uAuthR invId newvalue
      ).
  
  cpp.spec "getU()" as getU_spec2 with (
      \prepost{invId q} uFragR invId q
      \post{any:Z} [Vint any] [| isPrime any|]
      ).

  cpp.spec "getU()" as getU_spec_auth with (
      \prepost{invId uval} uAuthR invId uval
      \post [Vint uval] [| isPrime uval|]
      ).

  cpp.spec "setThenGetU(int)" as setThenGet_spec2 with (
      \pre{(oldvalue:Z) invId} uAuthR invId oldvalue
      \arg{uvnew:Z} "value" (Vint uvnew)
      \pre [| isPrime uvnew |]
      \post [Vint uvnew] uAuthR invId uvnew
      ).

  
  Lemma setGetU_prf2: denoteModule module ** int_store_spec  ** int_load_spec |-- setThenGet_spec2.
  Proof using MODd with (fold cQpc; normalize_ptrs).
    verify_spec'.
    unfold uAuthR, ucinv. work... (* [g440,476; g492,533; c4032,4043] *)
    slauto.
    normalize_ptrs.
    callAtomicCommitCinv.
    rename a into uvinv... (* [g567,608] [g615,653; g331,343] *)
    (* [atomicR_combine] *)
    (* [g600,608;g648,653] *)
    work using atomicR_combineF.
    rewrite <- mut_mut_add.  rewrite Qp.half_half... (* [g681,717; g604,641] *)
    go... (* [g633,638]*)
    closeCinvqs... (* [g552,557] *)
    go... (* [g474,479] [g497,499; g535,537] [g497,499; g535,537; g474,479] *)
    iModIntro...  (* code may run [c4077,4086; g441,479] but because of inv, private owned *)
    go.
    callAtomicCommitCinv.
    rename a into uvAtLoad... (* [g652,657; g697,705] *)
    (* same trick again: [atomicR_combine]
     *)
    wapply atomicR_combine. eagerUnifyU. iFrame.
    iIntros "[? a]". iRevert "a".
    rewrite <- only_provable_wand_forall_2.
    iIntros. 
    applyToSomeHyp (Vint_inj).
    subst uvAtLoad.
    rewrite <- mut_mut_add.  rewrite Qp.half_half...
    go...
    closeCinvqs.
    go.
    iModIntro.
    go.
  Qed.

  Lemma as_Rep_meaning (f: ptr -> mpred) (base:ptr) :
    (base |-> as_Rep f)  -|- f base.
  Proof using. iSplit; go. Qed.
  

      
    Opaque atomicR.
  
      Ltac finishOpeningCinv :=
      work using fwd_later_exist, fwd_later_sep;
        repeat removeLater;
        iApply fupd_mask_intro;[set_solver |]; (* openRest *)
      iIntrosDestructs.
      
  Lemma lock_lock_prf: denoteModule module ** exchange_spec |-- lock_spec.
  Proof using MODd.
    verify_spec'.
    go.
    wp_while (fun _ => emp).
    rewrite lockReq.
    go.
    callAtomicCommitCinv.
    go.
    closeCinvqs.
    go.
    iModIntro.
    go. destruct a; go.
  Qed.
      
  Lemma unlock_prf: denoteModule module ** store_spec |-- unlock_spec.
  Proof using MODd.
    verify_spec'.
    rewrite lockReq.
    go.
    iExists _.
    callAtomicCommitCinv.
    go.
    closeCinvqs.
    go.
    iModIntro.
    go.
    lose_resources.
  Qed.

  Lemma gcd_proof: denoteModule module |-- gcd_spec.
  Proof using.
    rewrite <- demoprf.gcd_proof.
    apply denoteModule_weaken.
    apply module_le_true.
    exact _.
  Qed.

  (* move this proof to the end? without discussing loopinv, this cannot be explained *)
  Lemma gcdl_proof: denoteModule module |-- gcdl_spec.
  Proof using MODd with (fold cQpc).
    verify_spec.
    slauto.
    wp_for (fun _ => Exists iv:nat,
        i_addr |-> primR uint 1 iv
        ** [| iv <= length l |]%nat
        ** result_addr |-> primR uint 1 ((fold_left Z.gcd (firstn iv l) 0))).
    go. iExists 0%nat. go.
    wp_if.
    {
      slauto.
      eapplyToSomeHyp @arrayR_cell2.
      forward_reason.
      rewrite -> autogenhypr.
      hideRhs.
      go.
      unhideAllFromWork...
      slauto. (* call to gcd. we have already proved it's spec *)
      wapply gcd_proof. work. (* gcd_spec is now in context *)
      go. (* loop body finished, reistablish loopinv *)
      iExists (1+iv)%nat.
      slauto.
      simpl.
      go.
      rewrite -> autogenhypr.
      go.
    }
    {
      slauto.
      assert (iv=length l) as Heq by lia.
      subst.
      autorewrite with syntactic.
      go.
    }
  Qed.

  
  (* move this proof to the end? without discussing loopinv, this cannot be explained *)
  Lemma fold_left_prf : denoteModule module |-- fold_left_spec.
  Proof using MODd.
    verify_spec'.
    slauto.
    wp_for (fun _ => Exists iv:nat,
        i_addr |-> primR uint 1 iv
        ** [| iv <= length l |]%nat
        ** result_addr |-> primR uint 1 ((fold_left fm (firstn iv l) initv))).
    unfold cQpc.
    go.
    Set Printing Coercions.
    rewrite <- (bi.exist_intro 0%nat).
    go.
    wp_if.
    {
      slauto.
      Set Printing Implicit.
      eapplyToSomeHyp @arrayR_cell2.
      forward_reason.
      rewrite -> autogenhypr.
      hideRhs.
      go.
      unhideAllFromWork.
      slauto. (* loop body finished, reistablish loopinv *)
      iExists (1+iv)%nat.
      slauto.
      rewrite -> autogenhypr.
      go.
    }
    {
      slauto.
      assert (iv=length l) as Heq by lia.
      subst.
      autorewrite with syntactic.
      go.
    }
  Qed.
  
  cpp.spec (Nscoped 
              "parallel_fold_left(unsigned int*, unsigned int, unsigned int(*)(unsigned int,unsigned int), unsigned int)::@0"
              Ndtor)  as lam3destr  inline.
  Lemma pfl_proof: denoteModule module
                   ** (thread_class_specs "parallel_fold_left(unsigned int*, unsigned int, unsigned int(*)(unsigned int,unsigned int), unsigned int)::@0")
                       |-- par_fold_left_spec.
  Proof using MODd with (fold cQpc).
    unfold thread_class_specs.
    verify_spec'.
    wapply fold_left_prf; work.
    name_locals.
    wapplyObserve  obsUintArrayR.
    eagerUnifyU. work.
    go.
    rename a into lam.
    aggregateRepPieces lam.
    hideP ps.
    Opaque Nat.div.
    assert ( (length l/ 2 <= length l)%nat) as Hle.
    {
      rewrite <- Nat.div2_div.
      apply Nat.le_div2_diag_l.
    }
    nat2ZNLdup.
    rewrite (primr_split nums_addr).
    name_locals.
    rewrite (primr_split mid_addr).
    simpl in *.
    closed.norm closed.numeric_types.
    rewrite -> arrayR_split with (i:=((length l)/2)%nat) (xs:=l) by lia;
      go... (* array ownership spit into 2 pieces *)
    revertAdrs constr:([numsp; resultl_addr; nums_addr; mid_addr]).
    repeat rewrite bi.wand_curry.
    intantiateWand.
    instWithPEvar taskPost.
    go.
    iSplitL "".
    { verify_spec'.
      go.
      iExists _, fm. eagerUnifyU.
      autorewrite with syntactic. go.
      erefl.
    }
    unhideAllFromWork.
    autorewrite with syntactic. go. 
    iExists _, fm. eagerUnifyU. 
    autorewrite with syntactic. go.
    wapply @arrayR_combinep. eagerUnifyU.
    autorewrite with syntactic. go...
    (* c++ semantics computes, postcond requires *)
    icancel (cancel_at p);[| go].
    do 2 f_equiv.
    symmetry.
    apply fold_split; auto.
  Qed.

  cpp.spec "testgcdl()" as testspec with (
    \pre emp
    \post [Vint 6] emp).

  Lemma testgcdl_prf: denoteModule module ** parallel_gcdl_spec |-- testspec.
  Proof using.
    verify_spec'.
    slauto.
  Qed.
  
End with_Sigma.

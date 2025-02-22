Require Import monad.proofs.demo2.

Require Import monad.proofs.misc. (* monad/proofs/misc.v *)
Require Import bedrock.auto.invariants.
Require Import bedrock.auto.cpp.proof.
Require Import bedrock.auto.cpp.tactics4.
Require Import monad.proofs.demomisc.
Require Import monad.proofs.demoprf.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Z.
Import stdpp.list.
Import stdpp.decidable.
Import cQp_compat.
Open Scope cQp_scope.
Open Scope Z_scope.
Import Verbose.
Ltac slauto := misc.slauto1.
Disable Notation take.
Disable Notation drop.
Disable Notation "`div`" (all).
Disable Notation intR.
Disable Notation uintR.
Lemma lose_resources `{cpp_logic} (P:mpred): P |-- emp.
Proof using.
  go.
Qed.

Ltac lose_resources := try iStopProof; apply lose_resources.

Import linearity.
(** start recording *)

(** [gcd_proof] *)
Notation memory_order_seq_cst := 5.

Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
  Context  {MODd : demo2.module ⊧ CU}.
  Definition atomic_core_field_offset : offset. Proof. Admitted.
  Definition atomicR (ty:type) (q : cQp.t) (v : val) : Rep :=
      structR (Ninst "std::atomic" [Atype ty]) q **
    atomic_core_field_offset |-> primR ty q v.

(** Properties of [atomicR] *)
Section atomicR.
  Definition ns := (nroot .@@ "::SpinLock").

  #[global] Instance atomicR_frac T : CFracSplittable_1 (atomicR T).
  Proof.  solve_cfrac. Qed.

  #[global] Instance atomic_type_ptrR_observe ty v q
    : Observe (type_ptrR (Tnamed (Ninst "std::atomic" [Atype ty]))) (atomicR ty v q) := _.

  #[global] Instance atomic_agree ty v1 v2 q1 q2
    : Observe2 [| v1 = v2 |] (atomicR ty q1 v1) (atomicR ty q2 v2) := _.

  #[global] Instance atomic_agree_inj `{Vinj : A -> val} `{!Inj eq eq Vinj} ty v1 v2 q1 q2
    : Observe2 [| v1 = v2 |] (atomicR ty q1 (Vinj v1)) (atomicR ty q2 (Vinj v2)).
  Proof. exact: (observe2_inj Vinj). Qed.

  Definition learn_atomic_val (p : ptr) ty v1 v2 q1 q2
    : Learnable (p |-> atomicR ty q1 v1) (p |-> atomicR ty q2 v2) [v2=v1].
  Proof. solve_learnable. Qed.

  (** [atomicR ty q v] implies that value [v] has type [ty]. *)
  Lemma atomicR_has_type_prop ty v q :
    Observe [| has_type_prop v ty |] (atomicR ty q v).
  Proof. refine _. Qed.
End atomicR.

Opaque atomicR.

(*
Hint Resolve learn_atomic_val : br_opacity.
*)  
  Open Scope Z_scope.
  Set Nested Proofs Allowed.

  (**  *Arrays *)
  Definition gcdl_spec_core : WpSpec mpredI val val :=
      \arg{numsp:ptr} "nums" (Vptr numsp)
      \prepost{(l: list Z) (q:Qp)} numsp |-> arrayR uint (fun i:Z => primR uint q i) l
      \arg "size" (Vint (length l))
      \post [Vint (fold_left Z.gcd l 0)] emp.

  Example fold_left_gcd (n1 n2 n3: Z) :
    fold_left Z.gcd [n1;n2;n3] 0 =  Z.gcd (Z.gcd (Z.gcd 0 n1) n2) n3.
  Proof. reflexivity. Abort.
  
  Example arrayR3 (p:ptr) (n1 n2 n3: Z) (q: Qp):
    p |-> arrayR uint (fun i:Z => primR uint q i) [n1;n2;n3]
      -|- ( valid_ptr (p .[ uint ! 3 ])
              ** p |-> primR uint q n1
              ** p .[ uint ! 1 ] |-> primR uint q n2
              ** p .[ uint ! 2 ] |-> primR uint q n3).
  Proof.
    repeat rewrite arrayR_cons.
    repeat rewrite arrayR_nil.
    iSplit; go;
    repeat rewrite o_sub_sub;
    closed.norm closed.numeric_types; go.
  Abort.
    
  cpp.spec "gcdl(unsigned int*, unsigned int)" as gcdl_spec with (gcdl_spec_core).
  cpp.spec "parallel_gcdl(unsigned int*, unsigned int)" as parallel_gcdl_spec with (gcdl_spec_core).

  Compute (findBodyOfFnNamed2 module (isFunctionNamed2 "fold_left")).

  #[ignore_errors]
  cpp.spec "fold_left(unsigned int*, unsigned int, unsigned int(*)(unsigned int,unsigned int), unsigned int)" as fold_left_spec with (
      \arg{numsp:ptr} "nums" (Vptr numsp)
      \prepost{(l: list Z) (q:Qp)} numsp |-> arrayR uint (fun i:Z => primR uint q i) l
      \arg "size" (Vint (length l))
      \arg{fptr} "f" (Vptr fptr)
      \arg{initv} "init" (Vint initv)
      \pre{fm: Z->Z->Z} fptr |-> cpp_specR (tFunction "unsigned int" ["unsigned int*"%cpp_type; "unsigned int"%cpp_type])
      (
        \arg{av:Z} "a" (Vint av)
        \arg{bv:Z} "b" (Vint bv)
        \post [Vint (fm av bv)] emp
       )
      \post [Vint (fold_left fm l initv)] emp).

    
  (** * 2+ ways to split an arrays *)
  (** split fraction: both threads can read entire array *)
  Lemma fractionalSplitArrayR (numsp:ptr) (l: list Z) (q:Qp):
    numsp |-> arrayR uint (fun i:Z => primR uint q i) l |--
      numsp |-> arrayR uint (fun i:Z => primR uint (q/2) i) l
      ** numsp |-> arrayR uint (fun i:Z => primR uint (q/2) i) l.
  Proof.
    rewrite -> cfractional_split_half with (R := fun q => arrayR uint (fun i:Z => primR uint q i) l);
      [| exact _].
    rewrite _at_sep.
    f_equiv; f_equiv; f_equiv;
      simpl; rewrite cqpp2; auto.
  Qed.

  (** subarray partitioning: when threads concurrently read/write to disjoint segments.
     demonstrated in next example, which also illustrates the power of commutativity
   *)
  Lemma arrayR_split {T} ty (base:ptr) (i:nat) xs (R: T-> Rep):
    (i <= length xs)%nat ->
       base |-> arrayR ty R xs
    |-- base |-> arrayR ty R (firstn i xs) ** base .[ ty ! i ] |-> arrayR ty R (skipn i xs).
  Proof.
    intros.
    rewrite arrayR_split; eauto. go. 
  Qed.

  (** Structs: Point2D *)
  Definition NodeR `{Σ : cpp_logic, σ : genv} (q: cQp.t) (data: Z) (nextLoc: ptr): Rep :=
    structR "Node" q
    ** _field "Node::data_" |-> primR Ti32                       (cQp.mut q) data
    ** _field "Node::next_" |-> primR (Tptr (Tnamed "Node")) (cQp.mut q) (Vptr nextLoc).

  (** Structs: LinkedList *)


  Fixpoint ListR (q : cQp.t) (l : list Z) : Rep :=
    match l with
    | [] => nullR
    | hd :: tl => Exists (p : ptr), NodeR q hd p ** pureR (p |-> ListR q tl)
    end.


  Example listRUnfold (q:Qp) (head:ptr): head |-> ListR 1 [4;5;6] |--
    Exists node5loc node6loc,
       head |-> NodeR 1 4 node5loc
       ** node5loc |-> NodeR 1 5 node6loc
       ** node6loc |-> NodeR 1 6 nullptr
       (* ** [| node5loc <> node6loc <> head|] *).
  Proof using. work. unfold NodeR.  go. Qed.

  cpp.spec "reverse(Node*)" as reverse_spec with
    (\arg{lp} "l" (Vptr lp)
     \pre{l} lp |-> ListR 1 l
     \post{r}[Vptr r] r |-> ListR (cQp.m 1) (List.rev l)).

  Search List.rev.
  Check rev_app_distr.

  Definition sort (l:list Z) : list Z. Proof. Admitted.
  cpp.spec "sort(Node*)" as sort_spec with
    (\arg{lp} "l" (Vptr lp)
     \pre{l} lp |-> ListR 1 l
     \post{r}[Vptr r] r |-> ListR (1) (sort l)).

  Fixpoint sorted (l: list Z) : Prop :=
    match l with
    | [] => True
    | h::tl => forall t, t ∈ tl -> h <= t
    end.
  
  cpp.spec "sort(Node*)" as sort_spec2 with
    (\arg{lp} "l" (Vptr lp)
     \pre{l} lp |-> ListR 1 l
     \post{r}[Vptr r] Exists ls, r |-> ListR (1) ls ** [| sorted ls |]).
  
  (**  extensional spec
     - simpler than writing a 
     - the postcondition is too weak. why? *)






















  cpp.spec "sort(Node*)" as sort_spec3 with
    (\arg{lp} "l" (Vptr lp)
     \pre{l} lp |-> ListR 1 l
     \post{r}[Vptr r] Exists ls, r |-> ListR (1) ls ** [| sorted ls /\ l ≡ₚ ls|]).

  Lemma fold_id {A:Type} (f: A->A->A) (asoc: Associative (=) f)
    (start id: A) (lid: LeftId (=) id f) (rid: RightId (=) id f) (l: list A):
    fold_left f l start = f start (fold_left f l id).
  Proof using.
    hnf in lid.
    hnf in rid.
    revert start.
    induction l; auto.
    simpl.
    simpl. rewrite lid.
    intros.
    simpl.
    rewrite IHl.
    symmetry.
    rewrite IHl.
    aac_reflexivity.
  Qed.

  Lemma fold_split {A:Type} (f: A->A->A)(asoc: Associative (=) f)
    (id: A) (lid: LeftId (=) id f) (rid: RightId (=) id f) (l: list A) (lSplitSize: nat):
    fold_left f l id =
      f (fold_left f (firstn lSplitSize l) id)
        (fold_left f (skipn  lSplitSize l) id).
  Proof.
    rewrite <- (take_drop lSplitSize) at 1.
    rewrite fold_left_app.
    rewrite fold_id.
    aac_reflexivity.
  Qed.
  
  (** Passing resources between running threads

last session, we saw:
- pass assertions (incl ownership) to a new thread when starting it
- get back its postcondition at t.join()

  ┌──────────────────────────┐
  │  Parent owns P:mpred     │
  └──────────────────────────┘
           |
           | Split resources:  P -|- Pₖ ** C
           v
  ┌──────────────┬──────────────┐
  │ Pₖ (Parent)  │  C (Child)   │
  └──────────────┴──────────────┘
           |                |
           |                |
           |     <-?->      |
           |                |
           |                |
     Parent Thread       Child Thread (new)
         runs with Pₖ        runs with C
  ┌──────────────┬──────────────┐
  │ Pₖ' (Parent) │  C'(Child)   │ child done executing
  └──────────────┴──────────────┘
           |                |
Parent: Child.join 
  ┌──────────────────────────┐
  │ Parent owns Pk' ** C'    │
  └──────────────────────────┘


- no way to pass resources between running threads
*)

(** *Concurrent Invariants 
[c200,345]
   *)

  Notation inv := (cinvq (nroot .@@ "::demo2")).
  
Lemma cinvq_alloc `{Σ : cpp_logic} (E : coPset) (N : namespace) (P : mpred) :
  WeaklyObjective P → ▷ P |-- |={E}=> ∃ γ : gname, cinvq N γ 1 P.
Proof.
  intros.
  unfold cinvq.
  wapply (cinv_alloc E N P).
  work.
  iModIntro.
  ework.
  eagerUnifyU. go.
Qed.


Example boxedResource (P:mpred) (invId: gname): mpred := inv invId 1 P.


Lemma splitInv (P:mpred) (invId: gname) (q:Qp):
  inv invId q P |-- inv invId (q/2) P ** inv invId (q/2) P.
Proof using.
  rewrite <- (@fractional _ _ (cinvq_frac _)).
  f_equiv.
  Ltac solveQpeq2 :=
    repeat match goal with
      H:Qp |- _ => destruct H; simpl in *;
              f_equal;
      solveQpeq;
        solveQeq
      end.
  solveQpeq2.
Qed.

  cpp.spec "bar()" as bar_spec with (
      \prepost{q invId} inv q invId (∃ zv, _global "z" |-> primR "int" 1 zv)
      \post emp
    ).
  Lemma bar_prf : denoteModule module |-- bar_spec.
  Proof using.
    verify_spec.
    go.
  Abort. (* highlight. not an atomic op. cannot open the inv box *)

  cpp.spec "setU(int)" as setU_spec with (
      \prepost{q invId} inv q invId (∃ zv:Z, _global "u" |-> atomicR "int" 1 zv)
      \arg{value} "value" (Vint value)
      \post emp
      ).
    #[ignore_errors]
    cpp.spec "std::__atomic_base<int>::exchange(int, enum std::memory_order)"  as int_exchange_spec with
            (λ this : ptr,
       \arg{(x : Z)} "v" (Vint x)
       \arg "order" (Vint memory_order_seq_cst)
       \let pd := this ,, o_derived CU "std::__atomic_base<int>" "std::atomic<int>"  
       \pre{Q : Z → mpred}
         AC1 << ∀ y : Z, pd |-> atomicR "int" (cQp.mut 1) (Vint y)>> @ ⊤, ∅
            << pd |-> atomicR "int" (cQp.mut 1) (Vint x), COMM Q y >> 
       \post{y : Z}[Vint y]
       Q y).

    Opaque coPset_difference.
    
  Lemma setU_prf: denoteModule module ** int_exchange_spec |-- setU_spec.
  Proof using.
    verify_spec.
    go.
    iAssert (_global "u" |-> o_base CU "std::atomic<int>" "std::__atomic_base<int>" |-> structR  "std::__atomic_base<int>" 1) as "?".
    admit.
    slauto.
    iExists _.
    callAtomicCommitCinv.
    go.
    Existing Instance learn_atomic_val.
    go.
    closeCinvqs.
    go.
    iModIntro.
    simpl.
    iIntrosDestructs.
    iFrame.
    do 5 step.
    step.
    step...
    go.
     Fail idtac.
  Admitted.
    
    
  Definition AWrapperR  (q: Qp) (invId: gname): Rep :=
    structR "AWRapper" q **
    as_Rep (fun this:ptr =>
      inv invId q (∃ i:Z, this ,, _field "v" |-> atomicR "int" 1 i)).

  (** above, i is ∃ quantified *)
  Definition AWrapperRs  (q: Qp) (i:Z): Rep :=
    structR "AWRapper" q **
      _field "v" |-> atomicR "int" q (Vint i).

  
  cpp.spec "AWrapper::setValue(int)" as setValue_spec with (fun (this:ptr) =>
     \prepost{q invid} this |-> AWrapperR q invid
     \arg{newval:Z} "value" (Vint newval)
     \post emp).
  
  cpp.spec "AWrapper::setValue(int)" as setValue_nonconcurrent_spec with (fun (this:ptr) =>
     \pre{oldVal} this |-> AWrapperRs 1 oldVal
     \arg{i:Z} "value" (Vint i)
     \post this |-> AWrapperRs 1 i). (** but.. no other thread can call any method during this call *)

  cpp.spec "AWrapper::getValue()" as getValue_spec with (fun (this:ptr) =>
     \prepost{q invid} this |-> AWrapperR q invid
     \post{any:Z} [Vint any] emp).

  cpp.spec "AWrapper::getValue()" as getValue_nonconcurrent_spec with (fun (this:ptr) =>
     \prepost{q (val:Z)} this |-> AWrapperRs q val
     \post [Vint val] emp).

  Lemma as_Rep_meaning (f: ptr -> mpred) (base:ptr) :
    (base |-> as_Rep f)  -|- f base.
  Proof using. iSplit; go. Qed.
  
  Definition AWrapperR2  (q: Qp) (invId: gname): Rep :=
    structR "AWRapper" q **
    as_Rep (fun this:ptr =>
       inv invId q (∃ i:Z, this ,, _field "v" |-> atomicR "int" 1 i
                        ** [| isPrime i |] )).

  cpp.spec "AWrapper::setValue(int)" as setValue2_spec with (fun (this:ptr) =>
     \prepost{q invId} this |-> AWrapperR2 q invId
     \arg{i:Z} "value" (Vint i)
     \pre [| isPrime i |] 
     \post emp).

  cpp.spec "AWrapper::getValue()" as getValue2_spec with (fun (this:ptr) =>
     \prepost{q invid} this |-> AWrapperR2 q invid
     \post{any:Z} [Vint any] [| isPrime any |]).

  Opaque atomicR.
  Lemma duplPrime (i:Z) (this:ptr) :
    let p := this ,, _field "v" |-> atomicR "int" 1 i ** [| isPrime i |] in
    p |-- p ** [| isPrime i |].
  Proof using. go. Qed.

  
  
  (** *Parallelizing a sequence of operations
- e.g. sequence of operations monad transactions.
- Commutativivity enables ||: a o b = b o a

o commutative, with i as its left identity (forall x, i o x = x)

fold_left o [a1;a2;a3;a4;a5;a6] i =
((((((i o a1) o a2) o a3) o a4) o a5) o a6)


(((i o a1) o a2 ) o a3 )        (((i o a4) o a5 ) o a6 )
                    \               /
                     \             /
                      \           /
                   left_result   right_result
                          \       /
                           \     /
                            \   /
                        (left_result o right_result)

also, arrays
*)

  Hint Rewrite @fold_left_app: syntactic.
  Existing Instance UNSAFE_read_prim_cancel.
  
  Lemma gcd_proof: denoteModule module |-- gcd_spec.
  Proof using.
    rewrite <- demoprf.gcd_proof.
    apply denoteModule_weaken.
    apply module_le_true.
    exact _.
  Qed.
  
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
      unhideAllFromWork.
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

  Lemma fold_left_prf : denoteModule module |-- fold_left_spec.
  Proof using.
    verify_spec'.
    slauto.
    wp_for (fun _ => Exists iv:nat,
        i_addr |-> primR uint 1 iv
        ** [| iv <= length l |]%nat
        ** result_addr |-> primR uint 1 ((fold_left fm (firstn iv l) initv))).
    unfold cQpc.
    go.
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
      slauto.
      Hint Resolve @find_spec.find_cpp_specR : br_opacity.
      go.
      (*
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
    } *)
  Abort.
  
      Compute (Z.quot (-5) 4).
      Compute (Z.div (-5) 4).
      Set Default Goal Selector "!".
  cpp.spec (Nscoped 
              "parallel_gcdl(unsigned int*, unsigned int)::@0" Ndtor)  as lam2destr  inline.


  Lemma pgcdl_proof: denoteModule module
                       ** (thread_class_specs "parallel_gcdl(unsigned int*, unsigned int)::@0")
                       |-- parallel_gcdl_spec.
  Proof using MODd with (fold cQpc).
    unfold thread_class_specs.
    verify_spec'.
    wapply gcdl_proof.
    wapply gcd_proof. go.
    name_locals.
    wapplyObserve  obsUintArrayR.
    eagerUnifyU. work.
    aggregateRepPieces gcdlLambda_addr.
    go.
    hideP ps.
    Opaque Nat.div.
    assert ( (length l/ 2 <= length l)%nat) as Hle.
    {
      rewrite <- Nat.div2_div.
      apply Nat.le_div2_diag_l.
    }
    nat2ZNLdup.
    rewrite (primr_split nums_addr).
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
      iExists _. eagerUnifyU.
      autorewrite with syntactic. go.
      erefl.
    }
    unhideAllFromWork. subst taskPost.
    autorewrite with syntactic. go. 
    iExists _. eagerUnifyU. 
    autorewrite with syntactic. go.
    wapply @arrayR_combinep. eagerUnifyU.
    autorewrite with syntactic. go.
    (* c++ semantics computes ... postcond requires *)
    icancel (cancel_at p);[| go].
    do 2 f_equiv.
    symmetry.
    apply fold_split_gcd.
    auto.
    Check fold_split.
  Qed.
  Lemma fold_split_gcd  (l: list Z) (pl: forall a, In a l -> 0 <= a) (lSplitSize: nat):
    fold_left Z.gcd l 0=
      Z.gcd (fold_left Z.gcd (firstn lSplitSize l) 0) (fold_left Z.gcd (skipn lSplitSize l) 0).
  Proof using. apply misc.fold_split_gcd; auto. Qed.

  (** *Structs and Classes
     we often use multi-word numbers: EVMword is 256 bits *)
  
  Lemma unint32 (p:ptr) (v:Z) : p |-> primR uint 1 v |-- [| 0 <=v < 2^32 |] ** p |-> primR uint 1 v.
  Proof.
    go.
  Qed.


  
  (*class UnboundUint *)
  
  Require Import Coq.NArith.BinNat.
  Require Import Coq.Lists.List.
  Require Import Coq.Wellfounded.Wellfounded.
  Require Import Coq.Program.Wf.
  Import ListNotations.
  Require Import FunInd.

  Open Scope N_scope.
  Search N.size.
  Require Import Recdef.
  Function split_in_32 (n : N) {measure (fun n => N.to_nat (N.log2 n))} : list N :=
    match n with
    | 0%N => []
    | 1%N => [1]
    | _ =>
        let chunk := n `mod` (2^32) in
        let n'   := n / (2^32) in
        chunk :: split_in_32 n'
    end.
  Proof.
    {
      intros. subst.
      rewrite <- N.shiftr_div_pow2.
      repeat rewrite N.log2_shiftr.
      simpl.
      lia.
    }
    {
      intros. subst.
      rewrite <- N.shiftr_div_pow2.
      repeat rewrite N.log2_shiftr.
      simpl.
      lia.
    }
  Defined.

  Eval vm_compute in (split_in_32 (2^65 + 2^32 + 45)).

  Definition UnboundUintR (q:Qp) (n:N) : Rep :=
    let pieces32 : list N := split_in_32 n in 
    _field "size" |-> primR uint q (length pieces32)
      ** Exists arrBase, _field "data" |-> primR uint q (Vptr arrBase)
                           ** pureR (arrBase |-> arrayR uint (fun i:N => primR uint q i)  pieces32).
  (** note the logical abstraction *)

  Example unfoldUnboundUintR (p:ptr) q n:
    let pieces32 := split_in_32 n in   
    p |-> UnboundUintR q n -|-
      p |-> _field "size" |-> primR uint q (length pieces32)
      ** Exists arrBase, p |-> _field "data" |-> primR uint q (Vptr arrBase)
                           ** arrBase |-> arrayR uint (fun i:N => primR uint q i)  pieces32.
  Proof. simpl.  unfold UnboundUintR. iSplit; go. Qed.

  Transparent atomicR.
  
  
   (*
    (λ this : ptr,
       \arg{(Q : bool → mpred) (x : bool)} "v" (Vbool x)
       \pre
         AU1 << ∀ y : bool, this |-> atomicR Tbool (Vbool y) (cQp.mut 1) >> @ ⊤, ∅
            << this |-> atomicR Tbool (Vbool x) (cQp.mut 1), COMM Q y >> 
       \post{y : bool}[Vbool y]
                Q y)
  Rep ~= ptr -> mpred
                *)

  Locate inv.
  Definition LockR (q: cQp.t) (invId: gname) (lockProtectedResource: mpred) : Rep :=
  as_Rep (fun (this:ptr)=>
     this |-> structR "::SpinLock" q
     ** cinvq ns invId q (Exists locked:bool,
                  this |-> _field "::SpinLock::locked" |-> atomicR Tbool 1 (Vbool locked)
	          ** if locked then emp else lockProtectedResource
    )).

  cpp.spec "SpinLock::SpinLock()" as lock_constr_spec with
      (fun this:ptr =>
         \pre{R:mpred} R
         \post Exists invId,  this |-> LockR 1 invId R
      ).
  
  cpp.spec "SpinLock::lock()" as lock_spec with
      (fun this:ptr =>
         \prepost{q invId R} this |-> LockR q  invId R
         \post R
      ).
  
  cpp.spec "SpinLock::unlock()" as unlock_spec with
      (fun this:ptr =>
         \prepost{q invId R} this |-> LockR q  invId R
         \pre R
         \post emp
      ).
    #[ignore_errors]
    cpp.spec "std::atomic<bool>::exchange(bool, enum std::memory_order)"  as exchange_spec with
            (λ this : ptr,
       \arg{(x : bool)} "v" (Vbool x)
       \arg "order" (Vint memory_order_seq_cst)
       \pre{Q : bool → mpred}
         AC1 << ∀ y : bool, this |-> atomicR Tbool (cQp.mut 1) (Vbool y)>> @ ⊤, ∅
            << this |-> atomicR Tbool (cQp.mut 1) (Vbool x), COMM Q y >> 
       \post{y : bool}[Vbool y]
       Q y).
    Opaque atomicR.
  Definition fwd_later_exist := [FWD] (@bi.later_exist).
  Definition fwd_later_sep := [FWD] (@bi.later_sep).
  Definition bwd_later_exist := [BWD_MW->] (@bi.later_exist).
  Definition bwd_later_sep := [BWD_MW->] (@bi.later_sep).
  Definition fwd_at_later := [FWD<-] (@_at_later).
  Hint Resolve fwd_later_exist fwd_later_sep bwd_later_exist
    bwd_later_sep : br_opacity.

(* open all cinvq invariants then open rest. used in callAtomicCommitCinv*)
Ltac openCinvqsRest :=
  repeat openCinvq;
  work using fwd_later_exist, fwd_later_sep;
  repeat removeLater;
  iApply fupd_mask_intro;[set_solver |]; (* openRest *)
  iIntrosDestructs.

(**
   the RHS of your goal should look like a permutation of
   [[
   AC pre post ?Q ** (forall ..., ?Q ... -* ...)
   ]]
  it first calls [callAtomicCommit] to instantiate the public post Q.
  then it opens all cinvq invariants
  then it opens everything else (change the goal from [|={⊤ \ ..\ ... ,∅}=> U)] to  [|={∅}=> U)])
  and then "does iModIntro" so that you can start proving U which is typically of the form [pre ** ...]
 *)
Ltac callAtomicCommitCinv :=
  callAtomicCommit;
  openCinvqsRest.

(* applies to goals that look like [|-- AC pre post Q] or [|-- AU pre post Q]  in IPM: only 1 conjuct in conclusion and not 2, where [callAtomicCommitCinv] works. it sets up the proof of AC/AU by doing the usual initialization
 and opening all invariants and rest so that you can immediately begin proving [pre] *)
Ltac proveAuAc :=
  (iAcIntro || iAuIntro);
  (unfold commit_acc || unfold atomic_acc);
  openCinvqsRest.
  
  Lemma lock_lock_prf: denoteModule module ** exchange_spec |-- lock_spec.
  Proof using MODd.
    verify_spec'.
    go.
    wp_while (fun _ => emp).
    go.
    iExists (fun oldval:bool => (if oldval then emp else R) **  cinvq ns invId q
        (∃ locked : bool, this |-> o_field CU "SpinLock::locked" |-> atomicR "bool" 1%Qp (Vbool locked) ∗ (if locked then emp else R))).
    Require Import bedrock.auto.tactics.
    wrename [cinvq _ _ _ _]  "inv".
    iSplitL "inv".
    -
      Opaque coPset_difference. go.
      iAcIntro. unfold commit_acc.
      openCinvqsRest.
      go.
      closeCinvqs.
      go.
      iModIntro.
      go.
    - go.
      wp_if; go.
   Qed.
    #[ignore_errors]
    cpp.spec "std::atomic<bool>::store(bool, enum std::memory_order)"  as store_spec with
(λ this : ptr,
       \arg{(Q : mpred) (x : bool)} "v" (Vbool x)
       \arg "memorder" (Vint 5)
       \pre
         AC1 << ∀ y : bool, this |-> atomicR Tbool (cQp.mut 1) (Vbool y)>> @ ⊤, ∅
            << this |-> atomicR Tbool (cQp.mut 1) (Vbool x), COMM Q >> 
                                                               \post    Q).
      
  Lemma unlock_prf: denoteModule module ** store_spec |-- unlock_spec.
  Proof using MODd.
    verify_spec'.
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

End with_Sigma.
  

(* TODO

0. linkedlist
1. remove AWrapper. work on a global atomic variable to make things simpler. dont  need a class rep. getU() , setU(v) instead.
2. just after bar_prf, contrast how the cinv version allows access and how it requires to return back ownership
3. show prime number dupl
4. BlockState picture
5. counter auth frag specs
6. block state specs
8. lock 
7. lock protected linked list


sequence:
1. arrays: gcdl spec
2: structs: point: not much logical abstraction 
3: structs: linked list
4: thread sharing resources while running: asciiart
5: setU/getU specs: 3 variants: concurrent, sequential, concurrent with Primes
6: setU/getU 4th spec: auth frag
7: execute_block diagram to explain the auth/frag spec of BlockState
8. block state specs
9. lock code and lock protected linked list: asciiart/animation explaining how lock protects linked list. emplasize the lock protected resource need not be atomic.
10. ThreadSafeLinkedList Rep


*)

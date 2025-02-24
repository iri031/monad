Require Import monad.proofs.demo2.
Require Import bedrock.auto.invariants.
Require Import bedrock.auto.cpp.proof.
Require Import bedrock.auto.cpp.tactics4.
Require Import monad.proofs.misc.
Require Import monad.proofs.demomisc.
Require Import monad.proofs.demoprf.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Z.
Import cQp_compat.
Import Verbose.
Import linearity.


(** start recording.
Exercises:
 *)

Notation memory_order_seq_cst := 5.

Section with_Sigma.
  Context `{Sigma:cpp_logic}  {CU: genv}.
  Context  {MODd : demo2.module ⊧ CU}.

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

    #[ignore_errors]
    cpp.spec "std::__atomic_base<int>::load(enum std::memory_order) const"  as int_load_spec with
            (λ this : ptr,
       \let pd := this ,, o_derived CU "std::__atomic_base<int>" "std::atomic<int>"  
       \arg "order" (Vint memory_order_seq_cst)
       \pre{ (q:Qp) (InvOut : Z → mpred)}
         AC1 << ∀ y : Z, pd |-> atomicR "int" q (Vint y)>> @ ⊤, ∅
                      << pd |-> atomicR "int" q (Vint y), COMM InvOut y >> 
       \post{y : Z}[Vint y]
       InvOut y).
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
    #[ignore_errors]
    cpp.spec "std::atomic<bool>::store(bool, enum std::memory_order)"  as store_spec with
(λ this : ptr,
       \arg{(Q : mpred) (x : bool)} "v" (Vbool x)
       \arg "memorder" (Vint 5)
       \pre
         AC1 << ∀ y : bool, this |-> atomicR Tbool (cQp.mut 1) (Vbool y)>> @ ⊤, ∅
            << this |-> atomicR Tbool (cQp.mut 1) (Vbool x), COMM Q >> 
                                                               \post    Q).
  
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

  (** * 2+ ways to split an arrays

   +---+---+---+---+---+---+
   | q | q | q | q | q | q |
   +---+---+---+---+---+---+

  +---+---+---+---+---+---+       +---+---+---+---+---+---+
   |q/2|q/2|q/2|q/2|q/2|q/2|      |q/2|q/2|q/2|q/2|q/2|q/2|
   +---+---+---+---+---+---+      +---+---+---+---+---+---+

   *)
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
   +---+---+---+---+---+---+
   | q | q | q | q | q | q |
   +---+---+---+---+---+---+


   +---+---+---+                   +---+---+---+
   | q | q | q |                    | q | q | q |
   +---+---+---+                    +---+---+---+

   *)
  Lemma arrayR_split {T} ty (base:ptr) (i:nat) xs (R: T-> Rep):
    (i <= length xs)%nat ->
       base |-> arrayR ty R xs
    |-- base |-> arrayR ty R (firstn i xs) ** base .[ ty ! i ] |-> arrayR ty R (skipn i xs).
  Proof.
    intros.
    rewrite arrayR_split; eauto. go. 
  Qed.

  Hint Rewrite @fold_left_app: syntactic.
  Existing Instance UNSAFE_read_prim_cancel.
  
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
    rename a into lam.
    aggregateRepPieces lam.
    go.
    hideP ps.
    Opaque Nat.div.
    assert ( (length l/ 2 <= length l)%nat) as Hle.
    {
      rewrite <- Nat.div2_div.
      apply Nat.le_div2_diag_l.
    }
    nat2ZNLdup.
    progress closed.norm closed.numeric_types.
    rewrite -> arrayR_split with (i:=((length l)/2)%nat) (xs:=l) by lia;
      go... (* array ownership spit into 2 pieces. [g], the child thread gets [g] *)
    revertAdrs constr:([numsp; resultl_addr]);
      repeat rewrite bi.wand_curry;
      intantiateWand.
    (*
    iExists (resultl_addr |-> uninitR "unsigned int" 1%Qp **
               numsp |-> arrayR "unsigned int" (λ i : Z, primR "unsigned int" q i) (firstn (length l / 2) l))...
     *)
    instWithPEvar taskPost.
    go.
    iSplitL "".
    { verify_spec'.
      go.
      iExists _. eagerUnifyU.
      autorewrite with syntactic. go.
      erefl.
    }
    unhideAllFromWork.
    autorewrite with syntactic. go. 
    iExists _. eagerUnifyU. 
    autorewrite with syntactic. go.
    wapply @arrayR_combinep. eagerUnifyU.
    autorewrite with syntactic. go...
    (* symbolic eval computs, postcond requires, [g] *)
    icancel (cancel_at p);[| go].
    do 2 f_equiv.
    symmetry.
    apply fold_split_gcd.
    auto.
  Qed.

  Lemma fold_split_gcd  (l: list Z) (pl: forall a, In a l -> 0 <= a) (lSplitSize: nat):
      Z.gcd
        (fold_left Z.gcd (firstn lSplitSize l) 0)
        (fold_left Z.gcd (skipn lSplitSize l) 0)=
    fold_left Z.gcd l 0.
  Proof using. symmetry. apply misc.fold_split_gcd; auto. Qed.

  (** o:=Z.gcd
((((((i o a1) o a2) o a3) o a4) o a5) o a6)

(((i o a1) o a2 ) o a3 )        (((i o a4) o a5 ) o a6 )
                    \               /
                      \           /
                   left_result   right_result
                          \       /
                            \   /
                        (left_result o right_result)
*)

  (** * Time for Quiz
[c]
   *)

  #[ignore_errors]
  cpp.spec "fold_left(unsigned int*, unsigned int, unsigned int(*)(unsigned int,unsigned int), unsigned int)" as fold_left_spec with (
      \arg{numsp:ptr} "nums" (Vptr numsp)
      \prepost{(l: list Z) (q:Qp)} numsp |-> arrayR uint (fun i:Z => primR uint q i) l
      \arg "size" (Vint (length l))
      \arg{fptr} "f" (Vptr fptr)
      \arg{initv} "init" (Vint initv)
      \pre{fm: Z->Z->Z} fptr |->
          cpp_specR (tFunction "unsigned int" ["unsigned int"%cpp_type; "unsigned int"%cpp_type])
            (
              \arg{av:Z} "a" (Vint av)
                \arg{bv:Z} "b" (Vint bv)
                \post [Vint (fm av bv)] emp
            )
      \post [Vint (fold_left fm l initv)] emp).

  #[ignore_errors]
  cpp.spec "parallel_fold_left(unsigned int*, unsigned int, unsigned int(*)(unsigned int,unsigned int), unsigned int)" as par_fold_left_spec with (
      \arg{numsp:ptr} "nums" (Vptr numsp)
      \prepost{(l: list Z) (q:Qp)} numsp |-> arrayR uint (fun i:Z => primR uint q i) l
      \arg "size" (Vint (length l))
      \arg{fptr} "f" (Vptr fptr)
      \pre{fm: Z->Z->Z} fptr |->
          cpp_specR (tFunction "unsigned int" ["unsigned int"%cpp_type; "unsigned int"%cpp_type])
            (
              \arg{av:Z} "a" (Vint av)
                \arg{bv:Z} "b" (Vint bv)
                \post [Vint (fm av bv)] emp
            )
      \pre [| Associative (=) fm |]
      \arg{initv} "init" (Vint initv)
      \pre [| LeftId (=) initv fm |]
      \pre [| RightId (=) initv fm |]
      \post [Vint (fold_left fm l initv)] emp).
  
  Lemma fold_split {A:Type} (f: A->A->A)(asoc: Associative (=) f)
    (id: A) (lid: LeftId (=) id f) (rid: RightId (=) id f) (l: list A) (lSplitSize: nat):
    fold_left f l id =
      f (fold_left f (firstn lSplitSize l) id)
        (fold_left f (skipn  lSplitSize l) id).
  Proof.
    rewrite <- (take_drop lSplitSize) at 1.
    rewrite fold_left_app.
    rewrite fold_id2.
    aac_reflexivity.
  Qed.
  
  (** Structs: Node [c] *)
  Definition NodeR `{Σ : cpp_logic, σ : genv} (q: cQp.t) (data: Z) (nextLoc: ptr): Rep :=
    structR "Node" q
    ** _field "Node::data_" |-> primR Ti32                       (cQp.mut q) data
    ** _field "Node::next_" |-> primR (Tptr (Tnamed "Node")) (cQp.mut q) (Vptr nextLoc).

  (** Structs: LinkedList [c] *)


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
  

Example boxedResource (P:mpred) (invId: gname): mpred := cinv invId 1 P.

  
Lemma splitInv (P:mpred) (invId: gname) (q:Qp):
  cinv invId q P |-- cinv invId (q/2) P ** cinv invId (q/2) P.
Proof using.
  apply splitcinvq.
Qed.

  cpp.spec "bar()" as bar_spec with (
      \prepost{q invId} cinv q invId (∃ zv, _global "z" |-> primR "int" 1 zv)
      \post emp
    ).
  Lemma bar_prf : denoteModule module |-- bar_spec.
  Proof using.
    verify_spec.
    go.
  Abort. (* highlight. not an atomic op. cannot open the cinv box *)

  cpp.spec "setU(int)" as setU_spec with (
      \prepost{q invId} cinv q invId (∃ zv:Z, _global "u" |-> atomicR "int" 1 zv)
      \arg{value} "value" (Vint value)
      \post emp
      ).
      
    Opaque coPset_difference.
    Opaque atomicR.
Ltac slauto := (slautot ltac:(autorewrite with syntactic; try solveRefereceTo)); try iPureIntro.
  Lemma setU_prf: denoteModule module ** int_exchange_spec |-- setU_spec.
  Proof using MODd.
    verify_spec'.
    slauto.
    callAtomicCommitCinv.
    Existing Instance learn_atomic_val.
    go.
    closeCinvqs.
    go.
    iModIntro.
    simpl.
    do 9 step...
    go.
  Qed.
    
  cpp.spec "setThenGetU(int)" as setGetU_spec_wrong with (
      \prepost{q invId} cinv q invId (∃ zv:Z, _global "u" |-> atomicR "int" 1 zv)
      \arg{value} "value" (Vint value)
      \post [Vint value] emp
        ).
  (** why is the above spec unprovable? *)
  
  Lemma setGetU_prf: denoteModule module ** int_exchange_spec  ** int_load_spec |-- setGetU_spec_wrong.
  Proof using MODd.
    verify_spec.
    slauto.
    callAtomicCommitCinv.
    Existing Instance learn_atomic_val.
    go. (* now u has value value. TODO: rename value *)
    closeCinvqs.
    go. (* now u's value is any zv *)
    iModIntro.
    Existing Instance learn_atomic_val_UNSAFE.
    go.
    callAtomicCommitCinv. (* when we open the invariant again, a may be <> value [g100,220] *)
    go.
    closeCinvqs.
    go.
    iModIntro.
    go.
  Abort.

  cpp.spec "setThenGetU(int)" as setGetU_spec with (
      \prepost{q invId} cinv q invId (∃ zv:Z, _global "u" |-> atomicR "int" 1 zv)
      \arg{value} "value" (Vint value)
      \post{any:Z} [Vint any] emp
      ).

  Lemma setGetU_prf: denoteModule module ** int_exchange_spec  ** int_load_spec |-- setGetU_spec.
  Proof using MODd.
    verify_spec'.
    slauto.
    callAtomicCommitCinv.
    go. (* now u has value value. TODO: rename value *)
    closeCinvqs.
    go. (* now u's value is any zv *)
    iModIntro.
    go.
    callAtomicCommitCinv. (* when we open the invariant again, a may be <> value [g100,220] *)
    go.
    closeCinvqs.
    go.
    iModIntro.
    go.
  Qed.

  cpp.spec "setThenGetU(int)" as setGetU_spec2 with (
      \prepost{q invId} cinv q invId (∃ zv:Z, _global "u" |-> atomicR "int" 1 zv ** [| isPrime zv |])
      \arg{value} "value" (Vint value)
      \post{any:Z} [Vint any] emp
      ).
  
  (* why is the above spec unprovable (for the code) *)
  Lemma setGetU_prf_prime: denoteModule module ** int_exchange_spec  ** int_load_spec |-- setGetU_spec2.
  Proof using MODd.
    verify_spec'.
    slauto.
    callAtomicCommitCinv.
    go. (* now u has value value. TODO: rename value *)
    closeCinvqs. (* highlight zv and instantiation is value *)
    go. 
  Abort.
  cpp.spec "setThenGetU(int)" as setGetU_spec_prime with (
      \prepost{q invId} cinv q invId (∃ zv:Z, _global "u" |-> atomicR "int" 1 zv ** [| isPrime zv |])
      \arg{value} "value" (Vint value)
      \pre [| isPrime value |] 
      \post{any:Z} [Vint any] [| isPrime value |]
      ).

  Lemma setGetU_prf_prime: denoteModule module ** int_exchange_spec  ** int_load_spec |-- setGetU_spec_prime.
  Proof using MODd.
    verify_spec'.
    slauto.
    callAtomicCommitCinv.
    go. (* now u has value value. TODO: rename value *)
    closeCinvqs.
    go. (* now u's value is any zv *)
    iModIntro.
    go.
    callAtomicCommitCinv. (* when we open the invariant again, a may be <> value [g100,220] *)
    go.
    closeCinvqs.
    go.
    iModIntro.
    go.
  Qed.
  
(** * heart of concurrency proofs
sequential proofs: loop invariants
concurrency proofs: cinv: rename inv?

- loopinvy:  beginning/end of loop body
- concurrency invariants: always hold. all code points in all methods

next .. examples of more interesting loopinv
 *)


  
  (** * BlockState analog: *)

  Definition ucinv (q:Qp) (invId: gname): mpred
    := cinv invId q (∃ zv:Z, _global "u" |-> atomicR "int" (1/2) zv ** [| isPrime zv |]).
  (** only half in cinv *)


  Definition uAuthR (invId: gname) (uv: Z): mpred
    := ucinv (1/2) invId ** _global "u" |-> atomicR "int" (1/2) uv.

  (* no fraction argument in uAuthR:
     p1: ucinv (1/4) invId ** _global "u" |-> atomicR "int" (1/4) uv.

     p2: ucinv (1/4) invId ** _global "u" |-> atomicR "int" (1/4) uv.
   *)
  
  Definition uFragR (q:Qp) (invId: gname) : mpred := ucinv (q/2) invId.
  (* different from fractional ownership: [_global "u" |-> atomicR "int" q 3], [_global "x" |-> primR "int" q 3] *)

  Hint Resolve atomicrC : br_opacity.
  Existing Instance lcinvqg_unsafe.
  Hint Resolve cinvqC : br_opacity.
  Lemma init (initv:Z) E:
    _global "u" |-> atomicR "int" 1 initv ** [| isPrime initv |]
      |-- |={E}=> Exists invId, uAuthR invId initv ** uFragR 1 invId.
  Proof using.
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
      \post{any:Z} [Vint uval] [| isPrime uval|]
      ).
  
  cpp.spec "setThenGetU(int)" as setThenGet_spec2 with (
      \pre{(oldvalue:Z) invId} uAuthR invId oldvalue
      \arg{newvalue:Z} "value" (Vint newvalue)
      \pre [| isPrime newvalue |]
      \post [Vint newvalue] uAuthR invId newvalue
      ).

  
  Lemma setGetU_prf2: denoteModule module ** int_exchange_spec  ** int_load_spec |-- setThenGet_spec2.
  Proof using MODd with (fold cQpc).
    verify_spec'.
    slauto. unfold uAuthR, ucinv. go.
    callAtomicCommitCinv.
    go.
    work using atomicR_combineF.
    rewrite <- mut_mut_add.  rewrite Qp.half_half...
    go.
    closeCinvqs.
    go.
    iModIntro.
    (** closed the invariant and se still have 1/2 left [g11,12].
        crucial when we call load next: [g11,12]
        other threads can race but they can only read. I own 1/2 of atomicR. other threads can only access the 1/2 in the cinv *)
    go.
    callAtomicCommitCinv...
    (* had before [g11,12]. opening the invariant got this part [g] says u has value a and is IsPrime [g].
       same trick again: agreement [g]
     *)
    wapply atomicR_combine. eagerUnifyU. iFrame.
    iIntros "[? a]". iRevert "a".
    rewrite <- only_provable_wand_forall_2.
    iIntros. 
    applyToSomeHyp (Vint_inj).
    subst a.
    rewrite <- mut_mut_add.  rewrite Qp.half_half...
    go.
    closeCinvqs.
    go.
    iModIntro. go.
  Qed.
    
  

  Lemma as_Rep_meaning (f: ptr -> mpred) (base:ptr) :
    (base |-> as_Rep f)  -|- f base.
  Proof using. iSplit; go. Qed.
  

  Lemma duplPrime (i:Z) (this:ptr) :
    let p := this ,, _field "v" |-> atomicR "int" 1 i ** [| isPrime i |] in
    p |-- p ** [| isPrime i |].
  Proof using. go. Qed.

      
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
    Opaque atomicR.
  
  Lemma lock_lock_prf: denoteModule module ** exchange_spec |-- lock_spec.
  Proof using MODd.
    verify_spec'.
    go.
    wp_while (fun _ => emp).
    go.
    iExists (fun oldval:bool => (if oldval then emp else R) **  cinvq ns invId q
        (∃ locked : bool, this |-> o_field CU "SpinLock::locked" |-> atomicR "bool" 1%Qp (Vbool locked) ∗ (if locked then emp else R))).
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
End with_Sigma.
  

(* TODO:
2: clean this file
3. finalize cpp code and goal before determining offsets
8. narrartive+offsets in coments. optimize around proofchecking times
7. lock protected linked list: code
10. lock protected linked list: tikz animation

done:
0. linkedlist
1. remove AWrapper. work on a global atomic variable to make things simpler. dont  need a class rep. getU() , setU(v) instead.
2. just after bar_prf, contrast how the cinv version allows access and how it requires to return back ownership
3. show prime number dupl
5. counter auth frag specs
9. spec of BlockState::read_storage
6. BlockState::merge and can_merge specs: cleanup
4. BlockState tikz aniimation
11. fold_left proof w/ function ptr
12. test cases of c++ functions


sequence:
1. arrays: gcdl spec
2: structs: Node: not much logical abstraction 
3: structs: linked list
4: thread sharing resources while running: asciiart
5: setU/getU specs: 3 variants: concurrent, sequential, concurrent with Primes
6: setU/getU 4th spec: auth frag
7: execute_block diagram to explain the auth/frag spec of BlockState
8. block state specs
9. lock code and lock protected linked list: asciiart/animation explaining how lock protects linked list. emplasize the lock protected resource need not be atomic.
10. ThreadSafeLinkedList Rep


*)

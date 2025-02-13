Require Import monad.asts.demo.
Require Import monad.proofs.misc.
Require Import monad.proofs.libspecs.
Require Import bedrock.auto.invariants.
Require Import bedrock.auto.cpp.proof.
Require Import bedrock.auto.cpp.tactics4.
Require Import monad.proofs.demomisc.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Z.
Import stdpp.list.
Import stdpp.decidable.
Import cQp_compat.
Open Scope cQp_scope.
Open Scope Z_scope.
Import linearity.
Import Verbose.
Ltac slauto := misc.slauto1.
Disable Notation take.
Disable Notation drop.
Disable Notation "`div`" (all).

(** ** Questions/comment timing recommendation *)

(** turn on zoom recording *)

(** ** why formal verification:
- highest level of assurance:
PLDI 2011: Finding and Understanding Bugs in C Compilers
CompCert C compiler

first step: write specs
 *)
Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
  Context  {MODd : demo.module ⊧ CU}.
  Definition cQpc := cQp.mk false.
  Coercion cQpc : Qp >-> cQp.t.

  Disable Notation intR.
  Disable Notation uintR.
  Open Scope Z_scope.
  Notation uint := "unsigned int"%cpp_type.
Set Nested Proofs Allowed.

  
  (* /home/abhishek/work/coq/monad/demo.cpp *)
  cpp.spec "foo()" as foo_spec with (
        \pre{xv:Z} _global "x" |-> primR uint (1/2) xv (* forall xv .. *)
        \pre _global "y" |-> anyR uint 1
        \post _global "y" |-> primR uint 1 (xv+1)
              ** _global "x" |-> primR uint (1/2)  xv
    ).
  (* fractions ∈ (0,1], write needs 1, read any*)
  
  (* what is wrong with the spec above? *)

  Example anyR_if : _global "y" |-> uninitR uint 1
                   \\// (Exists xv:Z, _global "y" |-> primR uint 1 xv)
                 |--  _global "y" |-> anyR uint 1.
  
  Proof. rewrite bi.or_alt. go. destruct b; go. Qed.

  Remove Hints plogic.learnable_primR : br_opacity.

  Set Printing Width 100.
  (* The game of proof: gory details *)
  Lemma prf: denoteModule demo.module |-- foo_spec.
  Proof with (fold cQpc).
    verify_spec...
    (* ignore numbers here, focus on the bluish highlight *)
    (* meaning of goal view: [g289,367] [g437,696; c123,146]
[g713,796] [g437,696; c123,146]*)
    (* now symbolically execute code one AST node at a time *)
    do 4 run1; step... (* writing to y: demands full(1) ownership [g435,468;c129,131] [g435,468; g318,352;c129,131] *)
    (* cancel highlighted. 1BTC *)
    iFrame... (* y gone from wallet [g278,398]*)
    iIntros... (*[g361,397] write done: receive postcond of write. uniswap *)
    do 3 run1...
    (* eval f operand (argument) of + : [g524,549;c140,141] *)
    step... (* cant read uninit location [g399,401; g479,480; g527,528; g719,720] [g392,395; g487,488; g526,527]*)
                                                                                 
    iExists xv; (* instantiate v with xv, q with 1 *)
    work; [iExists (1/2:cQp.t); work|]... (* free transaction [g544,555; c142,143]  2nd op of + *)
    do 2 step... (* free! [g512,516; c141,142] *)
    step;
    unfold trim;
      step.
    iFrame... (* [g479,512;c138,140] [g403,439; g479,512;c138,140] *)
    Check anyR_if.
    rewrite -> (primR_anyR _ _ 0)... (* cancel [g403,437; g477,510;c138,140] *)
    iFrame...
    iIntros... (* write finished  [g439,454] *)
    do 10 step... (* code finished. post.  cancel y [g658,698; g481,522] *)
    iFrame...
  Abort. (* bug in spec *)

  (* summarize: rule of the game
how we lose:
- at end : postcond mismatch
- during symbolic code exec: wallet is too weak/underfunded to meet \pre of a c++ command/expression
   *)
  cpp.spec "foo()" as foo_spec2 with (
        \pre{xv:Z} _global "x" |-> primR uint (1/2) xv (* forall xv .. *)
        \post _global "x" |-> primR uint (1/2)  xv
    ).

  Lemma prf: denoteModule module |-- foo_spec2.
  Proof using.
    verify_spec'.
    go.
  Abort. (* game over even before executing the code fully *)
  
  Hint Resolve plogic.learnable_primR : br_opacity.

  cpp.spec "foo()" as foo_spec_correct with (
        \prepost{(xv:N) (q:Qp)} _global "x" |-> primR uint q xv
        \pre{yv:N} _global "y" |-> primR uint 1 yv
        \post _global "y" |-> primR uint 1 ((xv+1) `mod` (2^32))%N
      ).

  Lemma prf: denoteModule demo.module |-- foo_spec_correct.
  Proof.
    verify_spec.
    slauto.
  Qed.

  cpp.spec "sfoo()" as sfoo_spec with (
    \pre{xv:Z} _global "a" |-> primR "int" 1 xv
    \pre{yv:Z} _global "b" |-> primR "int" 1 yv
    \post _global "b" |-> primR "int" 1 ((xv+1))%Z ** _global "a" |-> primR "int" 1 xv
      ).

  (* what is wrong with the spec above? *)

  Lemma sprf: denoteModule demo.module |-- sfoo_spec.
  Proof.
    verify_spec'.
    slauto.
    provePure.
  Abort.
  
  cpp.spec "sfoo()" as sfoo_spec_correct with (
    \prepost{xv:Z} _global "a" |-> primR "int" 1 xv
    \pre [| (- 2 ^ (32 - 1) -1  ≤ xv ≤ 2 ^ (32 - 1) - 2) |]
    \pre{yv:Z} _global "b" |-> primR "int" 1 yv
    \post _global "b" |-> primR "int" 1 ((xv+1))
      ).

  Lemma sprf: denoteModule demo.module |-- sfoo_spec_correct.
  Proof.
    verify_spec'.
    slauto.
  Qed.

  (** *Under the hood: *)

  (** Pre and post conditions of specs are elements of type [mpred] *)

  Require Import stdpp.decidable.
  Import Znumtheory.
  Example isPrime (bv: Z): Prop := prime bv.
  Lemma proof: isPrime 3.
  Proof.  apply prime_3. Qed.
  
  (* `mpred` (memory predicates): they can implicitly
             talk about the current state of memory and ownership of memory locations.
        memory --> "state of the world"
   *)
  Example assertion1 (bv:Z): mpred := _global "b" |-> primR "int" 1 bv.

  Example embed (P:Prop) : mpred := [| P |].
  Example pureAssertion (bv:Z) : mpred := [| bv=0|].

  (** postcond of a function that guarantees to set variable b to a prime number:
     note the nondeterminism *)
  Example as2 :mpred := Exists (bv:Z),
      _global "b" |-> primR "int" 1 bv
      ** [| Znumtheory.prime bv |].

  Example conjP (P Q: Prop) := P /\ Q.
  Example conjmpred (P Q: mpred) := P ** Q.

  (** -> is logical implication, aka => in math textbooks *)
  Lemma propDupl (P:Prop) : P -> P /\ P. Proof. tauto. Qed.

  (** - analogous property doesnt hold in `mpred`.
      - ownership is like bitcoin: cannot doublespend*)
  Lemma doesNotHold1 (xv:Z):
    let own: mpred := _global "x" |-> primR "int" 1 xv in
    own |-- own ** own.
  Abort.

  (* knowledge can be freely duplicated, resources cannot *)
  Lemma propEmbedDupl (n:Z) :
    let o : mpred :=   [| isPrime n |] in o |-- o ** o.
  Proof. go. Qed.
          
  Example as11 (bv:Z) :mpred :=  _global "b" |-> primR "int" 1 bv.
  (** |-> : points_to *)
  (** left of |-> must be a memory location, of type [ptr] *)
  Example memLoc: ptr := _global "b".

  (** right of |-> must be a "memory representation", of type [Rep].
      Reps:
      - defines how some "mathematical" Coq object is laid out in memory
      - specify the amount of ownership

     The cpp2v logic axiomatizes representations of primitives:
             int/char/long/int*/...
   *)
  
  Example intRep (q:Qp) (x:Z) : Rep := primR "int" q x.

  Example UnboundedIntR (q:Qp) (x:Z) : Rep. Abort.
  (* [c3701,3779] *)
  
  Check primR.
  Print val. (* primitive values in C++. vs struct objects/arrays *)
  Example as3 (bv:Z): mpred := _global "b" |-> primR "int" 1 (Vint bv).
  Example as3elide (bv:Z): mpred := _global "b" |-> primR "int" 1 bv.
  Set Printing Coercions.
  Print as3elide.
  Unset Printing Coercions.

  Example ptrRep (q:Qp) (mloc: ptr) : Rep := primR "int*" q (Vptr mloc).
  (* [c198,206] *)

  cpp.spec "fooptr()" as ptrspec with
      (\pre _global "ptr" |-> anyR "int *" 1
       \post _global "ptr" |-> primR "int *" 1 (Vptr (_global "a")) 
      ).
  (* [c209,241] *)

  Lemma foopptr: denoteModule module |-- ptrspec.
  Proof.
    verify_spec'.
    slauto.
  Qed.
  (** "all" theorem statements in Coq have type Prop *)
  Example stm (L R : mpred): Prop := L |-- R.

  Lemma moreThanLogicalImpl :
    _global "x" |-> primR "int" (1/3) 0 |--
    _global "x" |-> primR "int" (1/2) 0.
  Abort. (* not provable *)
  
  Print ptrspec.
  Example specstar : WpSpec mpredI val val :=
    \pre _global "x" |-> primR "int" (1/3) 0
    \pre _global "y" |-> primR "int" (1/3) 0
    \post emp.
  
  Example specstarEquiv : WpSpec mpredI val val :=
    \pre _global "x" |-> primR "int" (1/3) 0
         ** _global "y" |-> primR "int" (1/3) 0
    \post emp.

  (** ** functions that take arguments *)
  
  (* now ownership received/returned *)
  cpp.spec "gcd(unsigned int, unsigned int)" as gcd_spec with (
     \arg{av:Z} "a" (Vint av) (* forall av, ... *)
     \arg{bv:Z} "b" (Vint bv)
     \post [Vint (Z.gcd av bv)] emp
      ).

  (**  we pass most args by reference ... *)
  cpp.spec "gcd(const unsigned int&, const unsigned int&, unsigned int&)"
    as gcd2_spec with (
    \arg{ap:ptr} "a" (Vptr ap)
    \prepost{(qa:Qp) (av:Z)} ap |-> primR uint qa av
    \arg{bp:ptr} "b" (Vptr bp)
    \prepost{(qb:Qp) (bv:Z)} bp |-> primR uint qb bv
    \arg{resultp:ptr} "gcd_result" (Vptr resultp)
    \pre resultp |-> anyR uint 1
    \post resultp |-> primR uint 1 (Z.gcd av bv)
      ).
  (* [g1,1; c375,385] *)

  (** \prepost  in sequential code, ..., but in concurrent code ...*)

  Lemma primr_split_half (p:ptr) ty (q:Qp) v :
    p|-> primR ty q v -|-
      (p |-> primR ty (q/2) v) ** p |-> primR ty (q/2) v.
  Proof. apply primr_split. Qed.
  
  (** parallel_gcd_lcm in demo.cpp *)
  (** diagram *)
  
  
  (** *Demo: read-read concurrency using fractional permissions *)

  (*
  Step 1: Initial Resource Ownership
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

*)  

  cpp.spec "parallel_gcd_lcm(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)"
   as par_gcd_lcm_spec with (
   \arg{ap} "a" (Vptr ap)
   \prepost{(qa:Qp) (av:Z)} ap |-> primR uint qa av
   \arg{bp} "b" (Vptr bp)
   \prepost{(qb:Qp) (bv:Z)} bp |-> primR uint qb bv
   \arg{gcd_resultp} "gcd_result" (Vptr gcd_resultp)
   \pre gcd_resultp |-> anyR uint 1
   \arg{lcm_resultp} "lcm_result" (Vptr lcm_resultp)
   \pre lcm_resultp |-> anyR uint 1
   \pre[| 0<bv \/ 0<av |] (* why is this needed? *)
   \post gcd_resultp |-> primR uint 1 (Z.gcd av bv) ** lcm_resultp |->
         (if decide (av*bv < 2^32)
          then primR uint 1 (Z.lcm av bv)
          else Exists garbage, primR uint 1 garbage)
      ). (* [c1290,1312] *)
  
  Definition ThreadR (lamStructName: core.name) (P Q : mpred) : Rep. Proof. Admitted.
  Definition ThreadStartedR (lamStructName: core.name) (Q : mpred) : Rep. Proof. Admitted.
  Definition ThreadDoneR (lamStructName: core.name) : Rep. Proof. Admitted.

  
  Definition ThreadConstructor (lamStructName: core.name) (this:ptr): WpSpec mpredI val val :=
    \arg{lambdap:ptr} "lambda" (Vptr lambdap)
    \prepost{lamStructObjOwnership} lambdap |-> lamStructObjOwnership
    \pre{taskPre taskPost}
      specify {| info_name :=  (Nscoped lamStructName taskOpName);
                info_type := tMethod lamStructName QC "void" [] |}
           (fun (this:ptr) =>
              \prepost this |-> lamStructObjOwnership
                \pre taskPre
                \post taskPost)
    
    \post this |-> ThreadR lamStructName taskPre taskPost. (* [c1231,1285] *)

  Definition start (lamStructName: core.name) (this:ptr)
       :WpSpec mpredI val val :=
    \pre{taskPre taskPost} this |-> ThreadR lamStructName taskPre taskPost
    \pre taskPre (* NOT a prepost *)
    \post this |-> ThreadStartedR lamStructName taskPost. (* [c570,582] *)

  Definition join (lamStructName: core.name) (this:ptr)
       : WpSpec mpredI val val :=
    \pre{taskPost} this |-> ThreadStartedR lamStructName taskPost
    \post taskPost ** this |-> ThreadDoneR lamStructName.

    Definition ThreadDtor (lamStructName: core.name) (this:ptr)
       : WpSpec mpredI val val :=
    \pre this |-> ThreadDoneR lamStructName
    \post emp.

    (** protocol enforced, concurrency clarified: cannot split ThreadR *)

  Definition thread_constructor (lamStructTyName: core.name) :=
  specify
    {|
      info_name :=
        Nscoped (Ninst "Thread" [Atype (Tnamed lamStructTyName)]) (Nctor [Tref (Tconst (Tnamed lamStructTyName))]);
      info_type :=
        tCtor (Ninst "Thread" [Atype (Tnamed lamStructTyName)])
          [Tref (Tconst (Tnamed lamStructTyName))]
    |}
    (ThreadConstructor lamStructTyName).

  Definition thread_destructor (lamStructTyName: core.name) :=
  specify
    {|
      info_name :=
        Nscoped (Ninst "Thread" [Atype (Tnamed lamStructTyName)]) Ndtor;
      info_type :=
        tDtor (Ninst "Thread" [Atype (Tnamed lamStructTyName)])
    |}
    (ThreadDtor lamStructTyName).
  
  Definition thread_start (lamStructTyName: core.name) :=
  specify
    {|
      info_name :=
        Nscoped (Ninst "Thread" [Atype (Tnamed lamStructTyName)]) (Nfunction function_qualifiers.N "start" []);
      info_type :=
        tMethod (Ninst "Thread" [Atype (Tnamed lamStructTyName)]) QM "void" []
    |}
    (start lamStructTyName).

  Definition thread_fork_join (lamStructTyName: core.name) :=
  specify
    {|
      info_name :=
        Nscoped (Ninst "Thread" [Atype (Tnamed lamStructTyName)]) (Nfunction function_qualifiers.N "join" []);
      info_type :=
        tMethod (Ninst "Thread" [Atype (Tnamed lamStructTyName)]) QM "void" []
    |}
    (join lamStructTyName).
  
  Definition thread_class_specs lamStructName :=
    thread_constructor lamStructName **
    thread_start lamStructName **
    thread_fork_join lamStructName **
    thread_destructor lamStructName.
   
  Existing Instance UNSAFE_read_prim_cancel.
  #[global] Instance : forall ty P Q, Observe (reference_toR (Tnamed (Ninst "Thread" [Atype (Tnamed ty)]))) (ThreadR ty P Q).
  Proof. Admitted.
  #[global] Instance : forall ty Q, Observe (reference_toR (Tnamed (Ninst "Thread" [Atype (Tnamed ty)]))) (ThreadStartedR ty Q).
  Proof. Admitted.
  #[global] Instance : forall ty, Observe (reference_toR (Tnamed (Ninst "Thread" [Atype (Tnamed ty)]))) (ThreadDoneR ty).
  Proof. Admitted.
  #[global] Instance : forall ty , LearnEq2 (ThreadR ty) := ltac:(solve_learnable).
  #[global] Instance : forall ty , LearnEq1 (ThreadStartedR ty) := ltac:(solve_learnable).

  (* TODO: delete?*)
  #[global] Instance obss (pp:ptr) ty P Q: Observe (reference_to (Tnamed (Ninst "Thread" [Atype (Tnamed ty)])) pp)
                                             (pp |-> ThreadR ty P Q). 
  Proof. Admitted.

  #[global] Instance obsss (pp:ptr) ty Q: Observe (reference_to (Tnamed (Ninst "Thread" [Atype (Tnamed ty)])) pp)
                                             (pp |-> ThreadStartedR ty Q). 
  Proof. Admitted.
  


  Lemma par: denoteModule module
             |-- par_gcd_lcm_spec.
  Proof using MODd.
    verify_spec.
    go.
    (* missing spec of Thread Constructor *)
  Abort.

  Set Nested Proofs Allowed.

  cpp.spec (Nscoped 
              "parallel_gcd_lcm(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)::@0" Ndtor)  as lamdestr inline.
  
  Lemma par: denoteModule module
               ** (thread_class_specs "parallel_gcd_lcm(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)::@0")
               ** gcd2_spec (* proven later in this file *)
             |-- par_gcd_lcm_spec.
  Proof using MODd with (fold cQpc).
    unfold thread_class_specs.
    verify_spec'.
    slauto.
    rename a into lam...
    (* call to [ThreadConstructor] just happened  [c1384,1463]*)
    aggregateRepPieces lam.
    iExists (     gcd_resultp |-> anyR uint 1
               ** ap |-> primR uint (qa/2) av
               ** bp |-> primR uint (qb/2) bv)...
    instWithPEvar taskPost... (* taskPost: infer it automatically, optimally *)
    slauto; iSplitL ""...
    (* scroll up: remaining precond of [ThreadConstructor] *)
    { verify_spec'.
      go... (* any postcond choice must be implied by currently available context => it is the strongest postcond *)
      erefl.
      (* inferring both \pre and \post: no optimality guarantee *)
    }
    unhideAllFromWork.
    iIntrosDestructs.
    subst taskPost... (* now we have the postcond of Thread constructor *)
    
    do 11 run1... (* [g2350,2357; c1469,1479]. *)
    Remove Hints primR_split_C: br_opacity.
    step... (* preconditions of [start]*)
    do 2 step... (* lost gcd_resultp. *)
    rewrite (primr_split ap);
    rewrite (primr_split bp)...
    run1... (* got only TheadStartedR back,lost ownership gcd_resultp, 1/2 of a,b. 1/2 suffices for a,b. next: operands of * *)
    Hint Resolve primR_split_C: br_opacity.

    name_locals.
    do 7 run1... (* call to [join] [g2408,2415; c1558,1567] *)
    run1... (* back: gcd_resultp ownership, updated value. other halfs:imp!. *)
    do 4 run1;
    do 1 (step;[slauto|]); step; step;[slauto|]... (*/ [g2257,2261; c1591,1592] *)
    step...
    pose proof (Z.gcd_eq_0 av bv);
    pose proof (Z.gcd_nonneg av bv);
    go. (* code finished, remaining postcond:  *)
    case_decide.
    2:{ (* overflow case*) go. }
    {
       (* uint *: % 2^32 *)
      icancel (cancel_at lcm_resultp);[| go]. 
      do 2 f_equiv. (* L is what c++ semantics computed, R is what the postcondition requires *)
      Arith.remove_useless_mod_a.
      unfold Z.lcm.
      rewrite -> Z.lcm_equiv1 by arith.
      rewrite -> Z.abs_eq by (apply Z_div_nonneg_nonneg; try arith).
      rewrite Z.quot_div_nonneg; arith.
    }
  Qed.

  (** Summary so far:

- start thread: partitioning resources
- fractional permissions: split for concurrent reads
- many more ways to split, e.g. write/write, write/read concurrency
- enforce complex protocols:
      - one thread can only increment a counter, another can only decrement

*)

  (** another source of complexity in proofs: loops
*)
  Lemma gcd_proof: denoteModule module |-- gcd_spec.
  Proof with (fold cQpc).
    verify_spec.
    slauto...
    rename av into av_init.
    rename bv into bv_init.
    wp_while  (fun _ =>
             (Exists av' bv' : Z,
                 [| 0 ≤ av' ≤ 2 ^ 32 - 1 |]
                 **[| 0 ≤ bv' ≤ 2 ^ 32 - 1 |]
                 ** a_addr |-> primR Tu32 1 (Vint av')
                 ** b_addr |-> primR Tu32 1 (Vint bv')
                 ** [| Z.gcd av' bv' = Z.gcd av_init bv_init |]))...
    slauto.
    ren a_addr av'.
    ren b_addr bv'. (* context is now generalized to be the loopinv: av --> av', but H *)
    wp_if; intros.
    { (* loop cond true: exec body:  *)
      do 10 run1. rename addr into temp_addr.
      (* reached end of loop body, asked to: 1) return FULL ownership of temp 2) reistablish loopinv *)
      (* av'0 := bv', bv'0:= av' `mod` bv' *)
      slauto. (* gcd of new values of a b = gcd of original a b *)
      Search Z.gcd (_ `mod` _)%Z.
      aac_rewrite Z.gcd_mod; arith.
    }

    { (* loop condition is false =>  bv'=0  and loop terminates*)
      slauto...
      (* C++ computes av' as return value but postcondition requires... *)
      Check Z.gcd_0_r_nonneg.
      (* H comes from the loopinv *)
      aac_rewriteh Z.gcd_0_r_nonneg in H;[| assumption]. subst. go.
    }
  Qed.

  Lemma gcd2_proof: denoteModule module |-- gcd2_spec.
  Proof.
    verify_spec'.
    wapply gcd_proof. go.
  Qed.

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
  

  Check Z.gcd_comm.
  Check Z.gcd_assoc.

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

  Lemma fold_split {A:Type} (f: A->A->A) (c: Commutative (=) f) (asoc: Associative (=) f)
    (id: A) (lid: LeftId (=) id f) (l: list A) (lSplitSize: nat):
    fold_left f l id =
      f (fold_left f (firstn lSplitSize l) id)
        (fold_left f (skipn  lSplitSize l) id).
  Proof.
    rewrite <- (take_drop lSplitSize) at 1.
    rewrite fold_left_app.
    rewrite fold_id.
    aac_reflexivity.
  Qed.

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


Require Import monad.proofs.exec_specs.
Print execute_block_simpler.

(** Next tutorial sessions

Next:
- more expressive ways to split ownership: read-write/ write/write-concurrency: SPSCQueue: one thread can only increment one can only decrement
- deeper dive into proofs of execute_block

After next:
- pick a module in our codebase, write specs, sketch high-level correctness proof

Overall goal:
- write specs in Coq.
  + precise documentation
  + tools to either prove the spec, or give you counterexample
  + when bug happens, can focus on unprover parts

 *)

  Lemma doubleSpending: _global "x" |-> primR "int" 1 0 ** _global "x" |-> primR "int" 1 0|-- [| False |].
  Proof. Abort.
  
  Lemma okSpending: _global "x" |-> primR "int" (1/2) 0 ** _global "x" |-> primR "int" (1/2) 0|--  _global "x" |-> primR "int" 1 0.
  Proof. Abort.
  Lemma duplTypePtr (ap:ptr): type_ptr uint ap |-- type_ptr uint ap ** type_ptr uint ap.
  Proof. go. Qed.
  Lemma duplSpec (ap:ptr): gcd_spec |-- gcd_spec ** gcd_spec.
  Proof. go. Qed.
                                          
  Example nestedArrayR (rows: list (list Z)) (p:ptr) (q:Qp): mpred :=
p|->arrayR "int*"
      (fun mrow: list Z => Exists rowBase:ptr, primR "int*" q (Vptr rowBase)
                            ** pureR (rowBase |-> arrayR "int" (fun i:Z => primR uint q i) mrow))
      rows.
    
End with_Sigma.
(*

- map C-q to gpts new highlighter that centers c++ findow
- remap c=q to a new function that would advance green region to the next ... if a comment end is encountered before the next hightlight region
- add c++ offsets to the Thread constructor spec, gcd specs
- add 
- remove all occurrences nat: define length, take, split, arrayR_split in terms of nat
- execute_block spec: narrative and prettify
- remaining goal pprinter
- make fast the proof of parall_gcd: getting to the 2 breakpoints there
- check arg names
- S n by 1+n
- pretty printing of goal: ltac.
- remove type in array offset
- In to ∈
- docker image

 *)


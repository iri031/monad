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
Ltac aac_norm :=
  aac_normalise;
  repeat match goal with
    | H: _ |- _ => aac_normalise in H
    end.
    Hint Rewrite Nat2Z.inj_div : syntactic.
    Hint Rewrite Nat2Z.inj_sub using lia: syntactic.
    Hint Rewrite Z.quot_div_nonneg using lia : syntactic.

Ltac slauto := misc.slauto1.
Ltac arith := (try aac_norm); Arith.arith_solve.
Ltac ren addr v :=
  IPM.perm_left
    ltac:(fun L n =>
            match L with
              addr |-> primR _ _ (Vint ?x) => rename x into v
            end
         ).

Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
  Context  {MODd : demo.module ⊧ CU}.
  Definition cQpc := cQp.mk false.
  Coercion cQpc : Qp >-> cQp.t.
  (* questions policy slide *)

  Disable Notation intR.
  Disable Notation uintR.
  Open Scope Z_scope.
  Notation uint := "unsigned int"%cpp_type.
Set Nested Proofs Allowed.
Lemma cqpp2 q: (cQp.scale (1 / 2) (cQp.mut q)) = (cQp.mut (q / 2)).
Proof using.    
      rewrite cQp.scale_mut;
      f_equiv;
      destruct q; simpl in *.
    f_equal.
      solveQpeq;
        solveQeq.
Qed.
    
  
  Lemma primR2_anyR : ∀ t (q:Qp) (v:val) (p:ptr),
      p|-> primR t (q/2) v ** p|->primR t (q/2) v  |-- p|->anyR t q.
  Proof. Admitted.
  Definition primR2_anyRC := [CANCEL] primR2_anyR.
  Hint Resolve primR2_anyRC: br_opacity.
  Hint Resolve array_combine_C: br_opacity.
  Hint Rewrite @length_drop: syntactic.

  
  (* open foo in demo.cpp *)
  cpp.spec "foo()" as foo_spec with (
        \pre{xv:Z} _global "x" |-> primR uint 1  xv (* forall xv .. *)
        \pre _global "y" |-> anyR uint 1
        \post _global "y" |-> primR uint 1 (xv+1)
              ** _global "x" |-> primR uint 1  xv
      ).
  (* what is wrong with the spec above? *)

  Example anyy : _global "y" |-> uninitR uint 1
                   \\// (Exists xv:Z, _global "y" |-> primR uint 1 xv)
                 |--  _global "y" |-> anyR uint 1.
  
  Proof. rewrite bi.or_alt. go. destruct t; go. Qed.

  Remove Hints plogic.learnable_primR : br_opacity.

  Set Printing Width 110.
  (* small stepping through the proof *)
  Lemma prf: denoteModule demo.module |-- foo_spec.
  Proof with (fold cQpc).
    verify_spec...
    (* meaning of goal view. [g395,492] [g589,837; c127,141] [g880,970] *)  
    do 4 run1...
    (* eval first operand (argument) of + : [g657,685;c135,136] *)
    step... (* [g592,601;g622,633;g662,663], [g608,620; g659,661], [g496,547;g622,663] [g545,547;g592,601;g662,663] [g608,620; g659,661] *)
                                                                                 
    iExists xv. (*  *)
    work; [iExists (1:cQp.t); work|].
    step. (* evalualte the second operand of +, which is the constant 1 *)
    step. (* evaluate the binary operator + *)
    step.
    unfold trim. 
    step. (* + evaluated, now process the write to y. not the pre and post of write *)
    (* - pre + post *)
    do 10 step.
    (* highlight cancels *)
    work.
  Abort.

  Hint Resolve plogic.learnable_primR : br_opacity.

  cpp.spec "foo()" as foo_spec_correct with (
        \prepost{xv:N} _global "x" |-> primR uint 1 xv
        \pre{yv:N} _global "y" |-> primR uint 1 yv
        \post _global "y" |-> primR uint 1 ((xv+1) `mod` (2^32))%N
      ).

  Lemma prf: denoteModule demo.module |-- foo_spec_correct.
  Proof.
    verify_spec.
    slauto.
  Qed.

  cpp.spec "sfoo()" as sfoo_spec with (
        \prepost{xv:Z} _global "a" |-> primR "int" 1 xv
        \pre{yv:N} _global "b" |-> primR "int" 1 yv
        \post _global "b" |-> primR "int" 1 ((xv+1))%Z
      ).

  (* what is wrong with the spec above? *)

  Lemma sprf: denoteModule demo.module |-- sfoo_spec.
  Proof.
    verify_spec'.
    slauto.
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

  (** Pre and post conditions of specs are elements of type [mpred]: *)

  Require Import stdpp.decidable.
  Import Znumtheory.
  Example isPrime (bv: Z): Prop := prime bv.
  #[global] Instance primeDec z: Decision (prime z) := ltac:(apply prime_dec).
  Lemma proof: isPrime 3.
  Proof.  apply prime_3. Qed.
  
  (* `mpred` (memory predicates): they can implicitly
             talk about the current state of memory and ownership of locations *)
  Example assertion1 (bv:Z): mpred := _global "b" |-> primR "int" 1 bv.

  Example embed (P:Prop) : mpred := [| P |].
  Example pureAssertion (bv:Z) : mpred := [| bv=0|].

  (** postcond of a function that guarantees to set variable b to a prime number:
     note the nondeterminism *)
  Example as2 :mpred := Exists (bv:Z), _global "b" |-> primR "int" 1 bv ** [| Znumtheory.prime bv |].

  Example conjP (P Q: Prop) := P /\ Q.
  Example conjmpred (P Q: mpred) := P ** Q.

  (** -> is logical implication, aka => in math textbooks *)
  Lemma propDupl (P:Prop) : P -> P /\ P. Proof. tauto. Qed.

  (** - analogous property doesnt hold in `mpred`.
      - ownership is like bitcoin: cannot doublespend*)
  Lemma doesNotHold1 (xv:Z):
    let own:= _global "x" |-> primR "int" 1 xv in
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

     The cpp2v logic axiomatizes representations of primitives: int/char/long/int*/...
   *)
  
  Example intRep (q:Qp) (x:Z) : Rep := primR "int" q x.

  Example UnboundedR (q:Qp) (x:Z) : Rep. Abort.
  
  Check primR.
  Print val. (* primitive values in C++. vs struct objects/arrays ...: not directly passed *)
  Example as3 (bv:Z): mpred := _global "b" |-> primR "int" 1 (Vint bv).
  Example as3elide (bv:Z): mpred := _global "b" |-> primR "int" 1 bv.
  Set Printing Coercions.
  Print as3elide.
  Unset Printing Coercions.

  Example ptrRep (q:Qp) (mloc: ptr) : Rep := primR "int*" q (Vptr mloc).

  (* open demo.cpp *)
  cpp.spec "fooptr()" as ptrspec with
      (\pre _global "ptr" |-> anyR "int *"1
       \post _global "ptr" |-> primR "int *" 1 (Vptr (_global "a")) 
      ).

  Lemma foopptr: denoteModule module |-- ptrspec.
  Proof.
    verify_spec'.
    slauto.
  Qed.
  (** "all" theorem statements in Coq have type Prop *)
  Example stm (L R : mpred): Prop := L |-- R.

  Lemma moreThanLogicalImpl :
    _global "x" |-> primR "int" (1/3) 0 |-- _global "x" |-> primR "int" (1/2) 0.
  Abort. (* not provable *)
  
  Print ptrspec.
  Example specstart : WpSpec mpredI val val :=
    \pre _global "x" |-> primR "int" (1/3) 0
    \pre _global "y" |-> primR "int" (1/3) 0
    \post emp.
  
  Example specstart2 : WpSpec mpredI val val :=
    \pre _global "x" |-> primR "int" (1/3) 0
         ** _global "y" |-> primR "int" (1/3) 0
      \post emp.

  (* now ownership received/returned *)
  cpp.spec "gcd(unsigned int, unsigned int)" as gcd_spec with (
        \arg{av:Z} "a" (Vint av) (* forall av, ... *)
        \arg{bv:Z} "b" (Vint bv)
        \post [Vint (Z.gcd av bv)] emp
      ).

  (** in monad, codebase, we pass most args (usually bulky objects) by reference ... *)
  cpp.spec "gcd(const unsigned int&, const unsigned int&, unsigned int&)" as gcd2_spec with (
        \arg{ap:ptr} "a" (Vptr ap)
        \prepost{(qa:Qp) (av:Z)} ap |-> primR uint qa av
        \arg{bp:ptr} "b" (Vptr bp)
        \prepost{(qb:Qp) (bv:Z)} bp |-> primR uint qb bv
        \arg{resultp:ptr} "gcd_result" (Vptr resultp)
        \pre resultp |-> anyR uint 1
        \post resultp |-> primR uint 1 (Z.gcd av bv)
      ).

  (** \prepost  in sequential code, ..., but in concurrent code ...*)

  Lemma primr_split_half (p:ptr) ty (q:Qp) v :
    p|-> primR ty q v -|- (p |-> primR ty (q/2) v) ** p |-> primR ty (q/2) v.
  Proof. apply primr_split. Qed.
  
  (** parallel_gcd_lcm in demo.cpp *)
  (** diagram *)
  
  
(** *Demo: read-read concurrency using fractional permissions *)
  
  Definition ThreadR (lamStructName: core.name) (P Q : mpred) : Rep. Proof. Admitted.
  Definition ThreadStartedR (lamStructName: core.name) (Q : mpred) : Rep. Proof. Admitted.
  Definition ThreadDoneR (lamStructName: core.name) : Rep. Proof. Admitted.
  
  Definition ThreadConstructor (lamStructName: core.name) (this:ptr): WpSpec mpredI val val :=
    \arg{lambdap:ptr} "lambda" (Vptr lambdap)
    \prepost{lamStructObjOwnership} lambdap |-> lamStructObjOwnership (* ownerhsip of fields othe lambda struct *)
    \pre{taskPre taskPost}
      specify {| info_name :=  (Nscoped lamStructName taskOpName);
                info_type := tMethod lamStructName QC "void" [] |}
           (fun (this:ptr) =>
              \prepost this |-> lamStructObjOwnership
                \pre taskPre
                \post taskPost)
    
    \post this |-> ThreadR lamStructName taskPre taskPost.

  Definition ThreadDtor (lamStructName: core.name) (this:ptr): WpSpec mpredI val val :=
    \pre this |-> ThreadDoneR lamStructName
    \post emp.
  
  Definition start (lamStructName: core.name) (this:ptr): WpSpec mpredI val val :=
    \pre{P Q} this |-> ThreadR lamStructName P Q
    \pre P
    \post this |-> ThreadStartedR lamStructName Q.

  Definition join (lamStructName: core.name) (this:ptr): WpSpec mpredI val val :=
    \pre{Q} this |-> ThreadStartedR lamStructName Q
    \post Q ** this |-> ThreadDoneR lamStructName.

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
  
  (*TODO: rename to just start? *)
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
  
  cpp.spec (Nscoped 
              "parallel_gcd_lcm(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)::@0" Ndtor)  as lamdestr
                                                                                                                          inline.

  cpp.spec "parallel_gcd_lcm(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)" as par_gcd_lcm_spec with
      (
        \arg{ap} "a" (Vptr ap)
        \prepost{(qa:Qp) (av:Z)} ap |-> primR uint qa av
        \arg{bp} "b" (Vptr bp)
        \prepost{(qb:Qp) (bv:Z)} bp |-> primR uint qb bv
        \arg{gcdrp} "gcd_result" (Vptr gcdrp)
        \pre gcdrp |-> anyR uint 1
        \arg{lcmrp} "lcm_result" (Vptr lcmrp)
        \pre lcmrp |-> anyR uint 1
        \pre[| 0<bv \/ 0<av |] (* why is this needed? *)
        \post gcdrp |-> primR uint 1 (Z.gcd av bv)
              ** (if decide (av*bv < 2^32) then
                  lcmrp |-> primR uint 1 (Z.lcm av bv)
                  else Exists garbage3, lcmrp |-> primR uint 1 garbage3)
      ).                              (*lcmrp |-> primR uint 1 ((av*bv) % 2^32) *)

  Lemma par: denoteModule module
             |-- par_gcd_lcm_spec.
  Proof using MODd.
    verify_spec.
    go.
    (* missing spec of Thread Constructor *)
  Abort.

      Set Nested Proofs Allowed.
      Ltac erefl :=
        unhideAllFromWork;
        match goal with
          H := _ |- _ => subst H
        end;
        iClear "#";
        iStopProof; reflexivity.
      Ltac unhideAllFromWork :=  tactics.unhideAllFromWork;
                                 try match goal with
                                   H := _ |- _ => subst H
                                 end.
      #[global] Instance : forall ty , LearnEq2 (ThreadR ty) := ltac:(solve_learnable).

      Ltac instWithPEvar name :=
      match goal with
      | |- environments.envs_entails _ (@bi_exist _ ?T _) =>
          evar (name:T);
          iExists name;
          let hname := fresh name "P" in
          hideFromWorkAs name hname
      end.

  Lemma par: denoteModule module
               ** (thread_class_specs "parallel_gcd_lcm(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)::@0")
               ** gcd2_spec
             |-- par_gcd_lcm_spec.
  Proof using MODd.
    unfold thread_class_specs.
    verify_spec'.
    slauto. (* call to [ThreadConstructor] just happened *)
    fold cQpc.
    aggregateRepPieces gcdLambda_addr. (*TODO shorten gcdLambda *)
    iExists (gcdrp |-> anyR uint 1 ** ap |-> primR uint (qa/2) av ** bp |-> primR uint (qb/2) bv). (* taskPre. look at code *)
    instWithPEvar taskPost. (* taskPost: infer it automatically, optimally *)
    slauto; iSplitL "".
    (* 2 goals:
       - prove that the lambda function satisfies the spec with pre:=taskPre and post:=taskPost (TBD)
       - continue with the code after the Thread constructor, with the \post of the constructor 
     *)
    { verify_spec'.
      go. (* any postcond choice must be implied by currently available context => it is the strongest postcond *)
      erefl.
      (* inferring both \pre and \post: no optimality guarantee *)
    }
    unhideAllFromWork.
    iIntrosDestructs.
    do 5 run1. (* call to  [start]. *)
    Remove Hints primR_split_C: br_opacity.
    step. (* needs 1) ownership of thead object 2) prev. chosen \pre. the latter is not returned  *)
    do 2 step.
    fold cQpc.
    rewrite (primr_split ap).
    rewrite (primr_split bp).
    fold cQpc.
    run1. (* evaluating operands for *. lost ownership gcdrsp, 1/2 of a,b. 1/2 suffices for a,b *)
    Hint Resolve primR_split_C: br_opacity.
    
    do 7 run1. (* call to join() *)
    run1. (* got back ownership of gcdrp, now it holds the result of gcd. also other halfs. need to return full *)
    do 3 run1. fold cQpc.
    do 2 (step;[slauto|]). step. do 1 (step;[slauto|]). (* next: / *)
    step.
    Search (Z.gcd _ _ = 0 )%Z.
    pose proof (Z.gcd_eq_0 av bv).
    pose proof (Z.gcd_nonneg av bv).
    go.
    case_decide.
    2:{ (* overflow case*) go. }
    {
       (* uint *: % 2^32 *)
      icancel (cancel_at lcmrp);[| go]. 
      do 2 f_equiv. (* L is what c++ semantics computed, R is what the postcondition requires *)
      Arith.remove_useless_mod_a.
      unfold Z.lcm.
      rewrite -> Z.lcm_equiv1 by arith.
      rewrite -> Z.abs_eq by (apply Z_div_nonneg_nonneg; try arith).
      rewrite Z.quot_div_nonneg; arith.
    }
  Qed.

  (** Summary so far:

- saw how forking a thread requires partitioning resources into the 2 threads
- fractional permissions allow splitting ownership into pieces for concurrent reading
   - simplest way to split ownership
- the main strength of iris SL is the richness of the ways in which we can express how ownership can be split into multiple threads
- main innovation of iris separation logic (test of time award):
    - enforce protocls: exactly specify how/whether a thread can modify a datastructure.
      - one thread can only increment a counter, another can only decrement

another source of complexity in proofs: loops
*)

  Lemma gcd_proof: denoteModule module |-- gcd_spec.
  Proof.
    verify_spec.
    slauto.
    wp_while  (fun _ => (Exists av' bv' : Z,
                      [| 0 ≤ av' ≤ 2 ^ 32 - 1 |] **
                      [| 0 ≤ bv' ≤ 2 ^ 32 - 1 |] **
                      a_addr |-> primR Tu32 (cQp.mut 1) (Vint av') **
                      b_addr |-> primR Tu32 (cQp.mut 1) (Vint bv') ** [| Z.gcd av' bv' = Z.gcd av bv |])).
    slauto.
    ren a_addr av'.
    ren b_addr bv'. (* context is now generalized to be the loopinv: av --> av', but H *)
    wp_if; intros.
    { (* loop cond true: exec body:  *)
      do 10 run1. rename addr into temp_addr.
      (* reached end of loop body, asked to: 1) return FULL ownership of temp 2) reistablish loopinv *)
      (* av'0 := bv', bv'0:= av' `mod` bv' *)
      slauto.
      Check Z.gcd_mod.
      aac_rewrite Z.gcd_mod; arith.
    }

    { (* loop condition is false =>  bv'=0  and loop terminates*)
      slauto.
      (* C++ computes av' as return value but postcondition requires... *)
      simplPure.
      Check Z.gcd_0_r_nonneg.
      aac_rewriteh Z.gcd_0_r_nonneg in H; subst; try arith.
      go.
    }
  Qed.

  Lemma gcd2_proof: denoteModule module |-- gcd2_spec.
  Proof.
    verify_spec'.
    wapply gcd_proof. go.
  Qed.

  Lemma pos (p:ptr) (v:Z) : p |-> primR uint 1 v |-- [| 0 <=v |] ** p |-> primR uint 1 v.
  Proof.
    go.
  Qed.
  
  (* TODO: lemma to unroll arrayR for 3 elements *)

  (* parallelization: *)
  Check Z.gcd_comm.
  Check Z.gcd_assoc.

  (** *Parallelizing a sequence of operations
- e.g. sequence of operations monad transactions.
- Commutativivity enables much greater degree of parallelization [SLIDE]
- gcd of a list of numbers.
- arrayR
*)

  Definition gcdl_spec_core : WpSpec mpredI val val :=
        \arg{numsp:ptr} "nums" (Vptr numsp)
        \prepost{(l: list Z) (q:Qp)} numsp |-> arrayR uint (fun i:Z => primR uint q i) l
        \arg "size" (Vint (length l))
        \post [Vint (fold_left Z.gcd l 0)] emp.

  Example arrayR3 (p:ptr) (n1 n2 n3: Z) (q: Qp):
    p |-> arrayR uint (fun i:Z => primR uint q i) [n1;n2;n3]
      -|- ( valid_ptr (p .[ uint ! 3 ])
              ** p |-> primR uint (cQp.mut q) n1
              ** p .[ uint ! 1 ] |-> primR uint (cQp.mut q) n2
              ** p .[ uint ! 2 ] |-> primR uint (cQp.mut q) n3).
  Proof.
    repeat rewrite arrayR_cons.
    repeat rewrite arrayR_nil.
    iSplit; go;
    repeat rewrite o_sub_sub;
    closed.norm closed.numeric_types; go.
  Abort.

  Example fold_left_gcd (n1 n2 n3: Z) :
    fold_left Z.gcd [n1;n2;n3] 0 =  Z.gcd (Z.gcd (Z.gcd 0 n1) n2) n3.
  Proof. reflexivity. Abort.
  
  Check Z.gcd_0_r_nonneg.
  
  cpp.spec "gcdl(unsigned int*, unsigned int)" as gcdl_spec with (gcdl_spec_core).
  cpp.spec "parallel_gcdl(unsigned int*, unsigned int)" as parallel_gcdl_spec with (gcdl_spec_core).


  Hint Rewrite @fold_left_app: syntactic.

    Disable Notation take.
    Disable Notation drop.
    Disable Notation "`div`" (all).
  
  Lemma gcdl_proof: denoteModule module |-- gcdl_spec.
  Proof using MODd.
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
      rename t into iv.
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
      rename t into iv.
      assert (iv=length l) as Heq by lia.
      subst.
      autorewrite with syntactic.
      go.
    }
  Qed.
  
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
  
      Compute (Z.quot (-5) 4).
      Compute (Z.div (-5) 4).
      Set Printing Coercions.
      Set Default Goal Selector "!".
  cpp.spec (Nscoped 
              "parallel_gcdl(unsigned int*, unsigned int)::@0" Ndtor)  as lam2destr  inline.


  Lemma pgcdl_proof: denoteModule module
                       ** (thread_class_specs "parallel_gcdl(unsigned int*, unsigned int)::@0")
                       |-- parallel_gcdl_spec.
  Proof using MODd.
    unfold thread_class_specs.
    verify_spec'.
    wapply gcdl_proof. work.
    wapply gcd_proof. work.
    wapplyObserve  obsUintArrayR.
    eagerUnifyU. work.
    progress slauto.
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
    rewrite -> arrayR_split with (i:=((length l)/2)%nat) (xs:=l) by lia.
    go. (* array ownership spit into 2 pieces *)
    progress slauto.
    revertAdrs constr:([numsp; resultl_addr; nums_addr; mid_addr]).
    repeat rewrite bi.wand_curry.
    intantiateWand.
    instWithPEvar taskPost.
    go.

    iSplitL "".
    { verify_spec'.
      slauto.
      iExists _. eagerUnifyU. (* Hint already there*)
      go.
      erefl.
    }
    unhideAllFromWork.
    slauto.
    iExists _. eagerUnifyU. 
    slauto.
    wapply arrayR_combinep. eagerUnifyU.
    slauto. (* c++ semantics computes ... postcond requires *)
    icancel (cancel_at p);[| go].
    do 2 f_equiv.
    symmetry.
    apply fold_split_gcd.
    Check fold_split.
    auto.
  Qed.
  
  (* what if both threads needed to read but not write all of the array *)
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
- slides
- execute_block spec: narrative and prettify
- remaining goal pprinter
- check arg names
- hide cQp?
- auto splitting in parallel_gcd_lcm proof
- replace all Z.gcd by N.gcd. no Vint, only Vn. or only Vint and Z stuff
- remove all occurrences nat ?
- S n by 1+n
- pretty printing of goal: ltac.
- remove type in array offset
- In to ∈
- docker image

done:
- emacs plugin to autocenter
- rename all Vptr to Vptr?
 *)

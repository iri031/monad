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
Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
  Context  {MODd : demo.module ⊧ CU}.
  Definition cQpc := cQp.mk false.
  Coercion cQpc : Qp >-> cQp.t.

  (* questions policy slide *)

  Disable Notation intR.

  Lemma primR2_anyR : ∀ t (q:Qp) (v:val) (p:ptr),
      p|-> primR t (q/2) v ** p|->primR t (q/2) v  |-- p|->anyR t q.
  Proof using. Admitted.
  Definition primR2_anyRC := [CANCEL] primR2_anyR.
  Hint Resolve primR2_anyRC: br_opacity.
  Hint Resolve array_combine_C: br_opacity.
  Hint Rewrite @length_drop: syntactic.

  
  (* open foo in demo.cpp *)
  Open Scope Z_scope.
  cpp.spec "foo()" as foo_spec with (
        \prepost{xv:Z} _global "x" |-> primR "unsigned int" 1  xv
        \pre{yv:Z} _global "y" |-> anyR "unsigned int" 1 (* possibly uninitialized *)
        \post _global "y" |-> primR "unsigned int" 1 (xv+1)
      ).

  Example anyy : _global "y" |-> uninitR "unsigned int" 1
                   \\// (Exists xv:Z, _global "y" |-> primR "unsigned int" 1 xv)
                   |--  _global "y" |-> anyR "unsigned int" 1.
  Proof using. rewrite bi.or_alt. go. destruct t; go. Qed.
  (* what is wrong with the spec above? *)

  Remove Hints plogic.learnable_primR : br_opacity.

  (* small stepping through the proof *)
  Lemma prf: denoteModule demo.module |-- foo_spec.
  Proof using.
    verify_spec.
    (* meaning of goal view*)
    do 4 run1.
    (* eval first operand (argument) of + *)
    step.
    iExists xv.
    work; [iExists (cQpc 1); work|].
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
        \prepost{xv:N} _global "x" |-> primR "unsigned int" 1 xv
        \pre{yv:N} _global "y" |-> primR "unsigned int" 1 yv
        \post _global "y" |-> primR "unsigned int" 1 ((xv+1) `mod` (2^32))%N
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
    do 5 run1;[slauto|].
    do 2 step.
    rewrite <- has_int_type.
    simpl.
    unfold bitsize.bound.
    simpl.
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
          
  (** |-> : points_t *)
  (** left of |-> must be a memory location, of type [ptr] *)
  Example memLoc: ptr := _global "b".

  (** right of |-> must be a "memory representation", of type [Rep].
      Reps:
      - connect what is stored in memory to some "mathematical" Coq object
      - specify the amount of ownership

     The cpp2v logic axiomatizes representations of primitives: int/char/long/int*/...
   *)
  
  Example intRep (q:Qp) (x:Z) : Rep := primR "int" q x.
  Check primR.
  Print val.
  Example as3 (bv:Z): mpred := _global "b" |-> primR "int" 1 (Vint bv).
  Example as3elide (bv:Z): mpred := _global "b" |-> primR "int" 1 bv.
  Set Printing Coercions.
  Print as3elide.

  Example ptrRep (q:Qp) (mloc: ptr) : Rep := primR "int*" q (Vptr mloc).

  (* open demo.cpp *)
  cpp.spec "fooptr()" as ptrspec with
      (\pre _global "ptr" |-> anyR "int *"1
       \post _global "ptr" |-> primR "int *" 1 (Vptr (_global "a")) 
      ).

  Lemma foopptr: denoteModule module |-- ptrspec.
  Proof using.
    verify_spec'.
    slauto.
  Qed.
  (** "all" theorem statements in Coq have type Prop *)
  Example stm (L R : mpred): Prop := L |-- R.

  Lemma moreThanLogicalImpl :
    _global "x" |-> primR "int" (1/3) 0 |-- _global "x" |-> primR "int" (1/2) 0.
  Abort. (* not provable *)
  
  Print ptrspec.

  (* now ownership received/returned *)
  cpp.spec "gcd(unsigned int, unsigned int)" as gcd_spec with (
        \arg{av:Z} "a" (Vint av) (* forall av, ... *)
        \arg{bv:Z} "b" (Vint bv)
        \post [Vint (Z.gcd av bv)] emp
      ).

  (** in monad, codebase, we pass most args (usually bulky objects) by reference ... *)
  cpp.spec "gcd(const unsigned int&, const unsigned int&, unsigned int&)" as gcd2_spec with (
        \arg{ap:ptr} "a" (Vref ap)
        \prepost{(qa:Qp) (av:N)} ap |-> primR "unsigned int" qa av
        \arg{bp:ptr} "b" (Vref bp)
        \prepost{(qb:Qp) (bv:N)} bp |-> primR "unsigned int" qb bv
        \arg{resultp:ptr} "gcd_result" (Vref resultp)
        \pre resultp |-> anyR "unsigned int" 1
        \post resultp |-> primR "unsigned int" 1 (Z.gcd av bv)
      ).

  (** \prepost  in sequential code, ..., but in concurrent code ...*)

  Lemma primr_split_half (p:ptr) ty (q:Qp) v :
    p|-> primR ty q v -|- (p |-> primR ty (q/2) v) ** p |-> primR ty (q/2) v.
  Proof using. apply primr_split. Qed.
  
  (** parallel_gcd_lcm in demo.cpp *)
  (** diagram *)
  
  
(** *Demo: read-read concurrency using fractional permissions *)
  
  Definition ThreadR (lamStructName: core.name) (P Q : mpred) : Rep. Proof using. Admitted.
  
  Definition ThreadConstructor (lamStructName: core.name) (this:ptr): WpSpec mpredI val val :=
    \arg{lambdap:ptr} "lambda" (Vref lambdap)
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
    \pre{taskPre taskPost} this |-> ThreadR lamStructName taskPre taskPost
    \post emp.
  
  Definition fork_start (lamStructName: core.name) (this:ptr): WpSpec mpredI val val :=
    \prepost{P Q} this |-> ThreadR lamStructName P Q
    \pre P
    \post emp.

  Definition join (lamStructName: core.name) (this:ptr): WpSpec mpredI val val :=
    \prepost{P Q} this |-> ThreadR lamStructName P Q
    \post Q.

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
  Definition thread_fork_start (lamStructTyName: core.name) :=
  specify
    {|
      info_name :=
        Nscoped (Ninst "Thread" [Atype (Tnamed lamStructTyName)]) (Nfunction function_qualifiers.N "fork_start" []);
      info_type :=
        tMethod (Ninst "Thread" [Atype (Tnamed lamStructTyName)]) QM "void" []
    |}
    (fork_start lamStructTyName).

  Definition thread_fork_join (lamStructTyName: core.name) :=
  specify
    {|
      info_name :=
        Nscoped (Ninst "Thread" [Atype (Tnamed lamStructTyName)]) (Nfunction function_qualifiers.N "join" []);
      info_type :=
        tMethod (Ninst "Thread" [Atype (Tnamed lamStructTyName)]) QM "void" []
    |}
    (join lamStructTyName).
  
  cpp.spec "Thread<parallel_gcd_lcm(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)::@0>::fork_start()"
           as ff with (fork_start "parallel_gcd_lcm(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)::@0").

  Definition thread_class_specs lamStructName :=
    thread_constructor lamStructName **
    thread_fork_start lamStructName **
    thread_fork_join lamStructName **
    thread_destructor lamStructName.
   
  Existing Instance UNSAFE_read_prim_cancel.
  #[global] Instance : forall ty P Q, Observe (reference_toR (Tnamed ty)) (ThreadR ty P Q).
  Proof. Admitted.

  #[global] Instance obss (pp:ptr) ty P Q: Observe (reference_to (Tnamed (Ninst "Thread" [Atype (Tnamed ty)])) pp) (pp |-> ThreadR ty P Q).
  Proof. Admitted.
  cpp.spec (Nscoped 
              "parallel_gcd_lcm(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)::@0" Ndtor)  as lamdestr
                                                                                                                          inline.

  cpp.spec "parallel_gcd_lcm(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)" as par_gcd_lcm_spec with
      (
        \arg{ap} "a" (Vref ap)
        \prepost{(qa:Qp) (av:N)} ap |-> primR "unsigned int" qa av
        \arg{bp} "b" (Vref bp)
        \prepost{(qb:Qp) (bv:N)} bp |-> primR "unsigned int" qb bv
        \arg{gcdrp} "gcd_result" (Vref gcdrp)
        \pre gcdrp |-> anyR "unsigned int" 1
        \arg{lcmrp} "lcm_result" (Vref lcmrp)
        \pre lcmrp |-> anyR "unsigned int" 1
        \pre[| 0<bv \/ 0<av |]%N
        \post gcdrp |-> primR "unsigned int" 1 (Z.gcd av bv)
              ** (if decide (av*bv < 2^32)%N then
                  lcmrp |-> primR "unsigned int" 1 (Z.lcm av bv)
                  else Exists garbage3, lcmrp |-> primR "unsigned int" 1 garbage3)
      ).

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
    slauto.
    fold cQpc.
    aggregateRepPieces gcdLambda_addr. (*TODO shorten gcdLambda *)
    iExists (gcdrp |-> anyR "unsigned int" 1 ** ap |-> uintR (qa/2) av ** bp |-> uintR (qb/2) bv). (* taskPre *)
    instWithPEvar taskPost. (* taskPost: infer it automatically, optimally *)
    slauto; iSplitL "".
    (* 2 goals:
       - prove that the lambda function satisfies the spec with pre:=taskPre and post:=taskPost (TBD)
       - continue with the code after the Thread constructor, with the \post of the constructor 
     *)
    { verify_spec'.
      go.
      erefl.
    }
    unhideAllFromWork.
    iIntrosDestructs.
    do 5 run1.
    step. (* needs 1) ownership of thead object 2) prev. chosen \pre. the latter is not returned  *)
    do 2 step.
    fold cQpc.
    rewrite (primr_split ap).
    rewrite (primr_split bp).
    run1. (* evaluating operands for *. lost ownership gcdrsp, 1/2 of a,b. 1/2 suffices for a,b *)
    
    do 7 run1. (* call to join() *)
    run1. (* got back ownership of gcdrp, now it holds the result of gcd. also other halfs. need to return full *)
    do 4 run1.
    do 3 step;[slauto|]. (* next: / *)
    step.
    Search (Z.gcd _ _ = 0 )%Z.
    pose proof (Z.gcd_eq_0 av bv).
    pose proof (Z.gcd_nonneg av bv).
    step.
    provePure. { nia. }. step.
    go.
    case_decide.
    2:{ go. }
    {
      Arith.remove_useless_mod_a. (* * is mod 2^32 *)
      icancel (cancel_at lcmrp);[| go].
      do 2 f_equiv.
      unfold Z.lcm.
      rewrite Z.lcm_equiv1.
      rewrite Z.abs_eq.
      rewrite Z.quot_div_nonneg.
      reflexivity.
      nia.
      nia.
      apply Z_div_nonneg_nonneg; try nia.
      nia.
    }
  Qed.

    (** main innovation of iris separation logic (test of time award):
- richest formal languange to describe ownerships and how it can be spit into multiple threads
   - enforce protocls: exactly specify how/whether a thread can modify a datastructure.
      - one thread can only increment a counter, another can only decrement
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
    wp_if.
    { (* loop condition is true: loop executed body *)
      slauto.
      iPureIntro.
      aac_normalise in H.
      aac_rewrite Z.gcd_mod; try Arith.arith_solve.
      aac_normalise.
      Arith.arith_solve.
    }

    { (* loop condition is false: loop terminates *)
      slauto.
      simplPure.
      aac_normalise in H.
      aac_rewriteh Z.gcd_0_r_nonneg in H; subst; try Arith.arith_solve.
      go.
    }

  Qed.

  Lemma gcd2_proof: denoteModule module |-- gcd2_spec.
  Proof.
    verify_spec'.
    wapply gcd_proof. go.
  Qed.

  Lemma pos (p:ptr) (v:Z) : p |-> uintR 1 v |-- [| 0 <=v |] ** p |-> uintR 1 v.
  Proof using.
    go.
  Qed.
  
  (* TODO: lemma to unroll arrayR for 3 elements *)

  (* parallelization: *)
  Check Z.gcd_comm.
  Check Z.gcd_assoc.

  Definition gcdl_spec_core : WpSpec mpredI val val :=
        \arg{numsp:ptr} "nums" (Vptr numsp)
        \prepost{(l: list Z) (q:Qp)} (numsp |-> arrayR "unsigned int" (fun i => primR "unsigned int" q (Vint i)) l) 
        \arg "size" (Vint (lengthZ l))
        \post [Vint (fold_left Z.gcd l 0)] emp.
  
  cpp.spec "gcdl(unsigned int*, unsigned int)" as gcdl_spec with (gcdl_spec_core).
  cpp.spec "parallel_gcdl(unsigned int*, unsigned int)" as parallel_gcdl_spec with (gcdl_spec_core).


  Lemma gcdl_proof: denoteModule module |-- gcdl_spec.
  Proof using MODd.
    verify_spec.
    slauto.
    wp_for (fun _ => Exists iv:nat,
                i_addr |-> uintR (cQp.mut 1) iv **
                [| iv <= length l |]%nat **
              result_addr |-> uintR (cQp.mut 1) ((fold_left Z.gcd (firstn iv l) 0))
           ).
    go. iExists 0%nat. go.
    wp_if.
    {
      slauto.
      rename t into iv.
      unfold lengthN in *.
      autorewrite with syntactic in *.
      eapplyToSomeHyp @arrayR_cell2.
      forward_reason.
      rewrite -> autogenhypr.
      hideRhs.
      go.
      unhideAllFromWork.
      slauto.
      wapply gcd_proof.
      go.
      iExists (1+iv)%nat.
      go.
      erewrite take_S_r;[|eauto].
      rewrite fold_left_app.
      simpl.
      go.
      rewrite -> autogenhypr.
      go.
    }
    {
      slauto.
      unfold lengthN in *.
      rename t into iv.
      assert (iv=length l) as Heq by lia.
      subst.
      autorewrite with syntactic.
      go.
    }
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
    wapplyObserve  obsUintArrayR.
    eagerUnifyU. work.
    slauto.
    aggregateRepPieces gcdlLambda_addr.
    go.
    hideP ps.
    Opaque Nat.div.
    assert ( (length l `div` 2 <= length l)%nat) as Hle.
    {
      rewrite <- Nat.div2_div.
      apply Nat.le_div2_diag_l.
    }
    assert ( (length l `div` 2 <= length l)) as Hlez.
    {
      rewrite <- (Nat2Z.inj_div _ 2).
      lia.
    }
    rewrite -> arrayR_split with (i:=((length l)/2)%nat) (xs:=l) by lia.
    slauto.
    rewrite (primr_split nums_addr).
    rewrite (primr_split mid_addr).
    go.
    (* todo: replace the last many lines by a oneliner: ideally, obtain the list automatically *)
    repeat IPM.perm_left ltac:(fun L n=>
                          match L with
                          | numsp |-> _ => iRevert n
                          | resultl_addr |-> _ => iRevert n
                          end
                              ) .
    IPM.perm_left ltac:(fun L n=>
                          match L with
                          | nums_addr |-> _ => iRevert n
                          end).
    IPM.perm_left ltac:(fun L n=>
                          match L with
                          | mid_addr |-> _ => iRevert n
                          end).
    repeat rewrite bi.wand_curry.
    match goal with
      [ |-environments.envs_entails _ (?R -* _)] =>
        iIntrosDestructs;
        iExists R
    end.
    instWithPEvar taskPost.
    go.

    iSplitL "".
    { verify_spec'.
      slauto.
      unfold lengthN. go.
      autorewrite with syntactic.
      rewrite Z.quot_div_nonneg; try lia.
      go.
      rewrite Nat2Z.inj_div.
      go.
      iExists _. eagerUnifyU.
      go.
      erefl.
    }
    unhideAllFromWork.
    iIntrosDestructs.
    slauto.
    unfold lengthN.
    autorewrite with syntactic.
    rewrite Z.quot_div_nonneg; try lia.
    rewrite Nat2Z.inj_div. (* add to syntacctic? *)
    slauto.
    unfold lengthN.
    autorewrite with syntactic.
    rewrite -> Nat2Z.inj_sub by lia.
    Arith.remove_useless_mod_a.
    rewrite Nat2Z.inj_div.
    simpl.
    go.
    iExists _. eagerUnifyU.
    slauto.
    wapply gcd_proof. go.
  go.
  hideLhs.
  rewrite <- arrayR_combine.
  unhideAllFromWork.
  simpl. work.
  rewrite Nat2Z.inj_div. go.
  iClear "#".
  iStopProof.
  f_equiv.
  f_equal.
  f_equal.
  symmetry.
  apply fold_split_gcd.
  auto.
Qed.
  Lemma doubleSpending: _global "x" |-> primR "int" 1 0 ** _global "x" |-> primR "int" 1 0|-- [| False |].
  Proof using. Abort.
  
  Lemma okSpending: _global "x" |-> primR "int" (1/2) 0 ** _global "x" |-> primR "int" (1/2) 0|--  _global "x" |-> primR "int" 1 0.
  Proof using. Abort.
      Lemma duplTypePtr (ap:ptr): type_ptr "unsigned int" ap |-- type_ptr "unsigned int" ap ** type_ptr "unsigned int" ap.
      Proof using. go. Qed.
      Lemma duplSpec (ap:ptr): gcd_spec |-- gcd_spec ** gcd_spec.
      Proof using. go. Qed.
    
End with_Sigma.
(*
- check arg names
- hide cQp?
- auto splitting in parallel_gcd_lcm proof
- rename all Vref to Vptr?
- replace all Z.gcd by N.gcd. no Vint, only Vn. or only Vint and Z stuff
- remove all occurrences nat ?
- S n by 1+n
- pretty printing of goal: ltac.
- remove type in array offset
- In to ∈
- docker image

done:
- emacs plugin to autocenter

 *)

Require Import monad.asts.demo.
Require Import monad.proofs.misc.
Require Import monad.proofs.libspecs.
Require Import bedrock.auto.invariants.
Require Import bedrock.auto.cpp.proof.
Require Import bedrock.auto.cpp.tactics4.
Require Import monad.proofs.demomisc.
Import cQp_compat.
Open Scope cQp_scope.
Import linearity.
Import Verbose.
Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
  Context  {MODd : demo.module ⊧ CU}.
  Definition cQpc := cQp.mk false.
  Coercion cQpc : Qp >-> cQp.t.

  cpp.spec "foo()" as foo_spec with (
        \prepost{xv:N} _global "x" |-> primR "unsigned int" 1  xv
        \pre{yv:N} _global "y" |-> primR "unsigned int" 1 yv
        \post _global "y" |-> primR "unsigned int" 1 (xv+1)%N
      ).

  Lemma prf: denoteModule demo.module |-- foo_spec.
  Proof using.
    iIntrosDestructs.
    verify_spec.
    do 5 run1.
    - slauto.
    - hideLoc (_global "y"). go.
      rewrite <- primR_anyR_ex.
      work.
      unhideAllFromWork.
      iExists yv.
      iFrame.
      iIntros.
      runUntilPost.
      
   Abort.

  cpp.spec "foo()" as foo_spec_correct with (
        \prepost{xv:N} _global "x" |-> primR "unsigned int" 1 xv
        \pre{yv:N} _global "y" |-> primR.body "unsigned int" 1 yv
        \post _global "y" |-> primR.body "unsigned int" 1 ((xv+1) `mod` (2^32))%N
      ).

  Lemma prf: denoteModule demo.module |-- foo_spec_correct.
  Proof.
    verify_spec'.
    slauto.
  Qed.


  
  cpp.spec "sfoo()" as sfoo_spec with (
        \prepost{xv:Z} _global "a" |-> primR "int" 1 xv
        \pre{yv:N} _global "b" |-> primR.body "int" 1 yv
        \post _global "b" |-> primR.body "int" 1 ((xv+1))%Z
      ).

  Lemma sprf: denoteModule demo.module |-- sfoo_spec.
  Proof.
    verify_spec'.
    slauto.
    provePure.
    type.has_type_prop_prep.
  Abort.
  
  cpp.spec "sfoo()" as sfoo_spec_correct with (
        \prepost{xv:Z} _global "a" |-> primR "int" 1 xv
        \pre [| (- 2 ^ (32 - 1) -1  ≤ xv ≤ 2 ^ (32 - 1) - 2)%Z |]
        \pre{yv:N} _global "b" |-> primR.body "int" 1 yv
        \post _global "b" |-> primR.body "int" 1 ((xv+1))%Z
      ).

  Lemma sprf: denoteModule demo.module |-- sfoo_spec_correct.
  Proof.
    verify_spec'.
    slauto.
  Qed.


  (* TODO: add lambdap and lambdStructObjOwnership arguments *)
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

  cpp.spec "parallel_gcd_lcm(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)" as pgl with
      (
        \arg{ap} "a" (Vref ap)
        \prepost{(qa:Qp) (av:N)} ap |-> primR "unsigned int" qa av
        \arg{bp} "b" (Vref bp)
        \prepost{(qb:Qp) (bv:N)} bp |-> primR "unsigned int" qb bv
        \arg{gcdp} "gcd_result" (Vref gcdp)
        \pre{garbage1:N} gcdp |-> primR "unsigned int" 1 garbage1
        \arg{lcmp} "lcm_result" (Vref lcmp)
        \pre{garbage2:N} lcmp |-> primR "unsigned int" 1 garbage2
        \pre[| 0<bv \/ 0<av |]%N
        \post gcdp |-> primR "unsigned int" 1 (Z.gcd av bv)
              ** (if decide (av*bv < 2^32)%N then
                  lcmp |-> primR "unsigned int" 1 (Z.lcm av bv)
                  else Exists garbage3, lcmp |-> primR "unsigned int" 1 garbage3)
      ).

  cpp.spec "gcd(unsigned int, unsigned int)" as gcd_spec with (
        \arg{a:Z} "a" (Vint a)
        \arg{b:Z} "b" (Vint b)
        \post [Vint (Z.gcd a b)] emp
      ).

  cpp.spec "gcd(const unsigned int&, const unsigned int&, unsigned int&)" as gcd2_spec with (
        \arg{ap} "a" (Vref ap)
        \prepost{(qa:Qp) (av:N)} ap |-> primR "unsigned int" qa av
        \arg{bp} "b" (Vref bp)
        \prepost{(qb:Qp) (bv:N)} bp |-> primR "unsigned int" qb bv
        \arg{gp} "gcd_result" (Vref gp)
        \pre{garbage1:N} gp |-> primR "unsigned int" 1 garbage1
        \post gp |-> primR "unsigned int" 1 (Z.gcd av bv)
      ).

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
  Lemma par: denoteModule module |-- pgl.
  Proof using.
    verify_spec'.
    go.
  Abort.

  Definition thread_class_specs lamStructName :=
    thread_constructor lamStructName **
    thread_fork_start lamStructName **
    thread_fork_join lamStructName **
    thread_destructor lamStructName.
   
  Existing Instance UNSAFE_read_prim_cancel.
  #[global] Instance : forall ty P Q, Observe (reference_toR (Tnamed ty)) (ThreadR ty P Q).
  Proof. Admitted.

  Lemma primr_split (p:ptr) ty (q:Qp) v :
    p|-> primR ty (cQpc q) v -|- (p |-> primR ty (cQpc q/2) v) ** p |-> primR ty (cQpc q/2) v.
  Proof using.
    unfold cQpc.
    rewrite -> cfractional_split_half with (R := fun q => primR ty q v).
    2:{ exact _. }
    rewrite _at_sep.
    f_equiv; f_equiv; f_equiv;
    simpl;
      rewrite cQp.scale_mut;
      f_equiv;
    destruct q; simpl in *;
      solveQpeq;
      solveQeq.
  Qed.
  #[global] Instance obss (pp:ptr) ty P Q: Observe (reference_to (Tnamed (Ninst "Thread" [Atype (Tnamed ty)])) pp) (pp |-> ThreadR ty P Q).
  Proof. Admitted.
  cpp.spec (Nscoped 
              "parallel_gcd_lcm(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)::@0" Ndtor)  as lamdestr
                                                                                                                          inline.
  
  Lemma par: denoteModule module ** (thread_class_specs "parallel_gcd_lcm(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)::@0") ** gcd2_spec |-- pgl.
  Proof using MODd.
    unfold thread_class_specs.
    verify_spec'.
    slauto.
    aggregateRepPieces gcdLambda_addr.
    go.
    
    fold cQpc.
    (* TODO: pick a better name for gp. TODO. replace unintR with primR  *)
    iExists (gcdp |-> uintR 1%Qp garbage1 ** ap |-> uintR (qa/2) av ** bp |-> uintR (qb/2) bv).
    iExists (gcdp |-> uintR 1%Qp (Z.gcd av bv) ** ap |-> uintR (qa/2) av ** bp |-> uintR (qb/2) bv).
    go.
    iSplitL "".
    { verify_spec'.
      go.
    }
    iIntrosDestructs.
    do 6 run1.
  #[global] Instance : forall ty , LearnEq2 (ThreadR ty) := ltac:(solve_learnable).
    step.
    step.
    step.
    fold cQpc.
    rewrite (primr_split ap).
    rewrite (primr_split bp).
    go.
    Compute (Z.gcd 0 0).
    Search 0%Z (Z.gcd _ _)%Z.
    pose proof (Z.gcd_nonneg av bv).
    pose proof (Z.gcd_eq_0 av bv).
    provePure.
    nia.
    work.
    run1.
    run1.
    run1.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    do 3 step.
    go.
    case_decide.
    {
      Arith.remove_useless_mod_a.
      icancel (cancel_at lcmp).
      f_equiv.
      unfold Z.lcm.
      rewrite Z.lcm_equiv1.
      rewrite Z.abs_eq.
      rewrite Z.quot_div_nonneg.
      reflexivity.
      nia.
      nia.
      apply Z_div_nonneg_nonneg; try nia.
      nia.
      go.
    }
    {
      go.
    }
  Qed.
    

    
cpp.spec ((Ninst
          (Nscoped resultn
             (Nctor
                [Trv_ref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Receipt"))));
                 Tnamed (Nscoped resultn (Nid "value_converting_constructor_tag"))]))
          [Atype (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Receipt")))); Atype "void"]))
  as result_val_constr with (fun this:ptr =>
                               \arg{recp} ("recp"%pstring) (Vref recp)
                               \prepost{r} recp |-> ReceiptR r
                               \arg{vtag} ("vtag"%pstring) (Vptr vtag)
                               \post this |-> ResultSuccessR ReceiptR r).
  
End with_Sigma.
(*
- pretty printing of goal: ltac.
- hide cQp?
- docker image
-  rename all Vref to Vptr?
 *)

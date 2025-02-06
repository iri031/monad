Require Import monad.asts.demo.
Require Import monad.proofs.misc.
Require Import monad.proofs.libspecs.
Require Import bedrock.auto.invariants.
Require Import bedrock.auto.cpp.proof.
Require Import bedrock.auto.cpp.tactics4.
Require Import monad.proofs.demomisc.
Import cQp_compat.
Open Scope cQp_scope.
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


  Definition ThreadR (lamStructName: core.name) (P Q : mpred) : Rep. Proof using. Admitted.
  
  Definition ThreadConstructor (lamStructName: core.name) (this:ptr): WpSpec mpredI val val :=
    \arg{lambdap:ptr} "lambda" (Vref lambdap)
    \pre{lamStructObjOwnership} lambdap |-> lamStructObjOwnership (* ownerhsip of fields othe lambda struct *)
    \pre{taskPre taskPost}
      specify {| info_name :=  (Nscoped lamStructName taskOpName);
                info_type := tMethod lamStructName QC "void" [] |}
      (fun (this:ptr) =>
         \prepost this |-> lamStructObjOwnership
         \pre taskPre
         \post taskPost)
    
    \post this |-> ThreadR lamStructName taskPre taskPost.

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
        \prepost{(qa:Qp) (av:N)} ap |-> primR "int" qa av
        \arg{bp} "b" (Vref bp)
        \prepost{(qb:Qp) (bv:N)} bp |-> primR "int" qb bv
        \arg{gp} "gcd_result" (Vref gp)
        \pre{garbage1:N} gp |-> primR "int" 1 garbage1
        \arg{lp} "lcm_result" (Vref lp)
        \pre{garbage2:N} lp |-> primR "int" 1 garbage2
        \post emp
      ).

  cpp.spec "gcd(unsigned int, unsigned int)" as gcd_spec with (
        \arg{a:Z} "a" (Vint a)
        \arg{b:Z} "b" (Vint b)
        \post [Vint (Z.gcd a b)] emp
      ).

  cpp.spec "gcd(const unsigned int&, const unsigned int&, unsigned int&)" as gcd2_spec with (
        \arg{ap} "a" (Vref ap)
        \prepost{(qa:Qp) (av:N)} ap |-> primR "int" qa av
        \arg{bp} "b" (Vref bp)
        \prepost{(qb:Qp) (bv:N)} bp |-> primR "int" qb bv
        \arg{gp} "gcd_result" (Vref gp)
        \pre{garbage1:N} gp |-> primR "int" 1 garbage1
        \post gp |-> primR "int" 1 (Z.gcd av bv)
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

  Lemma par: denoteModule module |-- pgl.
  Proof using.
    verify_spec'.
    go.
  Abort.
   
  Existing Instance UNSAFE_read_prim_cancel.

  Lemma par: denoteModule module ** (thread_constructor "parallel_gcd_lcm(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)::@0") ** gcd2_spec |-- pgl.
  Proof using.
    verify_spec'.
    slauto.
    aggregateRepPieces a.
    go.
    
    fold cQpc.
    (* TODO: pick a better name *)
    iExists (gp |-> intR 1%Qp garbage1 ** ap |-> intR (qa/3) av ** bp |-> intR (qb/3) bv).
    iExists (gp |-> intR 1%Qp (Z.gcd av bv) ** ap |-> intR (qa/3) av ** bp |-> intR (qb/3) bv).
    go.
    iSplitL "".
    { verify_spec'.
      go.
    }
    iIntrosDestructs.
    slauto.
    const.
    go.
    slauto.
    go.
    go.
    iModIntro.
    fwd removeLater.


    
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

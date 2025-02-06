Require Import monad.asts.demo.
Require Import monad.proofs.misc.
Require Import monad.proofs.libspecs.
Require Import bedrock.auto.invariants.
Require Import bedrock.auto.cpp.proof.
Require Import bedrock.auto.cpp.tactics4.
Import cQp_compat.
Open Scope cQp_scope.
Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
  Context  {MODd : demo.module ⊧ CU}.
  Definition cQpc := cQp.mk false.
  Coercion cQpc : Qp >-> cQp.t.

  Arguments primR.body {thread_info _Σ Σ σ} ty%cpp_type_scope q%cQp_scope v.
  cpp.spec "foo()" as foo_spec with (
        \prepost{xv:N} _global "x" |-> primR "unsigned int" 1 xv
        \pre{yv:N} _global "y" |-> primR.body "unsigned int" 1 yv
        \post _global "y" |-> primR.body "unsigned int" 1 (xv+1)%N
      ).


  Import Verbose.
      Ltac hideLoc l :=
        IPM.perm_left ltac:(fun t n=>
                              match t with
                              | l |-> ?r => hideFromWork r
                              end

                           ).

      Lemma primR_anyR_ex: ∀  (t : type) (q : cQp.t),
         Exists v,  primR t q v ⊢ anyR t q.
      Proof using.
        intros.
        go.
      Qed.

  Lemma uncurry_post_wand (P:mpred) (Qs Q: ptr -> mpred):
    (P -* Forall x, (Qs x-* Q x))
      |-- (Forall x, ((P ** Qs x)-* Q x)).
  Proof. Admitted.
    Lemma wpl f ρ s Qs Q:
      (Forall v, Qs v -* Q v) **  (wp f ρ s (Kreturn (λ v : ptr, Qs v))) |--
        (wp f ρ s (Kcleanup module [] (Kreturn (λ v : ptr, |> Q v)))).
    Proof using. Admitted.

  Ltac clearPost :=
    repeat match goal with
    | H: mpred |- _ => try clear H
    | H : ptr-> mpred |- _ => try clear H
    end.
    
  Ltac verify_spec2 :=
    work; (* NOT go as that puts Seq into the continuation as Kseq, making the next rewrite fail *)
    try rewrite uncurry_post_wand; (* TODO: make it work only the hyp of the form -* POST v *)
    rewrite <- wpl;
    eagerUnifyU; (* this does not suffice: see split_spec proof. need to do evar tricks to infer Qs *)
    work;
    name_locals;
    cpp.hints.type.has_type_prop_prep;
    try clearPost.
      
  Ltac verify_spec1 :=
    iApply (verify_spec_new false false false module with ""%string);
    [vm_compute; reflexivity|].

  Ltac verify_spec :=
    iIntrosDestructs;
    verify_spec1;
    verify_spec2.

      Ltac runUntilPost :=
      match goal with
        |- context[Kreturn ?post] => hideFromWork post
      end;
      go;
      unhideAllFromWork;
      repeat rewrite <- primR_tptsto_fuzzyR.
  Lemma prf: denoteModule demo.module |-- foo_spec.
  Proof using.
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
        \post _global "b" |-> primR.body "int" 1 ((xv+1) `mod` (2^32))%Z
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

    
End with_Sigma.

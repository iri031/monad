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
        
  Lemma prf: denoteModule demo.module |-- foo_spec.
  Proof using.
    verify_spec'.
    do 5 run1.
    - slauto.
    - hideLoc (_global "y"). go.
      rewrite <- primR_anyR_ex.
      work.
      unhideAllFromWork.
      iExists yv.

  IPM.perm_left ltac:(fun L n =>
                        match L with
                        | HiddenPostCondition => hideFromWorkAs L fullyHiddenPostcond;
                      iRename n into "post"
                        end
                     ).
      go.
      unhideAllFromWork.
      rewrite HiddenPostCondition.unlock.
      iApply "post".
   Abort.
   
      
          
    (* todo
- add calendar event.
- 

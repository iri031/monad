Require Import monad.proofs.demo2.
Require Import bedrock.auto.invariants.
Require Import bedrock.auto.cpp.proof.
Require Import bedrock.auto.cpp.tactics4.

Require Import monad.proofs.misc. (* monad/proofs/misc.v *)
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
Disable Notation take.
Disable Notation drop.
Disable Notation "`div`" (all).
Disable Notation intR.
Disable Notation uintR.

Import linearity.
Section with_Sigma.
  Context `{Sigma:cpp_logic}  {CU: genv}.
  Context  {MODd : demo2.module ⊧ CU}.

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

  Definition AWrapperR  (q: Qp) (invId: gname): Rep :=
    structR "AWRapper" q **
    as_Rep (fun this:ptr =>
      cinv invId q (∃ i:Z, this ,, _field "v" |-> atomicR "int" 1 i)).

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
  Definition AWrapperR2  (q: Qp) (invId: gname): Rep :=
    structR "AWRapper" q **
    as_Rep (fun this:ptr =>
       cinv invId q (∃ i:Z, this ,, _field "v" |-> atomicR "int" 1 i
                        ** [| isPrime i |] )).

  cpp.spec "AWrapper::setValue(int)" as setValue2_spec with (fun (this:ptr) =>
     \prepost{q invId} this |-> AWrapperR2 q invId
     \arg{i:Z} "value" (Vint i)
     \pre [| isPrime i |] 
     \post emp).

  cpp.spec "AWrapper::getValue()" as getValue2_spec with (fun (this:ptr) =>
     \prepost{q invid} this |-> AWrapperR2 q invid
     \post{any:Z} [Vint any] [| isPrime any |]).
  
End with_Sigma.

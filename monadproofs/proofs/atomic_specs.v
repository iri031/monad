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

Notation memory_order_seq_cst := 5.

Section with_Sigma.
  Context `{Sigma:cpp_logic}  {CU: genv}.
  Context  {MODd : demo2.module ⊧ CU}.

(*
Hint Resolve learn_atomic_val : br_opacity.
*)  
  Open Scope Z_scope.
  Set Nested Proofs Allowed.


  #[ignore_errors]
  cpp.spec "std::__1::__atomic_base<int, 0b>::exchange(int, enum std::__1::memory_order)"  as int_exchange_spec with
          (λ this : ptr,
     \arg{(x : Z)} "v" (Vint x)
     \arg "order" (Vint memory_order_seq_cst)
       \let pd := this ,, o_derived CU "std::__1::__atomic_base<int, 0b>" "std::__1::__atomic_base<int, 1b>"
                       ,, o_derived CU "std::__1::__atomic_base<int, 1b>" "std::__1::atomic<int>"
     \pre{Q : Z → mpred}
       AC1 << ∀ y : Z, pd |-> atomicR "int" (cQp.mut 1) (Vint y)>> @ ⊤, ∅
          << pd |-> atomicR "int" (cQp.mut 1) (Vint x), COMM Q y >> 
     \post{y : Z}[Vint y]
     Q y).

  #[ignore_errors]
  cpp.spec "std::__1::__atomic_base<int, 0b>::load(enum std::__1::memory_order) const"  as int_load_spec with
          (λ this : ptr,
       \let pd := this ,, o_derived CU "std::__1::__atomic_base<int, 0b>" "std::__1::__atomic_base<int, 1b>"
                       ,, o_derived CU "std::__1::__atomic_base<int, 1b>" "std::__1::atomic<int>"
     \arg "order" (Vint memory_order_seq_cst)
     \pre{ (q:Qp) (InvOut : Z → mpred)}
       AC1 << ∀ y : Z, pd |-> atomicR "int" q (Vint y)>> @ ⊤, ∅
                    << pd |-> atomicR "int" q (Vint y), COMM InvOut y >> 
     \post{y : Z}[Vint y]
     InvOut y).

  
  #[ignore_errors]
  cpp.spec "std::__1::__atomic_base<bool, 0b>::exchange(bool, enum std::__1::memory_order)"  as exchange_spec with
          (λ this : ptr,
     \arg{(x : bool)} "v" (Vbool x)
     \arg "order" (Vint memory_order_seq_cst)
     \let pd := this,, o_derived CU "std::__1::__atomic_base<bool, 0b>" "std::__1::atomic<bool>"
     \pre{Q : bool → mpred}
       AC1 << ∀ y : bool, pd |-> atomicR Tbool (cQp.mut 1) (Vbool y)>> @ ⊤, ∅
          << pd |-> atomicR Tbool (cQp.mut 1) (Vbool x), COMM Q y >> 
     \post{y : bool}[Vbool y]
     Q y).
  
  #[ignore_errors]
  cpp.spec "std::__1::__atomic_base<bool, 0b>::store(bool, enum std::__1::memory_order)"  as store_spec with
      (λ this : ptr,
     \arg{(Q : mpred) (x : bool)} "v" (Vbool x)
     \arg "memorder" (Vint 5)
     \let pd := this,, o_derived CU "std::__1::__atomic_base<bool, 0b>" "std::__1::atomic<bool>"
     \pre
       AC1 << ∀ y : bool, pd |-> atomicR Tbool (cQp.mut 1) (Vbool y)>> @ ⊤, ∅
          << pd |-> atomicR Tbool (cQp.mut 1) (Vbool x), COMM Q >> 
     \post    Q).

  #[ignore_errors]
  cpp.spec "std::__1::__atomic_base<int, 0b>::store(int, enum std::__1::memory_order)"  as int_store_spec with
      (λ this : ptr,
     \arg{(Q : mpred) (x : Z)} "v" (Vint x)
       \let pd := this ,, o_derived CU "std::__1::__atomic_base<int, 0b>" "std::__1::__atomic_base<int, 1b>"
                       ,, o_derived CU "std::__1::__atomic_base<int, 1b>" "std::__1::atomic<int>"
     \arg "memorder" (Vint 5)
     \pre
       AC1 << ∀ y : Z, pd |-> atomicR "int" 1 (Vint y)>> @ ⊤, ∅
          << pd |-> atomicR "int" 1 (Vint x), COMM Q >> 
     \post Q).

End with_Sigma.

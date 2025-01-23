Require Import monad.proofs.misc.
Require Import monad.proofs.libspecs.
Require Import monad.proofs.evmopsem.
Import linearity.
Require Import bedrock.auto.invariants.
Require Import bedrock.auto.cpp.proof.

Require Import bedrock.auto.cpp.tactics4.
Require Import monad.asts.exb.
Require Import monad.proofs.exec_specs.


Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}.
  Context  {MODd : exb.module ⊧ CU}.


  Existing Instance learnArrUnsafe.
  Existing Instance learnpArrUnsafe.

Lemma prf: denoteModule module
             ** tvector_spec
             ** reset_promises
             ** fork_task
             ** vector_op_monad
             ** recover_sender
             ** opt_move_assign
             ** wait_for_promise
             ** set_value
             ** destrop
             |-- exect.
Proof using MODd.
Abort.
End with_Sigma.


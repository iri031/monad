Require Import QArith.
Require Import bedrock.lang.cpp.
Require Import stdpp.gmap.

Import cQp_compat.

#[local] Open Scope Z_scope.

(*
Require Import EVMOpSem.evmfull. *)
Import cancelable_invariants.

Definition storedAtGhostLoc  `{Sigma:cpp_logic} {CU: genv} (q: Q) (g: gname) (n: nat) : mpred.
  Admitted.

  

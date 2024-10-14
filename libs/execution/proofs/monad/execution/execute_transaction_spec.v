Require Import QArith.
Require Import Lens.Elpi.Elpi.
Require Import bedrock.lang.cpp.

Import cQp_compat.

#[local] Open Scope Z_scope.

Require Import EVMOpSem.evmfull.
Require Import stdpp.gmap.

Notation StateOfAccounts := GlobalState.
Definition Transaction := Message.t. (* TODO: refine *)

Definition stateAfterTransaction  (s: StateOfAccounts) (t: Transaction): StateOfAccounts.
Admitted. (* To be provided by an appropriate EVM semantics *)

Definition stateAfterTransactions  (s: StateOfAccounts) (ts: list Transaction): StateOfAccounts :=
  List.fold_left stateAfterTransaction ts s.

Record Block :=
  {
    transactions: list Transaction
  }.
  Import cancelable_invariants.
    
Module BlockState. Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)

   (* this comes from the iris separation logic library *)
  Definition storedAtGhostLoc (q: Q) (g: gname) (n: nat) : mpred.
  Admitted.

   (* this comes from the iris separation logic library *)
  Definition cinvq (g : gname) (q : Qp) (P : mpred) := cinv_own g q ** cinv nroot (* FIX? *) g P.
  

  Context (b: Block) (blockPreState: StateOfAccounts). (* BlockState is a type that makes sense in the context of a block and the state before the block  *)
  (** defines how the Coq (mathematical) state of Coq type [StateOfAccounts] is represented as a C++ datastructure in the fields of the BlockState class.
      [blockPreState] is the state at the beginning of the block.  newState
   *)
  Definition Raux (newState: StateOfAccounts): Rep.
    
  Admitted. (* To be defined later. something like: [_field db_ |-> DbR blockPreState ** _field deltas |-> StateDeltasR blockPreState newState] *)


  Definition inv  (commitedIndexLoc: gname)
    : Rep :=
    Exists committedIndex: nat,
        Raux (stateAfterTransactions blockPreState (List.firstn committedIndex (transactions b)))
          ** pureR (storedAtGhostLoc (1/3)%Q commitedIndexLoc committedIndex).

  Record glocs :=
    {
      commitedIndexLoc: gname;
      invLoc: gname;
    }.
  
  Definition R (q: Qp) (g: glocs) : Rep  :=
    as_Rep (fun this:ptr =>
              cinvq (invLoc g) q (this |-> inv (commitedIndexLoc g))).

  
End with_Sigma. End BlockState.

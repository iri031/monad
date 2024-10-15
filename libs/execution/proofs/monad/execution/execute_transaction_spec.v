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

  Definition storedAtGhostLoc  `{Sigma:cpp_logic} {CU: genv} (q: Q) (g: gname) (n: nat) : mpred.
  Admitted.
  
Module BlockState. Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)

   (* this comes from the iris separation logic library *)

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

(* Coq model of the Chain type in C++ *)
Definition Chain: Type. Admitted.

(* Coq model of the priority pool type in C++ *)
Definition PriorityPool: Type. Admitted.
Import bedrock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.
Inductive Revision := Shanghai | Frontier.

Definition valOfRev (r : Revision) : val := Vint 0. (* TODO: fix *)


Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)

  (* defines how [c] is represented in memory as an object of class Chain. this predicate asserts [q] ownership of the object, assuming it can be shared across multiple threads  *)
  Definition ChainR (q: Qp) (c: Chain): Rep. Proof. Admitted.

  (* defines how [c] is represented in memory as an object of class Chain *)
  Definition PriorityPoolR (q: Qp) (c: PriorityPool): Rep. Proof. Admitted.

  Definition BlockR (q: Qp) (c: Block): Rep. Proof. Admitted.
  
  Definition execute_block_spec : WpSpec mpredI val val :=
    \arg{chainp :ptr} "chain" (Vref chainp)
    \prepost{(qchain:Qp) (chain: Chain)} chainp |-> ChainR qchain chain
    \arg "rev" (valOfRev Shanghai)
    \arg{blockp: ptr} "block" (Vref blockp)
    \prepost{(block: Block)} blockp |-> BlockR 1 block (* is this modified, if so, fix this line, else make it const in C++ code? *)
    \arg{block_statep: ptr} "block_state" (Vref block_statep)
    \prepost{(preBlockState: StateOfAccounts) (gl: BlockState.glocs)}
      blockp |-> BlockState.R block preBlockState 1 gl
    \arg{block_hash_bufferp: ptr} "block_hash_buffer" (Vref block_hash_bufferp)
    \arg{priority_poolp: ptr} "priority_pool" (Vref priority_poolp)
    \prepost{priority_pool: PriorityPool} priority_poolp |-> PriorityPoolR 1 priority_pool
    \post storedAtGhostLoc (2/3)%Q (BlockState.commitedIndexLoc gl) (length (transactions block)).
  

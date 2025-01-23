Require Import stdpp.gmap.
Axiom GlobalState: Set.
Notation StateOfAccounts := GlobalState.
Axiom Transaction : Set.
Module evm.
  Axiom log_entry: Set.
  Axiom address: Set.
End evm.
Definition BlockHeader: Type. Admitted.
Record TransactionResult :=
  {
    gas_used: N;
    gas_refund: N;
    logs: list evm.log_entry;
  }.

Definition stateAfterTransactionAux  (s: StateOfAccounts) (t: Transaction): StateOfAccounts * TransactionResult.
Admitted. (* To be provided by an appropriate EVM semantics *)

(* similar to what execute_final does *)
Definition applyGasRefundsAndRewards (hdr: BlockHeader) (s: StateOfAccounts) (t: TransactionResult): StateOfAccounts. Admitted.

Definition stateAfterTransaction (hdr: BlockHeader) (s: StateOfAccounts) (t: Transaction): StateOfAccounts * TransactionResult :=
  let (si, r) := stateAfterTransactionAux s t in
  (applyGasRefundsAndRewards hdr si r, r).

Definition stateAfterTransactions  (hdr: BlockHeader) (s: StateOfAccounts) (ts: list Transaction): StateOfAccounts * list TransactionResult :=
  List.fold_left (fun s t =>
                    let '(si, rl) := s in
                    let (sf, r) := stateAfterTransaction hdr si t in (sf, r::rl)) ts (s,[]).

Record Withdrawal:=
  {
    recipient: evm.address;
    value_wei: N;
  }.

Record Block :=
  {
    transactions: list Transaction;
    header: BlockHeader;
    ommers: list BlockHeader;
    withdrawals: list Withdrawal;
  }.

Definition applyWithdrawals (s: StateOfAccounts) (ws: list Withdrawal): StateOfAccounts.
Proof. Admitted.

Definition applyBlockReward (s: StateOfAccounts) (num_omsers: nat): StateOfAccounts.
Proof. Admitted.

Definition stateAfterBlock (b: Block) (s: StateOfAccounts): StateOfAccounts * list TransactionResult :=
  let '(s, tr) := stateAfterTransactions (header b) s (transactions b) in
  let s:= applyWithdrawals s (withdrawals b) in
  (applyBlockReward s (length (ommers b)), tr).

(* Coq model of the Chain type in C++ *)
Definition Chain: Type. Admitted.
Inductive Revision := Shanghai | Frontier.
Axiom sender: Transaction -> evm.address.




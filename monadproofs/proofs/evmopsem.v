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

(* txindex can be used to store incarnation numbers *)
Definition stateAfterTransaction (hdr: BlockHeader) (txindex: nat) (s: StateOfAccounts) (t: Transaction): StateOfAccounts * TransactionResult :=
  let (si, r) := stateAfterTransactionAux s t in
  (applyGasRefundsAndRewards hdr si r, r).

Fixpoint stateAfterTransactions' (hdr: BlockHeader) (s: StateOfAccounts) (ts: list Transaction) (start:nat) (prevResults: list TransactionResult): StateOfAccounts * list TransactionResult :=
  match ts with
  | [] => (s, prevResults)
  | t::tls => let (sf, r) := stateAfterTransaction hdr start s t in
              stateAfterTransactions' hdr sf tls (1+start) (prevResults++[r])
  end.
    
    
Definition stateAfterTransactions  (hdr: BlockHeader) (s: StateOfAccounts) (ts: list Transaction): StateOfAccounts * list TransactionResult := stateAfterTransactions' hdr s ts 0 [].

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




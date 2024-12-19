Require Import QArith.
Require Import Lens.Elpi.Elpi.
Require Import bedrock.lang.cpp.

Import cQp_compat.

(*
int x;
int y;

\pre x |-> 1
\post x |-> 2
void f()

\pre y |-> 1
\post y |-> 2
void g()

Exists q v, x |-q> v
wp (read x)

(Exists v,  x |-1> v)(write x foo) (x |-> foo)


x |-0.4-> 1 ** x |-0.6-> 1 |-- x |-1.0-> 1
void h()
{
  x=1;
  y=1;
  f();

  g();
}
*)
#[local] Open Scope Z_scope.

(*
Require Import EVMOpSem.evmfull. *)
Require Import stdpp.gmap.
Axiom GlobalState: Set.
Notation StateOfAccounts := GlobalState.
Axiom Transaction : Set.
Module evm.
  Axiom log_entry: Set.
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

Record Block :=
  {
    transactions: list Transaction;
    header: BlockHeader;
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
  Definition R (newState: StateOfAccounts): Rep.
    
  Admitted. (* To be defined later. something like: [_field db_ |-> DbR blockPreState ** _field deltas |-> StateDeltasR blockPreState newState] *)


  Definition inv  (commitedIndexLoc: gname)
    : Rep :=
    Exists committedIndex: nat,
        R (fst (stateAfterTransactions (header b) blockPreState (List.firstn committedIndex (transactions b))))
          ** pureR (storedAtGhostLoc (1/3)%Q commitedIndexLoc committedIndex).

  Record glocs :=
    {
      commitedIndexLoc: gname;
      invLoc: gname;
    }.
  
  Definition Rc (q: Qp) (g: glocs) : Rep  :=
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

Require Import bedrock_auto.tests.data_class.exb.
Require Import bedrock_auto.tests.data_class.exb_names.
Open Scope cpp_name.
Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)

    (* set_value() passes the resource/assertion P to the one calling get_future->wait()*)
  Definition PromiseR (q:Qp) (g: gname) (P: mpred) : Rep. Proof. Admitted.

  Lemma sharePromise q1 q2 g P:  PromiseR (q1+q2) g P |-- PromiseR q1 g P **  PromiseR q2 g P.
  Proof. Admitted.
    
  
  Definition promise_constructor_spec (this:ptr) :WpSpec mpredI val val :=
    \pre{P:mpred} emp
    \post Exists g:gname, this |->  PromiseR 1 g P.
  
  Definition promise_setvalue_spec (this:ptr) :WpSpec mpredI val val :=
    \prepost{(P:mpred) (q:Qp) (g:gname)} this |-> PromiseR q g P
    \pre P
    \post emp.

  Definition promise_getfuture_wait_spec (this:ptr) :WpSpec mpredI val val :=
    \prepost{(P:mpred) (q:Qp) (g:gname)} this |-> PromiseR q g P
    \post P.
  
  (* defines how [c] is represented in memory as an object of class Chain. this predicate asserts [q] ownership of the object, assuming it can be shared across multiple threads  *)
  Definition ChainR (q: Qp) (c: Chain): Rep. Proof. Admitted.

  (* defines how [c] is represented in memory as an object of class Chain *)
  Definition PriorityPoolR (q: Qp) (c: PriorityPool): Rep. Proof. Admitted.

  Definition VectorR {ElemType} (cppType: type) (elemRep: ElemType -> Rep) (q:Qp) (t:list ElemType): Rep. Proof. Admitted.
  Definition TransactionR (t: Transaction) : Rep. Proof using. Admitted.
  Definition BlockR (q: Qp) (c: Block): Rep :=
    _field ``::monad::Block::transactions`` |-> VectorR (Tnamed ``::monad::Transaction``) TransactionR q (transactions c)
    ** structR ``::monad::Block`` q.
  Definition ResultR {T} (trep: T -> Rep) (t:T): Rep. Proof. Admitted.
  Definition ReceiptR (t: TransactionResult): Rep. Admitted.
  

(*  
  Definition execute_block_spec : WpSpec mpredI val val :=
    \arg{chainp :ptr} "chain" (Vref chainp)
    \prepost{(qchain:Qp) (chain: Chain)} chainp |-> ChainR qchain chain
    \arg "rev" (valOfRev Shanghai)
    \arg{blockp: ptr} "block" (Vref blockp)
    \prepost{(block: Block)} blockp |-> BlockR 1 block (* is this modified? if so, fix this line, else make it const in C++ code? *)
    \arg{block_statep: ptr} "block_state" (Vref block_statep)
    \prepost{(preBlockState: StateOfAccounts) (gl: BlockState.glocs)}
      block_statep |-> BlockState.Rc block preBlockState 1 gl
    \arg{block_hash_bufferp: ptr} "block_hash_buffer" (Vref block_hash_bufferp)
    \arg{priority_poolp: ptr} "priority_pool" (Vref priority_poolp)
    \prepost{priority_pool: PriorityPool} priority_poolp |-> PriorityPoolR 1 priority_pool
    \post storedAtGhostLoc (2/3)%Q (BlockState.commitedIndexLoc gl) (length (transactions block)).
 *)
  
  Definition execute_block_simpler : WpSpec mpredI val val :=
    \arg{chainp :ptr} "chain" (Vref chainp)
    \prepost{(qchain:Qp) (chain: Chain)} chainp |-> ChainR qchain chain
(*     \arg "rev" (valOfRev Shanghai) *)
    \arg{blockp: ptr} "block" (Vref blockp)
    \prepost{qb (block: Block)} blockp |-> BlockR qb block
    \arg{block_statep: ptr} "block_state" (Vref block_statep)
    \pre{(preBlockState: StateOfAccounts)}
      block_statep |-> BlockState.R block preBlockState preBlockState
    \arg{block_hash_bufferp: ptr} "block_hash_buffer" (Vref block_hash_bufferp)
    \arg{priority_poolp: ptr} "priority_pool" (Vref priority_poolp)
    \prepost{priority_pool: PriorityPool} priority_poolp |-> PriorityPoolR 1 priority_pool (* TODO: write a spec of priority_pool.submit() *)
    \post{retp}[Vptr retp]
      let (actual_final_state, receipts) := stateAfterTransactions (header block) preBlockState (transactions block) in
      retp |-> VectorR (Tnamed ``::monad::Receipt``) ReceiptR 1 receipts
      ** block_statep |-> BlockState.R block preBlockState actual_final_state.

Import namemap.
Locate symbols.
Import translation_unit.
Check (NM.elements module.(symbols)).
Require Import List.
Locate BS.String.
Import bytestring_core.
Definition xx:=
  (bytestring_core.BS.String "s"
                                 (bytestring_core.BS.String "t"
                                    (bytestring_core.BS.String "d" bytestring_core.BS.EmptyString))).
Require Import bedrock.auto.cpp.
Require Import bedrock.auto.cpp.specs.

Context  {MOD : exb.module ⊧ CU}.
(* Node::Node(Node*,int) *)
Check exb.module.

cpp.spec (Ninst
   "monad::execute_block(const monad::Chain&, monad::Block&, monad::BlockState&, const monad::BlockHashBuffer&, monad::fiber::PriorityPool&)"
   [Avalue (Eint 11 "enum evmc_revision")]) as exb_spec with (execute_block_simpler).

Require Import bedrock.auto.cpp.tactics4.

Ltac slauto :=                                                                                                        go; (* TODO: hide evars *)                                                                                        try name_locals;                                                                                                  tryif progress(try (ego; eagerUnifyU; go; fail); try (apply False_rect; try contradiction; try congruence; try nia; fail); try autorewrite with syntactic equiv iff slbwd in *; try rewrite left_id (* in equiv rw db but doesnt work *))                  
  then slauto  else idtac.


  cpp.spec
    "std::vector<monad::Transaction, std::allocator<monad::Transaction>>::size() const"
    as tvector_spec with
      (fun (this:ptr) =>
         \prepost{q ts} this |-> VectorR (Tnamed ``::monad::Transaction``) TransactionR q (ts)
         \post[Vn (lengthN ts)] (emp:mpred)
      ).

Lemma prf: denoteModule module ** tvector_spec |-- exb_spec.
Proof using.
  verify_spec'.
  name_locals.
  unfold BlockR.
  slauto.
  ego.
  provePure.
  Print pointer_size.
  hnf.

  invoke.wp_minvoke_O.body module Direct
    "const std::vector<monad::Transaction, std::allocator<monad::Transaction>>" "unsigned long"%cpp_type
    "unsigned long()()" "std::vector<monad::Transaction, std::allocator<monad::Transaction>>::size() const"
    (blockp ,, o_field CU "monad::Block::transactions") [] None
    (λ x : val,
        ∃ array_sizeN : N, [| x = Vn array
                                     
  ego.
  name_locals.
  rewrite <- wp_operand_array_new.
  work.
  go.
  
Compute (lengthN defns).
Check defns.
Import NM.
Compute (nth_error defns 0).
Search NM.key.
Print defns.
(* this is the entry we need to verify:
 Ninst
   "monad::execute_block(const monad::Chain&, monad::Block&, monad::BlockState&, const monad::BlockHashBuffer&, monad::fiber::PriorityPool&)"
   [Avalue (Eint 12 "enum evmc_revision")];

*)
  

  
  Definition TransactionR (q: Qp) (t: Transaction): Rep. Proof. Admitted.

  Definition optionAddressR (q:Qp) (oaddr: option evm.address): Rep. Proof. Admitted.



  Definition execute_spec : WpSpec mpredI val val :=
    \arg{chainp :ptr} "chain" (Vref chainp)
    \prepost{(qchain:Qp) (chain: Chain)} chainp |-> ChainR qchain chain
    \arg{i:nat} "i" (Vnat i)
    \arg{txp} "tx" (Vref txp)
    \pre{(qtx: Qp) (block: Block) t} Exists t, [| nth_error (transactions block) i = Some t |]
    \pre txp |-> TransactionR qtx t
    \arg{senderp} "sender" (Vref senderp)
    \pre{qs} senderp |-> optionAddressR qs (Some (Message.caller t))
    \arg{hdrp: ptr} "hdr" (Vref hdrp)
    \arg{block_hash_bufferp: ptr} "block_hash_buffer" (Vref block_hash_bufferp)
    \arg{block_statep: ptr} "block_state" (Vref block_statep)
    \prepost{(preBlockState: StateOfAccounts) (gl: BlockState.glocs)}
      block_statep |-> BlockState.Rc block preBlockState 1 gl (* the concurrent invariant does not hold during BlockState.merge : Fix *)
    \arg{prevp: ptr} "prev" (Vref prevp)
    \prepost{prg: gname} prevp |-> PromiseR (1/2) prg (storedAtGhostLoc (2/3)%Q (BlockState.commitedIndexLoc gl) (i-1))
    \post{retp}[Vptr retp]
      let actualPreState := fst (stateAfterTransactions (header block) preBlockState (firstn i (transactions block))) in
      let '(_, result) := stateAfterTransactionAux actualPreState t in
       retp |-> ResultR ReceiptR result
       ** storedAtGhostLoc (2/3)%Q (BlockState.commitedIndexLoc gl) i.

  Record State :=
    {
      original: gmap evm.address account.state;
      newStates: gmap evm.address (list account.state); (* head is the latest *)
      blockStatePtr: ptr;
    }.

  (* not supposed to be shared, so no fraction *)
  Definition StateR (s: State): Rep. Proof. Admitted.

  Definition preImpl2State (blockStatePtr: ptr) (senderAddr: evm.address) (sender: account.state): State:=
    {|
      blockStatePtr:= blockStatePtr;
      newStates:= ∅;
      original := <[senderAddr := sender]>∅;
      |}.

  Definition tnonce (t: Transaction) : N. Proof. Admitted.

  Definition EvmcResultR (r: TransactionResult): Rep. Proof. Admitted.
  
  Definition execute_impl2_spec : WpSpec mpredI val val :=
    \arg{chainp :ptr} "chain" (Vref chainp)
    \prepost{(qchain:Qp) (chain: Chain)} chainp |-> ChainR qchain chain
    \arg{txp} "tx" (Vref txp)
    \pre{(qtx: Qp) (i:nat) (block: Block) t} Exists t, [| nth_error (transactions block) i = Some t |]
    \pre txp |-> TransactionR qtx t
    \arg{senderp} "sender" (Vref senderp)
    \pre{qs} senderp |-> optionAddressR qs (Some (Message.caller t))
    \arg{hdrp: ptr} "hdr" (Vref hdrp)
    \arg{block_hash_bufferp: ptr} "block_hash_buffer" (Vref block_hash_bufferp)
    \arg{statep: ptr} "state" (Vref statep)
    \pre{(blockStatePtr: ptr) (senderAddr: evm.address) (senderAcState: account.state)}
      statep |-> StateR (preImpl2State blockStatePtr senderAddr senderAcState)
    \prepost{(preBlockState: StateOfAccounts) (gl: BlockState.glocs)}
      blockStatePtr |-> BlockState.Rc block preBlockState 1 gl
    \pre [| account.nonce senderAcState = tnonce t|]
    \post{retp}[Vptr retp] Exists stateFinal,
      let actualPreState := fst (stateAfterTransactions (header block) preBlockState (firstn i (transactions block))) in
      let '(actualPostState, result) := stateAfterTransactionAux actualPreState t in
      retp |-> ResultR EvmcResultR result 
      ** statep |-> StateR stateFinal
      ** [| match original stateFinal !! senderAddr with
            | Some senderAcState' => senderAcState'= senderAcState
            | _ => False
            end |]
      ** [| (forall acAddr acState, original stateFinal !! acAddr = Some acState -> Some acState = actualPreState !! acAddr) (* original matches the result of sequential execution of previous transactions *)
            ->  (forall acAddr acNewStates, newStates stateFinal !! acAddr = Some acNewStates ->
                          match actualPostState !! acAddr with
                          | Some actualAcPostState => acNewStates=[actualAcPostState]
                          | None => False
                          end) |].
  
End with_Sigma.
Module Generalized1.
  Record State :=
    {
      assumptionsOnPreState: GlobalState -> Prop ;
      stateUpdates: GlobalState -> GlobalState;
      blockStatePtr: ptr;
    }.
  
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)
    Definition StateR (s: State): Rep. Proof. Admitted.

  Definition can_merge (this:ptr): WpSpec mpredI val val :=
    \prepost{(preState curState: StateOfAccounts) (block: Block)}
      this |-> BlockState.R block preState curState
    \arg{statep: ptr} "prev" (Vref statep)
    \pre{finalS}
      statep |-> StateR finalS
    \post{b} [Vbool b] if b then [|assumptionsOnPreState finalS curState|] else [| True |].
    
    
End Generalized1.
Module Generalized2.
  Class SplitGlobalState (Tcomm Trest: Type):=
    {
      isoL: (Tcomm * Trest) -> GlobalState;
      isoR: GlobalState -> (Tcomm * Trest);
      isIso: ssrfun.cancel isoL isoR;
    }.

  Context {Tcomm Trest: Type} {ss: SplitGlobalState Tcomm Trest}.

    Record State :=
    {
      assumptionsOnPreState: GlobalState -> Prop ;
      commStateUpdates: Tcomm -> Tcomm;
      restStateUpdates: Trest -> Trest;
      blockStatePtr: ptr;
    }.
    
End Generalized2.

Require Import QArith.
Require Import Lens.Elpi.Elpi.
Require Import bedrock.lang.cpp.
Require Import stdpp.gmap.
Require Import monad.proofs.misc.
Require Import monad.proofs.libspecs.
Require Import monad.proofs.evmopsem.
Import linearity.
Require Import bedrock.auto.invariants.
Require Import bedrock.auto.cpp.proof.

Require Import bedrock.auto.cpp.tactics4.

Notation resultn :=
                  (Ninst (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "basic_result"))
                   [Atype (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Receipt")));
                    Atype
                      (Tnamed
                         (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code")) [Atype (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                    Atype
                      (Tnamed
                         (Ninst (Nscoped (Nscoped (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "experimental")) (Nid "policy")) (Nid "status_code_throw"))
                            [Atype (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Receipt")));
                             Atype
                               (Tnamed
                                  (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                                     [Atype (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                             Atype "void"]))]).

Import cQp_compat.

#[local] Open Scope Z_scope.
(*
Require Import EVMOpSem.evmfull. *)
Import cancelable_invariants.
  
Module BlockState. Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)


  Context (blockPreState: StateOfAccounts). (* BlockState is a type that makes sense in the context of a block and the state before the block  *)
  (** defines how the Coq (mathematical) state of Coq type [StateOfAccounts] is represented as a C++ datastructure in the fields of the BlockState class.
      [blockPreState] is the state at the beginning of the block.  newState
   *)
    

  Record glocs :=
    {
      cmap: gname;
    }.

  Definition Rauth (g: glocs) (newState: StateOfAccounts): Rep.
  Proof using blockPreState. Admitted. (* To be defined later. something like: [_field db_ |-> DbR blockPreState ** _field deltas |-> StateDeltasR blockPreState newState] *)

  Definition Rfrag (q:Qp) (g: glocs): Rep.
  Proof using blockPreState. Admitted.

  (* TODO: move to a proofmisc file and replace by a lemma about just binary splitting *)
  Lemma split_frag {T} q g (l : list T):
    Rfrag q g -|- Rfrag (q/(N_to_Qp (1+ lengthN l))) g ** 
    ([∗ list] _ ∈ l,  (Rfrag (q*/(N_to_Qp (1+ lengthN l))) g)).
  Proof using. Admitted.

  (* TODO: move to a proofmisc file *)
  Lemma split_frag_loopinv {T} q g (l : list T) (i:nat) (prf: i=0):
    Rfrag q g -|- Rfrag (q/(N_to_Qp (1+ lengthN l))) g ** 
    ([∗ list] _ ∈ (drop i l),  (Rfrag (q*/(N_to_Qp (1+ lengthN l))) g)).
  Proof using.
    subst.  autorewrite with syntactic. apply split_frag.
  Qed.

End with_Sigma. End BlockState.


(* Coq model of the priority pool type in C++ *)
Import bedrock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.

Require Import monad.asts.exb.

Open Scope cpp_name.
Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)

   
  (* defines how [c] is represented in memory as an object of class Chain. this predicate asserts [q] ownership of the object, assuming it can be shared across multiple threads  *)
  Definition ChainR (q: Qp) (c: Chain): Rep. Proof. Admitted.

  Lemma ChainR_split_loopinv {T} q (b: Chain) (l : list T) (i:nat) (p:i=0):
    ChainR q b -|- ChainR (q/(N_to_Qp (1+ lengthN l))) b ** 
    ([∗ list] _ ∈ (drop i l),  (ChainR (q*/(N_to_Qp (1+ lengthN l))) b)).
  Proof using. Admitted.

 
  Definition TransactionR (q:Qp) (tq: Transaction) : Rep. Proof using. Admitted.
  #[global] Instance learnTrRbase: LearnEq2 TransactionR:= ltac:(solve_learnable).

  Definition BheaderR (q:Qp) (hdr: BlockHeader) : Rep. Proof. Admitted.
  
  Definition BlockR (q: Qp) (c: Block): Rep :=
    _field "::monad::Block::transactions" |-> VectorR (Tnamed "::monad::Transaction") (fun t => TransactionR q t) q (transactions c)
    ** _field "::monad::Block::header" |-> BheaderR q (header c)
      ** structR "::monad::Block" q.
  
  Definition ResultR {T} (trep: T -> Rep) (t:T): Rep. Proof. Admitted.
  Definition ReceiptR (t: TransactionResult): Rep. Admitted.
  
  Definition valOfRev (r : Revision) : val := Vint 0. (* TODO: fix *)

  Record BlockHashBuffer :=
    { fullHistory: list N;
      startIndex: N}.

  Definition lastIndex (b: BlockHashBuffer) : N := startIndex b + lengthN (fullHistory b).

  (* move to utils
  Definition rotate_list {A} (r : Z) (elems : list A) : list A :=
    let sz : Z := length elems in
    let split_count : nat := Z.to_nat $ r `mod` length elems in
    drop split_count elems ++ take split_count elems.
*)  
  Definition BlockHashBufferR (q:Qp) (m: BlockHashBuffer) : Rep :=
    _field "monad::n_" |-> u64R q (lastIndex m).
    (* ** _field "monad::b_" |-> arrayR ... (rotate_list ) *)
  Lemma bhb_split_sn {T} q (b: BlockHashBuffer) (l : list T):
    BlockHashBufferR q b -|- BlockHashBufferR (q/(N_to_Qp (1+ lengthN l))) b ** 
    ([∗ list] _ ∈ l,  (BlockHashBufferR (q*/(N_to_Qp (1+ lengthN l))) b)).
  Proof using. Admitted.

  Lemma bhb_splitl_loopinv {T} q (b: BlockHashBuffer) (l : list T) (i:nat) (p:i=0):
    BlockHashBufferR q b -|- BlockHashBufferR (q/(N_to_Qp (1+ lengthN l))) b ** 
    ([∗ list] _ ∈ (drop i l),  (BlockHashBufferR (q*/(N_to_Qp (1+ lengthN l))) b)).
  Proof using.
    intros. subst. autorewrite with syntactic.
    apply bhb_split_sn.
  Qed.
  

  
  Definition execute_block_simpler : WpSpec mpredI val val :=
    \arg{chainp :ptr} "chain" (Vref chainp)
    \prepost{(qchain:Qp) (chain: Chain)} chainp |-> ChainR qchain chain
(*     \arg "rev" (valOfRev Shanghai) *)
    \arg{blockp: ptr} "block" (Vref blockp)
    \prepost{qb (block: Block)} blockp |-> BlockR qb block
    \arg{block_statep: ptr} "block_state" (Vref block_statep)
    \pre{(preBlockState: StateOfAccounts) g qf}
       block_statep |-> BlockState.Rauth preBlockState g preBlockState
    \prepost block_statep |-> BlockState.Rfrag preBlockState qf g
    \arg{block_hash_bufferp: ptr} "block_hash_buffer" (Vref block_hash_bufferp)
    \prepost{buf qbuf} block_hash_bufferp |-> BlockHashBufferR qbuf buf
    \arg{priority_poolp: ptr} "priority_pool" (Vref priority_poolp)
    \prepost{priority_pool: PriorityPool} priority_poolp |-> PriorityPoolR 1 priority_pool (* TODO: write a spec of priority_pool.submit() *)
    \post{retp}[Vptr retp]
      let (actual_final_state, receipts) := stateAfterBlock block preBlockState in
      retp |-> VectorR (Tnamed "::monad::Receipt") ReceiptR 1 receipts
      ** block_statep |-> BlockState.Rauth preBlockState g actual_final_state.

Import namemap.
Import translation_unit.
Require Import List.
Import bytestring_core.
Require Import bedrock.auto.cpp.
Require Import bedrock.auto.cpp.specs.


Context  {MODd : exb.module ⊧ CU}.
  cpp.spec (Ninst
   "monad::execute_block(const monad::Chain&, monad::Block&, monad::BlockState&, const monad::BlockHashBuffer&, monad::fiber::PriorityPool&)"
   [Avalue (Eint 11 "enum evmc_revision")]) as exbb_spec with (execute_block_simpler).


  cpp.spec 
  "monad::reset_promises(unsigned long)" as reset_promises with
      ( \with (Transaction: Type)
        \arg{transactions: list Transaction} "n" (Vn (lengthN transactions))
       \pre{newPromisedResource}
           _global "monad::promises" |-> parrayR (Tnamed "boost::fibers::promise<void>") (fun i t => PromiseUnusableR) transactions
       \post Exists prIds, _global "monad::promises" |-> parrayR (Tnamed "boost::fibers::promise<void>") (fun i t => PromiseR (prIds i) (newPromisedResource i t)) transactions).
  
cpp.spec
  "monad::compute_senders(const monad::Block&, monad::fiber::PriorityPool&)"
  as compute_senders
  with (
    \arg{blockp: ptr} "block" (Vref blockp)
    \prepost{qb (block: Block)} blockp |-> BlockR qb block
    \arg{priority_poolp: ptr} "priority_pool" (Vref priority_poolp)
    \prepost{priority_pool: PriorityPool} priority_poolp |-> PriorityPoolR 1 priority_pool
    \prepost
        _global "monad::promises" |->
          parrayR
            (Tnamed "boost::fibers::promise<void>")
            (fun i t => PromiseUnusableR)
            (transactions block)
    \pre Exists garbage,
        _global "monad::senders" |->
          arrayR
            (Tnamed "std::optional<evmc::address>")
            (fun t=> optionAddressR 1 (garbage t))
            (transactions block)
    \post _global "monad::senders" |->
          arrayR
            (Tnamed "std::optional<evmc::address>")
            (fun t=> optionAddressR 1 (Some (sender t)))
            (transactions block)).


Definition resultT := (Tnamed resultn).

Definition oResultT := (Tnamed (Ninst "std::optional" [Atype resultT])).

cpp.spec (Ninst "monad::execute_transactions(const monad::Block&, monad::fiber::PriorityPool&, const monad::Chain&, const monad::BlockHashBuffer&, monad::BlockState &)" [Avalue (Eint 11 "enum evmc_revision")]) as exect with (
    \arg{blockp: ptr} "block" (Vref blockp)
    \prepost{qb (block: Block)} blockp |-> BlockR qb block
    \pre [| lengthN (transactions block) < 2^64 - 1 |]%N
    \arg{priority_poolp: ptr} "priority_pool" (Vref priority_poolp)
    \prepost{priority_pool: PriorityPool} priority_poolp |-> PriorityPoolR 1 priority_pool
    \arg{chainp :ptr} "chain" (Vref chainp)
    \prepost{(qchain:Qp) (chain: Chain)} chainp |-> ChainR qchain chain
    \arg{block_hash_bufferp: ptr} "block_hash_buffer" (Vref block_hash_bufferp)
    \prepost{buf qbuf} block_hash_bufferp |-> BlockHashBufferR qbuf buf
    \arg{block_statep: ptr} "block_state" (Vref block_statep)
    \pre{(preBlockState: StateOfAccounts) g qf}
       block_statep |-> BlockState.Rauth preBlockState g preBlockState
    \prepost block_statep |-> BlockState.Rfrag preBlockState qf g
    \prepost
        _global "monad::promises" |->
          parrayR
            (Tnamed "boost::fibers::promise<void>")
            (fun i t => PromiseUnusableR)
            ((map (fun _ => ()) (transactions block))++[()])
    \pre Exists garbage,
        _global "monad::results" |->
          arrayR
            oResultT
            (fun t=> libspecs.optionR resultT ReceiptR 1 (garbage t))
            (transactions block)
    \pre{qs} _global "monad::senders" |->
          arrayR
            (Tnamed "std::optional<evmc::address>")
            (fun t=> optionAddressR qs (Some (sender t)))
            (transactions block)
   \post
      let (actual_final_state, receipts) := stateAfterTransactions (header block) preBlockState (transactions block) in
      _global "monad::senders" |-> arrayR oResultT (fun r => libspecs.optionR resultT ReceiptR 1 (Some r)) receipts
      ** block_statep |-> BlockState.Rauth preBlockState g actual_final_state

    ).
    
    (* \pre assumes that the input is a valid transaction encoding (sender computation will not fail) *)
    cpp.spec "monad::recover_sender(const monad::Transaction&)"  as recover_sender with
        (
    \arg{trp: ptr} "tr" (Vref trp)
    \prepost{qt (tr: Transaction)} trp |-> TransactionR qt tr
    \post{retp} [Vptr retp] retp |-> optionAddressR 1 (Some (sender tr))).


    cpp.spec (fork_task_nameg "monad::compute_senders(const monad::Block&, monad::fiber::PriorityPool&)::@0") as fork_task with (forkTaskSpec "monad::compute_senders(const monad::Block&, monad::fiber::PriorityPool&)::@0").

    (* todo: generalize over the template arg *)
cpp.spec 
  "std::vector<monad::Transaction, std::allocator<monad::Transaction>>::operator[](unsigned long) const" as vector_op_monad with (vector_opg "monad::Transaction").

  cpp.spec (Nscoped 
              "monad::compute_senders(const monad::Block&, monad::fiber::PriorityPool&)::@0" (Nfunction function_qualifiers.N Ndtor []))  as cslamdestr inline.

(*
  erewrite sizeof.size_of_compat;[| eauto; fail| vm_compute; reflexivity].
*)
  
  Definition execute_transaction_spec : WpSpec mpredI val val :=
    \arg{chainp :ptr} "chain" (Vref chainp)
    \prepost{(qchain:Qp) (chain: Chain)} chainp |-> ChainR qchain chain
    \arg{i:nat} "i" (Vnat i)
    \arg{txp} "tx" (Vref txp)
    \prepost{qtx t} txp |-> TransactionR qtx t
    \arg{senderp} "sender" (Vref senderp)
    \prepost{qs} senderp |-> optionAddressR qs (Some (sender t))
    \arg{hdrp: ptr} "hdr" (Vref hdrp)
    \prepost{qh header} hdrp |-> BheaderR qh header
    \arg{block_hash_bufferp: ptr} "block_hash_buffer" (Vref block_hash_bufferp)
    \arg{block_statep: ptr} "block_state" (Vref block_statep)
    \prepost{g qf preBlockState} block_statep |-> BlockState.Rfrag preBlockState qf g
    \arg{prevp: ptr} "prev" (Vref prevp)
    \pre{(prg: gname) (prevTxGlobalState: StateOfAccounts) (OtherPromisedResources:mpred)}
        prevp |-> PromiseConsumerR prg (OtherPromisedResources ** block_statep |-> BlockState.Rauth preBlockState g prevTxGlobalState)
    \post{retp}[Vptr retp] OtherPromisedResources ** prevp |-> PromiseUnusableR **
      let '(finalState, result) := stateAfterTransaction header i prevTxGlobalState t in
       retp |-> ResultR ReceiptR result
         ** block_statep |->  BlockState.Rauth preBlockState g finalState.

cpp.spec ((Ninst
             (Nscoped (Nglobal (Nid "monad"))
                (Nfunction function_qualifiers.N (Nf "execute")
                   [Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Chain")))); "unsigned long"%cpp_type; Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Transaction"))));
                    Tref (Tconst (Tnamed (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "optional")) [Atype (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "address")))])));
                    Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockHeader")))); Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockHashBuffer"))));
                    Tref (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockState"))); Tref (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "fibers")) (Nid "promise")) [Atype "void"]))]))
             [Avalue (Eint 11 (Tenum (Nglobal (Nid "evmc_revision"))))])) as ext1 with (execute_transaction_spec).
  
(*       

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
*)  
End with_Sigma.
(*
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
(* demo:
- int sum(int x, int y)
- double(int & x, int & res) : show ocode using double in parallel
- uint64 gcd(uint64 x, uint64 y)
- struct Point. void double(Point & x)
- llist::rev: spec, why trust gallina rev: show lemmas

- forkTask
*)
*)

Require Import QArith.
Require Import Lens.Elpi.Elpi.
Require Import bedrock.lang.cpp.

Import cQp_compat.

#[local] Open Scope Z_scope.

(*
Require Import EVMOpSem.evmfull. *)
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

Require Import monad.asts.exb.
Require Import monad.asts.exb_names.

Open Scope cpp_name.
Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)

    (* set_value() passes the resource/assertion P to the one calling get_future->wait()*)
  Definition PromiseR (g: gname) (P: mpred) : Rep. Proof. Admitted.
  Definition PromiseProducerR (g: gname) (P: mpred) : Rep. Proof. Admitted.
  Definition PromiseConsumerR (g: gname) (P: mpred) : Rep. Proof. Admitted.
  Definition PromiseUnusableR: Rep. Proof. Admitted.

  Lemma sharePromise g P:  PromiseR g P -|- PromiseProducerR g P **  PromiseConsumerR g P.
  Proof. Admitted.
   
  (* defines how [c] is represented in memory as an object of class Chain. this predicate asserts [q] ownership of the object, assuming it can be shared across multiple threads  *)
  Definition ChainR (q: Qp) (c: Chain): Rep. Proof. Admitted.

  (* defines how [c] is represented in memory as an object of class Chain *)
  Definition PriorityPoolR (q: Qp) (c: PriorityPool): Rep. Proof. Admitted.

  Definition VectorRbase (cppType: type) (q:Qp) (base: ptr) (size: N): Rep.
  Proof using.
    (*Exists cap, 
       _field "base" |-> ptrR q base
       ** _field "size" |-> intR q size
       ** _field "capacity" |-> intR q cap *)
  Admitted.
  
 Definition VectorR {ElemType} (cppType: type) (elemRep: ElemType -> Rep) (q:Qp) (lt:list ElemType): Rep :=
   Exists (base: ptr), VectorRbase cppType q base (lengthN lt)
       ** pureR (base |-> arrayR cppType elemRep lt).
 
  Definition TransactionR (q:Qp) (t: Transaction) : Rep. Proof using. Admitted.
 
  Definition BlockR (q: Qp) (c: Block): Rep :=
    _field ``::monad::Block::transactions`` |-> VectorR (Tnamed ``::monad::Transaction``) (fun t => TransactionR q t) q (transactions c)
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

(*
                         (Ninst
                            "monad::compute_senders(std::optional<evmc::address>*, const monad::Block&, monad::fiber::PriorityPool&)"
                            [Avalue (Eint 0 "enum evmc_revision")])

 *)

Require Import bedrock.auto.cpp.tactics4.

Ltac slauto := go; try name_locals; tryif progress(try (ego; eagerUnifyU; go; fail); try (apply False_rect; try contradiction; try congruence; try nia; fail); try autorewrite with syntactic equiv iff slbwd in *; try rewrite left_id)
  then slauto  else idtac.

Context  {MODd : exb.module ⊧ CU}.
(* Node::Node(Node*,int) *)
  Definition promise_constructor_spec (this:ptr) :WpSpec mpredI val val :=
    \pre{P:mpred} emp
    \post Exists g:gname, this |->  PromiseR g P.
  
  cpp.spec "boost::fibers::promise<void>::set_value()"  as set_value with
     (fun (this:ptr) =>
    \pre{(P:mpred) (g:gname)} this |-> PromiseProducerR g P
    \pre P
    \post emp).

  cpp.spec (Ninst
   "monad::execute_block(const monad::Chain&, monad::Block&, monad::BlockState&, const monad::BlockHashBuffer&, monad::fiber::PriorityPool&)"
   [Avalue (Eint 11 "enum evmc_revision")]) as exbb_spec with (execute_block_simpler).

  cpp.spec
    "std::vector<monad::Transaction, std::allocator<monad::Transaction>>::size() const"
    as tvector_spec with
      (fun (this:ptr) =>
         \prepost{q base size} this |-> VectorRbase (Tnamed ``::monad::Transaction``)  q base size
         \post[Vn size] (emp:mpred)
      ).
  Print lt.


  Definition optionAddressR (q:Qp) (oaddr: option evm.address): Rep. Proof. Admitted.

Definition parrayR  {T:Type} ty (Rs : nat -> T -> Rep) (l: list T) : Rep :=
  .[ ty ! length l ] |-> validR ** [| is_Some (size_of _ ty) |] **
  (* ^ both of these are only relevant for empty arrays, otherwise, they are implied by the
     following conjunct *)
     [∗ list] i ↦ li ∈ l, .[ ty ! Z.of_nat i ] |-> (type_ptrR ty ** Rs i li).


  Lemma arrR_cons0 ty R Rs :
    arrR ty (R :: Rs) -|- type_ptrR ty ** (.[ ty ! 0 ] |-> R) ** .[ ty ! 1 ] |-> arrR ty Rs.
  Proof.
    rewrite arrR_eq/arrR_def /= !_offsetR_sep !_offsetR_only_provable.
    apply: (observe_both (is_Some (size_of _ ty))) => Hsz.
    rewrite !_offsetR_sub_0; auto.
    rewrite _offsetR_big_sepL -assoc.
    rewrite _offsetR_succ_sub Nat2Z.inj_succ;
      setoid_rewrite _offsetR_succ_sub; setoid_rewrite Nat2Z.inj_succ.
    iSplit; [ iIntros "(? & ? & ? & ? & ?)" | iIntros "(? & ? & ? & ? & ?)"]; iFrame.
  Qed.

  Lemma arrayR_cons0 {T} ty (R:T->Rep) x xs :
    arrayR ty R (x :: xs) -|- type_ptrR ty ** (.[ ty ! 0 ] |-> R x) ** .[ ty ! 1 ] |-> arrayR ty R xs.
  Proof. rewrite arrayR_eq. unfold arrayR_def. exact: arrR_cons0. Qed.

  Definition offsetR_only_fwd := ([BWD->] _offsetR_only_provable).
  Hint Resolve offsetR_only_fwd: br_opacity.
  Lemma parrayR_cons {T:Type} ty (R : nat -> T -> Rep) (x:T) (xs: list T) :
    parrayR ty R (x :: xs) -|- type_ptrR ty ** (.[ ty ! 0 ] |-> (R 0 x)) ** .[ ty ! 1 ] |-> parrayR ty (fun n => R (S n)) xs.
  Proof using.
    unfold parrayR.
    apply: (observe_both (is_Some (size_of _ ty))) => Hsz.
    repeat rewrite !_offsetR_sub_0; auto.
    repeat rewrite _offsetR_sep.
    repeat rewrite _offsetR_big_sepL.
    repeat rewrite _offsetR_succ_sub.
    repeat setoid_rewrite  _offsetR_succ_sub.
    simpl.
    repeat rewrite Nat2Z.inj_succ.
    repeat rewrite !_offsetR_sub_0; auto.
    setoid_rewrite Nat2Z.inj_succ.
    iSplit; work.
  Qed.
  Opaque parrayR.
  Hypothesis sender: Transaction -> evm.address.


  Hint Rewrite offset_ptr_sub_0 using (auto; apply has_size; exact _): syntactic.

  cpp.spec 
  "monad::reset_promises(unsigned long)" as reset_promises
      with
      (\arg{transactions: list Transaction} "n" (Vn (lengthN transactions))
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

    (* \pre assumes that the input is a valid transaction encoding (sender computation will not fail) *)
    cpp.spec "monad::recover_sender(const monad::Transaction&)"  as recover_sender with
        (
    \arg{trp: ptr} "tr" (Vref trp)
    \prepost{qt (tr: Transaction)} trp |-> TransactionR qt tr
    \post{retp} [Vptr retp] retp |-> optionAddressR 1 (Some (sender tr))).
    (*
  cpp.spec
    "std::vector<monad::Transaction, std::allocator<monad::Transaction>>::size() const"
    as csector_spec with
      (fun (this:ptr) =>
         \prepost{q ts} this |-> VectorR (Tnamed ``::monad::Transaction``) TransactionR q (ts)
         \post[Vn (lengthN ts)] (emp:mpred)
      ).
*)
  Definition lamName :name :=
    "monad::compute_senders(std::optional<evmc::address>*, const monad::Block&, monad::fiber::PriorityPool&)::@0".

  Definition lamBody :option GlobDecl := Eval vm_compute in
    NM.map_lookup lamName (types module).

(*  Definition forkEntry : list (name * ObjValue) := *)

    Print atomic_name_.
  Fixpoint isFunctionNamed2 (fname: ident) (n:name): bool :=
    match n with
    | Nglobal  (Nfunction _ (Nf i) _) => bool_decide (i=fname)
    | Ninst nm _ => isFunctionNamed2 fname nm
    | Nscoped _ (Nfunction _ (Nf i) _) => bool_decide (i=fname)
    | _ => false
    end.

  Fixpoint containsDep (n:name): bool :=
    match n with
    | Ndependent _ => true
    | Nglobal  (Nfunction _ (Nf i) _) => false
    | Ninst nm _ => containsDep nm
    | Nscoped nm (Nfunction _ (Nf i) _) => containsDep nm
    | _ => false
    end.
  
  Definition findBodyOfFnNamed2 module filter :=
    List.filter (fun p => let '(nm, body):=p in filter nm) (NM.elements (symbols module)).


  Definition firstEntryName (l :list (name * ObjValue)) :=
    (List.nth 0 (map fst l) (Nunsupported "impossible")).
  
  Definition fork_task_namei:= Eval vm_compute in (firstEntryName (findBodyOfFnNamed2 exb.module (isFunctionNamed2 "fork_task"))).

  Definition basee3 (n:name) :=
    match n with
    | Ninst (Nscoped (Nglobal (Nid scopename)) _) targs => scopename
    | _ => ""%pstring
    end.

  Definition all_but_last {T:Type} (l: list T):= take (length l -1)%nat l. 
  Definition fork_task_nameg (taskLamStructTy: core.name) :=
    match fork_task_namei with
    | Ninst (Nscoped (Nglobal (Nid scopename)) (Nfunction q (Nf base) argTypes)) templateArgs =>
        let argTypes' := all_but_last argTypes ++  [Tref (Tqualified QC (Tnamed taskLamStructTy))] in
        Ninst (Nscoped (Nglobal (Nid scopename)) (Nfunction q (Nf base) argTypes')) [Atype (Tnamed taskLamStructTy)]
    | _ => Nunsupported "no match"
    end.


  Lemma fork_task_name_inst: exists ty, fork_task_nameg ty = fork_task_namei.
  Proof using.
    unfold fork_task_nameg. unfold fork_task_namei.
    eexists. reflexivity.
  Qed.

  Definition taskOpName : atomic_name := Nfunction function_qualifiers.Nc (Nop OOCall) [].
  
  Definition taskOpSpec (lamStructName: core.name) (objOwnership: Rep) (taskPre: mpred):=
    specify {| info_name :=  (Nscoped lamStructName taskOpName) ;
              info_type := tMethod lamStructName QC "void" [] |}
      (fun (this:ptr) =>
         \prepost this |-> objOwnership
         \pre taskPre
         \post emp).
  
  Definition forkTaskSpec (lamStructName: core.name) : WpSpec mpredI val val :=
    \arg{priority_poolp: ptr} "priority_pool" (Vref priority_poolp)
    \prepost{priority_pool: PriorityPool} priority_poolp |-> PriorityPoolR 1 priority_pool
    \arg{priority} "i" (Vint priority)  
    \arg{task:ptr} "func" (Vref task)
    \pre{objOwnership taskPre} taskOpSpec lamStructName objOwnership taskPre
    \prepost task |-> objOwnership
    \pre taskPre
    \post emp.
  
  Lemma learnVUnsafe e t (r:e->Rep): LearnEq2 (VectorR t r).
  Proof. solve_learnable. Qed.
  Lemma learnVUnsafe2 e t: LearnEq3 (@VectorR e t).
  Proof. solve_learnable. Qed.

  Existing Instance learnVUnsafe2.
  Lemma learnArrUnsafe e t: LearnEq2 (@arrayR _ _ _ e _ t).
  Proof. solve_learnable. Qed.
  Lemma learnpArrUnsafe e t: LearnEq2 (@parrayR e t).
  Proof. solve_learnable. Qed.
  
  Existing Instance learnArrUnsafe.
  Existing Instance learnpArrUnsafe.
  Hint Opaque parrayR: br_opacity.
  
  (* not in use anymore *)
  Lemma promiseArrDecompose (p:ptr) prIds ltr promiseRes:
    p |-> parrayR "boost::fibers::promise<void>"
            (λ (i : nat) (t : Transaction),
               PromiseR (prIds i) (promiseRes i t))
            ltr
   -|- (valid_ptr (p .[ "boost::fibers::promise<void>" ! length ltr ])) **
      [| is_Some (glob_def CU "boost::fibers::promise<void>" ≫= GlobDecl_size_of) |]         **
      ([∗ list] k↦_ ∈ ltr, □ (type_ptr "boost::fibers::promise<void>" (p .[ "boost::fibers::promise<void>" ! k ]))) ∗
      ([∗ list] k↦t ∈ ltr, p .[ "boost::fibers::promise<void>" ! k ] |-> PromiseProducerR (prIds k) (promiseRes k t)) ∗
      ([∗ list] k↦t ∈ ltr, p .[ "boost::fibers::promise<void>" ! k ] |-> PromiseConsumerR (prIds k) (promiseRes k t)).
  Proof using.
    Transparent parrayR. unfold parrayR.
    iSplit.
    - 
      go.
       setoid_rewrite sharePromise.
       go.
       repeat rewrite _at_big_sepL.
       erewrite big_sepL_mono.
       2:{
         intros.
         go.
       }
       simpl. 
       repeat setoid_rewrite big_sepL_sep.
       go.
       setoid_rewrite (@right_id _ _ ((True)%I:mpred));[go | go; rewrite bi.and_elim_l; go].
    - go.
       setoid_rewrite sharePromise.
       go.
       repeat rewrite _at_big_sepL.
       hideLhs.
       erewrite big_sepL_proper .
       2:{
         intros.
         iSplitL.
         go.
         simpl.
         go.
       }
       simpl.
       unhideAllFromWork.
       repeat setoid_rewrite big_sepL_sep.
       go.
       rewrite big_sepL_emp. go.
       setoid_rewrite (@right_id _ _ ((True)%I:mpred)); go. 
  Qed.
Lemma cancelLstar {PROP:bi} {T} l (va vb : T -> PROP):
  (forall id, id ∈ l -> va id |-- vb id) ->
  ([∗ list] id ∈ l, va id) |-- ([∗ list] id ∈ l,vb id).
Proof using.
  intros He.
  apply big_sepL_mono.
  intros.
  apply He.
  eapply elem_of_list_lookup_2; eauto.
Qed.

  Lemma promiseArrDecompose2 (p:ptr) prIds ltr promiseRes:
    p |-> parrayR "boost::fibers::promise<void>"
            (λ (i : nat) (t : Transaction),
               PromiseR (prIds i) (promiseRes i t))
            ltr
   -|- (valid_ptr (p .[ "boost::fibers::promise<void>" ! length ltr ])) **
      [| is_Some (glob_def CU "boost::fibers::promise<void>" ≫= GlobDecl_size_of) |]         **
      (□ ([∗ list] k↦_ ∈ ltr,  (type_ptr "boost::fibers::promise<void>" (p .[ "boost::fibers::promise<void>" ! k ])))) ∗
      ([∗ list] k↦t ∈ ltr, p .[ "boost::fibers::promise<void>" ! k ] |-> PromiseProducerR (prIds k) (promiseRes k t)) ∗
      ([∗ list] k↦t ∈ ltr, p .[ "boost::fibers::promise<void>" ! k ] |-> PromiseConsumerR (prIds k) (promiseRes k t)).
  Proof using.
    rewrite promiseArrDecompose.
    iSplit.
    - go.
      icancel @big_sepL_mono; go.
    -  go.
       hideLhs.
       rewrite big_sepL_proper; try go.
       2:{ intros. iSplit. 2:{go.  evartacs.maximallyInstantiateLhsEvar. }  go. }
       simpl.
       unhideAllFromWork.
       go.
     Qed.
  Opaque parrayR.

cpp.spec (fork_task_nameg "monad::compute_senders(const monad::Block&, monad::fiber::PriorityPool&)::@0") as fork_task with (forkTaskSpec "monad::compute_senders(const monad::Block&, monad::fiber::PriorityPool&)::@0").
  
#[global] Instance learnPpool : LearnEq2 PriorityPoolR := ltac:(solve_learnable).
    Require Import bedrock.auto.invariants.

    (* TODO: move out of section *)
    Ltac aggregateRepPieces base :=
      repeat rewrite <- (_at_offsetR base);
      repeat (IPM.perm_left ltac:(fun L n =>
                            lazymatch L with
                            | base |-> _ => iRevert n
                            end
        ));
      repeat rewrite bi.wand_curry;
      repeat rewrite <- _at_sep;
      match goal with
        [ |-environments.envs_entails _ (base |-> ?R -* _)] =>
          iIntrosDestructs;
          iExists R
      end.


  Definition vector_opg (cppType: type) (this:ptr): WpSpec mpredI val val :=
    \arg{index} "index" (Vn index)
    \prepost{qb base size} this |-> VectorRbase cppType qb base size
    \require (index<size)%Z
    \post [Vref (base ,, .[cppType!index])] emp.


    (* todo: generalize over the template arg *)
cpp.spec 
  "std::vector<monad::Transaction, std::allocator<monad::Transaction>>::operator[](unsigned long) const" as vector_op_monad with (vector_opg "monad::Transaction").

Opaque VectorR.
       #[global] Instance learnVectorRbase: LearnEq4 VectorRbase:= ltac:(solve_learnable).

       (* TODO: generalize over template arg *)
  cpp.spec "std::optional<evmc::address>::operator=(std::optional<evmc::address>&&)" as opt_move_assign with
    (fun (this:ptr) =>
       \arg{other} "other" (Vptr other)
       \pre{q oaddr} other |-> optionAddressR q oaddr
       \pre{prev} this |-> optionAddressR 1 prev
       \post [Vptr this] this |-> optionAddressR 1 oaddr **  other |-> optionAddressR q None
    ).
           
       Set Nested Proofs Allowed.
       cpp.spec (Nscoped "std::optional<evmc::address>" (Nfunction function_qualifiers.N Ndtor [])) as destrop with
           (fun (this:ptr) =>
              \pre{oa} this |-> optionAddressR 1 oa
              \post emp
           ).
       
       #[global] Instance learnTrRbase: LearnEq2 TransactionR:= ltac:(solve_learnable).
       Import Verbose.
       #[global] Instance learnTrRbase2: LearnEq2 optionAddressR:= ltac:(solve_learnable).
       #[global] Instance : LearnEq2 PromiseR := ltac:(solve_learnable).
       #[global] Instance : LearnEq2 PromiseProducerR:= ltac:(solve_learnable).

  Lemma parrayR_sep {V} ty xs  : forall (A B : nat -> V -> Rep),
    parrayR ty (fun i v => A i v ** B i v) xs -|-
    parrayR ty (fun i v => A i v) xs **
    parrayR ty (fun i v=> B i v) xs.
  Proof.
    elim: xs => [|x xs IH] /=; intros.
    Transparent parrayR.
    - unfold parrayR. simpl. iSplit; go.
    - repeat rewrite parrayR_cons.  simpl.
      rewrite {}IH. repeat rewrite _offsetR_sep.
    all: iSplit; work.
  Qed.

  #[global] Instance parrayR_proper X ty:
    Proper ((pointwise_relation nat (pointwise_relation X (≡))) ==> (=) ==> (≡)) (parrayR ty).
  Proof.
    unfold parrayR.
    intros f g Hf xs y ?. subst. f_equiv.
    f_equiv.
    f_equiv.
    hnf.
    intros. hnf. intros.
    hnf in Hf.
    rewrite Hf.
    reflexivity.
  Qed.

  #[global] Instance arrayR_mono X ty:
    Proper (pointwise_relation nat (pointwise_relation X (⊢)) ==> (=) ==> (⊢)) (parrayR ty).
  Proof.
    unfold parrayR.
    intros f g Hf xs y ?. subst. f_equiv.
    f_equiv.
    f_equiv.
    hnf.
    intros. hnf. intros.
    hnf in Hf.
    rewrite Hf.
    reflexivity.
  Qed.

  #[global] Instance arrayR_flip_mono X ty:
    Proper (pointwise_relation nat (pointwise_relation X (flip (⊢))) ==> (=) ==> flip (⊢)) (parrayR ty).
  Proof. solve_proper. Qed.
  Hint Rewrite @skipn_0: syntactic.
  Lemma generalize_arrayR_loopinv (i : nat) (p:ptr) {X : Type} (R : X → Rep) (ty : type) xs (Heq: i=0):
    p |-> arrayR ty R xs
    -|- (p  .[ty ! i]) |-> arrayR ty R (drop i xs).
  Proof using.
    intros.
    apply: (observe_both (is_Some (size_of _ ty))) => Hsz.
    subst.
    autorewrite with syntactic.
    reflexivity.
  Qed.
    
  Lemma generalize_parrayR_loopinv (i : nat) (p:ptr) {X : Type} (R : nat -> X → Rep) (ty : type) xs (Heq: i=0):
    p |-> parrayR ty R xs
    -|- (p  .[ty ! i]) |-> parrayR ty (fun ii => R (i+ii)) (drop i xs).
  Proof using.
    intros.
    apply: (observe_both (is_Some (size_of _ ty))) => Hsz.
    subst.
    autorewrite with syntactic.
    reflexivity.
  Qed.
  
  Lemma vectorbase_loopinv {T} ty base q (l: list T) (i:nat) (Heq: i=0):
    VectorRbase ty q base (lengthN l) -|- (VectorRbase ty (q*Qp.inv (N_to_Qp (1+lengthN l))) base (lengthN l) ** 
    ([∗ list] _ ∈ (drop i l),  VectorRbase ty (q*Qp.inv (N_to_Qp (1+lengthN l))) base (lengthN l))).
  Proof using. Admitted.

      Set Printing Coercions.
    Lemma drop_S2: ∀ {A : Type} (l : list A) (n : nat),
        (Z.of_nat n < lengthZ l)%Z→
          exists x,  l !! n = Some x /\ drop n l = x :: drop (S n) l.
    Proof using.
      intros ? ? ? Hl.
      unfold lengthN in Hl.
      assert (n< length l)%nat as Hln by lia.
      erewrite <- nth_error_Some in Hln.
      pose proof (fun x => drop_S l x n).
      rewrite <- lookup_nth_error in Hln.
      destruct (l !! n); try congruence.
      eexists; split; eauto.
    Qed.

       Ltac iExistsTac  foo:=match goal with
                               |- environments.envs_entails _ (Exists (_:?T), _) => iExists ((ltac:(foo)):T)
                             end.
  Lemma parrayR_nil {T} (R : nat -> T -> Rep) ty: parrayR ty R [] -|- validR ** [| is_Some (size_of _ ty) |].
  Proof using.
    unfold parrayR. simpl.
    apply: (observe_both (is_Some (size_of _ ty))) => Hsz.
    change (Z.of_nat 0) with 0%Z.
    autorewrite with syntactic.
    rewrite _offsetR_sub_0; try assumption.
    iSplit; work.
  Qed.

  Import linearity.

  Lemma arrayR_cell {X} ty (R:X->Rep) xs i x iZ :
    iZ = Z.of_nat i →	(** Ease [eapply] *)
    xs !! i = Some x →	(** We have an [i]th element *)
    arrayR ty R xs -|-
           arrayR ty R (take i xs) **
           _sub ty iZ |-> type_ptrR ty **
           _sub ty iZ |-> R x **
           _sub ty (iZ + 1) |-> arrayR ty R (drop (S i) xs).
  Proof.
    intros Hi Hl.
    rewrite -{1}(take_drop_middle xs i _ Hl) arrayR_app arrayR_cons !_offsetR_sep.
    f_equiv.
    enough (length (take i xs) = i) as ->.
    { subst. by rewrite _offsetR_sub_sub. }
    { apply length_take_le.
      apply lookup_lt_Some in Hl. lia. }
  Qed.

  Lemma parrayR_app {X} ty xs ys : forall (R:nat -> X->Rep),
    parrayR ty R (xs ++ ys) -|- parrayR ty R xs ** .[ ty ! length xs ] |-> parrayR ty (fun ii => R (length xs +ii)) ys.
  Proof.
    induction xs => /=.
    { unfold parrayR. intros.
      apply: (observe_both (is_Some _)) => Hsz.
      simpl.
      change (Z.of_nat 0) with 0%Z.
      repeat rewrite o_sub_0; auto.
      repeat rewrite _offsetR_id.
      iSplit; go. admit.
      (*
  _ : .[ ty ! Z.of_nat (length ys) ] |-> validR
  --------------------------------------□
  validR
*)
    }
    { intros. repeat rewrite parrayR_cons.
      by rewrite IHxs !_offsetR_sep !_offsetR_succ_sub Nat2Z.inj_succ -!assoc.
    }
  Admitted.
  
  Lemma parrayR_cell i {X} ty (R:nat -> X->Rep) xs x iZ :
    iZ = Z.of_nat i →	(** Ease [eapply] *)
    xs !! i = Some x →	(** We have an [i]th element *)
    parrayR ty R xs -|-
           parrayR ty R (take i xs) **
           _sub ty iZ |-> type_ptrR ty **
           _sub ty iZ |-> R i x **
           _sub ty (iZ + 1) |-> parrayR ty (fun ii => R (S i+ii)) (drop (S i) xs).
  Proof.
    intros Hi Hl.
    rewrite -{1}(take_drop_middle xs i _ Hl) parrayR_app parrayR_cons !_offsetR_sep.
    f_equiv.
    enough (length (take i xs) = i) as ->.
    { subst. repeat setoid_rewrite _offsetR_sub_sub.
      replace (i+0) with i by lia.
      replace (Z.of_nat i + 0)%Z with (Z.of_nat i) by lia.
      repeat setoid_rewrite Nat.add_succ_r.
      iSplit; go.
    }
    { apply length_take_le.
      apply lookup_lt_Some in Hl. lia. }
  Qed.

  Lemma parrayR_cell2 i {X} ty (R:nat -> X->Rep) xs:
    (Z.of_nat i < Z.of_nat (length xs))%Z ->
          exists x, 
            xs !! i = Some x /\	(** We have an [i]th element *)
    (parrayR ty R xs -|-
           parrayR ty R (take i xs) **
           _sub ty (Z.of_nat i) |-> type_ptrR ty **
           _sub ty (Z.of_nat i) |-> R i x **
           _sub ty ((Z.of_nat i) + 1) |-> parrayR ty (fun ii => R (S i+ii)) (drop (S i) xs)).
  Proof using.
    intros.
    assert (i<length xs) as Hex by lia.
    applyToSomeHyp @lookup_lt_is_Some_2.
    hnf in autogenhyp.
    forward_reason.
    subst.
    eexists; split; eauto.
    apply parrayR_cell; auto.
  Qed.

  cpp.spec "monad::wait_for_promise(boost::fibers::promise<void>&)" as wait_for_promise with 
          (
            \arg{promise} "promise" (Vref promise)
            \pre{(P:mpred) (g:gname)} promise |-> PromiseConsumerR g P
            \post P ** promise |-> PromiseUnusableR).

  Search arrayR equiv.
  Lemma arrDecompose {T} (p:ptr) ltr (R: T -> Rep) (ty:type):
    p |-> arrayR ty R ltr
   -|- (valid_ptr (p .[ ty ! length ltr ])) ** [| is_Some (size_of CU ty) |] **
     ( □ ([∗ list] k↦_ ∈ ltr, (type_ptr ty (p .[ ty ! k ])))) ∗
      ([∗ list] k↦t ∈ ltr, p .[ ty ! k ] |-> R t).
  Proof using.
    rewrite arrayR_eq.
    unfold arrayR_def.
    rewrite arrR_eq.
    unfold arrR_def.
    repeat rewrite length_fmap.
    repeat rewrite big_opL_fmap.
    iSplit; go.
    {
      setoid_rewrite _offsetR_sep.
      rewrite big_sepL_sep.
      go.
      repeat rewrite _at_big_sepL.
      setoid_rewrite _at_offsetR.
      go.
      iClear "#".
      iStopProof.
      f_equiv.
      go.
    }
    {
      setoid_rewrite _offsetR_sep.
      rewrite big_sepL_sep.
      go.
      repeat rewrite _at_big_sepL.
      setoid_rewrite _at_offsetR.
      go.
       hideLhs.
       rewrite big_sepL_proper; try go.
       2:{ intros. iSplit. 2:{go.  evartacs.maximallyInstantiateLhsEvar. }  go. }
       simpl.
       unhideAllFromWork.
       go.
    }
  Qed.

  Lemma arrLearn (p:ptr) {T} ltr (R: T -> Rep) (ty:type):
    p |-> arrayR ty R ltr
   |-- (valid_ptr (p .[ ty ! length ltr ])) ** [| is_Some (size_of CU ty) |] **
   ( □ ([∗ list] k↦_ ∈ ltr, (type_ptr ty (p .[ ty ! k ])))) **
   p |-> arrayR ty R ltr.
  Proof using.
    iIntrosDestructs.
    rewrite arrDecompose.
    go.
  Qed.

  Lemma arrLearn2 (p:ptr) {T} ltr (R: T -> Rep) (ty:type):
    p |-> arrayR ty R ltr
   |-- valid_ptr p ** (valid_ptr (p .[ ty ! length ltr ])) ** [| is_Some (size_of CU ty) |] **
   ( □ ([∗ list] k↦_ ∈ ltr, (type_ptr ty (p .[ ty ! k ])))) **
   p |-> arrayR ty R ltr.
  Proof using.
    iIntrosDestructs.
    rewrite arrDecompose.
    go.
    destruct ltr.
    - go. autorewrite with syntactic. go.
    -  simpl. autorewrite with syntactic. go.
  Qed.

  Lemma parrDecompose {T} (p:ptr) ltr (R: nat -> T -> Rep) (ty:type):
    p |-> parrayR ty R ltr
   -|- (valid_ptr (p .[ ty ! length ltr ])) ** [| is_Some (size_of CU ty) |] **
     ( □ ([∗ list] k↦_ ∈ ltr, (type_ptr ty (p .[ ty ! k ])))) ∗
      ([∗ list] k↦t ∈ ltr, p .[ ty ! k ] |-> R k t).
  Proof using.
    unfold parrayR.
    repeat rewrite length_fmap.
    repeat rewrite big_opL_fmap.
    iSplit; go.
    {
      setoid_rewrite _offsetR_sep.
      rewrite big_sepL_sep.
      go.
      repeat rewrite _at_big_sepL.
      setoid_rewrite _at_offsetR.
      go.
      iClear "#".
      iStopProof.
      f_equiv.
      go.
    }
    {
      setoid_rewrite _offsetR_sep.
      rewrite big_sepL_sep.
      go.
      repeat rewrite _at_big_sepL.
      setoid_rewrite _at_offsetR.
      go.
       hideLhs.
       rewrite big_sepL_proper; try go.
       2:{ intros. iSplit. 2:{go.  evartacs.maximallyInstantiateLhsEvar. }  go. }
       simpl.
       unhideAllFromWork.
       go.
    }
  Qed.

  Lemma parrLearn (p:ptr) {T} ltr (R: nat -> T -> Rep) (ty:type):
    p |-> parrayR ty R ltr
   |-- (valid_ptr (p .[ ty ! length ltr ])) ** [| is_Some (size_of CU ty) |] **
   ( □ ([∗ list] k↦_ ∈ ltr, (type_ptr ty (p .[ ty ! k ])))) **
   p |-> parrayR ty R ltr.
  Proof using.
    iIntrosDestructs.
    rewrite parrDecompose.
    go.
  Qed.

  Lemma parrLearn2 (p:ptr) {T} ltr (R: nat -> T -> Rep) (ty:type):
    p |-> parrayR ty R ltr
   |-- valid_ptr p ** (valid_ptr (p .[ ty ! length ltr ])) ** [| is_Some (size_of CU ty) |] **
   ( □ ([∗ list] k↦_ ∈ ltr, (type_ptr ty (p .[ ty ! k ])))) **
   p |-> parrayR ty R ltr.
  Proof using.
    iIntrosDestructs.
    rewrite parrDecompose.
    go.
    destruct ltr.
    - go. autorewrite with syntactic. go.
    -  simpl. autorewrite with syntactic. go.
  Qed.
  

  Ltac hideP fullyHiddenPostcond :=
      IPM.perm_left ltac:(fun L n =>
                        match L with
                        | HiddenPostCondition => hideFromWorkAs L fullyHiddenPostcond
                        end
                         ).

  cpp.spec (Nscoped 
"monad::compute_senders(const monad::Block&, monad::fiber::PriorityPool&)::@0" (Nfunction function_qualifiers.N Ndtor []))  as cslamdestr inline.  
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
             |-- compute_senders.
Proof using MODd.
  verify_spec'.
  name_locals.
  hideRhs.
  hideP ff.
  
  Transparent VectorR.
  unfold BlockR, VectorR.
  work.
  rename v into vectorbase. (* Fix *)
  rewrite (arrLearn2 vectorbase).
  rewrite (arrLearn2 (_global "monad::senders")).
  rewrite parrLearn2.
  unhideAllFromWork.
  slauto.
    iExists  (fun i t => (_global "monad::senders"  .[ "std::optional<evmc::address>" ! i ] |-> optionAddressR 1 (Some (sender t)))
  ** (vectorbase .[ "monad::Transaction" ! i ] |-> TransactionR qb t)
  ** (blockp ,, o_field CU "monad::Block::transactions"
        |-> VectorRbase "monad::Transaction" (qb * / N_to_Qp (1 + lengthN (transactions block))) vectorbase (lengthN (transactions block)))
             ).
    go.
  name_locals.
  unfold VectorR.
  go.
  setoid_rewrite sharePromise.
  rewrite parrayR_sep.
  go.
  assert (exists ival:nat, ival=0) as Hex by (eexists; reflexivity).
  destruct Hex as [ival Hex].
  hideRhs.
  IPM.perm_left ltac:(fun L n =>
                        match L with
                        | HiddenPostCondition => hideFromWorkAs L fullyHiddenPostcond
                        end
                     ).
  rewrite (generalize_arrayR_loopinv ival (_global "monad::senders")); [| assumption].
  rewrite (generalize_arrayR_loopinv ival vectorbase); [| assumption].
  rewrite (@vectorbase_loopinv _ _ _ _ _ ival); auto.
  IPM.perm_left ltac:(fun L n =>
                        match L with
                        | context[PromiseConsumerR] => hideFromWorkAs L pc
                        end
                      ).
  rewrite (generalize_parrayR_loopinv ival (_global "monad::promises")); [| assumption].
  assert (Vint 0 = Vnat ival) as Hexx by (subst; auto).
  rewrite Hexx. (* TODO: use a more precise pattern *)
  clear Hexx.
  assert (ival <= length (transactions block)) as Hle by (subst; lia).
  clear Hex.
  unhideAllFromWork.
  iStopProof.
  evartacs.revertSPDeps ival.
  apply wp_for; slauto.
  wp_if.
  { (* loop condition is true and thus the body runs. so we need to reistablish the loopinv *)
    slauto.
    ren_hyp ival nat.
    applyToSomeHyp @drop_S2.
    match goal with
      [H:_ |- _] => destruct H as [tri Htt]; destruct Htt as [Httl Httr]
    end.
    rewrite Httr.
    repeat rewrite -> arrayR_cons0.
    repeat rewrite -> parrayR_cons.
    go.
    autorewrite with syntactic.
    repeat rewrite o_sub_sub.
    simpl.
    progress go.
    aggregateRepPieces a.
    go.
    IPM.perm_left ltac:(fun L n =>
      match L with
      |   _ |-> VectorRbase _ _ _ _ => iRevert n
      end
      ).
    repeat IPM.perm_left ltac:(fun L n =>
      match L with
      | _ .[_ ! Z.of_nat ival] |-> _ => iRevert n
      end).
    repeat rewrite bi.wand_curry.
    match goal with
        [ |-environments.envs_entails _ (?R -* _)] => iIntrosDestructs; iExists R
    end.
    slauto.
    iSplitL "".
    {
      unfold taskOpSpec.
      verify_spec'.
      slauto.
      iExists (N.of_nat ival). (* automate this using some Refine1 hint *)
      go.
      Hint Rewrite nat_N_Z: syntactic.
      autorewrite with syntactic.
      slauto.
      replace (ival + 0) with ival;[| lia].
      go.
    }
    {
      slauto.
      go.
       iExists (1+ival).
       unfold lengthN in *.
       iExistsTac lia.
       go.
       replace (Z.of_nat ival + 1)%Z with (Z.of_nat (S ival)); try lia.
       go.
       setoid_rewrite Nat.add_succ_r.
       go.
    }
  }
  { (* loop condition is false *)
    go.
    unfold lengthN in *.
    ren_hyp ival nat.
    assert (ival=length(transactions block))  by lia.
    subst.
    go.
    Hint Rewrite @drop_all: syntactic.
    autorewrite with syntactic.
    repeat rewrite arrayR_nil.
    repeat rewrite parrayR_nil.
    go.
    rename i_addr into i1_addr.
    name_locals.
    IPM.perm_left ltac:(fun L n =>
       match L with
       | ?p |-> parrayR ?ty (fun i v => PromiseConsumerR (@?P i) (@?R i v) ) ?l =>
           wp_for (fun _ =>
          Exists (ival:nat), i_addr |-> ulongR (cQp.mut 1) ival **
          (p .[ty ! ival] |-> parrayR ty (fun i v => PromiseConsumerR (P (ival+i)) (R (ival+i) v) ) (drop ival (transactions block))) **
          (p |-> parrayR ty (fun i v => PromiseUnusableR) (take ival (transactions block))) **
          [| ival <= length (transactions block) |] **
           [∗list] j↦v ∈ (take ival (transactions block)),
               R j v)%I
       end).
    work.
    rewrite <- (bi.exist_intro 0%nat).
    slauto.
    rewrite parrayR_nil. go.
    autorewrite with syntactic.
    slauto.
    ren_hyp ival nat. 
    wp_if.
    { (* loop continues *)
      slauto.
      autorewrite with syntactic in *.
      pose proof @drop_S2 as Hd.
      unfold lengthN in Hd.
      autorewrite with syntactic in *.
      Search Z.of_N Z.of_nat.
      setoid_rewrite nat_N_Z in Hd.
      applyToSomeHyp Hd.
      match goal with
        [H:_ |- _] => destruct H as [tri Htt]; destruct Htt as [Httl Httr]
      end.
      rewrite Httr.
      rewrite -> parrayR_cons.
      slauto.
      #[global] Instance : LearnEq2 PromiseConsumerR:= ltac:(solve_learnable).
      go.
      Hint Rewrite Nat.add_0_r Z.add_0_r :syntactic.
      repeat rewrite o_sub_sub.
      autorewrite with syntactic.
      Set Printing Coercions.
      slauto.
      iExists (1+ival).
      slauto.
      replace (Z.of_nat ival + 1)%Z with (Z.of_nat (S ival)); try lia.
      setoid_rewrite Nat.add_succ_r.
      slauto.
      erewrite take_S_r; eauto.
      rewrite parrayR_app. (* todo: rewrite with a snoc lemma  to cut down the script below *)
      go.
      autorewrite with syntactic.
      rewrite -> length_take_le by lia.
      go.
      rewrite parrayR_cons.
      go.
      autorewrite with syntactic.
      go.
      rewrite parrayR_nil.
      go.
      Search big_opL app.
      rewrite big_opL_snoc.
      rewrite -> length_take_le by lia.
      go.
    }
    { (* loop condition is false *)
      go.
      assert (ival=length(transactions block))  by lia.
      subst.
    Hint Rewrite @firstn_all: syntactic.
      autorewrite with syntactic.
      go.
      repeat rewrite parrayR_nil. go.
      repeat rewrite big_sepL_sep.
      go.
      hideLhs.
      setoid_rewrite -> vectorbase_loopinv with (i:=0); try reflexivity.
      unhideAllFromWork.
      go.
      rewrite _at_big_sepL.
      go.
      repeat rewrite arrDecompose.
      go.
    }
  }
Qed.
(*       
(*
  erewrite sizeof.size_of_compat;[| eauto; fail| vm_compute; reflexivity].
*)

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

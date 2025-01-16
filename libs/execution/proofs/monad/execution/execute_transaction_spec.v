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

Require Import bedrock_auto.tests.data_class.exb.
Require Import bedrock_auto.tests.data_class.exb_names.
Require Import bedrock_auto.tests.data_class.lam.
Require Import bedrock_auto.tests.data_class.lam_names.

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


Section lam.
Context  {MOD : lam.module ⊧ CU}.


(*


#include<functional>

int sum(std::function<int(int)> f)
{
  return f(0) + f(1);
}

int callsum()
{
    int x = 42; // Captured variable
    auto lambda = [x](int y) { return x + y; };
    return sum(lambda);
}


int main() {
    int x = 42; // Captured variable
    auto lambda = [x](int y) { return x + y; };
    //return callsum();
    return lambda(10);

template version:


~/work/coq/monad$cat ../lam.cpp
template<typename Func>
int sum(const Func& f)
{
  return f(0) + f(1);
}

int callsum()
{
    int x = 42; // Captured variable
    auto lambda = [x](int y) { return x + y; };
    return sum(lambda);
}


int main() {
    int x = 42; // Captured variable
    auto lambda = [x](int y) { return x + y; };
    //return callsum();// returned 85
    return lambda(10);
}
}
 *)
  cpp.spec "main()::@0::operator()(int) const" as mainlam_spec inline.
(*   cpp.spec (lam.n5) as destructor_spec2 inline. *)
  cpp.spec "main()" as main_spec with (\pre emp \post [Vint 52] emp).
  cpp.spec "callsum()" as csum_spec with (\pre emp \post [Vint 52] emp).

  cpp.spec (Nscoped "main()::@0" (Nfunction function_qualifiers.N Ndtor [])) as lam_destructor_spec  with
      (fun this:ptr => \pre this |-> structR "main()::@0" (cQp.mut 1)
                       \pre this ,, o_field CU "main()::@0::x" |-> intR (cQp.mut 1) 42
                         \post emp).

  Lemma main_proof: denoteModule module |-- csum_spec.
  Proof using.
    verify_spec'.
    go.
    rewrite <- wp_init_lambda.
    slauto.
    (*
  _ : denoteModule module
  _ : type_ptr "int" x_addr
  _ : type_ptr "callsum()::@0" lambda_addr
  --------------------------------------□
  _ : HiddenPostCondition
  _ : x_addr |-> intR (cQp.mut 1) 42
  _ : lambda_addr ,, o_field CU "callsum()::@0::x" |-> intR (cQp.mut 1) 42
  _ : lambda_addr |-> structR "callsum()::@0" (cQp.mut 1)
  --------------------------------------∗
  ::wpPRᵢ
    [region: "lambda" @ lambda_addr; "x" @ x_addr; return {?: "int"%cpp_type}]
    (Pointer ↦ p) 
    (Econstructor "std::function<int()(int)>::function<callsum()::@0&, void>(callsum()::@0&)"
       [Evar "lambda" "callsum()::@0"] "std::function<int()(int)>")
     *)
  Abort.


  Definition pName (n:name): bs :=
    match n with
    | Nglobal  (Nfunction _ (Nf i) _) => i
    | _ => ""
    end.

  Definition isFunctionNamed (n:name) (fname: ident): bool :=
    match n with
    | Nglobal  (Nfunction _ (Nf i) _) => bool_decide (i=fname)
    | Ninst (Nglobal  (Nfunction _ (Nf i) _)) _ => bool_decide (i=fname)
    | _ => false
    end.

  Definition fnArgTypes (n:name) : list type :=
    match n with
    | Nglobal  (Nfunction _ (Nf i) argTypes) => argTypes
    | _ => []
    end.

  Definition findBodyOfFnNamed module (fname:ident) :=
    List.filter (fun p => let '(nm, body):=p in isFunctionNamed nm fname) (NM.elements (symbols module)).

  Definition sumEntry : list (name * ObjValue) := (findBodyOfFnNamed module "sum").


  Definition firstEntryName (l :list (name * ObjValue)) :=
    (List.nth 0 (map fst l) (Nunsupported "impossible")).
      
  Definition sumStructuredName :name := Eval vm_compute in (firstEntryName sumEntry).
  cpp.spec "sum<callsum()::@0>(const callsum()::@0&)" as sum_spec with
      (\pre emp
         \arg{task} "task" (Vref task)
         \post [Vint 52] emp).
  Definition sc :name := "sum<callsum()::@0>(const callsum()::@0&)".

  Definition instee (n:name) : name :=
    match n with
    | Ninst base i => base
    | _ => Nunsupported "not a Ninst"
    end.
  Definition basee (n:name) :=
    match n with
    | Ninst (Nglobal  (Nfunction q (Nf base) l)) targs => (base,l,q, targs)
    | _ => (BS.EmptyString,[],function_qualifiers.N, [])
    end.

  Compute (basee sc).

  Definition sumname (lamTy: core.name) : name :=
    Ninst (Nglobal  (Nfunction function_qualifiers.N (Nf "sum") [Tref (Tqualified QC (Tnamed lamTy))])) [Atype (Tnamed lamTy)].
    
  
  Definition lamOperator (fullopName: name) :=
    match fullopName with
    | Nscoped _ op => op
    | _ => Nunsupported_atomic ""
    end.

  Definition lamStructName :name :="callsum()::@0".
  Definition opName :name := "callsum()::@0::operator()(int) const".
  Definition lamOpInt := Eval vm_compute in (lamOperator opName).
  Definition operatorSpec (lamStructName: core.name) (R: Rep) (f: Z->Z):=
    specify {| info_name :=  (Nscoped lamStructName lamOpInt) ;
              info_type := tMethod lamStructName QC "int" ["int"%cpp_type] |}
      (fun (this:ptr) =>
           \prepost this |-> R
           \arg{y} "y" (Vint y)
           \require (y<100)%Z (* to avoid overflow *)
           \post[Vint (f y)] emp).
  
  Definition sumSpec (lamStructName: core.name) : WpSpec mpredI val val :=
    \arg{func:ptr} "func" (Vref func)
    \pre{R f} operatorSpec lamStructName R f
    \prepost func |-> R
    \post [Vint (f 0 + f 1)] emp.

  cpp.spec (sumname "callsum()::@0") as sum_spec2 with (sumSpec "callsum()::@0").
  
  cpp.spec "callsum()" as callsum_spec2 with (\post [Vint 85] emp).

  Lemma destr (lambda_addr:ptr) P :
    (lambda_addr |-> structR "callsum()::@0" (cQp.mut 1))
      **
  (lambda_addr ,, o_field CU "callsum()::@0::x" |-> intR (cQp.mut 1) 42)
  **
    P |--    wp_destroy_named module "callsum()::@0" lambda_addr P.
  Proof. go. Admitted.

  Import linearity.
  Lemma callsum_proof: denoteModule module ** sum_spec2 |-- callsum_spec2.
  Proof using MOD.
    verify_spec'.
    name_locals.
    slauto.
    rewrite <- wp_init_lambda.
    slauto.
    iExists (structR "callsum()::@0" 1 ** o_field CU "callsum()::@0::x" |-> intR (cQp.mut 1) 42).
    iExists (fun x=> x+42)%Z.
    go.
    unfold operatorSpec.
    iSplitL "".
    - go.
      verify_spec'.
      slauto.
    - go.
      rewrite <- destr.
      go.
   Qed.
      
End lam.  

Require Import bedrock_auto.tests.data_class.exb.
Require Import bedrock_auto.tests.data_class.exb_names.

Context  {MODd : exb.module ⊧ CU}.
(* Node::Node(Node*,int) *)
Check exb.module.

  cpp.spec (Ninst
   "monad::execute_block(const monad::Chain&, monad::Block&, monad::BlockState&, const monad::BlockHashBuffer&, monad::fiber::PriorityPool&)"
   [Avalue (Eint 11 "enum evmc_revision")]) as exbb_spec with (execute_block_simpler).

  cpp.spec
    "std::vector<monad::Transaction, std::allocator<monad::Transaction>>::size() const"
    as tvector_spec with
      (fun (this:ptr) =>
         \prepost{q ts} this |-> VectorR (Tnamed ``::monad::Transaction``) (fun t => TransactionR q (* can be a different q *) t)  q (ts)
         \post[Vn (lengthN ts)] (emp:mpred)
      ).
  Print lt.


  Definition optionAddressR (q:Qp) (oaddr: option evm.address): Rep. Proof. Admitted.

Definition parrayR  {T:Type} ty (Rs : nat -> T -> Rep) (l: list T) : Rep :=
  .[ ty ! length l ] |-> validR ** [| is_Some (size_of _ ty) |] **
  (* ^ both of these are only relevant for empty arrays, otherwise, they are implied by the
     following conjunct *)
  [∗ list] i ↦ li ∈ l, .[ ty ! Z.of_nat i ] |-> (type_ptrR ty ** Rs i li).

  Opaque parrayR.
  Hypothesis sender: Transaction -> evm.address.
cpp.spec 
  "monad::reset_promises(unsigned long)" as reset_promises
      with
      (\arg{transactions: list Transaction} "n" (Vn (lengthN transactions))
       \pre{prIds oldPromisedResource newPromisedResource}
           _global "promises" |-> parrayR (Tnamed "boost::fiber::promise") (fun i t => PromiseR 1 (prIds i) (oldPromisedResource i t)) transactions
       \post _global "promises" |-> parrayR (Tnamed "boost::fiber::promise") (fun i t => PromiseR 1 (prIds i) (newPromisedResource i t)) transactions).
  
cpp.spec
  "monad::compute_senders(const monad::Block&, monad::fiber::PriorityPool&)"
  as compute_senders
  with (
    \arg{blockp: ptr} "block" (Vref blockp)
    \prepost{qb (block: Block)} blockp |-> BlockR qb block
    \arg{priority_poolp: ptr} "priority_pool" (Vref priority_poolp)
    \prepost{priority_pool: PriorityPool} priority_poolp |-> PriorityPoolR 1 priority_pool
    \prepost{prIds} Exists garbage,
        _global "promises" |->
          parrayR
            (Tnamed "boost::fiber::promise")
            (fun i t => PromiseR 1 (prIds i) (garbage i t))
            (transactions block)
    \pre Exists garbage,
        _global "senders" |->
          arrayR
            (Tnamed "std::optional<evmc::address>")
            (fun t=> optionAddressR 1 garbage)
            (transactions block)
    \post _global "senders" |->
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
    Eval vm_compute in (findBodyOfFnNamed exb.module "monad::fork_task").

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

  Definition fork_task_namei:= Eval vm_compute in (firstEntryName (findBodyOfFnNamed2 exb.module (isFunctionNamed2 "fork_task"))).

  Definition basee3 (n:name) :=
    match n with
    | Ninst (Nscoped (Nglobal (Nid scopename)) _) targs => scopename
    | _ => BS.EmptyString
    end.

  Definition all_but_last {T:Type} (l: list T):= take (length l -1)%nat l. 
  Definition fork_task_nameg (taskLamStructTy: core.name) :=
    match fork_task_namei with
    | Ninst (Nscoped (Nglobal (Nid scopename)) (Nfunction q (Nf base) argTypes)) templateArgs =>
        let argTypes' := all_but_last argTypes ++  [Tref (Tqualified QC (Tnamed taskLamStructTy))] in
        Ninst (Nscoped (Nglobal (Nid scopename)) (Nfunction q (Nf base) argTypes')) templateArgs
    | _ => fork_task_namei
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
Lemma prf: denoteModule module ** tvector_spec ** reset_promises |-- compute_senders.
Proof using.
  verify_spec'.
  name_locals.
  unfold BlockR.
  slauto.
  iExists prIds. (* why does the array learning hint not work? *)
  go.
  iExists _.
  iExists  (fun i t => _global "senders"  |-> .[ "std::optional<evmc::address>" ! i ] |-> optionAddressR 1 (Some (sender t)) ).
  eagerUnifyU. go.
  rewrite arrayR_eq. unfold arrayR_def. rewrite arrR_eq. unfold arrR_def. go.
  Transparent parrayR.
  unfold parrayR. go.
  Search big_opL _at.
  repeat rewrite _at_big_sepL.
  slauto.
  rewrite
  Search arrayR.
  wp_for (fun _ => ).
  iExists (transactions block).
  go.
  go using learnArrUnsafe.
  iExists _.
  iExists _.
  iExists _.
  eagerUnifyU.
  go.
  slauto.
  Search Learnable arrayR.

@globa  
  iExists _.
  iExists _.
  go.
  slauto.
  
  Definition lamName :name :=
                                      (Nscoped
                                     (Ninst
                                        "monad::compute_senders(std::optional<evmc::address>*, const monad::Block&, monad::fiber::PriorityPool&)"
                                        [Avalue (Eint 0 "enum evmc_revision")])
                                     (Nanon 0)).

  Search NM.t.

  Compute lamBody.
Lemma prf: denoteModule module ** tvector_spec |-- exb_spec.
Proof using.
  verify_spec'.
  name_locals.
  unfold BlockR.
  slauto.
  iExists _.
  iExists _.
  go.
  erewrite sizeof.size_of_compat;[| eauto; fail| vm_compute; reflexivity].
  assert ((lengthN (transactions block)< 10000000)%N) as Hl by admit.
  slauto.
  {
    (* out of memory error, maybe the code should return an error result here instead of throwing which the logic doesnt support yet *)
    admit.
  }
  {
    go.
    go.
    go.
  
    
  
  provePure.
  work.
  go.
  provePure.
  hnf.
  2:{ go.
  2:{
  Search glob_def  GlobDecl_size_of .
  ego.
  Search Enew.
  
  slauto.
  ego.
  provePure.
  Print pointer_size.
 
  Show Proof.
  hnf.

  invoke.wp_minvoke_O.body module Direct
    "const std::vector<monad::Transaction, std::allocator<monad::Transaction>>" "unsigned long"%cpp_type
    "unsigned long()()" "std::vector<monad::Transaction, std::allocator<monad::Transaction>>::size() const"
    (blockp ,, o_field CU "monad::Block::transactions") [] None
    (λ x : val,
        ∃ array_sizeN : N, [| x = Vn array


        Sdecl
          [Dvar "senders" "std::optional<evmc::address>* const"
             (Some
                (Enew
                   ("operator new[](unsigned long, const std::nothrow_t&)"%cpp_name,
                    "void*()(unsigned long, const std::nothrow_t&)"%cpp_type)
                   [Eglobal "std::nothrow" "const std::nothrow_t"] (new_form.Allocating false)
                   "std::optional<evmc::address>"
                   (Some
                      (Emember_call false
                         (inl
                            ("std::vector<monad::Transaction, std::allocator<monad::Transaction>>::size() const"%cpp_name,
                             Direct, "unsigned long()()"%cpp_type))
                         (Ecast
                            (Cnoop "const std::vector<monad::Transaction, std::allocator<monad::Transaction>>&")
                            (Emember false (Evar "block" "monad::Block&") (Nid "transactions") false
                               "std::vector<monad::Transaction, std::allocator<monad::Transaction>>"))
                         []))
                   (Some
                      (Econstructor "std::optional<evmc::address>::optional()" [] "std::optional<evmc::address>[]")                                     
                                     
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

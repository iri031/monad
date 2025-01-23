Require Import bedrock.auto.cpp.proof.

Require Import monad.asts.exb.
Require Import bedrock.auto.invariants.
Require Import monad.proofs.evmopsem.
Require Import monad.proofs.misc.

Definition PriorityPool: Type. Proof using. Admitted.

Section cp.
  Import own.
  Import frac.

Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI algebra.frac.fracR}. (* some standard assumptions about the c++ logic *)



  (* defines how [c] is represented in memory as an object of class Chain *)
  Definition PriorityPoolR (q: Qp) (c: PriorityPool): Rep. Proof using. Admitted.

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

    (* set_value() passes the resource/assertion P to the one calling get_future->wait()*)
  Definition PromiseR (g: gname) (P: mpred) : Rep. Proof using. Admitted.
  Definition PromiseProducerR (g: gname) (P: mpred) : Rep. Proof using. Admitted.
  Definition PromiseConsumerR (g: gname) (P: mpred) : Rep. Proof using. Admitted.
  Definition PromiseUnusableR: Rep. Proof using. Admitted.

  Lemma sharePromise g P:  PromiseR g P -|- PromiseProducerR g P **  PromiseConsumerR g P.
  Proof using. Admitted.

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

  cpp.spec
    "std::vector<monad::Transaction, std::allocator<monad::Transaction>>::size() const"
    as tvector_spec with
      (fun (this:ptr) =>
         \prepost{q base size} this |-> VectorRbase (Tnamed "::monad::Transaction")  q base size
         \post[Vn size] (emp:mpred)
      ).

  Definition optionR {B} (baseRep: B-> Rep) (q:Qp) (oaddr: option B): Rep. Proof. Admitted.
  Definition addressR (a: evm.address) (q: Qp): Rep. Proof. Admitted.
  Definition optionAddressR (q:Qp) (oaddr: option evm.address): Rep := optionR (fun a => addressR a q) q oaddr.

  cpp.spec "monad::wait_for_promise(boost::fibers::promise<void>&)" as wait_for_promise with 
          (
            \arg{promise} "promise" (Vref promise)
            \pre{(P:mpred) (g:gname)} promise |-> PromiseConsumerR g P
            \post P ** promise |-> PromiseUnusableR).

  Lemma vectorbase_loopinv {T} ty base q (l: list T) (i:nat) (Heq: i=0):
    VectorRbase ty q base (lengthN l) -|- (VectorRbase ty (q*Qp.inv (N_to_Qp (1+lengthN l))) base (lengthN l) ** 
    ([∗ list] _ ∈ (drop i l),  VectorRbase ty (q*Qp.inv (N_to_Qp (1+lengthN l))) base (lengthN l))).
  Proof using. Admitted.
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
  Lemma learnpArrUnsafe e t: LearnEq2 (@parrayR _ _ _ _ e t).
  Proof. solve_learnable. Qed.
  
  #[global] Instance learnVectorRbase: LearnEq4 VectorRbase:= ltac:(solve_learnable).
  #[global] Instance learnPpool : LearnEq2 PriorityPoolR := ltac:(solve_learnable).


  Definition vector_opg (cppType: type) (this:ptr): WpSpec mpredI val val :=
    \arg{index} "index" (Vn index)
    \prepost{qb base size} this |-> VectorRbase cppType qb base size
    \require (index<size)%Z
    \post [Vref (base ,, .[cppType!index])] emp.

Opaque VectorR.

       (* TODO: generalize over template arg *)
  cpp.spec "std::optional<evmc::address>::operator=(std::optional<evmc::address>&&)" as opt_move_assign with
    (fun (this:ptr) =>
       \arg{other} "other" (Vptr other)
       \pre{q oaddr} other |-> optionAddressR q oaddr
       \pre{prev} this |-> optionAddressR 1 prev
       \post [Vptr this] this |-> optionAddressR 1 oaddr **  other |-> optionAddressR q None
    ).
           
  cpp.spec (Nscoped "std::optional<evmc::address>" (Nfunction function_qualifiers.N Ndtor [])) as destrop with
      (fun (this:ptr) =>
         \pre{oa} this |-> optionAddressR 1 oa
           \post emp
      ).
  
  #[global] Instance learnTrRbase2: LearnEq2 optionAddressR:= ltac:(solve_learnable).
  #[global] Instance learnOpt b: LearnEq3 (@optionR b):= ltac:(solve_learnable).
  #[global] Instance : LearnEq2 PromiseR := ltac:(solve_learnable).
  #[global] Instance : LearnEq2 PromiseProducerR:= ltac:(solve_learnable).
  
End cp.



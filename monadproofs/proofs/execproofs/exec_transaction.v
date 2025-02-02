Require Import monad.proofs.misc.
Require Import monad.proofs.libspecs.
Require Import monad.proofs.evmopsem.
Import linearity.
Require Import bedrock.auto.invariants.
Require Import bedrock.auto.cpp.proof.

Require Import bedrock.auto.cpp.tactics4.
Require Import monad.asts.ext.
Require Import monad.proofs.exec_specs.

Opaque libspecs.optionR.

Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
           (*   hh = @has_own_monpred thread_info _Σ fracR (@cinv_inG _Σ (@cpp_has_cinv thread_info _Σ Sigma)) *)
  Context  {MODd : ext.module ⊧ CU}.

  Set Nested Proofs Allowed.
  Set Printing Coercions.
  #[global] Instance learnOpt a b c d e a1 b1 c1 d1 e1: Learnable (@libspecs.optionR _ _ _ _ a b c d e) (@libspecs.optionR _ _ _ _ a1 b1 c1 d1 e1) [a=a1] := ltac:(solve_learnable).

  cpp.spec (
          (Ninst
             (Nscoped (Nglobal (Nid "monad"))
                (Nfunction function_qualifiers.N (Nf "execute_impl")
                   [Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Chain")))); "unsigned long"%cpp_type;
                    Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Transaction"))));
                    Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "address"))));
                    Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockHeader"))));
                    Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockHashBuffer"))));
                    Tref (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockState")));
                    Tref
                      (Tnamed
                         (Ninst (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "fibers")) (Nid "promise"))
                            [Atype "void"]))]))
             [Avalue (Eint 11 (Tenum (Nglobal (Nid "evmc_revision"))))])) as fff inline.

  cpp.spec  (Ninst
             (Nscoped (Nglobal (Nid "monad"))
                (Nfunction function_qualifiers.N (Nf "static_validate_transaction")
                   [Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Transaction"))));
                    Tref
                      (Tconst
                         (Tnamed
                            (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "optional"))
                               [Atype (Tnamed (Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")]))])));
                    Tref (Tconst (Tnamed (Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")])))]))
             [Avalue (Eint 11 (Tenum (Nglobal (Nid "evmc_revision"))))]) as validate_spec with
      (
        \arg{txp} "tx" (Vref txp)
        \prepost{qtx t} txp |-> TransactionR qtx t
        \arg{basefeep} "base" (Vref basefeep)
        \arg{chainidp} "base" (Vref chainidp)
       \post{retp} [Vptr retp] (reference_to
    (Tnamed
       (Ninst (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "basic_result"))
          [Atype "void";
           Atype
             (Tnamed
                (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                   [Atype (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
           Atype
             (Tnamed
                (Ninst
                   (Nscoped (Nscoped (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "experimental")) (Nid "policy"))
                      (Nid "status_code_throw"))
                   [Atype "void";
                    Atype
                      (Tnamed
                         (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                            [Atype
                               (Tnamed
                                  (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                    Atype "void"]))]))
    retp ∗
 retp |-> emp)
    ).
Definition destr_u256 :=
λ {thread_info : biIndex} {_Σ : gFunctors} {Sigma : cpp_logic thread_info _Σ} {CU : genv},
  specify
    {|
      info_name :=
        Nscoped
          (Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")])
          (Nfunction function_qualifiers.N Ndtor []);
      info_type :=
        tDtor
          (Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")])
    |} (λ this : ptr, \pre{w} this |-> u256R 1 w
                        \post    emp).
  #[global] Instance : LearnEq2 u256R := ltac:(solve_learnable).

  cpp.spec 
          (Ninst
             (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2"))
                (Nfunction function_qualifiers.N (Nf "try_operation_has_value")
                   [Tref
                      (Tnamed
                         (Ninst (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "basic_result"))
                            [Atype "void";
                             Atype
                               (Tnamed
                                  (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                                     [Atype (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                             Atype
                               (Tnamed
                                  (Ninst (Nscoped (Nscoped (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "experimental")) (Nid "policy")) (Nid "status_code_throw"))
                                     [Atype "void";
                                      Atype
                                        (Tnamed
                                           (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                                              [Atype (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                                      Atype "void"]))]));
                    Tnamed (Nscoped (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "detail")) (Nid "has_value_overload"))]))
             [Atype
                (Tref
                   (Tnamed
                      (Ninst (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "basic_result"))
                         [Atype "void";
                          Atype
                            (Tnamed
                               (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                                  [Atype (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                          Atype
                            (Tnamed
                               (Ninst (Nscoped (Nscoped (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "experimental")) (Nid "policy")) (Nid "status_code_throw"))
                                  [Atype "void";
                                   Atype
                                     (Tnamed
                                        (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                                           [Atype (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                                   Atype "void"]))])));
              Atype "bool"]) as try_op_has_val with
      (
        \arg{basefeep} "base" (Vref basefeep)
        \arg{chainidp} "base" (Vref chainidp)        
        \post [Vbool true] emp).

Definition destr_outcome_overload :=
λ {thread_info : biIndex} {_Σ : gFunctors} {Sigma : cpp_logic thread_info _Σ} {CU : genv},
  specify
    {|
      info_name :=
        Nscoped
          (Nscoped (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "detail")) (Nid "has_value_overload"))
          (Nfunction function_qualifiers.N Ndtor []);
      info_type :=
        tDtor
          (Nscoped (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "detail")) (Nid "has_value_overload"))
    |} (λ this : ptr, \pre this |->  structR (Nscoped (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "detail")) (Nid "has_value_overload")) (cQp.mut 1)
                        \post    emp).

(* use a const instance instead *)
  Lemma wp_const_const_delete tu ty from to p Q :
    Q |-- wp_const tu from to p ty Q.
  Proof using. Admitted.

  cpp.spec (Nscoped (Nscoped (Nglobal (Nid "monad")) (Nid "Incarnation"))
             (Nfunction function_qualifiers.N Nctor ["unsigned long"%cpp_type; "unsigned long"%cpp_type]))
         as incarnation_constr with
  (fun this:ptr =>
     \arg{bn} "" (Vn bn)
     \arg{txn} "" (Vn txn)
     \post this |-> IncarnationR 1 (Build_Incarnation bn txn)  
  ).

Definition destr_incarnation :=
  specify
    {|
      info_name :=
        Nscoped
          (Nscoped (Nglobal (Nid "monad")) (Nid "Incarnation"))
          (Nfunction function_qualifiers.N Ndtor []);
      info_type :=
        tDtor
          (Nscoped (Nglobal (Nid "monad")) (Nid "Incarnation"))
    |} (λ this : ptr, \pre{w} this |-> IncarnationR 1 w
                        \post    emp).
Require Import bedrock.prelude.lens.
    #[only(lens)] derive AssumptionsAndUpdates.
    #[only(lens)] derive block.block_account.


    Import LensNotations.
    #[local] Open Scope lens_scope.

  Definition set_original_nonce (addr: evm.address) (n: keccak.w256) (s sf : AssumptionsAndUpdates) : Prop :=
  match original s !! addr with
  | Some ac => sf = (s &: _original %= <[addr:=ac &: _block_account_nonce .= n]>)
  | None => exists loadedAc, (block.block_account_nonce loadedAc = n)
                             /\ sf = (s &: _original %= <[addr:= loadedAc]>)
  end.


  Search Bvector.Bvector Z.
cpp.spec ((Nscoped (Nscoped (Nglobal (Nid "monad")) (Nid "State"))
       (Nfunction function_qualifiers.N (Nf "set_original_nonce")
          [Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "address")))); "unsigned long"%cpp_type])))
  as set_original_nonce_spec with
    (fun this:ptr =>
       \arg{addrp} "a" (Vptr addrp)
       \arg{nonce} "a" (Vint nonce)
       \prepost{addr q} addrp |-> addressR q addr
       \pre{au} this |-> StateR au
       \post Exists auf, this |-> StateR auf **
                [| set_original_nonce addr (Zdigits.Z_to_binary 256 nonce) au auf |]
    ).
#[global] Instance : LearnEq2 (addressR) := ltac:(solve_learnable).
#[global] Instance : LearnEq1 (StateR) := ltac:(solve_learnable).
cpp.spec (Ninst
             (Nscoped (Nglobal (Nid "monad"))
                (Nfunction function_qualifiers.N (Nf "execute_impl2")
                   [Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Chain"))));
                    Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Transaction"))));
                    Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "address"))));
                    Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockHeader"))));
                    Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockHashBuffer"))));
                    Tref (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "State")))]))
             [Avalue (Eint 11 (Tenum (Nglobal (Nid "evmc_revision"))))])
  as execute_impl2 with (execute_impl2_spec).
  cpp.spec (Nscoped (Nscoped (Nglobal (Nid "monad")) (Nid "State"))
          (Nfunction function_qualifiers.N Nctor
             [Tref (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockState")));
              Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Incarnation"))]))
    as StateConstr with
  (    fun (this:ptr) =>
      \arg{bsp} "" (Vref bsp)
      \arg{incp} "" (Vptr incp)
      \prepost{q inc} incp |-> IncarnationR q inc 
      \post this |-> StateR {| blockStatePtr := bsp; incarnation:= inc; original := ∅; newStates:= ∅ |}).
  
  #[global] Instance : LearnEq2 IncarnationR := ltac:(solve_learnable).
Opaque Zdigits.Z_to_binary.

  Lemma prf: denoteModule module
             ** (opt_reconstr TransactionResult resultT)
             ** wait_for_promise
             ** destrop
             ** destr_res
             ** destr_u256
             ** (has_value "evmc::address")
             ** (value "evmc::address")
             ** get_chain_id
             ** validate_spec
             ** try_op_has_val
             ** destr_outcome_overload
             ** incarnation_constr
             ** StateConstr
             ** set_original_nonce_spec
             ** execute_impl2
             ** destr_incarnation
             |-- ext1.
Proof using MODd.
  verify_spec'.
  go; try (ego; fail).
  Transparent BheaderR.
  unfold BheaderR.
  slauto.
  rewrite <- wp_const_const_delete.
  go.
  unshelve rewrite <- wp_init_implicit.
  slauto.
iAssert (reference_to (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "State"))) state_addr) as "#?"%string;[admit|].
slauto.
Transparent TransactionR.
unfold TransactionR.
slauto.

Ltac slauto2 := go; try name_locals; tryif progress(try (ego; eagerUnifyU; go; fail); try (apply False_rect; try contradiction; try congruence; try nia; fail); try autorewrite with syntactic)
  then slauto2  else idtac.
Ltac slauto1 := go; try name_locals; tryif progress(try (ego; eagerUnifyU; go; fail); try (apply False_rect; try contradiction; try congruence; try nia; fail))
  then slauto1  else idtac.

Transparent libspecs.optionR.
slauto1.
Transparent set_original_nonce.
Existing Instance UNSAFE_read_prim_cancel.
unfold set_original_nonce in *.
simpl in *.
autorewrite with syntactic.
rewrite lookup_empty in H.
forward_reason. subst.
go. subst. go.
unfold BheaderR. go.
#[global] Instance : LearnEq3 (BlockState.Rauth) := ltac:(solve_learnable).
unfold TransactionR. go. eagerUnifyU. slauto.
do 3 (iExists _).  eagerUnifyU. slauto.
cpp.spec (Nscoped (Nscoped (Nglobal (Nid "monad")) (Nid "BlockState"))
       (Nfunction function_qualifiers.N (Nf "can_merge")
          [Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "State"))))]))
         as can_merge with
  (
         fun (this:ptr) =>
  \arg{statep} "" (Vptr statep) 
  \prepost{assumptionsAndUpdates} statep |-> StateR assumptionsAndUpdates
  \prepost{preBlockState g preTxState} this |-> BlockState.Rauth preBlockState g preTxState
  \post{b} [Vbool b] [| if b then  (satisfiesAssumptions assumptionsAndUpdates preTxState) else Logic.True |]).

iAssert (can_merge) as "#?"%string;[admit|].
slauto.
wp_if.
{
  slauto.
  iAssert (  reference_to
    (Tnamed
       (Ninst (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "basic_result"))
          [Atype (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "Result")));
           Atype
             (Tnamed
                (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                   [Atype (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
           Atype
             (Tnamed
                (Ninst
                   (Nscoped (Nscoped (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "experimental")) (Nid "policy"))
                      (Nid "status_code_throw"))
                   [Atype (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "Result")));
                    Atype
                      (Tnamed
                         (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                            [Atype (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                    Atype "void"]))]))
    result_addr) as "#?"%string;[admit|]. (* TODO: add this to ResultSuccessR  and maybe add an observe hint*)
  go.


  (* TODO: generalize over evmc::Result *)
cpp.spec 
       (Ninst
             (Nscoped (Nglobal (Nid "monad"))
                (Nfunction function_qualifiers.N (Nf "has_error")
                   [Tref
                      (Tconst
                         (Tnamed
                            (Ninst (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "basic_result"))
                               [Atype (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "Result")));
                                Atype
                                  (Tnamed
                                     (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                                        [Atype
                                           (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                                Atype
                                  (Tnamed
                                     (Ninst
                                        (Nscoped (Nscoped (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "experimental")) (Nid "policy"))
                                           (Nid "status_code_throw"))
                                        [Atype (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "Result")));
                                         Atype
                                           (Tnamed
                                              (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                                                 [Atype
                                                    (Tnamed
                                                       (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                                         Atype "void"]))])))]))
             [Atype (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "Result")))]) as has_error with
      (\pre emp (* TODO: fix *)
         \arg{resp} "res" (Vptr resp)
         \prepost{res} resp |->  ResultSuccessR EvmcResultR (* TODO: EvmcResultR *) res
         \post [Vbool false] emp
    ).
  
iAssert (has_error) as "#?"%string;[admit|].
slauto.


Definition opt_value_or  :=
specify
  {|
    info_name :=
      Ninst
        (Nscoped
           (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "optional"))
              [Atype (Tnamed (Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")]))])
           (Nfunction function_qualifiers.Ncl (Nf "value_or") ["int&&"%cpp_type]))
        [Atype "int"];
    info_type :=
      tMethod
        (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "optional"))
           [Atype (Tnamed (Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")]))])
        QC (Tnamed (Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")]))
        ["int&&"%cpp_type]
  |}
      ( fun this =>
          \arg{defp} "" (Vptr defp)
           \prepost{q (n:N)} defp |-> intR (cQp.mut q) n
      \pre{q hdr} this |-> libspecs.optionR u256t (u256R q) q (base_fee_per_gas hdr)
      \post{retp} [Vptr retp] retp |-> u256R 1 (match (base_fee_per_gas hdr) with | Some x => x | None => n end)
    ).

Existing Instance UNSAFE_read_prim_cancel.
iAssert (opt_value_or) as "#?"%string;[admit|].
slauto.
Search (primR) Learnable.
go.
repeat (iExists _).
eagerUnifyU.
slauto.
rewrite <- wp_const_const_delete.
slauto.

(*
constexpr const value_type &&value() const && { return static_cast<value_type &&>(_value); }
*)
cpp.spec (Ninst
             (Nscoped (Nglobal (Nid "monad"))
                (Nfunction function_qualifiers.N (Nf "value")
                   [Tref
                      (Tconst
                         (Tnamed
                            (Ninst (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "basic_result"))
                               [Atype (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "Result")));
                                Atype
                                  (Tnamed
                                     (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                                        [Atype
                                           (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                                Atype
                                  (Tnamed
                                     (Ninst
                                        (Nscoped (Nscoped (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "experimental")) (Nid "policy"))
                                           (Nid "status_code_throw"))
                                        [Atype (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "Result")));
                                         Atype
                                           (Tnamed
                                              (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                                                 [Atype
                                                    (Tnamed
                                                       (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                                         Atype "void"]))])))]))
             [Atype (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "Result")))]) as result_value with
    (
      \arg{this} "this" (Vptr this)
       \pre{res} this |-> ResultSuccessR EvmcResultR (* TODO: EvmcResultR *) res
       \post [Vref (this ,, _field "boost::outcome_v2::value_fixme")] emp).

iAssert (result_value) as "#?"%string;[admit|].
go.



Abort.

  End with_Sigma.

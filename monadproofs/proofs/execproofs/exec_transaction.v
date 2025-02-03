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
   Definition execute_final_spec : WpSpec mpredI val val :=
    \arg{statep: ptr} "state" (Vref statep)
    \pre{assumptionsAndUpdates}  statep |-> StateR assumptionsAndUpdates
    \arg{txp} "tx" (Vref txp)
    \prepost{qtx t} txp |-> TransactionR qtx t
    \arg{senderp} "sender" (Vref senderp)
    \prepost{qs} senderp |-> addressR qs (sender t)
    \arg{bfeep: ptr} "base_fee_per_gase" (Vref bfeep)
    \prepost{q basefeepergas} bfeep |-> u256R q basefeepergas
    \arg{i preTxState resultp hdr} "" (Vptr resultp)
    \pre{postTxState result} [| (postTxState, result) = stateAfterTransactionAux hdr preTxState i t |]
    \pre resultp |-> EvmcResultR result
    \arg{benp} "beneficiary" (Vref benp)
    \prepost{benAddr qben} benp |-> addressR qben benAddr
    \pre [| postTxState = applyUpdates assumptionsAndUpdates preTxState |]
    \post{retp}[Vptr retp] Exists assumptionsAndUpdatesFinal,
        retp |-> ReceiptR result ** statep |-> StateR assumptionsAndUpdatesFinal
        ** [| (stateAfterTransaction hdr i preTxState t).1 = applyUpdates assumptionsAndUpdatesFinal preTxState |].

Ltac applyPHyp :=
  let Hbb := fresh "autogenhyp" in
  match goal with
    [ Ha:?T, Hb: _ |- _] =>
      let Tt := type of T in
      unify Tt Prop;
      pose proof Hb as Hbb; apply Ha in Hbb
  end.
Lemma ResultSucRDef {T} (R: T-> _) t : ResultSuccessR R t  -|- o_field CU (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "value_fixme")) |-> R t.
Proof using. Admitted.
Ltac slauto2 := go; try name_locals; tryif progress(try (ego; eagerUnifyU; go; fail); try (apply False_rect; try contradiction; try congruence; try nia; fail); try autorewrite with syntactic)
  then slauto2  else idtac.
Ltac slauto1 := go; try name_locals; tryif progress(try (ego; eagerUnifyU; go; fail); try (apply False_rect; try contradiction; try congruence; try nia; fail))
  then slauto1  else idtac.
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
       \prepost{res} this |-> ResultSuccessR EvmcResultR (* TODO: EvmcResultR *) res
       \post [Vref (this ,, _field "boost::outcome_v2::value_fixme")] emp).


Definition exec_final :=
  specify
  {|
    info_name :=
      Ninst
        (Nscoped (Nglobal (Nid "monad"))
           (Nfunction function_qualifiers.N (Nf "execute_final")
              [Tref (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "State"))); Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Transaction"))));
               Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "address"))));
               Tref (Tconst (Tnamed (Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")])));
               Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "Result")))); Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "address"))))]))
        [Avalue (Eint 11 (Tenum (Nglobal (Nid "evmc_revision"))))];
    info_type :=
      tFunction (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Receipt")))
        [Tref (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "State"))); Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Transaction"))));
         Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "address"))));
         Tref (Tconst (Tnamed (Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")])));
         Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "Result")))); Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "address"))))]
  |} execute_final_spec.

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


  
iAssert (has_error) as "#?"%string;[admit|].
slauto.



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

iAssert (result_value) as "#?"%string;[admit|].
go.
iAssert (exec_final) as "#?"%string;[admit|].
go.
unfold TransactionR.
go.
progress applyPHyp.
repeat (iExists _). eagerUnifyC.
match goal with
| H:context[stateAfterTransactionAux ?a1 ?b1 ?c1 ?d1] |- context[stateAfterTransactionAux ?a2 ?b2 ?c2 ?d2] => 
    unify a1 a2; unify b1 b2; unify c1 c2; unify d1 d2;
    remember (stateAfterTransactionAux a1 b1 c1 d1) as saf; destruct saf as [smid result]
end.

simpl in *.
go.
eagerUnifyU.
  
rewrite ResultSucRDef.
go.
eagerUnifyC.
forward_reason.
subst.
go.
rewrite <- wp_const_const_delete.
go.
rewrite <- wp_const_const_delete.
go.
cpp.spec (Nscoped (Nscoped (Nglobal (Nid "monad")) (Nid "BlockState"))
            (Nfunction function_qualifiers.N (Nf "merge") [Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "State"))))]))
  as merge with
  (
         fun (this:ptr) =>
  \arg{statep} "" (Vptr statep) 
  \prepost{assumptionsAndUpdates} statep |-> StateR assumptionsAndUpdates
  \pre{preBlockState g preTxState} this |-> BlockState.Rauth preBlockState g preTxState
  \pre [| satisfiesAssumptions assumptionsAndUpdates preTxState |]
  \post this |-> BlockState.Rauth preBlockState g (applyUpdates assumptionsAndUpdates preTxState)).
iAssert merge as "#?"%string;[admit|].
go.
Check satisfiesAssumptions.




execute_final_spec
BheaderR
applyHyp
iExists state_addr.
iExists _.
ren_hyp tx Transaction.
do 2 (iExists _).
iExists tx.
do 5 (iExists _).
iExists i. iExists prevTxGlobalState.
iExists _.
iExists header.
destruct (stateAfterTransactionAux header prevTxGlobalState i tx).
simpl.
work. eagerUnifyC.
go.
simpl.
go.

do 7 (iExists _). 
iExists _, _, _, _
rewrite <- (bi.exist_intro prevTxGlobalState).
slauto.
go.



Abort.

  End with_Sigma.

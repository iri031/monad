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
       \post{retp} [Vptr retp] (retp |-> emp)
    ).
  
Lemma prf: denoteModule module
             ** (opt_reconstr TransactionResult resultT)
             ** tvector_spec
             ** reset_promises
             ** (fork_taskg (Nscoped (Ninst "monad::execute_transactions(const monad::Block&, monad::fiber::PriorityPool&, const monad::Chain&, const monad::BlockHashBuffer&, monad::BlockState &)" [Avalue (Eint 11 "enum evmc_revision")]) (Nanon 0)))
             ** vector_op_monad
             ** recover_sender
             ** wait_for_promise
             ** set_value
             ** destrop
             ** destr_res
             ** (has_value "evmc::address")
             ** (value "evmc::address")
             ** get_chain_id
             ** validate_spec
             |-- ext1.
Proof using MODd.
  verify_spec'.
  go; try (ego; fail).
  Transparent BheaderR.
  unfold BheaderR.
  slauto.
  rewrite <- wp_const_const.
  2:{ hnf.
  Search wp_const.
  Locate "wp_make_mutable".
   Search wp_mutable.
  slauto.
  Search wp_const.
  rewrite <- wp_const_const.
  2:{ hnf.

  _ : _x_8 |-> u256R 1 (chainid chain)
  _ : txp |-> TransactionR qtx _t_
  --------------------------------------∗
  wp_destroy_named module (Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")]) _x_8
    (interp module 1
       (wp_decls module
          [region:
            "_outcome_try_unique_name_temporary1" @ _outcome_try_unique_name_temporary1_addr; "prev" @ prev_addr;
            "block_state" @ block_state_addr; "block_hash_buffer" @ block_hash_buffer_addr; "hdr" @ hdr_addr; "sender" @ sender_addr;
            "tx" @ tx_addr; "i" @ i_addr; "chain" @ chain_addr; return {?: Tnamed resultn}]
          []
          (λ (ρ : region) (free' : FreeTemps),
             ▷ wp_block module ρ
                 [Sif None
                    (Ecall
                       (Ecast Cfun2ptr
                          (Eglobal
                             (Ninst
                                (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2"))
                                   (Nfunction function_qualifiers.N (Nf "try_operation_has_value")
                                      [Tref
                                         (Tnamed
                                            (Ninst (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "basic_result"))
                                               [Atype "void";      
Abort.

End with_Sigma.

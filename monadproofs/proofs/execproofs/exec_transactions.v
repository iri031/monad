Require Import monad.proofs.misc.
Require Import monad.proofs.libspecs.
Require Import monad.proofs.evmopsem.
Import linearity.
Require Import bedrock.auto.invariants.
Require Import bedrock.auto.cpp.proof.

Require Import bedrock.auto.cpp.tactics4.
Require Import monad.asts.exb.
Require Import monad.proofs.exec_specs.


Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}.
  Context  {MODd : exb.module ⊧ CU}.


  Existing Instance learnArrUnsafe.
  Existing Instance learnpArrUnsafe.

  Set Nested Proofs Allowed.
  Opaque BlockHashBufferR.
  Hint Opaque BlockHashBufferR: br_opacity.
  
Lemma prf: denoteModule module
             ** tvector_spec
             ** reset_promises
             ** (fork_taskg (Nscoped (Ninst "monad::execute_transactions(const monad::Block&, monad::fiber::PriorityPool&, const monad::Chain&, const monad::BlockHashBuffer&, monad::BlockState &)" [Avalue (Eint 11 "enum evmc_revision")]) (Nanon 0)))
             ** vector_op_monad
             ** recover_sender
             ** opt_move_assign
             ** wait_for_promise
             ** set_value
             ** destrop
             |-- exect.
Proof using MODd.
  verify_spec'.
  name_locals.
  hideRhs.
  hideP ff.

  
  Transparent VectorR.
  unfold BlockR, VectorR.
  work.
  ren_hyp vectorbase ptr.
  rewrite (arrLearn2 vectorbase).
  rewrite (arrLearn2 (_global "monad::senders")).
  rewrite (arrLearn2 (_global "monad::results")).
  rewrite parrLearn2.
  unhideAllFromWork.
  slauto.
  iExists unit.
  go.
  iExists  (fun i _ =>
    let '(actual_final_state, receipts) := stateAfterTransactions (header block) preBlockState (take i (transactions block)) in
    _global "monad::results" |-> arrayR (Tnamed "std::optional<Result<Receipt>>") (fun r => libspecs.optionR ReceiptR 1 (Some r)) (take i receipts)
     ** block_statep |-> BlockState.R block preBlockState actual_final_state
     ** ([∗ list] _ ∈ (take i (transactions block)),  (block_hash_bufferp |-> BlockHashBufferR (qbuf*/(N_to_Qp (1+ lengthN (transactions block)))) buf))
     **  vectorbase
          |-> arrayR (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Transaction"))) (λ t0 : Transaction, TransactionR qb t0)
               (take i (transactions block))).
  go.
  unfold lengthN in *.
  autorewrite with syntactic.
  go.
  autorewrite with syntactic.
  go.
  hideP p.
  setoid_rewrite sharePromise.
  rewrite parrayR_sep. go.
  IPM.perm_left ltac:(fun L n =>
                        match L with
                        | context[PromiseProducerR] =>  iRevert n
                        end
                     ).
  hideLhs.
  rewrite unit_snoc_cons.
  unhideAllFromWork.
  iIntros "?"%string.
  rewrite parrayR_cons.
  autorewrite with syntactic.
  go.
  autorewrite with syntactic.
  go.
  autorewrite with syntactic.
  go.
  hideP p.
  rewrite parrayR_app1.
  go.
  autorewrite with syntactic.
  (* for loop *)
  name_locals.
  assert (exists ival:nat, ival=0) as Hex by (eexists; reflexivity).
  destruct Hex as [ival Hex].
  rewrite (generalize_arrayR_loopinv ival (_global "monad::senders")); [| assumption].
  rewrite -> (generalize_arrayR_loopinv ival vectorbase); [| assumption].
  rewrite (vectorbase_loopinv _ _ _ _ ival); auto.
  rewrite (generalize_parrayR_loopinv ival (_global "monad::promises")); [| assumption].
  rewrite (generalize_parrayR_loopinv ival (_global "monad::promises" ,, _)); [| assumption].
  assert (Vint 0 = Vnat ival) as Hexx by (subst; auto).
  rewrite Hexx. (* TODO: use a more precise pattern *)
  clear Hexx.
  assert (ival <= length (transactions block)) as Hle by (subst; lia).
  clear Hex.
  genOver ival.
  wp_for (fun _ => emp).
  go.
  unhideAllFromWork.
  slauto.
  wp_if.
  { (* loop condition is true and thus the body runs. so we need to reistablish the loopinv *)
    slauto.
    ren_hyp ival nat.
    applyToSomeHyp @drop_S2.
    match goal with
      [H:_ |- _] => destruct H as [tri Htt]; destruct Htt as [Httl Httr]
    end.
    repeat rewrite Httr.
    repeat rewrite -> arrayR_cons.
    repeat rewrite -> parrayR_cons.
    go.
    autorewrite with syntactic.
    progress repeat rewrite o_sub_sub.
    simpl.
    progress go.
    Set Printing Coercions.
    iExists (N.of_nat ival). (* automate this using some Refine1 hint *)
    slauto.
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
    go.
    iSplitL ""%string.
    {
      unfold taskOpSpec.
      verify_spec'.
      slauto.
      iExists (N.of_nat ival). (* automate this using some Refine1 hint *)
      go.
      autorewrite with syntactic.
      slauto.
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
Abort.
End with_Sigma.


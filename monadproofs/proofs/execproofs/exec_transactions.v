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
  Context `{Sigma:cpp_logic} {CU: genv}.
           (*   hh = @has_own_monpred thread_info _Σ fracR (@cinv_inG _Σ (@cpp_has_cinv thread_info _Σ Sigma)) *)
  Context  {MODd : exb.module ⊧ CU}.


  Existing Instance learnArrUnsafe.
  Existing Instance learnpArrUnsafe.

  Set Nested Proofs Allowed.
  Opaque BlockHashBufferR.
  Hint Opaque BlockHashBufferR: br_opacity.

  (* TODO: move *)

#[global] Instance : LearnEq2 ChainR:= ltac:(solve_learnable).
#[global] Instance : LearnEq3 BlockState.Rfrag := ltac:(solve_learnable).
  Lemma header_split_loopinv {T} q (b: BlockHeader) (l : list T) (i:nat) (p:i=0):
    BheaderR q b -|- BheaderR (q/(N_to_Qp (1+ lengthN l))) b ** 
    ([∗ list] _ ∈ (drop i l),  (BheaderR (q*/(N_to_Qp (1+ lengthN l))) b)).
  Proof using. Admitted.


Definition opt_reconstr_spec T ty : ptr -> WpSpec mpredI val val :=
      (fun (this:ptr) =>
       \arg{other} "other" (Vptr other)
       \prepost{(R: T -> Rep) t} other |-> R t
       \pre{prev} this |-> libspecs.optionR ty R 1 prev
       \post [Vptr this] this |-> libspecs.optionR ty R 1 (Some t)
    ).
      
Definition opt_reconstr baseModelTy basety :=
λ {thread_info : biIndex} {_Σ : gFunctors} {Sigma : cpp_logic thread_info _Σ} {CU : genv},
  specify
    {|
      info_name :=
        Ninst
        (Nscoped
          (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "optional"))
             [Atype basety])
          (Nfunction function_qualifiers.N (Nop OOEqual)
             [Trv_ref
                      basety])) [Atype basety];
      info_type :=
        tMethod
          (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "optional"))
             [Atype basety])
          QM
          (Tref
             (Tnamed
                (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "optional"))
                   [Atype basety])))
          [Trv_ref  basety]
    |} (opt_reconstr_spec baseModelTy resultT).
      
      Lemma  rect_len g l lt h bs : (g, l) = stateAfterTransactions h bs lt ->
                                    length l = length lt.
      Proof using. Admitted. (* easy *)
      Lemma takesr2 {X} l n (x:X) : length l = n → take (S n) (l++[x]) = take n l ++ [x].
      Proof using. Admitted. (* easy *)

Definition destr_res :=
λ {thread_info : biIndex} {_Σ : gFunctors} {Sigma : cpp_logic thread_info _Σ} {CU : genv},
  specify
    {|
      info_name :=
        Nscoped
          resultn
          (Nfunction function_qualifiers.N Ndtor []);
      info_type :=
        tDtor
          resultn
    |} (λ this : ptr, \pre{res} this |-> ResultSuccessR ReceiptR res
                        \post    emp).

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
             ** ext1
             ** destr_res
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
    ((_global "monad::results" |-> arrayR oResultT (fun r => libspecs.optionR resultT (ResultSuccessR ReceiptR) 1 (Some r)) receipts)
     ** ([∗ list] _ ∈ (take i (transactions block)),  (block_hash_bufferp |-> BlockHashBufferR (qbuf*/(N_to_Qp (1+ lengthN (transactions block)))) buf))
     ** ([∗ list] _ ∈ (take i (transactions block)),  (chainp |-> ChainR (qchain*/(N_to_Qp (1+ lengthN (transactions block)))) chain))
     ** _global "monad::senders" |->
          arrayR
            (Tnamed "std::optional<evmc::address>")
            (fun t=> optionAddressR qs (Some (sender t)))
            (take i (transactions block))

     ** (_global "monad::promises" |->
            parrayR
              (Tnamed "boost::fibers::promise<void>")
              (fun i t => PromiseUnusableR)
              ((map (fun _ => ()) (take i (transactions block)))))
     ** ([∗ list] _ ∈ (take i (transactions block)),  blockp ,, o_field CU (Nscoped (Nscoped (Nglobal (Nid "monad")) (Nid "Block")) (Nid "header"))
      |-> BheaderR (qb*/(N_to_Qp (1+ lengthN (transactions block)))) (header block))
     ** ([∗ list] _ ∈ (take i (transactions block)),  (block_statep |-> BlockState.Rfrag preBlockState (qf*/(N_to_Qp (1+ lengthN (transactions block)))) g))
     **  vectorbase
          |-> arrayR (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Transaction"))) (λ t0 : Transaction, TransactionR qb t0)
          (take i (transactions block)))
      ** block_statep |-> BlockState.Rauth preBlockState g actual_final_state
           ).
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
  rewrite parrayR_nil. go.
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
  rewrite -> (generalize_arrayR_loopinv ival (_global "monad::senders")); [| assumption].
  rewrite (generalize_arrayR_loopinv ival (_global "monad::results")); [| assumption].
  rewrite -> (generalize_arrayR_loopinv ival vectorbase); [| assumption].
  rewrite (vectorbase_loopinv _ _ _ _ ival); auto.
  rewrite (generalize_parrayR_loopinv ival (_global "monad::promises")); [| assumption].
  rewrite (generalize_parrayR_loopinv ival (_global "monad::promises" ,, _)); [| assumption].
  rewrite -> @bhb_splitl_loopinv with (i:=ival) (l:=transactions block) by assumption.
  rewrite -> @BlockState.split_frag_loopinv with (i:=ival) (l:=transactions block) by assumption.
  rewrite -> @ChainR_split_loopinv with (i:=ival) (l:=transactions block) by assumption.
  rewrite -> @header_split_loopinv with (i:=ival) (l:=transactions block) by assumption.
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
    repeat rewrite skipn_map.
    applyToSomeHyp @drop_S2.
    match goal with
      [H:_ |- _] => destruct H as [tri Htt]; destruct Htt as [Httl Httr]
    end.
    repeat rewrite Httr.
    go.
    iExists (N.of_nat ival). (* automate this using some Refine1 hint *)
    slauto.
    aggregateRepPieces a.
    slauto.
    repeat rewrite -> arrayR_cons.
    repeat rewrite -> parrayR_cons.
    go.
    autorewrite with syntactic.
    progress repeat rewrite o_sub_sub.
    simpl.
    progress go.
    IPM.perm_left ltac:(fun L n =>
      match L with
      |   _ |-> BlockHashBufferR _ _ => iRevert n
      end
      ).
    IPM.perm_left ltac:(fun L n =>
      match L with
      |   _ |-> BlockState.Rfrag _ _ _ => iRevert n
      end
      ).
    repeat IPM.perm_left_spatial  ltac:(fun L n =>
      match L with
      | _ .[_ ! Z.of_nat ival] |-> _ => iRevert n
      end).
    IPM.perm_left_spatial  ltac:(fun L n =>
      match L with
      | _ .[_ ! _] |-> PromiseProducerR _ _ => iRevert n
      end).
    IPM.perm_left_spatial  ltac:(fun L n =>
      match L with
      | chainp |-> _ => iRevert n
      end).
    IPM.perm_left_spatial  ltac:(fun L n =>
      match L with
      | _ |-> BheaderR _ _ => iRevert n
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
      match goal with
        |- context[stateAfterTransactions ?a ?b (take ival ?l)] => remember (stateAfterTransactions a b (take ival l)) as sabc
      end.
      destruct sabc.
      simpl in *.
      go.
#[global] Instance : LearnEq2 BheaderR := ltac:(solve_learnable).
      go.
      unshelve (do 3 iExists _; eagerUnifyU);[].
      slauto.
      match goal with
        |- context[stateAfterTransaction ?a ?b ?c ?d] => remember (stateAfterTransaction a b c d) as sat
      end.
      destruct sat.
      simpl in *.
      #[global] Instance rrr {T}: LearnEq2 (@ResultSuccessR _ _ _ T) := ltac:(solve_learnable).
      slauto.
      replace (1+ival)%Z with (ival+1)%Z  by lia.
      go.
      erewrite -> take_S_r with (n:=ival);[| eauto].
      rewrite stateAfterTransactionsC.
      rewrite <- Heqsabc.
      simpl.
      Hint Rewrite @length_take_le using lia: syntactic.
      autorewrite with syntactic.
      rewrite <- Heqsat.
      simpl.
      go.
      repeat rewrite arrayR_snoc.
      go.
      autorewrite with syntactic.
      go.
      repeat rewrite big_opL_snoc.
      go.
      applyToSomeHyp rect_len.
      autorewrite with syntactic in *.
      go.
      rewrite map_app.
      simpl.
      subst.
      rewrite parrayR_app1.
      go.
      autorewrite with syntactic.
      go.
    }
    {
  cpp.spec (Nscoped 
              (Nscoped (Ninst "monad::execute_transactions(const monad::Block&, monad::fiber::PriorityPool&, const monad::Chain&, const monad::BlockHashBuffer&, monad::BlockState &)" [Avalue (Eint 11 "enum evmc_revision")]) (Nanon 0)) (Nfunction function_qualifiers.N Ndtor []))  as exlamdestr inline.
      
      slauto.
      iExists (1+ival).
      unfold lengthN in *.
      go.
Lemma cancel_at `{xx: cpp_logic} (p:ptr) (R1 R2 : Rep) :
  (R1 |-- R2) -> (p |-> R1 |-- p |-> R2).
Proof using.
  apply _at_mono.
Qed.
      Set Printing Coercions.
      
      replace (Z.of_nat ival + 1)%Z with (Z.of_nat (S ival)); try lia.
      go.
      progress repeat rewrite Nat.add_succ_r.
      progress setoid_rewrite Nat.add_succ_r.
      go.
      repeat rewrite skipn_map.
      go.
      icancel (cancel_at (_global "monad::promises"  ,, _)).
      {
        repeat f_equiv; try 
                          apply Nat.add_succ_r.
      }
      autorewrite with syntactic.
      go.
      normalize_ptrs.
      replace (1+ Z.of_nat ival + 1)%Z with (1+ Z.of_nat (S ival))%Z; try lia.
      icancel (cancel_at (_global "monad::promises"  ,, _)).
      {
        repeat f_equiv; try 
                          apply Nat.add_succ_r.
      }

      (*
  --------------------------------------□
  _ : blockp ,, o_field CU (Nscoped (Nscoped (Nglobal (Nid "monad")) (Nid "Block")) (Nid "transactions"))
      |-> VectorRbase (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Transaction")))
            (qb * / N_to_Qp (1 + N.of_nat (length (transactions block)))) vectorbase (N.of_nat (length (transactions block)))
  --------------------------------------∗
  emp
*)
      
    }
    
      
      
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


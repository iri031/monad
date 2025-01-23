Require Import QArith.
Require Import bedrock.auto.cpp.proof.

Require Import stdpp.gmap.
Require Import bedrock.auto.cpp.tactics4.

Import cQp_compat.
Import linearity.
Hint Rewrite @firstn_all: syntactic.
Hint Rewrite Nat.add_0_r Z.add_0_r :syntactic.
Hint Rewrite @drop_all: syntactic.
Hint Rewrite nat_N_Z: syntactic.
Hint Rewrite offset_ptr_sub_0 using (auto; apply has_size; exact _): syntactic.
Hint Rewrite @skipn_0: syntactic.
Ltac hideP fullyHiddenPostcond :=
  IPM.perm_left ltac:(fun L n =>
                        match L with
                        | HiddenPostCondition => hideFromWorkAs L fullyHiddenPostcond
                        end
                     ).
Ltac iExistsTac  foo:=match goal with
                        |- environments.envs_entails _ (Exists (_:?T), _) => iExists ((ltac:(foo)):T)
                      end.
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

#[local] Open Scope Z_scope.

(*
Require Import EVMOpSem.evmfull. *)
Import cancelable_invariants.

Definition storedAtGhostLoc  `{Sigma:cpp_logic} {CU: genv} (q: Q) (g: gname) (n: nat) : mpred.
  Admitted.


Ltac slauto := go; try name_locals; tryif progress(try (ego; eagerUnifyU; go; fail); try (apply False_rect; try contradiction; try congruence; try nia; fail); try autorewrite with syntactic equiv iff slbwd in *; try rewrite left_id)
  then slauto  else idtac.
  

Section cp.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI algebra.frac.fracR}. (* some standard assumptions about the c++ logic *)

  Definition parrayR  {T:Type} ty (Rs : nat -> T -> Rep) (l: list T) : Rep :=
  .[ ty ! length l ] |-> validR ** [| is_Some (size_of _ ty) |] **
  (* ^ both of these are only relevant for empty arrays, otherwise, they are implied by the
     following conjunct *)
     [∗ list] i ↦ li ∈ l, .[ ty ! Z.of_nat i ] |-> (type_ptrR ty ** Rs i li).


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

  Lemma parrayR_nil {T} (R : nat -> T -> Rep) ty: parrayR ty R [] -|- validR ** [| is_Some (size_of _ ty) |].
  Proof using.
    unfold parrayR. simpl.
    apply: (observe_both (is_Some (size_of _ ty))) => Hsz.
    change (Z.of_nat 0) with 0%Z.
    autorewrite with syntactic.
    rewrite _offsetR_sub_0; try assumption.
    iSplit; work.
  Qed.
  
End cp.
Opaque parrayR.
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
Hint Opaque parrayR: br_opacity.

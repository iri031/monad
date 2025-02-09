Require Import QArith.
Require Import bedrock.auto.cpp.proof.

Require Import stdpp.gmap.
Require Import bedrock.auto.cpp.tactics4.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Z.
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

Ltac simplPure :=
  simpl in *; autorewrite with syntactic (* equiv *) iff  in *; try rewrite left_id in *; simpl in *.

Lemma trans4 `{Equivalence} a b a' b': R a a' -> R b b' -> R a b -> R a' b'.
Proof. now intros -> ->. Qed.

Tactic Notation "aac_rewriteh" uconstr(L) "in" hyp(H) :=
  (eapply trans4 in H;[| try aac_rewrite L; try reflexivity | try aac_rewrite L; try reflexivity ]).

Ltac slautot rw := go; try name_locals; tryif progress(try (ego; eagerUnifyU; go; fail); try (apply False_rect; try contradiction; try congruence; try nia; fail); rw; try (erewrite take_S_r;[| eauto;fail]))
  then slautot rw  else idtac.

Ltac slauto := slautot idtac. (* try rewrite left_id; *)
Ltac slauto1 := slautot ltac:(autorewrite with syntactic); try iPureIntro.
Ltac slauto2 := slautot ltac:(autorewrite with syntactic equiv iff slbwd; try rewrite left_id); try iPureIntro.

Lemma pureAsWand (mpred:bi) (P:Prop) (C:mpred) E: P -> environments.envs_entails E ([|P|] -* C) ->  environments.envs_entails E C.
Proof using.
  intros p.
  repeat rewrite to_entails.
  intros Hp.
  go.
  rewrite Hp.
  go.
Qed.
Lemma genWand  (mpred:bi) {T} (ival:T)  W (C:mpred) E :
  environments.envs_entails E ((Exists ival, W ival) -* C) ->  environments.envs_entails E (W ival-* C).
Proof using.
  repeat rewrite to_entails.
  intros Hp.
  go.
  rewrite Hp.
  go.
  iExists _. iStopProof. reflexivity.
Qed.

Ltac genOver ival :=
  repeat match goal with
    | H:context[ival] |- _ => apply (@pureAsWand _ _ _ _ H); clear H
    end;
  repeat IPM.perm_left ltac:(fun L n =>
                               match L with
                               | context[ival] => iRevert n
                               end
                            );
  repeat rewrite bi.wand_curry;
  pattern ival;
  lazymatch goal with
  | |- (fun x => environments.envs_entails _ (@?P x -* _)) _ =>
      apply (@genWand mpredI nat ival P)
  end; clear ival; simpl;
  lazymatch goal with
    |- environments.envs_entails _ (?P -* _) => hideFromWork P
  end;
  iIntros "?"%string.

Ltac wapplyObserve lemma:=
    try intros;
  idtac;
  [
    wapply (@observe_elim _ _ _ (lemma)) || wapply (@observe_elim _ _ _ (lemma _))
    || wapply (@observe_elim _ _ _ (lemma _ _)) || wapply (@observe_elim _ _ _ (lemma _ _ _))
    || wapply (@observe_elim _ _ _ (lemma _ _ _ _)) || wapply (@observe_elim _ _ _ (lemma _ _ _ _ _))
    || wapply (@observe_elim _ _ _ (lemma _ _ _ _ _ _)) || wapply (@observe_elim _ _ _ (lemma _ _ _ _ _ _ _))
    || wapply (@observe_elim _ _ _ (lemma _ _ _ _ _ _ _ _)) || wapply (@observe_elim _ _ _ (lemma _ _ _ _ _ _ _ _ _))
    || wapply (@observe_elim _ _ _ (lemma _ _ _ _ _ _ _ _ _ _)) || wapply (@observe_elim _ _ _ (lemma _ _ _ _ _ _ _ _ _ _ _))
    ||
    wapply (@observe_2_elim _ _ _ _ (lemma)) || wapply (@observe_2_elim _ _ _ _ (lemma _))
    || wapply (@observe_2_elim _ _ _ _ (lemma _ _)) || wapply (@observe_2_elim _ _ _ _ (lemma _ _ _))
    || wapply (@observe_2_elim _ _ _ _ (lemma _ _ _ _)) || wapply (@observe_2_elim _ _ _ _ (lemma _ _ _ _ _))
    || wapply (@observe_2_elim _ _ _ _ (lemma _ _ _ _ _ _)) || wapply (@observe_2_elim _ _ _ _ (lemma _ _ _ _ _ _ _))
    || wapply (@observe_2_elim _ _ _ _ (lemma _ _ _ _ _ _ _ _)) || wapply (@observe_2_elim _ _ _ _ (lemma _ _ _ _ _ _ _ _ _))
    || wapply (@observe_2_elim _ _ _ _ (lemma _ _ _ _ _ _ _ _ _ _)) || wapply (@observe_2_elim _ _ _ _ (lemma _ _ _ _ _ _ _ _ _ _ _))
  ].

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

  Lemma generalize_arrayR_loopinv_produce (i : nat) (p:ptr) {X : Type} (R : X → Rep) (ty : type) xs (Heq: i=(length xs)):
    p |-> arrayR ty R xs
    -|- p |-> arrayR ty R (take i xs).
  Proof using.
    intros. subst.
    autorewrite with syntactic.
    reflexivity.
  Qed.
    
  Lemma generalize_parrayR_loopinv_produce (i : nat) (p:ptr) {X : Type} (R : nat -> X → Rep) (ty : type) xs (Heq: i=length xs):
    p |-> parrayR ty R xs
    -|- (p |-> parrayR ty R (take i xs)).
  Proof using.
    intros. subst.
    autorewrite with syntactic.
    reflexivity.
  Qed.

  Lemma arrayR_nils{T} ty (R:T->_) : arrayR ty R [] = (.[ ty ! 0%nat ] |-> validR ∗ [| is_Some (size_of CU ty) |] ∗ emp)%I.
  Proof. rewrite arrayR_eq /arrayR_def arrR_eq /arrR_def. simpl. reflexivity. Qed.
  Lemma unit_snoc_cons (l: list unit) : (l++[()] = ()::l).
  Proof using.
    induction l; auto.
    simpl.
    destruct a.
    rewrite IHl. reflexivity.
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

   Lemma parrLearn2r {T} ltr (R: nat -> T -> Rep) (ty:type):
   parrayR ty R ltr
   |-- validR ** (.[ ty ! length ltr ] |-> validR) ** [| is_Some (size_of CU ty) |] **
   ( □ ([∗ list] k↦_ ∈ ltr, (.[ ty ! k ] |-> type_ptrR ty))) **
   parrayR ty R ltr.
   Proof using.
     apply Rep_entails_at.
     intros.
     rewrite -> parrLearn2 at 1.
     Opaque parrayR.
     go.
     setoid_rewrite _at_big_sepL.
     go.
     setoid_rewrite _at_offsetR.
     setoid_rewrite _at_type_ptrR.
     go.
   Qed.
   Transparent parrayR.
    
  Lemma parrayR_app {X} ty xs ys : forall (R:nat -> X->Rep),
    parrayR ty R (xs ++ ys) -|- parrayR ty R xs ** .[ ty ! length xs ] |-> parrayR ty (fun ii => R (length xs +ii)) ys.
  Proof.
    induction xs => /=.
    { intros.
      intros.
      iSplit.
      {
        go.
        rewrite -> parrLearn2r at 1.
        go.
        change (Z.of_nat 0) with 0%Z.
        repeat rewrite o_sub_0; auto.
        repeat rewrite _offsetR_id.
        go.
        unfold parrayR. go.
        change (Z.of_nat 0) with 0%Z.
        repeat rewrite o_sub_0; auto.
        repeat rewrite _offsetR_id.
        go.
      }

      {
        unfold parrayR.
        go.
        simpl.
        change (Z.of_nat 0) with 0%Z.
        repeat rewrite o_sub_0; auto.
        repeat rewrite _offsetR_id.
        go.
      }
    }
    { intros. repeat rewrite parrayR_cons.
      by rewrite IHxs !_offsetR_sep !_offsetR_succ_sub Nat2Z.inj_succ -!assoc.
    }
  Qed.

  Lemma parrayR_app1 {X} ty xs y : forall (R:nat -> X->Rep),
    parrayR ty R (xs ++ [y]) -|- parrayR ty R xs ** .[ ty ! length xs ] |-> (R (length xs) y ** type_ptrR ty).
  Proof.
    intros.
    apply Rep_equiv_at.
    intros.
    apply: (observe_both (is_Some (size_of _ ty))) => Hsz.
    rewrite parrayR_app.
    iSplit; go; unfold parrayR; simpl;
      autorewrite with syntactic;
      repeat rewrite o_sub_0; auto; go.
    normalize_ptrs.
    go.
  Qed.
  
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
    | Nglobal  (Nfunction _ i _) => bool_decide (i=fname)
    | Ninst nm _ => isFunctionNamed2 fname nm
    | Nscoped _ (Nfunction _ i _) => bool_decide (i=fname)
    | _ => false
    end.

  Fixpoint containsDep (n:name): bool :=
    match n with
    | Ndependent _ => true
    | Nglobal  (Nfunction _ i _) => false
    | Ninst nm _ => containsDep nm
    | Nscoped nm (Nfunction _ i _) => containsDep nm
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

  #[global] Instance parrayR_mono X ty:
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

  #[global] Instance parrayR_flip_mono X ty:
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

  Lemma primr_split (p:ptr) ty (q:Qp) v :
    p|-> primR ty (cQp.mut q) v -|- (p |-> primR ty (cQp.mut q/2) v) ** p |-> primR ty (cQp.mut q/2) v.
  Proof using.
    rewrite -> cfractional_split_half with (R := fun q => primR ty q v).
    2:{ exact _. }
    rewrite _at_sep.
    f_equiv; f_equiv; f_equiv;
    simpl;
      rewrite cQp.scale_mut;
      f_equiv;
    destruct q; simpl in *;
      solveQpeq;
      solveQeq.
  Qed.
  Definition primR_split_C := [CANCEL] primr_split.

    Lemma arrayR_cell2 i {X} ty (R:X->Rep) xs:
    (Z.of_nat i < Z.of_nat (length xs))%Z ->
          exists x, 
            xs !! i = Some x /\	(** We have an [i]th element *)
    (arrayR ty R xs -|-
           arrayR ty R (take i xs) **
           _sub ty (Z.of_nat i) |-> type_ptrR ty **
           _sub ty (Z.of_nat i) |-> R  x **
           _sub ty ((Z.of_nat i) + 1) |-> arrayR ty R (drop (1+i) xs)).
  Proof using.
    intros.
    assert (i<length xs)%nat as Hex by lia.
    applyToSomeHyp @lookup_lt_is_Some_2.
    hnf in autogenhyp.
    forward_reason.
    subst.
    eexists; split; eauto.
    apply arrayR_cell; auto.
  Qed.
      
  Lemma fold_id {A:Type} (f: A->A->A) (c: Commutative (=) f) (asoc: Associative (=) f)
    (start id: A) (lid: LeftId (=) id f) (l: list A):
    fold_left f l start = f (fold_left f l id) start.
  Proof using.
    hnf in lid. revert start.
    induction l; auto;[].
    simpl. rewrite lid.
    intros.
    simpl.
    rewrite IHl.
    symmetry.
    rewrite IHl.
    aac_reflexivity.
  Qed.
  
  Lemma fold_split {A:Type} (f: A->A->A) (c: Commutative (=) f) (asoc: Associative (=) f)
    (id: A) (lid: LeftId (=) id f) (l: list A) (lSplitSize: nat):
    fold_left f l id =
      f (fold_left f (firstn lSplitSize l) id) (fold_left f (skipn lSplitSize l) id).
  Proof using.
    rewrite <- (take_drop lSplitSize) at 1.
    rewrite fold_left_app.
    rewrite fold_id.
    aac_reflexivity.
  Qed.


  Definition liftf {A:Type} (f: A->A->A) (P:A->Prop) {hdec: forall a, Decision (P a)} (fpres: forall a b, P a -> P b -> P (f a b))
    (a: dsig P) (b: dsig P) : dsig P :=
    (dexist (f (`a) (`b)) (fpres _ _ (proj2_dsig a) (proj2_dsig b))).

  #[global] Instance liftfComm {A:Type} (f: A->A->A) (P:A->Prop) {hdec: forall a, Decision (P a)} (fpres: forall a b, P a -> P b -> P (f a b))
    (c: Commutative (=) f) : Commutative (=) (liftf f P fpres).
  Proof using.
    hnf.
    intros x y. destruct x, y. simpl in *.
    unfold liftf.
    simpl.
    Search dsig.
    apply dsig_eq.
    simpl.
    auto.
  Qed.
  
  #[global] Instance liftfAssoc {A:Type} (f: A->A->A) (P:A->Prop) {hdec: forall a, Decision (P a)} (fpres: forall a b, P a -> P b -> P (f a b))
    (c: Associative (=) f) : Associative (=) (liftf f P fpres).
  Proof using.
    hnf.
    intros x y z. destruct x, y, z. simpl in *.
    unfold liftf.
    simpl.
    apply dsig_eq.
    simpl.
    auto.
  Qed.

    Lemma fold_left_proj1dsig {A:Type} (f: A->A->A) (P:A->Prop) {hdec: forall a, Decision (P a)} (fpres: forall a b, P a -> P b -> P (f a b)) l start:
      proj1_sig (fold_left (liftf f P fpres) l start) = fold_left f (map proj1_sig l) (`start).
    Proof using.
      revert start.
      induction l; auto.
      intros.  simpl.
      rewrite IHl.
      simpl.
      reflexivity.
    Qed.
  
  Lemma fold_split_condid1 {A:Type} (f: A->A->A) (P:A->Prop) {hdec: forall a, Decision (P a)} (c: Commutative (=) f) (asoc: Associative (=) f)
    (id: A) (lid: forall a, P a -> f id a = a) (ld: list (dsig P)) (lSplitSize: nat) (pid: P id)
    (fpres: forall a b, P a -> P b -> P (f a b)):
    let l:= map proj1_sig ld in
    fold_left f l id=
      f (fold_left f (firstn lSplitSize l) id) (fold_left f (skipn lSplitSize l) id).
  Proof using.
    pose proof (fun lid => @fold_split _  (liftf f P fpres) _ _ (dexist id pid) lid ld lSplitSize) as Hh.
    lapply Hh.
    2:{ hnf. intros x. destruct x. unfold liftf. simpl.
        apply dsig_eq. simpl. apply lid.
        apply bool_decide_unpack in i. assumption. }
    intros Hx.
    clear Hh.
    simpl.
    apply (f_equal proj1_sig) in Hx.
    simpl in Hx.

    repeat rewrite fold_left_proj1dsig in Hx.
    simpl.
    unfold dexist in Hx. simpl in Hx.
    repeat rewrite map_take in Hx.
    repeat rewrite map_drop in Hx.
    rewrite Hx.
    f_equal.
    f_equal.
    rewrite skipn_map.
    reflexivity.
  Qed.
    Fixpoint pairProofDsig {A} (l: list A) (P:A->Prop) {hdec: forall a, Decision (P a)} (pl: forall a, In a l -> P a) : list (dsig P).
      destruct l; simpl in *.
      - exact [].
      -  pose proof (pl a ltac:(left;apply eq_refl)) as pll.
         apply cons.
         + exists a. apply bool_decide_pack. assumption.
         +  apply pairProofDsig with (l:=l). intros. apply pl. right. assumption.
    Defined.
    Lemma pairProofDsigMapFst {A} (l: list A) (P:A->Prop) {hdec: forall a, Decision (P a)} (pl: forall a, In a l -> P a):
      map proj1_sig (pairProofDsig l P pl) = l.
    Proof using.
      induction l; auto.
      -  simpl. auto. f_equal.
         rewrite IHl.
         reflexivity.
    Qed.
  
  Lemma fold_split_condid {A:Type} (f: A->A->A) (P:A->Prop) {hdec: forall a, Decision (P a)} (c: Commutative (=) f) (asoc: Associative (=) f)
    (id: A) (lid: forall a, P a -> f id a = a) (l: list A) (pl: forall a, In a l -> P a) (lSplitSize: nat) (pid: P id)
    (fpres: forall a b, P a -> P b -> P (f a b)):
    fold_left f l id=
      f (fold_left f (firstn lSplitSize l) id) (fold_left f (skipn lSplitSize l) id).
  Proof using.
    pose proof (fold_split_condid1 f P c asoc id lid (pairProofDsig l P pl)) as Hx.
    simpl in Hx.
    repeat rewrite pairProofDsigMapFst in Hx.
    apply Hx; auto.
  Qed.

  Open Scope Z_scope.
  Lemma fold_split_gcd  (l: list Z) (pl: forall a, In a l -> 0 <= a) (lSplitSize: nat):
    fold_left Z.gcd l 0=
      Z.gcd (fold_left Z.gcd (firstn lSplitSize l) 0) (fold_left Z.gcd (skipn lSplitSize l) 0).
  Proof using.
    apply fold_split_condid with (P:= fun z => 0<=z); auto; try exact _; try lia;
      intros; try apply Z.gcd_nonneg.
    rewrite Z.gcd_0_l.
    rewrite Z.abs_eq; auto.
  Qed.
  Lemma obsUintArrayR (p:ptr) q (l: list Z): Observe [| forall (a : Z), In a l → 0 ≤ a|] (p|->arrayR "unsigned int" (fun i => primR "unsigned int" q (Vint i)) l) .
  Proof using.
    apply observe_intro; [exact _ |].
    revert p.
    induction l; auto.
    simpl. intros. rewrite arrayR_cons.
    hideRhs.
    go.
    rewrite -> IHl at 1.
    go.
    unhideAllFromWork.
    go.
    iPureIntro.
    intros? Hin.
    destruct Hin; auto.
    subst.
    type.has_type_prop.
  Qed.
  Lemma spurious {T:Type} {ing: Inhabited T} (P: mpred) :
  P |-- Exists a:T, P.
  Proof using.
    work.
    iExists (@inhabitant T _).
    work.
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
Hint Rewrite @arrayR_nils: syntactic.
Hint Rewrite @repeat_length: syntactic.
Hint Rewrite @length_cons: syntactic.
Hint Rewrite @firstn_0: syntactic.

Lemma takesr2 {X} l n (x:X) : length l = n → take (S n) (l++[x]) = take n l ++ [x].
Proof using. Admitted. (* easy *)

Hint Rewrite @length_take_le using lia: syntactic.

Lemma cancel_at `{xx: cpp_logic} (p:ptr) (R1 R2 : Rep) :
  (R1 |-- R2) -> (p |-> R1 |-- p |-> R2).
Proof using.
  apply _at_mono.
Qed.

Hint Resolve primR_split_C : br_opacity.



#[global] Hint Rewrite @inj_iff using (typeclasses eauto): iff.
#[global] Hint Rewrite negb_if: syntactic.
#[global] Hint Rewrite bool_decide_eq_true_2 using (auto; fail): syntactic.
#[global] Hint Rewrite bool_decide_eq_false_2 using (auto; fail): syntactic.
#[global] Hint Rewrite @elem_of_cons: iff.
#[global] Hint Rewrite N.sub_diag : syntactic.
#[global] Hint Rewrite seqN_lengthN @lengthN_nil @seqN_S_start: syntactic.
#[global] Hint Rewrite orb_true_r: syntactic.
#[global] Hint Rewrite N_nat_Z: syntactic.
#[global] Hint Rewrite @left_id using (exact _): equiv.
#[global] Hint Rewrite @right_id using (exact _): equiv.
#[global] Hint Rewrite @elem_of_list_difference: iff.

Require Import bedrock.prelude.propset.

#[global] Hint Rewrite @propset_singleton_equiv: equiv.

#[global] Hint Rewrite <- @spurious using exact _: slbwd.

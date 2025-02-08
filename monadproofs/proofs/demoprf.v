Require Import monad.asts.demo.
Require Import monad.proofs.misc.
Require Import monad.proofs.libspecs.
Require Import bedrock.auto.invariants.
Require Import bedrock.auto.cpp.proof.
Require Import bedrock.auto.cpp.tactics4.
Require Import monad.proofs.demomisc.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import cQp_compat.
Open Scope cQp_scope.
Import linearity.
Import Verbose.
Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
  Context  {MODd : demo.module ⊧ CU}.
  Definition cQpc := cQp.mk false.
  Coercion cQpc : Qp >-> cQp.t.

  cpp.spec "foo()" as foo_spec with (
        \prepost{xv:N} _global "x" |-> primR "unsigned int" 1  xv
        \pre{yv:N} _global "y" |-> primR "unsigned int" 1 yv
        \post _global "y" |-> primR "unsigned int" 1 (xv+1)%N
      ).

  Lemma prf: denoteModule demo.module |-- foo_spec.
  Proof using.
    iIntrosDestructs.
    verify_spec.
    do 5 run1.
    - slauto.
    - hideLoc (_global "y"). go.
      rewrite <- primR_anyR_ex.
      work.
      unhideAllFromWork.
      iExists yv.
      iFrame.
      iIntros.
      runUntilPost.
      
   Abort.

  cpp.spec "foo()" as foo_spec_correct with (
        \prepost{xv:N} _global "x" |-> primR "unsigned int" 1 xv
        \pre{yv:N} _global "y" |-> primR.body "unsigned int" 1 yv
        \post _global "y" |-> primR.body "unsigned int" 1 ((xv+1) `mod` (2^32))%N
      ).

  Lemma prf: denoteModule demo.module |-- foo_spec_correct.
  Proof.
    verify_spec'.
    slauto.
  Qed.


  
  cpp.spec "sfoo()" as sfoo_spec with (
        \prepost{xv:Z} _global "a" |-> primR "int" 1 xv
        \pre{yv:N} _global "b" |-> primR.body "int" 1 yv
        \post _global "b" |-> primR.body "int" 1 ((xv+1))%Z
      ).

  Lemma sprf: denoteModule demo.module |-- sfoo_spec.
  Proof.
    verify_spec'.
    slauto.
    provePure.
    type.has_type_prop_prep.
  Abort.
  
  cpp.spec "sfoo()" as sfoo_spec_correct with (
        \prepost{xv:Z} _global "a" |-> primR "int" 1 xv
        \pre [| (- 2 ^ (32 - 1) -1  ≤ xv ≤ 2 ^ (32 - 1) - 2)%Z |]
        \pre{yv:N} _global "b" |-> primR.body "int" 1 yv
        \post _global "b" |-> primR.body "int" 1 ((xv+1))%Z
      ).

  Lemma sprf: denoteModule demo.module |-- sfoo_spec_correct.
  Proof.
    verify_spec'.
    slauto.
  Qed.


  (* TODO: add lambdap and lambdStructObjOwnership arguments *)
  Definition ThreadR (lamStructName: core.name) (P Q : mpred) : Rep. Proof using. Admitted.
  
  Definition ThreadConstructor (lamStructName: core.name) (this:ptr): WpSpec mpredI val val :=
    \arg{lambdap:ptr} "lambda" (Vref lambdap)
    \prepost{lamStructObjOwnership} lambdap |-> lamStructObjOwnership (* ownerhsip of fields othe lambda struct *)
    \pre{taskPre taskPost}
      specify {| info_name :=  (Nscoped lamStructName taskOpName);
                info_type := tMethod lamStructName QC "void" [] |}
      (fun (this:ptr) =>
         \prepost this |-> lamStructObjOwnership
         \pre taskPre
         \post taskPost)
    
    \post this |-> ThreadR lamStructName taskPre taskPost.

  Definition ThreadDtor (lamStructName: core.name) (this:ptr): WpSpec mpredI val val :=
    \pre{taskPre taskPost} this |-> ThreadR lamStructName taskPre taskPost
    \post emp.
  
  Definition fork_start (lamStructName: core.name) (this:ptr): WpSpec mpredI val val :=
    \prepost{P Q} this |-> ThreadR lamStructName P Q
    \pre P
    \post emp.

  Definition join (lamStructName: core.name) (this:ptr): WpSpec mpredI val val :=
    \prepost{P Q} this |-> ThreadR lamStructName P Q
    \post Q.

  cpp.spec "parallel_gcd_lcm(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)" as pgl with
      (
        \arg{ap} "a" (Vref ap)
        \prepost{(qa:Qp) (av:N)} ap |-> primR "unsigned int" qa av
        \arg{bp} "b" (Vref bp)
        \prepost{(qb:Qp) (bv:N)} bp |-> primR "unsigned int" qb bv
        \arg{gcdp} "gcd_result" (Vref gcdp)
        \pre{garbage1:N} gcdp |-> primR "unsigned int" 1 garbage1
        \arg{lcmp} "lcm_result" (Vref lcmp)
        \pre{garbage2:N} lcmp |-> primR "unsigned int" 1 garbage2
        \pre[| 0<bv \/ 0<av |]%N
        \post gcdp |-> primR "unsigned int" 1 (Z.gcd av bv)
              ** (if decide (av*bv < 2^32)%N then
                  lcmp |-> primR "unsigned int" 1 (Z.lcm av bv)
                  else Exists garbage3, lcmp |-> primR "unsigned int" 1 garbage3)
      ).

  cpp.spec "gcd(unsigned int, unsigned int)" as gcd_spec with (
        \arg{a:Z} "a" (Vint a)
        \arg{b:Z} "b" (Vint b)
        \post [Vint (Z.gcd a b)] emp
      ).

  cpp.spec "gcd(const unsigned int&, const unsigned int&, unsigned int&)" as gcd2_spec with (
        \arg{ap} "a" (Vref ap)
        \prepost{(qa:Qp) (av:N)} ap |-> primR "unsigned int" qa av
        \arg{bp} "b" (Vref bp)
        \prepost{(qb:Qp) (bv:N)} bp |-> primR "unsigned int" qb bv
        \arg{gp} "gcd_result" (Vref gp)
        \pre{garbage1:N} gp |-> primR "unsigned int" 1 garbage1
        \post gp |-> primR "unsigned int" 1 (Z.gcd av bv)
      ).

  Definition thread_constructor (lamStructTyName: core.name) :=
  specify
    {|
      info_name :=
        Nscoped (Ninst "Thread" [Atype (Tnamed lamStructTyName)]) (Nctor [Tref (Tconst (Tnamed lamStructTyName))]);
      info_type :=
        tCtor (Ninst "Thread" [Atype (Tnamed lamStructTyName)])
          [Tref (Tconst (Tnamed lamStructTyName))]
    |}
    (ThreadConstructor lamStructTyName).

  Definition thread_destructor (lamStructTyName: core.name) :=
  specify
    {|
      info_name :=
        Nscoped (Ninst "Thread" [Atype (Tnamed lamStructTyName)]) Ndtor;
      info_type :=
        tDtor (Ninst "Thread" [Atype (Tnamed lamStructTyName)])
    |}
    (ThreadDtor lamStructTyName).
  
  (*TODO: rename to just start? *)
  Definition thread_fork_start (lamStructTyName: core.name) :=
  specify
    {|
      info_name :=
        Nscoped (Ninst "Thread" [Atype (Tnamed lamStructTyName)]) (Nfunction function_qualifiers.N "fork_start" []);
      info_type :=
        tMethod (Ninst "Thread" [Atype (Tnamed lamStructTyName)]) QM "void" []
    |}
    (fork_start lamStructTyName).

  Definition thread_fork_join (lamStructTyName: core.name) :=
  specify
    {|
      info_name :=
        Nscoped (Ninst "Thread" [Atype (Tnamed lamStructTyName)]) (Nfunction function_qualifiers.N "join" []);
      info_type :=
        tMethod (Ninst "Thread" [Atype (Tnamed lamStructTyName)]) QM "void" []
    |}
    (join lamStructTyName).
  
  cpp.spec "Thread<parallel_gcd_lcm(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)::@0>::fork_start()"
           as ff with (fork_start "parallel_gcd_lcm(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)::@0").
  Lemma par: denoteModule module |-- pgl.
  Proof using.
    verify_spec'.
    go.
  Abort.

  Definition thread_class_specs lamStructName :=
    thread_constructor lamStructName **
    thread_fork_start lamStructName **
    thread_fork_join lamStructName **
    thread_destructor lamStructName.
   
  Existing Instance UNSAFE_read_prim_cancel.
  #[global] Instance : forall ty P Q, Observe (reference_toR (Tnamed ty)) (ThreadR ty P Q).
  Proof. Admitted.

  Lemma primr_split (p:ptr) ty (q:Qp) v :
    p|-> primR ty (cQpc q) v -|- (p |-> primR ty (cQpc q/2) v) ** p |-> primR ty (cQpc q/2) v.
  Proof using.
    unfold cQpc.
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
  #[global] Instance obss (pp:ptr) ty P Q: Observe (reference_to (Tnamed (Ninst "Thread" [Atype (Tnamed ty)])) pp) (pp |-> ThreadR ty P Q).
  Proof. Admitted.
  cpp.spec (Nscoped 
              "parallel_gcd_lcm(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)::@0" Ndtor)  as lamdestr
                                                                                                                          inline.
  
  Lemma par: denoteModule module ** (thread_class_specs "parallel_gcd_lcm(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)::@0") ** gcd2_spec |-- pgl.
  Proof using MODd.
    unfold thread_class_specs.
    verify_spec'.
    slauto.
    aggregateRepPieces gcdLambda_addr.
    go.
    
    fold cQpc.
    (* TODO: pick a better name for gp. TODO. replace unintR with primR  *)
    iExists (gcdp |-> uintR 1%Qp garbage1 ** ap |-> uintR (qa/2) av ** bp |-> uintR (qb/2) bv).
    evar (post:mpred).
    iExists post.
    hideFromWork post.
    go.
    iSplitL "".
    { verify_spec'.
      go.
      unhideAllFromWork.
      unfold post.
      iClear "#".
      iStopProof. reflexivity.
    }
    unhideAllFromWork.
    unfold post.
    iIntrosDestructs.
    do 6 run1.
  #[global] Instance : forall ty , LearnEq2 (ThreadR ty) := ltac:(solve_learnable).
    step.
    step.
    step.
    fold cQpc.
    rewrite (primr_split ap).
    rewrite (primr_split bp).
    go.
    Compute (Z.gcd 0 0).
    Search 0%Z (Z.gcd _ _)%Z.
    pose proof (Z.gcd_nonneg av bv).
    pose proof (Z.gcd_eq_0 av bv).
    provePure.
    nia.
    work.
    run1.
    run1.
    run1.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    do 3 step.
    go.
    case_decide.
    {
      Arith.remove_useless_mod_a.
      icancel (cancel_at lcmp).
      f_equiv.
      unfold Z.lcm.
      rewrite Z.lcm_equiv1.
      rewrite Z.abs_eq.
      rewrite Z.quot_div_nonneg.
      reflexivity.
      nia.
      nia.
      apply Z_div_nonneg_nonneg; try nia.
      nia.
      go.
    }
    {
      go.
    }
  Qed.

  Check gcd_spec. (* jump to defn here to contrast the simpler spec because of passing args by value *)

  Ltac simplPure :=
    simpl in *; autorewrite with syntactic (* equiv *) iff  in *; try rewrite left_id in *; simpl in *.
  Search Commutative Z.gcd.

  Import Instances.Z.
  Lemma trans4 `{Equivalence} a b a' b': R a a' -> R b b' -> R a b -> R a' b'.
  Proof. now intros -> ->. Qed.
  
  Tactic Notation "aac_rewriteh" uconstr(L) "in" hyp(H) :=
    (eapply trans4 in H;[| try aac_rewrite L; try reflexivity | try aac_rewrite L; try reflexivity ]).
  
  Lemma proof: denoteModule module |-- gcd_spec.
  Proof.
    verify_spec.
    slauto.

    wp_while  (fun _ => (Exists a' b' : Z,
                      [| 0 ≤ a' ≤ 2 ^ 32 - 1 |]%Z **
                      [| 0 ≤ b' ≤ 2 ^ 32 - 1 |]%Z **
                      a_addr |-> primR Tu32 (cQp.mut 1) (Vint a') **
                      b_addr |-> primR Tu32 (cQp.mut 1) (Vint b') ** [| Z.gcd a' b' = Z.gcd a b |])).
    slauto.
    wp_if.
    { (* loop condition is true: loop executed body *)
      slauto.
      iPureIntro.
      aac_normalise in H.
      aac_rewrite Z.gcd_mod; try Arith.arith_solve.
      aac_normalise.
      Arith.arith_solve.
    }

    { (* loop condition is false: loop terminates *)
      slauto.
      simplPure.
      aac_normalise in H.
      aac_rewriteh Z.gcd_0_r_nonneg in H; subst; try Arith.arith_solve.
      go.
    }

  Qed.

  Lemma gcd2_proof: denoteModule module |-- gcd2_spec.
  Proof.
    verify_spec'.
    wapply proof. go.
  Qed.

  Lemma pos (p:ptr) (v:Z) : p |-> uintR 1 v |-- [| 0 <=v |] ** p |-> uintR 1 v.
  Proof using.
    go.
  Qed.
  (* TODO: lemma to unroll arrayR for 3 elements *)

  (* parallelization: *)
  Check Z.gcd_comm.
  Check Z.gcd_assoc.

  Definition gcdl_spec_core : WpSpec mpredI val val :=
        \arg{numsp:ptr} "nums" (Vptr numsp)
        \prepost{(l: list Z) (q:Qp)} (numsp |-> arrayR "unsigned int" (fun i => primR "unsigned int" q (Vint i)) l) 
        \arg "size" (Vint (lengthZ l))
        \post [Vint (fold_left Z.gcd l 0)] emp.
  
  cpp.spec "gcdl(unsigned int*, unsigned int)" as gcdl_spec with (gcdl_spec_core).
  cpp.spec "parallel_gcdl(unsigned int*, unsigned int)" as parallel_gcdl_spec with (gcdl_spec_core).


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

  Lemma gcdl_proof: denoteModule module |-- gcdl_spec.
  Proof using MODd.
    verify_spec.
    slauto.
    wp_for (fun _ => Exists iv:nat,
                i_addr |-> uintR (cQp.mut 1) iv **
                [| iv <= length l |]%nat **
              result_addr |-> uintR (cQp.mut 1) ((fold_left Z.gcd (firstn iv l) 0))
           ).
    go. iExists 0%nat. go.
    wp_if.
    {
      slauto.
      rename t into iv.
      unfold lengthN in *.
      autorewrite with syntactic in *.
      eapplyToSomeHyp @arrayR_cell2.
      forward_reason.
      rewrite -> autogenhypr.
      hideRhs.
      go.
      unhideAllFromWork.
      slauto.
      wapply proof.
      go.
      iExists (1+iv)%nat.
      go.
      erewrite take_S_r;[|eauto].
      rewrite fold_left_app.
      simpl.
      go.
      rewrite -> autogenhypr.
      go.
    }
    {
      slauto.
      unfold lengthN in *.
      rename t into iv.
      assert (iv=length l) as Heq by lia.
      subst.
      autorewrite with syntactic.
      go.
    }
  Qed.

      Compute (Z.quot (-5) 4).
      Compute (Z.div (-5) 4).
      Set Printing Coercions.
      Search Z.div Nat.div.
  Set Default Goal Selector "!".
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

  Import stdpp.list.
  Import stdpp.decidable.

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

  Lemma pgcdl_proof: denoteModule module
                       ** (thread_class_specs "parallel_gcdl(unsigned int*, unsigned int)::@0")
                       |-- parallel_gcdl_spec.
  Proof using MODd.
    unfold thread_class_specs.
    verify_spec'.
    wapply gcdl_proof. work.
    wapplyObserve  obsUintArrayR.
    eagerUnifyU. work.
    slauto.
    aggregateRepPieces gcdlLambda_addr.
    go.
    hideP ps.
    Opaque Nat.div.
    assert ( (length l `div` 2 <= length l)%nat) as Hle.
    {
      rewrite <- Nat.div2_div.
      apply Nat.le_div2_diag_l.
    }
    assert ( (length l `div` 2 <= length l)) as Hlez.
    {
      rewrite <- (Nat2Z.inj_div _ 2).
      lia.
    }
    rewrite -> arrayR_split with (i:=((length l)/2)%nat) (xs:=l) by lia.
    slauto.
    rewrite (primr_split nums_addr).
    rewrite (primr_split mid_addr).
    go.
    repeat IPM.perm_left ltac:(fun L n=>
                          match L with
                          | numsp |-> _ => iRevert n
                          | resultl_addr |-> _ => iRevert n
                          end
                              ) .
    IPM.perm_left ltac:(fun L n=>
                          match L with
                          | nums_addr |-> _ => iRevert n
                          end).
    IPM.perm_left ltac:(fun L n=>
                          match L with
                          | mid_addr |-> _ => iRevert n
                          end).
    repeat rewrite bi.wand_curry.
    match goal with
      [ |-environments.envs_entails _ (?R -* _)] =>
        iIntrosDestructs;
        iExists R
    end.
    evar (post:mpred).
    iExists post.
    hideFromWork post.
    go.

    iSplitL "".
    { verify_spec'.
      slauto.
      unfold lengthN. go.
      autorewrite with syntactic.
      rewrite Z.quot_div_nonneg; try lia.
      go.
      rewrite Nat2Z.inj_div.
      go.
      iExists _. eagerUnifyU.
      go.
      unhideAllFromWork.
      unfold post.
      iClear "#".
      iStopProof. reflexivity.
    }
    unhideAllFromWork.
    unfold post.
    iIntrosDestructs.
    slauto.
    unfold lengthN.
    autorewrite with syntactic.
    Search (valid_ptr (_ .[_ ! _])).
    rewrite Z.quot_div_nonneg; try lia.
    rewrite Nat2Z.inj_div. (* add to syntacctic? *)
    slauto.
    unfold lengthN.
    Hint Rewrite @length_drop: syntactic.
    autorewrite with syntactic.
    rewrite -> Nat2Z.inj_sub by lia.
    Arith.remove_useless_mod_a.
    rewrite Nat2Z.inj_div.
    simpl.
    go.
    iExists _. eagerUnifyU.
    slauto.
    wapply proof. go.
  cpp.spec (Nscoped 
              "parallel_gcdl(unsigned int*, unsigned int)::@0" Ndtor)  as lam2destr  inline.
  go.

  Set Nested Proofs Allowed.
  Lemma primR2_anyR : ∀ t (q:Qp) (v:val) (p:ptr),
      p|-> primR t (q/2) v ** p|->primR t (q/2) v  |-- p|->anyR t q.
  Proof using. Admitted.
  Definition primR2_anyRC := [CANCEL] primR2_anyR.
  Hint Resolve primR2_anyRC: br_opacity.
  go.
  Hint Resolve array_combine_C: br_opacity.
  go.
  hideLhs.
  rewrite <- arrayR_combine.
  unhideAllFromWork.
  simpl. work.
  rewrite Nat2Z.inj_div. go.
  iClear "#".
  iStopProof.
  f_equiv.
  f_equal.
  f_equal.
  symmetry.
  apply fold_split_gcd.
  auto.
Qed.
    
End with_Sigma.
(*
- pretty printing of goal: ltac.
- hide cQp?
- docker image
-  rename all Vref to Vptr?
- replace all Z.gcd by N.gcd. no Vint, only Vn. or only Vint and Z stuff
- remove all occurrences nat ?
- S n by 1+n
- remove type in array offset
 *)

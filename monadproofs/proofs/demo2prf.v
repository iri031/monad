Require Import monad.proofs.demo2.

Require Import monad.proofs.misc. (* monad/proofs/misc.v *)
Require Import bedrock.auto.invariants.
Require Import bedrock.auto.cpp.proof.
Require Import bedrock.auto.cpp.tactics4.
Require Import monad.proofs.demomisc.
Require Import monad.proofs.demoprf.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Z.
Import stdpp.list.
Import stdpp.decidable.
Import cQp_compat.
Open Scope cQp_scope.
Open Scope Z_scope.
Import linearity.
Import Verbose.
Ltac slauto := misc.slauto1.
Disable Notation take.
Disable Notation drop.
Disable Notation "`div`" (all).
Disable Notation intR.
Disable Notation uintR.

Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
  Context  {MODd : demo2.module ⊧ CU}.

  Open Scope Z_scope.
  Set Nested Proofs Allowed.
  (**  *Arrays *)
  Definition gcdl_spec_core : WpSpec mpredI val val :=
      \arg{numsp:ptr} "nums" (Vptr numsp)
      \prepost{(l: list Z) (q:Qp)} numsp |-> arrayR uint (fun i:Z => primR uint q i) l
      \arg "size" (Vint (length l))
      \post [Vint (fold_left Z.gcd l 0)] emp.

  Example fold_left_gcd (n1 n2 n3: Z) :
    fold_left Z.gcd [n1;n2;n3] 0 =  Z.gcd (Z.gcd (Z.gcd 0 n1) n2) n3.
  Proof. reflexivity. Abort.
  
  Example arrayR3 (p:ptr) (n1 n2 n3: Z) (q: Qp):
    p |-> arrayR uint (fun i:Z => primR uint q i) [n1;n2;n3]
      -|- ( valid_ptr (p .[ uint ! 3 ])
              ** p |-> primR uint q n1
              ** p .[ uint ! 1 ] |-> primR uint q n2
              ** p .[ uint ! 2 ] |-> primR uint q n3).
  Proof.
    repeat rewrite arrayR_cons.
    repeat rewrite arrayR_nil.
    iSplit; go;
    repeat rewrite o_sub_sub;
    closed.norm closed.numeric_types; go.
  Abort.

    
  cpp.spec "gcdl(unsigned int*, unsigned int)" as gcdl_spec with (gcdl_spec_core).
  cpp.spec "parallel_gcdl(unsigned int*, unsigned int)" as parallel_gcdl_spec with (gcdl_spec_core).


  (** * 2+ ways to split an arrays *)
  (** split fraction: both threads can read entire array *)
  Lemma fractionalSplitArrayR (numsp:ptr) (l: list Z) (q:Qp):
    numsp |-> arrayR uint (fun i:Z => primR uint q i) l |--
      numsp |-> arrayR uint (fun i:Z => primR uint (q/2) i) l
      ** numsp |-> arrayR uint (fun i:Z => primR uint (q/2) i) l.
  Proof.
    rewrite -> cfractional_split_half with (R := fun q => arrayR uint (fun i:Z => primR uint q i) l);
      [| exact _].
    rewrite _at_sep.
    f_equiv; f_equiv; f_equiv;
      simpl; rewrite cqpp2; auto.
  Qed.

  (** subarray partitioning: when threads concurrently read/write to disjoint segments.
     demonstrated in next example, which also illustrates the power of commutativity
   *)
  Lemma arrayR_split {T} ty (base:ptr) (i:nat) xs (R: T-> Rep):
    (i <= length xs)%nat ->
       base |-> arrayR ty R xs
    |-- base |-> arrayR ty R (firstn i xs) ** base .[ ty ! i ] |-> arrayR ty R (skipn i xs).
  Proof.
    intros.
    rewrite arrayR_split; eauto. go. 
  Qed.
  

  Check Z.gcd_comm.
  Check Z.gcd_assoc.

  (** *Parallelizing a sequence of operations
- e.g. sequence of operations monad transactions.
- Commutativivity enables ||: a o b = b o a

o commutative, with i as its left identity (forall x, i o x = x)

fold_left o [a1;a2;a3;a4;a5;a6] i =
((((((i o a1) o a2) o a3) o a4) o a5) o a6)


(((i o a1) o a2 ) o a3 )        (((i o a4) o a5 ) o a6 )
                    \               /
                     \             /
                      \           /
                   left_result   right_result
                          \       /
                           \     /
                            \   /
                        (left_result o right_result)

also, arrays
*)

  Hint Rewrite @fold_left_app: syntactic.
  Existing Instance UNSAFE_read_prim_cancel.
  
  Lemma gcd_proof: denoteModule module |-- gcd_spec.
  Proof using.
    rewrite <- demoprf.gcd_proof.
    apply denoteModule_weaken.
    apply module_le_true.
    exact _.
  Qed.
  
  Lemma gcdl_proof: denoteModule module |-- gcdl_spec.
  Proof using MODd with (fold cQpc).
    verify_spec.
    slauto.
    wp_for (fun _ => Exists iv:nat,
        i_addr |-> primR uint 1 iv
        ** [| iv <= length l |]%nat
        ** result_addr |-> primR uint 1 ((fold_left Z.gcd (firstn iv l) 0))).
    go. iExists 0%nat. go.
    wp_if.
    {
      slauto.
      eapplyToSomeHyp @arrayR_cell2.
      forward_reason.
      rewrite -> autogenhypr.
      hideRhs.
      go.
      unhideAllFromWork.
      slauto. (* call to gcd. we have already proved it's spec *)
      wapply gcd_proof. work. (* gcd_spec is now in context *)
      go. (* loop body finished, reistablish loopinv *)
      iExists (1+iv)%nat.
      slauto.
      simpl.
      go.
      rewrite -> autogenhypr.
      go.
    }
    {
      slauto.
      assert (iv=length l) as Heq by lia.
      subst.
      autorewrite with syntactic.
      go.
    }
  Qed.
  
      Compute (Z.quot (-5) 4).
      Compute (Z.div (-5) 4).
      Set Default Goal Selector "!".
  cpp.spec (Nscoped 
              "parallel_gcdl(unsigned int*, unsigned int)::@0" Ndtor)  as lam2destr  inline.


  Lemma pgcdl_proof: denoteModule module
                       ** (thread_class_specs "parallel_gcdl(unsigned int*, unsigned int)::@0")
                       |-- parallel_gcdl_spec.
  Proof using MODd with (fold cQpc).
    unfold thread_class_specs.
    verify_spec'.
    wapply gcdl_proof.
    wapply gcd_proof. go.
    name_locals.
    wapplyObserve  obsUintArrayR.
    eagerUnifyU. work.
    aggregateRepPieces gcdlLambda_addr.
    go.
    hideP ps.
    Opaque Nat.div.
    assert ( (length l/ 2 <= length l)%nat) as Hle.
    {
      rewrite <- Nat.div2_div.
      apply Nat.le_div2_diag_l.
    }
    nat2ZNLdup.
    rewrite (primr_split nums_addr).
    rewrite (primr_split mid_addr).
    simpl in *.
    closed.norm closed.numeric_types.
    rewrite -> arrayR_split with (i:=((length l)/2)%nat) (xs:=l) by lia;
      go... (* array ownership spit into 2 pieces *)
    revertAdrs constr:([numsp; resultl_addr; nums_addr; mid_addr]).
    repeat rewrite bi.wand_curry.
    intantiateWand.
    instWithPEvar taskPost.
    go.
    iSplitL "".
    { verify_spec'.
      go.
      iExists _. eagerUnifyU.
      autorewrite with syntactic. go.
      erefl.
    }
    unhideAllFromWork. subst taskPost.
    autorewrite with syntactic. go. 
    iExists _. eagerUnifyU. 
    autorewrite with syntactic. go.
    wapply @arrayR_combinep. eagerUnifyU.
    autorewrite with syntactic. go.
    (* c++ semantics computes ... postcond requires *)
    icancel (cancel_at p);[| go].
    do 2 f_equiv.
    symmetry.
    apply fold_split_gcd.
    auto.
    Check fold_split.
  Qed.
  Lemma fold_split_gcd  (l: list Z) (pl: forall a, In a l -> 0 <= a) (lSplitSize: nat):
    fold_left Z.gcd l 0=
      Z.gcd (fold_left Z.gcd (firstn lSplitSize l) 0) (fold_left Z.gcd (skipn lSplitSize l) 0).
  Proof using. apply misc.fold_split_gcd; auto. Qed.

  Lemma fold_split {A:Type} (f: A->A->A) (c: Commutative (=) f) (asoc: Associative (=) f)
    (id: A) (lid: LeftId (=) id f) (l: list A) (lSplitSize: nat):
    fold_left f l id =
      f (fold_left f (firstn lSplitSize l) id)
        (fold_left f (skipn  lSplitSize l) id).
  Proof.
    rewrite <- (take_drop lSplitSize) at 1.
    rewrite fold_left_app.
    rewrite fold_id.
    aac_reflexivity.
  Qed.

  (** *Structs and Classes
     we often use multi-word numbers: EVMword is 256 bits *)
  
  Lemma unint32 (p:ptr) (v:Z) : p |-> primR uint 1 v |-- [| 0 <=v < 2^32 |] ** p |-> primR uint 1 v.
  Proof.
    go.
  Qed.
  (*class UnboundUint *)
  
Require Import Coq.NArith.BinNat.
Require Import Coq.Lists.List.
Require Import Coq.Wellfounded.Wellfounded.
Require Import Coq.Program.Wf.
Import ListNotations.
Require Import FunInd.

Open Scope N_scope.
Search N.size.
Require Import Recdef.
Function split_in_32 (n : N) {measure (fun n => N.to_nat (N.log2 n))} : list N :=
  match n with
  | 0%N => []
  | 1%N => [1]
  | _ =>
    let chunk := n `mod` (2^32) in
    let n'   := n / (2^32) in
    chunk :: split_in_32 n'
  end.
Proof.
  {
    intros. subst.
    rewrite <- N.shiftr_div_pow2.
    repeat rewrite N.log2_shiftr.
    simpl.
    lia.
  }
  {
    intros. subst.
    rewrite <- N.shiftr_div_pow2.
    repeat rewrite N.log2_shiftr.
    simpl.
    lia.
  }
Defined.

Eval vm_compute in (split_in_32 (2^65 + 2^32 + 45)).

Definition UnboundUintR (q:Qp) (n:N) : Rep :=
  let pieces32 : list N := split_in_32 n in 
  _field "size" |-> primR uint q (length pieces32)
  ** Exists arrBase, _field "data" |-> primR uint q (Vptr arrBase)
     ** pureR (arrBase |-> arrayR uint (fun i:N => primR uint q i)  pieces32).
(** note the logical abstraction *)

Example unfoldUnboundUintR (p:ptr) q n:
let pieces32 := split_in_32 n in   
  p |-> UnboundUintR q n -|-
       p |-> _field "size" |-> primR uint q (length pieces32)
       ** Exists arrBase, p |-> _field "data" |-> primR uint q (Vptr arrBase)
                           ** arrBase |-> arrayR uint (fun i:N => primR uint q i)  pieces32.
Proof. simpl.  unfold UnboundUintR. iSplit; go. Qed.

  
End with_Sigma.
  

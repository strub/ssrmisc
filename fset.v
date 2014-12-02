(* --------------------------------------------------------------------
 * (c) Copyright 2014--2014 Pierre-Yves Strub
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import choice fintype generic_quotient.

Local Open Scope quotient_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Reserved Notation "{ 'useq' T }"
  (at level 0, format "{ 'useq'  T }").

Reserved Notation "[ 'useq' s ]"
  (at level 0, format "[ 'useq'  s ]").

Reserved Notation "{ 'fset' T }"
  (at level 0, format "{ 'fset'  T }").

Reserved Notation "[ 'fset' 'of' s ]"
  (at level 0, format "[ 'fset'  'of'  s ]").

Reserved Notation "[ 'fset' x1 ; .. ; xn & s ]"
  (at level 0, format "[ 'fset' '['  x1 ; '/'  .. ; '/'  xn ']' '/ '  &  s ]").

Reserved Notation "[ 'fset' x1 ; .. ; xn ]"
  (at level 0, format "[ 'fset' '['  x1 ; '/'  .. ; '/'  xn ']' ]").

Reserved Notation "[ 'fset' ]"
  (at level 0, format "[ 'fset' ]").

Reserved Notation "[ 'fset' : T ]"
  (at level 0, format "[ 'fset' :  T ]").

(* -------------------------------------------------------------------- *)
Section USeqDef.
  Variables (T : eqType).

  Inductive useq_type: predArgType :=
    USeq (usval : seq T) & uniq usval.

  Coercion usval s := let: USeq s _ := s in s.

  Definition useq_of of phant T : Type := useq_type.
  Identity Coercion type_of_useq : useq_of >-> useq_type.

  Notation usT := (useq_of (Phant T)).

  Canonical  useq_subType := Eval hnf in [subType for usval].
  Definition useq_eqMixin := Eval hnf in [eqMixin of useq_type by <:].
  Canonical  useq_eqType  := Eval hnf in EqType useq_type useq_eqMixin.

  Canonical useq_for_subType := Eval hnf in [subType of usT].
  Canonical useq_for_eqType  := Eval hnf in [eqType  of usT].

  Canonical useq_predType :=
    Eval hnf in mkPredType (fun t : usT => mem_seq t).

  Lemma memuE (s : usT) : mem s = mem (val s).
  Proof. by []. Qed.
End USeqDef.

Definition useq_of_seq (T : eqType) (s : seq T) :=
  USeq (undup_uniq s).

Notation "{ 'useq' T }" := (@useq_of _ (Phant T)).
Notation "[ 'useq' s ]" := (useq_of_seq s).

(* -------------------------------------------------------------------- *)
Lemma useqK (T : eqType) (s : seq T): [useq s] = undup s :> seq T.
Proof. by []. Qed.

Lemma uniq_useq (T : eqType) (s : {useq T}): uniq s.
Proof. by case s. Qed.

Hint Resolve uniq_useq.

Lemma useqE (T : eqType) (s : {useq T}): s = [useq s].
Proof. by apply/eqP; rewrite eqE /=; rewrite undup_id. Qed.

(* -------------------------------------------------------------------- *)
Definition useq_choiceMixin (T : choiceType) :=
  [choiceMixin of {useq T} by <:].

Canonical useq_choiceType (T : choiceType) :=
  Eval hnf in ChoiceType {useq T} (useq_choiceMixin T).

Definition useq_countMixin (T : countType) :=
  [countMixin of {useq T} by <:].

Canonical useq_countType (T : countType) :=
  Eval hnf in CountType {useq T} (useq_countMixin T).

Canonical useq_subCountType (T : countType) :=
  Eval hnf in [subCountType of {useq T}].

(* -------------------------------------------------------------------- *)
Module Quotient.
Section Quotient.
  Variable T : choiceType.

  Definition equiv (s1 s2 : {useq T}) := perm_eq s1 s2.

  Lemma equiv_refl: reflexive equiv.
  Proof. by move=> s; apply/perm_eq_refl. Qed.

  Lemma equiv_sym: symmetric equiv.
  Proof. by move=> s1 s2; apply/perm_eq_sym. Qed.

  Lemma equiv_trans: transitive equiv.
  Proof. by move=> s1 s2 s3 h12 h23; apply/(perm_eq_trans h12 h23). Qed.

  Canonical useq_equiv := EquivRel equiv equiv_refl equiv_sym equiv_trans.
  Canonical useq_equiv_direct := defaultEncModRel equiv.

  Definition type := {eq_quot equiv}.
  Definition type_of of phant T := type.

  Notation "{ 'fset' T }" := (@type_of (Phant T)).

  Canonical fset_quotType   := [quotType of type].
  Canonical fset_eqType     := [eqType of type].
  Canonical fset_choiceType := [choiceType of type].
  Canonical fset_eqQuotType := [eqQuotType equiv of type].

  Canonical fset_of_quotType   := [quotType of {fset T}].
  Canonical fset_of_eqType     := [eqType of {fset T}].
  Canonical fset_of_choiceType := [choiceType of {fset T}].
  Canonical fset_of_eqQuotType := [eqQuotType equiv of {fset T}].
End Quotient.

Module Exports.
  Canonical useq_equiv.
  Canonical useq_equiv_direct.

  Canonical fset_quotType.
  Canonical fset_eqType.
  Canonical fset_choiceType.
  Canonical fset_eqQuotType.
  Canonical fset_of_quotType.
  Canonical fset_of_eqType.
  Canonical fset_of_choiceType.
  Canonical fset_of_eqQuotType.

  Notation fsetequiv := equiv.

  Notation "{ 'fset' T }" := (type_of (Phant T)).

  Identity Coercion type_fset_of : type_of >-> type.
End Exports.
End Quotient.

Export Quotient.Exports.

(* -------------------------------------------------------------------- *)
Definition fset (T : choiceType) (s : seq T) : {fset T} :=
  \pi_{fset T} [useq s].

Notation "[ 'fset' 'of' s ]" := (fset s).

(* -------------------------------------------------------------------- *)
Notation "[ 'fset' ]" := [fset of [::]].
Notation "[ 'fset' x1 ; .. ; xn ]" := [fset of (x1 :: .. [:: xn] ..)].
Notation "[ 'fset' x1 ; .. ; xn & s ]" := [fset of (x1 :: .. (xn :: s) ..)].

(* -------------------------------------------------------------------- *)
Section QuotientTheory.
  Variable T : choiceType.

  Lemma equivfs_def (s1 s2 : {useq T}):
    s1 == s2 %[mod {fset T}] = perm_eq s1 s2.
  Proof. by rewrite eqmodE. Qed.

  Lemma equivfs_seq_def (s1 s2 : seq T):
    reflect (s1 =i s2) ([useq s1] == [useq s2] %[mod {fset T}]).
  Proof.
    rewrite equivfs_def !useqK; apply: (iffP idP).
    + by move/perm_eq_mem=> h x; move: (h x) => {h}; rewrite !mem_undup.
    + move=> h; apply/uniq_perm_eq; rewrite ?undup_uniq //.
      by move=> x; rewrite !mem_undup.
  Qed.

  Lemma equivfs_l (s : seq T): perm_eq (repr [fset of s]) (undup s).
  Proof.
    rewrite /fset /=; rewrite -useqK; move: {s} [useq s] => s.
    by rewrite -equivfs_def reprK.
  Qed.

  Lemma fsetW (P : {fset T} -> Prop):
       (forall (s : seq T), uniq s -> P [fset of s])
    -> forall A, P A.
  Proof. by move=> h; elim/quotW=> s; rewrite [s]useqE; apply/h. Qed.
End QuotientTheory.

(* -------------------------------------------------------------------- *)
Section MemPred.
  Variable T : choiceType.

  Canonical fset_predType :=
    Eval hnf in mkPredType (fun s : {fset T} => mem (repr s)).

  Lemma mem_fsetE (s : {fset T}) : mem s = mem (repr s).
  Proof. by []. Qed.

  Lemma mem_quot_fsetE (s : {useq T}): \pi_{fset T} s =i s.
  Proof. by apply/perm_eq_mem; rewrite -equivfs_def reprK. Qed.

  Lemma in_fset (s : seq T): [fset of s] =i s.
  Proof.
    apply/equivfs_seq_def; rewrite equivfs_def /= 1?undup_id //.
    by apply/(perm_eq_trans (equivfs_l _)).
  Qed.

  Lemma fsetP (A B : {fset T}): (A =i B) <-> (A = B).
  Proof.
    split=> [|->//]; elim/quotW: A=> A; elim/quotW: B=> B /=.
    move=> h; apply/eqP; rewrite equivfs_def; apply/uniq_perm_eq=> //.
    by move=> x; move: (h x); rewrite !mem_fsetE !mem_quot_fsetE.
  Qed.
End MemPred.

(* -------------------------------------------------------------------- *)
Section FSetOpsDef.
  Variable T : choiceType.

  Implicit Types A B : {fset T}.

  Definition fsetU A B := [fset of (repr A) ++ (repr B)].
  Definition fsetI A B := [fset of [seq x <- repr A | x \in B]].
  Definition fsetD A B := [fset of [seq x <- repr A | x \notin B]].
End FSetOpsDef.

(* -------------------------------------------------------------------- *)
Section FSetFinOpsDef.
  Variable T : finType.

  Implicit Types A B : {fset T}.

  Definition fsetT   := [fset of enum T].
  Definition fsetC A := [fset of [seq x <- enum T | x \notin A]].
End FSetFinOpsDef.

Implicit Arguments fsetT [T].

(* -------------------------------------------------------------------- *)
Reserved Notation "~: A" (at level 35, right associativity).

Notation "[ 'fset' : T ]" := (@fsetT T).

Notation "A :|: B" := (fsetU A B) : fset_scope.
Notation "A :&: B" := (fsetI A B) : fset_scope.
Notation "A :\: B" := (fsetD A B) : fset_scope.
Notation "~: A"    := (fsetC A  ) : fset_scope.

Local Open Scope fset_scope.

(* -------------------------------------------------------------------- *)
Local Notation inE := (in_fset, in_nil, mem_cat, mem_filter, inE).

(* -------------------------------------------------------------------- *)
Section FSetOpsTheory.
  Variable T : choiceType.

  Implicit Types x y : T.
  Implicit Types A B : {fset T}.

  (* ------------------------------------------------------------------ *)
  Lemma in_fset0 x: (x \in [fset]) = false.
  Proof. by rewrite in_fset in_nil. Qed.

  Lemma in_fset1 x y: (x \in [fset y]) = (x == y).
  Proof. by rewrite in_fset mem_seq1. Qed.

  Lemma in_fsetU x A B: (x \in A :|: B) = (x \in A) || (x \in B).
  Proof. by rewrite in_fset mem_cat. Qed.

  Lemma in_fsetI x A B: (x \in A :&: B) = (x \in A) && (x \in B).
  Proof. by rewrite in_fset mem_filter andbC. Qed.

  Lemma in_fsetD x A B: (x \in A :\: B) = (x \in A) && (x \notin B).
  Proof. by rewrite in_fset mem_filter andbC. Qed.

  (* ------------------------------------------------------------------ *)
  Lemma fsetUP x A B : reflect (x \in A \/ x \in B) (x \in A :|: B).
  Proof. by rewrite in_fsetU; apply/orP. Qed.

  Lemma fsetIP x A B : reflect (x \in A /\ x \in B) (x \in A :&: B).
  Proof. by rewrite in_fsetI; apply/andP. Qed.

  Lemma fsetDP x A B : reflect (x \in A /\ x \notin B) (x \in A :\: B).
  Proof. by rewrite in_fsetD; apply/andP. Qed.

  (* ------------------------------------------------------------------ *)
  Lemma fsetUC A B : A :|: B = B :|: A.
  Proof. by apply/fsetP => x; rewrite !inE orbC. Qed.

  Lemma fset0U A : [fset] :|: A = A.
  Proof. by apply/fsetP => x; rewrite !inE orFb. Qed.

  Lemma fsetU0 A : A :|: [fset] = A.
  Proof. by rewrite fsetUC fset0U. Qed.

  Lemma fsetUA A B C : A :|: (B :|: C) = A :|: B :|: C.
  Proof. by apply/fsetP => x; rewrite !inE orbA. Qed.

  Lemma fsetUCA A B C : A :|: (B :|: C) = B :|: (A :|: C).
  Proof. by rewrite !fsetUA (fsetUC B). Qed.

  Lemma fsetUAC A B C : A :|: B :|: C = A :|: C :|: B.
  Proof. by rewrite -!fsetUA (fsetUC B). Qed.

  Lemma fsetUACA A B C D : (A :|: B) :|: (C :|: D) = (A :|: C) :|: (B :|: D).
  Proof. by rewrite -!fsetUA (fsetUCA B). Qed.

  Lemma fsetUid A : A :|: A = A.
  Proof. by apply/fsetP=> x; rewrite !inE orbb. Qed.

  Lemma fsetUUl A B C : A :|: B :|: C = (A :|: C) :|: (B :|: C).
  Proof. by rewrite fsetUA !(fsetUAC _ C) -(fsetUA _ C) fsetUid. Qed.

  Lemma fsetUUr A B C : A :|: (B :|: C) = (A :|: B) :|: (A :|: C).
  Proof. by rewrite !(fsetUC A) fsetUUl. Qed.

  (* ------------------------------------------------------------------ *)
  Lemma fsetIC A B : A :&: B = B :&: A.
  Proof. by apply/fsetP => x; rewrite !inE andbC. Qed.

  Lemma fset0I A : [fset] :&: A = [fset].
  Proof. by apply/fsetP => x; rewrite !inE andbF. Qed.

  Lemma fsetI0 A : A :&: [fset] = [fset].
  Proof. by rewrite fsetIC fset0I. Qed.

  Lemma fsetIA A B C : A :&: (B :&: C) = A :&: B :&: C.
  Proof. by apply/fsetP=> x; rewrite !inE andbA. Qed.

  Lemma fsetICA A B C : A :&: (B :&: C) = B :&: (A :&: C).
  Proof. by rewrite !fsetIA (fsetIC A). Qed.

  Lemma fsetIAC A B C : A :&: B :&: C = A :&: C :&: B.
  Proof. by rewrite -!fsetIA (fsetIC B). Qed.

  Lemma fsetIACA A B C D : (A :&: B) :&: (C :&: D) = (A :&: C) :&: (B :&: D).
  Proof. by rewrite -!fsetIA (fsetICA B). Qed.

  Lemma fsetIid A : A :&: A = A.
  Proof. by apply/fsetP=> x; rewrite !inE andbb. Qed.

  Lemma fsetIIl A B C : A :&: B :&: C = (A :&: C) :&: (B :&: C).
  Proof. by rewrite fsetIA !(fsetIAC _ C) -(fsetIA _ C) fsetIid. Qed.

  Lemma fsetIIr A B C : A :&: (B :&: C) = (A :&: B) :&: (A :&: C).
  Proof. by rewrite !(fsetIC A) fsetIIl. Qed.

  (* ------------------------------------------------------------------ *)
  Lemma fsetIUr A B C : A :&: (B :|: C) = (A :&: B) :|: (A :&: C).
  Proof. by apply/fsetP=> x; rewrite !inE andb_orl. Qed.

  Lemma fsetIUl A B C : (A :|: B) :&: C = (A :&: C) :|: (B :&: C).
  Proof. by apply/fsetP=> x; rewrite !inE andb_orr. Qed.

  Lemma fsetUIr A B C : A :|: (B :&: C) = (A :|: B) :&: (A :|: C).
  Proof. by apply/fsetP=> x; rewrite !inE orb_andr. Qed.

  Lemma fsetUIl A B C : (A :&: B) :|: C = (A :|: C) :&: (B :|: C).
  Proof. by apply/fsetP=> x; rewrite !inE orb_andl. Qed.

  Lemma fsetUK A B : (A :|: B) :&: A = A.
  Proof. by apply/fsetP=> x; rewrite !inE orbC orKb. Qed.

  Lemma fsetKU A B : A :&: (B :|: A) = A.
  Proof. by apply/fsetP=> x; rewrite !inE orbC orbK. Qed.

  Lemma fsetIK A B : (A :&: B) :|: A = A.
  Proof. by apply/fsetP=> x; rewrite !inE andbC andbK. Qed.

  Lemma fsetKI A B : A :|: (B :&: A) = A.
  Proof. by apply/fsetP=> x; rewrite !inE andbC andKb. Qed.

  (* ------------------------------------------------------------------ *)
  Lemma setD0 A : A :\: [fset] = A.
  Proof. by apply/fsetP=> x; rewrite !inE. Qed.
  
  Lemma fset0D A : [fset] :\: A = [fset].
  Proof. by apply/fsetP=> x; rewrite !inE andbF. Qed.
  
  Lemma fsetDv A : A :\: A = [fset].
  Proof. by apply/fsetP=> x; rewrite !inE andNb. Qed.
  
  Lemma fsetID A B : A :&: B :|: A :\: B = A.
  Proof. by apply/fsetP=> x; rewrite !inE -andb_orl orbN. Qed.
  
  Lemma fsetDUl A B C : (A :|: B) :\: C = (A :\: C) :|: (B :\: C).
  Proof. by apply/fsetP=> x; rewrite !inE -andb_orr. Qed.
  
  Lemma fsetDUr A B C : A :\: (B :|: C) = (A :\: B) :&: (A :\: C).
  Proof. by apply/fsetP=> x; rewrite !inE andbACA andbb orbC negb_or. Qed.
  
  Lemma fsetDIl A B C : (A :&: B) :\: C = (A :\: C) :&: (B :\: C).
  Proof. by apply/fsetP=> x; rewrite !inE andbACA andbb. Qed.

  Lemma fsetIDA A B C : A :&: (B :\: C) = (A :&: B) :\: C.
  Proof. by apply/fsetP=> x; rewrite !inE !andbA. Qed.
  
  Lemma fsetIDAC A B C : (A :\: B) :&: C = (A :&: C) :\: B.
  Proof. by apply/fsetP=> x; rewrite !inE andbCA. Qed.
  
  Lemma fsetDIr A B C : A :\: (B :&: C) = (A :\: B) :|: (A :\: C).
  Proof. by apply/fsetP=> x; rewrite !inE -andb_orl orbC negb_and. Qed.
 
  Lemma fsetDDl A B C : (A :\: B) :\: C = A :\: (B :|: C).
  Proof. by apply/fsetP=> x; rewrite !inE orbC !negb_or !andbA. Qed.
  
  Lemma fsetDDr A B C : A :\: (B :\: C) = (A :\: B) :|: (A :&: C).
  Proof. by apply/fsetP=> x; rewrite !inE -andb_orl orbC negb_and negbK. Qed.
End FSetOpsTheory.

(* -------------------------------------------------------------------- *)
Section FSetFinOpsTheory.
  Variable T : finType.

  Implicit Types x y : T.
  Implicit Types A B : {fset T}.

  (* ------------------------------------------------------------------ *)
  Lemma in_fsetT (x : T): x \in fsetT.
  Proof. by rewrite in_fset mem_enum. Qed.

  Lemma in_fsetC A x: (x \in ~: A) = (x \notin A).
  Proof. by rewrite inE mem_filter mem_enum andbT. Qed.

  Local Notation inE := (in_fsetT, in_fsetC, inE).

  (* ------------------------------------------------------------------ *)
  Lemma fsetTU A : fsetT :|: A = fsetT.
  Proof. by apply/fsetP => x; rewrite !inE orTb. Qed.

  Lemma fsetUT A : A :|: fsetT = fsetT.
  Proof. by rewrite fsetUC fsetTU. Qed.

  (* ------------------------------------------------------------------ *)
  Lemma fsetCP x A : reflect (~ x \in A) (x \in ~: A).
  Proof. by rewrite !inE; exact: negP. Qed.

  (* ------------------------------------------------------------------ *)
  Lemma fsetTI A : fsetT :&: A = A.
  Proof. by apply/fsetP => x; rewrite !inE andbT. Qed.

  Lemma fsetIT A : A :&: fsetT = A.
  Proof. by rewrite fsetIC fsetTI. Qed.

  (* ------------------------------------------------------------------ *)
  Lemma fsetCK : involutive (@fsetC T).
  Proof. by move=> A; apply/fsetP=> x; rewrite !inE negbK. Qed.

  Lemma fsetC_inj : injective (@fsetC T).
  Proof. exact: can_inj fsetCK. Qed.

  Lemma fsetDE A B : A :\: B = A :&: ~: B.
  Proof. by apply/fsetP => x; rewrite !inE andbC. Qed.

  Lemma fsetDT A : A :\: fsetT = [fset].
  Proof. by apply/fsetP=> x; rewrite !inE. Qed.
  
  Lemma fsetTD A : fsetT :\: A = ~: A.
  Proof. by apply/fsetP=> x; rewrite !inE andbT. Qed.

  Lemma fsetCU A B : ~: (A :|: B) = ~: A :&: ~: B.
  Proof. by apply/fsetP=> x; rewrite !inE negb_or andbC. Qed.

  Lemma fsetCI A B : ~: (A :&: B) = ~: A :|: ~: B.
  Proof. by apply/fsetP=> x; rewrite !inE negb_and orbC. Qed.

  Lemma fsetUCr A : A :|: ~: A = fsetT.
  Proof. by apply/fsetP=> x; rewrite !inE orbN. Qed.

  Lemma fsetICr A : A :&: ~: A = [fset].
  Proof. by apply/fsetP=> x; rewrite !inE andNb. Qed.

  Lemma fsetC0 : ~: [fset] = [fset: T].
  Proof. by apply/fsetP=> x; rewrite !inE. Qed.

  Lemma fsetCT : ~: [fset: T] = [fset].
  Proof. by rewrite -fsetC0 fsetCK. Qed.
  
  Lemma fsetCD A B : ~: (A :\: B) = ~: A :|: B.
  Proof. by rewrite !fsetDE fsetCI fsetCK. Qed.
End FSetFinOpsTheory.

(* -------------------------------------------------------------------- *)
Section Card.
  Variable T : choiceType.

  Implicit Types x y : T.
  Implicit Types A B : {fset T}.

  Definition card A := size (repr A).

  Lemma pi_card: {mono \pi_{fset T} : A / size (usval A) >-> card A}.
  Proof. by move=> A; rewrite [A]useqE /card (perm_eq_size (equivfs_l _)). Qed.

  Canonical pi_card_mono := PiMono1 pi_card.
End Card.

(* -------------------------------------------------------------------- *)
Notation "#|< A >|" := (card A)
  (at level 0, format "#|<  A  >|") : fset_scope.

(* -------------------------------------------------------------------- *)
Section CardTheory.
  Variable T : choiceType.

  Implicit Types x y : T.
  Implicit Types A B : {fset T}.

  (* ------------------------------------------------------------------ *)
  Lemma fcard0: #|<[fset] : {fset T}>| = 0.
  Proof. by rewrite !piE. Qed.

  (* ------------------------------------------------------------------ *)
  Lemma fcardUI A B : #|<A :|: B>| + #|<A :&: B>| = #|<A>| + #|<B>|.
  Proof. Admitted.

  Lemma fcardU A B : #|<A :|: B>| = (#|<A>| + #|<B>| - #|<A :&: B>|)%N.
  Proof. by rewrite -fcardUI addnK. Qed.

  Lemma fcardI A B : #|<A :&: B>| = (#|<A>| + #|<B>| - #|<A :|: B>|)%N.
  Proof. by rewrite -fcardUI addKn. Qed.
End CardTheory.

(* -------------------------------------------------------------------- *)
Section CardFinTheory.
  Variable T : finType.

  Implicit Types x y : T.
  Implicit Types A B : {fset T}.

  (* ------------------------------------------------------------------ *)
  Lemma fcardT: #|<[fset: T]>| = #|T|.
  Proof. by rewrite !piE /= undup_id ?enum_uniq // -cardT. Qed.
End CardFinTheory.

(*
*** Local Variables: ***
*** coq-load-path: ("ssreflect" ".") ***
*** End: ***
 *)

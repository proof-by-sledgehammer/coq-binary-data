From Coq Require Import ssreflect.

From Binary.Util Require Import Notation.
From Binary.Structure Require Import Binary.

Module Bit.

  Inductive Bit := One | Zero.

  Definition neg b   := if b is One then Zero else One.
  Definition and x y := if x is One then y else Zero.
  Definition  or x y := if x is One then One else y.

  Lemma zero_neq_one : Zero <> One. Proof. by discriminate. Qed.
  Lemma neg_zero : neg Zero = One. Proof. by reflexivity. Qed.
  Lemma neg_one  : neg One = Zero. Proof. by reflexivity. Qed.
  Lemma neg_neg x : neg $ neg x = x. Proof. by case: x. Qed.
  Global Hint Resolve neg_neg : core.
  Lemma and_de_morgan x y : and x y = neg $ or (neg x) (neg y).
  Proof. by case: x => /=. Qed.
  Lemma or_de_morgan x y : or x y = neg $ and (neg x) (neg y).
  Proof. by case: x => /=. Qed.
  Lemma and_assoc x y z : and x (and y z) = and (and x y) z.
  Proof. by case: x. Qed.
  Lemma or_assoc x y z : or x (or y z) = or (or x y) z.
  Proof. by case: x. Qed.
  Global Hint Resolve and_assoc : core.
  Global Hint Resolve  or_assoc : core.
  Lemma and_ident x : and x One  = x.    Proof. by case: x. Qed.
  Lemma  or_ident x : or  x Zero = x.    Proof. by case: x. Qed.
  Lemma and_anhil x : and x Zero = Zero. Proof. by case: x. Qed.
  Lemma  or_anhil x : or  x One  = One.  Proof. by case: x. Qed.
  Global Hint Resolve and_ident : core.
  Global Hint Resolve  or_ident : core.
  Global Hint Resolve and_anhil : core.
  Global Hint Resolve  or_anhil : core.
  Lemma and_comm x y : and x y = and y x. Proof. by case: x. Qed.
  Lemma  or_comm x y :  or x y =  or y x. Proof. by case: x. Qed.
  Lemma and_distr x y z : and x ( or y z) =  or (and x y) (and x z).
  Proof. by case: x. Qed.
  Lemma  or_distr x y z :  or x (and y z) = and ( or x y) ( or x z).
  Proof. by case: x. Qed.
  Global Hint Resolve and_distr : core.
  Global Hint Resolve  or_distr : core.
  Lemma and_idemp x : and x x = x. Proof. by case: x. Qed.
  Lemma  or_idemp x :  or x x = x. Proof. by case: x. Qed.
  Global Hint Resolve and_idemp : core.
  Global Hint Resolve  or_idemp : core.
  Lemma and_absorp x y : and x ( or x y) = x. Proof. by case: x. Qed.
  Lemma  or_absorp x y :  or x (and x y) = x. Proof. by case: x. Qed.
  Global Hint Resolve and_absorp : core.
  Global Hint Resolve  or_absorp : core.
  Lemma and_compl x : and x (neg x) = Zero. Proof. by case: x. Qed.
  Lemma  or_compl x :  or x (neg x) = One.  Proof. by case: x. Qed.
  Global Hint Resolve and_compl : core.
  Global Hint Resolve  or_compl : core.

End Bit.

Instance Binary_Bit : Binary.Binary Bit.Bit :=
  { (* Definition *)
    zero := Bit.Zero
  ; one  := Bit.One
  ; inv  := Bit.neg
  ; conj := Bit.and
  ; disj := Bit.or
    (* Laws *)
  ; zero_neq_one   := Bit.zero_neq_one
  ; inv_zero       := Bit.neg_zero
  ; inv_one        := Bit.neg_one
  ; inv_inv        := Bit.neg_neg
  ; conj_de_morgan := Bit.and_de_morgan
  ; disj_de_morgan := Bit.or_de_morgan
  ; conj_assoc     := Bit.and_assoc
  ; disj_assoc     := Bit.or_assoc
  ; conj_comm      := Bit.and_comm
  ; disj_comm      := Bit.or_comm
  ; conj_distr     := Bit.and_distr
  ; disj_distr     := Bit.or_distr
  ; conj_ident     := Bit.and_ident
  ; disj_ident     := Bit.or_ident
  ; conj_anhil     := Bit.and_anhil
  ; disj_anhil     := Bit.or_anhil
  ; conj_idemp     := Bit.and_idemp
  ; disj_idemp     := Bit.or_idemp
  ; conj_absorp    := Bit.and_absorp
  ; disj_absorp    := Bit.or_absorp
  ; conj_compl     := Bit.and_compl
  ; disj_compl     := Bit.or_compl
  }.

From Coq Require Import ssreflect.

From Binary.Util Require Import Notation.
From Binary.Structure Require Import Binary.
From Binary.Data Require Import Bit.

Module Bin := Binary.
Module B   := Bit.

Import Bin.Notations.

Module Octett.

  Record Octett :=
    { bit0 : B.Bit ; bit1 : B.Bit ; bit2 : B.Bit ; bit3 : B.Bit
    ; bit4 : B.Bit ; bit5 : B.Bit ; bit6 : B.Bit ; bit7 : B.Bit }.

  Definition all_zero :=
    {| bit0 := B.Zero ; bit1 := B.Zero ; bit2 := B.Zero ; bit3 := B.Zero
     ; bit4 := B.Zero ; bit5 := B.Zero ; bit6 := B.Zero ; bit7 := B.Zero |}.
  Definition all_one :=
    {| bit0 := B.One ; bit1 := B.One ; bit2 := B.One ; bit3 := B.One
     ; bit4 := B.One ; bit5 := B.One ; bit6 := B.One ; bit7 := B.One |}.

  Definition inv (o : Octett) :=
    {| bit0 := ¬ o.(bit0) ; bit1 := ¬ o.(bit1) ; bit2 := ¬ o.(bit2) ; bit3 := ¬ o.(bit3)
     ; bit4 := ¬ o.(bit4) ; bit5 := ¬ o.(bit5) ; bit6 := ¬ o.(bit6) ; bit7 := ¬ o.(bit7) |}.

  Definition and (o1 o2 : Octett) :=
    {| bit0 := o1.(bit0) & o2.(bit0) ; bit1 := o1.(bit1) & o2.(bit1) ; bit2 := o1.(bit2) & o2.(bit2) ; bit3 := o1.(bit3) & o2.(bit3)
     ; bit4 := o1.(bit4) & o2.(bit4) ; bit5 := o1.(bit5) & o2.(bit5) ; bit6 := o1.(bit6) & o2.(bit6) ; bit7 := o1.(bit7) & o2.(bit7)  |}.
  Definition or (o1 o2 : Octett) :=
    {| bit0 := o1.(bit0) ∥ o2.(bit0) ; bit1 := o1.(bit1) ∥ o2.(bit1) ; bit2 := o1.(bit2) ∥ o2.(bit2) ; bit3 := o1.(bit3) ∥ o2.(bit3)
     ; bit4 := o1.(bit4) ∥ o2.(bit4) ; bit5 := o1.(bit5) ∥ o2.(bit5) ; bit6 := o1.(bit6) ∥ o2.(bit6) ; bit7 := o1.(bit7) ∥ o2.(bit7)  |}.

  Definition shl (o : Octett) (b : B.Bit) : (B.Bit * Octett) :=
    (o.(bit0), {| bit0 := o.(bit1) ; bit1 := o.(bit2) ; bit2 := o.(bit3) ; bit3 := o.(bit4)
                ; bit4 := o.(bit5) ; bit5 := o.(bit6) ; bit6 := o.(bit7) ; bit7 := b |}).
  Definition shr (o : Octett) (b : B.Bit) : (B.Bit * Octett) :=
    (o.(bit7), {| bit0 := b        ; bit1 := o.(bit0) ; bit2 := o.(bit1) ; bit3 := o.(bit2)
                ; bit4 := o.(bit3) ; bit5 := o.(bit4) ; bit6 := o.(bit5) ; bit7 := o.(bit6) |}).

  Definition masked_set (dst src mask : Octett) : Octett :=
    or (and src mask) (and dst (inv mask)).

  Lemma eq_all o1 o2 :
    o1 = o2 <-> o1.(bit0) = o2.(bit0) /\ o1.(bit1) = o2.(bit1) /\ o1.(bit2) = o2.(bit2) /\ o1.(bit3) = o2.(bit3)
            /\ o1.(bit4) = o2.(bit4) /\ o1.(bit5) = o2.(bit5) /\ o1.(bit6) = o2.(bit6) /\ o1.(bit7) = o2.(bit7).
  Proof.
    constructor.
    - repeat constructor ; congruence.
    - case: o1 ; case: o2 => > /=. by do 7 case=> -> ; move=> ->.
  Qed.

  Lemma zero_neq_one : all_zero <> all_one.
  Proof. by discriminate. Qed.
  Lemma inv_zero : inv all_zero = all_one.
  Proof. by reflexivity. Qed.
  Lemma inv_one : inv all_one = all_zero.
  Proof. by reflexivity. Qed.
  Lemma inv_inv o : inv $ inv o = o.
  Proof. apply eq_all. by rewrite /inv /= ?Bit.neg_neg. Qed.
  Lemma and_de_morgan x y : and x y = inv $ or (inv x) (inv y).
  Proof. apply eq_all. by rewrite /or /and /inv /= ?B.and_de_morgan. Qed.
  Lemma or_de_morgan x y : or x y = inv $ and (inv x) (inv y).
  Proof. apply eq_all. by rewrite /or /and /inv /= ?B.or_de_morgan. Qed.
  Lemma and_assoc x y z : and x (and y z) = and (and x y) z.
  Proof. apply eq_all => /=. by repeat rewrite B.and_assoc. Qed.
  Lemma or_assoc x y z : or x (or y z) = or (or x y) z.
  Proof. apply eq_all => /=. by repeat rewrite B.or_assoc. Qed.
  Lemma and_comm x y : and x y = and y x.
  Proof. apply eq_all ; rewrite /and => /=. by repeat constructor ; rewrite B.and_comm. Qed.
  Lemma or_comm x y : or x y = or y x.
  Proof. apply eq_all ; rewrite /or => /=. by repeat constructor ; rewrite B.or_comm. Qed.
  Lemma and_distr x y z : and x (or y z) = or (and x y) (and x z).
  Proof. apply eq_all ; rewrite /or /and => /=. by repeat constructor ; rewrite Bit.and_distr. Qed.
  Lemma or_distr x y z : or x (and y z) = and (or x y) (or x z).
  Proof. apply eq_all ; rewrite /or /and => /=. by repeat constructor ; rewrite Bit.or_distr. Qed.
  Lemma and_ident x : and x all_one = x.
  Proof. apply eq_all ; rewrite /and => /=. by repeat constructor ; rewrite B.and_ident. Qed.
  Lemma or_ident x : or x all_zero = x.
  Proof. apply eq_all ; rewrite /or => /=. by repeat constructor ; rewrite B.or_ident. Qed.
  Lemma and_anhil x : and x all_zero = all_zero.
  Proof. apply eq_all => /=. by repeat rewrite B.and_anhil. Qed.
  Lemma or_anhil x : or x all_one = all_one.
  Proof. apply eq_all => /=. by repeat rewrite B.or_anhil. Qed.
  Lemma and_idemp x : and x x = x.
  Proof. apply eq_all ; rewrite /and => /=. by repeat constructor ; rewrite B.and_idemp. Qed.
  Lemma or_idemp x : or x x = x.
  Proof. apply eq_all ; rewrite /or => /=. by repeat constructor ; rewrite B.or_idemp. Qed.
  Lemma and_absorp x y : and x (or x y) = x.
  Proof. apply eq_all ; rewrite /and /or => /=. by repeat constructor ; rewrite B.and_absorp. Qed.
  Lemma or_absorp x y : or x (and x y) = x.
  Proof. apply eq_all ; rewrite /and /or => /=. by repeat constructor ; rewrite B.or_absorp. Qed.
  Lemma and_compl x : and x (inv x) = all_zero.
  Proof. apply eq_all ; rewrite /and /inv => /=. by repeat constructor ; rewrite B.and_compl. Qed.
  Lemma or_compl x : or x (inv x) = all_one.
  Proof. apply eq_all ; rewrite /or /inv => /=. by repeat constructor ; rewrite B.or_compl. Qed.

End Octett.

Instance Binary_Octett : Bin.Binary Octett.Octett :=
  { (* Definition *)
    zero    := Octett.all_zero
  ; one     := Octett.all_one
  ; inv     := Octett.inv
  ; conj    := Octett.and
  ; disj    := Octett.or
    (* Laws *)
  ; zero_neq_one   := Octett.zero_neq_one
  ; inv_zero       := Octett.inv_zero
  ; inv_one        := Octett.inv_one
  ; inv_inv        := Octett.inv_inv
  ; conj_de_morgan := Octett.and_de_morgan
  ; disj_de_morgan := Octett.or_de_morgan
  ; conj_assoc     := Octett.and_assoc
  ; disj_assoc     := Octett.or_assoc
  ; conj_comm      := Octett.and_comm
  ; disj_comm      := Octett.or_comm
  ; conj_distr     := Octett.and_distr
  ; disj_distr     := Octett.or_distr
  ; conj_ident     := Octett.and_ident
  ; disj_ident     := Octett.or_ident
  ; conj_anhil     := Octett.and_anhil
  ; disj_anhil     := Octett.or_anhil
  ; conj_idemp     := Octett.and_idemp
  ; disj_idemp     := Octett.or_idemp
  ; conj_absorp    := Octett.and_absorp
  ; disj_absorp    := Octett.or_absorp
  ; conj_compl     := Octett.and_compl
  ; disj_compl     := Octett.or_compl
  }.

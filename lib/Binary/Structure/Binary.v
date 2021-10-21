From Binary.Util Require Import Notation.

Module Binary.

  Class Binary (T : Type) :=
    { (* Definition *)
      zero    : T
    ; one     : T
    ; inv     : T -> T
    ; conj    : T -> T -> T
    ; disj    : T -> T -> T
      (* Laws *)
    ; zero_neq_one : zero <> one
    ; inv_zero : inv zero = one
    ; inv_one  : inv one  = zero
    ; inv_inv  : forall x, inv $ inv x = x
    ; conj_de_morgan : forall x y, conj x y = inv $ disj (inv x) (inv y)
    ; disj_de_morgan : forall x y, disj x y = inv $ conj (inv x) (inv y)
    ; conj_assoc : forall x y z, conj x (conj y z) = conj (conj x y) z
    ; disj_assoc : forall x y z, disj x (disj y z) = disj (disj x y) z
    ; conj_comm : forall x y, conj x y = conj y x
    ; disj_comm : forall x y, disj x y = disj y x
    ; conj_distr : forall x y z, conj x (disj y z) = disj (conj x y) (conj x z)
    ; disj_distr : forall x y z, disj x (conj y z) = conj (disj x y) (disj x z)
    ; conj_ident : forall x, conj x one  = x
    ; disj_ident : forall x, disj x zero = x
    ; conj_anhil : forall x, conj x zero = zero
    ; disj_anhil : forall x, disj x one  = one
    ; conj_idemp : forall x, conj x x = x
    ; disj_idemp : forall x, disj x x = x
    ; conj_absorp : forall x y, conj x (disj x y) = x
    ; disj_absorp : forall x y, disj x (conj x y) = x
    ; conj_compl : forall x, conj x (inv x) = zero
    ; disj_compl : forall x, disj x (inv x) = one
    }.

  Module Notatios.

    Notation "⊥" := zero.
    Notation "⊤" := one.
    Notation "¬ b" := (inv b) (at level 5).
    Infix "&" := conj (at level 40).
    Infix "∥" := disj (at level 40).

    Notation "x ⊃ y" := (¬x ∥ y) (at level 40).
    Notation "x ⊕ y" := ((x ∥ y) & ¬(x & y)) (at level 40).
    Notation "x ≡ y" := (¬ (x ⊕ y)) (at level 40).

  End Notatios.
End Binary.

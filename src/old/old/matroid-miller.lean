import data.fintype.basic
import data.finset
import tactic
import finset_extra

noncomputable theory
open_locale classical
open finset

def size{β : Type*} (X: finset β) := ((card X) : ℤ )

#check subtype.val

@[simp] lemma size_subtype{β : Type*} {Y: set β} {X : finset Y} : size (X.image subtype.val)  = size X :=
begin
    unfold size,
    simp only [int.coe_nat_inj'],
    apply card_image_of_injective,
    exact subtype.val_injective
end

universes u v

structure matroid_on (E : Type u) :=
(r : finset E → ℤ)
(R1 : ∀ (X : finset E), 0 ≤ r X ∧ r X ≤ size X)
(R2 : ∀ {X Y : finset E}, X ⊆ Y → r X ≤ r Y)
(R3 : ∀ (X Y : finset E), r (X ∪ Y) + r (X ∩ Y) ≤ r X + r Y)

class matroids (α : Type v) :=
(E : α → Type u)
(to_matroid : Π (M : α), matroid_on (E M))
-- M is the name of the matroid, (E M) is the ground set of the matroid; the function to_matroid maps the name M to the structure of
-- matroid M (i.e. a rank function and proofs of axioms).

-- TOY EXAMPLES ***************************

-- Defines two matroids: a 'true matroid' and a 'false matroid' on the same ground sets (in general, ground sets need not be the same).
--The true matroid is free, false matroid has rank zero ,

namespace hidden
def α : Type := bool
example : α := tt
example : α := ff

inductive my_true_E : Type | A | B | C
def my_false_E : Type := my_true_E

def my_E : α -> Type
| tt := my_true_E
| ff := my_false_E

def my_to_matroid : Π (M : α), matroid_on (my_E M)
| tt := {
  r := (λ X, card X : (finset my_true_E -> ℤ)),
  R1 := sorry,
  R2 := sorry,
  R3 := sorry,
}
| ff := {
  r := (λ X, 0 : (finset my_true_E -> ℤ)),
  R1 := sorry,
  R2 := sorry,
  R3 := sorry,
}

example : matroids bool := {
  E := my_E,
  to_matroid := my_to_matroid,
}

-- the collection of all matroids on a fixed ground set
constant β : Type
instance : matroids (matroid_on β) := {
  E := (λ _, β),
  to_matroid := (λ M, M),
}
end hidden

-- END TOY EXAMPLES ***************************

instance matroid_on.matroids (E : Type u) : matroids (matroid_on E) :=
{ E := λ _, E,
  to_matroid := id }

namespace matroid

variables {α : Type v} [matroids α]
-- Accessor functions for terms that have a matroid representation

def E (M : α) := matroids.E M
--def groundset {M: α} : (set (E M))
def r {M : α} (X : finset (E M)) : ℤ := (matroids.to_matroid M).r X
def R1 (M : α) (X : finset (E M)) : 0 ≤ r X ∧ r X ≤ X.card := (matroids.to_matroid M).R1 X
def R2 (M : α) {X Y : finset (E M)} (h : X ⊆ Y) : r X ≤ r Y := (matroids.to_matroid M).R2 h
def R3 (M : α) (X Y : finset (E M)) : r (X ∪ Y) + r (X ∩ Y) ≤ r X + r Y := (matroids.to_matroid M).R3 X Y

@[simp] lemma r_empty_eq_zero (M : α) : r (∅ : finset (E M)) = 0 := sorry
--by { have h := R1 M ∅, rwa [card_empty, le_zero_iff_eq] at h }

lemma rank_subadditive {M : α} (X Y : finset (E M)) : r (X ∪ Y) ≤ r X + r Y := sorry
--le_trans (nat.le.intro rfl) (R3 M X Y)

lemma r_le_union {M : α} (X Y : finset (E M)) : r X ≤ r (X ∪ Y) :=
by { apply R2 M, apply subset_union_left }

lemma r_le_union_right {M : α} (X Y : finset (E M)) : r Y ≤ r (X ∪ Y) :=
by { rw union_comm, apply r_le_union }


structure submatroid (M : α) :=
(F : set (E M))

-- TOY ********************************

def my_α : Type := unit
def the_unit : unit := ()

inductive my_finite_set : Type | A | B | C
constant my_matroid : matroid_on my_finite_set
def my_instance : matroids my_α := {
  E := (λ x, my_finite_set),
  to_matroid := (λ x, my_matroid)
}

def my_finite_subset : (set my_finite_set)
| my_finite_set.A := true
| my_finite_set.B := true
| my_finite_set.C := false

example : (@submatroid my_α my_instance the_unit) := { F := my_finite_subset }
--submatroid : Π {α : Type u_2} [_inst_1 : matroids α], α → Type u_3
--Type ?m1 -> Type ?m1 + 1
-- END TOY ***************************

@[simp] def raise{β : Type*} {Y: set β} (X : finset Y) := X.image subtype.val

instance submatroid.matroid (M : α) : matroids (submatroid M) :=
{ E := λ (M' : submatroid M), M'.F,
  to_matroid := λ (M' : submatroid M),
  { r := λ (X : finset M'.F), @r _ _ M (X.image subtype.val),
    R1 := λ (X : finset M'.F),
    begin   
        split,
        apply (R1 M (X.image subtype.val)).1,

        apply le_trans ((R1 M _).2),
        apply int.coe_nat_le_coe_nat_of_le,
        apply card_image_le,
        --apply ,
     
    end,
    R2 := λ s₁ s₂ hs, R2 M (image_subset_image hs),
    R3 := λ s₁ s₂, by { rw [image_union, image_inter], apply R3 M, apply subtype.ext, } } }


def delete (M : α) (F : set (E M)) : submatroid M :=
submatroid.mk F

structure matroid_contraction (M : α) :=
(C : finset (E M))

def contract (M : α) (C : finset (E M)) : matroid_contraction M :=
matroid_contraction.mk C

instance matroid_contraction.matroid (M : α) : matroids (matroid_contraction M) :=
{ E := λ M', ↥((↑M'.C : set (E M))ᶜ),
  to_matroid := λ M',
  { r := λ X, r (X.image subtype.val ∪ M'.C) - r M'.C,
    R1 := λ X,
    begin
      let X' := X.image subtype.val,
      split,
      linarith [R2 M (subset_union_right X' M'.C : M'.C ⊆ X' ∪ M'.C)],
     
      have := rank_subadditive X' M'.C,

      calc r (X' ∪ M'.C) - r M'.C ≤ r X'        : by linarith
                             ...  ≤ size X'     : (R1 M X').2
                             ...  = size X      : by simp,
    end,
    R2 := λ X,
    begin
        intros Y hXY,
        let X' := X.image subtype.val,
        let Y' := Y.image subtype.val,
        have : X' ⊆ Y', exact image_subset_image hXY,
        have := R2 M ((union_subset_union_left this) : (X' ∪ M'.C ⊆ Y' ∪ M'.C)),
        linarith,
    end,
    R3 :=
    begin
        intros X Y,
        let X' := X.image subtype.val,
        let Y' := Y.image subtype.val,
        rw [image_union, image_inter],
        have := R3 M (X' ∪ M'.C) (Y' ∪ M'.C),
        simp only [@union_unions _ _ X' Y' _, inter_unions]  at this,
       
        linarith,
        intros x y,
        exact subtype.eq,
    end,
    }
 }

def dual (M : α) [fintype (E M)] : matroid_on (E M) :=
{ r := λ X, r (univ.filter (λ x, x ∉ X)) + X.card - r (univ : finset (E M)),
  R1 := sorry,
  R2 := sorry,
  R3 := sorry }


end matroid

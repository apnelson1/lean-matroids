import data.fintype.basic
import data.finset
import tactic
import finset_extra

noncomputable theory
open_locale classical
open set

universes u v

def size {γ : Type u} (X: set γ) := (sorry : ℤ) -- need to fix this to actually be the size

lemma finsize {γ : Type u} {hfin: fintype γ} (X: set γ) : size X = (fintype.card ↥X : ℤ) := sorry



structure matroid_on (γ : Type u)[fintype γ]  :=

(r : set γ → ℤ)
(R1l : ∀ (X : set γ), 0 ≤ r X)
(R1u : ∀ (X:  set γ), r X ≤ size X)
(R2 : ∀ {X Y : set γ}, X ⊆ Y → r X ≤ r Y)
(R3 : ∀ (X Y : set γ), r (X ∪ Y) + r (X ∩ Y) ≤ r X + r Y)

class matroids (α : Type v)  :=
(type_map : α → Σ (γ : Type u), fintype γ)
(to_matroid : Π (M : α), @matroid_on (type_map M).1 (type_map M).2)
-- M is the name of the matroid and has type α.
-- (γ M) is the 'ground type' of the matroid M;
--the function to_matroid maps the name M to the structure of -- matroid M (i.e. a rank function and proofs of axioms).

instance matroid_on.matroids (γ  : Type u)[h: fintype γ]  : matroids (matroid_on γ) :=
{ type_map := λ (M: matroid_on γ), ⟨γ, h⟩,
  to_matroid := id }

namespace matroid

local attribute [simp] image_union image_inter

variables {α : Type v} [matroids α]
-- Accessor functions for terms that have a matroid representation

def γ (M : α) := (matroids.type_map M).1 -- matroid elements have type γ
def E (M: α) : (set (γ M)) := set.univ  -- E is the ground set viewed as a set, not a type.
def r (M : α) (X : set (γ M) ) : ℤ := (matroids.to_matroid M).r X 
def R1l (M : α) (X : set (γ M)) : 0 ≤ r M X := (matroids.to_matroid M).R1l X
def R1u (M:  α) (X: set (γ M))  : r M X ≤ size X := (matroids.to_matroid M).R1u X
def R2 (M : α) {X Y : set (γ M)} (h : X ⊆ Y) : r M X ≤ r M Y := (matroids.to_matroid M).R2 h
def R3 (M : α) (X Y : set (γ M)) : r M (X ∪ Y) + r M (X ∩ Y) ≤ r M X + r M Y := (matroids.to_matroid M).R3 X Y

@[simp] lemma r_empty_eq_zero (M : α) : r M (∅ : set (γ M)) = 0 :=
begin
    have := R1u M ∅,
    have := R1l M ∅,
    have := finsize (∅ : set (γ M)),
    sorry,
    --simp only [card_empty, int.coe_nat_zero] at this,
    --linarith,    
end
--by { have h := R1 M ∅, rwa [card_empty, le_zero_iff_eq] at h }



lemma rank_subadditive (M : α) (X Y : set (γ M)) : r M (X ∪ Y) ≤ r M X + r M Y := by linarith [R3 M X Y, (R1 M (X ∩ Y)).1]

lemma r_le_union (M : α) (X Y : set (γ M)) : r M X ≤ r M (X ∪ Y) :=
by { apply R2 M, apply subset_union_left }

lemma r_le_union_right (M : α) (X Y : set (γ M)) : r M Y ≤ r M (X ∪ Y) :=
by { rw union_comm, apply r_le_union }


instance coe_subtype_set {α : Type*} {Y: set α} :
    has_coe (set Y) (set α) := ⟨λ X, X.image subtype.val⟩


@[simp] lemma coe_subtype_size {α : Type*} {Y: set α} (X: set Y) :
    size X = size (X: set α) := sorry

@[simp] lemma coe_subtype_union {α: Type*} {Y: set α} (X₁ X₂ : set Y) :
    (((X₁ ∪ X₂ : set Y)) :set α ) = X₁ ∪ X₂ := by apply image_union

@[simp] lemma coe_subtype_inter {α: Type*} {Y: set α} (X₁ X₂ : set Y) :
    (((X₁ ∩ X₂ : set Y)) :set α) = X₁ ∩ X₂ :=
begin
    sorry,
end



structure submatroid (M : α) :=
(F : set (γ M))

--set_option pp.beta true
--set_option pp.universes true
instance submatroid.matroid (M : α) : matroids (submatroid M) :=
{ γ := λ (M' : submatroid M), ↥(M'.F),
  to_matroid := λ (M' : submatroid M),
  { r := λ X, r M X,
    R1 := λ X,
    begin   
        split,       
        apply (R1 M X).1,
        simp only [coe_subtype_size],
        exact (R1 M X).2,
    end,
    R2 := λ X₁ X₂ h, R2 M (image_subset _ h),
    R3 := λ X₁ X₂,
    begin
        convert (R3 M X₁ X₂),
        simp,
        simp,
    end, }}


def delete (M : α) (F : set (γ M)) : submatroid M :=
submatroid.mk F

structure matroid_contraction (M : α) :=
(C : set (γ M))

--def contract (M : α) (C : set (γ M)) : matroid_contraction M :=
--matroid_contraction.mk C

instance matroid_contraction.matroid (M : α) : matroids (matroid_contraction M) :=
{ γ := λ M', ↥((M'.C : set (γ M))ᶜ),
  to_matroid := λ M',
  { r := λ X, r M (X ∪ M'.C) - r M M'.C,
    R1 := λ X,
    begin

      split,
      linarith [R2 M (subset_union_right ↑X M'.C)],
     
      have h1 := rank_subadditive M X M'.C,
      have := (R1 M X).2,
      rw coe_subtype_size X,
      --unfold size,
      linarith,
    end,
    R2 := λ X,
    begin
        intros Y hXY,
        have hXYC: (X ∪ M'.C: set (γ M)) ⊆ (Y ∪ M'.C: set (γ M)),
        {
            apply union_subset_union_left,
            apply image_subset,
            exact hXY,
        },
        linarith [R2 M hXYC],
    end,
    R3 :=
    begin
        intros X Y,
        --rw ← coe_subtype_union,
        suffices : r M (↑(X ∪ Y) ∪ M'.C) + r M (↑(X ∩ Y) ∪ M'.C) ≤ r M (↑X ∪ M'.C) + r M (↑Y ∪ M'.C), by linarith,
       
        
        --calc r M (↑(X ∪ Y) ∪ M'.C) - r M M'.C + (r M (↑(X ∩ Y) ∪ M'.C) - r M M'.C) ≤ r M (↑(X ∪ Y) ∪ M'.C) + (r M (↑(X ∩ Y) ∪ M'.C) - 2*(r M M'.C) : by linarith
        --... = r M (↑X ∪ M'.C) - r M M'.C + (r M (↑Y ∪ M'.C) - r M M'.C) : sorry,
        --... =

        --sorry,
        --exact this,
       
        --{linarith,},
        --rw @image_union (finset (↑(M'.C))ᶜ) () _ _ _ X Y ,
        --sorry,
       
        /-intros X Y,
        let X' := X.image subtype.val,
        let Y' := Y.image subtype.val,
        rw [image_union, image_inter],
        have := R3 M (X' ∪ M'.C) (Y' ∪ M'.C),
        simp only [@union_unions _ _ X' Y' _, inter_unions]  at this,
       
        linarith,
        intros x y,
        exact subtype.eq,-/
    end,
    }
 }

def dual (M : α) [fintype (γ M)] : matroid_on (γ M) :=
{ r := λ X, size X - r M (E M) + r M (Xᶜ),
  R1 :=
  begin
    sorry,
    /-intros X,
    split,
    have h1 : r X ≤ size X := (R1 M X).2,
    have h2 := rank_subadditive M X (Xᶜ),
    have h3 := lambda_conn_nonegative M X,
    --unfold lambda_conn at h3,
   
    calc size X - r (E M) + r Xᶜ = size X - r X + (r X + r Xᶜ - r (E M)) : by linarith
                        ...      ≥ size X - r X                          : by linarith [lambda_conn_nonegative M X]
                        ...      ≥ 0                                     : by linarith [(R1 M X).2],

    linarith[ R2 M ((by simp) :(Xᶜ ⊆ E M))], -/
  end,
  R2 := sorry,
  R3 := sorry }


end matroid

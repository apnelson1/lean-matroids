import data.finset data.set

noncomputable theory
open_locale classical
open finset

variables (E : Type*)[fintype E]

-- infinite matroid where every set has finite rank.

def size (X: set E) := (15 :ℕ)



structure finite_rk_matroid :=
(r : set E → ℕ)
(R1 : ∀ (X : set E), r X ≤ size X)
(R2 : ∀ {X Y : finset E}, X ⊆ Y → r X ≤ r Y)
(R3 : ∀ {X Y : finset E}, r (X ∪ Y) + r (X ∩ Y) ≤ r X + r Y)

def submatroid (M : finite_rk_matroid E) (F : finset E) : finite_rk_matroid (coe F : set E)  :=
{ r := λ s, M.r $ s.image coe,
  R1 := λ s, le_trans (M.R1 _) card_image_le,
  R2 := λ s₁ s₂ hs, M.R2 $ image_subset_image hs,
  R3 := λ s₁ s₂, by { rw [image_union, image_inter], apply M.R3, exact λ _ _, subtype.ext } }


#check (set.univ)

--def deletion (M: finite_rk_matroid E) (D: set E) := submatroid M (λ x : E, (x ∉ D))

def contraction (M: finite_rk_matroid E) (C : finset E) : finite_rk_matroid (coe Cᶜ: set E) :=
{
    r := λ X, M.r ((coe X: finset E) ∪ C)
}
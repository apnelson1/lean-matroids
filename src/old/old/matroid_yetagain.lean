import data.set data.fintype.basic


noncomputable theory
open_locale classical
open finset

variables (α : Type*)[decidable_eq α]

def size {β : Type*} (X: set β) := (0 : ℤ)



structure matroid :=
(E : set α)
{Efin: set.finite E}
(r : set E → ℤ)
(R1a : ∀ (X: set E), r X ≥ 0)
(R1b : ∀ (X : set E), r X ≤ size X)
(R2 : ∀ {X Y : set E }, X ⊆ Y → r X ≤ r Y)
(R3 : ∀ {X Y : set E}, r (X ∪ Y) + r (X ∩ Y) ≤ r X + r Y)

def submatroid (M : matroid α) {F: set α} {hF: F ⊆ M.E} : matroid α :=
{   E := F,
    r := λ s, M.r $ ((by library_search) :),
    R1 := λ s, le_trans (M.R1 _) card_image_le,
    R2 := λ s₁ s₂ hs, M.R2 $ image_subset_image hs,
    R3 := λ s₁ s₂, by { rw [image_union, image_inter], apply M.R3, exact λ _ _, subtype.ext } }




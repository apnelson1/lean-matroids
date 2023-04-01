import boolalg.basic boolalg.examples
import .basic .dual

namespace boolalg


def is_minor {U: boolalg} {E : U} : rankfun (subalg E) → rankfun U → Prop :=
  λ N M, ∃ C, E ∩ C = ⊥ ∧ ∀ X : subalg E, N.r X = M.r (X ∪ C) - M.r C



structure minor_on' (U: boolalg) (M: rankfun U) (E : U) := 
(mat : rankfun (subalg E))
(is_minor : is_minor mat M)


@[simp] instance coe_to_matroid {U : boolalg} {M :rankfun U} {E : U} : has_coe (minor_on' U M E) (rankfun (subalg E)) := {coe := minor_on'.mat}

def corestrict' (U : boolalg) (M : rankfun U) (E : U) : minor_on' U M E :=
let r := M.r, C := Eᶜ in
{
  mat :=
  ⟨
  λ X, M.r (X ∪ C) - M.r C,
  λ X, by {rw sub_nonneg, exact M.R2 C (X ∪ C) (subset_union_right X C)},
  λ X, by linarith [subalg_coe_size X, M.R0 (X ∩ C), M.R3 X C, M.R1 X], 
  λ X Y hXY, by linarith [M.R2 (X ∪ C) (Y ∪ C) (subset_union_subset_left X Y C (subalg_coe_subset hXY))] ,
  λ X Y, by
  {
    suffices : M.r (coe (X ∪ Y) ∪ C) + M.r (coe (X ∩ Y) ∪ C) ≤ M.r (X ∪ C) + M.r (Y ∪ C), by linarith,
    have h := M.R3 (X ∪ C) (Y ∪ C),
    rw [←union_distrib_right, ←union_distrib_union_left] at h, refine h,
  },⟩,
  is_minor := ⟨C, ⟨inter_compl_self E, λ X, rfl⟩⟩, 
}

def restrict' (U : boolalg) (M : rankfun U) (E : U) : minor_on' U M E :=
let r := M.r in
{
  mat := ⟨λ X, M.r X, λ X, M.R0 X , λ X, M.R1 X, λ X Y, M.R2 X Y, λ X Y, M.R3 X Y⟩,
  is_minor := ⟨⊥, ⟨ inter_bot E, λ X, by {simp only [union_bot], linarith [rank_bot M]}⟩⟩,
}

lemma corestrict_corestrict' (U : boolalg) (M : rankfun U) (E F : U) (h : E ⊆ F) :
  corestrict' (subalg F) (corestrict' U M F).mat E = corestrict' U M E

 
end boolalg 
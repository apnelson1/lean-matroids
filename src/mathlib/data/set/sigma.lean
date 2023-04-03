import data.set.lattice
import data.set.sigma
import logic.pairwise

/-! Some lemmas about sets in sigma types -/

open set

namespace sigma

variables {ι : Type*} {α : ι → Type*} {x y : set (Σ i, α i)} {f : ∀ i, set (α i)} {i j : ι}

lemma subset_iff : x ⊆ y ↔ ∀ i, sigma.mk i ⁻¹' x ⊆ sigma.mk i ⁻¹' y :=
⟨λ h i a ha, h ha, λ h ⟨i, a⟩ ha, h i ha⟩

lemma eq_iff_forall_preimage_mk_eq : x = y ↔ ∀ i, sigma.mk i ⁻¹' x = sigma.mk i ⁻¹' y :=
⟨by {rintro rfl, exact λ _, rfl}, λ h, (sigma.subset_iff.mpr (λ i, (h i).subset)).antisymm
  (sigma.subset_iff.mpr (λ i, (h i).symm.subset))⟩

@[simp] lemma preimage_mk_Union_image_mk : sigma.mk j ⁻¹' (⋃ i, sigma.mk i '' f i) = f j :=
begin
  rw [preimage_Union, subset_antisymm_iff, Union_subset_iff],
  refine ⟨λ k, _, subset_Union_of_subset j (by rw preimage_image_eq _ sigma_mk_injective)⟩,
  obtain (rfl | hjk) := eq_or_ne j k,
  { rw preimage_image_eq _ sigma_mk_injective},
  rw preimage_image_sigma_mk_of_ne hjk,
  exact empty_subset _,
end

lemma eq_Union_image_preimage_mk (x : set (Σ i, α i)) : x = ⋃ i, sigma.mk i '' (sigma.mk i ⁻¹' x) :=
by simp [sigma.eq_iff_forall_preimage_mk_eq]

lemma image_preimage_mk_pairwise_disjoint (x : set (Σ i, α i)) :
  pairwise (disjoint on (λ i, sigma.mk i '' (sigma.mk i ⁻¹' x))) :=
begin
  refine λ i j hij s hs hs' a ha, hij _,
  simp only [bot_eq_empty, le_eq_subset, mem_empty_iff_false] at hs hs' ⊢,
  obtain ⟨t,ht,rfl⟩ := hs ha,
  obtain ⟨t', ht', h'⟩ := hs' ha,
  simp only at h',
  rw h'.1,
end

end sigma

lemma equiv.sigma_equiv_prod_sigma_mk {ι α : Type*} {i : ι} :
  equiv.sigma_equiv_prod ι α ∘ sigma.mk i = prod.mk i :=
by ext; simp
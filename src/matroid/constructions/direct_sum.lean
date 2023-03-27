import ..dual
import .uniform 
import algebra.big_operators.finprod

noncomputable theory 

open set function

open_locale classical 
open_locale big_operators

namespace matroid 

section direct_sum 

variables {ι : Type*} {E : ι → Type*} {M : ∀ i, matroid (E i)}
/-- The direct sum of an `ι`-indexed collection of matroids `(M i : matroid E i)`. A set is a base
  if and only if its intersection with each matroid is a base -/ 
def direct_sum (M : ∀ i, matroid (E i)) :
  matroid (Σ i, E i) :=
{ base := λ B, (∀ (i : ι), (M i).base ((sigma.mk i) ⁻¹' B)),
  exists_base' := begin
    choose B hB using λ i, (M i).exists_base,  
    refine ⟨⋃ (i : ι), (sigma.mk i) '' (B i), λ i, _⟩, 
    rw sigma.preimage_mk_Union_image_mk, 
    exact hB i, 
  end,
  base_exchange' := begin
    rintros B₁ B₂ hB₁ hB₂ ⟨j,x⟩ hx, 
    obtain ⟨y,hy,hBy⟩  := (hB₁ j).exchange (hB₂ j) hx, 
    refine ⟨sigma.mk j y, hy, λ i, _⟩, 
    { obtain (rfl | hne) := eq_or_ne i j, 
      { convert hBy, ext, simp},
    convert hB₁ i using 1,
    rw [←union_singleton, preimage_union, preimage_diff], 
    -- ext, 
    convert (union_empty _),
    {ext, simpa using hne},
    convert diff_empty.symm,
    ext, 
    simpa using hne},
  end}

@[simp] lemma direct_sum_base_iff {B : set (Σ i, E i)} :
  (direct_sum M).base B ↔ ∀ i, (M i).base ((sigma.mk i) ⁻¹' B) := 
iff.rfl 

variables [finite ι] [∀ i, finite (E i)]

@[simp] lemma direct_sum_indep_iff {I : set (Σ i, E i)} :
  (direct_sum M).indep I ↔ ∀ i, (M i).indep ((sigma.mk i) ⁻¹' I) :=
begin
  simp_rw [indep_iff_subset_base, sigma.subset_iff, direct_sum_base_iff, preimage_subset_iff, 
    mem_preimage], 
  refine ⟨λ ⟨B, hB, hIB⟩ i, ⟨sigma.mk i ⁻¹' B, hB i, λ a ha, hIB _ _ ha⟩, λ h, _⟩,
  choose! f hf using h, 
  refine ⟨⋃ i, sigma.mk i '' (f i), λ i, _, λ i a ha, mem_Union_of_mem i _⟩, 
  { rw sigma.preimage_mk_Union_image_mk, exact (hf i).1},
  simpa using (hf i).2 a ha, 
end

@[simp] lemma direct_sum_basis_iff {I X : set (Σ i, E i)} : 
  (direct_sum M).basis I X ↔ ∀ i, (M i).basis (sigma.mk i ⁻¹' I) (sigma.mk i ⁻¹' X) :=
begin
  simp_rw [basis_iff, direct_sum_indep_iff],
  refine ⟨λ h i, ⟨h.1 i,preimage_mono h.2.1,λ J hJ hIJ hJX, _⟩, 
          λ h, ⟨λ i, (h i).1,sigma.subset_iff.mpr (λ i, (h i).2.1), λ J hJ hIJ hJX, _⟩⟩,
  { have h' := h.2.2 (I ∪ sigma.mk i '' J) (λ j, _) (subset_union_left _ _) 
      (union_subset h.2.1 (by simpa)), 
    { rwa [h', preimage_union, preimage_image_eq _ sigma_mk_injective, union_eq_right_iff_subset]}, 
    obtain (rfl | hne) := eq_or_ne j i, 
    { rwa [preimage_union, preimage_image_eq _ sigma_mk_injective, 
        union_eq_right_iff_subset.mpr hIJ]},
    rw [preimage_union, preimage_image_sigma_mk_of_ne hne, union_empty], 
    exact h.1 j}, 
  rw sigma.eq_iff_forall_preimage_mk_eq, 
  rw sigma.subset_iff at hIJ hJX,
  exact λ i, (h i).2.2 _ (hJ _) (hIJ _) (hJX _), 
end 

@[simp] lemma direct_sum_r_eq (X : set (Σ i, E i)) : 
  (direct_sum M).r X = ∑ᶠ i, (M i).r (sigma.mk i ⁻¹' X) := 
begin
  obtain ⟨I, hI⟩ := (direct_sum M).exists_basis X, 
  rw [←hI.r, hI.indep.r, sigma.ncard_eq_finsum_ncard_image_preimage_mk _ (to_finite I)], 
  rw [direct_sum_basis_iff] at hI, 
  congr', 
  ext i, 
  rw [←(hI i).r, (hI i).indep.r, ncard_image_of_injective _ sigma_mk_injective], 
end 

end direct_sum

section sum 

variables {ι E₁ E₂ : Type*} {E : ι → Type*} {M₁ : matroid E₁} {M₂ : matroid E₂}

def sum (M₁ : matroid E₁) (M₂ : matroid E₂) : 
  matroid (E₁ ⊕ E₂) := 
{ base := λ B, M₁.base (sum.inl ⁻¹' B) ∧ M₂.base (sum.inr ⁻¹' B),
  exists_base' := 
  begin
    obtain ⟨⟨B₁,hB₁⟩,⟨B₂,hB₂⟩⟩ := ⟨M₁.exists_base, M₂.exists_base⟩, 
    refine ⟨sum.inl '' B₁ ∪ sum.inr '' B₂, _⟩,
    simp only [preimage_union, preimage_inl_image_inr, union_empty, 
      preimage_inr_image_inl, empty_union],
    rw [preimage_image_eq _ (sum.inl_injective), preimage_image_eq _ (sum.inr_injective)], 
    exact ⟨hB₁,hB₂⟩, 
  end,
  base_exchange' := 
  begin
    rintro B B' hB hB' (x | x) hx, 
    { rw [←mem_preimage, preimage_diff] at hx, 
      obtain ⟨y,hy,hBy⟩ := hB.1.exchange hB'.1 hx, 
      rw [←preimage_diff, mem_preimage] at hy, 
      refine ⟨_, hy, by {convert hBy, ext, simp}, _⟩,
      convert hB.2 using 1,
      ext, 
      simp},
    rw [←mem_preimage, preimage_diff] at hx, 
    obtain ⟨y,hy,hBy⟩ := hB.2.exchange hB'.2 hx, 
    rw [←preimage_diff, mem_preimage] at hy, 
    refine ⟨_, hy, _, by {convert hBy, ext, simp}⟩,
    convert hB.1 using 1,
    ext, 
    simp,
  end}

@[simp] lemma sum_base_iff {B : set (E₁ ⊕ E₂)} :
  (M₁.sum M₂).base B ↔ M₁.base (sum.inl ⁻¹' B) ∧ M₂.base (sum.inr ⁻¹' B) :=
iff.rfl 


-- /-- Gluing together of an `ι`-indexed collection of different matroids on the same ground set. 
--   This is a tamer special case of sigma, and is used in the proof of matroid union. -/
-- def copy_sum {E : Type*} (M : ι → matroid E) : matroid (ι × E) := 
--   (direct_sum M).congr_equiv (equiv.sigma_equiv_prod ι E) 

-- @[simp] lemma copy_sum_base_iff {E : Type*} {M : ι → matroid E} {B : set (ι × E)}:
--   (copy_sum M).base B ↔ ∀ i, (M i).base (prod.mk i ⁻¹' B) := 
-- by {simp only [copy_sum, congr_equiv_apply_base, direct_sum_base_iff], congr'}

-- @[simp] lemma copy_sum_indep_iff {E : Type*} [finite ι] [finite E] {M : ι → matroid E} 
-- {I : set (ι × E)}:
--   (copy_sum M).indep I ↔ ∀ i, (M i).indep (prod.mk i ⁻¹' I) := 
-- by {simp only [copy_sum, congr_equiv_apply_indep, direct_sum_indep_iff], congr'}

end sum 

section partition 

variables {ι : Type*} {E : ι → Type*} {rk : ι → ℕ} [finite ι] [∀ i, finite (E i)] 

/-- The direct sum of uniform matroids with prescribed ranks -/
def partition_matroid (E : ι → Type*) [∀ i, finite (E i)] (rk : ι → ℕ) : 
  matroid (Σ i, E i) :=
direct_sum (λ i, unif (E i) (rk i)) 

lemma partition_matroid_base_iff (h_le : ∀ i, rk i ≤ nat.card (E i)) {B : set (Σ i, E i)} :
  (partition_matroid E rk).base B ↔ ∀ i, (sigma.mk i ⁻¹' B).ncard = rk i := 
begin
  simp [partition_matroid], 
  refine ⟨λ h i, _, λ h i, _⟩,
  { specialize h i, 
    rwa [unif_base_iff (h_le i), sigma.ncard_preimage_mk] at h},
  rw [unif_base_iff (h_le i), sigma.ncard_preimage_mk], 
  exact h i, 
end 

@[simp] lemma partition_matroid_indep_iff {I : set (Σ i, E i)} :
  (partition_matroid E rk).indep I ↔ ∀ i, (I ∩ sigma.fst ⁻¹' {i}).ncard ≤ rk i := 
begin
  simp only [partition_matroid, direct_sum_indep_iff, unif_indep_iff], 
  refine forall_congr (λ i, _), 
  rw sigma.ncard_preimage_mk,
end 

@[simp] lemma partition_matroid_r_eq (X : set (Σ i, E i)) :
  (partition_matroid E rk).r X = ∑ᶠ i, min (rk i) (X ∩ sigma.fst ⁻¹' {i}).ncard := 
begin
  simp only [partition_matroid, direct_sum_r_eq, unif_r], 
  apply finsum_congr (λ i, _), 
  rw sigma.ncard_preimage_mk, 
end 

end partition 

end matroid 




import .basic
import ..equiv
import algebra.big_operators.finprod

noncomputable theory 

open set function sigma

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
    rw preimage_mk_Union_image_mk, 
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

lemma eq_union_image_bases_of_direct_sum_base {B : set (Σ i, E i)} (h : (direct_sum M).base B) : 
  ∃ Bs : (∀ i, set (E i)), (B = ⋃ i, (sigma.mk i '' (Bs i))) ∧ (∀ i, (M i).base (Bs i)) := 
⟨λ i, sigma.mk i ⁻¹' B, by rw ←eq_Union_image_preimage_mk B, direct_sum_base_iff.mp h⟩
  
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

lemma eq_union_image_indeps_of_direct_sum_indep {I : set (Σ i, E i)} (h : (direct_sum M).indep I) : 
  ∃ Is : (∀ i, set (E i)), (I = ⋃ i, (sigma.mk i '' (Is i))) ∧ (∀ i, (M i).indep (Is i)) := 
⟨λ i, sigma.mk i ⁻¹' I, by rw ←eq_Union_image_preimage_mk I, direct_sum_indep_iff.mp h⟩

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

/- This proof is a bit of a disaster. -/
@[simp] lemma direct_sum_circuit_iff {C : set (Σ i, E i)} :
  (direct_sum M).circuit C ↔ ∃ i C₀, (M i).circuit C₀ ∧ C = sigma.mk i '' C₀ :=
begin
  refine ⟨λ hC, _,_⟩, 
  { have h_dep : ∃ i, ¬(M i).indep (sigma.mk i ⁻¹' C), 
    { by_contra' h, rw [←direct_sum_indep_iff] at h, exact hC.dep h, }, 
    obtain ⟨i,hi⟩ := h_dep,    
    
    have h_forall : ∀ j ≠ i, sigma.mk j ⁻¹' C = ∅,
    { refine λ j hj, eq_empty_of_forall_not_mem (λ e he, hi _),  
      have hjC : (⟨j,e⟩ : (Σ i, E i)) ∈ C, from he, 
      convert ((direct_sum_indep_iff.mp (hC.diff_singleton_indep hjC)) i).subset rfl.subset using 1,
      rw [preimage_diff, eq_comm], 
      convert diff_empty, 
      convert preimage_image_sigma_mk_of_ne hj.symm {e}, 
      rw [image_singleton]},  
    
    have hC₀ : C = sigma.mk i '' (sigma.mk i ⁻¹' C), 
    { nth_rewrite 0 ←Union_image_preimage_sigma_mk_eq_self C,  
      refine subset_antisymm (Union_subset (λ j, _)) (subset_Union _ i), 
      obtain (rfl | hne) := eq_or_ne j i, 
      { exact subset.rfl},
      rintro x ⟨h,h',rfl⟩, 
      exact (not_mem_empty _ ((h_forall _ hne).subset h')).elim, },
    refine ⟨_,_,_,hC₀⟩, 
    simp_rw [circuit_iff_dep_forall_diff_singleton_indep, direct_sum_indep_iff] at hC ⊢, 
    refine ⟨hi, λ e he, _⟩,    
    convert hC.2 ⟨i,e⟩ he i using 1, 
    ext, 
    simp},
  simp_rw [circuit_iff_dep_forall_diff_singleton_indep, direct_sum_indep_iff, not_forall], 
  rintro ⟨i,C, ⟨hC,hmin⟩, rfl⟩, 
  
  refine ⟨⟨i,by rwa preimage_image_eq _ sigma_mk_injective⟩, _⟩, 
  rintro ⟨j,e⟩ ⟨f,hf,⟨h'⟩⟩ j,     
  rw preimage_diff, 
  obtain (rfl | hne) := eq_or_ne i j, 
  { rw [preimage_image_eq _ sigma_mk_injective], convert hmin f hf, ext, simp},
  convert (M j).empty_indep, 
  rw [preimage_image_sigma_mk_of_ne hne.symm, empty_diff], 
end

@[simp] lemma direct_sum_flat_iff {F : set (Σ i, E i)} :
  (direct_sum M).flat F ↔ ∀ i, (M i).flat (sigma.mk i ⁻¹' F) :=
begin
  simp_rw [flat_iff_forall_circuit, direct_sum_circuit_iff], 
  refine ⟨λ h i C e hC heC hss, h (sigma.mk i '' C) ⟨i,e⟩ ⟨_,_,hC,rfl⟩ ⟨e,heC,rfl⟩ _,λ h C e, _⟩, 
  { simp_rw [diff_singleton_subset_iff, image_subset_iff, ←union_singleton, preimage_union] at 
      ⊢ hss,
    convert hss, 
    ext, 
    simp},
  rintro ⟨i,C₀,hC₀,rfl⟩ ⟨f,hf,rfl⟩ h',  
  refine h i C₀ f hC₀ hf _,
  rintro x ⟨hxC₀,(hne : x ≠ f)⟩,   
  exact h' ⟨⟨_,hxC₀,rfl⟩,by simpa⟩, 
end  

end direct_sum

-- section prod_sum

-- variables {ι E : Type*} [finite ι] [finite E] {M : ι → matroid E}

-- def prod_sum (M : ι → matroid E) : 
--   matroid (ι × E) := 
-- (direct_sum M).congr_equiv (equiv.sigma_equiv_prod ι E)

-- @[simp] lemma prod_sum_base_iff {B : set (ι × E)} :
--   (prod_sum M).base B ↔ ∀ i, (M i).base (prod.mk i ⁻¹' B) := 
-- iff.rfl 

-- @[simp] lemma prod_sum_indep_iff {I : set (ι × E)} :
--   (prod_sum M).indep I ↔ ∀ i, (M i).indep (prod.mk i ⁻¹' I) :=
-- begin
--   convert @congr_equiv_apply_indep _ _ _ _ (equiv.sigma_equiv_prod ι E) (direct_sum M) I,  
--   simp_rw [direct_sum_indep_iff], 
--   convert rfl, 
-- end 

-- @[simp] lemma prod_sum_circuit_iff {C : set (ι × E)} :
--   (prod_sum M).circuit C ↔ ∃ i C₀, (M i).circuit C₀ ∧ C = prod.mk i '' C₀ :=
-- begin
--   set e := equiv.sigma_equiv_prod ι E with he, 
--   convert @congr_equiv_apply_circuit _ _ _ _ e (direct_sum M) C,  
--   simp_rw [direct_sum_circuit_iff, eq_iff_iff, preimage_eq_iff_eq_image e.bijective, image_image], 
--   convert iff.rfl,  
-- end 

-- @[simp] lemma prod_sum_flat_iff {F : set (ι × E)} :
--   (prod_sum M).flat F ↔ ∀ i, (M i).indep (prod.mk i ⁻¹' F) :=
-- begin

-- end 

-- end prod_sum

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
  (partition_matroid E rk).indep I ↔ ∀ i, (I ∩ fst ⁻¹' {i}).ncard ≤ rk i := 
begin
  simp only [partition_matroid, direct_sum_indep_iff, unif_indep_iff], 
  refine forall_congr (λ i, _), 
  rw sigma.ncard_preimage_mk,
end 

@[simp] lemma partition_matroid_r_eq (X : set (Σ i, E i)) :
  (partition_matroid E rk).r X = ∑ᶠ i, min (rk i) (X ∩ fst ⁻¹' {i}).ncard := 
begin
  simp only [partition_matroid, direct_sum_r_eq, unif_r], 
  apply finsum_congr (λ i, _), 
  rw sigma.ncard_preimage_mk, 
end 

lemma partition_one_flat_iff {F : set (Σ i, E i)} :
  (partition_matroid E 1).flat F ↔ ∀ i, (fst ⁻¹' {i} ⊆ F) ∨ (disjoint F (fst ⁻¹' {i})) :=   
begin
  simp only [partition_matroid, pi.one_apply, direct_sum_flat_iff, unif_flat_iff, ncard_preimage_mk, 
    nat.lt_one_iff, ncard_eq_zero], 
  refine forall_congr (λ i, _ ), 
  convert iff.rfl, 
  { simp_rw [eq_univ_iff_forall, eq_iff_iff], 
    exact ⟨λ h x, h (rfl : sigma.fst ⟨i,x⟩ = i), λ h, by {rintro ⟨j,e⟩ (rfl : j = i), exact h _}⟩},
  simp_rw [eq_iff_iff, ←disjoint_iff_inter_eq_empty], 
end   

end partition 

section partition_on

variables {E ι : Type*} [finite E] [finite ι] {f : E → ι} {rks : ι → ℕ}
/-- The partition matroid on ground set `E` induced by a partition `f : E → ι` of the ground set 
  and ranks `rks : ι → ℕ`. -/
def partition_matroid_on (f : E → ι) (rks : ι → ℕ) : 
  matroid E :=
(partition_matroid (λ i, {x // f x = i}) rks).congr_equiv (equiv.sigma_fiber_equiv f)
  
lemma partition_matroid_on_indep_iff {I : set E}: 
  (partition_matroid_on f rks).indep I ↔ ∀ i, (I ∩ f ⁻¹' {i}).ncard ≤ rks i :=
begin
  simp only [partition_matroid_on, congr_equiv_apply_indep, partition_matroid_indep_iff], 
  apply forall_congr (λ i, _), 
  rw [←ncard_image_of_injective _ (equiv.sigma_fiber_equiv f).symm.injective, 
    ←preimage_equiv_eq_image_symm, preimage_inter], 
  convert iff.rfl, 
  ext x, 
  obtain ⟨j, x, rfl⟩ := x, 
  simp
end 

lemma partition_matroid_on_r_eq (X : set E) : 
  (partition_matroid_on f rks).r X = ∑ᶠ i, min (rks i) (X ∩ f ⁻¹' {i}).ncard :=
begin
  simp only [partition_matroid_on, congr_equiv_apply_r, partition_matroid_r_eq], 
  refine finsum_congr (λ i, _ ), 
  rw [←ncard_image_of_injective _ (equiv.sigma_fiber_equiv f).symm.injective, 
    ←preimage_equiv_eq_image_symm, preimage_inter], 
  convert rfl, 
  ext x, 
  obtain ⟨j, x, rfl⟩ := x, 
  simp,
end 



end partition_on

end matroid 




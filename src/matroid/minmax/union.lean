import .inter
import ..constructions.direct_sum
import ..equiv
import algebra.big_operators.finprod

open_locale classical 
open_locale big_operators

open matroid set equiv 


section partitionable 

variables {ι E : Type*} [finite E] [finite ι] {M : ι → matroid E} {I A X : set E}

/-- A set is partitionable with respect to a collection of matroids on `E` if it admits a partition   
  into sets that are independent in these matroids  -/
def partitionable (M : ι → matroid E) (I : set E) : Prop := 
  ∃ f : I → ι, ∀ i, (M i).indep (I ∩ (coe '' (f⁻¹' {i})))

lemma partitionable_iff_is_Union :
  partitionable M I ↔ ∃ J : ι → set E, (I = ⋃ i, J i) ∧ ∀ i, (M i).indep (J i) :=
begin
  split, 
  { rintro ⟨f, hf⟩, 
    refine ⟨_, subset_antisymm (λ x hx, mem_Union_of_mem (f ⟨x,hx⟩) _) (Union_subset _), hf⟩, 
    { exact ⟨hx, by simpa⟩},
    exact λ _, inter_subset_left _ _},
  rintro ⟨J, hIJ, hJ⟩, 
  have h : ∀ (x : I), ∃ i, (x : E) ∈ J i,  
  { intro x,  
    obtain ⟨J,⟨i,rfl⟩,hxi⟩ :=  (hIJ.subset x.2), 
    exact ⟨i, hxi⟩},
  choose f hf using h, 
  refine ⟨f, λ i, (hJ i).subset _⟩,
  rintro x ⟨hxI, ⟨x,h,rfl⟩⟩, 
  convert hf x,
  rw eq_comm, 
  exact h,   
end  

lemma partitionable_ub {M : ι → matroid E} {I : set E} (X : set E) (h : partitionable M I) :
  I.ncard ≤ ∑ᶠ i, (M i).r X + Xᶜ.ncard := 
begin
  rw [←ncard_inter_add_ncard_diff_eq_ncard I X], 
  refine add_le_add _ 
    (ncard_le_of_subset (by {rw compl_eq_univ_diff, exact diff_subset_diff_left (subset_univ _)})),

  obtain ⟨J, rfl, hJ⟩ := partitionable_iff_is_Union.mp h, 
  rw [Union_inter], 
  refine (ncard_Union_le _ (λ _, to_finite _)).trans _, 
  refine finsum_le_finsum (to_finite _) (to_finite _) (λ i, _), 
  rw [←((hJ i).inter_right _).r], 
  apply r_inter_right_le_r, 
end 

theorem matroid_union (M : ι → matroid E) : 
  ∃ I X, partitionable M I ∧ I.ncard = ∑ᶠ i, (M i).r X + Xᶜ.ncard := 
begin
  suffices h : ∃ I X : set E, partitionable M I ∧ ∑ᶠ i, (M i).r Xᶜ + X.ncard ≤ I.ncard,   
  { obtain ⟨I, X, hI, hle⟩ := h, 
    refine ⟨I, Xᶜ, hI, _⟩, 
    rw compl_compl, 
    refine hle.antisymm' _,  
    have := (partitionable_ub Xᶜ hI),
    rwa compl_compl at this},

  set M₁ := (direct_sum M).congr_equiv (sigma_equiv_prod ι E) with hM₁, 
  set M₂ := (partition_matroid (λ (e : E), ι) 1).congr_equiv 
    ((sigma_equiv_prod E ι).trans (prod_comm _ _)) with hM₂, 
  
  obtain ⟨I,X, hI₁,hI₂, hIX, hF⟩ := exists_common_ind_with_flat_right M₁ M₂, 

  simp only [congr_equiv_apply_flat, equiv.coe_trans, coe_prod_comm, preimage_compl, 
    partition_one_flat_iff] at hF, 

  simp_rw [← disjoint_compl_left_iff_subset, compl_compl, disjoint_compl_left_iff_subset] at hF, 

  refine ⟨prod.snd '' I, prod.snd '' Xᶜ, _, _⟩, 
  { rw partitionable_iff_is_Union, 
    refine ⟨λ i, prod.snd '' (I ∩ (prod.fst ⁻¹' {i})), _, λ i, _⟩,
    { rw [←image_Union, ←inter_Union, ←bUnion_univ, bUnion_preimage_singleton, preimage_univ, 
      inter_univ]},
    simp only [congr_equiv_apply_indep, direct_sum_indep_iff] at hI₁,
    convert hI₁ i, ext, simp},  
  
  have hI : (prod.snd '' I).ncard = I.ncard,
  { refine ncard_image_of_inj_on _,
    rintro ⟨i₁,e⟩ h₁ ⟨i₂,e'⟩ h₂ (rfl : e = e'),
    simp only [prod.mk.inj_iff, eq_self_iff_true, and_true], 
    simp only [congr_equiv_apply_indep, equiv.coe_trans, coe_prod_comm, partition_matroid_indep_iff,
      pi.one_apply, ncard_le_one_iff, mem_inter_iff, mem_preimage, function.comp_app,   
      sigma_equiv_prod_apply, prod.swap_prod_mk, mem_singleton_iff, and_imp, sigma.forall] at hI₂, 
    simpa using (@hI₂ e e i₂ ⟨e,i₁⟩ h₂ rfl h₁ rfl).symm},

  rw hI, 
  refine le_of_le_of_eq (add_le_add (le_of_eq _) _) hIX.symm, 
  
  { simp only [congr_equiv_apply_r, direct_sum_r_eq], 
    convert rfl, ext i, convert rfl, ext e, 
    simp only [mem_compl_iff, mem_image, prod.exists, exists_eq_right, not_exists_not, 
      mem_preimage, sigma_equiv_prod_apply], 
    refine ⟨λ h, h _, λ hie x, _⟩,  
    obtain (hdj | hss) := hF e,
    { exact (@disjoint.ne_of_mem _ _ _ hdj ⟨e,i⟩ ⟨e,i⟩ (by simpa) rfl rfl).elim},
    exact @hss ⟨e,x⟩ rfl},
  
  simp only [congr_equiv_apply_r, equiv.coe_trans, coe_prod_comm, preimage_compl, 
    partition_matroid_r_eq, pi.one_apply, ←finsum_mem_one], 

  nth_rewrite_rhs 0 ←finsum_mem_univ, 
  refine (finsum_mem_le_finsum_mem (to_finite _) (to_finite _) _).trans 
    (finsum_le_finsum_of_subset (subset_univ (prod.snd '' Xᶜ)) (to_finite _)), 
  
  rintro i ⟨⟨x1,x2⟩,hx, rfl⟩, 
  simp only [mem_inter_iff, mem_compl_iff, mem_preimage, function.comp_app, 
    sigma_equiv_prod_apply, prod.swap_prod_mk, mem_singleton_iff, le_min_iff, le_refl, true_and], 
  
  
  conv_rhs {congr, funext, rw finsum_eq_if,  },
  
  rw ←finsum_mem_univ, 
  
  refine le_trans _ (mem_le_finsum (mem_univ ((sigma_equiv_prod _ _).symm ⟨x2,x1⟩)) 
    (to_finite _)), 
  
  rw [sigma_equiv_prod_symm_apply, if_pos], 
  simp only [eq_self_iff_true, and_true], 
  rwa mem_compl_iff at hx, 
end 












-- example (M : ι → matroid E) : false := 
-- begin
  
  
--   -- set M₁ := copy_sum M with hM₁, 
--   -- set M₁ := (matroid.sigma M).congr_equiv (sigma_equiv_prod ι E) with hM₁, 
--   -- set one_unif : ∀ E, matroid ι := λ (e : E), unif ι 1,  
--   -- set M₂ := (copy_sum one_unif).congr_equiv (prod_comm _ _), 
--   set M₂ := (direct_sum M).congr_equiv (sigma_equiv_prod ι E), 
--   set M₁ := (partition_matroid (λ (e : E), ι) (λ _, 1)).congr_equiv 
--     ((sigma_equiv_prod E ι).trans (prod_comm _ _)), 

--   have hM₁ : ∀ (I : set (ι × E)), M₁.indep I ↔ ∀ (e : E), (I ∩ (prod.snd ⁻¹' {e})).ncard ≤ 1, 
--   { intro I, 
--     simp only [congr_equiv_apply_indep, equiv.coe_trans, coe_prod_comm, 
--       partition_matroid_indep_iff], 
--     refine forall_congr (λ e, _),
--     convert iff.rfl using 2,
    
--     convert (ncard_image_of_injective _ 
--       ((prod_comm _ _).trans (sigma_equiv_prod E ι).symm).symm.injective),  
--     ext, 
--     simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, symm_trans_apply, prod_comm_symm,
--      symm_symm, sigma_equiv_prod_apply, prod_comm_apply, prod.swap_prod_mk, mem_image, 
--       function.comp_app, sigma.exists], 
--     split, 
--     { rintro ⟨hxI, rfl⟩, use [x.2,x.1], simpa},
--     rintro ⟨a,b,⟨h,rfl⟩,rfl⟩, 
--     exact ⟨h,rfl⟩},

--     obtain ⟨I,X, hI₁,hI₂, hIX⟩ := exists_common_ind M₁ M₂, 


    
  

    



--   -- have hB : ∀ B, M₁.base B ↔ ∀ i, (M i).base 
--   -- set M₁ : matroid (ι × E) := matroid.sigma _, 
-- end 

end partitionable

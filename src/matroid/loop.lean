import .flat 

noncomputable theory
open_locale classical

variables {E : Type*} [finite E] {M M₁ M₂ : matroid E} 
  {I C X Y Z F F₁ F₂ : set E} {e f x y z : E}

open set 

namespace matroid

lemma loop_def : 
  M.loop e ↔ M.circuit {e} :=
iff.rfl 

lemma loop.circuit (he : M.loop e) : 
  M.circuit {e} :=
he

lemma loop.r (he : M.loop e) :
  M.r {e} = 0 :=
begin
 have h := he.circuit.card, 
 rwa [ncard_singleton, self_eq_add_left] at h, 
end 

lemma loop_iff_r :
  M.loop e ↔ M.r {e} = 0 :=
begin
  refine ⟨loop.r, λ h, _⟩, 
  rw [loop_def, circuit_def, ←r_lt_card_iff_dep, h, ncard_singleton],   
  refine ⟨zero_lt_one, λ I hI, _⟩, 
  rw [ssubset_singleton_iff.mp hI], 
  apply empty_indep, 
end  

lemma loop_iff_not_mem_base_forall :
  M.loop e ↔ ∀ B, M.base B → e ∉ B :=
begin
  refine ⟨λ h B hB heB, h.circuit.dep (hB.indep.subset (singleton_subset_iff.mpr heB)),
    λ h, _⟩, 
  refine ⟨λ h_ind, _,λ I hI, _⟩, 
  { obtain ⟨B,hB⟩ := h_ind.exists_base_supset, 
    exact h _ hB.1 (singleton_subset_iff.mp hB.2)},
  convert M.empty_indep, 
  rwa ssubset_singleton_iff at hI, 
end   

lemma loop.dep_of_mem (he : M.loop e) (h : e ∈ X) :
  ¬M.indep X := 
λ hX, he.circuit.dep (hX.subset (singleton_subset_iff.mpr h))

/- TODO : Don't use rank here -/
lemma cl_empty_eq_loops (M : matroid E) : 
  M.cl ∅ = {e | M.loop e} :=
by {ext e, rw [mem_cl, r_empty, insert_emptyc_eq, ←loop_iff_r], refl}

lemma loop_iff_mem_cl_empty :
  M.loop e ↔ e ∈ M.cl ∅ :=
by simp_rw [cl_empty_eq_loops, mem_set_of_eq]
 
lemma loop.not_mem_indep (he : M.loop e) (hI : M.indep I) : 
  e ∉ I :=
λ h, he.dep_of_mem h hI   

lemma indep.nonloop_of_mem (hI : M.indep I) (h : e ∈ I) :
  ¬ M.loop e := 
λ he, (he.not_mem_indep hI) h  
  
lemma indep.disjoint_cl_empty (hI : M.indep I) : 
  disjoint I (M.cl ∅) :=
begin
  rw [cl_empty_eq_loops], 
  by_contra' h, 
  obtain ⟨e,he⟩ := not_disjoint_iff.mp h, 
  exact he.2.not_mem_indep hI he.1, 
end 

lemma loop.eq_of_circuit_mem (he : M.loop e) (hC : M.circuit C) (h : e ∈ C) : 
  C = {e} :=
by rw he.circuit.eq_of_subset_circuit hC (singleton_subset_iff.mpr h)

lemma coloop_def : 
  M.coloop e ↔ ∀ B, M.base B → e ∈ B :=
iff.rfl 

lemma coloop.r_compl_add_one (he : M.coloop e) : 
  M.r {e}ᶜ + 1 = M.rk := 
begin
  obtain ⟨I,hI⟩ := M.exists_basis {e}ᶜ, 
  obtain ⟨B, hIB, hB⟩ := hI.indep.subset_basis_of_subset (subset_univ I), 
  rw [←base_iff_basis_univ] at hB, 
  have heI : e ∉ I, from λ heI, by simpa using hI.subset heI, 
  have hIB' : B = insert e I,
  { refine subset_antisymm _ _, 
    { rw [←union_singleton, ←inter_union_diff B {e}, union_subset_iff], 
      refine ⟨(inter_subset_right _ _).trans (subset_union_right _ _), 
        subset_union_of_subset_left _ _⟩,
      rw hI.eq_of_subset_indep (hB.indep.diff {e}) (subset_diff_singleton hIB heI) _,  
      rw [compl_eq_univ_diff],
      exact diff_subset_diff_left (subset_univ _)},
    exact insert_subset.mpr ⟨he B hB, hIB⟩},  
  subst hIB', 
  rw [←hI.r, hI.indep.r, ←hB.r, hB.indep.r, ncard_insert_of_not_mem heI], 
end   

lemma coloop_iff_r_compl_add_one_eq :
  M.coloop e ↔ M.r {e}ᶜ + 1 = M.rk := 
begin
  refine ⟨coloop.r_compl_add_one, λ h B hB, by_contra (λ h', _)⟩, 
  rw ←subset_compl_singleton_iff at h',
  have hB' := M.r_mono h', 
  rw [hB.r, ←h] at hB', 
  simpa only [add_le_iff_nonpos_right, le_zero_iff, nat.one_ne_zero] using hB', 
end 

lemma coloop_iff_r_compl_lt : 
  M.coloop e ↔ M.r {e}ᶜ < M.rk :=
begin
  refine ⟨λ h, _,λ h, _⟩, 
  { rw ←h.r_compl_add_one, apply lt_add_one, }, 
  have he :insert e ({e}ᶜ : set E) = univ, 
  {ext, simp [em]}, 
  rw [rk, ←he] at h, 
  rw [coloop_iff_r_compl_add_one_eq, eq_comm, rk, ←he, r_insert_eq_add_one_of_r_ne h.ne.symm], 
end  

lemma coloop.coe_r_compl (he : M.coloop e) : 
  (M.r {e}ᶜ : ℤ) = M.rk - 1 :=
by simp [←he.r_compl_add_one]

lemma coloop.not_mem_circuit (he : M.coloop e) (hC : M.circuit C) :
  e ∉ C := 
begin
  intro heC, 
  obtain ⟨B,hB, hCB⟩ := (hC.diff_singleton_indep heC).exists_base_supset, 
  have h := insert_subset.mpr ⟨he _ hB, hCB⟩, 
  rw [insert_diff_singleton, insert_eq_of_mem heC] at h, 
  exact hC.dep (hB.indep.subset h), 
end 


-- lemma loop_iff_rank_zero : 
--   M.loop e ↔ M.r 

end matroid 

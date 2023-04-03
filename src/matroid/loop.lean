import .flat 

/-
  A `loop` of a matroid is a one-element circuit. The set of loops of `M` is equal to `M.cl ∅`, 
  and we prefer this notation instead of `{e | M.loop e}` or similar. 
-/


open_locale classical

variables {E : Type*} [finite E] {M M₁ M₂ : matroid E} 
  {I C X Y Z F F₁ F₂ : set E} {e f x y z : E}

open set 

namespace matroid

lemma loop_iff_mem_cl_empty :
  M.loop e ↔ e ∈ M.cl ∅ :=
iff.rfl 

lemma loop.r (he : M.loop e) :
  M.r {e} = 0 :=
(nat.zero_le _).antisymm' (by {convert M.r_mono (singleton_subset_iff.mpr he), rw [r_cl, r_empty]}) 

lemma loop_iff_r :
  M.loop e ↔ M.r {e} = 0 :=
⟨loop.r, λ h, by rwa [loop_iff_mem_cl_empty, mem_cl, r_empty, insert_emptyc_eq]⟩
   
lemma loop_iff_dep : 
  M.loop e ↔ ¬M.indep {e} :=
by {rw [loop_iff_mem_cl_empty, iff_not_comm, M.empty_indep.not_mem_cl_iff], simp}

lemma nonloop_iff_indep : 
  (¬ M.loop e) ↔ M.indep {e} := 
by rw [not_iff_comm, loop_iff_dep]  

lemma loop_iff_circuit : 
  M.loop e ↔ M.circuit {e} :=
by {simp_rw [loop_iff_dep, circuit_def, ssubset_singleton_iff], simp [empty_indep]}

lemma loop.circuit (he : M.loop e) : 
  M.circuit {e} :=
loop_iff_circuit.mp he 

lemma loop_iff_not_mem_base_forall :
  M.loop e ↔ ∀ B, M.base B → e ∉ B :=
begin
  rw ←not_iff_not, 
  simp_rw [nonloop_iff_indep, not_forall, not_not_mem, ←singleton_subset_iff, exists_prop], 
  refl, 
end   

lemma cl_empty_eq_loops (M : matroid E) : 
  M.cl ∅ = {e | M.loop e} :=
by {simp_rw loop_iff_mem_cl_empty, refl}

lemma loop.mem_cl (he : M.loop e) (X : set E) : 
  e ∈ M.cl X := 
mem_of_mem_of_subset (loop_iff_mem_cl_empty.mp he) (M.cl_mono (empty_subset _)) 

lemma loop.dep_of_mem (he : M.loop e) (h : e ∈ X) :
  ¬M.indep X := 
λ hX, he.circuit.dep (hX.subset (singleton_subset_iff.mpr h))

lemma loop.not_mem_indep (he : M.loop e) (hI : M.indep I) : 
  e ∉ I :=
λ h, he.dep_of_mem h hI   

lemma indep.nonloop_of_mem (hI : M.indep I) (h : e ∈ I) :
  ¬ M.loop e := 
λ he, (he.not_mem_indep hI) h  
  
lemma mem_nonloops_iff_not_loop :
  e ∈ M.nonloops ↔ ¬M.loop e :=
by rw [nonloops, mem_compl_iff, loop_iff_mem_cl_empty]  

lemma indep.disjoint_loops (hI : M.indep I) : 
  disjoint I (M.cl ∅) :=
begin
  rw [cl_empty_eq_loops], 
  by_contra' h, 
  obtain ⟨e,he⟩ := not_disjoint_iff.mp h, 
  exact he.2.not_mem_indep hI he.1, 
end 

lemma nonloop_iff_r :
  ¬M.loop e ↔ M.r {e} = 1 :=
by rw [nonloop_iff_indep, indep_iff_r_eq_card, ncard_singleton]

lemma loop.eq_of_circuit_mem (he : M.loop e) (hC : M.circuit C) (h : e ∈ C) : 
  C = {e} :=
by rw he.circuit.eq_of_subset_circuit hC (singleton_subset_iff.mpr h)

lemma coloop_iff_forall_mem_base : 
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

lemma cl_eq_loops_of_subset (h : X ⊆ M.cl ∅) : 
  M.cl X = M.cl ∅ :=
(cl_subset_cl_of_subset_cl h).antisymm (M.cl_mono (empty_subset _))

lemma r_zero_iff_subset_loops :
  M.r X = 0 ↔ X ⊆ M.cl ∅ :=
begin
  obtain ⟨I, hI⟩ := M.exists_basis X, 
  rw [←hI.r, hI.indep.r, ncard_eq_zero, ←cl_subset_cl_iff_subset_cl, ←hI.cl, 
    cl_subset_cl_iff_subset_cl], 
  refine ⟨λ h, _,λ h, _⟩, 
  { rw h, exact empty_subset _},
  have := disjoint_iff_inter_eq_empty.mp hI.indep.disjoint_loops, 
  rwa inter_eq_left_iff_subset.mpr h at this, 
end   

end matroid 

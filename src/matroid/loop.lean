import .rank

/-
  A `loop` of a matroid is a one-element circuit, or, definitionally, a member of `M.cl ∅`.  
  Thus, the set of loops of `M` is equal to `M.cl ∅`, and we prefer this notation instead of 
  `{e | M.loop e}` or similar. A `nonloop` is simply an element that is not a loop, but we give 
  it a definition for the sake of dot notation. 
-/

open_locale classical

variables {E : Type*} {M M₁ M₂ : matroid E} {I C X Y Z F F₁ F₂ : set E} {e f x y z : E}
    
open set

namespace matroid

/- ### Loops -/

lemma loop_iff_mem_cl_empty : M.loop e ↔ e ∈ M.cl ∅ := iff.rfl 

lemma cl_empty_eq_loops (M : matroid E) : M.cl ∅ = {e | M.loop e} := rfl 

lemma loop_iff_dep : M.loop e ↔ ¬ M.indep {e} :=
by rw [loop_iff_mem_cl_empty, iff_not_comm, M.empty_indep.not_mem_cl_iff, 
  mem_empty_iff_false, not_false_iff, true_and, insert_emptyc_eq]

lemma loop_iff_circuit : M.loop e ↔ M.circuit {e} := 
begin
  simp_rw [circuit, loop_iff_dep, iff_self_and, ssubset_singleton_iff, forall_eq], 
  exact λ _, M.empty_indep, 
end 

lemma loop_iff_r : M.loop e ↔ M.r {e} = 0 :=
begin
  rw [loop_iff_dep, indep_iff_r_eq_card_of_finite (finite_singleton e), ncard_singleton],
  refine ⟨λ h, nat.eq_zero_of_le_zero (nat.lt_succ_iff.mp _), 
    λ h h', (nat.zero_ne_one (h.symm.trans h'))⟩, 
  convert (M.r_le_card_of_finite (finite_singleton e)).lt_of_ne _,
  { rw ncard_singleton }, 
  rwa ncard_singleton,  
end 

lemma loop_iff_not_mem_base_forall : M.loop e ↔ ∀ B, M.base B → e ∉ B :=
by simp_rw [loop_iff_dep, indep_iff_subset_base, not_exists, not_and, singleton_subset_iff]

lemma loop.circuit (he : M.loop e) : M.circuit {e} := loop_iff_circuit.mp he 

lemma loop.r (he : M.loop e) : M.r {e} = 0 := loop_iff_r.mp he 

lemma loop.dep (he : M.loop e) : ¬ M.indep {e} := loop_iff_dep.mp he 

lemma loop.mem_cl (he : M.loop e) (X : set E) : e ∈ M.cl X :=
M.cl_mono (empty_subset _) he 

lemma loop.mem_flat (he : M.loop e) {F : set E} (hF : M.flat F) : e ∈ F :=
by { have := he.mem_cl F, rwa hF.cl at this }

lemma loop.dep_of_mem (he : M.loop e) (h : e ∈ X) : ¬M.indep X :=
λ hX, he.circuit.dep (hX.subset (singleton_subset_iff.mpr h))

lemma loop.not_mem_indep (he : M.loop e) (hI : M.indep I) : e ∉ I :=
λ h, he.dep_of_mem h hI

lemma loop.eq_of_circuit_mem (he : M.loop e) (hC : M.circuit C) (h : e ∈ C) : C = {e} :=
by rw he.circuit.eq_of_subset_circuit hC (singleton_subset_iff.mpr h)

lemma cocircuit.nonloop_of_mem {K : set E} (hK : M.cocircuit K) (he : e ∈ K) : M.nonloop e := 
λ h, (h.mem_flat hK.compl_hyperplane.flat) he

lemma indep.disjoint_loops (hI : M.indep I) : disjoint I (M.cl ∅) :=
by_contra (λ h, let ⟨e,⟨heI,he⟩⟩ := not_disjoint_iff.mp h in loop.not_mem_indep he hI heI)

lemma indep.eq_empty_of_subset_loops (hI : M.indep I) (h : I ⊆ M.cl ∅) : I = ∅ :=
eq_empty_iff_forall_not_mem.mpr (λ e he, loop.not_mem_indep (h he) hI he) 

lemma cl_eq_loops_of_subset (h : X ⊆ M.cl ∅) : M.cl X = M.cl ∅ :=
(cl_subset_cl_of_subset_cl h).antisymm (M.cl_mono (empty_subset _))

lemma loop.cl (he : M.loop e) : M.cl {e} = M.cl ∅ :=
cl_eq_loops_of_subset (singleton_subset_iff.mpr he)

lemma loop_iff_cl_eq_cl_empty : M.loop e ↔ M.cl {e} = M.cl ∅ :=
⟨λ h, by rw h.cl ,λ h, by { rw [loop_iff_mem_cl_empty, ←h], exact M.mem_cl_self e }⟩

lemma r_eq_zero_iff_forall_loop [finite_rk M] : M.r X = 0 ↔ ∀ e ∈ X, M.loop e :=
begin
  refine ⟨λ h e he, loop_iff_r.mpr ((nat.zero_le _).antisymm' _), λ h, (nat.zero_le _).antisymm' _⟩,
  { rw ←h, exact M.r_mono (singleton_subset_iff.mpr he) },
  have h' := M.r_mono h, 
  rwa [r_cl, r_empty] at h', 
end 

lemma r_eq_zero_iff_subset_loops [finite_rk M] : M.r X = 0 ↔ X ⊆ M.cl ∅ := r_eq_zero_iff_forall_loop

lemma cl_union_eq_cl_of_subset_loops {Y : set E} (hY : Y ⊆ M.cl ∅) (X : set E) :
  M.cl (X ∪ Y) = M.cl X := 
by rw [←cl_union_cl_right_eq_cl_union, cl_eq_loops_of_subset hY, cl_union_cl_right_eq_cl_union, 
    union_empty]

lemma cl_diff_eq_cl_of_subset_loops {Y : set E} (hY : Y ⊆ M.cl ∅) (X : set E) :
  M.cl (X \ Y) = M.cl X := 
by rw [←cl_union_eq_cl_of_subset_loops hY, diff_union_self, cl_union_eq_cl_of_subset_loops hY]

/- ### Nonloops -/

@[simp] lemma not_loop_iff : ¬ M.loop e ↔ M.nonloop e := iff.rfl 

@[simp] lemma not_nonloop_iff : ¬ M.nonloop e ↔ M.loop e := by rw [←not_loop_iff, not_not]

lemma nonloops_eq_compl_cl_empty : M.nonloops = (M.cl ∅)ᶜ := rfl 

@[simp] lemma compl_nonloops_eq_cl_empty : (M.nonloops)ᶜ = M.cl ∅ := 
by rw [nonloops_eq_compl_cl_empty, compl_compl] 

lemma loop_or_nonloop (M : matroid E) (e : E) : M.loop e ∨ M.nonloop e := em _ 

@[simp] lemma indep_singleton : M.indep {e} ↔ M.nonloop e := by rw [nonloop, loop_iff_dep, not_not]

alias indep_singleton ↔ indep.nonloop nonloop.indep

attribute [protected] indep.nonloop nonloop.indep

lemma nonloop_iff_r : M.nonloop e ↔ M.r {e} = 1 :=
by rw [←indep_singleton, indep_iff_r_eq_card_of_finite (finite_singleton e), ncard_singleton]

lemma nonloop.r (he : M.nonloop e) : M.r {e} = 1 := nonloop_iff_r.mp he 

lemma indep.nonloop_of_mem (hI : M.indep I) (h : e ∈ I) : ¬ M.loop e := 
λ he, (he.not_mem_indep hI) h

lemma circuit.nonloop_of_mem_of_one_lt_card (hC : M.circuit C) (h : 1 < C.ncard) (he : e ∈ C) :
  M.nonloop e :=
not_loop_iff.mp (λ hlp, by simpa [hlp.eq_of_circuit_mem hC he] using h)

lemma nonloop_of_not_mem_cl (h : e ∉ M.cl X) : M.nonloop e :=
not_loop_iff.mp (λ he, h (he.mem_cl X))

lemma nonloop.mem_cl_singleton (he : M.nonloop e) (hef : e ∈ M.cl {f}) : f ∈ M.cl {e} :=
begin
  refine (M.loop_or_nonloop f).elim (λ hf, hf.mem_cl _) (λ hf, _), 
  rw [he.indep.mem_cl_iff, mem_singleton_iff], 
  rwa [hf.indep.mem_cl_iff, mem_singleton_iff, eq_comm, pair_comm] at hef, 
end 

lemma nonloop.mem_cl_comm (he : M.nonloop e) (hf : M.nonloop f) : f ∈ M.cl {e} ↔ e ∈ M.cl {f} :=
⟨hf.mem_cl_singleton, he.mem_cl_singleton⟩ 

lemma nonloop.nonloop_of_mem_cl (he : M.nonloop e) (hef : e ∈ M.cl {f}) : M.nonloop f :=
λ hf, he (by rwa [hf.cl] at hef)
  
lemma nonloop.cl_eq_of_mem_cl (he : M.nonloop e) (hef : e ∈ M.cl {f}) : M.cl {e} = M.cl {f} :=
begin
  ext x, 
  obtain (hx | hx) := M.loop_or_nonloop x, 
  { exact ⟨λ _, hx.mem_cl _, λ _, hx.mem_cl _⟩ },
  refine ⟨λ h, _, λ h, he.mem_cl_singleton _⟩,
  { rw [←singleton_subset_iff, ←cl_subset_cl_iff_subset_cl] at *,
    exact h.trans hef },
  have hfx := hx.mem_cl_singleton h, 
  rw [←singleton_subset_iff, ←cl_subset_cl_iff_subset_cl] at *,
  exact hef.trans hfx, 
end 

lemma nonloop.cl_eq_cl_iff_dep (he : M.nonloop e) (hf : M.nonloop f) : 
  M.cl {e} = M.cl {f} ↔ e = f ∨ ¬ M.indep {e,f} := 
begin
  rw [←imp_iff_or_not], 
  refine ⟨λ hef, _, λ h, he.cl_eq_of_mem_cl (by rwa [hf.indep.mem_cl_iff])⟩,
  have hf : f ∈ M.cl {e}, by {rw hef, exact M.mem_cl_self f },
  rw [pair_comm, eq_comm, ←mem_singleton_iff], 
  exact he.indep.mem_cl_iff.mp hf,  
end 

/- ### Coloops -/ 

lemma coloop_iff_forall_mem_base : M.coloop e ↔ ∀ B, M.base B → e ∈ B := iff.rfl

lemma coloop.r_compl_add_one [finite_rk M] (he : M.coloop e) : M.r {e}ᶜ + 1 = M.rk :=
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
      exact diff_subset_diff_left (subset_univ _) },
    exact insert_subset.mpr ⟨he hB, hIB⟩},
  subst hIB',
  rw [←hI.r, hI.indep.r, ←hB.r, hB.indep.r, ncard_insert_of_not_mem heI hI.finite],
end

lemma coloop_iff_r_compl_add_one_eq [finite_rk M] : M.coloop e ↔ M.r {e}ᶜ + 1 = M.rk :=
begin
  refine ⟨coloop.r_compl_add_one, λ h B hB, by_contra (λ h', _)⟩,
  rw ←subset_compl_singleton_iff at h',
  have hB' := M.r_mono h',
  rw [hB.r, ←h] at hB',
  simpa only [add_le_iff_nonpos_right, le_zero_iff, nat.one_ne_zero] using hB',
end

lemma coloop_iff_r_compl_lt [finite_rk M] : M.coloop e ↔ M.r {e}ᶜ < M.rk :=
begin
  refine ⟨λ h, _,λ h, _⟩,
  { rw ←h.r_compl_add_one, apply lt_add_one, },
  have he :insert e ({e}ᶜ : set E) = univ,
  {ext, simp [em]},
  rw [rk, ←he] at h,
  rw [coloop_iff_r_compl_add_one_eq, eq_comm, rk, ←he, r_insert_eq_add_one_of_r_ne h.ne.symm],
end

lemma coloop.coe_r_compl [finite_rk M] (he : M.coloop e) : (M.r {e}ᶜ : ℤ) = M.rk - 1 :=
by simp [←he.r_compl_add_one]

lemma coloop.not_mem_circuit (he : M.coloop e) (hC : M.circuit C) : e ∉ C :=
begin
  intro heC,
  obtain ⟨B,hB, hCB⟩ := (hC.diff_singleton_indep heC).exists_base_supset,
  have h := insert_subset.mpr ⟨he hB, hCB⟩,
  rw [insert_diff_singleton, insert_eq_of_mem heC] at h,
  exact hC.dep (hB.indep.subset h),
end

lemma circuit.not_coloop_of_mem (hC : M.circuit C) (heC : e ∈ C) : ¬M.coloop e :=  
λ h, h.not_mem_circuit hC heC 

end matroid

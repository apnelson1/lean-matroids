import .circuit 

noncomputable theory
open_locale classical
open_locale big_operators

variables {E : Type*} [finite E] {M M₁ M₂ : matroid E} 
  {I X Y Z F F₁ F₂ : set E} {e f x y z : E}

open set 

namespace matroid 

lemma flat_def : 
  M.flat F ↔ ∀ I X, M.basis I F → M.basis I X → X ⊆ F  :=
iff.rfl 

lemma flat.r_insert_of_not_mem (hF : M.flat F) (he : e ∉ F) :
  M.r (insert e F) = M.r F + 1 :=
begin
  suffices h' : M.r F < M.r (insert e F), 
  { rw (nat.lt_iff_add_one_le.mp h').antisymm (M.r_insert_le_add_one F e)},
  obtain ⟨I,hI⟩ := M.exists_basis F, 
  have hnb : ¬ M.basis I (insert e F),  
    from λ hI', he (hF I (insert e F) hI hI' (mem_insert e F)), 
  by_contra' h_le, 
  exact hnb (hI.indep.basis_of_subset_of_r_le (hI.subset.trans (subset_insert _ _)) 
    (h_le.trans_eq hI.r.symm)), 
end 
  
lemma flat_iff_r_lt_r_insert :
  M.flat F ↔ ∀ e ∉ F, M.r F < M.r (insert e F) :=
begin
  refine ⟨λ hF e heF, nat.lt_iff_add_one_le.mpr (hF.r_insert_of_not_mem heF).symm.le,
    λ h, flat_def.mpr (λ I X hIF hIX, _)⟩, 
  by_contra' hXF,
  obtain ⟨e,heX,heF⟩ := not_subset.mp hXF,   
  apply (h e heF).ne, 
  rw [←hIF.r_eq_r_insert, hIX.r_eq_r_insert, insert_eq_of_mem heX, ←hIF.r, ←hIX.r], 
end  

lemma flat.Inter {ι : Type*} (F : ι → set E) (hF : ∀ i, M.flat (F i)) : 
  M.flat (⋂ i, F i) := 
begin
  simp_rw [flat_iff_r_lt_r_insert], 
  by_contra' h, 
  obtain ⟨e, he, hre⟩ := h,  
  rw [mem_Inter, not_forall] at he, 
  obtain ⟨j, hj⟩ := he, 
  have hj' := (hF j).r_insert_of_not_mem hj, 
  rw r_insert_eq_of_r_insert_subset_le (Inter_subset F j) hre at hj',
  simpa using hj', 
end 

lemma flat.inter (hF₁ : M.flat F₁) (hF₂ : M.flat F₂) : 
  M.flat (F₁ ∩ F₂) :=
begin
  rw inter_eq_Inter, 
  refine flat.Inter _ (λ i, _), 
  cases i; assumption,
end

lemma univ_flat (M : matroid E) : 
  M.flat univ :=
flat_iff_r_lt_r_insert.mpr (λ e he, (he (mem_univ e)).elim)

lemma exists_flat_not_mem_of_r_insert_ne (M : matroid E) (h : M.r (insert e X) ≠ M.r X):
  ∃ F, M.flat F ∧ X ⊆ F ∧ e ∉ F :=
begin
  have hr := r_insert_eq_add_one_of_r_ne h, 
  have heX : e ∉ X, 
  { intro heX, rw [insert_eq_of_mem heX] at h, exact h rfl},
  obtain ⟨F, ⟨hXF, hF⟩, hF'⟩ := 
    finite.exists_maximal (λ F, X ⊆ F ∧ M.r F ≤ M.r X) ⟨X, rfl.subset, rfl.le⟩, 
  dsimp only at hF', 
  have heF : e ∉ F, 
  { intro heF, 
    simpa only [add_le_iff_nonpos_right, le_zero_iff, hr, ←(hF.antisymm (M.r_mono hXF))] using 
      M.r_mono (insert_subset.mpr ⟨heF, hXF⟩)},
  refine ⟨F, flat_iff_r_lt_r_insert.mpr (λ f hfF, _), hXF, heF⟩, 
  by_contra' hle, 
  rw hF' (insert f F) ⟨hXF.trans (subset_insert _ _), hle.trans hF⟩ (subset_insert _ _) at hfF,   
  simpa only [mem_insert_iff, eq_self_iff_true, true_or, not_true] using hfF, 
end      

lemma cl_def (M : matroid E) : M.cl X = ⋂₀ {F | M.flat F ∧ X ⊆ F} := rfl 

lemma mem_cl_iff_forall_mem_flat : 
  e ∈ M.cl X ↔ ∀ F, M.flat F → X ⊆ F → e ∈ F :=
by simp_rw [cl_def, mem_sInter, mem_set_of_eq, and_imp]

lemma flat_of_cl (M : matroid E) (X : set E) :
  M.flat (M.cl X) :=
begin
  rw [cl_def, sInter_eq_Inter], 
  refine flat.Inter _ _,
  rintro ⟨F,hF⟩,  
  exact hF.1, 
end 

lemma subset_cl (M : matroid E) (X : set E) :
  X ⊆ M.cl X :=
by simp only [cl_def, subset_sInter_iff, mem_set_of_eq, and_imp, imp_self, implies_true_iff]

lemma mem_cl: 
  e ∈ M.cl X ↔ M.r (insert e X) = M.r X := 
begin
  have hF := M.flat_of_cl X, 
  rw flat_iff_r_lt_r_insert at hF, 
  refine ⟨λ hecl, by_contra (λ hne, _),λ h, by_contra (λ heX, (hF e heX).ne _)⟩, 
  { have hlem : ∃ F, M.flat F ∧ X ⊆ F ∧ e ∉ F, 
    { have hr := r_insert_eq_add_one_of_r_ne hne, 
      have heX : e ∉ X, 
      { intro heX, rw [insert_eq_of_mem heX] at hne, exact hne rfl},
      obtain ⟨F, ⟨hXF, hF⟩, hF'⟩ := 
        finite.exists_maximal (λ F, X ⊆ F ∧ M.r F ≤ M.r X) ⟨X, rfl.subset, rfl.le⟩, 
      dsimp only at hF', 
      have heF : e ∉ F, 
      { intro heF, 
        simpa only [add_le_iff_nonpos_right, le_zero_iff, hr, ←(hF.antisymm (M.r_mono hXF))] using 
          M.r_mono (insert_subset.mpr ⟨heF, hXF⟩)},
      refine ⟨F, flat_iff_r_lt_r_insert.mpr (λ f hfF, _), hXF, heF⟩, 
      by_contra' hle, 
      rw hF' (insert f F) ⟨hXF.trans (subset_insert _ _), hle.trans hF⟩ (subset_insert _ _) at hfF,   
      simpa only [mem_insert_iff, eq_self_iff_true, true_or, not_true] using hfF},
    obtain ⟨F, hF, hXf, heF⟩ := hlem,    
    rw mem_cl_iff_forall_mem_flat at hecl, 
    exact heF (hecl _ hF hXf)},
  rw r_insert_eq_of_r_insert_subset_le (M.subset_cl X) h.le,     
end      

@[simp] lemma r_cl (M : matroid E) (X : set E) : 
  M.r (M.cl X) = M.r X :=
(r_eq_of_r_all_insert_eq (M.subset_cl X) (λ e h, (mem_cl.mp h).symm)).symm

@[simp] lemma cl_cl (M : matroid E) (X : set E) : 
  M.cl (M.cl X) = M.cl X :=
begin
  ext x, 
  simp_rw [mem_cl, r_cl], 
  refine ⟨λ h, (M.r_mono (subset_insert _ _)).antisymm' _, λ h, _⟩, 
  { rw ←h, 
    exact M.r_mono (insert_subset_insert (M.subset_cl _))}, 
  convert (@r_union_eq_of_subset_of_r_eq _ _ M _ _ (M.cl X) (subset_insert x X) h.symm).symm 
    using 1,
  { rw [insert_union, union_eq_right_iff_subset.mpr (M.subset_cl X)]}, 
  rw [union_eq_right_iff_subset.mpr (M.subset_cl X), r_cl], 
end 

lemma cl_le_cl_of_subset (M : matroid E) (h : X ⊆ Y) :
  M.cl X ⊆ M.cl Y :=
sInter_subset_sInter (λ F hF, ⟨hF.1, h.trans hF.2⟩)

lemma cl_mono (M : matroid E) : monotone M.cl := 
  λ _ _, M.cl_le_cl_of_subset

lemma r_insert_eq_add_one_of_not_mem_cl (h : e ∉ M.cl X) : 
  M.r (insert e X) = M.r X + 1 :=
r_insert_eq_add_one_of_r_ne (h ∘ mem_cl.mpr)
 
lemma not_mem_cl_of_r_insert_gt (h : M.r X < M.r (insert e X)) : 
  e ∉ M.cl X := 
h.ne.symm ∘ mem_cl.mp

lemma not_mem_cl_iff_r_insert_eq_add_one  : 
  e ∉ M.cl X ↔ M.r (insert e X) = M.r X + 1 :=
⟨r_insert_eq_add_one_of_not_mem_cl, λ h, not_mem_cl_of_r_insert_gt (by {rw h, apply lt_add_one})⟩ 

lemma mem_cl_insert (he : e ∉ M.cl X) (hef : e ∈ M.cl (insert f X)) : 
  f ∈ M.cl (insert e X) :=
begin
  by_contra hf, 
  rw not_mem_cl_iff_r_insert_eq_add_one at he hf, 
  rw [mem_cl, insert_comm, hf, he] at hef, 
  have h := M.r_insert_le_add_one X f,
  rw ←hef at h, 
  exact (lt_add_one _).not_le h, 
end  


end matroid 
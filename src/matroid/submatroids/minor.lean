import .matroid_in

open_locale classical 
noncomputable theory

open matroid set 

variables {E α : Type*} [finite E] [finite α] {I C B X Y : set α} {M : matroid_in α}

namespace matroid_in 

section minor

def contract (M : matroid_in α) (C : set α) : matroid_in α := 
{ E := M.E \ C,
  carrier := (M : matroid α) ⟋ C,
  support := 
  begin
    simp only [project_cl_eq, empty_union, diff_eq_compl_inter, compl_inter, compl_compl], 
    exact union_subset (M.carrier.subset_cl C) 
      (M.support.trans (M.carrier.cl_mono (empty_subset _))),
  end }

def delete (M : matroid_in α) (D : set α) : matroid_in α := 
{ E := M.E \ D,
  carrier := (M : matroid α) ⟍ D,
  support := 
  begin
    rw [loopify_cl_eq, empty_diff, compl_subset_comm, compl_union, diff_eq_compl_inter, 
      subset_inter_iff], 
    simp only [inter_subset_right, true_and],
    rw [←compl_union, compl_subset_comm], 
    exact subset_union_of_subset_left M.compl_ground_subset_loops_coe _, 
  end }

instance {α : Type*} [finite α] : has_con (matroid_in α) (set α) := ⟨matroid_in.contract⟩  
instance {α : Type*} [finite α] : has_del (matroid_in α) (set α) := ⟨matroid_in.delete⟩
instance {α : Type*} [finite α] : has_con (matroid_in α) α := ⟨λ M e, M.contract {e}⟩  
instance {α : Type*} [finite α] : has_del (matroid_in α) α := ⟨λ M e, M.delete {e}⟩  

-- reserve infix ` ⟋ `:85 
-- reserve infix ` ⟍ `:85 

-- notation (name := matroid_in_contract) M₁ ⟋  X := matroid_in.contract M₁ X 
-- notation (name := matroid_in_delete) M₁ ⟍ X := matroid_in.delete M₁ X 

@[simp] lemma contract_coe (M : matroid_in α) (C : set α) : 
  ((M ⟋ C : matroid_in α) : matroid α) = (M : matroid α) ⟋ C := rfl 

@[simp] lemma contract_elem (M : matroid_in α) (e : α) : M ⟋ e = M ⟋ ({e} : set α) := rfl  

@[simp] lemma contract_ground (M : matroid_in α) (C : set α): (M ⟋ C).E = M.E \ C := rfl 

@[simp] lemma delete_coe (M : matroid_in α) (D : set α) : 
  ((M ⟍ D : matroid_in α) : matroid α) = (M : matroid α) ⟍ D := rfl 

@[simp] lemma delete_elem (M : matroid_in α) (e : α) : M ⟍ e = M ⟍ ({e} : set α) := rfl 

@[simp] lemma delete_ground (M : matroid_in α) (D : set α): (M ⟍ D).E = M.E \ D := rfl 

@[simp] lemma contract_contract (M : matroid_in α) (C₁ C₂ : set α) : M ⟋ C₁ ⟋ C₂ = M ⟋ (C₁ ∪ C₂) :=
eq_of_coe_eq_coe (by simp [diff_diff]) (by simp)
  
lemma contract_comm (M : matroid_in α) (C₁ C₂ : set α) : M ⟋ C₁ ⟋ C₂ = M ⟋ C₂ ⟋ C₁ :=
by rw [contract_contract, contract_contract, union_comm]
 
@[simp] lemma delete_delete (M : matroid_in α) (D₁ D₂ : set α) : M ⟍ D₁ ⟍ D₂ = M ⟍ (D₁ ∪ D₂) :=
eq_of_coe_eq_coe (by simp [diff_diff]) (by simp)

lemma delete_comm (M : matroid_in α) (D₁ D₂ : set α) : M ⟍ D₁ ⟍ D₂ = M ⟍ D₂ ⟍ D₁ :=
by rw [delete_delete, delete_delete, union_comm]

lemma contract_delete_comm (M : matroid_in α) {C D : set α} (hCD : disjoint C D) : 
  M ⟋ C ⟍ D = M ⟍ D ⟋ C := 
eq_of_coe_eq_coe (by simp [diff_diff_comm]) (by simp [project_loopify_comm _ hCD]) 

lemma contract_indep_iff (hI : M.indep I) : 
  (M ⟋ I).indep X ↔ M.indep (X ∪ I) ∧ X ⊆ (M.E \ I) :=  
begin
  rw [indep_iff_coe, contract_coe, hI.project_indep_iff, and_comm, indep_iff_coe, subset_diff] at *, 
  exact ⟨λ h, ⟨h.1, indep.subset_ground (h.1.subset (subset_union_left _ _)),h.2⟩,
    λ h, ⟨h.1, h.2.2⟩⟩, 
end 

lemma delete_indep_iff (D : set α) : 
  (M ⟍ D).indep I ↔ M.indep I ∧ I ⊆ M.E \ D :=
begin
  rw [indep_iff_coe, indep_iff_coe, delete_coe, indep_loopify_iff, and_comm, subset_diff], 
  exact ⟨λ h, ⟨h.1, indep.subset_ground (h.1),h.2⟩, λ h, ⟨h.1, h.2.2⟩⟩, 
end    

lemma contract_eq_contract_inter_ground (M : matroid_in α) (C : set α) : M ⟋ C = M ⟋ (C ∩ M.E) :=
begin
  refine eq_of_coe_eq_coe (by simp) _, 
  rw [contract_coe, contract_coe, ←project_cl_eq_project, ←project_cl_eq_project _ (C ∩ M.E)], 
  convert rfl using 2,
  rw [←compl_compl M.E, inter_comm, ←diff_eq_compl_inter, cl_diff_eq_cl_of_subset_loops],  
  exact compl_ground_subset_loops_coe M, 
end   

lemma delete_eq_delete_inter_ground (M : matroid_in α) (D : set α) : M ⟍ D = M ⟍ (D ∩ M.E) :=
begin 
  nth_rewrite 0 ←inter_union_diff D M.E, 
  rw [←delete_delete],
  refine eq_of_coe_eq_coe (by simp) _, 
  rw [delete_coe, loopify_eq_of_loops], 
  simp only [delete_coe, loopify_cl_eq, empty_diff], 
  refine (diff_subset_diff_left (subset_univ D)).trans (subset_trans _ (subset_union_left _ _)),
  rw [←compl_eq_univ_diff] , 
  exact compl_ground_subset_loops_coe _,
end   

lemma contract_eq_contract_cl {C : set α} :
  M ⟋ (M.cl C) = M ⟋ C ⟍ (M.cl C \ C) :=
begin
  rw [contract_eq_contract_inter_ground, contract_eq_contract_inter_ground M C], 
  -- refine eq_of_coe_eq_coe _ _, 
  -- { rw [delete_ground, contract_ground, contract_ground, diff_diff, union_diff_cancel],
  --   exact M.subset_cl _ },
  -- -- dsimp only [contract], 
end  


-- lemma contract_dual (M : matroid_in α) (X : set α) : 
--   (M / X)* = M* \ X :=
-- begin
--   refine eq_of_base_iff_base rfl (λ I, _),
--   simp [contract, matroid_in.dual],  

-- end 

end minor

end matroid_in 
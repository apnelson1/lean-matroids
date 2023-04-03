import .matroid_in

open_locale classical 
noncomputable theory

open matroid set 

variables {E α : Type*} [finite E] [finite α] {I C B X Y : set α} {M : matroid_in α}

namespace matroid_in 

section minor

def contract (M : matroid_in α) (C : set α) : matroid_in α := 
{ E := M.E \ C,
  carrier := M.carrier ⟋ C,
  support := 
  begin
    simp only [project_cl_eq, empty_union, diff_eq_compl_inter, compl_inter, compl_compl], 
    exact union_subset (M.carrier.subset_cl C) 
      (M.support.trans (M.carrier.cl_mono (empty_subset _))),
  end }

def delete (M : matroid_in α) (D : set α) : matroid_in α := 
{ E := M.E \ D,
  carrier := M.carrier ⟍ D,
  support := 
  begin
    rw [loopify_cl_eq, empty_diff, compl_subset_comm, compl_union, diff_eq_compl_inter, 
      subset_inter_iff], 
    exact ⟨inter_subset_right _ _, (inter_subset_left _ _).trans 
      (λ x (hx : x ∉ M.carrier.cl ∅ ), mem_E_of_nonloop hx)⟩, 
    end }

reserve infix ` ⟋ `:85 
reserve infix ` ⟍ `:85 

notation (name := matroid_in_contract) M₁ ⟋  X := matroid_in.contract M₁ X 
notation (name := matroid_in_delete) M₁ ⟍ X := matroid_in.delete M₁ X 

@[simp] lemma contract_contract (M : matroid_in α) (C₁ C₂ : set α) : 
  M ⟋ C₁ ⟋ C₂ = M ⟋ (C₁ ∪ C₂) :=
by simp [contract, diff_diff]

lemma contract_comm (M : matroid_in α) (C₁ C₂ : set α) : 
  M ⟋ C₁ ⟋ C₂ = M ⟋ C₂ ⟋ C₁ :=
by rw [contract_contract, contract_contract, union_comm]
 
@[simp] lemma delete_delete (M : matroid_in α) (D₁ D₂ : set α) : 
  M ⟍ D₁ ⟍ D₂ = M ⟍ (D₁ ∪ D₂) :=
by simp [delete, diff_diff]

lemma delete_comm (M : matroid_in α) (D₁ D₂ : set α) : 
  M ⟍ D₁ ⟍ D₂ = M ⟍ D₂ ⟍ D₁ :=
by rw [delete_delete, delete_delete, union_comm]

lemma contract_delete_comm (M : matroid_in α) {C D : set α} (hCD : disjoint C D) : 
  M ⟋ C ⟍ D = M ⟍ D ⟋ C := 
by {simp_rw [delete, contract], rw [diff_diff_comm, project_loopify_comm _ hCD], exact ⟨rfl,rfl⟩}

lemma contract_indep_iff (hI : M.indep I) : 
  (M ⟋ I).indep X ↔ M.indep (X ∪ I) ∧ X ⊆ (M.E \ I) :=  
begin
  simp_rw indep_iff_carrier_indep at *, 
  dsimp only [contract], 
  rw [hI.project_indep_iff, and_comm, subset_diff], 
  exact ⟨λ h, ⟨h.1, subset_E_of_indep_carrier (h.1.subset (subset_union_left _ _)), h.2⟩,
    λ h, ⟨h.1, h.2.2⟩⟩, 
end 

lemma delete_indep_iff (D : set α) : 
  (M ⟍ D).indep I ↔ M.indep I ∧ I ⊆ M.E \ D :=
begin
  simp_rw indep_iff_carrier_indep at *, 
  dsimp only [delete], 
  rw [indep_loopify_iff, subset_diff], 
  exact ⟨λ h, ⟨h.2, subset_E_of_indep_carrier h.2, h.1⟩,λ h, ⟨h.2.2, h.1⟩⟩, 
end    

lemma contract_eq_contract_cl (C : set α) :
  M ⟋ C = M ⟋ (M.cl C) :=
begin
  
  -- dsimp only [contract], 
end  


-- lemma contract_dual (M : matroid_in α) (X : set α) : 
--   (M / X)* = M* \ X :=
-- begin
--   refine eq_of_base_iff_base rfl (λ I, _),
--   simp [contract, matroid_in.dual],  

-- end 

end minor

end matroid_in 
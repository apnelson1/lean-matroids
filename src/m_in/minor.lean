import .restriction
import .closure 

open set 

variables {α : Type*} {I J C D B X Y Z R : set α} {M : matroid_in α}

namespace matroid_in 

section delete

variables {D₁ D₂ : set α}

class has_delete (α β : Type*) := (del : α → β → α)

infix ` ⟍ ` :75 :=  has_delete.del 

def delete (M : matroid_in α) (D : set α) : matroid_in α := M ‖ Dᶜ 

instance del_set {α : Type*} : has_delete (matroid_in α) (set α) := ⟨matroid_in.delete⟩
instance del_elem {α : Type*} : has_delete (matroid_in α) α := ⟨λ M e, M.delete {e}⟩  

@[simp] lemma delete_compl (M : matroid_in α) (R : set α) : M ⟍ Rᶜ = M ‖ R := 
by { change M ‖ Rᶜᶜ = M ‖ R, rw compl_compl } 

@[simp] lemma restrict_compl (M : matroid_in α) (D : set α) : M ‖ Dᶜ = M ⟍ D := rfl    

@[simp] lemma delete_ground (M : matroid_in α) (D : set α) : (M ⟍ D).E = M.E \ D := 
by rw [←restrict_compl, restrict_ground_eq', diff_eq_compl_inter]

@[simp] lemma delete_elem (M : matroid_in α) (e : α) : M ⟍ e = M ⟍ ({e} : set α) := rfl 

@[simp] lemma delete_delete (M : matroid_in α) (D₁ D₂ : set α) : (M ⟍ D₁) ⟍ D₂ = M ⟍ (D₁ ∪ D₂) :=
by rw [←restrict_compl, ←restrict_compl, ←restrict_compl, restrict_restrict, compl_union]

lemma delete_comm (M : matroid_in α) (D₁ D₂ : set α) : M ⟍ D₁ ⟍ D₂ = M ⟍ D₂ ⟍ D₁ := 
by rw [delete_delete, union_comm, delete_delete]

@[simp] lemma delete_indep_iff : (M ⟍ D).indep I ↔ M.indep I ∧ disjoint I D := 
by rw [←restrict_compl, restrict_indep_iff, subset_compl_iff_disjoint_right]

@[simp] lemma delete_base_iff : (M ⟍ D).base B ↔ M.basis B (M.E \ D) :=
by rw [←restrict_compl, ←restrict_inter_ground, ←diff_eq_compl_inter, restrict_base_iff]

lemma delete_eq_delete_iff : M ⟍ D₁ = M ⟍ D₂ ↔ D₁ ∩ M.E = D₂ ∩ M.E := 
by simp_rw [←restrict_compl, restrict_eq_restrict_iff,
    ←diff_eq_compl_inter, diff_eq_diff_iff_inter_eq_inter, inter_comm M.E]

lemma delete_eq_self_iff : M ⟍ D = M ↔ disjoint D M.E := 
by rw [←restrict_compl, restrict_eq_self_iff, subset_compl_iff_disjoint_left]

@[simp] lemma delete_empty (M : matroid_in α) : M ⟍ (∅ : set α) = M := 
by { rw [delete_eq_self_iff], exact empty_disjoint _ }

@[simp] lemma delete_ground_eq_empty (M : matroid_in α) : M ⟍ M.E = empty α :=
by simp [←ground_eq_empty_iff_eq_empty]

lemma delete_delete_diff (M : matroid_in α) (D₁ D₂ : set α) : M ⟍ D₁ ⟍ D₂ = M ⟍ D₁ ⟍ (D₂ \ D₁) :=
by simp

lemma delete_eq_delete_inter_ground (M : matroid_in α) (D : set α) : M ⟍ D = M ⟍ (D ∩ M.E) := 
by rw [delete_eq_delete_iff, inter_assoc, inter_self]

end delete

section contract 

variables {C₁ C₂ : set α}

class has_contract (α β : Type*) := (con : α → β → α)

infix ` ⟋ ` :75 :=  has_contract.con

def contract (M : matroid_in α) (C : set α) : matroid_in α := (M﹡ ⟍ C)﹡

instance con_set {α : Type*} : has_contract (matroid_in α) (set α) := ⟨matroid_in.contract⟩
instance con_elem {α : Type*} : has_contract (matroid_in α) α := ⟨λ M e, M.contract {e}⟩ 

@[simp] lemma dual_delete_dual_eq_contract (M : matroid_in α) (X : set α) : (M﹡ ⟍ X)﹡ = M ⟋ X := 
rfl  

@[simp] lemma dual_contract_dual_eq_delete (M : matroid_in α) (X : set α) : (M﹡ ⟋ X)﹡ = M ⟍ X := 
by rw [←dual_delete_dual_eq_contract, dual_dual, dual_dual]

@[simp] lemma contract_ground (M : matroid_in α) (C : set α) : (M ⟋ C).E = M.E \ C := 
by rw [←dual_delete_dual_eq_contract, dual_ground, delete_ground, dual_ground]

@[simp] lemma contract_elem (M : matroid_in α) (e : α) : M ⟋ e = M ⟋ ({e} : set α) := rfl  

@[simp] lemma contract_contract (M : matroid_in α) (C₁ C₂ : set α) : M ⟋ C₁ ⟋ C₂ = M ⟋ (C₁ ∪ C₂) := 
by rw [eq_comm, ←dual_delete_dual_eq_contract, ←delete_delete, ←dual_contract_dual_eq_delete, 
    ←dual_contract_dual_eq_delete, dual_dual, dual_dual, dual_dual]

lemma contract_comm (M : matroid_in α) (C₁ C₂ : set α) : M ⟋ C₁ ⟋ C₂ = M ⟋ C₂ ⟋ C₁ := 
by rw [contract_contract, union_comm, contract_contract]

lemma contract_eq_self_iff : M ⟋ C = M ↔ disjoint C M.E := 
by rw [←dual_delete_dual_eq_contract, ←dual_inj_iff, dual_dual, delete_eq_self_iff, dual_ground]

@[simp] lemma contract_ground_eq_empty (M : matroid_in α) : M ⟋ M.E = empty α :=
by simp [←ground_eq_empty_iff_eq_empty]

@[simp] lemma contract_empty (M : matroid_in α) : M ⟋ (∅ : set α) = M := 
by { rw [contract_eq_self_iff], exact empty_disjoint _, }

lemma contract_contract_diff (M : matroid_in α) (C₁ C₂ : set α) :
  M ⟋ C₁ ⟋ C₂ = M ⟋ C₁ ⟋ (C₂ \ C₁) :=
by simp 

lemma contract_eq_contract_iff : M ⟋ C₁ = M ⟋ C₂ ↔ C₁ ∩ M.E = C₂ ∩ M.E := 
by rw [←dual_delete_dual_eq_contract, ←dual_delete_dual_eq_contract, dual_inj_iff, 
  delete_eq_delete_iff, dual_ground]

lemma contract_eq_contract_inter_ground (M : matroid_in α) (C : set α) : M ⟋ C = M ⟋ (C ∩ M.E) := 
by rw [←dual_delete_dual_eq_contract, delete_eq_delete_inter_ground, dual_delete_dual_eq_contract, 
  dual_ground]

lemma indep.contract_base_iff (hI : M.indep I) : (M ⟋ I).base B ↔ disjoint B I ∧ M.base (B ∪ I) := 
begin
  rw [←dual_dual M, dual_indep_iff_exists] at hI, 
  obtain ⟨hIE, B₀, hB₀, hfk⟩ := hI, 
  rw [←dual_dual M, ←dual_delete_dual_eq_contract, dual_base_iff', dual_base_iff', 
    delete_base_iff, dual_dual, delete_ground, diff_diff, union_comm, union_subset_iff, 
    and_iff_left hIE, subset_diff, disjoint.comm, and_comm (disjoint _ _), ←and_assoc, 
    and.congr_left_iff, and.congr_left_iff], 

  exact λ hIB hBE, ⟨λ h, h.base_of_base_subset hB₀ (subset_diff.mpr ⟨by ssE, hfk.symm⟩), 
    λ hB, hB.basis_of_subset (diff_subset _ _) (diff_subset_diff_right (subset_union_right _ _))⟩,
end  

lemma indep.contract_indep_iff (hI : M.indep I) : 
  (M ⟋ I).indep J ↔ disjoint J I ∧ M.indep (J ∪ I)  :=
begin
  simp_rw [indep_iff_subset_base, hI.contract_base_iff, union_subset_iff], 
  split, 
  { rintro ⟨B, ⟨hdj, hBI⟩, hJB⟩, 
    exact ⟨disjoint_of_subset_left hJB hdj, _, hBI, hJB.trans (subset_union_left _ _), 
      (subset_union_right _ _)⟩ },
  rintro ⟨hdj, B, hB, hJIB⟩, 
  refine ⟨B \I, ⟨disjoint_sdiff_left, _⟩, _⟩,
  { rwa [diff_union_self, union_eq_self_of_subset_right hJIB.2] }, 
  rw [subset_diff], 
  exact ⟨hJIB.1, hdj⟩, 
end 

lemma basis.contract_base_iff (hIX : M.basis I C) :
  (M ⟋ C).base B ↔ disjoint B C ∧ M.base (B ∪ I) :=
begin
  rw [←dual_delete_dual_eq_contract, dual_base_iff', delete_base_iff, delete_ground, dual_ground, 
    subset_diff, and_comm (disjoint _ _), ←and_assoc, and.congr_left_iff, ←dual_dual M, 
    dual_base_iff', dual_dual, dual_ground, union_subset_iff, and_comm (_ ⊆ _), ←and_assoc, 
    and.congr_left_iff, and_iff_left (hIX.subset_ground_left.trans_eq dual_ground.symm)], 
  -- set N := M﹡ with hN, 
  intros hBC hBE, 
  refine ⟨λ h, _, λ h, _⟩,
  { rw [dual_base_iff'], 
    simp only [dual_ground, sdiff_sdiff_right_self, inf_eq_inter, ground_inter_right, 
      and_iff_left (diff_subset _ _)], 
    },
  
  
end  

-- lemma contract_cl_eq : (M ⟋ C).cl X = M.cl (X ∪ C) \ C := 
-- begin

-- end 

lemma contract_eq_delete_of_subset_loops (hX : X ⊆ M.cl ∅) : M ⟋ X = M ⟍ X :=
begin
  rw [←dual_delete_dual_eq_contract], 
  rw ←empty_basis_iff at hX, 
  refine eq_of_indep_iff_indep_forall rfl (λ I hIE, _), 
  rw [dual_ground] at hIE, 
  simp_rw [dual_indep_iff_exists, and_iff_right hIE, delete_indep_iff, delete_base_iff, 
    dual_ground, basis_iff, dual_indep_iff_exists],  simp, 
  
  
end
-- lemma contract_eq_delete_iff : M ⟋ X = M ⟍ X ↔ X ⊆ M.cl ∅ ∪ 

-- lemma basis.foo (hI : M.basis I C) : M ⟋ C = M ⟋ I ⟍ (C \ I) :=
-- begin
--   nth_rewrite 0 ←union_diff_cancel hI.subset,
--   rw [←contract_contract], 
-- end

end contract 

section contract_delete

lemma contract_delete_diff (M : matroid_in α) (C D : set α) : M ⟋ C ⟍ D = M ⟋ C ⟍ (D \ C) := 
by rw [delete_eq_delete_iff, contract_ground, diff_eq, diff_eq, ←inter_inter_distrib_right, 
  inter_assoc]

-- lemma contract_delete_comm (M : matroid_in α) {C D : set α} (hCD : disjoint C D) : 
--   M ⟋ C ⟍ D = M ⟍ D ⟋ C := 
-- begin
--   rw [←dual_delete_dual_eq_contract, ←dual_delete_dual_eq_contract, eq_dual_comm, 
--     dual_delete_dual_eq_contract], 
-- end 



end contract_delete

end matroid_in 


-- /-- Contract a set from a `matroid_in α` to give a smaller `matroid_in α`-/
-- def contract (M : matroid_in α) (C : set α) : matroid_in α := 
-- { ground := M.E \ C,
--   carrier := (M : matroid α) ⟋ C,
--   support := 
--   begin
--     simp only [project.cl_eq, empty_union, diff_eq_compl_inter, compl_inter, compl_compl], 
--     exact union_subset (M.carrier.subset_cl C) 
--       (M.support.trans (M.carrier.cl_mono (empty_subset _))),
--   end }

-- /-- Restrict a `matroid_in α` to a smaller ground set. -/
-- def restrict (M : matroid_in α) (R : set α) : matroid_in α :=
-- ⟨M.E ∩ R, M ‖ R, 
-- begin
--   rw [lrestr.cl_eq, empty_inter, compl_inter],
--   exact union_subset_union_left _ (compl_ground_subset_loops_coe _ ),  
-- -- end⟩  

-- def delete (M : matroid_in α) (D : set α) : matroid_in α := M.restrict Dᶜ 

-- instance {α : Type*} : has_con (matroid_in α) (set α) := ⟨matroid_in.contract⟩  
-- instance {α : Type*} : has_del (matroid_in α) (set α) := ⟨matroid_in.delete⟩
-- instance {α : Type*} : has_restr (matroid_in α) (set α) := ⟨matroid_in.restrict⟩  
-- instance {α : Type*} : has_con (matroid_in α) α := ⟨λ M e, M.contract {e}⟩  
-- instance {α : Type*} : has_del (matroid_in α) α := ⟨λ M e, M.delete {e}⟩  

-- @[simp] lemma contract_coe (M : matroid_in α) (C : set α) : 
--   ((M ⟋ C : matroid_in α) : matroid α) = (M : matroid α) ⟋ C := rfl 




-- @[simp] lemma delete_coe (M : matroid_in α) (D : set α) : 
--   ((M ⟍ D : matroid_in α) : matroid α) = (M : matroid α) ⟍ D := rfl 

-- @[simp] lemma restrict_coe (M : matroid_in α) (R : set α) : 
--   ((M ‖ R : matroid_in α) : matroid α) = (M : matroid α) ‖ R := rfl  

-- @[simp] lemma delete_ground (M : matroid_in α) (D : set α) : (M ⟍ D).E = M.E \ D := rfl 

-- @[simp] lemma restrict_ground (M : matroid_in α) (R : set α) : (M ‖ R).E = M.E ∩ R := rfl

-- @[simp] lemma restrict_ground_self (M : matroid_in α) : M ‖ M.E = M := 
-- begin
--   refine eq_of_coe_eq_coe (by simp) _, 
--   rw [restrict_coe, lrestr_eq_self_iff], 
--   exact M.support, 
-- end 

-- lemma restrict_eq_self_iff : M ‖ X = M ↔ M.E ⊆ X := 
-- begin
--   rw [←eq_iff_coe_eq_coe, restrict_ground, inter_eq_left_iff_subset, restrict_coe, 
--     lrestr_eq_self_iff, compl_subset_comm, ←union_subset_iff], 
--   convert iff.rfl, 
--   rw [eq_comm, union_eq_left_iff_subset, compl_subset_comm], 
--   exact M.support,
-- end   

-- lemma restrict_eq_delete (M : matroid_in α) (R : set α) : M ‖ R = M ⟍ Rᶜ := 
-- by { change M ‖ R = M ‖ Rᶜᶜ, rw compl_compl } 

-- lemma delete_eq_restrict (M : matroid_in α) (D : set α) : M ⟍ D = M ‖ Dᶜ := rfl    

-- @[simp] lemma restrict_restrict (M : matroid_in α) (R₁ R₂ : set α) : 
--   (M ‖ R₁) ‖ R₂ = M ‖ (R₁ ∩ R₂) := 
-- eq_of_coe_eq_coe (by simp [inter_assoc]) (by simp)

-- lemma restrict_restrict_of_subset (M : matroid_in α) {R₁ R₂ : set α} (h : R₂ ⊆ R₁) :
--   (M ‖ R₁) ‖ R₂ = M ‖ R₂ :=
-- by rw [restrict_restrict, inter_eq_self_of_subset_right h]  

-- @[simp] lemma contract_contract (M : matroid_in α) (C₁ C₂ : set α) : M ⟋ C₁ ⟋ C₂ = M ⟋ (C₁ ∪ C₂) :=
-- eq_of_coe_eq_coe (by simp [diff_diff]) (by simp)

-- @[simp] lemma contract_empty (M : matroid_in α) : M ⟋ (∅ : set α) = M := 
-- eq_of_coe_eq_coe (by simp) (by simp)

-- @[simp] lemma delete_empty (M : matroid_in α) : M ⟍ (∅ : set α) = M := 
-- eq_of_coe_eq_coe (by simp) (by simp)

-- lemma contract_eq_self_of_disjoint_ground (hC : disjoint C M.E) : M ⟋ C = M := 
-- begin
--   apply eq_of_coe_eq_coe, 
--   rw [contract_ground, hC.sdiff_eq_right], 
--   rw [contract_coe, project.eq_of_subset_loops], 
--   exact subset_loops_coe_of_disjoint_ground hC, 
-- end 

-- lemma contract_eq_self_iff_disjoint_ground : M ⟋ C = M ↔ disjoint C M.E := 
-- ⟨λ hM, by { rw ←hM, exact disjoint_sdiff_right }, contract_eq_self_of_disjoint_ground⟩

-- lemma delete_eq_self_of_disjoint_ground (hD : disjoint D M.E) : M ⟍ D = M := 
-- begin
--   apply eq_of_coe_eq_coe, 
--   rw [delete_ground, hD.sdiff_eq_right], 
--   rw [delete_coe, loopify.eq_of_subset_loops], 
--   exact subset_loops_coe_of_disjoint_ground hD, 
-- end 

-- lemma delete_eq_self_iff_disjoint_ground : M ⟍ C = M ↔ disjoint C M.E := 
-- ⟨λ hM, by { rw ←hM, exact disjoint_sdiff_right }, delete_eq_self_of_disjoint_ground⟩
   
-- lemma contract_comm (M : matroid_in α) (C₁ C₂ : set α) : M ⟋ C₁ ⟋ C₂ = M ⟋ C₂ ⟋ C₁ :=
-- by rw [contract_contract, contract_contract, union_comm]
 
-- @[simp] lemma delete_delete (M : matroid_in α) (D₁ D₂ : set α) : M ⟍ D₁ ⟍ D₂ = M ⟍ (D₁ ∪ D₂) :=
-- eq_of_coe_eq_coe (by simp [diff_diff]) (by simp)

-- lemma delete_comm (M : matroid_in α) (D₁ D₂ : set α) : M ⟍ D₁ ⟍ D₂ = M ⟍ D₂ ⟍ D₁ :=
-- by rw [delete_delete, delete_delete, union_comm]

-- lemma delete_delete_diff (M : matroid_in α) (D₁ D₂ : set α) : M ⟍ D₁ ⟍ D₂ = M ⟍ D₁ ⟍ (D₂ \ D₁) :=
-- begin
--   nth_rewrite 0 ←inter_union_diff D₂ D₁, 
--   rw [union_comm, ←delete_delete, delete_eq_self_iff_disjoint_ground],  
--   exact disjoint_of_subset (inter_subset_right _ _) (diff_subset _ _) (disjoint_sdiff_right), 
-- end 

-- lemma restrict_eq_restrict_inter_ground (M : matroid_in α) (R : set α) : M ‖ R = M ‖ (R ∩ M.E) :=
-- begin 
--   rw [restrict_eq_delete, restrict_eq_delete, compl_inter, ←delete_delete, eq_comm, 
--     delete_eq_self_of_disjoint_ground], 
--   exact disjoint_of_subset_right (diff_subset _ _) disjoint_compl_left, 
-- end 

-- lemma restrict_eq_delete_diff (M : matroid_in α) (R : set α) : M ‖ R = M ⟍ (M.E \ R) :=
-- begin
--   rw [restrict_eq_delete], 
--   nth_rewrite 0 ←inter_union_diff Rᶜ M.E, 
--   rw [←diff_eq_compl_inter, ←delete_delete, delete_eq_self_iff_disjoint_ground], 
--   exact disjoint_of_subset_right (diff_subset _ _) (disjoint_sdiff_left), 
-- end 

-- lemma contract_contract_diff (M : matroid_in α) (C₁ C₂ : set α) : 
--   M ⟋ C₁ ⟋ C₂  = M ⟋ C₁ ⟋ (C₂ \ C₁)   :=
-- begin
--   nth_rewrite 0 ←inter_union_diff C₂ C₁, 
--   rw [union_comm, ←contract_contract, contract_eq_self_iff_disjoint_ground],  
--   exact disjoint_of_subset (inter_subset_right _ _) (diff_subset _ _) (disjoint_sdiff_right), 
-- end 

-- lemma contract_delete_diff (M : matroid_in α) (C D : set α) : 
--   M ⟋ C ⟍ D = M ⟋ C ⟍ (D \ C) := 
-- begin
--   nth_rewrite 0 ←inter_union_diff D C,
--   rw [union_comm, ←delete_delete, delete_eq_self_iff_disjoint_ground], 
--   exact disjoint_of_subset (inter_subset_right _ _) (diff_subset _ _) (disjoint_sdiff_right), 
-- end  

-- lemma contract_delete_comm (M : matroid_in α) {C D : set α} (hCD : disjoint C D) : 
--   M ⟋ C ⟍ D = M ⟍ D ⟋ C := 
-- eq_of_coe_eq_coe (by simp [diff_diff_comm]) (by simp [project_loopify_comm _ hCD]) 

-- lemma contract_indep_iff (hI : M.indep I) : 
--   (M ⟋ I).indep X ↔ M.indep (X ∪ I) ∧ X ⊆ (M.E \ I) :=  
-- begin
--   rw [indep_iff_coe, contract_coe, hI.project_indep_iff, and_comm, indep_iff_coe, subset_diff] at *, 
--   exact ⟨λ h, ⟨h.1, indep.subset_ground (h.1.subset (subset_union_left _ _)),h.2⟩,
--     λ h, ⟨h.1, h.2.2⟩⟩, 
-- end 

-- lemma indep.of_contract (hI : (M ⟋ C).indep I) : M.indep I := hI.of_project

-- @[simp] lemma restrict_indep_iff : (M ‖ R).indep I ↔ M.indep I ∧ I ⊆ R :=
-- by rw [indep_iff_coe, restrict_coe, lrestr.indep_iff, ←indep_iff_coe]

-- lemma indep.of_restrict (h : (M ‖ R).indep I) : M.indep I := (restrict_indep_iff.mp h).1

-- @[simp] lemma delete_indep_iff : 
--   (M ⟍ D).indep I ↔ M.indep I ∧ disjoint I D :=
-- by rw [indep_iff_coe, delete_coe, loopify.indep_iff, and_comm, indep_iff_coe]

-- @[simp] lemma delete_circuit_iff : 
--   (M ⟍ D).circuit C ↔ M.circuit C ∧ disjoint C D :=
-- begin
--   obtain (h | h) := em (disjoint C D), 
--   { simp_rw [circuit, delete_coe, loopify.circuit_iff_of_disjoint h, iff_true_intro h, and_true],
--     exact ⟨λ h', ⟨h'.1,h'.2.trans (diff_subset _ _)⟩, λ h', ⟨h'.1, subset_diff.mpr ⟨h'.2, h⟩⟩⟩ },
--   rw [circuit, delete_ground, subset_diff], 
--   simp [h], 
-- end 

-- lemma indep.delete_indep (hI : M.indep I) (hID : disjoint I D) : (M ⟍ D).indep I := 
-- delete_indep_iff.mpr ⟨hI,hID⟩  

-- @[simp] lemma contract_cl (M : matroid_in α) (C X : set α) : (M ⟋ C).cl X = M.cl (X ∪ C) \ C :=
-- by rw [cl_eq_coe_cl_inter, contract_coe, project.cl_eq, contract_ground, cl_eq_coe_cl_inter, 
--     diff_eq, diff_eq, inter_assoc]

-- @[simp] lemma delete_cl (M : matroid_in α) (h : disjoint X D) : (M ⟍ D).cl X = M.cl X \ D :=
-- by rw [cl_eq_coe_cl_inter, cl_eq_coe_cl_inter, delete_coe, loopify.cl_eq, delete_ground, 
--   h.sdiff_eq_left, inter_distrib_right, inter_diff_self, union_empty, diff_eq, diff_eq, inter_assoc]

-- @[simp] lemma restrict_cl (M : matroid_in α) (h : X ⊆ R) : (M ‖ R).cl X = M.cl X ∩ R :=
-- by rw [cl, restrict_coe, restrict_ground, lrestr.cl_eq, inter_distrib_right, inter_comm Rᶜ, 
--     inter_assoc, inter_compl_self, inter_empty, union_empty, inter_eq_self_of_subset_left h, 
--     cl, inter_assoc]

-- @[simp] lemma delete_loops (M : matroid_in α) (D : set α) : (M ⟍ D).cl ∅ = M.cl ∅ \ D :=
-- by { rw delete_cl, exact empty_disjoint _ }  

-- lemma contract_eq_contract_inter_ground (M : matroid_in α) (C : set α) : M ⟋ C = M ⟋ (C ∩ M.E) :=
-- begin
--   nth_rewrite 0 ←inter_union_diff C M.E, 
--   rw [←contract_contract, contract_eq_self_of_disjoint_ground], 
--   rw [contract_ground], 
--   exact disjoint_of_subset_right (diff_subset _ _) (disjoint_sdiff_left), 
-- end   

-- lemma delete_eq_delete_inter_ground (M : matroid_in α) (D : set α) : M ⟍ D = M ⟍ (D ∩ M.E) :=
-- begin 
--   nth_rewrite 0 ←inter_union_diff D M.E, 
--   rw [←delete_delete, delete_eq_self_of_disjoint_ground], 
--   rw [delete_ground], 
--   exact disjoint_of_subset_right (diff_subset _ _) (disjoint_sdiff_left), 
-- end   

-- lemma indep.contract_indep_iff (hI : M.indep I) : 
--   (M ⟋ I).indep J ↔ disjoint J I ∧ M.indep (J ∪ I)  :=
-- matroid.indep.project_indep_iff hI

-- lemma contract_loops (M : matroid_in α) (C : set α) : (M ⟋ C).cl ∅ = M.cl C \ C := 
-- by rw [contract_cl, empty_union]

-- @[simp] lemma delete_r_eq (M : matroid_in α) (D X : set α) : (M ⟍ D).r X = M.r (X \ D) :=
-- by rw [r_eq_coe_r, r_eq_coe_r, delete_coe, loopify.r_eq]

-- lemma r_fin.contract (h : M.r_fin X) (C : set α) : (M ⟋ C).r_fin (X \ C) := 
-- begin
--   refine ⟨(h.to_coe.project C).subset (diff_subset _ _), _⟩,  
--   rw [diff_subset_iff, contract_ground, union_diff_self], 
--   exact subset_union_of_subset_right h.subset_ground _, 
-- end 

-- lemma r_fin.of_contract (h : (M ⟋ C).r_fin X) (hC : M.r_fin C) : M.r_fin X :=
-- ⟨r_fin.of_project (by simpa using h.to_coe) hC.to_coe, h.subset_ground.trans (diff_subset _ _)⟩

-- lemma r_fin.r_fin_contract_iff (hC : M.r_fin C) :
--   (M ⟋ C).r_fin X ↔ M.r_fin X ∧ disjoint X C := 
-- begin
--   split, 
--   exact λ h, ⟨h.of_contract hC,disjoint_of_subset_left h.subset_ground disjoint_sdiff_left⟩,
--   rintro ⟨hX, hXC⟩,  
--   convert hX.contract C, 
--   rwa [eq_comm, sdiff_eq_left],
-- end 

-- lemma r_fin.contract_r_cast_eq (h : M.r_fin X) (hC : M.r_fin C) : 
--   ((M ⟋ C).r X : ℤ) = M.r (X ∪ C) - M.r C :=
-- h.to_coe.project_cast_r_eq hC.to_coe

-- lemma r_fin.contract_r_add_r_eq (h : M.r_fin X) (hC : M.r_fin C) : 
--   (M ⟋ C).r X + M.r C = M.r (X ∪ C) :=
-- by { zify, simp [h.contract_r_cast_eq hC] }

-- @[simp] lemma contract_r_cast_eq (M : matroid_in α) [M.finite_rk] (X C : set α) : 
--   ((M ⟋ C).r X : ℤ)  = M.r (X ∪ C) - M.r C := 
-- by rw [r_eq_coe_r, contract_coe, project_cast_r_eq, r_eq_coe_r, r_eq_coe_r]

-- @[simp] lemma contract_r_add_r_eq (M : matroid_in α) [M.finite_rk] (X C : set α) : 
--   (M ⟋ C).r X + M.r C = M.r (X ∪ C) :=
-- by { zify, simp [contract_r_cast_eq] }

-- @[simp] lemma contract_dual (M : matroid_in α) (X : set α) : (M ⟋ X)﹡ = M﹡ ⟍ X :=
-- begin
--   suffices : ∀ Y ⊆ M.E, (M ⟋ Y)﹡ = M﹡ ⟍ Y, 
--   { convert this (X ∩ M.E) (inter_subset_right _ _) using 1,
--     rw [dual_inj_iff, contract_eq_contract_inter_ground],
--     rw [delete_eq_delete_inter_ground, dual_ground] },
  
--   refine λ Y hY, eq_of_indep_iff_indep_forall rfl (λ I hI, _),  
--   rw [dual_indep_iff_coindep, delete_indep_iff, dual_indep_iff_coindep, 
--     coindep_iff_cl_compl_eq_ground, coindep_iff_cl_compl_eq_ground], 
--   { rw [dual_ground, contract_ground] at hI, 
--     have hXI := disjoint_of_subset_left hI disjoint_sdiff_left, 
--     rw [iff_true_intro hXI, and_true, contract_ground, contract_cl, diff_diff, subset_antisymm_iff, 
--       diff_subset_iff, union_diff_self, diff_subset_iff, union_diff_self,
--       iff_true_intro (subset_union_of_subset_right (cl_subset_ground _ _) _), true_and, 
--       union_eq_self_of_subset_left ((subset_cl hY).trans (cl_subset _ (subset_union_right _ _))), 
--       diff_eq, union_distrib_right, union_eq_self_of_subset_right hY, compl_union, 
--       union_distrib_right, compl_union_self, univ_inter, inter_distrib_left, 
--       union_eq_self_of_subset_right, ←diff_eq, subset_antisymm_iff, 
--       iff_true_intro (cl_subset_ground _ _), true_and],  
--     exact (inter_subset_right _ _).trans 
--       (subset_inter hY (subset_compl_iff_disjoint_left.mpr hXI)) },
--   { refine hI.trans _, simp [diff_subset] },
--   convert hI using 1, 
-- end 

-- @[simp] lemma delete_dual (M : matroid_in α) (X : set α) : (M ⟍ X)﹡ = M﹡ ⟋ X :=
-- by rw [←dual_inj_iff, contract_dual, dual_dual, dual_dual]

-- @[simp] lemma contract_coindep_iff : (M ⟋ C).coindep X ↔ M.coindep X ∧ disjoint X C := 
-- by rw [←dual_indep_iff_coindep, contract_dual, delete_indep_iff, dual_indep_iff_coindep]

-- lemma coindep.contract_coindep (h : M.coindep X) (hdj : disjoint X C) : (M ⟋ C).coindep X :=
-- contract_coindep_iff.mpr ⟨h,hdj⟩  

-- lemma contract_eq_delete_of_subset_loops (hX : X ⊆ M.cl ∅) : M ⟋ X = M ⟍ X :=
-- begin
--   refine eq_of_indep_iff_indep_forall rfl (λ I (hI : I ⊆ M.E \ X), _), 
--   rw subset_diff at hI, 
--   rw [delete_indep_iff, indep_iff_coe, contract_coe, ←(true_iff _).mpr hI.2, and_true,
--     project.eq_of_subset_loops (hX.trans (cl_subset_coe_cl _ _)), indep_iff_coe], 
-- end  

-- lemma contract_eq_delete_of_subset_coloops (M : matroid_in α) {X : set α} (hX : X ⊆ M﹡.cl ∅) :
--   M ⟋ X = M ⟍ X :=
-- by rw [←dual_inj_iff, contract_dual, delete_dual, contract_eq_delete_of_subset_loops hX]

-- lemma contract_cl_eq_contract_delete (M : matroid_in α) (C : set α) :
--   M ⟋ (M.cl C) = M ⟋ C ⟍ (M.cl C \ C) :=
-- begin
--   rw [←contract_eq_delete_of_subset_loops, contract_contract, union_diff_self, union_comm, 
--     ←union_diff_self, ←contract_contract, eq_comm],
--   refine contract_eq_self_of_disjoint_ground _, 
--   { rw [contract_ground, cl_eq_coe_cl_inter, diff_inter, 
--       diff_eq_empty.mpr (matroid.subset_cl (M : matroid α ) _), empty_union], 
--     exact disjoint_of_subset_right (diff_subset _ _) disjoint_sdiff_left },
--   rw [contract_cl, empty_union], 
-- end  

lemma basis.contract_eq (h : M.basis I X) : 
  M ⟋ X = M ⟋ I ⟍ (X \ I) :=
begin
  nth_rewrite 0 ←union_diff_cancel h.subset, 
  sorry,
  /-rw [←contract_contract, contract_eq_delete_of_subset_loops], 
  rw [contract_cl, empty_union], 
  exact diff_subset_diff_left h.subset_cl, -/
end  

-- @[simp] lemma restrict_contract_eq_contract_restrict (M : matroid_in α) (R C : set α) :
--   (M ‖ R) ⟋ C = (M ⟋ (R ∩ C)) ‖ (R \ C) :=   
-- begin
--   refine eq_of_coe_eq_coe _ (lrestr_project_eq_project_lrestr _ _ _), 
--   ext, 
--   simp only [contract_ground, restrict_ground, mem_diff, mem_inter_iff, not_and], 
--   tauto 
-- end 

-- lemma restrict_contract_eq_contract_restrict_of_subset (M : matroid_in α) (h : C ⊆ R) :
--   (M ‖ R) ⟋ C = (M ⟋ C) ‖ (R \ C) :=   
-- by rw [restrict_contract_eq_contract_restrict, inter_eq_self_of_subset_right h]

-- lemma restrict_contract_eq_restrict_contract_inter (M : matroid_in α) (R C : set α) : 
--   (M ‖ R) ⟋ C = M ‖ R ⟋ (C ∩ R) :=
-- begin
--   refine eq_of_coe_eq_coe _ (lrestr_project_eq_lrestr_project_inter _ _ _), 
--   ext, 
--   simp only [restrict_contract_eq_contract_restrict, restrict_ground, contract_ground, 
--     mem_inter_iff, mem_diff, not_and, diff_inter_self_eq_diff], 
--   tauto,
-- end 

-- lemma contract_restrict_eq_restrict_contract (M : matroid_in α) (R C : set α) : 
--   (M ⟋ C) ‖ R = (M ‖ (R ∪ C)) ⟋ C := 
-- begin
--   refine eq_of_coe_eq_coe _ (project_lrestr_eq_lrestr_project _ _ _ ), 
--   ext, simp only [restrict_ground, contract_ground, mem_inter_iff, mem_diff, 
--     union_diff_right, mem_union], 
--   tauto
-- end  

-- lemma contract_restrict_eq_contract_restr_diff (M : matroid_in α) (R C : set α) :
--   (M ⟋ C) ‖ R = (M ⟋ C) ‖ (R \ C) :=
-- begin
--   refine eq_of_coe_eq_coe _ (project_lrestr_eq_project_lrestr_diff _ _ _),
--   ext, 
--   simp only [restrict_ground, contract_ground, mem_inter_iff, mem_diff, and.congr_right_iff], 
--   tauto, 
-- end 

-- -- ### Skewness and minors 

-- lemma contract_restrict_eq_restrict_iff_skew_coe (hCR : disjoint C R): 
--   (M ⟋ C) ‖ R = M ‖ R ↔ (M : matroid α).skew C R :=
-- begin
--   rw [matroid.skew, ←eq_iff_coe_eq_coe],  
--   simp only [restrict_ground, contract_ground, restrict_coe, contract_coe, and_iff_right_iff_imp], 
--   rintro -, 
--   rw [diff_eq, inter_right_comm, inter_eq_left_iff_subset, subset_compl_iff_disjoint_left],  
--   exact disjoint_of_subset_right (inter_subset_right _ _) hCR, 
-- end

-- lemma skew_iff_contract_restrict_eq_restrict (hC : C ⊆ M.E) (hR : R ⊆ M.E) (hCR : disjoint C R) :
--   M.skew C R ↔ (M ⟋ C) ‖ R = M ‖ R  :=
-- by { rw [contract_restrict_eq_restrict_iff_skew_coe hCR], exact ⟨skew.to_coe, λ h, ⟨h,hC,hR⟩⟩ }

-- lemma skew_of_indep_contract (hC : C ⊆ M.E) (hI : (M ⟋ C).indep I) : M.skew I C := 
-- begin
--   rw skew.comm, 
--   simp_rw [skew, matroid.skew, and_iff_right hC, 
--     and_iff_left (hI.subset_ground.trans (diff_subset _ _)), 
--     lrestr_eq_lrestr_iff, ←contract_coe, ← indep_iff_coe], 
--   refine λ J hJI, _, 
--   rw [iff_true_intro (hI.subset hJI), true_iff], 
--   exact hI.of_contract.subset hJI, 
-- end 

-- lemma contract_skew_of_skew (hXC : disjoint X C) (hYC : disjoint Y C) (h : M.skew X (Y ∪ C)) : 
--   (M ⟋ C).skew X Y :=
-- begin
--   rw [skew.comm, skew, contract_ground, subset_diff, and_iff_left hYC, subset_diff, 
--     and_iff_left hXC, and_iff_left h.left_subset_ground, 
--     and_iff_left ((subset_union_left _ _).trans h.right_subset_ground)],  
--   refine project_skew_of_union_skew _, 
--   rw [union_comm, matroid.skew.comm], 
--   exact h.to_coe,
-- end 

-- -- lemma disjoint_contract_of_eq_contract_restr {M₀ : matroid_in α} (h : M₀ = (M ⟋ C) ‖ M₀.E) : 
-- --   disjoint M₀.E C := 
-- -- begin
-- --   rw [h, restrict_ground, contract_ground, inter_comm, diff_eq, ←inter_assoc, ←diff_eq], 
-- --   exact disjoint_sdiff_left, 
-- -- end 

-- -- lemma subset_ground_of_eq_contract_restr {M₁ : }

-- end con_del

-- section restriction

-- variables {M₀ M : matroid_in α}

-- /-- M₀ is a `restriction` of `M` if `M₀ = M ‖ M₀.E`. We write `M₀ ≤r M`. -/
-- def restriction (M₀ M : matroid_in α) := M₀ = M ‖ M₀.E  

-- infix ` ≤r ` :50 := restriction

-- lemma restriction.left_eq (h : M₀ ≤r M) : M₀ = M ‖ M₀.E := h 

-- lemma restriction.subset (h : M₀ ≤r M) : M₀.E ⊆ M.E := 
-- by { rw [h.left_eq, restrict_ground], apply inter_subset_left } 

-- @[simp] lemma restriction.refl (M : matroid_in α) : M ≤r M := by simp [restriction]

-- lemma restriction.trans ⦃M₀ M₁ M₂ : matroid_in α⦄ (h₀ : M₀ ≤r M₁) (h₁ : M₁ ≤r M₂) : M₀ ≤r M₂ :=
-- by rw [h₀.left_eq, h₁.left_eq, restrict_restrict, restriction, restrict_ground, 
--     inter_eq_self_of_subset_right ((inter_subset_left _ _).trans h₁.subset)]
    
-- lemma restriction.antisymm ⦃M₁ M₂ : matroid_in α⦄ (h₁ : M₁ ≤r M₂) (h₂ : M₂ ≤r M₁) : M₁ = M₂ :=
-- by rw [h₁.left_eq, h₂.left_eq, restrict_restrict_of_subset _ h₁.subset, 
--     h₁.subset.antisymm h₂.subset]

-- /-- `≤r` is a partial order on `matroid_in α` -/
-- instance {α : Type*} : is_partial_order (matroid_in α) (≤r) := 
-- { refl := restriction.refl,
--   trans := restriction.trans,
--   antisymm := restriction.antisymm }

-- @[simp] lemma restrict_restriction (M : matroid_in α) (R : set α) : M ‖ R ≤r M :=  
-- by rw [restriction, restrict_ground, restrict_eq_restrict_inter_ground, inter_comm]

-- @[simp] lemma delete_restriction (M : matroid_in α) (D : set α) : M ⟍ D ≤r M := 
-- by { rw delete_eq_restrict, apply restrict_restriction }   

-- lemma restriction.indep_of_indep {I : set α} (h : M₀ ≤r M) (hI : M₀.indep I) : M.indep I :=
-- by { rw [h.left_eq] at hI, exact hI.of_restrict }

-- lemma ground_disjoint_of_restriction_contract {C : set α} (h : M₀ ≤r (M ⟋ C)) : disjoint M₀.E C :=
-- begin
--   rw [h.left_eq, restrict_ground, contract_ground], 
--   exact disjoint_of_subset_left (inter_subset_left _ _) disjoint_sdiff_left, 
-- end 

-- end restriction

-- section minor

-- variables {M M₀ M₁ M₂ : matroid_in α} {C D I R X Y Z : set α}

-- /-- The minor order on `matroid_in α`; we write `M₀ ≤ M` if `M₀ = M ⟋ C ⟍ D` where `C,D` are 
--   disjoint subsets of `M.E` -/
-- instance {α : Type*} : partial_order (matroid_in α) := 
-- { le := λ M₀ M, ∃ (C ⊆ M.E), M₀ ≤r M ⟋ C,
--   le_refl := λ M, ⟨∅, by simp⟩,
--   le_trans :=
--   begin
--     rintro M₀ M₁ M₂ ⟨C₁, hC₁, h₁⟩ ⟨C₂,hC₂, h₂⟩, 
--     rw [h₂.left_eq, restrict_contract_eq_contract_restrict, contract_contract] at h₁, 
--     exact ⟨_, union_subset hC₂ ((inter_subset_left _ _).trans (h₂.subset.trans (diff_subset _ _))), 
--       h₁.trans (restrict_restriction _ _)⟩,    
--   end, 
--   le_antisymm := 
--   begin
--     rintro M₁ M₂ ⟨C₁, hC₁, h₁⟩ ⟨C₂, hC₂, h₂⟩, 
--     have h₂' : C₂ = ∅, 
--     { have con := h₁.subset.trans ((diff_subset _ _).trans h₂.subset),
--       rwa [contract_ground, subset_diff, and_iff_right subset.rfl, 
--         disjoint.comm, disjoint_iff_inter_eq_empty, inter_eq_self_of_subset_left hC₂] at con,  },
--     rw [h₂', contract_empty] at h₂, 
--     have h₁' : C₁ = ∅, 
--     { have con := (h₂.trans h₁).subset, 
--       rwa [contract_ground, subset_diff, and_iff_right subset.rfl, 
--         disjoint.comm, disjoint_iff_inter_eq_empty, inter_eq_self_of_subset_left hC₁] at con, }, 
--     rw [h₁', contract_empty] at h₁, 
--     exact h₁.antisymm h₂, 
--   end }

-- @[simp] lemma restriction.minor (h : M₀ ≤r M) : M₀ ≤ M := ⟨∅, by simpa⟩    

-- @[simp] lemma contract_minor (M : matroid_in α) : (M ⟋ C) ≤ M := 
-- begin
--   refine ⟨C ∩ M.E, inter_subset_right _ _, _⟩, 
--   rw [contract_eq_contract_inter_ground], 
--   exact restriction.refl _, 
-- end 
 
-- @[simp] lemma restrict_minor (M : matroid_in α) (R : set α) : M ‖ R ≤ M := 
--   (restrict_restriction _ _).minor

-- @[simp] lemma delete_minor (M : matroid_in α) : (M ⟍ D) ≤ M := (delete_restriction _ _).minor  

-- @[simp] lemma contract_restrict_minor (M : matroid_in α) (C R : set α) : (M ⟋ C) ‖ R ≤ M := 
-- (restrict_restriction _ _).minor.trans (contract_minor _)

-- /-- Contracting and deleting any set gives a minor, even if the contractions and deletions are 
--   not well-defined (i.e. they overlap or are not contained in the ground set) -/
-- @[simp] lemma contract_delete_minor (M : matroid_in α) (C D : set α) : (M ⟋ C ⟍ D) ≤ M := 
-- (delete_restriction _ _).minor.trans (contract_minor _)

-- lemma minor.ground_subset (h : M₀ ≤ M) : M₀.E ⊆ M.E := 
-- by { obtain ⟨C, hC, h⟩ := h, exact h.subset.trans (diff_subset _ _) }

-- /-- Every minor is obtained by contracting an independent set and then restricting -/
-- lemma exists_indep_contr_of_minor (h : M₀ ≤ M) : 
--   ∃ I, M.indep I ∧ M₀ ≤r M ⟋ I := 
-- begin
--   obtain ⟨C, hC, h⟩ := h, 
--   obtain ⟨I, hI⟩ := M.exists_basis hC, 
--   rw hI.contract_eq at h, 
--   exact ⟨I, hI.indep, h.trans (delete_restriction _ _)⟩,  
-- end   

-- theorem minor.exists_indep_contract_spanning_restriction (h : M₀ ≤ M) :
--   ∃ (I : set α), M.indep I ∧ disjoint I M₀.E ∧ (M ⟋ I).cl M₀.E = (M ⟋ I).E ∧ M₀ ≤r M ⟋ I :=
-- begin
--   have h₀ := minor.ground_subset h, 
--   obtain ⟨I, hI, hr⟩ := exists_indep_contr_of_minor h, 
  
--   obtain ⟨B₀,hB₀⟩ := M₀.exists_base,  
--   have hB₀i := hr.indep_of_indep hB₀.indep, 
  
--   have hsk := skew_of_indep_contract hI.subset_ground (hr.indep_of_indep hB₀.indep), 
--   have hdj := hsk.disjoint_of_indep_right hI, 
--   have hB₀I := hsk.union_indep hB₀i.of_contract hI, 

--   obtain ⟨B, hB, hssB⟩ := hB₀I.exists_base_supset, 

--   have hdj' : disjoint (B \ B₀) M₀.E,   
--   { rw [disjoint_iff_inter_eq_empty, ←inter_eq_self_of_subset_right hr.subset, contract_ground, 
--       diff_eq M.E, inter_right_comm, inter_eq_self_of_subset_right h₀, ←diff_eq, 
--       eq_empty_iff_forall_not_mem],  

--     simp_rw [mem_inter_iff, not_and], 
--     rintro e ⟨heB, heB₀⟩ ⟨heM₀, heI⟩, 
--     refine hB₀.insert_dep heB₀ _,
--     rw [hr.left_eq, restrict_indep_iff, contract_indep_iff hI, subset_diff, and_comm (_ ⊆ _), 
--       and_assoc, and_assoc, ←subset_inter_iff, inter_eq_self_of_subset_right h₀, insert_subset, 
--       and_iff_right heM₀, and_iff_left hB₀.subset_ground, ←union_singleton, disjoint_union_left, 
--       disjoint_singleton_left, and_iff_right (hsk.disjoint_of_indep_right hI), and_iff_left heI, 
--       union_singleton, insert_union],
--      exact hB.indep.subset (insert_subset.mpr ⟨heB, hssB⟩) },
--   refine ⟨B \ B₀, hB.indep.diff _, hdj', _, _⟩, 
  
--   { simp only [contract_cl, contract_ground], 
--     refine (diff_subset_diff_left (M.cl_subset_ground _)).antisymm _,
--     rw [diff_subset_iff, union_diff_cancel 
--       (subset_cl_of_subset ((diff_subset _ _).trans hB.subset_ground) (subset_union_right _ _)),  
--       union_diff_cancel_of_subset _ hB₀.subset_ground, ←cl_union_cl_right_eq_cl, hB.cl, 
--       union_eq_self_of_subset_left h₀], 
--     exact subset_cl subset.rfl }, 
  
--   rw [restriction], 
--   nth_rewrite 0 [hr.left_eq],
--   rw [← union_diff_cancel ((subset_diff.mpr ⟨(subset_union_right _ _).trans hssB, hdj.symm⟩)), 
--     ←contract_contract, diff_diff, eq_comm, ←skew_iff_contract_restrict_eq_restrict _ hr.subset], 
--   { apply contract_skew_of_skew _ _ _, 
--     { exact disjoint_of_subset_right (subset_union_right _ _) disjoint_sdiff_left },
--     { exact ground_disjoint_of_restriction_contract hr }, 
--       have hcl : M₀.E ∪ I ⊆ M.cl (B₀ ∪ I), 
--       { rintro e (he | heI),
--       { have h' := hB₀.cl.symm.subset he,
--         rw [hr.left_eq, restrict_cl _ hB₀.subset_ground, contract_cl, diff_eq, inter_assoc] at h',
--         exact h'.1 },
--       exact (M.cl_subset (subset_union_right _ _)) (subset_cl hI.subset_ground heI) }, 
--       exact  (hB.indep.skew_diff_of_subset hssB).symm.cl_right.subset_right hcl },
--   { exact disjoint_of_subset_left (diff_subset_diff_right (subset_union_left _ _)) hdj' },
--   rw [diff_subset_iff, contract_ground, union_assoc, union_diff_self, ←union_assoc ], 
--   exact subset_union_of_subset_right hB.subset_ground _, 
-- end 

-- /-- The scum theorem : every minor is obtained by contracting an independent set and deleting a 
--   coindependent set -/
-- theorem scum (h : M₀ ≤ M) : 
--   ∃ (I X : set α), M ⟋ I ⟍ X = M₀ ∧ M.indep I ∧ M.coindep X ∧ disjoint I X := 
-- begin
--   obtain ⟨I, hI, hIM₀, hE, hle⟩ := minor.exists_indep_contract_spanning_restriction h,  
--   have h₀ := minor.ground_subset h, 
--   refine ⟨I, M.E \ I \ M₀.E, _, hI, _, _⟩,   
--   { nth_rewrite 1 [hle.left_eq], 
--     rw [delete_eq_restrict, restrict_eq_restrict_inter_ground], 
--     convert rfl, 
--     rw [contract_ground,  diff_eq, diff_eq, compl_inter, compl_inter, compl_compl, compl_compl, 
--       inter_distrib_right, ←inter_assoc, ←inter_assoc, inter_eq_self_of_subset_left h₀, 
--       inter_distrib_right, compl_inter_self, empty_union, inter_right_comm, inter_compl_self, 
--       empty_inter, empty_union, ←diff_eq, eq_comm, sdiff_eq_left],
--     exact ground_disjoint_of_restriction_contract hle },
--   { rw [coindep_iff_cl_compl_eq_ground, diff_diff, sdiff_sdiff_right_self, inf_eq_inter, 
--       inter_distrib_left, inter_eq_self_of_subset_right h₀, 
--       inter_eq_self_of_subset_right hI.subset_ground, union_comm],
--       { apply_fun (λ X, X ∪ I) at hE, 
--         simp only [contract_cl, diff_union_self, contract_ground] at hE, 
--         rwa [union_eq_self_of_subset_right hI.subset_ground, 
--           union_eq_self_of_subset_right] at hE,
--         refine subset_cl_of_subset hI.subset_ground (subset_union_right _ _),  },
--       rw diff_diff, 
--       exact diff_subset _ _},
--   rw [diff_diff],
--   exact disjoint_of_subset_left (subset_union_left _ _) (disjoint_sdiff_right), 
-- end

-- end minor

-- section flat

-- variables {M : matroid_in α} {X Y F C : set α} {e : α} {k : ℕ}

-- lemma flat_contract_iff (hC : C ⊆ M.E) : (M ⟋ C).flat F ↔ M.flat (F ∪ C) ∧ disjoint F C :=
-- begin
--   rw [flat_iff_cl_self, contract_cl, flat_iff_cl_self], 
--   refine ⟨λ h, ⟨_,_⟩, λ h, _⟩,
--   { nth_rewrite 1 ← h, 
--     rw [diff_union_self, @union_eq_self_of_subset_right _ (M.cl _)],
--     exact (subset_cl hC).trans (M.cl_subset (subset_union_right _ _)) },
--   { rw ←h, exact disjoint_sdiff_left },
--   rw [h.1, union_diff_right, sdiff_eq_left],
--   exact h.2,  
-- end 

-- lemma r_fin.flat_of_r_contract_iff (hC : M.r_fin C) : 
--   (M ⟋ C).flat_of_r k F ↔ M.flat_of_r (k + M.r C) (F ∪ C) ∧ disjoint F C :=
-- begin
--   simp_rw [flat_of_r_iff, flat_contract_iff hC.subset_ground, and_assoc, and.congr_right_iff, 
--     and_comm (disjoint _ _), ←and_assoc, and.congr_left_iff, hC.r_fin_contract_iff, 
--     r_fin_union_iff, and_iff_left hC, and_comm (M.r_fin F), ←and_assoc, and.congr_left_iff],  
--   refine λ hFC hdj hFC, _,
--   zify, 
--   rw [and_iff_left hdj, hFC.contract_r_cast_eq hC], 
--   exact ⟨λ h, by rw [←h, sub_add_cancel], λ h, by rw [h, add_sub_cancel]⟩,
-- end 

-- lemma flat_of_r_contract_iff [finite_rk M] (hC : C ⊆ M.E): 
--   (M ⟋ C).flat_of_r k F ↔ M.flat_of_r (k + M.r C) (F ∪ C) ∧ disjoint F C :=
-- r_fin.flat_of_r_contract_iff (to_r_fin hC)

-- lemma nonloop.point_of_contract_iff {P : set α} (he : M.nonloop e) : 
--   (M ⟋ e).point P ↔ M.line (insert e P) ∧ e ∉ P :=
-- by rw [contract_elem, point, (r_fin_singleton he.mem_ground).flat_of_r_contract_iff, 
--     union_singleton, he.r, one_add_one_eq_two, ←line, disjoint_singleton_right]


-- end flat

-- end matroid_in 

--
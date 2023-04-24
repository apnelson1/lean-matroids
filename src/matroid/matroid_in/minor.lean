import .basic

open_locale classical 
noncomputable theory

open matroid set 

variables {E α : Type*} 

namespace matroid_in 

section con_del

variables {I J C D B X Y Z R : set α} {M : matroid_in α}

/-- Contract a set from a `matroid_in α` to give a smaller `matroid_in α`-/
def contract (M : matroid_in α) (C : set α) : matroid_in α := 
{ ground := M.E \ C,
  carrier := (M : matroid α) ⟋ C,
  support := 
  begin
    simp only [project.cl_eq, empty_union, diff_eq_compl_inter, compl_inter, compl_compl], 
    exact union_subset (M.carrier.subset_cl C) 
      (M.support.trans (M.carrier.cl_mono (empty_subset _))),
  end }

/-- Restrict a `matroid_in α` to a smaller ground set. -/
def restrict (M : matroid_in α) (R : set α) : matroid_in α :=
⟨M.E ∩ R, M ‖ R, 
begin
  rw [lrestr.cl_eq, empty_inter, compl_inter],
  exact union_subset_union_left _ (compl_ground_subset_loops_coe _ ),  
end⟩  

def delete (M : matroid_in α) (D : set α) : matroid_in α := M.restrict Dᶜ 

instance {α : Type*} : has_con (matroid_in α) (set α) := ⟨matroid_in.contract⟩  
instance {α : Type*} : has_del (matroid_in α) (set α) := ⟨matroid_in.delete⟩
instance {α : Type*} : has_restr (matroid_in α) (set α) := ⟨matroid_in.restrict⟩  
instance {α : Type*} : has_con (matroid_in α) α := ⟨λ M e, M.contract {e}⟩  
instance {α : Type*} : has_del (matroid_in α) α := ⟨λ M e, M.delete {e}⟩  

@[simp] lemma contract_coe (M : matroid_in α) (C : set α) : 
  ((M ⟋ C : matroid_in α) : matroid α) = (M : matroid α) ⟋ C := rfl 

@[simp] lemma contract_elem (M : matroid_in α) (e : α) : M ⟋ e = M ⟋ ({e} : set α) := rfl  

@[simp] lemma contract_ground (M : matroid_in α) (C : set α): (M ⟋ C).E = M.E \ C := rfl 

@[simp] lemma delete_coe (M : matroid_in α) (D : set α) : 
  ((M ⟍ D : matroid_in α) : matroid α) = (M : matroid α) ⟍ D := rfl 

@[simp] lemma restrict_coe (M : matroid_in α) (R : set α) : 
  ((M ‖ R : matroid_in α) : matroid α) = (M : matroid α) ‖ R := rfl  

@[simp] lemma delete_elem (M : matroid_in α) (e : α) : M ⟍ e = M ⟍ ({e} : set α) := rfl 

@[simp] lemma delete_ground (M : matroid_in α) (D : set α) : (M ⟍ D).E = M.E \ D := rfl 

@[simp] lemma restrict_ground (M : matroid_in α) (R : set α) : (M ‖ R).E = M.E ∩ R := rfl

lemma restr_eq_del (M : matroid_in α) (R : set α) : M ‖ R = M ⟍ Rᶜ := 
by { change M ‖ R = M ‖ Rᶜᶜ, rw compl_compl } 

@[simp] lemma contract_contract (M : matroid_in α) (C₁ C₂ : set α) : M ⟋ C₁ ⟋ C₂ = M ⟋ (C₁ ∪ C₂) :=
eq_of_coe_eq_coe (by simp [diff_diff]) (by simp)

@[simp] lemma contract_empty (M : matroid_in α) : M ⟋ (∅ : set α) = M := 
eq_of_coe_eq_coe (by simp) (by simp)

@[simp] lemma delete_empty (M : matroid_in α) : M ⟍ (∅ : set α) = M := 
eq_of_coe_eq_coe (by simp) (by simp)

lemma contract_eq_self_of_disjoint_ground (hC : disjoint C M.E) : M ⟋ C = M := 
begin
  apply eq_of_coe_eq_coe, 
  rw [contract_ground, hC.sdiff_eq_right], 
  rw [contract_coe, project.eq_of_subset_loops], 
  exact subset_loops_coe_of_disjoint_ground hC, 
end 

lemma contract_eq_self_iff_disjoint_ground : M ⟋ C = M ↔ disjoint C M.E := 
⟨λ hM, by { rw ←hM, exact disjoint_sdiff_right }, contract_eq_self_of_disjoint_ground⟩

lemma delete_eq_self_of_disjoint_ground (hD : disjoint D M.E) : M ⟍ D = M := 
begin
  apply eq_of_coe_eq_coe, 
  rw [delete_ground, hD.sdiff_eq_right], 
  rw [delete_coe, loopify.eq_of_subset_loops], 
  exact subset_loops_coe_of_disjoint_ground hD, 
end 

lemma delete_eq_self_iff_disjoint_ground : M ⟍ C = M ↔ disjoint C M.E := 
⟨λ hM, by { rw ←hM, exact disjoint_sdiff_right }, delete_eq_self_of_disjoint_ground⟩
   
lemma contract_comm (M : matroid_in α) (C₁ C₂ : set α) : M ⟋ C₁ ⟋ C₂ = M ⟋ C₂ ⟋ C₁ :=
by rw [contract_contract, contract_contract, union_comm]
 
@[simp] lemma delete_delete (M : matroid_in α) (D₁ D₂ : set α) : M ⟍ D₁ ⟍ D₂ = M ⟍ (D₁ ∪ D₂) :=
eq_of_coe_eq_coe (by simp [diff_diff]) (by simp)

lemma delete_comm (M : matroid_in α) (D₁ D₂ : set α) : M ⟍ D₁ ⟍ D₂ = M ⟍ D₂ ⟍ D₁ :=
by rw [delete_delete, delete_delete, union_comm]

lemma delete_delete_diff (M : matroid_in α) (D₁ D₂ : set α) : M ⟍ D₁ ⟍ D₂ = M ⟍ D₁ ⟍ (D₂ \ D₁) :=
begin
  nth_rewrite 0 ←inter_union_diff D₂ D₁, 
  rw [union_comm, ←delete_delete, delete_eq_self_iff_disjoint_ground],  
  exact disjoint_of_subset (inter_subset_right _ _) (diff_subset _ _) (disjoint_sdiff_right), 
end 

lemma restr_eq_restr_inter (M : matroid_in α) (R : set α) : M ‖ R = M ‖ (R ∩ M.E) :=
begin 
  rw [restr_eq_del, restr_eq_del, compl_inter, ←delete_delete, eq_comm, 
    delete_eq_self_of_disjoint_ground], 
  exact disjoint_of_subset_right (diff_subset _ _) disjoint_compl_left, 
end 

lemma restr_eq_del_diff (M : matroid_in α) (R : set α) : M ‖ R = M ⟍ (M.E \ R) :=
begin
  rw [restr_eq_del], 
  nth_rewrite 0 ←inter_union_diff Rᶜ M.E, 
  rw [←diff_eq_compl_inter, ←delete_delete, delete_eq_self_iff_disjoint_ground], 
  exact disjoint_of_subset_right (diff_subset _ _) (disjoint_sdiff_left), 
end 

lemma contract_contract_diff (M : matroid_in α) (C₁ C₂ : set α) : 
  M ⟋ C₁ ⟋ C₂  = M ⟋ C₁ ⟋ (C₂ \ C₁)   :=
begin
  nth_rewrite 0 ←inter_union_diff C₂ C₁, 
  rw [union_comm, ←contract_contract, contract_eq_self_iff_disjoint_ground],  
  exact disjoint_of_subset (inter_subset_right _ _) (diff_subset _ _) (disjoint_sdiff_right), 
end 

lemma contract_delete_diff (M : matroid_in α) (C D : set α) : 
  M ⟋ C ⟍ D = M ⟋ C ⟍ (D \ C) := 
begin
  nth_rewrite 0 ←inter_union_diff D C,
  rw [union_comm, ←delete_delete, delete_eq_self_iff_disjoint_ground], 
  exact disjoint_of_subset (inter_subset_right _ _) (diff_subset _ _) (disjoint_sdiff_right), 
end  

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

@[simp] lemma delete_indep_iff : 
  (M ⟍ D).indep I ↔ M.indep I ∧ disjoint I D :=
by rw [indep_iff_coe, delete_coe, loopify.indep_iff, and_comm, indep_iff_coe]

@[simp] lemma delete_circuit_iff : 
  (M ⟍ D).circuit C ↔ M.circuit C ∧ disjoint C D :=
begin
  obtain (h | h) := em (disjoint C D), 
  { simp_rw [circuit, delete_coe, loopify.circuit_iff_of_disjoint h, iff_true_intro h, and_true],
    exact ⟨λ h', ⟨h'.1,h'.2.trans (diff_subset _ _)⟩, λ h', ⟨h'.1, subset_diff.mpr ⟨h'.2, h⟩⟩⟩ },
  rw [circuit, delete_ground, subset_diff], 
  simp [h], 
end 

lemma indep.delete_indep (hI : M.indep I) (hID : disjoint I D) : (M ⟍ D).indep I := 
delete_indep_iff.mpr ⟨hI,hID⟩  

lemma contract_eq_delete_of_subset_loops (M : matroid_in α) {X : set α} (hX : X ⊆ M.cl ∅) :
  M ⟋ X = M ⟍ X :=
begin
  refine eq_of_indep_iff_indep rfl (λ I (hI : I ⊆ M.E \ X), _), 
  rw subset_diff at hI, 
  rw [delete_indep_iff, indep_iff_coe, contract_coe, ←(true_iff _).mpr hI.2, and_true,
    project.eq_of_subset_loops (hX.trans (cl_subset_coe_cl _ _)), indep_iff_coe], 
end  

lemma contract_eq_delete_of_subset_coloops (M : matroid_in α) {X : set α} (hX : X ⊆ M﹡.cl ∅) :
  M ⟋ X = M ⟍ X :=
begin
  refine eq_of_coe_eq_coe rfl _,
  rw [contract_coe, delete_coe, project_eq_loopify_of_subset_coloops], 
end 

@[simp] lemma contract_cl (M : matroid_in α) (C X : set α) : (M ⟋ C).cl X = M.cl (X ∪ C) \ C :=
by rw [cl_eq_coe_cl_inter, contract_coe, project.cl_eq, contract_ground, cl_eq_coe_cl_inter, 
    diff_eq, diff_eq, inter_assoc]

lemma delete_cl (M : matroid_in α) (D X : set α) (h : disjoint X D) : (M ⟍ D).cl X = M.cl X \ D :=
by rw [cl_eq_coe_cl_inter, cl_eq_coe_cl_inter, delete_coe, loopify.cl_eq, delete_ground, 
  h.sdiff_eq_left, inter_distrib_right, inter_diff_self, union_empty, diff_eq, diff_eq, inter_assoc]

@[simp] lemma loops_delete (M : matroid_in α) (D : set α) : (M ⟍ D).cl ∅ = M.cl ∅ \ D :=
by { rw delete_cl, exact empty_disjoint _ }  

lemma contract_eq_contract_inter_ground (M : matroid_in α) (C : set α) : M ⟋ C = M ⟋ (C ∩ M.E) :=
begin
  nth_rewrite 0 ←inter_union_diff C M.E, 
  rw [←contract_contract, contract_eq_self_of_disjoint_ground], 
  rw [contract_ground], 
  exact disjoint_of_subset_right (diff_subset _ _) (disjoint_sdiff_left), 
end   

lemma delete_eq_delete_inter_ground (M : matroid_in α) (D : set α) : M ⟍ D = M ⟍ (D ∩ M.E) :=
begin 
  nth_rewrite 0 ←inter_union_diff D M.E, 
  rw [←delete_delete, delete_eq_self_of_disjoint_ground], 
  rw [delete_ground], 
  exact disjoint_of_subset_right (diff_subset _ _) (disjoint_sdiff_left), 
end   

lemma contract_cl_eq_contract_delete (M : matroid_in α) (C : set α) :
  M ⟋ (M.cl C) = M ⟋ C ⟍ (M.cl C \ C) :=
begin
  rw [←contract_eq_delete_of_subset_loops, contract_contract, union_diff_self, union_comm, 
    ←union_diff_self, ←contract_contract, eq_comm],
  refine contract_eq_self_of_disjoint_ground _, 
  { rw [contract_ground, cl_eq_coe_cl_inter, diff_inter, 
      diff_eq_empty.mpr (matroid.subset_cl (M : matroid α ) _), empty_union], 
    exact disjoint_of_subset_right (diff_subset _ _) disjoint_sdiff_left },
  rw [contract_cl, empty_union], 
end  

lemma basis.contract_eq (h : M.basis I X) : 
  M ⟋ X = M ⟋ I ⟍ (X \ I) :=
begin
  nth_rewrite 0 ←union_diff_cancel h.subset, 
  rw [←contract_contract, contract_eq_delete_of_subset_loops], 
  rw [contract_cl, empty_union], 
  exact diff_subset_diff_left h.subset_cl, 
end  

lemma indep.contract_indep_iff (hI : M.indep I) : 
  (M ⟋ I).indep J ↔ disjoint J I ∧ M.indep (J ∪ I)  :=
matroid.indep.project_indep_iff hI

@[simp] lemma delete_r_eq (M : matroid_in α) (D X : set α) : (M ⟍ D).r X = M.r (X \ D) :=
by rw [r_eq_coe_r, r_eq_coe_r, delete_coe, loopify.r_eq]

@[simp] lemma contract_r_cast_eq (M : matroid_in α) [M.finite_rk] (C X : set α) : 
  ((M ⟋ C).r X : ℤ)  = M.r (X ∪ C) - M.r C := 
by rw [r_eq_coe_r, contract_coe, project.cast_r, r_eq_coe_r, r_eq_coe_r]

-- ### Duality 

lemma contract_dual (M : matroid_in α) (X : set α) : (M ⟋ X)﹡ = M﹡ ⟍ X :=
begin
  suffices : ∀ Y ⊆ M.E, (M ⟋ Y)﹡ = M﹡ ⟍ Y, 
  { convert this (X ∩ M.E) (inter_subset_right _ _) using 1,
    rw [dual_inj_iff, contract_eq_contract_inter_ground],
    rw [delete_eq_delete_inter_ground, dual_ground] },
  refine λ Y hY, eq_of_indep_iff_indep rfl (λ I hI, _),  
  rw [dual_indep_iff_coindep, delete_indep_iff, dual_indep_iff_coindep, 
    coindep_iff_cl_compl_eq_ground, coindep_iff_cl_compl_eq_ground], 
  { rw [dual_ground, contract_ground] at hI, 
    have hXI := disjoint_of_subset_left hI disjoint_sdiff_left, 
    rw [iff_true_intro hXI, and_true, contract_ground, contract_cl, diff_diff, subset_antisymm_iff, 
      diff_subset_iff, union_diff_self, diff_subset_iff, union_diff_self,
      iff_true_intro (subset_union_of_subset_right (cl_subset_ground _ _) _), true_and, 
      union_eq_self_of_subset_left ((subset_cl hY).trans (cl_mono _ (subset_union_right _ _))), 
      diff_eq, union_distrib_right, union_eq_self_of_subset_right hY, compl_union, 
      union_distrib_right, compl_union_self, univ_inter, inter_distrib_left, 
      union_eq_self_of_subset_right, ←diff_eq, subset_antisymm_iff, 
      iff_true_intro (cl_subset_ground _ _), true_and],  
    exact (inter_subset_right _ _).trans 
      (subset_inter hY (subset_compl_iff_disjoint_left.mpr hXI)) },
  { refine hI.trans _, simp [diff_subset] },
  convert hI using 1
end 

lemma delete_dual (M : matroid_in α) (X : set α) : (M ⟍ X)﹡ = M﹡ ⟋ X :=
by rw [←dual_inj_iff, contract_dual, dual_dual, dual_dual]

@[simp] lemma contract_coindep_iff : (M ⟋ C).coindep X ↔ M.coindep X ∧ disjoint X C := 
by rw [←dual_indep_iff_coindep, contract_dual, delete_indep_iff, dual_indep_iff_coindep]

lemma coindep.contract_coindep (h : M.coindep X) (hdj : disjoint X C) : (M ⟋ C).coindep X :=
contract_coindep_iff.mpr ⟨h,hdj⟩  

-- ### Skewness and minors 

lemma contract_restr_eq_restr_iff_skew_coe (hCR : disjoint C R) : 
  (M ⟋ C) ‖ R = M ‖ R ↔ (M : matroid α).skew C R :=
begin
  rw [skew_iff_project_lrestrict_eq_lrestrict, ←contract_coe, ←restrict_coe, ←restrict_coe], 
  refine ⟨congr_arg _,λ h, eq_of_coe_eq_coe _ h⟩, 
  rw [restrict_ground, restrict_ground, contract_ground, diff_eq, inter_right_comm, ←diff_eq, 
    inter_diff_assoc, hCR.sdiff_eq_right], 
end

lemma skew_iff_contract_restr_eq_restr (hC : C ⊆ M.E) (hR : R ⊆ M.E) (hCR : disjoint C R) :
  M.skew C R ↔ (M ⟋ C) ‖ R = M ‖ R  :=
by { rw [contract_restr_eq_restr_iff_skew_coe hCR], exact ⟨skew.to_coe, λ h, ⟨h,hC,hR⟩⟩ }

lemma contract_skew_of_skew (hXZ : disjoint X Z) (hYZ : disjoint Y Z) (h : M.skew X (Y ∪ Z)) : 
  (M ⟋ Z).skew X Y :=
begin
  rw [skew_iff_r],  
  { have h' := h.r_add, 
    have h'' := (h.subset_right (subset_union_right _ _)).r_add, 
    zify at *, 
    simp_rw [contract_r_cast_eq, union_assoc, ←h', ←h''], 
    ring },
  all_goals { rw [contract_ground, subset_diff] }, 
  { exact ⟨h.left_subset_ground, hXZ⟩ },
  exact ⟨(subset_union_left _ _).trans h.right_subset_ground, hYZ⟩,
end 

end con_del

section minor

variables {M M₀ : matroid_in α} {C D I R X Y Z : set α}

/-- The minor order on `matroid_in α`; we write `M₀ ≤ M` if `M₀ = M ⟋ C ⟍ D` where `C,D` are 
  disjoint subsets of `M.E` -/
instance {α : Type*} [finite α] : partial_order (matroid_in α) := 
{ le := λ M₀ M, ∃ (C D : set α), (M₀ = M ⟋ C ⟍ D) ∧ disjoint C D ∧ C ⊆ M.E ∧ D ⊆ M.E ,
  le_refl := λ M, ⟨∅, ∅, by simp⟩  ,
  le_trans := 
  (begin
    rintro M₀ M₁ M₂ ⟨C₁,D₁,rfl,h₁',hC₁E,hD₁E⟩ ⟨C₂,D₂,rfl,h₂',hC₂E,hD₂E⟩,
    have hdj : disjoint (C₂ ∪ C₁) (D₂ ∪ D₁), 
    { simp only [disjoint_union_right, disjoint_union_left],
      refine ⟨⟨h₂', disjoint.symm (disjoint_of_subset_left hD₁E _)⟩, 
        ⟨disjoint_of_subset_left hC₁E (disjoint_sdiff_left),h₁'⟩⟩,     
      rw [contract_delete_comm _ h₂'], exact disjoint_sdiff_left},
    rw [contract_delete_comm, delete_delete, ←contract_delete_comm, contract_contract],
    { exact ⟨_,_,rfl,hdj,
        union_subset hC₂E (hC₁E.trans ((diff_subset _ _).trans (diff_subset _ _))),
        union_subset hD₂E (hD₁E.trans ((diff_subset _ _).trans (diff_subset _ _)))⟩ },
    { exact disjoint_of_subset_left (subset_union_right _ _) hdj},
    exact h₁',
  end),
  le_antisymm := 
  begin
    rintro M M₀ ⟨C,D,rfl,hdj,hC,hD⟩ ⟨C',D',h,hdj',hC',hD'⟩, 
    apply_fun E at h, 
    simp only [delete_ground, contract_ground, diff_diff, @eq_comm _ M₀.E, sdiff_eq_left, 
      union_assoc ] at h,  
    rw [←inter_eq_left_iff_subset, inter_comm, 
      (disjoint_of_subset_right (subset_union_left _ _) h).inter_eq] at hC, 
    rw [← union_assoc, union_comm C, union_assoc ] at h, 
    rw [←inter_eq_left_iff_subset, inter_comm, 
      (disjoint_of_subset_right (subset_union_left _ _) h).inter_eq] at hD, 
    simp [←hC,←hD], 
  end } 

/-- Contracting and deleting any set gives a minor, even if the contractions and deletions are 
  not well-defined (i.e. they overlap or are not contained in the ground set) -/
lemma con_del_minor (M : matroid_in α) (C D : set α) : M ⟋ C ⟍ D ≤ M :=   
begin
  use [C ∩ M.E, (D \ C) ∩ M.E], 
  simp only [inter_subset_right, true_and, and_true], 
  split, 
  { rw [delete_eq_delete_inter_ground, contract_ground, diff_eq, inter_comm M.E, ←inter_assoc, 
    diff_eq, contract_eq_contract_inter_ground] },
  exact disjoint_of_subset (inter_subset_left _ _) (inter_subset_left _ _) (disjoint_sdiff_right),  
end 

lemma ground_subset_ground_of_minor (h : M₀ ≤ M) : M₀.E ⊆ M.E := 
by { obtain ⟨C,D,rfl,h⟩ := h, exact (diff_subset _ _).trans (diff_subset _ _) } 

lemma con_minor (M : matroid_in α) (C : set α) : M ⟋ C ≤ M := by simpa using con_del_minor M C ∅ 

lemma del_minor (M : matroid_in α) (D : set α) : M ⟍ D ≤ M := by simpa using con_del_minor M ∅ D

lemma restr_minor (M : matroid_in α) (R : set α) : M ‖ R ≤ M := del_minor _ _

lemma con_restr_minor (M : matroid_in α) (C R : set α) : (M ⟋ C) ‖ R ≤ M := con_del_minor _ _ _

/-- Every minor is obtained by contracting an independent set and then restricting -/
lemma exists_indep_contr_of_minor (h : M₀ ≤ M) : 
  ∃ I, M₀ = (M ⟋ I) ‖ M₀.E ∧ M.indep I ∧ disjoint I M₀.E := 
begin
  obtain ⟨C, D, rfl, hdj, hC, hD⟩ := h, 
  obtain ⟨I, hI⟩ := M.exists_basis hC, 
  refine ⟨I, _, hI.indep, _⟩, 
  { rw [hI.contract_eq, delete_ground, delete_delete, delete_ground, contract_ground, diff_diff, 
      diff_diff, ←union_assoc, union_diff_cancel hI.subset, restr_eq_del, diff_eq M.E,  
      compl_inter, compl_compl, ←delete_delete _ M.Eᶜ, ←delete_delete, ←contract_delete_diff,
      delete_delete, delete_eq_self_of_disjoint_ground (_ : disjoint M.Eᶜ (M ⟋ I).E)], 
    exact disjoint_of_subset_right (diff_subset _ _) disjoint_compl_left },
  simp_rw [delete_ground, contract_ground], 
  exact disjoint_of_subset_left hI.subset 
    (disjoint_of_subset_right (diff_subset _ _) disjoint_sdiff_right), 
end   

/-- Every minor is obtained by contracting an independent set and then restricting to a 
  spanning set-/
theorem exists_indep_contract_spanning_restr_of_minor (h : M₀ ≤ M) :
  ∃ (I : set α), M₀ = M ⟋ I ‖ M₀.E ∧ M.indep I ∧ disjoint I M₀.E ∧ (M ⟋ I).cl M₀.E = (M ⟋ I).E :=
begin
  have h0 : ∃ I₀, M.indep I₀ ∧ M₀ ≤ M ⟋ I₀ ∧ disjoint I₀ M₀.E, 
    from ⟨∅, (M : matroid α).empty_indep, by simpa⟩, 
  obtain ⟨I, ⟨hI,h1,hIdj⟩, hImax⟩ := finite.exists_maximal _ h0, 
  obtain ⟨I', hM₀, hI', hI'E⟩ := exists_indep_contr_of_minor h1, 

  have hI'_empty : I' = ∅, 
  { have hu := hImax (I ∪ I') ⟨_,_⟩ (subset_union_left _ _), 
    { have h' := subset_inter hI'.subset_ground (by { rw hu, apply subset_union_right } : I' ⊆ I), 
      rwa [contract_ground, diff_inter_self, subset_empty_iff] at h' },
    { rw [hI.contract_indep_iff, union_comm] at hI', exact hI'.2 },
    rw [hM₀, contract_contract, restrict_ground, contract_ground], 
    exact ⟨restr_minor _ _, 
      disjoint_of_subset_right (inter_subset_left _ _) disjoint_sdiff_right⟩ },
  
  subst hI'_empty, 
  rw contract_empty at hM₀, 
  simp_rw [contract_cl],

  refine ⟨I, hM₀, hI, hIdj, (diff_subset_diff_left (M.cl_subset_ground _)).antisymm (λ e he, _)⟩,  
  by_contra h', 
  simp only [mem_diff, not_and, not_not_mem] at h', 
  have he' : e ∉ M.cl (M₀.E ∪ I), from λ he', he.2 (h' he'), 
  have hnl := nonloop_of_not_mem_cl he.1 he', 
  have hsk := (hnl.singleton_skew_iff 
    (union_subset (ground_subset_ground_of_minor h) hI.subset_ground)).mpr he', 
  
  have hsk_con := contract_skew_of_skew (disjoint_singleton_left.mpr he.2) hIdj.symm hsk, 
  have he₀ : e ∉ M₀.E, 
  { refine not_mem_subset ((subset_union_left _ _).trans (subset_cl _)) he', 
    exact union_subset (ground_subset_ground_of_minor h) hI.subset_ground },

  have hIe : M.indep (insert e I), 
  { rw [indep_iff_coe, hI.to_coe.insert_indep_iff_of_not_mem he.2, cl_coe_eq, mem_union, 
      not_or_distrib, not_mem_compl_iff],
    exact ⟨not_mem_subset (M.cl_mono (subset_union_right _ _)) he', hnl.mem_ground⟩ },

  rw [skew_iff_contract_restr_eq_restr, contract_contract, union_singleton, ←hM₀] at hsk_con, 
  { rw hImax _ ⟨hIe,_,_⟩ (subset_insert _ _) at he, 
    { exact he.2 (mem_insert _ _) },
    { rw ←hsk_con, exact restr_minor _ _ },
    rw [←union_singleton, disjoint_union_left, disjoint_singleton_left],
    exact ⟨hIdj, he₀⟩ },
  { rwa [singleton_subset_iff, contract_ground] },
  { rw [hM₀], simp, },
  rw [disjoint_singleton_left], 
  exact he₀, 
end 
 
/-- The scum theorem : every minor is obtained by contracting an independent set and deleting a 
  coindependent set -/
theorem scum (h : M₀ ≤ M) : 
  ∃ (I X : set α), M ⟋ I ⟍ X = M₀ ∧ M.indep I ∧ M.coindep X ∧ disjoint I X := 
begin
  obtain ⟨I, hM₀, hI, hdj, hcl⟩ := exists_indep_contract_spanning_restr_of_minor h, 
  refine ⟨I, M.E \ I \ M₀.E, _, hI,_,_⟩, 
  { nth_rewrite 1 hM₀, rw [restr_eq_del_diff], refl }, 
  { suffices : (M ⟋ I).coindep (M.E \ I \ M₀.E), 
    { rw contract_coindep_iff at this, exact this.1},
    rw [coindep_iff_cl_compl_eq_ground],
    { convert hcl,
      simp only [contract_ground, sdiff_sdiff_right_self, inf_eq_inter, 
        inter_eq_right_iff_subset, subset_diff],
      exact ⟨ground_subset_ground_of_minor h, hdj.symm⟩ },
    exact diff_subset _ _ },
  exact disjoint_of_subset_right (diff_subset _ _) (disjoint_sdiff_right), 
end

end minor

end matroid_in 

import .basic

open_locale classical 
noncomputable theory

open matroid set 

variables {E α : Type*} [finite E] [finite α] 

namespace matroid_in 

section con_del

variables {I J C D B X Y : set α} {M : matroid_in α}

/-- Contract a set from a `matroid_in α` to give a smaller `matroid_in α`-/
def contract (M : matroid_in α) (C : set α) : matroid_in α := 
{ ground := M.E \ C,
  carrier := (M : matroid α) ⟋ C,
  support := 
  begin
    simp only [project_cl_eq, empty_union, diff_eq_compl_inter, compl_inter, compl_compl], 
    exact union_subset (M.carrier.subset_cl C) 
      (M.support.trans (M.carrier.cl_mono (empty_subset _))),
  end }

/-- Delete a set from a `matroid_in α` to give a smaller `matroid_in α` -/
def delete (M : matroid_in α) (D : set α) : matroid_in α := 
{ ground := M.E \ D,
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

@[simp] lemma restrict_ground (M : matroid_in α) (R : set α) : (M ‖ R).E = M.E ∩ R := diff_compl

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
  rw [contract_coe, project_eq_of_loops], 
  exact subset_loops_coe_of_disjoint_ground hC, 
end 

lemma contract_eq_self_iff_disjoint_ground : M ⟋ C = M ↔ disjoint C M.E := 
⟨λ hM, by { rw ←hM, exact disjoint_sdiff_right }, contract_eq_self_of_disjoint_ground⟩

lemma delete_eq_self_of_disjoint_ground (hD : disjoint D M.E) : M ⟍ D = M := 
begin
  apply eq_of_coe_eq_coe, 
  rw [delete_ground, hD.sdiff_eq_right], 
  rw [delete_coe, loopify_eq_of_loops], 
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

@[simp] lemma delete_indep_iff (D : set α) : 
  (M ⟍ D).indep I ↔ M.indep I ∧ I ⊆ M.E \ D :=
begin
  rw [indep_iff_coe, indep_iff_coe, delete_coe, indep_loopify_iff, and_comm, subset_diff], 
  exact ⟨λ h, ⟨h.1, indep.subset_ground (h.1),h.2⟩, λ h, ⟨h.1, h.2.2⟩⟩, 
end    

lemma contract_eq_delete_of_subset_loops (M : matroid_in α) {X : set α} (hX : X ⊆ M.cl ∅) :
  M ⟋ X = M ⟍ X :=
begin
  refine eq_of_indep_iff_indep rfl (λ I (hI : I ⊆ M.E \ X), _), 
  rw [delete_indep_iff, ←(true_iff _).mpr hI, and_true, indep_iff_coe, indep_iff_coe, 
    contract_coe, project_eq_of_loops (hX.trans (cl_subset_coe_cl _ _))], 
end  

@[simp] lemma contract_cl (M : matroid_in α) (C X : set α) : (M ⟋ C).cl X = M.cl (X ∪ C) \ C :=
by rw [cl_eq_coe_cl_inter, contract_coe, project_cl_eq, contract_ground, cl_eq_coe_cl_inter, 
    diff_eq, diff_eq, inter_assoc]

lemma delete_cl (M : matroid_in α) (D X : set α) (h : disjoint X D) : (M ⟍ D).cl X = M.cl X \ D :=
by rw [cl_eq_coe_cl_inter, cl_eq_coe_cl_inter, delete_coe, loopify_cl_eq, delete_ground, 
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
    ←union_diff_self, ←contract_contract, @contract_eq_self_of_disjoint_ground _ _ _ (M ⟋ M.cl C)],  
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
by rw [r_eq_coe_r, r_eq_coe_r, delete_coe, r_loopify]

@[simp] lemma contract_r_cast_eq (M : matroid_in α) (C X : set α) : 
  ((M ⟋ C).r X : ℤ)  = M.r (X ∪ C) - M.r C := 
by simp_rw [r_eq_coe_r, contract_coe, coe_r_project]

lemma contract_dual (M : matroid_in α) (X : set α) : 
  (M ⟋ X)* = M* ⟍ X :=
begin
  rw [contract_eq_contract_inter_ground, delete_eq_delete_inter_ground, dual_ground], 
  set A := X ∩ M.E with hA, 
  refine eq_of_r_eq_r rfl (λ Z (hZ : Z ⊆ M.E \ A), _), 
  zify, 
  rw [dual_r_cast_eq, rk_eq_r_ground, delete_r_eq, dual_r_cast_eq, contract_r_cast_eq, 
    contract_ground, contract_r_cast_eq, diff_union_self, diff_diff_right,
    union_eq_left_iff_subset.mpr (inter_subset_right _ _), diff_diff_comm, 
    inter_eq_right_iff_subset.mpr (inter_subset_right _ _), ←hA, diff_union_self, 
    (sdiff_eq_left.mpr _ : Z \ A = Z), rk_eq_r_ground], 
  { linarith},
  { exact disjoint_of_subset_left hZ disjoint_sdiff_left },
  { rw diff_subset_iff, exact hZ.trans ((diff_subset _ _).trans (subset_union_right _ _))}, 
  exact hZ, 
end 

lemma delete_dual (M : matroid_in α) (X : set α) : 
  (M ⟍ X)* = M* ⟋ X :=
by rw [←dual_inj_iff, contract_dual, dual_dual, dual_dual]

end con_del

section minor

variables {M M' M₀ : matroid_in α} {C D R X Y : set α}

/-- The minor order on `matroid_in α` -/
instance {α : Type*} [finite α] : partial_order (matroid_in α) := 
{ le := λ M' M, ∃ (C D : set α), (M' = M ⟋ C ⟍ D) ∧ disjoint C D ∧ C ⊆ M.E ∧ D ⊆ M.E ,
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
    rintro M M' ⟨C,D,rfl,hdj,hC,hD⟩ ⟨C',D',h,hdj',hC',hD'⟩, 
    apply_fun E at h, 
    simp only [delete_ground, contract_ground, diff_diff, @eq_comm _ M'.E, sdiff_eq_left, 
      union_assoc ] at h,  
    rw [←inter_eq_left_iff_subset, inter_comm, 
      (disjoint_of_subset_right (subset_union_left _ _) h).inter_eq] at hC, 
    rw [← union_assoc, union_comm C, union_assoc ] at h, 
    rw [←inter_eq_left_iff_subset, inter_comm, 
      (disjoint_of_subset_right (subset_union_left _ _) h).inter_eq] at hD, 
    simp [←hC,←hD], 
  end } 

/-- Contracting and deleting any set gives a minor, even if they overlap or are not contained in the 
  ground set -/
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

lemma contract_restr_eq_restr_iff_skew_coe (hCR : disjoint C R) : 
  (M ⟋ C) ‖ R = M ‖ R ↔ (M : matroid α).skew C R :=
begin
  rw [skew_iff_project_lrestrict_eq_lrestrict, ←contract_coe, ←restrict_coe, ←restrict_coe], 
  refine ⟨congr_arg _,λ h, eq_of_coe_eq_coe _ h⟩, 
  rw [restrict_ground, restrict_ground, contract_ground, diff_eq, inter_right_comm, ←diff_eq, 
    inter_diff_assoc, hCR.sdiff_eq_right], 
end

lemma exists_indep_contr_of_minor (h : M₀ ≤ M) : ∃ I, M.indep I ∧ M₀ = (M ⟋ I) ‖ M₀.E := 
begin
  obtain ⟨C, D, rfl, hdj, hC, hD⟩ := h, 
  obtain ⟨I, hI⟩ := M.exists_basis hC, 
  refine ⟨I, hI.indep, _⟩, 
  rw [hI.contract_eq, delete_ground, delete_delete, delete_ground, contract_ground, diff_diff, 
    diff_diff, ←union_assoc, union_diff_cancel hI.subset, restr_eq_del, diff_eq M.E,  
    compl_inter, compl_compl, ←delete_delete _ M.Eᶜ, ←delete_delete, ←contract_delete_diff,
    delete_delete, delete_eq_self_of_disjoint_ground (_ : disjoint M.Eᶜ (M ⟋ I).E)], 
  exact disjoint_of_subset_right (diff_subset _ _) disjoint_compl_left, 
end   

lemma skew_iff_contract_restr_eq_restr (hC : C ⊆ M.E) (hR : R ⊆ M.E) (hCR : disjoint C R) :
  M.skew C R ↔ (M ⟋ C) ‖ R = M ‖ R  :=
begin
  rw [contract_restr_eq_restr_iff_skew_coe hCR], 
  exact ⟨skew.to_coe, λ h, ⟨h,hC,hR⟩⟩, 
end 

lemma union_skew_iff_contract : 
  (M ⟋ C).skew X Y ↔ M.skew (X ∪ C) (Y ∪ C) :=
begin
  
  -- simp_rw [skew_iff_r], 
end 


lemma scum_restr (h : M₀ ≤ M) :
  ∃ (I : set α), M₀ = M ⟋ I ‖ M₀.E ∧ M.indep I ∧ (M ⟋ I).cl M₀.E = M.E \ I :=
begin
  have h0 : ∃ I₀, M.indep I₀ ∧ M₀ ≤ M ⟋ I₀, from ⟨∅, (M : matroid α).empty_indep, by simpa⟩, 
  obtain ⟨I, ⟨hI,h1⟩, hImax⟩ := finite.exists_maximal _ h0, 
  obtain ⟨I', hI', hI'E⟩ := exists_indep_contr_of_minor h1, 

  have hI' : I' = ∅, 
  { have hu := hImax (I ∪ I') ⟨_,_⟩ (subset_union_left _ _), 
    { have h' := subset_inter hI'.subset_ground (by { rw hu, apply subset_union_right } : I' ⊆ I), 
      rwa [contract_ground, diff_inter_self, subset_empty_iff] at h' },
    { rw [hI.contract_indep_iff, union_comm] at hI', exact hI'.2 },
    rw [hI'E, contract_contract], 
    apply restr_minor},

  subst hI', 
  rw contract_empty at hI'E, 
  simp_rw [contract_cl],

  refine ⟨I, hI'E, hI, (diff_subset_diff_left (M.cl_subset_ground _)).antisymm (λ e he, _)⟩,  
  by_contra h', 
  simp only [mem_diff, not_and, not_not_mem] at h', 
  have he' : e ∉ M.cl (M₀.E ∪ I), from λ he', he.2 (h' he'), 
  have hnl := nonloop_of_not_mem_cl he.1 he', 
  have hsk := (hnl.singleton_skew_iff 
    (union_subset (ground_subset_ground_of_minor h) hI.subset_ground)).mpr he', 
  have hsk' := hsk.subset_right (subset_union_left _ _), 

  -- have := contract_restr_eq_restr_iff_skew hI.subset_ground (ground_subset_ground_of_minor h), 

  

  -- have := contract_re
  
  

  -- obtain ⟨I, ⟨hI, ⟨C,D,rfl,hCD,hCE,hDE⟩⟩, hImax⟩ := finite.exists_maximal _ h0,  
end 
 

theorem scum (h : M' ≤ M) : 
  ∃ (I X : set α), M ⟋ I ⟍ X = M' ∧ M.indep I ∧ M.coindep X ∧ disjoint I X := 
begin
  have h0 : ∃ I₀, M.indep I₀ ∧ M' ≤ M ⟋ I₀, from ⟨∅, (M : matroid α).empty_indep, by simpa⟩, 
  obtain ⟨I, ⟨hI, ⟨C,D,rfl,hCD,hCE,hDE⟩⟩, hImax⟩ := finite.exists_maximal _ h0, 

  have hC : C ⊆ (M ⟋ I).cl ∅, 
  { simp only [contract_cl, empty_union, subset_diff], 
    refine ⟨by_contra (λ hnss, _), disjoint_of_subset_left hCE disjoint_sdiff_left⟩,  
    obtain ⟨e,heC,heI⟩ := not_subset.mp hnss,   
    rw [cl_eq_coe_cl_inter, mem_inter_iff, and_comm, not_and] at heI, 
    specialize heI ((hCE.trans (diff_subset _ _)) heC), 
    obtain ⟨heI',hei⟩ := (matroid.indep.not_mem_cl_iff hI).mp heI, 
    apply heI', 
    have hins := mem_insert e I,  
    rwa hImax (insert e I) ⟨hei,_⟩ (subset_insert _ _), 
    convert con_del_minor _ (C \ {e}) D using 1, 
    rw [contract_contract, contract_contract, ←union_singleton, union_assoc, singleton_union,   
      insert_diff_singleton, insert_eq_of_mem heC] },
  



  refine ⟨I, C ∪ D, _, hI, _, _⟩, 
  { rw [contract_eq_delete_of_subset_loops (M ⟋ I) hC, delete_delete] },
  { sorry, },
  rw [disjoint_union_right], 
  exact ⟨disjoint_of_subset_right hCE disjoint_sdiff_right, 
    disjoint_of_subset_right hDE disjoint_sdiff_right⟩, 

end


end minor



end matroid_in 

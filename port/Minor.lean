import Oneshot.Erank

open Set

variable {α : Type _} {I J C D B X Y Z R : Set α} {e : α} {M N : MatroidIn α}

namespace MatroidIn

section Delete

variable {D₁ D₂ : Set α}

class HasDelete (α β : Type _) where
  del : α → β → α
#align matroid_in.has_delete MatroidIn.HasDelete

infixl:75 " ⟍ " => HasDelete.del

def delete (M : MatroidIn α) (D : Set α) : MatroidIn α :=
  M ‖ Dᶜ
#align matroid_in.delete MatroidIn.delete

instance delSet {α : Type _} : HasDelete (MatroidIn α) (Set α) :=
  ⟨MatroidIn.delete⟩
#align matroid_in.del_set MatroidIn.delSet

instance delElem {α : Type _} : HasDelete (MatroidIn α) α :=
  ⟨fun M e => M.delete {e}⟩
#align matroid_in.del_elem MatroidIn.delElem

instance delete_finite [Finite M] : Finite (M ⟍ D) :=
  MatroidIn.restrict_finite
#align matroid_in.delete_finite MatroidIn.delete_finite

instance delete_finiteRk [FiniteRk M] : FiniteRk (M ⟍ D) :=
  MatroidIn.restrict_finiteRk
#align matroid_in.delete_finite_rk MatroidIn.delete_finiteRk

@[simp]
theorem delete_compl (M : MatroidIn α) (R : Set α) : M ⟍ Rᶜ = M ‖ R := by change M ‖ Rᶜᶜ = M ‖ R;
  rw [compl_compl]
#align matroid_in.delete_compl MatroidIn.delete_compl

@[simp]
theorem restrict_compl (M : MatroidIn α) (D : Set α) : M ‖ Dᶜ = M ⟍ D :=
  rfl
#align matroid_in.restrict_compl MatroidIn.restrict_compl

@[simp]
theorem restrict_ground_diff (M : MatroidIn α) (D : Set α) : M ‖ (M.e \ D) = M ⟍ D := by
  rw [← restrict_compl, ← M.restrict_inter_ground (Dᶜ), diff_eq_compl_inter]
#align matroid_in.restrict_ground_diff MatroidIn.restrict_ground_diff

@[simp]
theorem delete_restriction (M : MatroidIn α) (D : Set α) : M ⟍ D ≤r M :=
  restrict_restriction _ _
#align matroid_in.delete_restriction MatroidIn.delete_restriction

@[simp]
theorem delete_ground (M : MatroidIn α) (D : Set α) : (M ⟍ D).e = M.e \ D := by
  rw [← restrict_compl, restrict_ground_eq', diff_eq_compl_inter]
#align matroid_in.delete_ground MatroidIn.delete_ground

@[ssE_finish_rules]
theorem delete_ground_subset_ground (M : MatroidIn α) (D : Set α) : (M ⟍ D).e ⊆ M.e :=
  (M.delete_ground D).trans_subset (diff_subset _ _)
#align matroid_in.delete_ground_subset_ground MatroidIn.delete_ground_subset_ground

@[simp]
theorem delete_elem (M : MatroidIn α) (e : α) : M ⟍ e = M ⟍ ({e} : Set α) :=
  rfl
#align matroid_in.delete_elem MatroidIn.delete_elem

@[simp]
theorem delete_delete (M : MatroidIn α) (D₁ D₂ : Set α) : M ⟍ D₁ ⟍ D₂ = M ⟍ (D₁ ∪ D₂) := by
  rw [← restrict_compl, ← restrict_compl, ← restrict_compl, restrict_restrict, compl_union]
#align matroid_in.delete_delete MatroidIn.delete_delete

theorem delete_comm (M : MatroidIn α) (D₁ D₂ : Set α) : M ⟍ D₁ ⟍ D₂ = M ⟍ D₂ ⟍ D₁ := by
  rw [delete_delete, union_comm, delete_delete]
#align matroid_in.delete_comm MatroidIn.delete_comm

theorem delete_eq_delete_iff : M ⟍ D₁ = M ⟍ D₂ ↔ D₁ ∩ M.e = D₂ ∩ M.e := by
  simp_rw [← restrict_compl, restrict_eq_restrict_iff, ← diff_eq_compl_inter,
    diff_eq_diff_iff_inter_eq_inter, inter_comm M.E]
#align matroid_in.delete_eq_delete_iff MatroidIn.delete_eq_delete_iff

theorem delete_eq_delete_inter_ground (M : MatroidIn α) (D : Set α) : M ⟍ D = M ⟍ (D ∩ M.e) := by
  rw [delete_eq_delete_iff, inter_assoc, inter_self]
#align matroid_in.delete_eq_delete_inter_ground MatroidIn.delete_eq_delete_inter_ground

theorem restrict_eq_delete_diff (M : MatroidIn α) (R : Set α) : M ‖ R = M ⟍ (M.e \ R) :=
  by
  rw [← restrict_compl, restrict_eq_restrict_iff, inter_eq_inter_iff_right, diff_eq, compl_inter,
    compl_compl, inter_distrib_right, compl_inter_self, empty_union,
    and_iff_right (inter_subset_left _ _)]
  exact (inter_subset_left _ _).trans (subset_union_right _ _)
#align matroid_in.restrict_eq_delete_diff MatroidIn.restrict_eq_delete_diff

theorem delete_eq_restrict_diff (M : MatroidIn α) (D : Set α) : M ⟍ D = M ‖ (M.e \ D) := by
  rw [restrict_eq_delete_diff, sdiff_sdiff_right_self, delete_eq_delete_inter_ground, inter_comm,
    inf_eq_inter]
#align matroid_in.delete_eq_restrict_diff MatroidIn.delete_eq_restrict_diff

theorem delete_eq_self_iff : M ⟍ D = M ↔ Disjoint D M.e := by
  rw [← restrict_compl, restrict_eq_self_iff, subset_compl_iff_disjoint_left]
#align matroid_in.delete_eq_self_iff MatroidIn.delete_eq_self_iff

@[simp]
theorem delete_indep_iff : (M ⟍ D).indep I ↔ M.indep I ∧ Disjoint I D := by
  rw [← restrict_compl, restrict_indep_iff, subset_compl_iff_disjoint_right]
#align matroid_in.delete_indep_iff MatroidIn.delete_indep_iff

theorem Indep.of_delete (h : (M ⟍ D).indep I) : M.indep I :=
  (delete_indep_iff.mp h).1
#align matroid_in.indep.of_delete MatroidIn.Indep.of_delete

theorem Indep.indep_delete_of_disjoint (h : M.indep I) (hID : Disjoint I D) : (M ⟍ D).indep I :=
  delete_indep_iff.mpr ⟨h, hID⟩
#align matroid_in.indep.indep_delete_of_disjoint MatroidIn.Indep.indep_delete_of_disjoint

@[simp]
theorem delete_dep_iff : (M ⟍ D).Dep X ↔ M.Dep X ∧ Disjoint X D := by
  rw [dep_iff, dep_iff, delete_indep_iff, delete_ground, subset_diff]; tauto
#align matroid_in.delete_dep_iff MatroidIn.delete_dep_iff

@[simp]
theorem delete_base_iff : (M ⟍ D).base B ↔ M.Basis B (M.e \ D) := by
  rw [← restrict_compl, ← restrict_inter_ground, ← diff_eq_compl_inter, restrict_base_iff]
#align matroid_in.delete_base_iff MatroidIn.delete_base_iff

@[simp]
theorem delete_basis_iff : (M ⟍ D).Basis I X ↔ M.Basis I X ∧ Disjoint X D :=
  by
  simp_rw [basis_iff', delete_indep_iff, delete_ground, subset_diff, and_assoc',
    and_congr_right_iff, and_imp, ← and_assoc', and_congr_left_iff]
  refine' fun hI hdj hX =>
    ⟨fun h => ⟨h.1.2, fun J hJ hIJ hJX => h.2 J hJ _ hIJ hJX⟩, fun h =>
      ⟨⟨_, h.1⟩, fun J hJ hJD hIJ hJX => h.2 J hJ hIJ hJX⟩⟩
  · exact disjoint_of_subset_left hJX hdj
  exact disjoint_of_subset_left h.1 hdj
#align matroid_in.delete_basis_iff MatroidIn.delete_basis_iff

theorem Basis.of_delete (h : (M ⟍ D).Basis I X) : M.Basis I X :=
  (delete_basis_iff.mp h).1
#align matroid_in.basis.of_delete MatroidIn.Basis.of_delete

theorem Basis.to_delete (h : M.Basis I X) (hX : Disjoint X D) : (M ⟍ D).Basis I X := by
  rw [delete_basis_iff]; exact ⟨h, hX⟩
#align matroid_in.basis.to_delete MatroidIn.Basis.to_delete

@[simp]
theorem delete_loop_iff : (M ⟍ D).Loop e ↔ M.Loop e ∧ e ∉ D := by
  rw [loop_iff_dep, delete_dep_iff, disjoint_singleton_left, loop_iff_dep]
#align matroid_in.delete_loop_iff MatroidIn.delete_loop_iff

@[simp]
theorem delete_nonloop_iff : (M ⟍ D).Nonloop e ↔ M.Nonloop e ∧ e ∉ D := by
  rw [← indep_singleton, delete_indep_iff, disjoint_singleton_left, indep_singleton]
#align matroid_in.delete_nonloop_iff MatroidIn.delete_nonloop_iff

@[simp]
theorem delete_circuit_iff : (M ⟍ D).Circuit C ↔ M.Circuit C ∧ Disjoint C D :=
  by
  simp_rw [circuit_iff, delete_dep_iff, and_imp]
  rw [and_comm', ← and_assoc', and_congr_left_iff, and_comm', and_congr_right_iff]
  refine' fun hdj hC => ⟨fun h I hI hIC => h I hI _ hIC, fun h I hI hdj' hIC => h I hI hIC⟩
  exact disjoint_of_subset_left hIC hdj
#align matroid_in.delete_circuit_iff MatroidIn.delete_circuit_iff

@[simp]
theorem delete_cl_eq (M : MatroidIn α) (D X : Set α) : (M ⟍ D).cl X = M.cl (X \ D) \ D :=
  by
  obtain ⟨I, hI⟩ := (M ⟍ D).exists_basis (X \ D ∩ (M ⟍ D).e)
  simp_rw [delete_ground, diff_eq, inter_assoc, inter_comm (Dᶜ), inter_assoc, inter_self, ←
    inter_assoc] at hI 
  rw [cl_eq_cl_inter_ground, delete_ground, diff_eq, ← inter_assoc, ← hI.cl]
  have hI' := (delete_basis_iff.mp hI).1
  rw [M.cl_eq_cl_inter_ground, diff_eq X D, inter_right_comm, ← hI'.cl, Set.ext_iff]
  simp_rw [hI.indep.mem_cl_iff', mem_diff, hI'.indep.mem_cl_iff', delete_ground, mem_diff,
    delete_indep_iff, and_assoc', and_congr_right_iff, and_comm' (_ ∉ D), and_congr_left_iff,
    and_imp, ← union_singleton, disjoint_union_left, disjoint_singleton_left, union_singleton]
  refine' fun e heE heD => _
  rw [iff_true_intro (disjoint_of_subset_left hI'.subset _), iff_true_intro heD]
  · simp
  rw [← diff_eq]; exact disjoint_sdiff_left
#align matroid_in.delete_cl_eq MatroidIn.delete_cl_eq

theorem delete_loops_eq : (M ⟍ D).cl ∅ = M.cl ∅ \ D := by simp
#align matroid_in.delete_loops_eq MatroidIn.delete_loops_eq

theorem delete_er_eq' (M : MatroidIn α) (D X : Set α) : (M ⟍ D).er X = M.er (X \ D) :=
  by
  rw [delete_eq_delete_inter_ground, er_eq_er_inter_ground, delete_ground, diff_inter_self_eq_diff,
    diff_eq, inter_comm M.E, ← inter_assoc, ← diff_eq, M.er_eq_er_inter_ground (X \ D)]
  obtain ⟨I, hI⟩ := M.exists_basis (X \ D ∩ M.E)
  rw [←
    (hI.to_delete
        (disjoint_of_subset (inter_subset_left _ _) (inter_subset_left _ _)
          disjoint_sdiff_left)).encard,
    ← hI.encard]
#align matroid_in.delete_er_eq' MatroidIn.delete_er_eq'

theorem delete_er_eq (M : MatroidIn α) (hdj : Disjoint X D) : (M ⟍ D).er X = M.er X := by
  rw [delete_er_eq', sdiff_eq_self_iff_disjoint.mpr hdj.symm]
#align matroid_in.delete_er_eq MatroidIn.delete_er_eq

theorem delete_er_eq_delete_er_diff (M : MatroidIn α) (D X : Set α) :
    (M ⟍ D).er X = (M ⟍ D).er (X \ D) := by
  rw [er_eq_er_inter_ground, er_eq_er_inter_ground _ (X \ D)]; simp [inter_diff_assoc]
#align matroid_in.delete_er_eq_delete_er_diff MatroidIn.delete_er_eq_delete_er_diff

theorem delete_r_eq' (M : MatroidIn α) (D X : Set α) : (M ⟍ D).R X = M.R (X \ D) := by
  rw [← er_to_nat_eq_r, delete_er_eq', er_to_nat_eq_r]
#align matroid_in.delete_r_eq' MatroidIn.delete_r_eq'

theorem delete_r_eq (M : MatroidIn α) (hdj : Disjoint X D) : (M ⟍ D).R X = M.R X := by
  rw [delete_r_eq', sdiff_eq_self_iff_disjoint.mpr hdj.symm]
#align matroid_in.delete_r_eq MatroidIn.delete_r_eq

theorem delete_rFin_iff : (M ⟍ D).RFin X ↔ M.RFin (X \ D) := by
  rw [r_fin_iff_er_lt_top, delete_er_eq', r_fin_iff_er_lt_top]
#align matroid_in.delete_r_fin_iff MatroidIn.delete_rFin_iff

@[simp]
theorem delete_empty (M : MatroidIn α) : M ⟍ (∅ : Set α) = M := by rw [delete_eq_self_iff];
  exact empty_disjoint _
#align matroid_in.delete_empty MatroidIn.delete_empty

theorem delete_delete_diff (M : MatroidIn α) (D₁ D₂ : Set α) : M ⟍ D₁ ⟍ D₂ = M ⟍ D₁ ⟍ (D₂ \ D₁) :=
  by simp
#align matroid_in.delete_delete_diff MatroidIn.delete_delete_diff

noncomputable def deleteIso {β : Type _} {N : MatroidIn β} (i : M ≃i N) (D : Set α) :
    M ⟍ D ≃i (N ⟍ i.image D) :=
  (Iso.cast (M.restrict_ground_diff D).symm).trans
    ((restrictIso i _).trans (Iso.cast (by rw [i.image_ground_diff, restrict_ground_diff])))
#align matroid_in.delete_iso MatroidIn.deleteIso

end Delete

section Contract

variable {C₁ C₂ : Set α}

class HasContract (α β : Type _) where
  con : α → β → α
#align matroid_in.has_contract MatroidIn.HasContract

infixl:75 " ⟋ " => HasContract.con

def contract (M : MatroidIn α) (C : Set α) : MatroidIn α :=
  (M﹡ ⟍ C)﹡
#align matroid_in.contract MatroidIn.contract

instance conSet {α : Type _} : HasContract (MatroidIn α) (Set α) :=
  ⟨MatroidIn.contract⟩
#align matroid_in.con_set MatroidIn.conSet

instance conElem {α : Type _} : HasContract (MatroidIn α) α :=
  ⟨fun M e => M.contract {e}⟩
#align matroid_in.con_elem MatroidIn.conElem

@[simp]
theorem dual_delete_dual_eq_contract (M : MatroidIn α) (X : Set α) : (M﹡ ⟍ X)﹡ = M ⟋ X :=
  rfl
#align matroid_in.dual_delete_dual_eq_contract MatroidIn.dual_delete_dual_eq_contract

instance contract_finite [Finite M] : Finite (M ⟋ C) := by rw [← dual_delete_dual_eq_contract];
  infer_instance
#align matroid_in.contract_finite MatroidIn.contract_finite

@[simp]
theorem dual_contract_dual_eq_delete (M : MatroidIn α) (X : Set α) : (M﹡ ⟋ X)﹡ = M ⟍ X := by
  rw [← dual_delete_dual_eq_contract, dual_dual, dual_dual]
#align matroid_in.dual_contract_dual_eq_delete MatroidIn.dual_contract_dual_eq_delete

@[simp]
theorem contract_dual_eq_dual_delete (M : MatroidIn α) (X : Set α) : (M ⟋ X)﹡ = M﹡ ⟍ X := by
  rw [← dual_delete_dual_eq_contract, dual_dual]
#align matroid_in.contract_dual_eq_dual_delete MatroidIn.contract_dual_eq_dual_delete

@[simp]
theorem delete_dual_eq_dual_contract (M : MatroidIn α) (X : Set α) : (M ⟍ X)﹡ = M﹡ ⟋ X := by
  rw [← dual_delete_dual_eq_contract, dual_dual]
#align matroid_in.delete_dual_eq_dual_contract MatroidIn.delete_dual_eq_dual_contract

@[simp]
theorem contract_ground (M : MatroidIn α) (C : Set α) : (M ⟋ C).e = M.e \ C := by
  rw [← dual_delete_dual_eq_contract, dual_ground, delete_ground, dual_ground]
#align matroid_in.contract_ground MatroidIn.contract_ground

@[ssE_finish_rules]
theorem contract_ground_subset_ground (M : MatroidIn α) (C : Set α) : (M ⟋ C).e ⊆ M.e :=
  (M.contract_ground C).trans_subset (diff_subset _ _)
#align matroid_in.contract_ground_subset_ground MatroidIn.contract_ground_subset_ground

@[simp]
theorem contract_elem (M : MatroidIn α) (e : α) : M ⟋ e = M ⟋ ({e} : Set α) :=
  rfl
#align matroid_in.contract_elem MatroidIn.contract_elem

@[simp]
theorem contract_contract (M : MatroidIn α) (C₁ C₂ : Set α) : M ⟋ C₁ ⟋ C₂ = M ⟋ (C₁ ∪ C₂) := by
  rw [eq_comm, ← dual_delete_dual_eq_contract, ← delete_delete, ← dual_contract_dual_eq_delete, ←
    dual_contract_dual_eq_delete, dual_dual, dual_dual, dual_dual]
#align matroid_in.contract_contract MatroidIn.contract_contract

theorem contract_comm (M : MatroidIn α) (C₁ C₂ : Set α) : M ⟋ C₁ ⟋ C₂ = M ⟋ C₂ ⟋ C₁ := by
  rw [contract_contract, union_comm, contract_contract]
#align matroid_in.contract_comm MatroidIn.contract_comm

theorem contract_eq_self_iff : M ⟋ C = M ↔ Disjoint C M.e := by
  rw [← dual_delete_dual_eq_contract, ← dual_inj_iff, dual_dual, delete_eq_self_iff, dual_ground]
#align matroid_in.contract_eq_self_iff MatroidIn.contract_eq_self_iff

@[simp]
theorem contract_empty (M : MatroidIn α) : M ⟋ (∅ : Set α) = M := by rw [contract_eq_self_iff];
  exact empty_disjoint _
#align matroid_in.contract_empty MatroidIn.contract_empty

theorem contract_contract_diff (M : MatroidIn α) (C₁ C₂ : Set α) :
    M ⟋ C₁ ⟋ C₂ = M ⟋ C₁ ⟋ (C₂ \ C₁) := by simp
#align matroid_in.contract_contract_diff MatroidIn.contract_contract_diff

theorem contract_eq_contract_iff : M ⟋ C₁ = M ⟋ C₂ ↔ C₁ ∩ M.e = C₂ ∩ M.e := by
  rw [← dual_delete_dual_eq_contract, ← dual_delete_dual_eq_contract, dual_inj_iff,
    delete_eq_delete_iff, dual_ground]
#align matroid_in.contract_eq_contract_iff MatroidIn.contract_eq_contract_iff

theorem contract_eq_contract_inter_ground (M : MatroidIn α) (C : Set α) : M ⟋ C = M ⟋ (C ∩ M.e) :=
  by
  rw [← dual_delete_dual_eq_contract, delete_eq_delete_inter_ground, dual_delete_dual_eq_contract,
    dual_ground]
#align matroid_in.contract_eq_contract_inter_ground MatroidIn.contract_eq_contract_inter_ground

theorem coindep_contract_iff : (M ⟋ C).Coindep X ↔ M.Coindep X ∧ Disjoint X C := by
  rw [← dual_indep_iff_coindep, contract_dual_eq_dual_delete, delete_indep_iff,
    dual_indep_iff_coindep]
#align matroid_in.coindep_contract_iff MatroidIn.coindep_contract_iff

theorem Coindep.coindep_contract_of_disjoint (hX : M.Coindep X) (hXC : Disjoint X C) :
    (M ⟋ C).Coindep X :=
  coindep_contract_iff.mpr ⟨hX, hXC⟩
#align matroid_in.coindep.coindep_contract_of_disjoint MatroidIn.Coindep.coindep_contract_of_disjoint

theorem Indep.contract_base_iff (hI : M.indep I) : (M ⟋ I).base B ↔ Disjoint B I ∧ M.base (B ∪ I) :=
  by
  have hIE := hI.subset_ground
  rw [← dual_dual M, dual_indep_iff_coindep, coindep_iff_exists] at hI 
  obtain ⟨B₀, hB₀, hfk⟩ := hI
  rw [← dual_dual M, ← dual_delete_dual_eq_contract, dual_base_iff', dual_base_iff',
    delete_base_iff, dual_dual, delete_ground, diff_diff, union_comm, union_subset_iff, subset_diff,
    and_comm' (Disjoint _ _), ← and_assoc', and_congr_left_iff, dual_ground, and_iff_left hIE,
    and_congr_left_iff]
  exact fun hIB hBE =>
    ⟨fun h => h.base_of_base_subset hB₀ (subset_diff.mpr ⟨hB₀.subset_ground, hfk.symm⟩), fun hB =>
      hB.basis_of_subset (diff_subset _ _) (diff_subset_diff_right (subset_union_right _ _))⟩
#align matroid_in.indep.contract_base_iff MatroidIn.Indep.contract_base_iff

theorem Indep.contract_indep_iff (hI : M.indep I) :
    (M ⟋ I).indep J ↔ Disjoint J I ∧ M.indep (J ∪ I) :=
  by
  simp_rw [indep_iff_subset_base, hI.contract_base_iff, union_subset_iff]
  constructor
  · rintro ⟨B, ⟨hdj, hBI⟩, hJB⟩
    exact
      ⟨disjoint_of_subset_left hJB hdj, _, hBI, hJB.trans (subset_union_left _ _),
        subset_union_right _ _⟩
  rintro ⟨hdj, B, hB, hJIB⟩
  refine' ⟨B \ I, ⟨disjoint_sdiff_left, _⟩, _⟩
  · rwa [diff_union_self, union_eq_self_of_subset_right hJIB.2]
  rw [subset_diff]
  exact ⟨hJIB.1, hdj⟩
#align matroid_in.indep.contract_indep_iff MatroidIn.Indep.contract_indep_iff

theorem Indep.union_indep_iff_contract_indep (hI : M.indep I) :
    M.indep (I ∪ J) ↔ (M ⟋ I).indep (J \ I) := by
  rw [hI.contract_indep_iff, and_iff_right disjoint_sdiff_left, diff_union_self, union_comm]
#align matroid_in.indep.union_indep_iff_contract_indep MatroidIn.Indep.union_indep_iff_contract_indep

theorem Indep.diff_indep_contract_of_subset (hJ : M.indep J) (hIJ : I ⊆ J) :
    (M ⟋ I).indep (J \ I) := by
  rwa [← (hJ.subset hIJ).union_indep_iff_contract_indep, union_eq_self_of_subset_left hIJ]
#align matroid_in.indep.diff_indep_contract_of_subset MatroidIn.Indep.diff_indep_contract_of_subset

theorem Indep.contract_dep_iff (hI : M.indep I) : (M ⟋ I).Dep J ↔ Disjoint J I ∧ M.Dep (J ∪ I) :=
  by
  rw [dep_iff, hI.contract_indep_iff, dep_iff, contract_ground, subset_diff, disjoint_comm,
    union_subset_iff, and_iff_left hI.subset_ground]
  tauto
#align matroid_in.indep.contract_dep_iff MatroidIn.Indep.contract_dep_iff

theorem Indep.union_contract_basis_union_of_basis (hI : M.indep I) (hB : (M ⟋ I).Basis J X) :
    M.Basis (J ∪ I) (X ∪ I) := by
  have hi := hB.indep
  rw [hI.contract_indep_iff] at hi 
  refine' hi.2.basis_of_maximal_subset (union_subset_union_left _ hB.subset) _ _
  · intro K hK hJIK hKXI
    rw [union_subset_iff] at hJIK 
    have hK' : (M ⟋ I).indep (K \ I) := hK.diff_indep_contract_of_subset hJIK.2
    have hm := hB.eq_of_subset_indep hK'
    rw [subset_diff, and_iff_left hi.1, diff_subset_iff, union_comm, imp_iff_right hKXI,
      imp_iff_right hJIK.1] at hm 
    simp [hm]
  exact union_subset (hB.subset_ground.trans (contract_ground_subset_ground _ _)) hI.subset_ground
#align matroid_in.indep.union_contract_basis_union_of_basis MatroidIn.Indep.union_contract_basis_union_of_basis

theorem Basis.contract_basis_union_union (h : M.Basis (J ∪ I) (X ∪ I)) (hdj : Disjoint (J ∪ X) I) :
    (M ⟋ I).Basis J X := by
  rw [disjoint_union_left] at hdj 
  have hI := h.indep.subset (subset_union_right _ _)
  simp_rw [Basis, mem_maximals_setOf_iff, hI.contract_indep_iff, and_iff_right hdj.1,
    and_iff_right h.indep, contract_ground, subset_diff, and_iff_left hdj.2,
    and_iff_left ((subset_union_left _ _).trans h.subset_ground), and_imp,
    and_iff_right
      (Disjoint.subset_left_of_subset_union ((subset_union_left _ _).trans h.subset) hdj.1)]
  intro Y hYI hYi hYX hJY
  have hu :=
    h.eq_of_subset_indep hYi (union_subset_union_left _ hJY) (union_subset_union_left _ hYX)
  apply_fun fun x : Set α => x \ I at hu 
  simp_rw [union_diff_right, hdj.1.sdiff_eq_left, hYI.sdiff_eq_left] at hu 
  exact hu
#align matroid_in.basis.contract_basis_union_union MatroidIn.Basis.contract_basis_union_union

theorem contract_eq_delete_of_subset_coloops (hX : X ⊆ M﹡.cl ∅) : M ⟋ X = M ⟍ X :=
  by
  refine' eq_of_indep_iff_indep_forall rfl fun I hI => _
  rw [(indep_of_subset_coloops hX).contract_indep_iff, delete_indep_iff, and_comm',
    union_indep_iff_indep_of_subset_coloops hX]
#align matroid_in.contract_eq_delete_of_subset_coloops MatroidIn.contract_eq_delete_of_subset_coloops

theorem contract_eq_delete_of_subset_loops (hX : X ⊆ M.cl ∅) : M ⟋ X = M ⟍ X :=
  by
  rw [← dual_inj_iff, contract_dual_eq_dual_delete, delete_dual_eq_dual_contract, eq_comm,
    contract_eq_delete_of_subset_coloops]
  rwa [dual_dual]
#align matroid_in.contract_eq_delete_of_subset_loops MatroidIn.contract_eq_delete_of_subset_loops

theorem Basis.contract_eq_contract_delete (hI : M.Basis I X) : M ⟋ X = M ⟋ I ⟍ (X \ I) :=
  by
  nth_rw 1 [← diff_union_of_subset hI.subset]
  rw [union_comm, ← contract_contract]
  refine' contract_eq_delete_of_subset_loops fun e he => _
  have heE : e ∈ (M ⟋ I).e := ⟨he.2, hI.subset_ground he.1⟩
  rw [← loop_iff_mem_cl_empty, loop_iff_not_indep heE, hI.indep.contract_indep_iff,
    disjoint_singleton_left, and_iff_right he.2, singleton_union]
  apply dep.not_indep _
  rw [← hI.indep.mem_cl_iff_of_not_mem he.2, hI.cl]
  exact M.mem_cl_of_mem he.1
#align matroid_in.basis.contract_eq_contract_delete MatroidIn.Basis.contract_eq_contract_delete

theorem contract_cl_eq_contract_delete (M : MatroidIn α) (C : Set α) :
    M ⟋ M.cl C = M ⟋ C ⟍ (M.cl C \ C) :=
  by
  obtain ⟨I, hI⟩ := M.exists_basis (C ∩ M.E)
  rw [cl_diff_self_eq_cl_inter_ground_diff, cl_eq_cl_inter_ground,
    M.contract_eq_contract_inter_ground C, hI.contract_eq_contract_delete,
    hI.basis_cl.contract_eq_contract_delete, delete_delete, delete_eq_delete_iff, contract_ground,
    diff_inter_diff_right, ground_inter_left, inter_distrib_right, diff_inter_diff_right,
    inter_eq_self_of_subset_left (inter_subset_right _ _),
    inter_eq_self_of_subset_left (diff_subset_diff (M.cl_subset_ground _) hI.subset), union_comm,
    diff_union_diff_cancel (M.subset_cl _) hI.subset]
#align matroid_in.contract_cl_eq_contract_delete MatroidIn.contract_cl_eq_contract_delete

theorem exists_eq_contract_indep_delete (M : MatroidIn α) (C : Set α) :
    ∃ I D : Set α, M.Basis I (C ∩ M.e) ∧ D ⊆ (M ⟋ I).e ∧ D ⊆ C ∧ M ⟋ C = M ⟋ I ⟍ D :=
  by
  obtain ⟨I, hI⟩ := M.exists_basis (C ∩ M.E)
  use I, C \ I ∩ M.E, hI
  rw [contract_ground, and_iff_right ((inter_subset_left _ _).trans (diff_subset _ _)), diff_eq,
    diff_eq, inter_right_comm, inter_assoc, and_iff_right (inter_subset_right _ _),
    contract_eq_contract_inter_ground, hI.contract_eq_contract_delete, diff_eq, inter_assoc]
  apply IsTrans.swap
#align matroid_in.exists_eq_contract_indep_delete MatroidIn.exists_eq_contract_indep_delete

theorem Indep.of_contract (hI : (M ⟋ C).indep I) : M.indep I :=
  by
  obtain ⟨J, R, hJ, -, -, hM⟩ := M.exists_eq_contract_indep_delete C
  rw [hM, delete_indep_iff, hJ.indep.contract_indep_iff] at hI 
  exact hI.1.2.Subset (subset_union_left _ _)
#align matroid_in.indep.of_contract MatroidIn.Indep.of_contract

@[simp]
theorem contract_loop_iff_mem_cl : (M ⟋ C).Loop e ↔ e ∈ M.cl C \ C :=
  by
  obtain ⟨I, D, hI, -, hD, hM⟩ := M.exists_eq_contract_indep_delete C
  rw [hM, delete_loop_iff, loop_iff_dep, hI.indep.contract_dep_iff, disjoint_singleton_left,
    singleton_union, hI.indep.insert_dep_iff, mem_diff, M.cl_eq_cl_inter_ground C, hI.cl,
    and_comm' (e ∉ I), and_self_right, ← mem_diff, ← mem_diff, diff_diff]
  apply_fun MatroidIn.e at hM 
  rw [delete_ground, contract_ground, contract_ground, diff_diff, diff_eq_diff_iff_inter_eq_inter,
    inter_comm, inter_comm M.E] at hM 
  exact
    ⟨fun h => ⟨h.1, fun heC => h.2 (hM.subset ⟨heC, M.cl_subset_ground _ h.1⟩).1⟩, fun h =>
      ⟨h.1, fun h' => h.2 (hM.symm.subset ⟨h', M.cl_subset_ground _ h.1⟩).1⟩⟩
#align matroid_in.contract_loop_iff_mem_cl MatroidIn.contract_loop_iff_mem_cl

theorem contract_loops_eq : (M ⟋ C).cl ∅ = M.cl C \ C := by
  simp_rw [Set.ext_iff, ← loop_iff_mem_cl_empty, contract_loop_iff_mem_cl, iff_self_iff,
    imp_true_iff]
#align matroid_in.contract_loops_eq MatroidIn.contract_loops_eq

@[simp]
theorem contract_cl_eq (M : MatroidIn α) (C X : Set α) : (M ⟋ C).cl X = M.cl (X ∪ C) \ C :=
  by
  ext e
  by_cases heX : e ∈ X
  · by_cases he : e ∈ (M ⟋ C).e
    · refine' iff_of_true (mem_cl_of_mem' _ heX) _
      rw [contract_ground] at he 
      exact ⟨mem_cl_of_mem' _ (Or.inl heX) he.1, he.2⟩
    refine' iff_of_false (he ∘ fun h => cl_subset_ground _ _ h) (he ∘ fun h => _)
    rw [contract_ground]
    exact ⟨M.cl_subset_ground _ h.1, h.2⟩
  suffices h' : e ∈ (M ⟋ C).cl X \ X ↔ e ∈ M.cl (X ∪ C) \ (X ∪ C)
  · rwa [mem_diff, and_iff_left heX, mem_diff, mem_union, or_iff_right heX, ← mem_diff] at h' 
  rw [← contract_loop_iff_mem_cl, ← contract_loop_iff_mem_cl, contract_contract, union_comm]
#align matroid_in.contract_cl_eq MatroidIn.contract_cl_eq

/-- This lemma is useful where it is known (or unimportant) that `X ⊆ M.E` -/
theorem er_contract_eq_er_contract_diff (M : MatroidIn α) (C X : Set α) :
    (M ⟋ C).er X = (M ⟋ C).er (X \ C) := by
  rw [← er_cl, contract_cl_eq, ← er_cl _ (X \ C), contract_cl_eq, diff_union_self]
#align matroid_in.er_contract_eq_er_contract_diff MatroidIn.er_contract_eq_er_contract_diff

/-- This lemma is useful where it is known (or unimportant) that `X` and `C` are disjoint -/
theorem er_contract_eq_er_contract_inter_ground (M : MatroidIn α) (C X : Set α) :
    (M ⟋ C).er X = (M ⟋ C).er (X ∩ M.e) := by
  rw [er_eq_er_inter_ground, contract_ground, M.er_contract_eq_er_contract_diff _ (X ∩ M.E),
    inter_diff_assoc]
#align matroid_in.er_contract_eq_er_contract_inter_ground MatroidIn.er_contract_eq_er_contract_inter_ground

/-- This lemma is essentially defining the 'relative rank' of `X` to `C`. The required set `I` can 
  be obtained for any `X,C ⊆ M.E` using `M.exists_basis_union_inter_basis X C`. -/
theorem Basis.er_contract (hI : M.Basis I (X ∪ C)) (hIC : M.Basis (I ∩ C) C) :
    (M ⟋ C).er X = (I \ C).encard :=
  by
  rw [er_contract_eq_er_contract_diff, hIC.contract_eq_contract_delete, delete_er_eq',
    diff_inter_self_eq_diff, basis.encard]
  apply basis.contract_basis_union_union
  · rw [diff_union_inter, diff_diff, union_eq_self_of_subset_right (diff_subset _ _)]
    apply hI.basis_subset _ (union_subset_union (diff_subset _ _) (inter_subset_right _ _))
    rw [union_comm, ← diff_subset_iff, subset_diff, diff_self_inter, diff_subset_iff, union_comm]
    exact ⟨hI.subset, disjoint_sdiff_left⟩
  rw [disjoint_union_left]
  exact
    ⟨disjoint_of_subset_right (inter_subset_right _ _) disjoint_sdiff_left,
      disjoint_of_subset (diff_subset _ _) (inter_subset_right _ _) disjoint_sdiff_left⟩
#align matroid_in.basis.er_contract MatroidIn.Basis.er_contract

theorem Basis.er_contract_of_subset (hI : M.Basis I X) (hCX : C ⊆ X) (hIC : M.Basis (I ∩ C) C) :
    (M ⟋ C).er (X \ C) = (I \ C).encard :=
  by
  rw [← er_contract_eq_er_contract_diff, basis.er_contract _ hIC]
  rwa [union_eq_self_of_subset_right hCX]
#align matroid_in.basis.er_contract_of_subset MatroidIn.Basis.er_contract_of_subset

theorem er_contract_add_er_eq_er_union (M : MatroidIn α) (C X : Set α) :
    (M ⟋ C).er X + M.er C = M.er (X ∪ C) :=
  by
  obtain ⟨I, D, hIC, hD, hDC, hM⟩ := M.exists_eq_contract_indep_delete C
  obtain ⟨J, hJ, rfl⟩ :=
    hIC.exists_basis_inter_eq_of_supset (subset_union_right (X ∩ M.E) _) (by simp)
  rw [er_contract_eq_er_contract_inter_ground, contract_eq_contract_inter_ground,
    hJ.er_contract hIC, er_eq_er_inter_ground, ← hIC.encard, er_eq_er_inter_ground,
    inter_distrib_right, ← hJ.encard, encard_diff_add_encard_inter]
#align matroid_in.er_contract_add_er_eq_er_union MatroidIn.er_contract_add_er_eq_er_union

theorem Basis.diff_subset_loops_contract (hIX : M.Basis I X) : X \ I ⊆ (M ⟋ I).cl ∅ :=
  by
  rw [diff_subset_iff, contract_loops_eq, union_diff_self,
    union_eq_self_of_subset_left (M.subset_cl I)]
  exact hIX.subset_cl
#align matroid_in.basis.diff_subset_loops_contract MatroidIn.Basis.diff_subset_loops_contract

/-- Relative rank is additive -/
theorem contract_er_add_contract_er (M : MatroidIn α) (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) :
    (M ⟋ X).er Y + (M ⟋ Y).er Z = (M ⟋ X).er Z :=
  by
  suffices h' :
    ∀ X' Y' Z',
      X' ⊆ Y' →
        Y' ⊆ Z' → X' ⊆ M.E → Y' ⊆ M.E → Z' ⊆ M.E → (M ⟋ X').er Y' + (M ⟋ Y').er Z' = (M ⟋ X').er Z'
  · have :=
      h' (X ∩ M.E) (Y ∩ M.E) (Z ∩ M.E) (inter_subset_inter_left M.E hXY)
        (inter_subset_inter_left M.E hYZ) (inter_subset_right _ _) (inter_subset_right _ _)
        (inter_subset_right _ _)
    simp_rw [← contract_eq_contract_inter_ground, ← er_contract_eq_er_contract_inter_ground] at this 
    assumption
  clear hXY hYZ X Y Z
  intro X Y Z hXY hYZ hXE hYE hZE
  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain ⟨J, hJ, rfl⟩ := hI.exists_basis_inter_eq_of_supset hXY
  obtain ⟨K, hK, rfl⟩ := hJ.exists_basis_inter_eq_of_supset hYZ
  rw [M.er_contract_eq_er_contract_diff, M.er_contract_eq_er_contract_diff Y,
    M.er_contract_eq_er_contract_diff _ Z, hK.er_contract_of_subset hYZ hJ,
    hJ.er_contract_of_subset hXY hI, ←
    encard_union_eq (disjoint_of_subset_left _ disjoint_sdiff_right)]
  · rw [inter_assoc, inter_eq_self_of_subset_right hXY] at hI 
    rw [diff_eq, diff_eq, inter_assoc, ← inter_distrib_left, union_distrib_right, union_compl_self,
      univ_inter, ← compl_inter, ← diff_eq, inter_eq_self_of_subset_left hXY, basis.encard]
    rw [hI.contract_eq_contract_delete, delete_basis_iff,
      and_iff_left (disjoint_of_subset_right (diff_subset _ _) disjoint_sdiff_left)]
    refine' basis.contract_basis_union_union _ _
    · rw [diff_union_inter]
      refine'
        hK.basis_subset _ (union_subset (diff_subset _ _) ((inter_subset_left _ _).trans hK.subset))
      rw [union_comm, ← diff_subset_iff, diff_self_inter]
      exact diff_subset_diff_left hK.subset
    rw [← union_diff_distrib]
    exact disjoint_of_subset_right (inter_subset_right _ _) disjoint_sdiff_left
  refine' (diff_subset _ _).trans (inter_subset_right _ _)
#align matroid_in.contract_er_add_contract_er MatroidIn.contract_er_add_contract_er

theorem contract_er_diff_add_contract_er_diff (M : MatroidIn α) (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) :
    (M ⟋ X).er (Y \ X) + (M ⟋ Y).er (Z \ Y) = (M ⟋ X).er (Z \ X) := by
  simp_rw [← er_contract_eq_er_contract_diff, M.contract_er_add_contract_er hXY hYZ]
#align matroid_in.contract_er_diff_add_contract_er_diff MatroidIn.contract_er_diff_add_contract_er_diff

theorem er_contract_le_er (M : MatroidIn α) (C X : Set α) : (M ⟋ C).er X ≤ M.er X :=
  by
  obtain ⟨I, hI⟩ := (M ⟋ C).exists_basis (X ∩ (M ⟋ C).e)
  rw [er_eq_er_inter_ground, ← hI.encard, le_er_iff]
  exact ⟨I, hI.subset.trans (inter_subset_left _ _), hI.indep.of_contract, rfl⟩
#align matroid_in.er_contract_le_er MatroidIn.er_contract_le_er

theorem RFin.contract_rFin (h : M.RFin X) (C : Set α) : (M ⟋ C).RFin X := by
  rw [r_fin_iff_er_lt_top] at *; exact (er_contract_le_er _ _ _).trans_lt h
#align matroid_in.r_fin.contract_r_fin MatroidIn.RFin.contract_rFin

-- lemma r_fin.contract_r_fin_of_subset_union (h : M.r_fin Z) (X C : set α) (hX : X ⊆ M.cl (Z ∪ C)) :
--   (M ⟋ C).r_fin (X \ C) :=
-- begin
--   refine ((h.subset (diff_subset Z C)).contract_r_fin disjoint_sdiff_left).to_cl.subset _, 
--   rw [contract_cl_eq, diff_union_self], 
--   exact diff_subset_diff_left hX,
-- end
instance contract_finiteRk [FiniteRk M] : FiniteRk (M ⟋ C) :=
  by
  have h := ‹finite_rk M›
  rw [← r_fin_ground_iff] at h ⊢
  exact (h.contract_r_fin C).Subset (contract_ground_subset_ground _ _)
#align matroid_in.contract_finite_rk MatroidIn.contract_finiteRk

noncomputable def contractIso {β : Type _} {N : MatroidIn β} (i : M ≃i N) (C : Set α) :
    M ⟋ C ≃i (N ⟋ i.image C) :=
  (deleteIso i.dual C).dual
#align matroid_in.contract_iso MatroidIn.contractIso

-- lemma contract_eq_delete_iff : M ⟋ X = M ⟍ X ↔ X ⊆ M.cl ∅ ∪ 
-- lemma basis.foo (hI : M.basis I C) : M ⟋ C = M ⟋ I ⟍ (C \ I) :=
-- begin
--   nth_rewrite 0 ←union_diff_cancel hI.subset,
--   rw [←contract_contract], 
-- end
end Contract

section Minor

variable {M₀ M₁ M₂ : MatroidIn α}

theorem contract_delete_diff (M : MatroidIn α) (C D : Set α) : M ⟋ C ⟍ D = M ⟋ C ⟍ (D \ C) := by
  rw [delete_eq_delete_iff, contract_ground, diff_eq, diff_eq, ← inter_inter_distrib_right,
    inter_assoc]
#align matroid_in.contract_delete_diff MatroidIn.contract_delete_diff

theorem contract_delete_comm (M : MatroidIn α) {C D : Set α} (hCD : Disjoint C D) :
    M ⟋ C ⟍ D = M ⟍ D ⟋ C :=
  by
  rw [contract_eq_contract_inter_ground, (M ⟍ D).contract_eq_contract_inter_ground, delete_ground,
    inter_diff_distrib_left, hCD.inter_eq, diff_empty]
  obtain ⟨I, hI⟩ := M.exists_basis (C ∩ M.E)
  have hI' : (M ⟍ D).Basis I (C ∩ M.E) := by rw [delete_basis_iff];
    exact ⟨hI, disjoint_of_subset_left (inter_subset_left _ _) hCD⟩
  have hID : Disjoint I D := by refine' disjoint_of_subset_left hI'.subset_ground_left _;
    simp [disjoint_sdiff_left]
  rw [hI.contract_eq_contract_delete, hI'.contract_eq_contract_delete]
  refine' eq_of_indep_iff_indep_forall _ fun J hJ => _
  · ext;
    simp only [delete_delete, delete_ground, contract_ground, mem_diff, mem_union, mem_inter_iff,
      not_and, not_not_mem, and_imp]
    tauto
  simp only [hI.indep.contract_indep_iff, hI'.indep.contract_indep_iff, delete_delete,
    delete_indep_iff, disjoint_union_right, disjoint_union_left, and_assoc',
    and_comm' _ (Disjoint J D), and_congr_right_iff, iff_and_self, iff_true_intro hID, imp_true_iff]
#align matroid_in.contract_delete_comm MatroidIn.contract_delete_comm

theorem contract_delete_comm' (M : MatroidIn α) (C D : Set α) : M ⟋ C ⟍ D = M ⟍ (D \ C) ⟋ C := by
  rw [contract_delete_diff, contract_delete_comm _ disjoint_sdiff_right]
#align matroid_in.contract_delete_comm' MatroidIn.contract_delete_comm'

theorem delete_contract_diff (M : MatroidIn α) (D C : Set α) : M ⟍ D ⟋ C = M ⟍ D ⟋ (C \ D) := by
  rw [contract_eq_contract_iff, delete_ground, diff_inter_diff_right, diff_eq, diff_eq, inter_assoc]
#align matroid_in.delete_contract_diff MatroidIn.delete_contract_diff

theorem delete_contract_comm' (M : MatroidIn α) (D C : Set α) : M ⟍ D ⟋ C = M ⟋ (C \ D) ⟍ D := by
  rw [delete_contract_diff, ← contract_delete_comm _ disjoint_sdiff_left]
#align matroid_in.delete_contract_comm' MatroidIn.delete_contract_comm'

theorem contract_delete_contract' (M : MatroidIn α) (C D C' : Set α) :
    M ⟋ C ⟍ D ⟋ C' = M ⟋ (C ∪ C' \ D) ⟍ D := by
  rw [delete_contract_diff, ← contract_delete_comm _ disjoint_sdiff_left, contract_contract]
#align matroid_in.contract_delete_contract' MatroidIn.contract_delete_contract'

theorem contract_delete_contract (M : MatroidIn α) (C D C' : Set α) (h : Disjoint C' D) :
    M ⟋ C ⟍ D ⟋ C' = M ⟋ (C ∪ C') ⟍ D := by rw [contract_delete_contract', sdiff_eq_left.mpr h]
#align matroid_in.contract_delete_contract MatroidIn.contract_delete_contract

theorem contract_delete_contract_delete' (M : MatroidIn α) (C D C' D' : Set α) :
    M ⟋ C ⟍ D ⟋ C' ⟍ D' = M ⟋ (C ∪ C' \ D) ⟍ (D ∪ D') := by
  rw [contract_delete_contract', delete_delete]
#align matroid_in.contract_delete_contract_delete' MatroidIn.contract_delete_contract_delete'

theorem contract_delete_contract_delete (M : MatroidIn α) (C D C' D' : Set α) (h : Disjoint C' D) :
    M ⟋ C ⟍ D ⟋ C' ⟍ D' = M ⟋ (C ∪ C') ⟍ (D ∪ D') := by
  rw [contract_delete_contract_delete', sdiff_eq_left.mpr h]
#align matroid_in.contract_delete_contract_delete MatroidIn.contract_delete_contract_delete

theorem delete_contract_delete' (M : MatroidIn α) (D C D' : Set α) :
    M ⟍ D ⟋ C ⟍ D' = M ⟋ (C \ D) ⟍ (D ∪ D') := by rw [delete_contract_comm', delete_delete]
#align matroid_in.delete_contract_delete' MatroidIn.delete_contract_delete'

theorem delete_contract_delete (M : MatroidIn α) (D C D' : Set α) (h : Disjoint C D) :
    M ⟍ D ⟋ C ⟍ D' = M ⟋ C ⟍ (D ∪ D') := by rw [delete_contract_delete', sdiff_eq_left.mpr h]
#align matroid_in.delete_contract_delete MatroidIn.delete_contract_delete

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (C «expr ⊆ » M.E) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (D «expr ⊆ » M.E) -/
def Minor (N M : MatroidIn α) : Prop :=
  ∃ (C : _) (_ : C ⊆ M.e) (D : _) (_ : D ⊆ M.e), Disjoint C D ∧ N = M ⟋ C ⟍ D
#align matroid_in.minor MatroidIn.Minor

def StrictMinor (N M : MatroidIn α) : Prop :=
  M ‖ N.e = N ∧ N.e ⊂ M.e
#align matroid_in.strict_minor MatroidIn.StrictMinor

infixl:75 " ≤m " => MatroidIn.Minor

infixl:75 " <m " => MatroidIn.StrictMinor

theorem contract_delete_minor (M : MatroidIn α) (C D : Set α) : M ⟋ C ⟍ D ≤m M :=
  by
  rw [contract_delete_diff, contract_eq_contract_inter_ground, delete_eq_delete_inter_ground,
    contract_ground, diff_inter_self_eq_diff, diff_inter_diff_right, inter_diff_right_comm]
  refine' ⟨_, inter_subset_right _ _, _, inter_subset_right _ _, _, rfl⟩
  refine' disjoint_of_subset (inter_subset_left _ _) _ disjoint_compl_right
  rw [diff_eq, inter_right_comm]
  exact inter_subset_right _ _
#align matroid_in.contract_delete_minor MatroidIn.contract_delete_minor

theorem minor_iff_contract_delete : N ≤m M ↔ ∃ C D : Set α, N = M ⟋ C ⟍ D :=
  by
  constructor
  · rintro ⟨C, -, D, -, -, rfl⟩; exact ⟨_, _, rfl⟩
  rintro ⟨C, D, rfl⟩
  apply contract_delete_minor
#align matroid_in.minor_iff_contract_delete MatroidIn.minor_iff_contract_delete

instance minor_refl : IsRefl (MatroidIn α) (· ≤m ·) :=
  ⟨fun M => ⟨∅, empty_subset _, ∅, empty_subset _, empty_disjoint _, by simp⟩⟩
#align matroid_in.minor_refl MatroidIn.minor_refl

instance minor_antisymm : IsAntisymm (MatroidIn α) (· ≤m ·) :=
  by
  constructor
  rintro M M' ⟨C, hC, D, hD, hCD, h⟩ ⟨C', hC', D', hD', hCD', h'⟩
  have h'' := h'
  apply_fun E at h' 
  simp_rw [delete_ground, contract_ground, h, delete_ground, contract_ground, diff_diff] at h' 
  rw [eq_comm, sdiff_eq_left, disjoint_union_right, disjoint_union_right, disjoint_union_right] at
    h' 
  have hC : C = ∅ := h'.1.1.1.eq_bot_of_ge hC; subst hC
  have hD : D = ∅ := h'.1.1.2.eq_bot_of_ge hD; subst hD
  rwa [delete_empty, contract_empty] at h 
#align matroid_in.minor_antisymm MatroidIn.minor_antisymm

instance minor_trans : IsTrans (MatroidIn α) (· ≤m ·) :=
  by
  constructor
  rintro M₁ M₂ M₃ ⟨C₁, hC₁, D₁, hD₁, hdj, rfl⟩ ⟨C₂, hC₂, D₂, hD₂, hdj', rfl⟩
  rw [contract_delete_contract_delete']
  apply contract_delete_minor
#align matroid_in.minor_trans MatroidIn.minor_trans

theorem Minor.refl {M : MatroidIn α} : M ≤m M :=
  refl M
#align matroid_in.minor.refl MatroidIn.Minor.refl

theorem Minor.trans {M₁ M₂ M₃ : MatroidIn α} (h : M₁ ≤m M₂) (h' : M₂ ≤m M₃) : M₁ ≤m M₃ :=
  trans h h'
#align matroid_in.minor.trans MatroidIn.Minor.trans

theorem Minor.antisymm (h : N ≤m M) (h' : M ≤m N) : N = M :=
  antisymm h h'
#align matroid_in.minor.antisymm MatroidIn.Minor.antisymm

theorem contract_minor (M : MatroidIn α) (C : Set α) : M ⟋ C ≤m M := by rw [← (M ⟋ C).delete_empty];
  apply contract_delete_minor
#align matroid_in.contract_minor MatroidIn.contract_minor

theorem delete_minor (M : MatroidIn α) (D : Set α) : M ⟍ D ≤m M := by nth_rw 1 [← M.contract_empty];
  apply contract_delete_minor
#align matroid_in.delete_minor MatroidIn.delete_minor

theorem restrict_minor (M : MatroidIn α) (R : Set α) : M ‖ R ≤m M := by rw [← delete_compl];
  apply delete_minor
#align matroid_in.restrict_minor MatroidIn.restrict_minor

theorem Restriction.minor (h : N ≤r M) : N ≤m M := by rw [← h.eq_restrict]; apply restrict_minor
#align matroid_in.restriction.minor MatroidIn.Restriction.minor

theorem delete_contract_minor (M : MatroidIn α) (D C : Set α) : M ⟍ D ⟋ C ≤m M :=
  ((M ⟍ D).contract_minor C).trans (M.delete_minor D)
#align matroid_in.delete_contract_minor MatroidIn.delete_contract_minor

theorem contract_restrict_minor (M : MatroidIn α) (C R : Set α) : M ⟋ C ‖ R ≤m M := by
  rw [← delete_compl]; apply contract_delete_minor
#align matroid_in.contract_restrict_minor MatroidIn.contract_restrict_minor

theorem Minor.to_dual (h : N ≤m M) : N﹡ ≤m M﹡ :=
  by
  obtain ⟨C, hC, D, hD, hCD, rfl⟩ := h
  rw [delete_dual_eq_dual_contract, contract_dual_eq_dual_delete]
  apply delete_contract_minor
#align matroid_in.minor.to_dual MatroidIn.Minor.to_dual

theorem dual_minor_iff : N﹡ ≤m M﹡ ↔ N ≤m M :=
  by
  refine' ⟨fun h => _, minor.to_dual⟩
  rw [← dual_dual N, ← dual_dual M]
  exact h.to_dual
#align matroid_in.dual_minor_iff MatroidIn.dual_minor_iff

/-- The scum theorem. We can always realize a minor by contracting an independent set and deleting
  a coindependent set -/
theorem Minor.exists_contract_indep_delete_coindep (h : N ≤m M) :
    ∃ C D, M.indep C ∧ M.Coindep D ∧ Disjoint C D ∧ N = M ⟋ C ⟍ D :=
  by
  obtain ⟨C', hC', D', hD', hCD', rfl⟩ := h
  obtain ⟨I, hI⟩ := M.exists_basis C'
  obtain ⟨K, hK⟩ := M﹡.exists_basis D'
  have hIK : Disjoint I K := disjoint_of_subset hI.subset hK.subset hCD'
  use I ∪ D' \ K, C' \ I ∪ K
  refine' ⟨_, _, _, _⟩
  · have hss : (D' \ K) \ I ⊆ (M﹡ ⟋ K ⟍ I).cl ∅ := by rw [delete_loops_eq];
      exact diff_subset_diff_left hK.diff_subset_loops_contract
    rw [← delete_dual_eq_dual_contract, ← contract_dual_eq_dual_delete] at hss 
    have hi := indep_of_subset_coloops hss
    rw [← contract_delete_comm _ hIK, delete_indep_iff, hI.indep.contract_indep_iff,
      diff_union_self, union_comm] at hi 
    exact hi.1.2
  · rw [← dual_indep_iff_coindep]
    have hss : (C' \ I) \ K ⊆ (M ⟋ I ⟍ K)﹡﹡.cl ∅ := by rw [dual_dual, delete_loops_eq];
      exact diff_subset_diff_left hI.diff_subset_loops_contract
    have hi := indep_of_subset_coloops hss
    rw [delete_dual_eq_dual_contract, contract_dual_eq_dual_delete, ←
      contract_delete_comm _ hIK.symm, delete_indep_iff, hK.indep.contract_indep_iff,
      diff_union_self] at hi 
    exact hi.1.2
  · rw [disjoint_union_left, disjoint_union_right, disjoint_union_right,
      and_iff_right disjoint_sdiff_right, and_iff_right hIK, and_iff_left disjoint_sdiff_left]
    exact disjoint_of_subset (diff_subset _ _) (diff_subset _ _) hCD'.symm
  have hb : (M ⟋ C')﹡.Basis K D' :=
    by
    rw [contract_dual_eq_dual_delete, delete_basis_iff, and_iff_right hK]
    exact hCD'.symm
  rw [← dual_dual (M ⟋ C' ⟍ D'), delete_dual_eq_dual_contract, hb.contract_eq_contract_delete,
    hI.contract_eq_contract_delete, delete_dual_eq_dual_contract, contract_dual_eq_dual_delete,
    dual_dual, delete_delete, contract_delete_contract]
  rw [disjoint_union_right, and_iff_left disjoint_sdiff_left]
  exact disjoint_of_subset (diff_subset _ _) (diff_subset _ _) hCD'.symm
#align matroid_in.minor.exists_contract_indep_delete_coindep MatroidIn.Minor.exists_contract_indep_delete_coindep

theorem Minor.exists_contract_spanning_restrict (h : N ≤m M) :
    ∃ C, M.indep C ∧ N ≤r (M ⟋ C) ∧ (M ⟋ C).cl N.e = (M ⟋ C).e :=
  by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := h.exists_contract_indep_delete_coindep
  refine' ⟨C, hC, delete_restriction _ _, _⟩
  rw [← (hD.coindep_contract_of_disjoint hCD.symm).cl_compl, delete_ground]
#align matroid_in.minor.exists_contract_spanning_restrict MatroidIn.Minor.exists_contract_spanning_restrict

section Iso

variable {β : Type _} {N' M' : MatroidIn α}

/-- We have `N ≤i M` if `M` has an `N`-minor; i.e. `N` is isomorphic to a minor of `M` -/
def IsoMinor (N : MatroidIn β) (M : MatroidIn α) : Prop :=
  ∃ M' : MatroidIn α, M' ≤m M ∧ Nonempty (N ≃i M')
#align matroid_in.iso_minor MatroidIn.IsoMinor

infixl:75 " ≤i " => MatroidIn.IsoMinor

instance isoMinor_refl : IsRefl (MatroidIn α) (· ≤i ·) :=
  ⟨fun M => ⟨M, refl M, ⟨Iso.refl M⟩⟩⟩
#align matroid_in.iso_minor_refl MatroidIn.isoMinor_refl

theorem Iso.isoMinor {N : MatroidIn β} (e : N ≃i M) : N ≤i M :=
  ⟨M, Minor.refl, ⟨e⟩⟩
#align matroid_in.iso.iso_minor MatroidIn.Iso.isoMinor

theorem Minor.trans_iso {M' : MatroidIn β} (h : N ≤m M) (e : M ≃i M') : N ≤i M' :=
  by
  obtain ⟨C, hC, D, hD, hCD, rfl⟩ := h
  set i := delete_iso (contract_iso e C) D
  exact ⟨_, contract_delete_minor _ _ _, ⟨i⟩⟩
#align matroid_in.minor.trans_iso MatroidIn.Minor.trans_iso

theorem Minor.isoMinor (h : N ≤m M) : N ≤i M :=
  ⟨N, h, ⟨Iso.refl N⟩⟩
#align matroid_in.minor.iso_minor MatroidIn.Minor.isoMinor

theorem IsoMinor.trans {α₁ α₂ α₃ : Type _} {M₁ : MatroidIn α₁} {M₂ : MatroidIn α₂}
    {M₃ : MatroidIn α₃} (h : M₁ ≤i M₂) (h' : M₂ ≤i M₃) : M₁ ≤i M₃ :=
  by
  obtain ⟨M₂', hM₂'M₃, ⟨i'⟩⟩ := h'
  obtain ⟨M₁', hM₁'M₂, ⟨i''⟩⟩ := h
  obtain ⟨N, hN, ⟨iN⟩⟩ := hM₁'M₂.trans_iso i'
  exact ⟨N, hN.trans hM₂'M₃, ⟨i''.trans iN⟩⟩
#align matroid_in.iso_minor.trans MatroidIn.IsoMinor.trans

theorem Iso.trans_isoMinor {N : MatroidIn β} (e : N ≃i N') (h : N' ≤i M) : N ≤i M :=
  e.IsoMinor.trans h
#align matroid_in.iso.trans_iso_minor MatroidIn.Iso.trans_isoMinor

theorem IsoMinor.trans_minor {N : MatroidIn β} (h : N ≤i M) (h' : M ≤m M') : N ≤i M' :=
  h.trans h'.IsoMinor
#align matroid_in.iso_minor.trans_minor MatroidIn.IsoMinor.trans_minor

theorem Minor.trans_isoMinor {M' : MatroidIn β} (h : N ≤m M) (hM : M ≤i M') : N ≤i M' :=
  h.IsoMinor.trans hM
#align matroid_in.minor.trans_iso_minor MatroidIn.Minor.trans_isoMinor

end Iso

section Rank

variable {F F' : Set α}

-- /- This is still true with `M.r_fin (X ∪ C)` -/
-- lemma contract_r_add_r_eq (M : matroid_in α) [finite_rk M] (C X : set α) :
--   (M ⟋ C).r X + M.r C = M.r (X ∪ C) :=
-- begin
--   rw [contract_eq_contract_inter_ground, M.r_eq_r_inter_ground C], 
--   obtain ⟨I, hI⟩ := M.exists_basis (C ∩ M.E), 
--   rw [hI.contract_eq_contract_delete, delete_r_eq', r_eq_r_inter_ground, contract_ground, 
--     inter_diff_assoc, diff_inter, inter_distrib_right, diff_inter_self, union_empty, 
--     ←inter_diff_assoc, inter_diff_right_comm], 
--   obtain ⟨J, hJ⟩ := (M ⟋ I).exists_basis ((X \ C \ I) ∩ M.E) _, 
--   { rw [←hJ.card, ←hI.card, ←ncard_union_eq _ hJ.finite hI.finite], 
--     { have hb := hI.indep.union_contract_basis_union_of_basis hJ, 
--       rw [union_distrib_right, diff_union_self, ←union_distrib_right ] at hb,  
--       rw [hb.card, ←r_cl, ←cl_union_cl_right_eq, hI.cl, 
--         cl_union_cl_right_eq, ←inter_distrib_right, diff_union_self, 
--         r_cl, ←r_eq_r_inter_ground] }, 
--     refine disjoint_of_subset_left hJ.subset_ground_left _, 
--     simp [disjoint_sdiff_left] },
--   rw [auto_param_eq, contract_ground, inter_comm, diff_eq, diff_eq, diff_eq],
--   exact inter_subset_inter_right _ (inter_subset_right _ _), 
-- end
theorem Flat.covby_iff_er_contract_eq (hF : M.Flat F) (hF' : M.Flat F') :
    M.Covby F F' ↔ F ⊆ F' ∧ (M ⟋ F).er (F' \ F) = 1 :=
  by
  refine' (em' (F ⊆ F')).elim (fun h => iff_of_false (h ∘ covby.subset) (h ∘ And.left)) fun hss => _
  obtain ⟨I, hI⟩ := M.exists_basis F
  rw [hF.covby_iff_eq_cl_insert, and_iff_right hss]
  refine' ⟨_, fun h => _⟩
  · rintro ⟨e, ⟨heE, heF⟩, rfl⟩
    obtain ⟨J, hJF', rfl⟩ := hI.exists_basis_inter_eq_of_supset (subset_insert e F)
    rw [hJF'.basis_cl.er_contract_of_subset (M.subset_cl_of_subset (subset_insert e F)) hI]
    rw [← encard_singleton e]; apply congr_arg
    rw [subset_antisymm_iff, diff_subset_iff, singleton_subset_iff, mem_diff, and_iff_left heF,
      union_singleton, and_iff_right hJF'.subset]
    by_contra heJ
    have hJF := hF.cl_subset_of_subset ((subset_insert_iff_of_not_mem heJ).mp hJF'.subset)
    rw [hJF'.cl] at hJF 
    exact heF (hJF (M.mem_cl_of_mem (mem_insert e F)))
  obtain ⟨J, hJF', rfl⟩ := hI.exists_basis_inter_eq_of_supset hss
  rw [hJF'.er_contract_of_subset hss hI, ← ENat.coe_one, encard_eq_coe_iff, ncard_eq_one] at h 
  obtain ⟨e, he⟩ := h.2; use e
  rw [← singleton_subset_iff, ← union_singleton, ← he,
    and_iff_right (diff_subset_diff_left hJF'.subset_ground_left), union_diff_self, ←
    cl_union_cl_right_eq, hJF'.cl, hF'.cl, union_eq_self_of_subset_left hss, hF'.cl]
#align matroid_in.flat.covby_iff_er_contract_eq MatroidIn.Flat.covby_iff_er_contract_eq

theorem Covby.er_contract_eq (h : M.Covby F F') : (M ⟋ F).er (F' \ F) = 1 :=
  ((h.flat_left.covby_iff_er_contract_eq h.flat_right).mp h).2
#align matroid_in.covby.er_contract_eq MatroidIn.Covby.er_contract_eq

theorem Hyperplane.inter_right_covby_of_inter_left_covby {H₁ H₂ : Set α} (hH₁ : M.Hyperplane H₁)
    (hH₂ : M.Hyperplane H₂) (h : M.Covby (H₁ ∩ H₂) H₁) : M.Covby (H₁ ∩ H₂) H₂ :=
  by
  rw [(hH₁.flat.inter hH₂.flat).covby_iff_er_contract_eq hH₁.flat] at h 
  rw [(hH₁.flat.inter hH₂.flat).covby_iff_er_contract_eq hH₂.flat,
    and_iff_right (inter_subset_right _ _)]
  have h₁' := hH₁.covby.er_contract_eq
  have h₂' := hH₂.covby.er_contract_eq
  have h1 := M.contract_er_diff_add_contract_er_diff (inter_subset_left H₁ H₂) hH₁.subset_ground
  have h2 := M.contract_er_diff_add_contract_er_diff (inter_subset_right H₁ H₂) hH₂.subset_ground
  rwa [h.2, h₁', ← h2, h₂', ENat.add_eq_add_iff_right WithTop.one_ne_top, eq_comm] at h1 
#align matroid_in.hyperplane.inter_right_covby_of_inter_left_covby MatroidIn.Hyperplane.inter_right_covby_of_inter_left_covby

theorem Hyperplane.inter_covby_comm {H₁ H₂ : Set α} (hH₁ : M.Hyperplane H₁)
    (hH₂ : M.Hyperplane H₂) : M.Covby (H₁ ∩ H₂) H₁ ↔ M.Covby (H₁ ∩ H₂) H₂ :=
  ⟨hH₁.inter_right_covby_of_inter_left_covby hH₂, by rw [inter_comm]; intro h;
    exact hH₂.inter_right_covby_of_inter_left_covby hH₁ h⟩
#align matroid_in.hyperplane.inter_covby_comm MatroidIn.Hyperplane.inter_covby_comm

end Rank

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
-- lemma contract_delete_comm (M : matroid_in α) {C D : set α} (hCD : disjoint C D) : 
--   M ⟋ C ⟍ D = M ⟍ D ⟋ C := 
-- begin
--   rw [←dual_delete_dual_eq_contract, ←dual_delete_dual_eq_contract, eq_dual_comm, 
--     dual_delete_dual_eq_contract], 
-- end
end Minor

end MatroidIn

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
-- 
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

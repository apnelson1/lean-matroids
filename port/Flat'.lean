import Oneshot.Circuit
import Oneshot.Mathlib.Data.Set.Basic
import Oneshot.Mathlib.FinsumNcard

noncomputable section

open scoped Classical

open scoped BigOperators

variable {α : Type _} {M : MatroidIn α} {I B C X Y Z K F F₀ F₁ F₂ H H₁ H₂ : Set α} {e f x y z : α}

open Set

namespace MatroidIn

theorem flat_def : M.Flat F ↔ (∀ I X, M.Basis I F → M.Basis I X → X ⊆ F) ∧ F ⊆ M.e :=
  Iff.rfl
#align matroid_in.flat_def MatroidIn.flat_def

/- added `∧ F ⊆ M.E` to RHS.
   Here it is the last clause as in the definition, but 
   in closure.lean I wrote similar assumptions
   as the first clause. -/
@[ssE_finish_rules]
theorem Flat.subset_ground (hF : M.Flat F) : F ⊆ M.e :=
  hF.2
#align matroid_in.flat.subset_ground MatroidIn.Flat.subset_ground

theorem Flat.eq_ground_of_spanning (hF : M.Flat F) (h : M.Spanning F) : F = M.e := by
  rw [← hF.cl, h.cl]
#align matroid_in.flat.eq_ground_of_spanning MatroidIn.Flat.eq_ground_of_spanning

theorem Flat.spanning_iff (hF : M.Flat F) : M.Spanning F ↔ F = M.e :=
  ⟨hF.eq_ground_of_spanning, by rintro rfl; exact M.ground_spanning⟩
#align matroid_in.flat.spanning_iff MatroidIn.Flat.spanning_iff

theorem Flat.iInter {ι : Type _} [hι : Nonempty ι] (F : ι → Set α) (hF : ∀ i, M.Flat (F i)) :
    M.Flat (⋂ i, F i) := by
  constructor
  · refine' fun I X hI hIX => subset_Inter fun i => _
    obtain ⟨J, hIJ, hJ⟩ :=
      hI.indep.subset_basis_of_subset (hI.subset.trans (Inter_subset _ _) : I ⊆ F i)
    have hF' := hF i; rw [flat_def] at hF' 
    refine' (union_subset_iff.mp (hF'.1 _ (F i ∪ X) hIJ _)).2
    rw [← union_eq_left_iff_subset.mpr hIJ.subset, union_assoc]
    exact hIJ.basis_union (hIX.basis_union_of_subset hIJ.indep hJ)
  intro e he; obtain i₀ := hι.some
  rw [mem_Inter] at he 
  exact (flat.subset_ground (hF i₀)) (he i₀)
#align matroid_in.flat.Inter MatroidIn.Flat.iInter

-- added the assumption `nonempty ι`
theorem flat_of_cl (M : MatroidIn α) (X : Set α) : M.Flat (M.cl X) :=
  by
  rw [M.cl_def X, sInter_eq_Inter]
  apply flat.Inter _
  · rintro ⟨F, hF⟩; exact hF.1
  use M.E, M.ground_flat, inter_subset_right _ _
#align matroid_in.flat_of_cl MatroidIn.flat_of_cl

theorem flat_iff_cl_self : M.Flat F ↔ M.cl F = F := by
  refine'
    ⟨fun h =>
      subset_antisymm (sInter_subset_of_mem ⟨h, inter_subset_left F M.E⟩)
        (M.subset_cl F (flat.subset_ground h)),
      fun h => by rw [← h]; exact flat_of_cl _ _⟩
#align matroid_in.flat_iff_cl_self MatroidIn.flat_iff_cl_self

theorem Flat.inter (hF₁ : M.Flat F₁) (hF₂ : M.Flat F₂) : M.Flat (F₁ ∩ F₂) := by rw [inter_eq_Inter];
  refine' flat.Inter _ fun i => _; cases i <;> assumption
#align matroid_in.flat.inter MatroidIn.Flat.inter

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem flat_iff_sSubset_cl_insert_forall
    (hF : F ⊆ M.e := by
      run_tac
        ssE) :
    M.Flat F ↔ ∀ e ∈ M.e \ F, M.cl F ⊂ M.cl (insert e F) :=
  by
  refine' ⟨fun h e he => (M.cl_subset (subset_insert _ _)).ssubset_of_ne _, fun h => _⟩
  · rw [h.cl]
    refine' fun h' =>
      mt ((set.ext_iff.mp h') e).mpr (not_mem_of_mem_diff he) ((M.subset_cl _ _) (mem_insert _ _))
    rw [insert_eq]
    refine' union_subset _ hF
    rw [singleton_subset_iff]; exact he.1
  rw [flat_iff_cl_self]
  by_contra h'
  obtain ⟨e, he', heF⟩ := exists_of_ssubset (ssubset_of_ne_of_subset (Ne.symm h') (M.subset_cl F))
  have h'' := h e ⟨(M.cl_subset_ground F) he', heF⟩
  rw [← M.cl_insert_cl_eq_cl_insert e F, insert_eq_of_mem he', M.cl_cl] at h'' 
  exact h''.ne rfl
#align matroid_in.flat_iff_ssubset_cl_insert_forall MatroidIn.flat_iff_sSubset_cl_insert_forall

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem flat_iff_forall_circuit {F : Set α}
    (hF : F ⊆ M.e := by
      run_tac
        ssE) :
    M.Flat F ↔ ∀ C e, M.Circuit C → e ∈ C → C ⊆ insert e F → e ∈ F :=
  by
  rw [flat_iff_cl_self]
  refine' ⟨fun h C e hC heC hCF => _, fun h => _⟩
  · rw [← h]
    refine' (M.cl_subset _) (hC.subset_cl_diff_singleton e heC)
    rwa [diff_subset_iff, singleton_union]
  refine' subset_antisymm (fun e heF => by_contra fun he' => _) (M.subset_cl F hF)
  obtain ⟨C, hC, heC, hCF⟩ := (mem_cl_iff_exists_circuit_of_not_mem he').mp heF
  exact he' (h C e hC heC hCF)
#align matroid_in.flat_iff_forall_circuit MatroidIn.flat_iff_forall_circuit

-- hypothesis: added hF
theorem flat_iff_forall_circuit' {F : Set α} :
    M.Flat F ↔ (∀ C e, M.Circuit C → e ∈ C → C ⊆ insert e F → e ∈ F) ∧ F ⊆ M.e := by
  refine'
    ⟨fun h => ⟨(flat_iff_forall_circuit h.subset_ground).mp h, h.subset_ground⟩, fun h =>
      (flat_iff_forall_circuit h.2).mpr h.1⟩
#align matroid_in.flat_iff_forall_circuit' MatroidIn.flat_iff_forall_circuit'

-- hypothesis: only added hF to RHS
theorem Flat.cl_exchange (hF : M.Flat F) (he : e ∈ M.cl (insert f F) \ F) :
    f ∈ M.cl (insert e F) \ F := by nth_rw 2 [← hF.cl]; apply cl_exchange; rwa [hF.cl]
#align matroid_in.flat.cl_exchange MatroidIn.Flat.cl_exchange

theorem Flat.cl_insert_eq_cl_insert_of_mem (hF : M.Flat F) (he : e ∈ M.cl (insert f F) \ F) :
    M.cl (insert e F) = M.cl (insert f F) :=
  by
  have := hF.subset_ground
  apply cl_insert_eq_cl_insert_of_mem; rwa [hF.cl]
#align matroid_in.flat.cl_insert_eq_cl_insert_of_mem MatroidIn.Flat.cl_insert_eq_cl_insert_of_mem

theorem Flat.cl_subset_of_subset (hF : M.Flat F) (h : X ⊆ F) : M.cl X ⊆ F := by
  have h' := M.cl_mono h; rwa [hF.cl] at h' 
#align matroid_in.flat.cl_subset_of_subset MatroidIn.Flat.cl_subset_of_subset

-- ### Covering
/-- A flat is covered by another in a matroid if they are strictly nested, with no flat
  between them . -/
def Covby (M : MatroidIn α) (F₀ F₁ : Set α) : Prop :=
  M.Flat F₀ ∧ M.Flat F₁ ∧ F₀ ⊂ F₁ ∧ ∀ F, M.Flat F → F₀ ⊆ F → F ⊆ F₁ → F = F₀ ∨ F = F₁
#align matroid_in.covby MatroidIn.Covby

theorem covby_iff :
    M.Covby F₀ F₁ ↔
      M.Flat F₀ ∧ M.Flat F₁ ∧ F₀ ⊂ F₁ ∧ ∀ F, M.Flat F → F₀ ⊆ F → F ⊆ F₁ → F = F₀ ∨ F = F₁ :=
  Iff.rfl
#align matroid_in.covby_iff MatroidIn.covby_iff

-- question: should this lemma be renamed to `covby_def`, as in `flat_def`?
theorem Flat.covby_iff_of_flat (hF₀ : M.Flat F₀) (hF₁ : M.Flat F₁) :
    M.Covby F₀ F₁ ↔ F₀ ⊂ F₁ ∧ ∀ F, M.Flat F → F₀ ⊆ F → F ⊆ F₁ → F = F₀ ∨ F = F₁ := by
  rw [covby_iff, and_iff_right hF₀, and_iff_right hF₁]
#align matroid_in.flat.covby_iff_of_flat MatroidIn.Flat.covby_iff_of_flat

theorem Covby.flat_left (h : M.Covby F₀ F₁) : M.Flat F₀ :=
  h.1
#align matroid_in.covby.flat_left MatroidIn.Covby.flat_left

theorem Covby.flat_right (h : M.Covby F₀ F₁) : M.Flat F₁ :=
  h.2.1
#align matroid_in.covby.flat_right MatroidIn.Covby.flat_right

theorem Covby.sSubset (h : M.Covby F₀ F₁) : F₀ ⊂ F₁ :=
  h.2.2.1
#align matroid_in.covby.ssubset MatroidIn.Covby.sSubset

theorem Covby.subset (h : M.Covby F₀ F₁) : F₀ ⊆ F₁ :=
  h.2.2.1.Subset
#align matroid_in.covby.subset MatroidIn.Covby.subset

theorem Covby.eq_or_eq (h : M.Covby F₀ F₁) (hF : M.Flat F) (h₀ : F₀ ⊆ F) (h₁ : F ⊆ F₁) :
    F = F₀ ∨ F = F₁ :=
  h.2.2.2 F hF h₀ h₁
#align matroid_in.covby.eq_or_eq MatroidIn.Covby.eq_or_eq

theorem Covby.eq_of_subset_of_sSubset (h : M.Covby F₀ F₁) (hF : M.Flat F) (hF₀ : F₀ ⊆ F)
    (hF₁ : F ⊂ F₁) : F = F₀ :=
  (h.2.2.2 F hF hF₀ hF₁.Subset).elim id fun h' => (hF₁.Ne h').elim
#align matroid_in.covby.eq_of_subset_of_ssubset MatroidIn.Covby.eq_of_subset_of_sSubset

theorem Covby.eq_of_sSubset_of_subset (h : M.Covby F₀ F₁) (hF : M.Flat F) (hF₀ : F₀ ⊂ F)
    (hF₁ : F ⊆ F₁) : F = F₁ :=
  (h.2.2.2 F hF hF₀.Subset hF₁).elim (fun h' => (hF₀.Ne.symm h').elim) id
#align matroid_in.covby.eq_of_ssubset_of_subset MatroidIn.Covby.eq_of_sSubset_of_subset

theorem Covby.cl_insert_eq (h : M.Covby F₀ F₁) (he : e ∈ F₁ \ F₀) : M.cl (insert e F₀) = F₁ :=
  by
  refine'
    h.eq_of_ssubset_of_subset (M.flat_of_cl _)
      ((ssubset_insert he.2).trans_subset (M.subset_cl _ _))
      (h.flat_right.cl_subset_of_subset (insert_subset.mpr ⟨he.1, h.ssubset.subset⟩))
  rw [insert_eq, union_subset_iff, singleton_subset_iff]
  exact ⟨h.flat_right.subset_ground he.1, h.flat_left.subset_ground⟩
#align matroid_in.covby.cl_insert_eq MatroidIn.Covby.cl_insert_eq

theorem Flat.covby_iff_eq_cl_insert (hF₀ : M.Flat F₀) :
    M.Covby F₀ F₁ ↔ ∃ e ∈ M.e \ F₀, F₁ = M.cl (insert e F₀) :=
  by
  refine' ⟨fun h => _, _⟩
  · obtain ⟨e, heF₁, heF₀⟩ := exists_of_ssubset h.ssubset
    simp_rw [← h.cl_insert_eq ⟨heF₁, heF₀⟩]
    have : e ∈ M.E \ F₀ := ⟨h.flat_right.subset_ground heF₁, heF₀⟩
    exact ⟨_, this, rfl⟩
  rintro ⟨e, heF₀, rfl⟩
  refine'
    ⟨hF₀, M.flat_of_cl _, (M.subset_cl_of_subset (subset_insert _ _) _).sSubset_of_nonempty_diff _,
      fun F hF hF₀F hFF₁ => _⟩
  · rw [insert_eq, union_subset_iff, singleton_subset_iff]
    exact ⟨heF₀.1, hF₀.subset_ground⟩
  · use e
    refine' ⟨M.mem_cl_of_mem (mem_insert _ _) _, _⟩
    · rw [insert_eq, union_subset_iff, singleton_subset_iff]
      exact ⟨heF₀.1, hF₀.subset_ground⟩
    exact heF₀.2
  refine'
    or_iff_not_imp_left.mpr fun hne =>
      hFF₁.antisymm (hF.cl_subset_of_subset (insert_subset.mpr ⟨_, hF₀F⟩))
  obtain ⟨f, hfF, hfF₀⟩ := exists_of_ssubset (hF₀F.ssubset_of_ne (Ne.symm hne))
  obtain ⟨he', -⟩ := hF₀.cl_exchange ⟨hFF₁ hfF, hfF₀⟩
  exact mem_of_mem_of_subset he' (hF.cl_subset_of_subset (insert_subset.mpr ⟨hfF, hF₀F⟩))
#align matroid_in.flat.covby_iff_eq_cl_insert MatroidIn.Flat.covby_iff_eq_cl_insert

/- hypothesis: added `e ∈ M.E` to RHS.
   If `e ∉ M.E`, then `F₁ = M.cl F₀ = F₀`.
   In particular, `F₀` is not a proper subset
   of `F₁`. -/
theorem cl_covby_iff : M.Covby (M.cl X) F ↔ ∃ e ∈ M.e \ M.cl X, F = M.cl (insert e X) := by
  simp_rw [(M.flat_of_cl X).covby_iff_eq_cl_insert, cl_insert_cl_eq_cl_insert]
#align matroid_in.cl_covby_iff MatroidIn.cl_covby_iff

/- hypothesis: added `e ∈ M.E` to RHS, as in the previous
   lemma. -/
theorem Flat.existsUnique_flat_of_not_mem (hF₀ : M.Flat F₀) (he : e ∈ M.e \ F₀) :
    ∃! F₁, e ∈ F₁ ∧ M.Covby F₀ F₁ :=
  by
  simp_rw [hF₀.covby_iff_eq_cl_insert]
  use M.cl (insert e F₀)
  refine' ⟨_, _⟩
  · constructor
    · exact (M.inter_ground_subset_cl (insert e F₀)) ⟨mem_insert _ _, he.1⟩
    use e, he
  simp only [exists_prop, and_imp, forall_exists_index]
  rintro X heX f hfF₀ rfl
  rw [hF₀.cl_insert_eq_cl_insert_of_mem ⟨heX, he.2⟩]
#align matroid_in.flat.exists_unique_flat_of_not_mem MatroidIn.Flat.existsUnique_flat_of_not_mem

-- hypothesis: added `e ∈ M.E` 
-- lemma flat.covby_partition (hF : M.flat F) : 
--   setoid.is_partition (insert F ((λ F₁, F₁ \ F) '' {F₁ | M.covby F F₁}) \ {∅}) := 
-- begin
--     sorry
-- { simp only [mem_diff, mem_insert_iff, eq_self_iff_true, mem_image, mem_set_of_eq, true_or, 
--   mem_singleton_iff, true_and, exists_unique_iff_exists, exists_prop, and_imp, forall_eq_or_imp, 
--   implies_true_iff, forall_exists_index, forall_apply_eq_imp_iff₂],
--   simp_rw [iff_true_intro heF.1, and_true, not_true, false_implies_iff, imp_true_iff, and_true], 
--   rintro rfl, exact not_mem_empty e heF.1
-- },
-- {
--   by_cases g : e ∈ M.E,
--   {
--       sorry,
--   -- simp only [mem_diff, mem_insert_iff, mem_image, mem_set_of_eq, mem_singleton_iff, 
--   -- exists_unique_iff_exists, exists_prop], 
--   -- obtain ⟨F' ,hF'⟩ := hF.exists_unique_flat_of_not_mem heF, 
--   -- simp only [and_imp] at hF',   
--   -- use F' \ F, 
--   -- simp only [and_imp, forall_eq_or_imp, forall_exists_index, forall_apply_eq_imp_iff₂, mem_diff, 
--   --   iff_false_intro heF, is_empty.forall_iff, implies_true_iff, not_false_iff, forall_true_left, 
--   --   true_and, ← ne.def, ←nonempty_iff_ne_empty, and_true], 
--   -- refine ⟨⟨⟨or.inr ⟨_, hF'.1.2, rfl⟩,⟨ e, hF'.1.1, heF⟩⟩,hF'.1.1⟩, λ F₁ hFF₁ hne heF₁, _⟩, 
--   -- rw [hF'.2 F₁ heF₁ hFF₁]
--   },
-- },
-- refine ⟨not_mem_diff_singleton _ _,
--   λ e, (em (e ∈ F)).elim (λ heF, ⟨F, _⟩) (λ heF, _)⟩,
-- { simp only [mem_diff, mem_insert_iff, eq_self_iff_true, mem_image, mem_set_of_eq, true_or, 
--   mem_singleton_iff, true_and, exists_unique_iff_exists, exists_prop, and_imp, forall_eq_or_imp, 
--   implies_true_iff, forall_exists_index, forall_apply_eq_imp_iff₂],
--   simp_rw [iff_true_intro heF, and_true, not_true, false_implies_iff, imp_true_iff, and_true], 
--   rintro rfl, exact not_mem_empty e heF },
-- { simp only [mem_diff, mem_insert_iff, mem_image, mem_set_of_eq, mem_singleton_iff, 
--   exists_unique_iff_exists, exists_prop], 
--   obtain ⟨F' ,hF'⟩ := hF.exists_unique_flat_of_not_mem heF, 
--   simp only [and_imp] at hF',   
--   use F' \ F, 
--   simp only [and_imp, forall_eq_or_imp, forall_exists_index, forall_apply_eq_imp_iff₂, mem_diff, 
--     iff_false_intro heF, is_empty.forall_iff, implies_true_iff, not_false_iff, forall_true_left, 
--     true_and, ← ne.def, ←nonempty_iff_ne_empty, and_true], 
--   refine ⟨⟨⟨or.inr ⟨_, hF'.1.2, rfl⟩,⟨ e, hF'.1.1, heF⟩⟩,hF'.1.1⟩, λ F₁ hFF₁ hne heF₁, _⟩, 
--   rw [hF'.2 F₁ heF₁ hFF₁] }, 
-- end 
-- lemma flat.covby_partition_of_nonempty (hF : M.flat F) (hFne : F.nonempty) : 
--   setoid.is_partition (insert F ((λ F₁, F₁ \ F) '' {F₁ | M.covby F F₁})) := 
-- begin
--   convert hF.covby_partition, 
--   rw [eq_comm, sdiff_eq_left, disjoint_singleton_right], 
--   rintro (rfl | ⟨F', hF', h⟩) , 
--   { exact not_nonempty_empty hFne },
--   refine hF'.ssubset.not_subset _, 
--   simpa [diff_eq_empty] using h, 
-- end 
-- lemma flat.covby_partition_of_empty (hF : M.flat ∅) : 
--   setoid.is_partition {F | M.covby ∅ F} := 
-- begin
--   convert hF.covby_partition, 
--   simp only [diff_empty, image_id', insert_diff_of_mem, mem_singleton, set_of],
--   ext F,  
--   simp_rw [mem_diff, mem_singleton_iff, iff_self_and], 
--   rintro hF' rfl, 
--   exact hF'.ssubset.ne rfl, 
-- end 
-- lemma flat.sum_ncard_diff_of_covby [finite E] (hF : M.flat F) :
--   F.ncard + ∑ᶠ F' ∈ {F' | M.covby F F'}, (F' \ F).ncard = nat.card E :=
-- begin
--   obtain (rfl | hFne) := F.eq_empty_or_nonempty, 
--   { convert finsum_partition_eq hF.covby_partition_of_empty, simp },
--   convert finsum_partition_eq (hF.covby_partition_of_nonempty hFne), 
--   rw [finsum_mem_insert, add_left_cancel_iff, finsum_mem_image],  
--   { rintro F₁ hF₁ F₂ hF₂ (h : F₁ \ F = F₂ \ F), 
--     rw [←diff_union_of_subset hF₁.subset, h, diff_union_of_subset hF₂.subset] }, 
--   { rintro ⟨F', hF', (h : F' \ F = F)⟩, 
--     obtain ⟨e, he⟩ := hFne,
--     exact (h.symm.subset he).2 he },
--   exact (to_finite _).image _,
-- end
theorem Flat.cl_eq_iff_basis_of_indep (hF : M.Flat F) (hI : M.indep I) : M.cl I = F ↔ M.Basis I F :=
  ⟨by rintro rfl; exact hI.basis_cl, fun h => by rw [h.cl, hF.cl]⟩
#align matroid_in.flat.cl_eq_iff_basis_of_indep MatroidIn.Flat.cl_eq_iff_basis_of_indep

-- ### Hyperplanes
section Hyperplane

/-- A hyperplane is a maximal set containing no base  -/
def Hyperplane (M : MatroidIn α) (H : Set α) : Prop :=
  M.Covby H M.e
#align matroid_in.hyperplane MatroidIn.Hyperplane

@[ssE_finish_rules]
theorem Hyperplane.subset_ground (hH : M.Hyperplane H) : H ⊆ M.e :=
  hH.flat_left.subset_ground
#align matroid_in.hyperplane.subset_ground MatroidIn.Hyperplane.subset_ground

theorem hyperplane_iff_covby : M.Hyperplane H ↔ M.Covby H M.e :=
  Iff.rfl
#align matroid_in.hyperplane_iff_covby MatroidIn.hyperplane_iff_covby

theorem Hyperplane.covby (h : M.Hyperplane H) : M.Covby H M.e :=
  h
#align matroid_in.hyperplane.covby MatroidIn.Hyperplane.covby

theorem Hyperplane.flat (hH : M.Hyperplane H) : M.Flat H :=
  hH.Covby.flat_left
#align matroid_in.hyperplane.flat MatroidIn.Hyperplane.flat

theorem Hyperplane.sSubset_ground (hH : M.Hyperplane H) : H ⊂ M.e :=
  hH.Covby.SSubset
#align matroid_in.hyperplane.ssubset_ground MatroidIn.Hyperplane.sSubset_ground

theorem Hyperplane.sSubset_univ (hH : M.Hyperplane H) : H ⊂ univ :=
  hH.sSubset_ground.trans_subset (subset_univ _)
#align matroid_in.hyperplane.ssubset_univ MatroidIn.Hyperplane.sSubset_univ

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Hyperplane.cl_insert_eq (hH : M.Hyperplane H) (heH : e ∉ H)
    (he : e ∈ M.e := by
      run_tac
        ssE) :
    M.cl (insert e H) = M.e :=
  hH.Covby.cl_insert_eq ⟨he, heH⟩
#align matroid_in.hyperplane.cl_insert_eq MatroidIn.Hyperplane.cl_insert_eq

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Hyperplane.cl_eq_univ_of_ssupset (hH : M.Hyperplane H) (hX : H ⊂ X)
    (hX' : X ⊆ M.e := by
      run_tac
        ssE) :
    M.cl X = M.e := by
  obtain ⟨e, heX, heH⟩ := exists_of_ssubset hX
  exact
    (M.cl_subset_ground _).antisymm
      ((hH.cl_insert_eq heH (hX' heX)).symm.trans_subset
        (M.cl_subset (insert_subset.mpr ⟨heX, hX.subset⟩)))
#align matroid_in.hyperplane.cl_eq_univ_of_ssupset MatroidIn.Hyperplane.cl_eq_univ_of_ssupset

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Hyperplane.spanning_of_ssupset (hH : M.Hyperplane H) (hX : H ⊂ X)
    (hXE : X ⊆ M.e := by
      run_tac
        ssE) :
    M.Spanning X := by rw [spanning_iff_cl, hH.cl_eq_univ_of_ssupset hX]
#align matroid_in.hyperplane.spanning_of_ssupset MatroidIn.Hyperplane.spanning_of_ssupset

theorem Hyperplane.not_spanning (hH : M.Hyperplane H) : ¬M.Spanning H := by
  rw [hH.flat.spanning_iff]; exact hH.ssubset_ground.ne
#align matroid_in.hyperplane.not_spanning MatroidIn.Hyperplane.not_spanning

theorem Hyperplane.flat_supset_eq_ground (hH : M.Hyperplane H) (hF : M.Flat F) (hHF : H ⊂ F) :
    F = M.e := by rw [← hF.cl, hH.cl_eq_univ_of_ssupset hHF]
#align matroid_in.hyperplane.flat_supset_eq_ground MatroidIn.Hyperplane.flat_supset_eq_ground

theorem hyperplane_iff_maximal_proper_flat :
    M.Hyperplane H ↔ M.Flat H ∧ H ⊂ M.e ∧ ∀ F, H ⊂ F → M.Flat F → F = M.e :=
  by
  rw [hyperplane_iff_covby, Covby, and_iff_right M.ground_flat, and_congr_right_iff,
    and_congr_right_iff]
  simp_rw [or_iff_not_imp_left, ssubset_iff_subset_ne, and_imp, ← Ne.def]
  exact fun hH hHE hne =>
    ⟨fun h F hHF hne' hF => h F hF hHF hF.subset_ground hne'.symm, fun h F hF hHF hFE hne' =>
      h F hHF hne'.symm hF⟩
#align matroid_in.hyperplane_iff_maximal_proper_flat MatroidIn.hyperplane_iff_maximal_proper_flat

theorem hyperplane_iff_maximal_nonspanning :
    M.Hyperplane H ↔ H ∈ maximals (· ⊆ ·) {X | X ⊆ M.e ∧ ¬M.Spanning X} :=
  by
  simp_rw [mem_maximals_setOf_iff, and_imp]
  refine' ⟨fun h => ⟨⟨h.subset_ground, h.not_spanning⟩, fun X hX hX' hHX => _⟩, fun h => _⟩
  · exact by_contra fun hne => hX' (h.spanning_of_ssupset (hHX.ssubset_of_ne hne))
  rw [hyperplane_iff_covby, covby_iff, and_iff_right M.ground_flat,
    flat_iff_ssubset_cl_insert_forall h.1.1]
  refine'
    ⟨fun e he => _, h.1.1.ssubset_of_ne (by rintro rfl; exact h.1.2 M.ground_spanning),
      fun F hF hHF hFE => or_iff_not_imp_right.mpr fun hFE' => _⟩
  · have h' := h.2 (insert_subset.mpr ⟨he.1, h.1.1⟩)
    simp_rw [subset_insert, forall_true_left, @eq_comm _ H, insert_eq_self, iff_false_intro he.2,
      imp_false, Classical.not_not, spanning_iff_cl] at h' 
    rw [h', ← not_spanning_iff_cl h.1.1]
    exact h.1.2
  have h' := h.2 hFE
  rw [hF.spanning_iff] at h' 
  rw [h' hFE' hHF]
#align matroid_in.hyperplane_iff_maximal_nonspanning MatroidIn.hyperplane_iff_maximal_nonspanning

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
-- lemma hyperplane_iff_maximal_nonspanning : 
--   M.hyperplane H ↔ H ∈ maximals (⊆) {X | X ⊆ M.E ∧ ¬ M.spanning X } :=
@[simp]
theorem compl_cocircuit_iff_hyperplane
    (hH : H ⊆ M.e := by
      run_tac
        ssE) :
    M.Cocircuit (M.e \ H) ↔ M.Hyperplane H :=
  by
  simp_rw [cocircuit_iff_mem_minimals_compl_nonspanning, hyperplane_iff_maximal_nonspanning,
    mem_maximals_setOf_iff, mem_minimals_setOf_iff, sdiff_sdiff_right_self, inf_eq_inter,
    ground_inter_right, and_imp, and_iff_right hH, and_congr_right_iff, subset_diff]
  refine' fun hH' => ⟨fun h X hX hXE hXH => _, fun h X hX hXE => _⟩
  · rw [← diff_eq_diff_iff_eq (hXH.trans hX) hX]
    exact
      @h (M.E \ X) (by simpa) ⟨diff_subset _ _, disjoint_of_subset_right hXH disjoint_sdiff_left⟩
  rw [@h (M.E \ X) (diff_subset _ _) hX, sdiff_sdiff_right_self, inf_eq_inter,
    inter_eq_self_of_subset_right hXE.1]
  rw [subset_diff, and_iff_right hH]
  exact hXE.2.symm
#align matroid_in.compl_cocircuit_iff_hyperplane MatroidIn.compl_cocircuit_iff_hyperplane

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
@[simp]
theorem compl_hyperplane_iff_cocircuit
    (h : K ⊆ M.e := by
      run_tac
        ssE) :
    M.Hyperplane (M.e \ K) ↔ M.Cocircuit K := by
  rw [← compl_cocircuit_iff_hyperplane, diff_diff_right, diff_self, empty_union, inter_comm,
    inter_eq_left_iff_subset.mpr h]
#align matroid_in.compl_hyperplane_iff_cocircuit MatroidIn.compl_hyperplane_iff_cocircuit

-- added `K ⊆ M.E`
theorem Hyperplane.compl_cocircuit (hH : M.Hyperplane H) : M.Cocircuit (M.e \ H) :=
  compl_cocircuit_iff_hyperplane.mpr hH
#align matroid_in.hyperplane.compl_cocircuit MatroidIn.Hyperplane.compl_cocircuit

theorem Cocircuit.compl_hyperplane {K : Set α} (hK : M.Cocircuit K) : M.Hyperplane (M.e \ K) :=
  (compl_hyperplane_iff_cocircuit hK.subset_ground).mpr hK
#align matroid_in.cocircuit.compl_hyperplane MatroidIn.Cocircuit.compl_hyperplane

theorem univ_not_hyperplane (M : MatroidIn α) : ¬M.Hyperplane univ := fun h => h.sSubset_univ.Ne rfl
#align matroid_in.univ_not_hyperplane MatroidIn.univ_not_hyperplane

theorem Hyperplane.eq_of_subset (h₁ : M.Hyperplane H₁) (h₂ : M.Hyperplane H₂) (h : H₁ ⊆ H₂) :
    H₁ = H₂ :=
  (h₁.Covby.eq_or_eq h₂.Flat h h₂.subset_ground).elim Eq.symm fun h' =>
    (h₂.sSubset_ground.Ne h').elim
#align matroid_in.hyperplane.eq_of_subset MatroidIn.Hyperplane.eq_of_subset

theorem Hyperplane.not_sSubset (h₁ : M.Hyperplane H₁) (h₂ : M.Hyperplane H₂) : ¬H₁ ⊂ H₂ :=
  fun hss => hss.Ne (h₁.eq_of_subset h₂ hss.Subset)
#align matroid_in.hyperplane.not_ssubset MatroidIn.Hyperplane.not_sSubset

theorem Hyperplane.exists_not_mem (hH : M.Hyperplane H) : ∃ e, e ∉ H := by by_contra' h;
  apply M.univ_not_hyperplane; convert hH; rwa [eq_comm, eq_univ_iff_forall]
#align matroid_in.hyperplane.exists_not_mem MatroidIn.Hyperplane.exists_not_mem

theorem Base.hyperplane_of_cl_diff_singleton (hB : M.base B) (heB : e ∈ B) :
    M.Hyperplane (M.cl (B \ {e})) :=
  by
  rw [hyperplane_iff_covby, flat.covby_iff_eq_cl_insert (M.flat_of_cl _)]
  refine' ⟨e, ⟨hB.subset_ground heB, _⟩, _⟩
  · rw [(hB.indep.diff {e}).not_mem_cl_iff (hB.subset_ground heB)]
    simpa [insert_eq_of_mem heB] using hB.indep
  simpa [insert_eq_of_mem heB] using hB.cl.symm
#align matroid_in.base.hyperplane_of_cl_diff_singleton MatroidIn.Base.hyperplane_of_cl_diff_singleton

theorem Hyperplane.ssupset_eq_univ_of_flat (hH : M.Hyperplane H) (hF : M.Flat F) (h : H ⊂ F) :
    F = M.e :=
  hH.Covby.eq_of_sSubset_of_subset hF h hF.subset_ground
#align matroid_in.hyperplane.ssupset_eq_univ_of_flat MatroidIn.Hyperplane.ssupset_eq_univ_of_flat

theorem Hyperplane.cl_insert_eq_univ (hH : M.Hyperplane H) (he : e ∈ M.e \ H) :
    M.cl (insert e H) = M.e :=
  by
  refine'
    hH.ssupset_eq_univ_of_flat (M.flat_of_cl _)
      ((ssubset_insert he.2).trans_subset (M.subset_cl _ _))
  rw [insert_eq, union_subset_iff, singleton_subset_iff]
  exact ⟨he.1, hH.subset_ground⟩
#align matroid_in.hyperplane.cl_insert_eq_univ MatroidIn.Hyperplane.cl_insert_eq_univ

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
-- changed `univ` to `M.E` 
-- hypothesis: changed `e ∉ H` to `e ∈ M.E \ H` 
-- change e ∈ M.E \ H
theorem exists_hyperplane_sep_of_not_mem_cl (h : e ∈ M.e \ M.cl X)
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    ∃ H, M.Hyperplane H ∧ X ⊆ H ∧ e ∉ H :=
  by
  obtain ⟨I, hI⟩ := M.exists_basis X
  rw [← hI.cl] at h 
  have h' := h.2
  rw [hI.indep.not_mem_cl_iff] at h' 
  obtain ⟨B, hB, heIB⟩ := h'.2.exists_base_supset
  rw [insert_subset] at heIB 
  exact
    ⟨M.cl (B \ {e}), hB.hyperplane_of_cl_diff_singleton heIB.1,
      hI.subset_cl.trans (M.cl_subset (subset_diff_singleton heIB.2 h'.1)), fun hecl =>
      indep_iff_cl_diff_ne_forall.mp hB.indep e heIB.1 (cl_diff_singleton_eq_cl hecl)⟩
#align matroid_in.exists_hyperplane_sep_of_not_mem_cl MatroidIn.exists_hyperplane_sep_of_not_mem_cl

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem cl_eq_sInter_hyperplanes (M : MatroidIn α) (X : Set α)
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.cl X = ⋂₀ {H | M.Hyperplane H ∧ X ⊆ H} ∩ M.e :=
  by
  refine' subset_antisymm (subset_inter _ (M.cl_subset_ground _)) _
  · rw [subset_sInter_iff]; rintro H ⟨hH, hXH⟩; exact hH.flat.cl_subset_of_subset hXH
  rintro e ⟨heH, heE⟩
  refine' by_contra fun hx => _
  obtain ⟨H, hH, hXH, heH'⟩ := exists_hyperplane_sep_of_not_mem_cl ⟨heE, hx⟩
  exact heH' (heH H ⟨hH, hXH⟩)
#align matroid_in.cl_eq_sInter_hyperplanes MatroidIn.cl_eq_sInter_hyperplanes

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem mem_cl_iff_forall_hyperplane
    (hX : X ⊆ M.e := by
      run_tac
        ssE)
    (he : e ∈ M.e := by
      run_tac
        ssE) :
    e ∈ M.cl X ↔ ∀ H, M.Hyperplane H → X ⊆ H → e ∈ H :=
  by
  simp_rw [M.cl_eq_cl_inter_ground X, cl_eq_sInter_hyperplanes, mem_inter_iff, and_iff_left he,
    mem_sInter, mem_set_of_eq, and_imp]
  exact
    ⟨fun h H hH hXH => h _ hH ((inter_subset_left _ _).trans hXH), fun h H hH hXH =>
      h H hH (by rwa [inter_eq_self_of_subset_left hX] at hXH )⟩
#align matroid_in.mem_cl_iff_forall_hyperplane MatroidIn.mem_cl_iff_forall_hyperplane

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem mem_dual_cl_iff_forall_circuit
    (hX : X ⊆ M.e := by
      run_tac
        ssE)
    (he : e ∈ M.e := by
      run_tac
        ssE) :
    e ∈ M﹡.cl X ↔ ∀ C, M.Circuit C → e ∈ C → (X ∩ C).Nonempty :=
  by
  rw [← dual_dual M]
  simp_rw [dual_circuit_iff_cocircuit, dual_dual M, mem_cl_iff_forall_hyperplane]
  refine' ⟨fun h C hC heC => _, fun h H hH hXH => by_contra fun heH => _⟩
  · specialize h _ hC.compl_hyperplane
    rwa [imp_iff_not (fun he => he.2 heC : e ∉ M﹡.e \ C), subset_diff, not_and, dual_ground,
      imp_iff_right hX, not_disjoint_iff_nonempty_inter] at h 
  obtain ⟨f, hf⟩ := h _ hH.compl_cocircuit ⟨he, heH⟩
  exact hf.2.2 (hXH hf.1)
#align matroid_in.mem_dual_cl_iff_forall_circuit MatroidIn.mem_dual_cl_iff_forall_circuit

theorem Flat.subset_hyperplane_of_ne_ground (hF : M.Flat F) (h : F ≠ M.e) :
    ∃ H, M.Hyperplane H ∧ F ⊆ H :=
  by
  obtain ⟨e, heE, heF⟩ := exists_of_ssubset (hF.subset_ground.ssubset_of_ne h)
  rw [← hF.cl] at heF 
  obtain ⟨H, hH, hFH, -⟩ := exists_hyperplane_sep_of_not_mem_cl ⟨heE, heF⟩
  exact ⟨H, hH, hFH⟩
#align matroid_in.flat.subset_hyperplane_of_ne_ground MatroidIn.Flat.subset_hyperplane_of_ne_ground

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem subset_hyperplane_iff_cl_ne_ground
    (hY : Y ⊆ M.e := by
      run_tac
        ssE) :
    M.cl Y ≠ M.e ↔ ∃ H, M.Hyperplane H ∧ Y ⊆ H :=
  by
  refine' ⟨fun h => _, _⟩
  · obtain ⟨H, hH, hYH⟩ := (M.flat_of_cl Y).subset_hyperplane_of_ne_ground h
    exact ⟨H, hH, (M.subset_cl Y).trans hYH⟩
  rintro ⟨H, hH, hYH⟩ hY
  refine' hH.ssubset_ground.not_subset _
  rw [← hH.flat.cl]
  exact hY.symm.trans_subset (M.cl_mono hYH)
#align matroid_in.subset_hyperplane_iff_cl_ne_ground MatroidIn.subset_hyperplane_iff_cl_ne_ground

end Hyperplane

-- section from_axioms
-- lemma matroid_of_flat_aux [finite E] (flat : set α → Prop) (univ_flat : flat univ)
-- (flat_inter : ∀ F₁ F₂, flat F₁ → flat F₂ → flat (F₁ ∩ F₂)) (X : set α) :
--   flat (⋂₀ {F | flat F ∧ X ⊆ F}) ∧ ∀ F₀, flat F₀ → ((⋂₀ {F | flat F ∧ X ⊆ F}) ⊆ F₀ ↔ X ⊆ F₀) :=
-- begin
--   set F₁ := ⋂₀ {F | flat F ∧ X ⊆ F} with hF₁,
--   refine ⟨_, λ F₀ hF₀, ⟨λ hF₁F₀, _, λ hXF, _⟩⟩ ,
--   { obtain ⟨F',⟨hF',hYF'⟩,hmin⟩ := finite.exists_minimal (λ F, flat F ∧ X ⊆ F)
--       ⟨univ, univ_flat, subset_univ _⟩,
--     convert hF',
--     refine subset_antisymm (sInter_subset_of_mem ⟨hF',hYF'⟩) (subset_sInter _),
--     rintro F ⟨hF,hYF⟩,
--     rw hmin _ ⟨flat_inter _ _ hF hF', subset_inter hYF hYF'⟩ _,
--     { apply inter_subset_left},
--     apply inter_subset_right},
--   { refine subset_trans (subset_sInter (λ F h, _)) hF₁F₀, exact h.2},
--   apply sInter_subset_of_mem,
--   exact ⟨hF₀, hXF⟩,
-- end
-- /-- A collection of sets satisfying the flat axioms determines a matroid -/
-- def matroid_of_flat [finite E] (flat : set α → Prop) (univ_flat : flat univ)
-- (flat_inter : ∀ F₁ F₂, flat F₁ → flat F₂ → flat (F₁ ∩ F₂))
-- (flat_partition : ∀ F₀ e, flat F₀ → e ∉ F₀ →
--   ∃! F₁, flat F₁ ∧ insert e F₀ ⊆ F₁ ∧ ∀ F, flat F → F₀ ⊆ F → F ⊂ F₁ → F₀ = F) :=
-- matroid_of_cl_of_finite (λ X, ⋂₀ {F | flat F ∧ X ⊆ F})
-- (λ X, subset_sInter (λ F, and.right))
-- (λ X Y hXY, subset_sInter (λ F hF, by {apply sInter_subset_of_mem, exact ⟨hF.1, hXY.trans hF.2⟩}))
-- (begin
--   refine λ X, (subset_sInter (λ F, and.right)).antisymm' _,
--   simp only [subset_sInter_iff, mem_set_of_eq, and_imp],
--   rintro F hF hXF,
--   apply sInter_subset_of_mem,
--   split, assumption,
--   apply sInter_subset_of_mem,
--   exact ⟨hF, hXF⟩,
-- end )
-- (begin
--   simp only [mem_diff, mem_sInter, mem_set_of_eq, and_imp, not_forall, exists_prop,
--     forall_exists_index],
--   refine λ X e f h F₀ hF₀ hXF₀ hfF₀, ⟨λ Ff hFf hfXf, _,
--     ⟨F₀, hF₀, hXF₀, λ heF₀, hfF₀ (h _ hF₀ (insert_subset.mpr ⟨heF₀,hXF₀⟩))⟩⟩,
--   obtain ⟨hFX, hX'⟩    := matroid_of_flat_aux flat univ_flat flat_inter X,
--   obtain ⟨hFXe, hXe'⟩  := matroid_of_flat_aux flat univ_flat flat_inter (insert e X),
--   obtain ⟨hFXf, hXf'⟩  := matroid_of_flat_aux flat univ_flat flat_inter (insert f X),
--   set FX := sInter {F | flat F ∧ X ⊆ F} with hFX_def,
--   set FXe := sInter {F | flat F ∧ insert e X ⊆ F} with hFXe_def,
--   set FXf := sInter {F | flat F ∧ insert f X ⊆ F} with hFXe_def,
--   apply (hXf' Ff hFf).mpr hfXf,
--   have heFXe : e ∈ FXe := mem_sInter.mpr (λ _ hF, hF.2 (mem_insert _ _)),
--   have hfFXf : f ∈ FXf := mem_sInter.mpr (λ _ hF, hF.2 (mem_insert _ _)),
--   have hXFX : X ⊆ FX := subset_sInter (λ _, and.right),
--   have hfFX : f ∉ FX := λ hfFX, hfF₀ ((hX' F₀ hF₀).mpr hXF₀ hfFX),
--   have heFX : e ∉ FX := λ heFX, hfFX (h _ hFX (insert_subset.mpr ⟨heFX, hXFX⟩)),
--   have hFXFXe : FX ⊆ FXe,
--   { rw [hX' FXe hFXe], exact subset_sInter (λ F hF, (subset_insert _ _).trans hF.2)},
--   have hFXFXf : FX ⊆ FXf,
--   { rw [hX' FXf hFXf], exact subset_sInter (λ F hF, (subset_insert _ _).trans hF.2)},
--   have hfFXe := h FXe hFXe (insert_subset.mpr ⟨heFXe,hXFX.trans hFXFXe⟩),
--   have hss := (hXf' _ hFXe).mpr (insert_subset.mpr ⟨hfFXe, hXFX.trans hFXFXe⟩),
--   suffices h_eq : FXf = FXe, by rwa h_eq,
--   by_contra h_ne, apply hfFX,
--   have hssu := ssubset_of_subset_of_ne hss h_ne,
--   obtain ⟨FXe',⟨hFXe',heFX',hmin⟩, hunique⟩ := flat_partition FX e hFX heFX,
--   have hFXemin : ∀ (F : set α), flat F → FX ⊆ F → F ⊂ FXe → FX = F, from
--   λ F hF hFXF hFFXe, hmin _ hF hFXF
--     (hFFXe.trans_subset ((hXe' _ hFXe').mpr ((insert_subset_insert hXFX).trans heFX'))),
--   rw hunique FXe ⟨hFXe, insert_subset.mpr ⟨heFXe, hFXFXe⟩, hFXemin⟩ at hssu,
--   rwa ← (hmin _ hFXf hFXFXf hssu) at hfFXf,
-- end)
-- @[simp] lemma matroid_of_flat_apply [finite E] (flat : set α → Prop) (univ_flat : flat univ)
-- (flat_inter : ∀ F₁ F₂, flat F₁ → flat F₂ → flat (F₁ ∩ F₂))
-- (flat_partition : ∀ F₀ e, flat F₀ → e ∉ F₀ →
-- ∃! F₁, flat F₁ ∧ insert e F₀ ⊆ F₁ ∧ ∀ F, flat F → F₀ ⊆ F → F ⊂ F₁ → F₀ = F) :
--   (matroid_of_flat flat univ_flat flat_inter flat_partition).flat = flat :=
-- begin
--   ext F,
--   simp_rw [matroid_of_flat, matroid.flat_iff_cl_self, matroid_of_cl_of_finite_apply],
--   refine ⟨λ hF, _, λ hF, _⟩,
--   { rw ←hF, exact (matroid_of_flat_aux flat univ_flat flat_inter _).1},
--   exact (subset_sInter (λ F', and.right)).antisymm' (sInter_subset_of_mem ⟨hF,rfl.subset⟩),
-- end
-- end from_axioms
end MatroidIn


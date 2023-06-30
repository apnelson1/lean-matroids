import Oneshot.Restriction
import Oneshot.Mathlib.Data.Set.Basic

noncomputable section

open scoped Classical

open scoped BigOperators

open Set

namespace MatroidIn

variable {α : Type _} {M : MatroidIn α} {I J B C X Y : Set α} {e f x y : α}

/-- A flat is a maximal set having a given basis  -/
def Flat (M : MatroidIn α) (F : Set α) : Prop :=
  (∀ ⦃I X⦄, M.Basis I F → M.Basis I X → X ⊆ F) ∧ F ⊆ M.e
#align matroid_in.flat MatroidIn.Flat

theorem ground_flat (M : MatroidIn α) : M.Flat M.e :=
  ⟨fun _ _ _ => Basis.subset_ground, Subset.rfl⟩
#align matroid_in.ground_flat MatroidIn.ground_flat

/-- The closure of a subset of the ground set is the intersection of the flats containing it. 
  A set `X` that doesn't satisfy `X ⊆ M.E` has the junk value `M.cl X := M.cl (X ∩ M.E)`. -/
def cl (M : MatroidIn α) (X : Set α) : Set α :=
  ⋂₀ {F | M.Flat F ∧ X ∩ M.e ⊆ F}
#align matroid_in.cl MatroidIn.cl

theorem cl_def (M : MatroidIn α) (X : Set α) : M.cl X = ⋂₀ {F | M.Flat F ∧ X ∩ M.e ⊆ F} :=
  rfl
#align matroid_in.cl_def MatroidIn.cl_def

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem cl_eq_sInter_of_subset (X : Set α)
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.cl X = ⋂₀ {F | M.Flat F ∧ X ⊆ F} := by rw [cl, inter_eq_self_of_subset_left hX]
#align matroid_in.cl_eq_sInter_of_subset MatroidIn.cl_eq_sInter_of_subset

theorem cl_eq_cl_inter_ground (M : MatroidIn α) (X : Set α) : M.cl X = M.cl (X ∩ M.e) := by
  rw [cl_def, cl_eq_sInter_of_subset]
#align matroid_in.cl_eq_cl_inter_ground MatroidIn.cl_eq_cl_inter_ground

theorem inter_ground_subset_cl (M : MatroidIn α) (X : Set α) : X ∩ M.e ⊆ M.cl X := by
  rw [cl_eq_cl_inter_ground]; simp [cl_def]
#align matroid_in.inter_ground_subset_cl MatroidIn.inter_ground_subset_cl

@[ssE_finish_rules]
theorem cl_subset_ground (M : MatroidIn α) (X : Set α) : M.cl X ⊆ M.e :=
  by
  apply sInter_subset_of_mem
  simp only [mem_set_of_eq, inter_subset_right, and_true_iff]
  apply ground_flat
#align matroid_in.cl_subset_ground MatroidIn.cl_subset_ground

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem mem_cl_iff_forall_mem_flat (X : Set α)
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    e ∈ M.cl X ↔ ∀ F, M.Flat F → X ⊆ F → e ∈ F := by
  simp_rw [cl_eq_sInter_of_subset, mem_sInter, mem_set_of_eq, and_imp]
#align matroid_in.mem_cl_iff_forall_mem_flat MatroidIn.mem_cl_iff_forall_mem_flat

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem subset_cl (M : MatroidIn α) (X : Set α)
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    X ⊆ M.cl X := by rw [cl_eq_sInter_of_subset, subset_sInter_iff]; simp
#align matroid_in.subset_cl MatroidIn.subset_cl

theorem Flat.cl {F : Set α} (hF : M.Flat F) : M.cl F = F :=
  (sInter_subset_of_mem (by simpa)).antisymm (M.subset_cl F hF.2)
#align matroid_in.flat.cl MatroidIn.Flat.cl

/- `cl_flat` was previously commented out.
    It is now uncommented for `loop.mem_flat` -/
@[simp]
theorem cl_ground (M : MatroidIn α) : M.cl M.e = M.e :=
  (cl_subset_ground M M.e).antisymm (M.subset_cl _)
#align matroid_in.cl_ground MatroidIn.cl_ground

@[simp]
theorem cl_univ (M : MatroidIn α) : M.cl univ = M.e := by
  rw [cl_eq_cl_inter_ground, univ_inter, cl_ground]
#align matroid_in.cl_univ MatroidIn.cl_univ

@[simp]
theorem cl_cl (M : MatroidIn α) (X : Set α) : M.cl (M.cl X) = M.cl X :=
  by
  nth_rw 3 [cl_eq_cl_inter_ground]
  nth_rw 2 [cl_eq_cl_inter_ground]
  refine' (M.subset_cl _ (cl_subset_ground _ _)).antisymm' fun e he => _
  rw [mem_cl_iff_forall_mem_flat] at *
  refine' fun F hF hXF => he _ hF fun f hf => _
  rw [mem_cl_iff_forall_mem_flat] at hf 
  exact hf _ hF hXF
#align matroid_in.cl_cl MatroidIn.cl_cl

theorem cl_subset (M : MatroidIn α) (h : X ⊆ Y) : M.cl X ⊆ M.cl Y :=
  by
  rw [cl_eq_cl_inter_ground, M.cl_eq_cl_inter_ground Y]
  refine' sInter_subset_sInter _
  simp only [ground_inter_left, set_of_subset_set_of, and_imp]
  exact fun F hF hiF => ⟨hF, subset_trans (inter_subset_inter_left _ h) hiF⟩
#align matroid_in.cl_subset MatroidIn.cl_subset

theorem cl_mono (M : MatroidIn α) : Monotone M.cl :=
  by
  intro X Y h
  nth_rw 2 [cl_eq_cl_inter_ground]
  rw [cl_eq_cl_inter_ground]
  apply cl_subset
  exact inter_subset_inter_left M.E h
#align matroid_in.cl_mono MatroidIn.cl_mono

theorem cl_subset_cl (hXY : X ⊆ M.cl Y) : M.cl X ⊆ M.cl Y := by
  simpa only [cl_cl] using M.cl_subset hXY
#align matroid_in.cl_subset_cl MatroidIn.cl_subset_cl

theorem cl_subset_cl_iff_subset_cl' : X ⊆ M.e ∧ M.cl X ⊆ M.cl Y ↔ X ⊆ M.cl Y :=
  ⟨fun h => (M.subset_cl _ h.1).trans h.2, fun h =>
    ⟨h.trans (cl_subset_ground _ _), cl_subset_cl h⟩⟩
#align matroid_in.cl_subset_cl_iff_subset_cl' MatroidIn.cl_subset_cl_iff_subset_cl'

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem cl_subset_cl_iff_subset_cl
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.cl X ⊆ M.cl Y ↔ X ⊆ M.cl Y :=
  by
  nth_rw 2 [← cl_subset_cl_iff_subset_cl']
  rw [and_iff_right hX]
#align matroid_in.cl_subset_cl_iff_subset_cl MatroidIn.cl_subset_cl_iff_subset_cl

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem subset_cl_of_subset (M : MatroidIn α) (hXY : X ⊆ Y)
    (hY : Y ⊆ M.e := by
      run_tac
        ssE) :
    X ⊆ M.cl Y :=
  hXY.trans (M.subset_cl Y hY)
#align matroid_in.subset_cl_of_subset MatroidIn.subset_cl_of_subset

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem mem_cl_of_mem (M : MatroidIn α) (h : x ∈ X)
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    x ∈ M.cl X :=
  (M.subset_cl X hX) h
#align matroid_in.mem_cl_of_mem MatroidIn.mem_cl_of_mem

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem mem_cl_of_mem' (M : MatroidIn α) (h : e ∈ X)
    (hX : e ∈ M.e := by
      run_tac
        ssE) :
    e ∈ M.cl X := by rw [cl_eq_cl_inter_ground]; apply mem_cl_of_mem; exact ⟨h, hX⟩
#align matroid_in.mem_cl_of_mem' MatroidIn.mem_cl_of_mem'

theorem cl_insert_eq_of_mem_cl (he : e ∈ M.cl X) : M.cl (insert e X) = M.cl X :=
  by
  refine' (M.cl_mono (subset_insert _ _)).antisymm' _
  rw [← M.cl_cl X]
  rw [cl_eq_cl_inter_ground]
  nth_rw 3 [cl_eq_cl_inter_ground]
  apply cl_subset
  rintro x ⟨h | h, hx⟩
  · rw [h, ← cl_eq_cl_inter_ground]
    exact he
  · apply subset_cl; use h, hx
#align matroid_in.cl_insert_eq_of_mem_cl MatroidIn.cl_insert_eq_of_mem_cl

@[simp]
theorem cl_union_cl_right_eq (M : MatroidIn α) (X Y : Set α) : M.cl (X ∪ M.cl Y) = M.cl (X ∪ Y) :=
  by
  refine' subset_antisymm _ _
  · rw [cl_eq_cl_inter_ground, inter_distrib_right, ← cl_cl _ (X ∪ Y)]
    refine'
      M.cl_subset
        (union_subset ((inter_ground_subset_cl _ _).trans (cl_subset _ (subset_union_left _ _))) _)
    rw [ground_inter_left]
    exact cl_subset _ (subset_union_right _ _)
  rw [cl_eq_cl_inter_ground, inter_distrib_right]
  exact
    cl_subset _
      (union_subset ((inter_subset_left _ _).trans (subset_union_left _ _))
        ((inter_ground_subset_cl _ _).trans (subset_union_right _ _)))
#align matroid_in.cl_union_cl_right_eq MatroidIn.cl_union_cl_right_eq

@[simp]
theorem cl_union_cl_left_eq (M : MatroidIn α) (X Y : Set α) : M.cl (M.cl X ∪ Y) = M.cl (X ∪ Y) := by
  rw [union_comm, cl_union_cl_right_eq, union_comm]
#align matroid_in.cl_union_cl_left_eq MatroidIn.cl_union_cl_left_eq

@[simp]
theorem cl_cl_union_cl_eq_cl_union (M : MatroidIn α) (X Y : Set α) :
    M.cl (M.cl X ∪ M.cl Y) = M.cl (X ∪ Y) := by rw [cl_union_cl_left_eq, cl_union_cl_right_eq]
#align matroid_in.cl_cl_union_cl_eq_cl_union MatroidIn.cl_cl_union_cl_eq_cl_union

@[simp]
theorem cl_insert_cl_eq_cl_insert (M : MatroidIn α) (e : α) (X : Set α) :
    M.cl (insert e (M.cl X)) = M.cl (insert e X) := by
  simp_rw [← singleton_union, cl_union_cl_right_eq]
#align matroid_in.cl_insert_cl_eq_cl_insert MatroidIn.cl_insert_cl_eq_cl_insert

@[simp]
theorem cl_diff_loops_eq_cl (M : MatroidIn α) (X : Set α) : M.cl (X \ M.cl ∅) = M.cl X := by
  rw [← union_empty (X \ M.cl ∅), ← cl_union_cl_right_eq, diff_union_self, cl_union_cl_right_eq,
    union_empty]
#align matroid_in.cl_diff_loops_eq_cl MatroidIn.cl_diff_loops_eq_cl

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem mem_cl_self (M : MatroidIn α) (e : α)
    (he : e ∈ M.e := by
      run_tac
        ssE) :
    e ∈ M.cl {e} :=
  singleton_subset_iff.mp (M.subset_cl {e} (singleton_subset_iff.mpr he))
#align matroid_in.mem_cl_self MatroidIn.mem_cl_self

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic matroid_in.ssE -/
/- need the assumption `e ∈ M.E` for otherwise
  `e ∉ M.E` but `e ∈ M.cl {e} ⊆ M.E`, a contradiction -/
theorem Indep.cl_eq_setOf_basis (hI : M.indep I) : M.cl I = {x | M.Basis I (insert x I)} :=
  by
  set F := {x | M.basis I (insert x I)} with hF
  have hIF : M.basis I F := by
    rw [basis_iff]
    refine'
      ⟨hI, fun e he => by rw [hF, mem_set_of, insert_eq_of_mem he]; exact hI.basis_self,
        fun J hJ hIJ hJF => hIJ.antisymm fun e he => _⟩
    rw [basis.eq_of_subset_indep (hJF he) (hJ.subset (insert_subset.mpr ⟨he, hIJ⟩))
        (subset_insert _ _) subset.rfl]
    exact mem_insert _ _
    rw [hF]; rintro e ⟨_, he⟩
    rw [← singleton_union] at he 
    exact singleton_subset_iff.mp (union_subset_iff.mp he).1
  have hF : M.flat F :=
    by
    refine'
      ⟨fun J Y hJF hJY y hy =>
        indep.basis_of_forall_insert hI (subset_insert _ _) (fun e he => _)
          (insert_subset.mpr
            ⟨hJY.subset_ground hy, by
              run_tac
                ssE⟩),
        hIF.subset_ground⟩
    refine'
      (basis.insert_dep (hIF.transfer hJF (subset_union_right _ _) (hJY.basis_union hJF))
          (mem_of_mem_of_subset he _)).1
    rw [diff_subset_iff, union_diff_self, insert_subset]
    simp only [mem_union, subset_union_left, and_true_iff]
    right; left; exact hy
  rw [subset_antisymm_iff, cl, subset_sInter_iff]
  refine' ⟨sInter_subset_of_mem ⟨hF, (inter_subset_left I M.E).trans hIF.subset⟩, _⟩
  rintro F' ⟨hF', hIF'⟩ e (he : M.basis I (insert e I))
  rw [inter_eq_left_iff_subset.mpr (hIF.subset.trans hIF.subset_ground)] at hIF' 
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset hIF' hF'.2
  exact (hF'.1 hJ (he.basis_union_of_subset hJ.indep hIJ)) (Or.inr (mem_insert _ _))
#align matroid_in.indep.cl_eq_set_of_basis MatroidIn.Indep.cl_eq_setOf_basis

theorem cl_diff_self_eq_cl_inter_ground_diff (M : MatroidIn α) :
    M.cl X \ X = M.cl (X ∩ M.e) \ (X ∩ M.e) :=
  by
  rw [cl_eq_cl_inter_ground, diff_eq_diff_iff_inter_eq_inter, inter_eq_inter_iff_left, inter_comm X]
  exact
    ⟨(inter_subset_right _ _).trans (inter_subset_right _ _),
      inter_subset_inter_left _ (M.cl_subset_ground _)⟩
#align matroid_in.cl_diff_self_eq_cl_inter_ground_diff MatroidIn.cl_diff_self_eq_cl_inter_ground_diff

theorem Indep.mem_cl_iff' (hI : M.indep I) :
    x ∈ M.cl I ↔ x ∈ M.e ∧ (M.indep (insert x I) → x ∈ I) :=
  by
  simp_rw [hI.cl_eq_set_of_basis, mem_set_of_eq]
  refine'
    ⟨fun h =>
      ⟨h.subset_ground (mem_insert _ _), fun h' => h.mem_of_insert_indep (mem_insert _ _) h'⟩,
      fun h => _⟩
  refine'
    hI.basis_of_forall_insert (subset_insert x I) (fun e he hei => he.2 _)
      (insert_subset.mpr ⟨h.1, hI.subset_ground⟩)
  rw [← singleton_union, union_diff_right, mem_diff, mem_singleton_iff] at he 
  rw [he.1] at hei ⊢
  exact h.2 hei
#align matroid_in.indep.mem_cl_iff' MatroidIn.Indep.mem_cl_iff'

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Indep.mem_cl_iff (hI : M.indep I)
    (hx : x ∈ M.e := by
      run_tac
        ssE) :
    x ∈ M.cl I ↔ M.indep (insert x I) → x ∈ I :=
  by
  simp_rw [hI.mem_cl_iff', and_iff_right_iff_imp]
  intro; exact hx
#align matroid_in.indep.mem_cl_iff MatroidIn.Indep.mem_cl_iff

theorem Indep.mem_cl_iff_insert_dep_or_mem (hI : M.indep I) :
    x ∈ M.cl I ↔ M.Dep (insert x I) ∨ x ∈ I :=
  by
  rw [hI.mem_cl_iff', dep_iff, insert_subset, and_iff_left hI.subset_ground, imp_iff_not_or]
  refine' (em' (x ∈ M.E)).elim (fun hxE => _) (by tauto)
  rw [iff_false_intro hxE, false_and_iff, and_false_iff, false_or_iff, false_iff_iff]
  exact not_mem_subset hI.subset_ground hxE
#align matroid_in.indep.mem_cl_iff_insert_dep_or_mem MatroidIn.Indep.mem_cl_iff_insert_dep_or_mem

theorem Indep.insert_dep_iff (hI : M.indep I) : M.Dep (insert e I) ↔ e ∈ M.cl I \ I :=
  by
  rw [mem_diff, hI.mem_cl_iff_insert_dep_or_mem, or_and_right, and_not_self_iff, or_false_iff,
    iff_self_and]
  refine' fun hd heI => hd.not_indep _
  rwa [insert_eq_of_mem heI]
#align matroid_in.indep.insert_dep_iff MatroidIn.Indep.insert_dep_iff

theorem Indep.mem_cl_iff_of_not_mem (hI : M.indep I) (heI : e ∉ I) :
    e ∈ M.cl I ↔ M.Dep (insert e I) := by
  rw [hI.mem_cl_iff', dep_iff, insert_subset, and_iff_left hI.subset_ground]; tauto
#align matroid_in.indep.mem_cl_iff_of_not_mem MatroidIn.Indep.mem_cl_iff_of_not_mem

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Indep.not_mem_cl_iff (hI : M.indep I)
    (he : e ∈ M.e := by
      run_tac
        ssE) :
    e ∉ M.cl I ↔ e ∉ I ∧ M.indep (insert e I) := by
  rw [← not_iff_not, not_not_mem, and_comm', not_and, hI.mem_cl_iff, not_not_mem]
#align matroid_in.indep.not_mem_cl_iff MatroidIn.Indep.not_mem_cl_iff

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Indep.not_mem_cl_iff_of_not_mem (hI : M.indep I) (heI : e ∉ I)
    (he : e ∈ M.e := by
      run_tac
        ssE) :
    e ∉ M.cl I ↔ M.indep (insert e I) := by rw [hI.mem_cl_iff_of_not_mem heI, not_dep_iff]
#align matroid_in.indep.not_mem_cl_iff_of_not_mem MatroidIn.Indep.not_mem_cl_iff_of_not_mem

theorem iInter_cl_eq_cl_iInter_of_iUnion_indep {ι : Type _} (I : ι → Set α) [hι : Nonempty ι]
    (h : M.indep (⋃ i, I i)) : (⋂ i, M.cl (I i)) = M.cl (⋂ i, I i) :=
  by
  have hi : ∀ i, M.indep (I i) := fun i => h.subset (subset_Union _ _)
  refine' subset.antisymm _ (subset_Inter fun i => M.cl_subset (Inter_subset _ _))
  rintro e he; rw [mem_Inter] at he 
  by_contra h'
  obtain i₀ := hι.some
  have hiu : (⋂ i, I i) ⊆ ⋃ i, I i := (Inter_subset _ i₀).trans (subset_Union _ i₀)
  have hi_inter : M.indep (⋂ i, I i) := (hi i₀).Subset (Inter_subset _ _)
  rw [hi_inter.not_mem_cl_iff ((M.cl_subset_ground (I i₀)) (he i₀))] at h' 
  rw [mem_Inter] at h' 
  rw [not_forall] at h' 
  · obtain ⟨⟨i₁, hei₁⟩, hei⟩ := h'
    have hdi₁ : ¬M.indep (insert e (I i₁)) := fun h_ind =>
      hei₁ (((hi i₁).mem_cl_iff'.mp (he i₁)).2 h_ind)
    have heu : e ∉ ⋃ i, I i := fun he => hdi₁ (h.subset (insert_subset.mpr ⟨he, subset_Union _ _⟩))
    have hd_all : ∀ i, ¬M.indep (insert e (I i)) := fun i hind =>
      heu (mem_Union_of_mem _ (((hi i).mem_cl_iff'.mp (he i)).2 hind))
    have hb : M.basis (⋃ i, I i) (insert e (⋃ i, I i)) :=
      by
      have h' := M.cl_subset (subset_Union _ _) (he i₀)
      rwa [h.cl_eq_set_of_basis] at h' 
    obtain ⟨I', hI', hssI', hI'ss⟩ :=
      hei.exists_basis_subset_union_basis (insert_subset_insert hiu) hb
    rw [insert_union, union_eq_right_iff_subset.mpr hiu] at hI'ss 
    have hI'I : (I' \ ⋃ i, I i) = {e} :=
      by
      refine' subset.antisymm _ (singleton_subset_iff.mpr ⟨hssI' (mem_insert _ _), heu⟩)
      rwa [diff_subset_iff, union_singleton]
    obtain ⟨f, hfI, hf⟩ := hI'.eq_exchange_of_diff_eq_singleton hb hI'I
    have hf' : ∀ i, f ∈ I i :=
      by
      refine' fun i => by_contra fun hfi => hd_all i (hI'.indep.subset (insert_subset.mpr ⟨_, _⟩))
      · exact hssI' (mem_insert _ _)
      rw [← diff_singleton_eq_self hfi, diff_subset_iff, singleton_union]
      exact ((subset_Union _ i).trans_eq hf).trans (diff_subset _ _)
    exact hfI.2 (hssI' (Or.inr (by rwa [mem_Inter])))
#align matroid_in.Inter_cl_eq_cl_Inter_of_Union_indep MatroidIn.iInter_cl_eq_cl_iInter_of_iUnion_indep

/- added the assumption `(hι : nonempty ι)`, for otherwise
   `is_empty ι` leads to a contradiction -/
theorem bInter_cl_eq_cl_sInter_of_sUnion_indep (Is : Set (Set α)) (hIs : Is.Nonempty)
    (h : M.indep (⋃₀ Is)) : (⋂ I ∈ Is, M.cl I) = M.cl (⋂₀ Is) :=
  by
  rw [sUnion_eq_Union] at h 
  rw [bInter_eq_Inter, sInter_eq_Inter]
  haveI := hIs.to_subtype
  exact Inter_cl_eq_cl_Inter_of_Union_indep (fun x : Is => coe x) h
#align matroid_in.bInter_cl_eq_cl_sInter_of_sUnion_indep MatroidIn.bInter_cl_eq_cl_sInter_of_sUnion_indep

-- as in the previous lemma, added the assumption `(hIs : nonempty Is)`
theorem inter_cl_eq_cl_inter_of_union_indep (h : M.indep (I ∪ J)) :
    M.cl I ∩ M.cl J = M.cl (I ∩ J) :=
  by
  rw [inter_eq_Inter, inter_eq_Inter]; rw [union_eq_Union] at h 
  convert Inter_cl_eq_cl_Inter_of_Union_indep (fun b => cond b I J) (by simpa)
  ext; cases x <;> simp
#align matroid_in.inter_cl_eq_cl_inter_of_union_indep MatroidIn.inter_cl_eq_cl_inter_of_union_indep

theorem Basis.cl (hIX : M.Basis I X) : M.cl I = M.cl X :=
  (M.cl_subset hIX.Subset).antisymm
    (cl_subset_cl fun x hx => hIX.indep.mem_cl_iff.mpr fun h => hIX.mem_of_insert_indep hx h)
#align matroid_in.basis.cl MatroidIn.Basis.cl

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Basis.mem_cl_iff (hIX : M.Basis I X)
    (he : e ∈ M.e := by
      run_tac
        ssE) :
    e ∈ M.cl X ↔ M.indep (insert e I) → e ∈ I := by rw [← hIX.cl, hIX.indep.mem_cl_iff]
#align matroid_in.basis.mem_cl_iff MatroidIn.Basis.mem_cl_iff

/- added the assumption `(he : e ∈ M.E . ssE)`
   as in indep.mem_cl_iff
  -/
theorem Basis.mem_cl_iff' (hIX : M.Basis I X) :
    e ∈ M.cl X ↔ e ∈ M.e ∧ (M.indep (insert e I) → e ∈ I) := by rw [← hIX.cl, hIX.indep.mem_cl_iff']
#align matroid_in.basis.mem_cl_iff' MatroidIn.Basis.mem_cl_iff'

/- only added the assumption `(he : e ∈ M.E)`
   to the RHS, as in indep.mem_cl_iff' -/
theorem Basis.mem_cl_iff_of_not_mem (hIX : M.Basis I X) (heX : e ∉ X) :
    e ∈ M.cl X ↔ M.Dep (insert e I) := by
  by_cases he : e ∈ M.E
  · rw [hIX.mem_cl_iff, iff_false_intro (not_mem_subset hIX.subset heX), imp_false, not_indep_iff]
  exact
    iff_of_false (not_mem_subset (M.cl_subset_ground _) he) fun hD =>
      he (hD.subset_ground (mem_insert _ _))
#align matroid_in.basis.mem_cl_iff_of_not_mem MatroidIn.Basis.mem_cl_iff_of_not_mem

theorem Basis.mem_cl_iff_of_not_mem' (hIX : M.Basis I X) (heX : e ∉ X) :
    e ∈ M.cl X ↔ e ∈ M.e ∧ ¬M.indep (insert e I) :=
  by
  rw [hIX.mem_cl_iff']
  refine' ⟨_, _⟩
  · rintro ⟨he, h⟩
    refine' ⟨he, fun h' => heX (hIX.subset (h h'))⟩
  · rintro ⟨he, _⟩
    use he
#align matroid_in.basis.mem_cl_iff_of_not_mem' MatroidIn.Basis.mem_cl_iff_of_not_mem'

/- only added the assumption `(he : e ∈ M.E . ssE)`
   to the RHS, as in indep.mem_cl_iff' -/
theorem Basis.subset_cl (hI : M.Basis I X) : X ⊆ M.cl I := by rw [hI.cl];
  exact M.subset_cl X hI.subset_ground
#align matroid_in.basis.subset_cl MatroidIn.Basis.subset_cl

theorem Indep.basis_cl (hI : M.indep I) : M.Basis I (M.cl I) :=
  by
  refine' hI.basis_of_forall_insert (M.subset_cl I hI.subset_ground) fun e he heI => he.2 _
  rw [mem_diff, hI.mem_cl_iff] at he 
  obtain ⟨he, he'⟩ := he
  rw [hI.mem_cl_iff_of_not_mem he'] at he 
  exact (he.not_indep heI).elim
#align matroid_in.indep.basis_cl MatroidIn.Indep.basis_cl

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (I «expr ⊆ » X) -/
theorem cl_eq_setOf_indep_not_indep (M : MatroidIn α) (X : Set α) (hX : X ⊆ M.e) :
    M.cl X = X ∪ {e | ∃ (I : _) (_ : I ⊆ X), M.indep I ∧ M.Dep (insert e I)} :=
  by
  refine'
    subset_antisymm (fun e he => (em (e ∈ X)).elim Or.inl fun heX => Or.inr _)
      (union_subset (M.subset_cl X hX) _)
  · obtain ⟨I, hI⟩ := M.exists_basis X
    refine' ⟨I, hI.subset, hI.indep, _⟩
    refine'
      hI.indep.basis_cl.dep_of_ssubset (ssubset_insert (not_mem_subset hI.subset heX))
        (insert_subset.mpr ⟨by rwa [hI.cl], M.subset_cl I hI.subset_ground_left⟩)
  rintro e ⟨I, hIX, hI, hIe⟩
  refine' (M.cl_subset hIX) _
  rw [hI.mem_cl_iff']
  refine' ⟨hIe.subset_ground (mem_insert e I), _⟩
  · intro h; rw [dep] at hIe 
    have := hIe.1; contradiction
#align matroid_in.cl_eq_set_of_indep_not_indep MatroidIn.cl_eq_setOf_indep_not_indep

theorem Indep.basis_of_subset_cl (hI : M.indep I) (hIX : I ⊆ X) (h : X ⊆ M.cl I) : M.Basis I X :=
  hI.basis_cl.basis_subset hIX h
#align matroid_in.indep.basis_of_subset_cl MatroidIn.Indep.basis_of_subset_cl

theorem Indep.base_of_cl_eq_ground (hI : M.indep I) (h : M.cl I = M.e) : M.base I := by
  rw [base_iff_basis_ground]; exact hI.basis_of_subset_cl hI.subset_ground (by rw [h])
#align matroid_in.indep.base_of_cl_eq_ground MatroidIn.Indep.base_of_cl_eq_ground

theorem Basis.basis_cl (hI : M.Basis I X) : M.Basis I (M.cl X) := by rw [← hI.cl];
  exact hI.indep.basis_cl
#align matroid_in.basis.basis_cl MatroidIn.Basis.basis_cl

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem basis_iff_basis_cl_of_subset (hIX : I ⊆ X)
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.Basis I X ↔ M.Basis I (M.cl X) :=
  ⟨fun h => h.basis_cl, fun h => h.basis_subset hIX (M.subset_cl X hX)⟩
#align matroid_in.basis_iff_basis_cl_of_subset MatroidIn.basis_iff_basis_cl_of_subset

theorem basis_iff_basis_cl_of_subset' (hIX : I ⊆ X) : M.Basis I X ↔ X ⊆ M.e ∧ M.Basis I (M.cl X) :=
  ⟨fun h => ⟨h.subset_ground, h.basis_cl⟩, fun h => h.2.basis_subset hIX (M.subset_cl X h.1)⟩
#align matroid_in.basis_iff_basis_cl_of_subset' MatroidIn.basis_iff_basis_cl_of_subset'

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Basis.basis_of_cl_eq_cl (hI : M.Basis I X) (hY : I ⊆ Y)
    (hY' : Y ⊆ M.e := by
      run_tac
        ssE)
    (h : M.cl X = M.cl Y) : M.Basis I Y := by rw [basis_iff_basis_cl_of_subset hY, ← h];
  exact hI.basis_cl
#align matroid_in.basis.basis_of_cl_eq_cl MatroidIn.Basis.basis_of_cl_eq_cl

theorem Base.cl (hB : M.base B) : M.cl B = M.e := by rw [(base_iff_basis_ground.mp hB).cl];
  exact M.cl_ground
#align matroid_in.base.cl MatroidIn.Base.cl

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Base.mem_cl (hB : M.base B) (e : α)
    (he : e ∈ M.e := by
      run_tac
        ssE) :
    e ∈ M.cl B := by rwa [base.cl hB]
#align matroid_in.base.mem_cl MatroidIn.Base.mem_cl

theorem Base.cl_of_supset (hB : M.base B) (hBX : B ⊆ X) : M.cl X = M.e :=
  subset_antisymm (M.cl_subset_ground _) (by rw [← hB.cl]; exact M.cl_subset hBX)
#align matroid_in.base.cl_of_supset MatroidIn.Base.cl_of_supset

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (B «expr ⊆ » X) -/
theorem base_subset_iff_cl_eq_ground : (∃ (B : _) (_ : B ⊆ X), M.base B) ↔ M.cl X = M.e :=
  by
  refine' ⟨fun ⟨B, hBX, hB⟩ => hB.cl_of_supset hBX, fun h => _⟩
  obtain ⟨B, hBX⟩ := M.exists_basis (X ∩ M.E)
  use B, (basis.subset hBX).trans (inter_subset_left X M.E)
  rw [base_iff_basis_ground, ← h]
  have := hBX.cl
  rw [← cl_eq_cl_inter_ground] at this 
  rw [← this]; exact hBX.indep.basis_cl
#align matroid_in.base_subset_iff_cl_eq_ground MatroidIn.base_subset_iff_cl_eq_ground

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic matroid_in.ssE -/
theorem mem_cl_insert (he : e ∉ M.cl X) (hef : e ∈ M.cl (insert f X)) : f ∈ M.cl (insert e X) :=
  by
  rw [cl_eq_cl_inter_ground] at *
  have hfE : f ∈ M.E := by by_contra' hfE; rw [insert_inter_of_not_mem hfE] at hef ; exact he hef
  have heE : e ∈ M.E;
  run_tac
    ssE
  rw [insert_inter_of_mem hfE] at hef 
  rw [insert_inter_of_mem heE]
  have hf : f ∉ M.cl (X ∩ M.E) := fun hf => he (by rwa [← cl_insert_eq_of_mem_cl hf])
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  rw [← hI.cl, hI.indep.not_mem_cl_iff heE] at he 
  rw [← hI.cl, hI.indep.not_mem_cl_iff hfE] at hf 
  have he' := hI.insert_basis_insert he.2
  rw [← he'.cl, he'.indep.mem_cl_iff, mem_insert_iff]
  have hf' := hI.insert_basis_insert hf.2
  rw [← hf'.cl, hf'.indep.mem_cl_iff heE, insert_comm, mem_insert_iff] at hef 
  intro h'
  obtain rfl | heI := hef h'
  · exact Or.inl rfl
  exact (he.1 heI).elim
#align matroid_in.mem_cl_insert MatroidIn.mem_cl_insert

theorem cl_exchange (he : e ∈ M.cl (insert f X) \ M.cl X) : f ∈ M.cl (insert e X) \ M.cl X :=
  by
  refine' ⟨mem_cl_insert he.2 he.1, fun hf => _⟩
  rw [cl_insert_eq_of_mem_cl hf, diff_self] at he 
  exact not_mem_empty _ he
#align matroid_in.cl_exchange MatroidIn.cl_exchange

theorem cl_exchange_iff : e ∈ M.cl (insert f X) \ M.cl X ↔ f ∈ M.cl (insert e X) \ M.cl X :=
  ⟨cl_exchange, cl_exchange⟩
#align matroid_in.cl_exchange_iff MatroidIn.cl_exchange_iff

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic matroid_in.ssE -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic matroid_in.ssE -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic matroid_in.ssE -/
theorem cl_insert_eq_cl_insert_of_mem (he : e ∈ M.cl (insert f X) \ M.cl X) :
    M.cl (insert e X) = M.cl (insert f X) :=
  by
  have hf := cl_exchange he
  have heE : e ∈ M.E := (M.cl_subset_ground _) he.1
  have hfE : f ∈ M.E := (M.cl_subset_ground _) hf.1
  rw [M.cl_eq_cl_inter_ground (insert f X), insert_inter_of_mem hfE] at he ⊢
  rw [M.cl_eq_cl_inter_ground, insert_inter_of_mem heE] at hf ⊢
  rw [M.cl_eq_cl_inter_ground X] at he hf 
  rw [subset_antisymm_iff, cl_subset_cl_iff_subset_cl, insert_subset]
  · refine'
      ⟨⟨he.1,
          M.subset_cl_of_subset (subset_insert _ _)
            (insert_subset.mpr
              ⟨hfE, by
                run_tac
                  ssE⟩)⟩,
        _⟩
    exact
      cl_subset_cl
        (insert_subset.mpr
          ⟨hf.1,
            M.subset_cl_of_subset (subset_insert _ _)
              (insert_subset.mpr
                ⟨heE, by
                  run_tac
                    ssE⟩)⟩)
  exact
    insert_subset.mpr
      ⟨heE, by
        run_tac
          ssE⟩
#align matroid_in.cl_insert_eq_cl_insert_of_mem MatroidIn.cl_insert_eq_cl_insert_of_mem

theorem cl_diff_singleton_eq_cl (h : e ∈ M.cl (X \ {e})) : M.cl (X \ {e}) = M.cl X :=
  by
  rw [cl_eq_cl_inter_ground, diff_eq, inter_right_comm, ← diff_eq] at *
  rw [M.cl_eq_cl_inter_ground X]
  set X' := X ∩ M.E with hX'
  refine' (M.cl_mono (diff_subset _ _)).antisymm _
  have : X' \ {e} ⊆ M.cl (X' \ {e}) :=
    by
    refine' M.subset_cl (X' \ {e}) _
    have g := inter_subset_right X M.E
    have : X' \ {e} ⊆ X' := by simp only [diff_singleton_subset_iff, subset_insert]
    rw [← hX'] at g ; exact this.trans g
  have h' := M.cl_mono (insert_subset.mpr ⟨h, this⟩)
  rw [insert_diff_singleton, cl_cl] at h' 
  exact (M.cl_mono (subset_insert _ _)).trans h'
#align matroid_in.cl_diff_singleton_eq_cl MatroidIn.cl_diff_singleton_eq_cl

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem mem_cl_diff_singleton_iff_cl (he : e ∈ X)
    (heE : e ∈ M.e := by
      run_tac
        ssE) :
    e ∈ M.cl (X \ {e}) ↔ M.cl (X \ {e}) = M.cl X :=
  by
  rw [cl_eq_cl_inter_ground, M.cl_eq_cl_inter_ground X, diff_eq, inter_right_comm, ← diff_eq]
  refine' ⟨cl_diff_singleton_eq_cl, fun h => _⟩
  rw [h]
  exact M.mem_cl_of_mem' ⟨he, heE⟩
#align matroid_in.mem_cl_diff_singleton_iff_cl MatroidIn.mem_cl_diff_singleton_iff_cl

theorem indep_iff_cl_diff_ne_forall : M.indep I ↔ ∀ e ∈ I, M.cl (I \ {e}) ≠ M.cl I :=
  by
  refine' ⟨fun hI e heI h_eq => _, fun h => _⟩
  · have hecl : e ∈ M.cl I := M.subset_cl I hI.subset_ground heI
    rw [← h_eq] at hecl 
    simpa only [(hI.diff {e}).mem_cl_iff, insert_diff_singleton, not_mem_diff_singleton,
      insert_eq_of_mem heI, imp_iff_right hI] using hecl
  have hIE : I ⊆ M.E := by
    refine' fun e he => by_contra fun heE => h e he _
    rw [M.cl_eq_cl_inter_ground I, M.cl_eq_cl_inter_ground, diff_eq, inter_right_comm, inter_assoc,
      ← diff_eq, diff_singleton_eq_self heE]
  obtain ⟨J, hJ⟩ := M.exists_basis I
  convert hJ.indep
  refine' hJ.subset.antisymm' fun e he => by_contra fun heJ => _
  have hJIe : J ⊆ I \ {e} := subset_diff_singleton hJ.subset heJ
  have hcl := h e he
  rw [Ne.def, ← mem_cl_diff_singleton_iff_cl he] at hcl 
  have hcl' := not_mem_subset (M.cl_mono hJIe) hcl
  rw [hJ.cl] at hcl' 
  refine' hcl' (M.subset_cl _ hJ.subset_ground he)
#align matroid_in.indep_iff_cl_diff_ne_forall MatroidIn.indep_iff_cl_diff_ne_forall

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem indep_iff_not_mem_cl_diff_forall
    (hI : I ⊆ M.e := by
      run_tac
        ssE) :
    M.indep I ↔ ∀ e ∈ I, e ∉ M.cl (I \ {e}) :=
  by
  rw [indep_iff_cl_diff_ne_forall]
  ·
    refine'
      ⟨fun h x hxI => by rw [mem_cl_diff_singleton_iff_cl hxI]; exact h x hxI, fun h x hxI => by
        rw [Ne.def, ← mem_cl_diff_singleton_iff_cl hxI]; exact h x hxI⟩
#align matroid_in.indep_iff_not_mem_cl_diff_forall MatroidIn.indep_iff_not_mem_cl_diff_forall

theorem indep_iff_not_mem_cl_diff_forall' : M.indep I ↔ I ⊆ M.e ∧ ∀ e ∈ I, e ∉ M.cl (I \ {e}) :=
  ⟨fun h => ⟨h.subset_ground, (indep_iff_not_mem_cl_diff_forall h.subset_ground).mp h⟩, fun h =>
    (indep_iff_not_mem_cl_diff_forall h.1).mpr h.2⟩
#align matroid_in.indep_iff_not_mem_cl_diff_forall' MatroidIn.indep_iff_not_mem_cl_diff_forall'

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
-- question: would it be better to have `e ∈ I ∩ M.E`? 
-- lemma indep_iff_cl_ssubset_ssubset_forall (hI : I ⊆ M.E . ssE) : M.indep I ↔ ∀ J ⊂ I, M.cl J ⊂ M.cl I :=
-- begin
--   refine ⟨λ hI' J hJI, _, λ h, (indep_iff_cl_diff_ne_forall hI).mpr (λ x hx, (h _ $ diff_singleton_ssubset.2 hx).ne)⟩,
--   { obtain ⟨e,heI,heJ⟩ := exists_of_ssubset hJI,
--     exact (M.cl_subset (subset_diff_singleton hJI.subset heJ)).trans_ssubset
--       ((M.cl_subset (diff_subset I {e})).ssubset_of_ne
--       ((indep_iff_cl_diff_ne_forall hI).mp hI' e heI)) }
-- end
-- /- added `I ⊆ M.E`-/
-- lemma indep_iff_cl_ssubset_ssubset_forall' : M.indep I ↔ (I ⊆ M.E ∧ ∀ J ⊂ I, M.cl J ⊂ M.cl I) :=
-- ⟨ λ h, ⟨h.subset_ground, (indep_iff_cl_ssubset_ssubset_forall h.subset_ground).mp h⟩,
--            λ h, (indep_iff_cl_ssubset_ssubset_forall h.1).mpr h.2 ⟩
-- /- added `I ⊆ M.E` to RHS -/
theorem Indep.insert_indep_iff_of_not_mem (hI : M.indep I) (he : e ∉ I)
    (he' : e ∈ M.e := by
      run_tac
        ssE) :
    M.indep (insert e I) ↔ e ∉ M.cl I :=
  ⟨fun h => (hI.not_mem_cl_iff he').mpr ⟨he, h⟩, fun h => ((hI.not_mem_cl_iff he').mp h).2⟩
#align matroid_in.indep.insert_indep_iff_of_not_mem MatroidIn.Indep.insert_indep_iff_of_not_mem

-- added `e ∈ M.E`
theorem Indep.insert_indep_iff_of_not_mem' (hI : M.indep I) (he : e ∉ I) :
    M.indep (insert e I) ↔ e ∈ M.e ∧ e ∉ M.cl I :=
  ⟨fun h =>
    ⟨h.subset_ground (mem_insert e I),
      (hI.insert_indep_iff_of_not_mem he (h.subset_ground (mem_insert e I))).mp h⟩,
    fun h => (hI.insert_indep_iff_of_not_mem he h.1).mpr h.2⟩
#align matroid_in.indep.insert_indep_iff_of_not_mem' MatroidIn.Indep.insert_indep_iff_of_not_mem'

-- added `e ∈ M.E` to RHS
theorem Indep.cl_diff_singleton_sSubset (hI : M.indep I) (he : e ∈ I) : M.cl (I \ {e}) ⊂ M.cl I :=
  ssubset_of_subset_of_ne (M.cl_mono (diff_subset _ _)) (indep_iff_cl_diff_ne_forall.mp hI _ he)
#align matroid_in.indep.cl_diff_singleton_ssubset MatroidIn.Indep.cl_diff_singleton_sSubset

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (J «expr ⊆ » I) -/
-- lemma indep.cl_ssubset_ssubset (hI : M.indep I) (hJI : J ⊂ I) : M.cl J ⊂ M.cl I :=
-- indep_iff_cl_ssubset_ssubset_forall.mp hI J hJI
theorem basis_iff_cl : M.Basis I X ↔ I ⊆ X ∧ X ⊆ M.cl I ∧ ∀ (J) (_ : J ⊆ I), X ⊆ M.cl J → J = I :=
  by
  constructor
  · refine' fun h => ⟨h.Subset, h.subset_cl, fun J hJI hXJ => hJI.antisymm fun e heI => _⟩
    rw [(h.indep.subset hJI).cl_eq_setOf_basis] at hXJ 
    exact
      (h.subset.trans hXJ heI : M.basis _ _).mem_of_insert_indep (mem_insert _ _)
        (h.indep.subset (insert_subset.mpr ⟨heI, hJI⟩))
  rintro ⟨hIX, hXI, hmin⟩
  refine' indep.basis_of_forall_insert _ hIX _ _
  · rw [indep_iff_cl_diff_ne_forall]
    intro e he hecl
    rw [← hmin _ (diff_subset _ _) (hXI.trans_eq hecl.symm)] at he 
    exact he.2 (mem_singleton e)
  exact fun e he hi =>
    he.2 ((hi.Subset (subset_insert _ _)).basis_cl.mem_of_insert_indep (hXI he.1) hi)
  exact hXI.trans (M.cl_subset_ground I)
#align matroid_in.basis_iff_cl MatroidIn.basis_iff_cl

theorem basis_union_iff_indep_cl : M.Basis I (I ∪ X) ↔ M.indep I ∧ X ⊆ M.cl I :=
  by
  refine' ⟨fun h => ⟨h.indep, (subset_union_right _ _).trans h.subset_cl⟩, _⟩
  rw [basis_iff_cl]
  rintro ⟨hI, hXI⟩
  refine'
    ⟨subset_union_left _ _, union_subset (M.subset_cl I hI.subset_ground) hXI, fun J hJI hJ =>
      by_contra fun h' => _⟩
  obtain ⟨e, heI, heJ⟩ := exists_of_ssubset (hJI.ssubset_of_ne h')
  have heJ' : e ∈ M.cl J := hJ (Or.inl heI)
  refine' indep_iff_not_mem_cl_diff_forall.mp hI e heI (mem_of_mem_of_subset heJ' _)
  exact M.cl_subset (subset_diff_singleton hJI heJ)
#align matroid_in.basis_union_iff_indep_cl MatroidIn.basis_union_iff_indep_cl

theorem basis_iff_indep_cl : M.Basis I X ↔ M.indep I ∧ X ⊆ M.cl I ∧ I ⊆ X :=
  ⟨fun h => ⟨h.indep, h.subset_cl, h.Subset⟩, fun h =>
    (basis_union_iff_indep_cl.mpr ⟨h.1, h.2.1⟩).basis_subset h.2.2 (subset_union_right _ _)⟩
#align matroid_in.basis_iff_indep_cl MatroidIn.basis_iff_indep_cl

theorem Basis.eq_of_cl_subset (hI : M.Basis I X) (hJI : J ⊆ I) (hJ : X ⊆ M.cl J) : J = I :=
  (basis_iff_cl.mp hI).2.2 J hJI hJ
#align matroid_in.basis.eq_of_cl_subset MatroidIn.Basis.eq_of_cl_subset

theorem empty_basis_iff : M.Basis ∅ X ↔ X ⊆ M.cl ∅ :=
  by
  simp only [basis_iff_cl, empty_subset, true_and_iff, and_iff_left_iff_imp]
  exact fun h J hJ hXJ => subset_empty_iff.mp hJ
#align matroid_in.empty_basis_iff MatroidIn.empty_basis_iff

theorem eq_of_cl_eq_cl_forall {M₁ M₂ : MatroidIn α} (h : ∀ X, M₁.cl X = M₂.cl X) : M₁ = M₂ :=
  by
  have h' := h univ
  repeat' rw [cl_univ] at h' 
  refine' eq_of_indep_iff_indep_forall h' fun I hI => _
  have hI' := hI; rw [h'] at hI' 
  refine' ⟨_, _⟩
  · intro hIi
    rw [indep_iff_cl_diff_ne_forall]
    intro e he
    have := indep_iff_cl_diff_ne_forall.mp hIi e he
    rwa [h (I \ {e}), h I] at this 
  intro g
  rw [indep_iff_cl_diff_ne_forall]
  intro e he
  have := (indep_iff_cl_diff_ne_forall.mp g e) he
  rwa [← h (I \ {e}), ← h I] at this 
#align matroid_in.eq_of_cl_eq_cl_forall MatroidIn.eq_of_cl_eq_cl_forall

section Spanning

variable {S T : Set α}

/-- A set is `spanning` in `M` if its closure is equal to `M.E`, or equivalently if it contains 
  a base of `M`. -/
def Spanning (M : MatroidIn α) (S : Set α) :=
  M.cl S = M.e ∧ S ⊆ M.e
#align matroid_in.spanning MatroidIn.Spanning

@[ssE_finish_rules]
theorem Spanning.subset_ground (hS : M.Spanning S) : S ⊆ M.e :=
  hS.2
#align matroid_in.spanning.subset_ground MatroidIn.Spanning.subset_ground

theorem Spanning.cl (hS : M.Spanning S) : M.cl S = M.e :=
  hS.1
#align matroid_in.spanning.cl MatroidIn.Spanning.cl

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem spanning_iff_cl
    (hS : S ⊆ M.e := by
      run_tac
        ssE) :
    M.Spanning S ↔ M.cl S = M.e :=
  ⟨And.left, fun h => ⟨h, hS⟩⟩
#align matroid_in.spanning_iff_cl MatroidIn.spanning_iff_cl

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem not_spanning_iff_cl
    (hS : S ⊆ M.e := by
      run_tac
        ssE) :
    ¬M.Spanning S ↔ M.cl S ⊂ M.e :=
  by
  rw [spanning_iff_cl, ssubset_iff_subset_ne, Ne.def, iff_and_self,
    iff_true_intro (M.cl_subset_ground _)]
  refine' fun _ => trivial
#align matroid_in.not_spanning_iff_cl MatroidIn.not_spanning_iff_cl

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Spanning.supset (hS : M.Spanning S) (hST : S ⊆ T)
    (hT : T ⊆ M.e := by
      run_tac
        ssE) :
    M.Spanning T := by
  refine' ⟨(M.cl_subset_ground _).antisymm _, hT⟩
  rw [← hS.cl]
  exact M.cl_subset hST
#align matroid_in.spanning.supset MatroidIn.Spanning.supset

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Spanning.union_left (hS : M.Spanning S)
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.Spanning (S ∪ X) :=
  hS.supset (subset_union_left _ _)
#align matroid_in.spanning.union_left MatroidIn.Spanning.union_left

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Spanning.union_right (hS : M.Spanning S)
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.Spanning (X ∪ S) :=
  hS.supset (subset_union_right _ _)
#align matroid_in.spanning.union_right MatroidIn.Spanning.union_right

theorem Base.spanning (hB : M.base B) : M.Spanning B :=
  ⟨hB.cl, hB.subset_ground⟩
#align matroid_in.base.spanning MatroidIn.Base.spanning

theorem ground_spanning (M : MatroidIn α) : M.Spanning M.e :=
  ⟨M.cl_ground, rfl.Subset⟩
#align matroid_in.ground_spanning MatroidIn.ground_spanning

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Base.supset_spanning (hB : M.base B) (hBX : B ⊆ X)
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.Spanning X :=
  hB.Spanning.supset hBX
#align matroid_in.base.supset_spanning MatroidIn.Base.supset_spanning

theorem spanning_iff_supset_base' : M.Spanning S ↔ (∃ B, M.base B ∧ B ⊆ S) ∧ S ⊆ M.e :=
  by
  rw [spanning, and_congr_left_iff]
  refine' fun hSE => ⟨fun h => _, _⟩
  · obtain ⟨B, hB⟩ := M.exists_basis S
    refine' ⟨B, hB.indep.base_of_cl_eq_ground _, hB.subset⟩
    rwa [hB.cl]
  rintro ⟨B, hB, hBS⟩
  rw [subset_antisymm_iff, and_iff_right (M.cl_subset_ground _), ← hB.cl]
  exact M.cl_subset hBS
#align matroid_in.spanning_iff_supset_base' MatroidIn.spanning_iff_supset_base'

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem spanning_iff_supset_base
    (hS : S ⊆ M.e := by
      run_tac
        ssE) :
    M.Spanning S ↔ ∃ B, M.base B ∧ B ⊆ S := by rw [spanning_iff_supset_base', and_iff_left hS]
#align matroid_in.spanning_iff_supset_base MatroidIn.spanning_iff_supset_base

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem coindep_iff_compl_spanning
    (hI : I ⊆ M.e := by
      run_tac
        ssE) :
    M.Coindep I ↔ M.Spanning (M.e \ I) :=
  by
  simp_rw [coindep_iff_exists, spanning_iff_supset_base, subset_diff, disjoint_comm]
  exact
    ⟨Exists.imp fun B hB => ⟨hB.1, hB.1.subset_ground, hB.2⟩, Exists.imp fun B hB => ⟨hB.1, hB.2.2⟩⟩
#align matroid_in.coindep_iff_compl_spanning MatroidIn.coindep_iff_compl_spanning

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem spanning_iff_compl_coindep
    (hI : S ⊆ M.e := by
      run_tac
        ssE) :
    M.Spanning S ↔ M.Coindep (M.e \ S) := by simp [coindep_iff_compl_spanning]
#align matroid_in.spanning_iff_compl_coindep MatroidIn.spanning_iff_compl_coindep

theorem Coindep.compl_spanning (hI : M.Coindep I) : M.Spanning (M.e \ I) :=
  coindep_iff_compl_spanning.mp hI
#align matroid_in.coindep.compl_spanning MatroidIn.Coindep.compl_spanning

theorem Spanning.compl_coindep (hS : M.Spanning S) : M.Coindep (M.e \ S) :=
  spanning_iff_compl_coindep.mp hS
#align matroid_in.spanning.compl_coindep MatroidIn.Spanning.compl_coindep

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem coindep_iff_cl_compl_eq_ground
    (hK : X ⊆ M.e := by
      run_tac
        ssE) :
    M.Coindep X ↔ M.cl (M.e \ X) = M.e := by rw [coindep_iff_compl_spanning, spanning_iff_cl]
#align matroid_in.coindep_iff_cl_compl_eq_ground MatroidIn.coindep_iff_cl_compl_eq_ground

theorem Coindep.cl_compl (hX : M.Coindep X) : M.cl (M.e \ X) = M.e :=
  (coindep_iff_cl_compl_eq_ground hX.subset_ground).mp hX
#align matroid_in.coindep.cl_compl MatroidIn.Coindep.cl_compl

end Spanning

-- section from_axioms
-- lemma cl_diff_singleton_eq_cl' (cl : set α → set α) (M.subset_cl : ∀ X, X ⊆ cl X)
-- (cl_mono : ∀ X Y, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X )
-- {x : α} {I : set α} (h : x ∈ cl (I \ {x})) :
--   cl (I \ {x}) = cl I :=
-- begin
--   refine (cl_mono _ _ (diff_subset _ _)).antisymm _,
--   have h' := cl_mono _ _ (insert_subset.mpr ⟨h, (M.subset_cl _ )⟩),
--   rw [insert_diff_singleton, cl_idem] at h',
--   exact (cl_mono _ _ (subset_insert _ _)).trans h',
-- end
-- /-- A set is independent relative to a closure function if none of its elements are contained in 
--   the closure of their removal -/
-- def cl_indep (cl : set α → set α) (I : set α) : Prop := ∀ e ∈ I, e ∉ cl (I \ {e})   
-- lemma cl_indep_mono {cl : set α → set α} (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) {I J : set α} 
-- (hJ : cl_indep cl J) (hIJ : I ⊆ J) :
--   cl_indep cl I :=
-- (λ e heI hecl, hJ e (hIJ heI) (cl_mono (diff_subset_diff_left hIJ) hecl))
-- lemma cl_indep_aux {e : α} {I : set α} {cl : set α → set α} 
-- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X ) 
-- (h : cl_indep cl I) (heI : ¬cl_indep cl (insert e I)) : 
-- e ∈ cl I :=
-- begin
--   have he : α ∉ I, by { intro he, rw [insert_eq_of_mem he] at heI, exact heI h },
--   rw [cl_indep] at heI, push_neg at heI, 
--   obtain ⟨f, ⟨(rfl | hfI), hfcl⟩⟩ := heI, 
--   { rwa [insert_diff_self_of_not_mem he] at hfcl },
--   have hne : α ≠ f, by { rintro rfl, exact he hfI }, 
--   rw [←insert_diff_singleton_comm hne] at hfcl, 
--   convert (cl_exchange (I \ {f}) e f ⟨hfcl,h f hfI⟩).1, 
--   rw [insert_diff_singleton, insert_eq_of_mem hfI],  
-- end   
-- /-- If the closure axioms hold, then `cl`-independence gives rise to a matroid -/
-- def matroid_of_cl (cl : set α → set α) (M.subset_cl : ∀ X, X ⊆ cl X)
-- (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X )
-- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X ) 
-- (cl_indep_maximal : ∀ ⦃I X⦄, cl_indep cl I → I ⊆ X  → 
--     (maximals (⊆) {J | cl_indep cl J ∧ I ⊆ J ∧ J ⊆ X }).nonempty) :
-- matroid_in α := 
-- matroid_of_indep (cl_indep cl) 
-- (λ e he _, not_mem_empty _ he) (λ I J hJ hIJ, cl_indep_mono cl_mono hJ hIJ)
-- (begin
--   refine λ I I' hI hIn hI'm, _, 
--   obtain ⟨B, hB⟩ := cl_indep_maximal hI (subset_union_left I I'), 
--   have hB' : B ∈ maximals (⊆) {J | cl_indep cl J},  
--   { refine ⟨hB.1.1,(λ B' hB' hBB' e heB', by_contra (λ heB, _) )⟩,
--     have he' : α ∈ cl I', 
--     { refine (em (e ∈ I')).elim (λ heI', (M.subset_cl I') heI') 
--         (λ heI', cl_indep_aux cl_exchange hI'm.1 (λ hi, _)), 
--       exact heI' (hI'm.2 hi (subset_insert e _) (mem_insert e _)) },
--       have hI'B : I' ⊆ cl B, 
--     { refine λ f hf, (em (f ∈ B)).elim (λ h', M.subset_cl B h') 
--         (λ hfB', cl_indep_aux cl_exchange hB.1.1 (λ hi, hfB' _)),  
--       refine hB.2 ⟨hi,hB.1.2.1.trans (subset_insert _ _),_⟩ (subset_insert _ _) (mem_insert _ _), 
--       exact insert_subset.mpr ⟨or.inr hf,hB.1.2.2⟩ }, 
--     have heBcl := (cl_idem B).subset ((cl_mono hI'B) he'), 
--     refine cl_indep_mono cl_mono hB' (insert_subset.mpr ⟨heB', hBB'⟩) e (mem_insert _ _) _,
--     rwa [insert_diff_of_mem _ (mem_singleton e), diff_singleton_eq_self heB] },
--   obtain ⟨f,hfB,hfI⟩ := exists_of_ssubset 
--     (hB.1.2.1.ssubset_of_ne (by { rintro rfl, exact hIn hB' })), 
--   refine ⟨f, ⟨_, hfI⟩, cl_indep_mono cl_mono hB.1.1 (insert_subset.mpr ⟨hfB,hB.1.2.1⟩)⟩,    
--   exact or.elim (hB.1.2.2 hfB) (false.elim ∘ hfI) id, 
-- end)
-- (λ I X hI hIX, cl_indep_maximal hI hIX)
-- lemma cl_indep_cl_eq {cl : set α → set α }
--   (M.subset_cl : ∀ X, X ⊆ cl X )
--   (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y )
--   (cl_idem : ∀ X, cl (cl X) = cl X )
--   (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X ) 
--   (cl_indep_maximal : ∀ ⦃I X⦄, cl_indep cl I → I ⊆ X →  
--     (maximals (⊆) {J | cl_indep cl J ∧ I ⊆ J ∧ J ⊆ X }).nonempty ) (X : set α) :
-- cl X = X ∪ {e | ∃ I ⊆ X, cl_indep cl I ∧ ¬cl_indep cl (insert e I) }  :=
-- begin
--   ext f, 
--   refine ⟨λ h, (em (f ∈ X)).elim or.inl (λ hf, or.inr _), 
--     λ h, or.elim h (λ g, M.subset_cl X g) _⟩, 
--   { have hd : ¬ (cl_indep cl (insert f X)), 
--     { refine λ hi, hi f (mem_insert _ _) _, convert h, 
--       rw [insert_diff_of_mem _ (mem_singleton f), diff_singleton_eq_self hf] },
--     obtain ⟨I, hI⟩ := cl_indep_maximal (λ e he h', not_mem_empty _ he) (empty_subset X), 
--     have hXI : X ⊆ cl I,  
--     { refine λ x hx, (em (x ∈ I)).elim (λ h', M.subset_cl _ h') (λ hxI, _),
--       refine cl_indep_aux cl_exchange hI.1.1 (λ hi, hxI _),  
--       refine hI.2 ⟨hi, empty_subset (insert x I), _⟩ (subset_insert x _) (mem_insert _ _), 
--       exact insert_subset.mpr ⟨hx, hI.1.2.2⟩ },
--     have hfI : f ∈ cl I, from (cl_mono (hXI)).trans_eq (cl_idem I) h,
--     refine ⟨I, hI.1.2.2, hI.1.1, λ hi, hf (hi f (mem_insert f _) _).elim⟩,
--     rwa [insert_diff_of_mem _ (mem_singleton f), diff_singleton_eq_self],  
--     exact not_mem_subset hI.1.2.2 hf },
--   rintro ⟨I, hIX, hI, hfI⟩, 
--   exact (cl_mono hIX) (cl_indep_aux cl_exchange hI hfI), 
-- end 
-- @[simp] lemma matroid_of_cl_apply {cl : set α → set α} (M.subset_cl : ∀ X, X ⊆ cl X)
-- (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
-- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X) 
-- (cl_indep_maximal : ∀ ⦃I X⦄, cl_indep cl I → I ⊆ X →   
--     (maximals (⊆) {J | cl_indep cl J ∧ I ⊆ J ∧ J ⊆ X }).nonempty) :
-- (matroid_of_cl cl M.subset_cl cl_mono cl_idem cl_exchange cl_indep_maximal).cl = cl :=
-- begin
--   ext1 X,
--   rw [(cl_indep_cl_eq M.subset_cl cl_mono cl_idem cl_exchange cl_indep_maximal X : cl X = _), 
--     matroid_of_cl, matroid.cl_eq_set_of_indep_not_indep], 
--   simp, 
-- end 
-- @[simp] lemma matroid_of_cl_indep_iff {cl : set α → set α} (M.subset_cl : ∀ X, X ⊆ cl X)
-- (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
-- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X) 
-- (cl_indep_maximal : ∀ ⦃I X⦄, cl_indep cl I → I ⊆ X →   
--     (maximals (⊆) {J | cl_indep cl J ∧ I ⊆ J ∧ J ⊆ X }).nonempty) {I : set α}:
-- (matroid_of_cl cl M.subset_cl cl_mono cl_idem cl_exchange cl_indep_maximal).indep I ↔ cl_indep cl I :=
-- by rw [matroid_of_cl, matroid_of_indep_apply]
-- /-- The maximality axiom isn't needed if all independent sets are at most some fixed size. -/
-- def matroid_of_cl_of_indep_bounded (cl : set α → set α)
--   (M.subset_cl : ∀ X, X ⊆ cl X )
--   (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y )
--   (cl_idem : ∀ X, cl (cl X) = cl X )
--   (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X )  
--   (n : ℕ) (hn : ∀ I, cl_indep cl I → I.finite ∧ I.ncard ≤ n) :
-- matroid_in α := matroid_of_cl cl M.subset_cl cl_mono cl_idem cl_exchange
-- (exists_maximal_subset_property_of_bounded ⟨n, hn⟩)
-- @[simp] lemma matroid_of_cl_of_indep_bounded_apply (cl : set α → set α) (M.subset_cl : ∀ X, X ⊆ cl X )
-- (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X )
-- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X )  
-- (n : ℕ) (hn : ∀ I, cl_indep cl I → I.finite ∧ I.ncard ≤ n) : 
-- (matroid_of_cl_of_indep_bounded cl M.subset_cl cl_mono cl_idem cl_exchange n hn).cl = cl := 
-- by simp [matroid_of_cl_of_indep_bounded]
-- instance (cl : set α → set α) (M.subset_cl : ∀ X, X ⊆ cl X )
-- (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X )
-- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X )  
-- (n : ℕ) (hn : ∀ I, cl_indep cl I → I.finite ∧ I.ncard ≤ n) :
-- matroid.finite_rk (matroid_of_cl_of_indep_bounded cl M.subset_cl cl_mono cl_idem cl_exchange n hn) 
-- := 
-- begin
--   obtain ⟨B, h⟩ := 
--     (matroid_of_cl_of_indep_bounded cl M.subset_cl cl_mono cl_idem cl_exchange n hn).exists_base, 
--   refine h.finite_rk_of_finite (hn _ _).1, 
--   simp_rw [matroid_of_cl_of_indep_bounded, matroid_of_cl, matroid.base_iff_maximal_indep, 
--     matroid_of_indep_apply] at h, 
--   exact h.1, 
-- end 
-- /-- A finite matroid as defined by the closure axioms. -/
-- def matroid_of_cl_of_finite [finite E] (cl : set α → set α) (M.subset_cl : ∀ X, X ⊆ cl X )
-- (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
-- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X) : 
-- matroid_in α   :=
-- matroid_of_cl_of_indep_bounded cl M.subset_cl cl_mono cl_idem cl_exchange (nat.card E)
-- (λ I hI, ⟨to_finite _, by { rw [←ncard_univ], exact ncard_le_of_subset (subset_univ _) }⟩) 
-- @[simp] lemma matroid_of_cl_of_finite_apply [finite E] (cl : set α → set α) 
-- (M.subset_cl : ∀ X, X ⊆ cl X )
-- (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
-- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X) :
-- (matroid_of_cl_of_finite cl M.subset_cl cl_mono cl_idem cl_exchange).cl = cl :=
-- by simp [matroid_of_cl_of_finite] 
-- end from_axioms
end MatroidIn


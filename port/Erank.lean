import Oneshot.Loop
import Oneshot.Flat'
import Oneshot.Mathlib.Data.Set.Ncard

/- The rank of a set in a matroid `M` is the size of one of its bases. When such bases are infinite, 
  this quantity is not defined in general, so rank is not very useful when building API for 
  general matroids, even though it is often the easiest way to do things for finite matroids. 

  A good number of rank lemmas have both `r_fin` versions, for sets of finite rank in a matroid
  of potentially infinite rank, and `[finite_rk M]` version, which apply in the more commonly 
  considered case where the entire matroid has finite rank, and are implied by the `r_fin` version. 
   -/
/- The rank of a set in a matroid `M` is the size of one of its bases. When such bases are infinite, 
  this quantity is not defined in general, so rank is not very useful when building API for 
  general matroids, even though it is often the easiest way to do things for finite matroids. 

  A good number of rank lemmas have both `r_fin` versions, for sets of finite rank in a matroid
  of potentially infinite rank, and `[finite_rk M]` version, which apply in the more commonly 
  considered case where the entire matroid has finite rank, and are implied by the `r_fin` version. 
   -/
noncomputable section

open scoped Classical

open Set

namespace MatroidIn

variable {α : Type _} {M : MatroidIn α} {B X Y X' Y' Z I J : Set α} {e f x y z : α} {k n : ℕ}

section Basic

/-- The rank `r X` of a set `X` is the cardinality of one of its bases, or zero if its bases are 
  infinite -/
def er {α : Type _} (M : MatroidIn α) (X : Set α) : ℕ∞ :=
  ⨅ I : {I | M.Basis I (X ∩ M.e)}, encard (I : Set α)
#align matroid_in.er MatroidIn.er

def erk (M : MatroidIn α) :=
  M.er M.e
#align matroid_in.erk MatroidIn.erk

theorem erk_def {α : Type _} (M : MatroidIn α) : M.erk = M.er M.e :=
  rfl
#align matroid_in.erk_def MatroidIn.erk_def

theorem Basis.encard_of_inter_ground (hI : M.Basis I (X ∩ M.e)) : I.encard = M.er X :=
  by
  have hrw : ∀ J : {J : Set α | M.basis J (X ∩ M.E)}, (J : Set α).encard = I.encard := by
    rintro ⟨J, hJ⟩; exact (hI.encard_eq_encard_of_basis hJ).symm
  have : Nonempty {J : Set α | M.basis J (X ∩ M.E)} :=
    let ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
    ⟨⟨I, hI⟩⟩
  simp_rw [er, hrw, ciInf_const]
#align matroid_in.basis.encard_of_inter_ground MatroidIn.Basis.encard_of_inter_ground

theorem Basis.encard (hI : M.Basis I X) : I.encard = M.er X :=
  hI.basis_inter_ground.encard_of_inter_ground
#align matroid_in.basis.encard MatroidIn.Basis.encard

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem eq_er_iff {n : ℕ∞}
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.er X = n ↔ ∃ I, M.Basis I X ∧ I.encard = n :=
  by
  obtain ⟨I, hI⟩ := M.exists_basis X
  rw [← hI.encard]
  refine' ⟨fun h => ⟨I, hI, h⟩, _⟩
  rintro ⟨J, hJ, rfl⟩
  rw [hI.encard, hJ.encard]
#align matroid_in.eq_er_iff MatroidIn.eq_er_iff

theorem Indep.er (hI : M.indep I) : M.er I = I.encard :=
  eq_er_iff.mpr ⟨I, hI.basis_self, rfl⟩
#align matroid_in.indep.er MatroidIn.Indep.er

theorem Basis.er (hIX : M.Basis I X) : M.er I = M.er X := by rw [← hIX.encard, hIX.indep.er]
#align matroid_in.basis.er MatroidIn.Basis.er

theorem Basis.er_eq_encard (hIX : M.Basis I X) : M.er X = I.encard := by rw [← hIX.er, hIX.indep.er]
#align matroid_in.basis.er_eq_encard MatroidIn.Basis.er_eq_encard

theorem Base.er (hB : M.base B) : M.er B = M.erk := by rw [base_iff_basis_ground] at hB ;
  rw [hB.er, erk]
#align matroid_in.base.er MatroidIn.Base.er

theorem Base.encard (hB : M.base B) : B.encard = M.erk := by
  rw [(base_iff_basis_ground.mp hB).encard, erk]
#align matroid_in.base.encard MatroidIn.Base.encard

theorem er_eq_er_inter_ground (M : MatroidIn α) (X : Set α) : M.er X = M.er (X ∩ M.e) := by
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E); rwa [← hI.encard_of_inter_ground, ← basis.encard]
#align matroid_in.er_eq_er_inter_ground MatroidIn.er_eq_er_inter_ground

@[simp]
theorem er_empty (M : MatroidIn α) : M.er ∅ = 0 := by
  rw [← M.empty_indep.basis_self.encard, encard_empty]
#align matroid_in.er_empty MatroidIn.er_empty

@[simp]
theorem er_cl (M : MatroidIn α) (X : Set α) : M.er (M.cl X) = M.er X :=
  by
  rw [cl_eq_cl_inter_ground, M.er_eq_er_inter_ground X]
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  rw [← hI.er, ← hI.cl, hI.indep.basis_cl.er]
#align matroid_in.er_cl MatroidIn.er_cl

@[simp]
theorem er_union_cl_right_eq (M : MatroidIn α) (X Y : Set α) : M.er (X ∪ M.cl Y) = M.er (X ∪ Y) :=
  by rw [← er_cl, cl_union_cl_right_eq, er_cl]
#align matroid_in.er_union_cl_right_eq MatroidIn.er_union_cl_right_eq

@[simp]
theorem er_union_cl_left_eq (M : MatroidIn α) (X Y : Set α) : M.er (M.cl X ∪ Y) = M.er (X ∪ Y) := by
  rw [← er_cl, cl_union_cl_left_eq, er_cl]
#align matroid_in.er_union_cl_left_eq MatroidIn.er_union_cl_left_eq

@[simp]
theorem er_insert_cl_eq (M : MatroidIn α) (e : α) (X : Set α) :
    M.er (insert e (M.cl X)) = M.er (insert e X) := by
  rw [← union_singleton, er_union_cl_left_eq, union_singleton]
#align matroid_in.er_insert_cl_eq MatroidIn.er_insert_cl_eq

theorem er_lt_top_of_finite (M : MatroidIn α) (hX : X.Finite) : M.er X < ⊤ :=
  by
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  rw [er_eq_er_inter_ground, ← hI.encard, encard_lt_top_iff_finite]
  exact hX.subset (hI.subset.trans (inter_subset_left _ _))
#align matroid_in.er_lt_top_of_finite MatroidIn.er_lt_top_of_finite

@[simp]
theorem er_union_cl_right_eq_er_union (M : MatroidIn α) (X Y : Set α) :
    M.er (X ∪ M.cl Y) = M.er (X ∪ Y) := by rw [← er_cl, cl_union_cl_right_eq, er_cl]
#align matroid_in.er_union_cl_right_eq_er_union MatroidIn.er_union_cl_right_eq_er_union

@[simp]
theorem er_union_cl_left_eq_er_union (M : MatroidIn α) (X Y : Set α) :
    M.er (M.cl X ∪ Y) = M.er (X ∪ Y) := by rw [← er_cl, cl_union_cl_left_eq, er_cl]
#align matroid_in.er_union_cl_left_eq_er_union MatroidIn.er_union_cl_left_eq_er_union

@[simp]
theorem er_insert_cl_eq_er_insert (M : MatroidIn α) (e : α) (X : Set α) :
    M.er (insert e (M.cl X)) = M.er (insert e X) := by
  rw [← union_singleton, er_union_cl_left_eq_er_union, union_singleton]
#align matroid_in.er_insert_cl_eq_er_insert MatroidIn.er_insert_cl_eq_er_insert

theorem Basis.er_eq_er_union (hIX : M.Basis I X) (Y : Set α) : M.er (I ∪ Y) = M.er (X ∪ Y) :=
  by
  rw [← er_union_cl_right_eq_er_union, ← er_union_cl_right_eq_er_union _ _ Y]
  obtain ⟨I', hI', hII'⟩ :=
    hIX.indep.subset_basis_of_subset (hIX.subset.trans (subset_union_left _ (M.cl Y)))
  rw [← hI'.er, ← (hI'.basis_subset _ (union_subset_union_left _ hIX.subset)).er]
  refine' fun e he =>
    (hI'.subset he).elim (fun heX => Or.inl _) fun heY => subset_union_right _ _ heY
  exact hIX.mem_of_insert_indep heX (hI'.indep.subset (insert_subset.mpr ⟨he, hII'⟩))
#align matroid_in.basis.er_eq_er_union MatroidIn.Basis.er_eq_er_union

theorem Basis.er_eq_er_insert (hIX : M.Basis I X) (e : α) : M.er (insert e I) = M.er (insert e X) :=
  by rw [← union_singleton, hIX.er_eq_er_union, union_singleton]
#align matroid_in.basis.er_eq_er_insert MatroidIn.Basis.er_eq_er_insert

theorem er_le_encard (M : MatroidIn α) (X : Set α) : M.er X ≤ X.encard :=
  by
  rw [er_eq_er_inter_ground]
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  rw [← hI.encard]
  exact encard_subset_le (hI.subset.trans (inter_subset_left _ _))
#align matroid_in.er_le_encard MatroidIn.er_le_encard

theorem erk_le_encard_ground (M : MatroidIn α) : M.erk ≤ M.e.encard :=
  M.er_le_encard M.e
#align matroid_in.erk_le_encard_ground MatroidIn.erk_le_encard_ground

theorem er_mono (M : MatroidIn α) : Monotone M.er :=
  by
  rintro X Y (h : X ⊆ Y)
  rw [er_eq_er_inter_ground, M.er_eq_er_inter_ground Y]
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  obtain ⟨J, hJ, hIJ⟩ :=
    hI.indep.subset_basis_of_subset (hI.subset.trans (inter_subset_inter_left M.E h))
  rw [← hI.encard, ← hJ.encard]
  exact encard_mono hIJ
#align matroid_in.er_mono MatroidIn.er_mono

theorem Indep.encard_le_er_of_subset (hI : M.indep I) (hIX : I ⊆ X) : I.encard ≤ M.er X := by
  rw [← hI.er]; exact M.er_mono hIX
#align matroid_in.indep.encard_le_er_of_subset MatroidIn.Indep.encard_le_er_of_subset

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (I «expr ⊆ » X) -/
theorem le_er_iff {n : ℕ∞} : n ≤ M.er X ↔ ∃ (I : _) (_ : I ⊆ X), M.indep I ∧ I.encard = n :=
  by
  rw [er_eq_er_inter_ground]
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  rw [← hI.encard]
  refine' ⟨fun h => _, fun h => _⟩
  · obtain ⟨I', hI', rfl⟩ := exists_subset_encard_eq h
    exact ⟨I', hI'.trans (hI.subset.trans (inter_subset_left _ _)), hI.indep.subset hI', rfl⟩
  obtain ⟨J, hJX, hJ, rfl⟩ := h
  exact hJ.le_encard_basis (subset_inter hJX hJ.subset_ground) hI
#align matroid_in.le_er_iff MatroidIn.le_er_iff

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (I «expr ⊆ » X) -/
theorem er_le_iff {n : ℕ∞} : M.er X ≤ n ↔ ∀ (I) (_ : I ⊆ X), M.indep I → I.encard ≤ n :=
  by
  refine' ⟨fun h I hIX hI => (hI.encard_le_er_of_subset hIX).trans h, fun h => _⟩
  obtain ⟨J, hJ⟩ := M.exists_basis (X ∩ M.E)
  rw [er_eq_er_inter_ground, ← hJ.encard]
  exact h J (hJ.subset.trans (inter_subset_left _ _)) hJ.indep
#align matroid_in.er_le_iff MatroidIn.er_le_iff

/-- The submodularity axiom for the extended rank function -/
theorem er_inter_add_er_union_le_er_add_er (M : MatroidIn α) (X Y : Set α) :
    M.er (X ∩ Y) + M.er (X ∪ Y) ≤ M.er X + M.er Y :=
  by
  rw [er_eq_er_inter_ground, M.er_eq_er_inter_ground (_ ∪ _), M.er_eq_er_inter_ground X,
    M.er_eq_er_inter_ground Y, inter_inter_distrib_right, inter_distrib_right]
  obtain ⟨Ii, hIi⟩ := M.exists_basis (X ∩ M.E ∩ (Y ∩ M.E))
  obtain ⟨IX, hIX, hIX'⟩ :=
    hIi.indep.subset_basis_of_subset (hIi.subset.trans (inter_subset_left _ _))
  obtain ⟨IY, hIY, hIY'⟩ :=
    hIi.indep.subset_basis_of_subset (hIi.subset.trans (inter_subset_right _ _))
  rw [← hIX.er_eq_er_union, union_comm, ← hIY.er_eq_er_union, ← hIi.encard, ← hIX.encard, ←
    hIY.encard, union_comm, ← encard_union_add_encard_inter, add_comm]
  exact add_le_add (er_le_encard _ _) (encard_mono (subset_inter hIX' hIY'))
#align matroid_in.er_inter_add_er_union_le_er_add_er MatroidIn.er_inter_add_er_union_le_er_add_er

theorem er_eq_er_of_subset_le (hXY : X ⊆ Y) (hYX : M.er Y ≤ M.er X) : M.er X = M.er Y :=
  (M.er_mono hXY).antisymm hYX
#align matroid_in.er_eq_er_of_subset_le MatroidIn.er_eq_er_of_subset_le

alias er_inter_add_er_union_le_er_add_er ← er_submod
#align matroid_in.er_submod MatroidIn.er_submod

theorem er_union_le_er_add_er (M : MatroidIn α) (X Y : Set α) : M.er (X ∪ Y) ≤ M.er X + M.er Y :=
  le_add_self.trans (M.er_submod X Y)
#align matroid_in.er_union_le_er_add_er MatroidIn.er_union_le_er_add_er

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem er_eq_zero_iff_subset_loops
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.er X = 0 ↔ X ⊆ M.cl ∅ := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  rw [← hI.encard, encard_eq_zero]
  refine' ⟨_, fun h => _⟩
  · rintro rfl; exact hI.subset_cl
  simpa using hI.indep.encard_le_er_of_subset (hI.subset.trans h)
#align matroid_in.er_eq_zero_iff_subset_loops MatroidIn.er_eq_zero_iff_subset_loops

theorem er_eq_er_union_er_le_zero (X : Set α) (hY : M.er Y ≤ 0) : M.er (X ∪ Y) = M.er X :=
  (((M.er_union_le_er_add_er X Y).trans (add_le_add_left hY _)).trans_eq (add_zero _)).antisymm
    (M.er_mono (subset_union_left _ _))
#align matroid_in.er_eq_er_union_er_le_zero MatroidIn.er_eq_er_union_er_le_zero

theorem er_eq_er_diff_er_le_zero (X : Set α) (hY : M.er Y ≤ 0) : M.er (X \ Y) = M.er X := by
  rw [← er_eq_er_union_er_le_zero (X \ Y) hY, diff_union_self, er_eq_er_union_er_le_zero _ hY]
#align matroid_in.er_eq_er_diff_er_le_zero MatroidIn.er_eq_er_diff_er_le_zero

theorem er_le_er_inter_add_er_diff (X Y : Set α) : M.er X ≤ M.er (X ∩ Y) + M.er (X \ Y) := by
  nth_rw 1 [← inter_union_diff X Y]; apply er_union_le_er_add_er
#align matroid_in.er_le_er_inter_add_er_diff MatroidIn.er_le_er_inter_add_er_diff

theorem er_le_er_add_er_diff (h : Y ⊆ X) : M.er X ≤ M.er Y + M.er (X \ Y) := by
  nth_rw 1 [← union_diff_cancel h]; apply er_union_le_er_add_er
#align matroid_in.er_le_er_add_er_diff MatroidIn.er_le_er_add_er_diff

theorem indep_iff_er_eq_encard_of_finite (hI : I.Finite) : M.indep I ↔ M.er I = I.encard :=
  by
  refine' ⟨indep.er, fun h => _⟩
  obtain ⟨J, hJ⟩ := M.exists_basis (I ∩ M.E)
  have hJI : J ⊆ I := hJ.subset.trans (inter_subset_left _ _)
  rw [hI.encard_eq, er_eq_er_inter_ground, ← hJ.encard, (hI.subset hJI).encard_eq, Nat.cast_inj] at
    h 
  rw [← eq_of_subset_of_ncard_le hJI h.symm.le hI]
  exact hJ.indep
#align matroid_in.indep_iff_er_eq_encard_of_finite MatroidIn.indep_iff_er_eq_encard_of_finite

theorem er_singleton_le (M : MatroidIn α) (e : α) : M.er {e} ≤ 1 := by rw [er_le_iff];
  exact fun I hI _ => (encard_mono hI).trans_eq (encard_singleton e)
#align matroid_in.er_singleton_le MatroidIn.er_singleton_le

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem indep_iff_er_eq_card [Finite M]
    (hI : I ⊆ M.e := by
      run_tac
        ssE) :
    M.indep I ↔ M.er I = I.encard :=
  indep_iff_er_eq_encard_of_finite (M.set_finite I)
#align matroid_in.indep_iff_er_eq_card MatroidIn.indep_iff_er_eq_card

theorem er_lt_encard_of_dep_of_finite (h : X.Finite) (hX : M.Dep X) : M.er X < X.encard :=
  lt_of_le_of_ne (M.er_le_encard X) fun h' =>
    ((indep_iff_er_eq_encard_of_finite h).mpr h').not_dep hX
#align matroid_in.er_lt_encard_of_dep_of_finite MatroidIn.er_lt_encard_of_dep_of_finite

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem er_lt_encard_iff_dep_of_finite (hX : X.Finite)
    (hXE : X ⊆ M.e := by
      run_tac
        ssE) :
    M.er X < X.encard ↔ M.Dep X :=
  by
  rw [← not_iff_not, not_lt, not_dep_iff, indep_iff_er_eq_encard_of_finite hX, le_iff_eq_or_lt,
    eq_comm, or_iff_left]
  rw [not_lt]
  apply er_le_encard
#align matroid_in.er_lt_encard_iff_dep_of_finite MatroidIn.er_lt_encard_iff_dep_of_finite

theorem er_lt_encard_of_dep [Finite M] (hX : M.Dep X) : M.er X < X.encard :=
  er_lt_encard_of_dep_of_finite (M.set_finite _) hX
#align matroid_in.er_lt_encard_of_dep MatroidIn.er_lt_encard_of_dep

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem r_lt_card_iff_dep [Finite M]
    (hXE : X ⊆ M.e := by
      run_tac
        ssE) :
    M.er X < X.encard ↔ M.Dep X :=
  er_lt_encard_iff_dep_of_finite (M.set_finite X)
#align matroid_in.r_lt_card_iff_dep MatroidIn.r_lt_card_iff_dep

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem basis_iff_indep_encard_eq_of_finite (hIfin : I.Finite)
    (hXE : X ⊆ M.e := by
      run_tac
        ssE) :
    M.Basis I X ↔ I ⊆ X ∧ M.indep I ∧ I.encard = M.er X :=
  by
  rw [basis_iff_indep_cl, and_comm' (I ⊆ X), ← and_assoc', and_congr_left_iff, and_congr_right_iff]
  refine' fun hIX hI => ⟨fun h => (hI.encard_le_er_of_subset hIX).antisymm _, fun h => _⟩
  · refine' (M.er_mono h).trans _
    rw [er_cl, hI.er]; exact rfl.le
  intro e he
  rw [hI.mem_cl_iff (hXE he)]
  refine' fun hi => by_contra fun he' => _
  have hr := hi.er; rw [encard_insert_of_not_mem he'] at hr 
  have hle := M.er_mono (insert_subset.mpr ⟨he, hIX⟩)
  rw [hr, ← h, hIfin.encard_eq, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le] at hle 
  simpa using hle
#align matroid_in.basis_iff_indep_encard_eq_of_finite MatroidIn.basis_iff_indep_encard_eq_of_finite

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Indep.basis_of_subset_of_er_le_of_finite (hI : M.indep I) (hIX : I ⊆ X)
    (h : M.er X ≤ M.er I) (hIfin : I.Finite)
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.Basis I X :=
  by
  rw [basis_iff_indep_encard_eq_of_finite hIfin hX, and_iff_right hIX, and_iff_right hI,
    le_antisymm_iff, and_iff_left (h.trans hI.er.le)]
  exact hI.encard_le_er_of_subset hIX
#align matroid_in.indep.basis_of_subset_of_er_le_of_finite MatroidIn.Indep.basis_of_subset_of_er_le_of_finite

theorem er_insert_le_add_one (M : MatroidIn α) (e : α) (X : Set α) :
    M.er (insert e X) ≤ M.er X + 1 := by
  rw [← union_singleton]
  exact (M.er_union_le_er_add_er _ _).trans (add_le_add_left (er_singleton_le _ _) _)
#align matroid_in.er_insert_le_add_one MatroidIn.er_insert_le_add_one

theorem er_union_le_encard_add_er (M : MatroidIn α) (X Y : Set α) :
    M.er (X ∪ Y) ≤ X.encard + M.er Y :=
  (M.er_union_le_er_add_er X Y).trans (add_le_add_right (M.er_le_encard _) _)
#align matroid_in.er_union_le_encard_add_er MatroidIn.er_union_le_encard_add_er

theorem er_union_le_er_add_encard (M : MatroidIn α) (X Y : Set α) :
    M.er (X ∪ Y) ≤ M.er X + Y.encard :=
  (M.er_union_le_er_add_er X Y).trans (add_le_add_left (M.er_le_encard _) _)
#align matroid_in.er_union_le_er_add_encard MatroidIn.er_union_le_er_add_encard

theorem erk_le_encard_add_er_compl (M : MatroidIn α) (X : Set α) :
    M.erk ≤ X.encard + M.er (M.e \ X) :=
  by
  refine' le_trans _ (M.er_union_le_encard_add_er X (M.E \ X))
  rw [erk_def, union_diff_self, M.er_eq_er_inter_ground (X ∪ M.E), union_inter_cancel_right]
  exact rfl.le
#align matroid_in.erk_le_encard_add_er_compl MatroidIn.erk_le_encard_add_er_compl

theorem er_augment (h : M.er X < M.er Z) : ∃ z ∈ Z \ X, M.er (insert z X) = M.er X + 1 :=
  by
  rw [M.er_eq_er_inter_ground Z, M.er_eq_er_inter_ground] at h 
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  obtain ⟨J, hJ⟩ := M.exists_basis (Z ∩ M.E)
  obtain ⟨z, hzJ, hzI, h⟩ := hI.indep.augment_of_encard_lt hJ.indep (by rwa [hI.encard, hJ.encard])
  refine' ⟨z, ⟨(hJ.subset hzJ).1, hzI ∘ fun hzX => _⟩, _⟩
  · exact hI.mem_of_insert_indep ⟨hzX, hJ.indep.subset_ground hzJ⟩ h
  rw [← er_insert_cl_eq_er_insert, cl_eq_cl_inter_ground, ← hI.cl, er_insert_cl_eq_er_insert, h.er,
    er_eq_er_inter_ground, ← hI.encard, encard_insert_of_not_mem hzI]
#align matroid_in.er_augment MatroidIn.er_augment

theorem er_eq_of_er_insert_le_forall (hXY : X ⊆ Y) (hY : ∀ e ∈ Y \ X, M.er (insert e X) ≤ M.er X) :
    M.er X = M.er Y :=
  by
  refine' (M.er_mono hXY).antisymm (le_of_not_lt fun hlt => _)
  obtain ⟨z, hz, hr⟩ := er_augment hlt
  have hle := hY z hz
  rw [hr] at hle 
  have := ENat.eq_of_top_of_add_pos_le (by simp) hle
  rw [this] at hlt 
  exact not_top_lt hlt
#align matroid_in.er_eq_of_er_insert_le_forall MatroidIn.er_eq_of_er_insert_le_forall

end Basic

section RFin

def RFin (M : MatroidIn α) (X : Set α) :=
  M.er X < ⊤
#align matroid_in.r_fin MatroidIn.RFin

theorem rFin_iff_er_ne_top : M.RFin X ↔ M.er X ≠ ⊤ := by rw [r_fin, ← lt_top_iff_ne_top]
#align matroid_in.r_fin_iff_er_ne_top MatroidIn.rFin_iff_er_ne_top

theorem rFin_iff_er_lt_top : M.RFin X ↔ M.er X < ⊤ :=
  Iff.rfl
#align matroid_in.r_fin_iff_er_lt_top MatroidIn.rFin_iff_er_lt_top

theorem RFin.ne (h : M.RFin X) : M.er X ≠ ⊤ :=
  rFin_iff_er_ne_top.mp h
#align matroid_in.r_fin.ne MatroidIn.RFin.ne

theorem RFin.lt (h : M.RFin X) : M.er X < ⊤ :=
  h
#align matroid_in.r_fin.lt MatroidIn.RFin.lt

theorem not_rFin_iff : ¬M.RFin X ↔ M.er X = ⊤ := by rw [r_fin_iff_er_ne_top, not_ne_iff]
#align matroid_in.not_r_fin_iff MatroidIn.not_rFin_iff

theorem rFin_iff_inter_ground : M.RFin X ↔ M.RFin (X ∩ M.e) := by
  rw [r_fin, er_eq_er_inter_ground, r_fin]
#align matroid_in.r_fin_iff_inter_ground MatroidIn.rFin_iff_inter_ground

theorem RFin.to_inter_ground (h : M.RFin X) : M.RFin (X ∩ M.e) :=
  rFin_iff_inter_ground.mp h
#align matroid_in.r_fin.to_inter_ground MatroidIn.RFin.to_inter_ground

theorem RFin.finite_of_basis (h : M.RFin X) (hI : M.Basis I X) : I.Finite := by
  rwa [← encard_lt_top_iff_finite, hI.encard]
#align matroid_in.r_fin.finite_of_basis MatroidIn.RFin.finite_of_basis

theorem Basis.finite_of_rFin (hI : M.Basis I X) (h : M.RFin X) : I.Finite :=
  h.finite_of_basis hI
#align matroid_in.basis.finite_of_r_fin MatroidIn.Basis.finite_of_rFin

theorem rFin_iff' : M.RFin X ↔ ∃ I, M.Basis I (X ∩ M.e) ∧ I.Finite :=
  by
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  rw [r_fin_iff_er_ne_top, er_eq_er_inter_ground, ← hI.encard, encard_ne_top_iff_finite]
  exact ⟨fun h => ⟨I, hI, h⟩, fun ⟨J, hJ, hJfin⟩ => hJ.finite_of_finite hJfin hI⟩
#align matroid_in.r_fin_iff' MatroidIn.rFin_iff'

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem rFin_iff_exists_finite_basis
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.RFin X ↔ ∃ I, M.Basis I X ∧ I.Finite := by
  simp_rw [r_fin_iff', inter_eq_self_of_subset_left hX]
#align matroid_in.r_fin_iff_exists_finite_basis MatroidIn.rFin_iff_exists_finite_basis

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem RFin.exists_finite_basis (h : M.RFin X)
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    ∃ I, M.Basis I X ∧ I.Finite :=
  (M.exists_basis X).imp fun I hI => ⟨hI, h.finite_of_basis hI⟩
#align matroid_in.r_fin.exists_finite_basis MatroidIn.RFin.exists_finite_basis

theorem Basis.rFin_of_finite (hIX : M.Basis I X) (h : I.Finite) : M.RFin X := by
  rwa [r_fin_iff_er_ne_top, ← hIX.encard, encard_ne_top_iff_finite]
#align matroid_in.basis.r_fin_of_finite MatroidIn.Basis.rFin_of_finite

theorem Basis.rFin_iff_finite (hIX : M.Basis I X) : M.RFin X ↔ I.Finite :=
  ⟨hIX.finite_of_rFin, hIX.rFin_of_finite⟩
#align matroid_in.basis.r_fin_iff_finite MatroidIn.Basis.rFin_iff_finite

theorem Indep.rFin_iff_finite (hI : M.indep I) : M.RFin I ↔ I.Finite :=
  hI.basis_self.rFin_iff_finite
#align matroid_in.indep.r_fin_iff_finite MatroidIn.Indep.rFin_iff_finite

theorem Indep.finite_of_rFin (hI : M.indep I) (hfin : M.RFin I) : I.Finite :=
  hI.basis_self.finite_of_rFin hfin
#align matroid_in.indep.finite_of_r_fin MatroidIn.Indep.finite_of_rFin

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Indep.subset_finite_basis_of_subset_of_rFin (hI : M.indep I) (hIX : I ⊆ X) (hX : M.RFin X)
    (hXE : X ⊆ M.e := by
      run_tac
        ssE) :
    ∃ J, M.Basis J X ∧ I ⊆ J ∧ J.Finite :=
  (hI.subset_basis_of_subset hIX).imp fun J hJ => ⟨hJ.1, hJ.2, hJ.1.finite_of_rFin hX⟩
#align matroid_in.indep.subset_finite_basis_of_subset_of_r_fin MatroidIn.Indep.subset_finite_basis_of_subset_of_rFin

theorem rFin_of_finite (M : MatroidIn α) (hX : X.Finite) : M.RFin X := by rw [r_fin_iff_er_lt_top];
  exact (M.er_le_encard X).trans_lt (encard_lt_top_iff_finite.mpr hX)
#align matroid_in.r_fin_of_finite MatroidIn.rFin_of_finite

theorem rFin_singleton (M : MatroidIn α) (e : α) : M.RFin {e} :=
  M.rFin_of_finite (finite_singleton e)
#align matroid_in.r_fin_singleton MatroidIn.rFin_singleton

@[simp]
theorem rFin_empty (M : MatroidIn α) : M.RFin ∅ :=
  M.rFin_of_finite finite_empty
#align matroid_in.r_fin_empty MatroidIn.rFin_empty

theorem RFin.subset (h : M.RFin Y) (hXY : X ⊆ Y) : M.RFin X := by rw [r_fin_iff_er_lt_top] at h ⊢;
  exact (M.er_mono hXY).trans_lt h
#align matroid_in.r_fin.subset MatroidIn.RFin.subset

theorem not_rFin_supset (h : ¬M.RFin X) (hXY : X ⊆ Y) : ¬M.RFin Y := fun h' => h (h'.Subset hXY)
#align matroid_in.not_r_fin_supset MatroidIn.not_rFin_supset

theorem not_rFin_of_er_ge (h : ¬M.RFin X) (hXY : M.er X ≤ M.er Y) : ¬M.RFin Y := fun h' =>
  h (hXY.trans_lt h')
#align matroid_in.not_r_fin_of_er_ge MatroidIn.not_rFin_of_er_ge

theorem RFin.finite_of_indep_subset (hX : M.RFin X) (hI : M.indep I) (hIX : I ⊆ X) : I.Finite :=
  hI.finite_of_rFin (hX.to_inter_ground.Subset (subset_inter hIX hI.subset_ground))
#align matroid_in.r_fin.finite_of_indep_subset MatroidIn.RFin.finite_of_indep_subset

@[simp]
theorem rFin_ground_iff : M.RFin M.e ↔ M.FiniteRk :=
  by
  obtain ⟨B, hB⟩ := M.exists_base
  use fun h => ⟨⟨B, hB, h.finite_of_indep_subset hB.indep hB.subset_ground⟩⟩
  simp_rw [r_fin_iff_exists_finite_basis, ← base_iff_basis_ground]
  exact fun ⟨h⟩ => h
#align matroid_in.r_fin_ground_iff MatroidIn.rFin_ground_iff

theorem Indep.finite_of_subset_rFin (hI : M.indep I) (hIX : I ⊆ X) (hX : M.RFin X) : I.Finite :=
  hX.finite_of_indep_subset hI hIX
#align matroid_in.indep.finite_of_subset_r_fin MatroidIn.Indep.finite_of_subset_rFin

theorem RFin.to_cl (h : M.RFin X) : M.RFin (M.cl X) := by rwa [r_fin_iff_er_lt_top, er_cl]
#align matroid_in.r_fin.to_cl MatroidIn.RFin.to_cl

theorem rFin_iff_cl : M.RFin X ↔ M.RFin (M.cl X) := by
  rw [r_fin_iff_er_ne_top, ← er_cl, r_fin_iff_er_ne_top]
#align matroid_in.r_fin_iff_cl MatroidIn.rFin_iff_cl

theorem RFin.union (hX : M.RFin X) (hY : M.RFin Y) : M.RFin (X ∪ Y) :=
  by
  rw [r_fin_iff_er_lt_top] at *
  apply (M.er_union_le_er_add_er X Y).trans_lt
  rw [WithTop.add_lt_top]
  exact ⟨hX, hY⟩
#align matroid_in.r_fin.union MatroidIn.RFin.union

theorem RFin.inter_right (hX : M.RFin X) (Y : Set α) : M.RFin (X ∩ Y) :=
  hX.Subset (inter_subset_left _ _)
#align matroid_in.r_fin.inter_right MatroidIn.RFin.inter_right

theorem RFin.inter_left (hX : M.RFin X) (Y : Set α) : M.RFin (Y ∩ X) :=
  hX.Subset (inter_subset_right _ _)
#align matroid_in.r_fin.inter_left MatroidIn.RFin.inter_left

theorem RFin.diff (hX : M.RFin X) (D : Set α) : M.RFin (X \ D) :=
  hX.Subset (diff_subset _ _)
#align matroid_in.r_fin.diff MatroidIn.RFin.diff

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem RFin.insert (hX : M.RFin X) (e : α)
    (he : e ∈ M.e := by
      run_tac
        ssE) :
    M.RFin (insert e X) :=
  (M.rFin_singleton e).union hX
#align matroid_in.r_fin.insert MatroidIn.RFin.insert

theorem to_rFin (M : MatroidIn α) [FiniteRk M] (X : Set α) : M.RFin X :=
  by
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  rw [r_fin_iff_inter_ground, r_fin_iff_er_lt_top, ← hI.encard, encard_lt_top_iff_finite]
  exact hI.finite
#align matroid_in.to_r_fin MatroidIn.to_rFin

theorem RFin.cl_eq_cl_of_subset_of_er_ge_er (hX : M.RFin X) (hXY : X ⊆ Y) (hr : M.er Y ≤ M.er X) :
    M.cl X = M.cl Y :=
  by
  obtain ⟨I, J, hIX, hJY, hIJ⟩ := M.exists_basis_subset_basis (inter_subset_inter_left M.E hXY)
  rw [er_eq_er_inter_ground, ← hJY.encard, er_eq_er_inter_ground, ← hIX.encard] at hr 
  rw [cl_eq_cl_inter_ground, M.cl_eq_cl_inter_ground Y, ← hIX.cl, ← hJY.cl,
    (hIX.indep.finite_of_subset_r_fin hIX.subset hX.to_inter_ground).eq_of_subset_of_encard_le' hIJ
      hr]
#align matroid_in.r_fin.cl_eq_cl_of_subset_of_er_ge_er MatroidIn.RFin.cl_eq_cl_of_subset_of_er_ge_er

theorem RFin.cl_eq_cl_of_subset_of_er_ge_er' (hY : M.RFin Y) (hXY : X ⊆ Y) (hr : M.er Y ≤ M.er X) :
    M.cl X = M.cl Y :=
  (hY.Subset hXY).cl_eq_cl_of_subset_of_er_ge_er hXY hr
#align matroid_in.r_fin.cl_eq_cl_of_subset_of_er_ge_er' MatroidIn.RFin.cl_eq_cl_of_subset_of_er_ge_er'

theorem er_union_eq_of_subset_of_er_le_er (Z : Set α) (hXY : X ⊆ Y) (hr : M.er Y ≤ M.er X) :
    M.er (X ∪ Z) = M.er (Y ∪ Z) :=
  by
  obtain hX' | hX' := em (M.r_fin X)
  · rw [← er_union_cl_left_eq, hX'.cl_eq_cl_of_subset_of_er_ge_er hXY hr, er_union_cl_left_eq]
  rw [not_r_fin_iff.mp, not_r_fin_iff.mp]
  · exact not_r_fin_of_er_ge hX' (M.er_mono (subset_union_of_subset_left hXY _))
  exact not_r_fin_of_er_ge hX' (M.er_mono (subset_union_left _ _))
#align matroid_in.er_union_eq_of_subset_of_er_le_er MatroidIn.er_union_eq_of_subset_of_er_le_er

theorem er_union_eq_of_subsets_of_er_les (hX : X ⊆ X') (hY : Y ⊆ Y') (hXX' : M.er X' ≤ M.er X)
    (hYY' : M.er Y' ≤ M.er Y) : M.er (X ∪ Y) = M.er (X' ∪ Y') := by
  rw [er_union_eq_of_subset_of_er_le_er _ hX hXX', union_comm,
    er_union_eq_of_subset_of_er_le_er _ hY hYY', union_comm]
#align matroid_in.er_union_eq_of_subsets_of_er_les MatroidIn.er_union_eq_of_subsets_of_er_les

end RFin

section Rank

/-- The rank function. Intended to be used in a `finite_rk` matroid; otherwise `er` is better.-/
def r (M : MatroidIn α) (X : Set α) : ℕ :=
  (M.er X).toNat
#align matroid_in.r MatroidIn.r

/-- The rank of the ground set of a matroid -/
@[reducible]
def rk (M : MatroidIn α) : ℕ :=
  M.R M.e
#align matroid_in.rk MatroidIn.rk

theorem rk_def (M : MatroidIn α) : M.rk = M.R M.e :=
  rfl
#align matroid_in.rk_def MatroidIn.rk_def

@[simp]
theorem er_toNat_eq_r (M : MatroidIn α) (X : Set α) : (M.er X).toNat = M.R X :=
  rfl
#align matroid_in.er_to_nat_eq_r MatroidIn.er_toNat_eq_r

theorem RFin.coe_r_eq_er (hX : M.RFin X) : (M.R X : ℕ∞) = M.er X :=
  by
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  rwa [r, er_eq_er_inter_ground, ← hI.encard, ENat.coe_toNat_eq_self, hI.encard, ←
    er_eq_er_inter_ground, ← r_fin_iff_er_ne_top]
#align matroid_in.r_fin.coe_r_eq_er MatroidIn.RFin.coe_r_eq_er

theorem coe_r_eq_er_of_finite (M : MatroidIn α) (hX : X.Finite) : (M.R X : ℕ∞) = M.er X :=
  (M.rFin_of_finite hX).coe_r_eq_er
#align matroid_in.coe_r_eq_er_of_finite MatroidIn.coe_r_eq_er_of_finite

@[simp]
theorem coe_r_eq_er (M : MatroidIn α) [FiniteRk M] (X : Set α) : (M.R X : ℕ∞) = M.er X :=
  (M.to_rFin X).coe_r_eq_er
#align matroid_in.coe_r_eq_er MatroidIn.coe_r_eq_er

theorem r_eq_of_er_eq (h : M.er X = M.er Y) : M.R X = M.R Y := by rw [r, r, h]
#align matroid_in.r_eq_of_er_eq MatroidIn.r_eq_of_er_eq

theorem RFin.er_eq_er_iff (hX : M.RFin X) (hY : M.RFin Y) : M.er X = M.er Y ↔ M.R X = M.R Y := by
  rw [← hX.coe_r_eq_er, ← hY.coe_r_eq_er, ENat.coe_inj]
#align matroid_in.r_fin.er_eq_er_iff MatroidIn.RFin.er_eq_er_iff

theorem RFin.er_le_er_iff (hX : M.RFin X) (hY : M.RFin Y) : M.er X ≤ M.er Y ↔ M.R X ≤ M.R Y := by
  rw [← hX.coe_r_eq_er, ← hY.coe_r_eq_er, ENat.coe_le_coe_iff]
#align matroid_in.r_fin.er_le_er_iff MatroidIn.RFin.er_le_er_iff

@[simp]
theorem er_eq_er_iff [FiniteRk M] : M.er X = M.er Y ↔ M.R X = M.R Y :=
  (M.to_rFin X).er_eq_er_iff (M.to_rFin Y)
#align matroid_in.er_eq_er_iff MatroidIn.er_eq_er_iff

@[simp]
theorem er_le_er_iff [FiniteRk M] : M.er X ≤ M.er Y ↔ M.R X ≤ M.R Y := by
  rw [← coe_r_eq_er, ← coe_r_eq_er, ENat.coe_le_coe_iff]
#align matroid_in.er_le_er_iff MatroidIn.er_le_er_iff

@[simp]
theorem er_eq_coe_iff [FiniteRk M] {n : ℕ} : M.er X = n ↔ M.R X = n := by
  rw [← coe_r_eq_er, ENat.coe_inj]
#align matroid_in.er_eq_coe_iff MatroidIn.er_eq_coe_iff

@[simp]
theorem er_le_coe_iff [FiniteRk M] {n : ℕ} : M.er X ≤ n ↔ M.R X ≤ n := by
  rw [← coe_r_eq_er, ENat.coe_le_coe_iff]
#align matroid_in.er_le_coe_iff MatroidIn.er_le_coe_iff

@[simp]
theorem coe_le_er_iff [FiniteRk M] {n : ℕ} : (n : ℕ∞) ≤ M.er X ↔ n ≤ M.R X := by
  rw [← coe_r_eq_er, ENat.coe_le_coe_iff]
#align matroid_in.coe_le_er_iff MatroidIn.coe_le_er_iff

theorem RFin.r_le_r_of_er_le_er (hY : M.RFin Y) (hle : M.er X ≤ M.er Y) : M.R X ≤ M.R Y := by
  rwa [← r_fin.er_le_er_iff _ hY]; exact hle.trans_lt hY.lt
#align matroid_in.r_fin.r_le_r_of_er_le_er MatroidIn.RFin.r_le_r_of_er_le_er

theorem RFin.er_le_er_of_r_le_r (hX : M.RFin X) (hle : M.R X ≤ M.R Y) : M.er X ≤ M.er Y := by
  obtain h | h := em (M.r_fin Y); rwa [hX.er_le_er_iff h]; rw [not_r_fin_iff.mp h]; simp
#align matroid_in.r_fin.er_le_er_of_r_le_r MatroidIn.RFin.er_le_er_of_r_le_r

theorem r_eq_r_inter_ground (M : MatroidIn α) (X : Set α) : M.R X = M.R (X ∩ M.e) := by
  rw [← er_to_nat_eq_r, er_eq_er_inter_ground, er_to_nat_eq_r]
#align matroid_in.r_eq_r_inter_ground MatroidIn.r_eq_r_inter_ground

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (I «expr ⊆ » X) -/
theorem le_r_iff [FiniteRk M] : n ≤ M.R X ↔ ∃ (I : _) (_ : I ⊆ X), M.indep I ∧ I.ncard = n :=
  by
  simp_rw [← coe_le_er_iff, le_er_iff, encard_eq_coe_iff, exists_prop]
  exact exists_congr fun I => ⟨fun hI => by tauto, fun hI => ⟨hI.1, hI.2.1, hI.2.1.Finite, hI.2.2⟩⟩
#align matroid_in.le_r_iff MatroidIn.le_r_iff

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (I «expr ⊆ » X) -/
theorem r_le_iff [FiniteRk M] : M.R X ≤ n ↔ ∀ (I) (_ : I ⊆ X), M.indep I → I.ncard ≤ n :=
  by
  simp_rw [← ENat.coe_le_coe_iff, coe_r_eq_er, er_le_iff, encard_le_coe_iff, ENat.coe_le_coe_iff]
  exact forall_congr' fun I => ⟨by tauto, fun h hIX hI => ⟨hI.Finite, h hIX hI⟩⟩
#align matroid_in.r_le_iff MatroidIn.r_le_iff

theorem r_mono (M : MatroidIn α) [FiniteRk M] : Monotone M.R := by rintro X Y (hXY : X ⊆ Y);
  rw [← er_le_er_iff]; exact M.er_mono hXY
#align matroid_in.r_mono MatroidIn.r_mono

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem r_le_card (M : MatroidIn α) [Finite M] (X : Set α)
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.R X ≤ X.ncard := by rw [r_le_iff]; exact fun I h _ => ncard_le_of_subset h (M.set_finite X)
#align matroid_in.r_le_card MatroidIn.r_le_card

theorem r_le_rk (M : MatroidIn α) [FiniteRk M] (X : Set α) : M.R X ≤ M.rk := by
  rw [r_eq_r_inter_ground]; exact M.r_mono (inter_subset_right _ _)
#align matroid_in.r_le_rk MatroidIn.r_le_rk

theorem lt_rk_iff_ne_rk [FiniteRk M] : M.R X < M.rk ↔ M.R X ≠ M.rk :=
  (M.r_le_rk X).lt_iff_ne
#align matroid_in.lt_rk_iff_ne_rk MatroidIn.lt_rk_iff_ne_rk

theorem Indep.r (hI : M.indep I) : M.R I = I.ncard := by
  rw [← er_to_nat_eq_r, hI.er, encard_to_nat_eq]
#align matroid_in.indep.r MatroidIn.Indep.r

theorem Indep.card_le_r_of_subset [FiniteRk M] (hI : M.indep I) (h : I ⊆ X) : I.ncard ≤ M.R X := by
  rw [← hI.r]; exact M.r_mono h
#align matroid_in.indep.card_le_r_of_subset MatroidIn.Indep.card_le_r_of_subset

theorem Indep.card_le_rk [FiniteRk M] (hI : M.indep I) : I.ncard ≤ M.rk :=
  hI.R.symm.trans_le (M.r_le_rk I)
#align matroid_in.indep.card_le_rk MatroidIn.Indep.card_le_rk

theorem Basis.card (h : M.Basis I X) : I.ncard = M.R X := by
  rw [← encard_to_nat_eq, ← er_to_nat_eq_r, h.encard]
#align matroid_in.basis.card MatroidIn.Basis.card

theorem Basis.r (h : M.Basis I X) : M.R I = M.R X := by rw [← h.card, h.indep.r]
#align matroid_in.basis.r MatroidIn.Basis.r

theorem Basis.r_eq_card (h : M.Basis I X) : M.R X = I.ncard := by rw [← h.r, ← h.indep.r]
#align matroid_in.basis.r_eq_card MatroidIn.Basis.r_eq_card

theorem Base.r (hB : M.base B) : M.R B = M.rk := by rw [base_iff_basis_ground] at hB ; rw [hB.r, rk]
#align matroid_in.base.r MatroidIn.Base.r

theorem Base.card (hB : M.base B) : B.ncard = M.rk := by rw [(base_iff_basis_ground.mp hB).card, rk]
#align matroid_in.base.card MatroidIn.Base.card

@[simp]
theorem r_empty (M : MatroidIn α) : M.R ∅ = 0 := by
  rw [← M.empty_indep.basis_self.card, ncard_empty]
#align matroid_in.r_empty MatroidIn.r_empty

@[simp]
theorem r_cl (M : MatroidIn α) (X : Set α) : M.R (M.cl X) = M.R X :=
  r_eq_of_er_eq (er_cl _ _)
#align matroid_in.r_cl MatroidIn.r_cl

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem basis_iff_indep_card [FiniteRk M]
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.Basis I X ↔ M.indep I ∧ I ⊆ X ∧ I.ncard = M.R X :=
  by
  refine'
    I.finite_or_infinite.symm.elim
      (fun hI => iff_of_false (hI ∘ fun h => h.indep.finite) (hI ∘ fun h => h.1.Finite))
      fun hIfin => _
  rw [basis_iff_indep_encard_eq_of_finite hIfin hX, and_comm' (_ ⊆ _), and_assoc',
    and_comm' (_ ⊆ _), ← coe_r_eq_er, hIfin.encard_eq, ENat.coe_inj]
#align matroid_in.basis_iff_indep_card MatroidIn.basis_iff_indep_card

theorem indep_iff_r_eq_card_of_finite (hI : I.Finite) : M.indep I ↔ M.R I = I.ncard :=
  by
  obtain ⟨J, hJ⟩ := M.exists_basis (I ∩ M.E)
  rw [r_eq_r_inter_ground, ← hJ.card]
  refine' ⟨fun h => _, fun h => _⟩
  ·
    rw [← inter_eq_self_of_subset_left h.subset_ground,
      hJ.eq_of_subset_indep (h.inter_right M.E) hJ.subset subset.rfl]
  rw [← eq_of_subset_of_ncard_le (hJ.subset.trans (inter_subset_left _ _)) h.symm.le hI]
  exact hJ.indep
#align matroid_in.indep_iff_r_eq_card_of_finite MatroidIn.indep_iff_r_eq_card_of_finite

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem indep_iff_r_eq_card [Finite M]
    (hI : I ⊆ M.e := by
      run_tac
        ssE) :
    M.indep I ↔ M.R I = I.ncard :=
  indep_iff_r_eq_card_of_finite (M.set_finite I)
#align matroid_in.indep_iff_r_eq_card MatroidIn.indep_iff_r_eq_card

theorem base_iff_indep_card [FiniteRk M] : M.base B ↔ M.indep B ∧ B.ncard = M.rk := by
  rw [base_iff_basis_ground, basis_iff_indep_card, ← and_assoc',
    and_iff_left_of_imp indep.subset_ground]
#align matroid_in.base_iff_indep_card MatroidIn.base_iff_indep_card

theorem base_iff_indep_r [FiniteRk M] : M.base B ↔ M.indep B ∧ M.R B = M.rk := by
  rw [base_iff_indep_card, and_congr_right_iff]; exact fun h => by rw [h.r]
#align matroid_in.base_iff_indep_r MatroidIn.base_iff_indep_r

theorem Indep.base_of_rk_le_card [FiniteRk M] (hI : M.indep I) (h : M.rk ≤ I.ncard) : M.base I :=
  base_iff_indep_card.mpr ⟨hI, h.antisymm' (by rw [← hI.r]; apply r_le_rk)⟩
#align matroid_in.indep.base_of_rk_le_card MatroidIn.Indep.base_of_rk_le_card

theorem Basis.r_eq_r_union (hIX : M.Basis I X) (Y : Set α) : M.R (I ∪ Y) = M.R (X ∪ Y) :=
  r_eq_of_er_eq (hIX.er_eq_er_union _)
#align matroid_in.basis.r_eq_r_union MatroidIn.Basis.r_eq_r_union

theorem Basis.r_eq_r_insert (hIX : M.Basis I X) (e : α) : M.R (insert e I) = M.R (insert e X) :=
  r_eq_of_er_eq (hIX.er_eq_er_insert _)
#align matroid_in.basis.r_eq_r_insert MatroidIn.Basis.r_eq_r_insert

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Indep.basis_of_subset_of_r_le [FiniteRk M] (hI : M.indep I) (hIX : I ⊆ X)
    (h : M.R X ≤ M.R I)
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.Basis I X :=
  hI.basis_of_subset_of_er_le_of_finite hIX (er_le_er_iff.mpr h) hI.Finite
#align matroid_in.indep.basis_of_subset_of_r_le MatroidIn.Indep.basis_of_subset_of_r_le

/-- The submodularity axiom for the rank function -/
theorem r_inter_add_r_union_le_r_add_r (M : MatroidIn α) [FiniteRk M] (X Y : Set α) :
    M.R (X ∩ Y) + M.R (X ∪ Y) ≤ M.R X + M.R Y := by
  simp_rw [← ENat.coe_le_coe_iff, ENat.coe_add, coe_r_eq_er]; apply er_submod
#align matroid_in.r_inter_add_r_union_le_r_add_r MatroidIn.r_inter_add_r_union_le_r_add_r

alias r_inter_add_r_union_le_r_add_r ← r_submod
#align matroid_in.r_submod MatroidIn.r_submod

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (X «expr ⊆ » M₁.E) -/
theorem eq_of_r_eq_r_forall {M₁ M₂ : MatroidIn α} [FiniteRk M₁] (hE : M₁.e = M₂.e)
    (h : ∀ (X) (_ : X ⊆ M₁.e), M₁.R X = M₂.R X) : M₁ = M₂ :=
  by
  have h2 : ∀ I, M₂.indep I → I.Finite :=
    by
    refine' fun I hI => by_contra fun hinf : I.Infinite => _
    obtain ⟨B₁, hB₁⟩ := M₁.exists_base
    obtain ⟨I₁, hI₁I, hI₁fin, hI₁card⟩ := hinf.exists_subset_ncard_eq (M₁.rk + 1)
    rw [← (hI.subset hI₁I).R, ← h _ (hI₁I.trans (hI.subset_ground.trans_eq hE.symm))] at hI₁card 
    linarith [M₁.r_le_rk I₁]
  refine'
    eq_of_indep_iff_indep_forall hE fun I hI =>
      I.finite_or_infinite.symm.elim
        (fun hI' => iff_of_false (fun h' => hI' h'.Finite) fun h' => hI' (h2 _ h')) fun hI' => _
  suffices M₁.er I = M₂.er I by
    rw [indep_iff_er_eq_encard_of_finite hI', indep_iff_er_eq_encard_of_finite hI', this]
  rw [← M₁.coe_r_eq_er_of_finite hI', ← M₂.coe_r_eq_er_of_finite hI', h _ hI]
#align matroid_in.eq_of_r_eq_r_forall MatroidIn.eq_of_r_eq_r_forall

theorem r_inter_left_le_r (M : MatroidIn α) [FiniteRk M] (X Y : Set α) : M.R (X ∩ Y) ≤ M.R X :=
  M.r_mono (inter_subset_left X Y)
#align matroid_in.r_inter_left_le_r MatroidIn.r_inter_left_le_r

theorem r_inter_right_le_r (M : MatroidIn α) [FiniteRk M] (X Y : Set α) : M.R (X ∩ Y) ≤ M.R Y :=
  M.r_mono (inter_subset_right X Y)
#align matroid_in.r_inter_right_le_r MatroidIn.r_inter_right_le_r

theorem r_le_r_union_left (M : MatroidIn α) [FiniteRk M] (X Y : Set α) : M.R X ≤ M.R (X ∪ Y) :=
  M.r_mono (subset_union_left X Y)
#align matroid_in.r_le_r_union_left MatroidIn.r_le_r_union_left

theorem r_le_r_union_right (M : MatroidIn α) [FiniteRk M] (X Y : Set α) : M.R Y ≤ M.R (X ∪ Y) :=
  M.r_mono (subset_union_right X Y)
#align matroid_in.r_le_r_union_right MatroidIn.r_le_r_union_right

theorem r_diff_le_r (M : MatroidIn α) [FiniteRk M] (X Y : Set α) : M.R (X \ Y) ≤ M.R X := by
  rw [diff_eq]; apply r_inter_left_le_r
#align matroid_in.r_diff_le_r MatroidIn.r_diff_le_r

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem r_lt_card_iff_not_indep [M.Finite]
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.R X < X.ncard ↔ ¬M.indep X :=
  by
  rw [lt_iff_not_le, not_iff_not, indep_iff_r_eq_card]
  exact ⟨(M.r_le_card X hX).antisymm, fun h => by rw [h]⟩
#align matroid_in.r_lt_card_iff_not_indep MatroidIn.r_lt_card_iff_not_indep

theorem nonempty_of_r_nonzero (hX : M.R X ≠ 0) : X.Nonempty := by rw [nonempty_iff_ne_empty];
  rintro rfl; exact hX M.r_empty
#align matroid_in.nonempty_of_r_nonzero MatroidIn.nonempty_of_r_nonzero

theorem r_singleton_le (M : MatroidIn α) (e : α) : M.R {e} ≤ 1 :=
  by
  have := M.er_singleton_le e
  rw [← ENat.coe_one, WithTop.le_coe_iff] at this 
  obtain ⟨i, hi, hle⟩ := this
  rwa [← er_to_nat_eq_r, hi, ENat.toNat_coe]
#align matroid_in.r_singleton_le MatroidIn.r_singleton_le

theorem r_insert_le_add_one (M : MatroidIn α) (e : α) (X : Set α) : M.R (insert e X) ≤ M.R X + 1 :=
  by
  have hle := M.er_insert_le_add_one e X
  simp_rw [← er_to_nat_eq_r]
  obtain h | h := eq_or_ne (M.er X) ⊤
  · have h' := M.er_mono (subset_insert e X)
    simp [h] at h' 
    simp [h, h']
  have h' : M.er X + 1 ≠ ⊤ := by rw [WithTop.add_ne_top]; simp [h]
  convert ENat.toNat_le_toNat_of_ne_top hle h'
  rw [← ENat.coe_inj, ENat.coe_add, ENat.coe_toNat h, ENat.coe_toNat h', ENat.coe_one]
#align matroid_in.r_insert_le_add_one MatroidIn.r_insert_le_add_one

theorem r_eq_r_of_subset_le [FiniteRk M] (hXY : X ⊆ Y) (hYX : M.R Y ≤ M.R X) : M.R X = M.R Y :=
  (M.r_mono hXY).antisymm hYX
#align matroid_in.r_eq_r_of_subset_le MatroidIn.r_eq_r_of_subset_le

theorem r_eq_r_diff_r_le_zero [FiniteRk M] (X : Set α) (hY : M.R Y ≤ 0) : M.R (X \ Y) = M.R X := by
  apply r_eq_of_er_eq; rw [er_eq_er_diff_er_le_zero]; rwa [← ENat.coe_zero, er_le_coe_iff]
#align matroid_in.r_eq_r_diff_r_le_zero MatroidIn.r_eq_r_diff_r_le_zero

theorem r_eq_r_union_r_le_zero [FiniteRk M] (X : Set α) (hY : M.R Y ≤ 0) : M.R (X ∪ Y) = M.R X := by
  apply r_eq_of_er_eq; rw [er_eq_er_union_er_le_zero]; rwa [← ENat.coe_zero, er_le_coe_iff]
#align matroid_in.r_eq_r_union_r_le_zero MatroidIn.r_eq_r_union_r_le_zero

theorem cl_eq_cl_of_subset_of_r_ge_r [FiniteRk M] (hXY : X ⊆ Y) (hr : M.R Y ≤ M.R X) :
    M.cl X = M.cl Y :=
  (M.to_rFin X).cl_eq_cl_of_subset_of_er_ge_er hXY (by rwa [er_le_er_iff])
#align matroid_in.cl_eq_cl_of_subset_of_r_ge_r MatroidIn.cl_eq_cl_of_subset_of_r_ge_r

theorem r_union_eq_of_subset_of_r_le_r [FiniteRk M] (Z : Set α) (hXY : X ⊆ Y) (hr : M.R Y ≤ M.R X) :
    M.R (X ∪ Z) = M.R (Y ∪ Z) :=
  r_eq_of_er_eq (er_union_eq_of_subset_of_er_le_er Z hXY ((M.to_rFin Y).er_le_er_of_r_le_r hr))
#align matroid_in.r_union_eq_of_subset_of_r_le_r MatroidIn.r_union_eq_of_subset_of_r_le_r

theorem r_union_eq_of_subsets_of_r_les [FiniteRk M] (hX : X ⊆ X') (hY : Y ⊆ Y')
    (hXX' : M.R X' ≤ M.R X) (hYY' : M.R Y' ≤ M.R Y) : M.R (X ∪ Y) = M.R (X' ∪ Y') :=
  by
  rw [← er_eq_er_iff]; rw [← er_le_er_iff] at hXX' hYY' 
  apply er_union_eq_of_subsets_of_er_les <;> assumption
#align matroid_in.r_union_eq_of_subsets_of_r_les MatroidIn.r_union_eq_of_subsets_of_r_les

theorem r_union_le_add_r (M : MatroidIn α) [FiniteRk M] (X Y : Set α) :
    M.R (X ∪ Y) ≤ M.R X + M.R Y := by linarith [M.r_submod X Y]
#align matroid_in.r_union_le_add_r MatroidIn.r_union_le_add_r

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem r_union_le_card_add_r (M : MatroidIn α) [Finite M] (X Y : Set α)
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.R (X ∪ Y) ≤ X.ncard + M.R Y :=
  (M.r_union_le_add_r X Y).trans (add_le_add_right (M.r_le_card X hX) _)
#align matroid_in.r_union_le_card_add_r MatroidIn.r_union_le_card_add_r

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem r_union_le_r_add_card (M : MatroidIn α) [Finite M] (X Y : Set α)
    (hY : Y ⊆ M.e := by
      run_tac
        ssE) :
    M.R (X ∪ Y) ≤ M.R X + Y.ncard := by rw [add_comm, union_comm]; exact M.r_union_le_card_add_r Y X
#align matroid_in.r_union_le_r_add_card MatroidIn.r_union_le_r_add_card

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem rk_le_card_add_r_compl (M : MatroidIn α) [Finite M] (X : Set α)
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.rk ≤ X.ncard + M.R (M.e \ X) := by
  simpa only [ground_inter_left, union_diff_self, M.r_eq_r_inter_ground (X ∪ _),
    union_inter_cancel_right, ← rk_def] using M.r_union_le_card_add_r (X ∩ M.E) (M.E \ X)
#align matroid_in.rk_le_card_add_r_compl MatroidIn.rk_le_card_add_r_compl

end Rank

end MatroidIn

-- /-- The rank `M.rk` of a matroid is the rank of its ground set -/
-- def rk {α : Type*} (M : matroid_in α) : ℕ := M.r M.E
-- lemma rk_def {α : Type*} (M : matroid_in α) : M.rk = M.r M.E := rfl 
-- /-- The rank of a set is the size of a basis -/
-- lemma basis.card_of_inter_ground (hI : M.basis I (X ∩ M.E)) : I.ncard = M.r X :=
-- begin
--   have hrw : ∀ J : {J : set α | M.basis J (X ∩ M.E)}, (J : set α).ncard = I.ncard,
--   { rintro ⟨J, (hJ : M.basis J (X ∩ M.E))⟩, rw [subtype.coe_mk, hI.card_eq_card_of_basis hJ] },
--   haveI : nonempty {J : set α | M.basis J (X ∩ M.E)}, 
--     from let ⟨I,hI⟩ := M.exists_basis (X ∩ M.E) in ⟨⟨I,hI⟩⟩,
--   simp_rw [r, hrw, cinfi_const], 
-- end
-- lemma basis.card (hI : M.basis I X) : I.ncard = M.r X := 
-- hI.basis_inter_ground.card_of_inter_ground
-- lemma eq_r_iff {n : ℕ} (hX : X ⊆ M.E . ssE) : M.r X = n ↔ ∃ I, M.basis I X ∧ I.ncard = n :=
-- begin
--   split,
--   { rintro rfl, 
--     obtain ⟨I,hI⟩ := M.exists_basis X, 
--     refine ⟨I, hI, hI.card⟩ },
--   rintro ⟨I,hI,rfl⟩, 
--   rw hI.card, 
-- end
-- lemma indep.r (hI : M.indep I) : M.r I = I.ncard := eq_r_iff.mpr ⟨I, hI.basis_self, rfl⟩
-- lemma basis.r (hIX : M.basis I X) : M.r I = M.r X := 
-- by rw [←hIX.card, hIX.indep.r]
-- lemma basis.r_eq_card (hIX : M.basis I X) : M.r X = I.ncard :=
-- by rw [←hIX.r, ←hIX.indep.r]
-- lemma base.r (hB : M.base B) : M.r B = M.rk := 
-- by { rw base_iff_basis_ground at hB, rw [hB.r, rk] }
-- lemma base.card (hB : M.base B) : B.ncard = M.rk := 
-- by rw [(base_iff_basis_ground.mp hB).card, rk]
-- lemma r_eq_r_inter_ground (M : matroid_in α) (X : set α) : M.r X = M.r (X ∩ M.E) :=
-- by { obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E), rwa [←hI.card_of_inter_ground, ←basis.card] }
-- @[simp] lemma r_empty (M : matroid_in α) : M.r ∅ = 0 := 
-- by rw [←M.empty_indep.basis_self.card, ncard_empty]
-- @[simp] lemma r_cl (M : matroid_in α) (X : set α) : M.r (M.cl X) = M.r X :=
-- begin
--   rw [cl_eq_cl_inter_ground, M.r_eq_r_inter_ground X], 
--   obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E), 
--   rw [←hI.r, ←hI.cl, hI.indep.basis_cl.r], 
-- end 
-- @[simp] lemma r_union_cl_right_eq_r_union (M : matroid_in α) (X Y : set α) :
--   M.r (X ∪ M.cl Y) = M.r (X ∪ Y) :=
-- by rw [←r_cl, cl_union_cl_right_eq, r_cl]
-- @[simp] lemma r_union_cl_left_eq_r_union (M : matroid_in α) (X Y : set α) :
--   M.r (M.cl X ∪ Y) = M.r (X ∪ Y) :=
-- by rw [←r_cl, cl_union_cl_left_eq, r_cl]
-- @[simp] lemma r_insert_cl_eq_r_insert (M : matroid_in α) (e : α) (X : set α) : 
--   M.r (insert e (M.cl X)) = M.r (insert e X) :=
-- by rw [← union_singleton, r_union_cl_left_eq_r_union, union_singleton]
-- lemma basis.r_eq_r_union (hIX : M.basis I X) (Y : set α) :
--   M.r (I ∪ Y) = M.r (X ∪ Y) :=
-- begin
--   rw [←r_union_cl_right_eq_r_union, ←r_union_cl_right_eq_r_union _ _ Y], 
--   obtain ⟨I', hI', hII'⟩ :=
--     hIX.indep.subset_basis_of_subset (hIX.subset.trans (subset_union_left _ (M.cl Y))), 
--   rw [←hI'.r, ← (hI'.basis_subset _ (union_subset_union_left _ hIX.subset)).r],   
--   refine λ e he, (hI'.subset he).elim (λ heX, or.inl _) (λ heY, subset_union_right _ _ heY), 
--   exact hIX.mem_of_insert_indep heX (hI'.indep.subset (insert_subset.mpr ⟨he, hII'⟩)), 
-- end
-- section finite
-- lemma r_le_card_of_finite (M : matroid_in α) {X : set α} (h : X.finite) : 
--   M.r X ≤ X.ncard := 
-- begin
--   rw [r_eq_r_inter_ground], 
--   obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E), 
--   rw ←hI.card, 
--   refine ncard_le_of_subset (hI.subset.trans (inter_subset_left _ _)) h, 
-- end 
-- lemma r_le_card (M : matroid_in α) [finite M] (X : set α) (hX : X ⊆ M.E . ssE) : M.r X ≤ X.ncard :=
-- M.r_le_card_of_finite (M.set_finite X)
-- lemma indep_iff_r_eq_card_of_finite {M : matroid_in α} (hI : I.finite) :
--   M.indep I ↔ M.r I = I.ncard :=
-- begin
--   obtain ⟨J,hJ⟩ := M.exists_basis (I ∩ M.E), 
--   rw [r_eq_r_inter_ground, ←hJ.card], 
--   refine ⟨λ h, _, λ h, _⟩,
--   { rw [←inter_eq_self_of_subset_left h.subset_ground, 
--       hJ.eq_of_subset_indep (h.inter_right M.E) hJ.subset subset.rfl] },
--   rw ← eq_of_subset_of_ncard_le (hJ.subset.trans (inter_subset_left _ _)) h.symm.le hI, 
--   exact hJ.indep, 
-- end
-- lemma indep_iff_r_eq_card [finite M] (hI : I ⊆ M.E . ssE): M.indep I ↔ M.r I = I.ncard :=
-- indep_iff_r_eq_card_of_finite (M.set_finite I)
-- lemma rk_le_card_ground (M : matroid_in α) [finite M] : M.rk ≤ M.E.ncard :=
-- M.r_le_card_of_finite (M.set_finite M.E)
-- lemma r_lt_card_of_dep_of_finite (h : X.finite) (hX : M.dep X) : M.r X < X.ncard :=
-- lt_of_le_of_ne (M.r_le_card_of_finite h) 
--   (λ h', ((indep_iff_r_eq_card_of_finite h).mpr h').not_dep hX)
-- lemma r_lt_card_of_dep [finite M] (hX : M.dep X) : M.r X < X.ncard :=
-- r_lt_card_of_dep_of_finite (M.set_finite _) hX 
-- lemma r_lt_card_iff_dep_of_finite (hX : X.finite) (hXE : X ⊆ M.E . ssE) : 
--   M.r X < X.ncard ↔ M.dep X := 
-- ⟨λ hlt, not_indep_iff.mp (λ hI, hlt.ne hI.r), r_lt_card_of_dep_of_finite hX⟩
-- lemma r_lt_card_iff_dep [finite M] (hXE : X ⊆ M.E . ssE) : M.r X < X.ncard ↔ M.dep X :=
-- r_lt_card_iff_dep_of_finite (M.set_finite _)
-- end finite
-- lemma infinite_of_not_r_fin (hX : ¬M.r_fin X) (hXE : X ⊆ M.E . ssE) : X.infinite :=
-- λ hX', hX (M.r_fin_of_finite hX') 
-- lemma basis.infinite_of_not_r_fin (hIX : M.basis I X) (hX : ¬ M.r_fin X) : I.infinite :=
-- hX ∘ (λ hI, hIX.r_fin_of_finite hI)
-- /-- A set with no finite basis has the junk rank value of zero -/
-- lemma r_eq_zero_of_not_r_fin (h : ¬M.r_fin X) (hX : X ⊆ M.E . ssE) : M.r X = 0 :=
-- begin
--   simp_rw [r_fin, not_exists, not_and] at h, 
--   obtain ⟨I, hI⟩ := M.exists_basis X, 
--   rw [←hI.card, infinite.ncard (h _ hI)], 
-- end
-- lemma r_fin_of_r_ne_zero (h : M.r X ≠ 0) (hX : X ⊆ M.E . ssE) : M.r_fin X := 
-- begin
--   obtain ⟨I, hI⟩ := M.exists_basis X, 
--   rw [←hI.card] at h, 
--   exact hI.r_fin_of_finite (finite_of_ncard_ne_zero h),  
-- end 
-- lemma indep.le_card_basis_of_r_fin (hI : M.indep I) (hIX : I ⊆ X) (hX : M.r_fin X) 
-- (hXJ : M.basis J X) : I.ncard ≤ J.ncard :=
-- begin
--   obtain ⟨I', hI, h⟩ := hI.subset_finite_basis_of_subset_of_r_fin hIX hX, 
--   rw hXJ.card_eq_card_of_basis hI, 
--   exact ncard_le_of_subset h.1 (hI.finite_of_r_fin hX), 
-- end 
-- lemma r_fin.le_r_iff (h : M.r_fin X) {n : ℕ} : n ≤ M.r X ↔ ∃ I ⊆ X, M.indep I ∧ I.ncard = n :=
-- begin
--   obtain ⟨J, hJ⟩ := eq_r_iff.mp (@rfl _ (M.r X)),
--   refine ⟨λ h, _, λ h, _⟩,
--   { obtain ⟨I', hI', rfl⟩ := exists_smaller_set _ _ (h.trans_eq hJ.2.symm),
--     exact ⟨I', hI'.trans hJ.1.subset, hJ.1.indep.subset hI', by simp⟩ },
--   obtain ⟨I, hIX, hI, rfl⟩ := h,
--   rw ←hJ.2,
--   exact hI.le_card_basis_of_r_fin hIX h hJ.1, 
-- end 
-- lemma r_fin.r_le_iff (h : M.r_fin X) {n : ℕ} : M.r X ≤ n ↔ (∀ I ⊆ X, M.indep I → I.ncard ≤ n) :=
-- begin
--   obtain ⟨I, hIX, hI⟩ := eq_r_iff.mp (@rfl _ (M.r X)),
--   exact ⟨λ h' J hJX hJ, (hJ.le_card_basis_of_r_fin hJX h hIX).trans (hI.trans_le h'),
--     λ h, hI.symm.trans_le (h I hIX.subset hIX.indep)⟩,
-- end 
-- lemma r_fin.r_mono (hY : M.r_fin Y) (hXY : X ⊆ Y) : M.r X ≤ M.r Y :=
-- by { simp_rw [(hY.subset hXY).r_le_iff, hY.le_r_iff], exact λ I hIX hI, ⟨I,hIX.trans hXY,hI,rfl⟩ }
-- lemma r_fin.r_eq_r_of_subset_le (h : M.r_fin Y) (hXY : X ⊆ Y) (hYX : M.r Y ≤ M.r X) : 
--   M.r X = M.r Y :=
-- (h.r_mono hXY).antisymm hYX
-- lemma indep.card_le_r_of_subset_of_r_fin (hI : M.indep I) (h : I ⊆ X) (hX : M.r_fin X) : 
--   I.ncard ≤ M.r X :=
-- by { rw [←hI.r], exact hX.r_mono h }
-- lemma indep.basis_of_subset_of_r_le_of_r_fin (hI : M.indep I) (hIX : I ⊆ X) (h : M.r X ≤ M.r I) 
-- (hX : M.r_fin X) :
--   M.basis I X :=
-- begin
--   obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset hIX,   
--   rwa eq_of_subset_of_ncard_le hIJ _ (hJ.finite_of_r_fin hX), 
--   rwa [hJ.card, ←hI.r], 
-- end
-- /-- The submodularity axiom for the rank function -/
-- lemma r_fin.r_inter_add_r_union_le_r_add_r (hX : M.r_fin X) (hY : M.r_fin Y) :
--   M.r (X ∩ Y) + M.r (X ∪ Y) ≤ M.r X + M.r Y :=
-- begin
--   obtain ⟨Ii, hIi⟩ := M.exists_basis (X ∩ Y),
--   obtain ⟨IX, hIX, hIX', hIXfin⟩ :=
--     hIi.indep.subset_finite_basis_of_subset_of_r_fin (hIi.subset.trans (inter_subset_left _ _)) hX,
--   obtain ⟨IY, hIY, hIY', hIYfin⟩ :=
--     hIi.indep.subset_finite_basis_of_subset_of_r_fin (hIi.subset.trans (inter_subset_right _ _)) hY,
--   rw [←hIX.r_eq_r_union, union_comm, ←hIY.r_eq_r_union, ←hIi.card, ←hIX.card, ←hIY.card, 
--    union_comm, ← ncard_union_add_ncard_inter _ _ hIXfin hIYfin, add_comm], 
--   refine add_le_add (M.r_le_card_of_finite (hIXfin.union hIYfin)) _, 
--   refine (ncard_le_of_subset (subset_inter hIX' hIY') (hIXfin.subset (inter_subset_left _ _))),
-- end
-- alias r_fin.r_inter_add_r_union_le_r_add_r ← r_fin.submod 
-- lemma r_fin.r_union_le_add_r (hX : M.r_fin X) (hY : M.r_fin Y) : M.r (X ∪ Y) ≤ M.r X + M.r Y :=
-- by linarith [hX.submod hY]
-- lemma r_fin.r_union_le_add_r' (hX : M.r_fin (X ∪ Y)) : M.r (X ∪ Y) ≤ M.r X + M.r Y := 
-- by { apply r_fin.r_union_le_add_r; 
--   apply hX.subset, apply subset_union_left, apply subset_union_right }
-- lemma r_fin.basis_iff_finite_indep_card (hX : M.r_fin X) :
--   M.basis I X ↔ M.indep I ∧ I ⊆ X ∧ I.finite ∧ I.ncard = M.r X :=
-- begin
--   refine (I.finite_or_infinite.symm.elim _ (λ hI, ⟨λ hb, ⟨hb.indep,hb.subset,hI,hb.card⟩, λ h, _⟩)), 
--   { exact λ hI, iff_of_false (λ hb, hI (hb.finite_of_r_fin hX)) (by simp [iff_false_intro hI]) }, 
--   refine h.1.basis_of_maximal_subset h.2.1 (λ J hJ hIJ hJX, _), 
--   rw [←eq_of_subset_of_ncard_le hIJ _ (hJ.finite_of_subset_r_fin hJX hX)], 
--   rw [h.2.2.2, hX.le_r_iff], 
--   exact ⟨J, hJX, hJ, rfl⟩, 
-- end 
-- lemma indep.basis_of_r_fin_of_subset_of_r_ge (hI : M.indep I) (hIX : I ⊆ X) (hX : M.r_fin X) 
-- (hr : M.r X ≤ I.ncard) : 
--   M.basis I X  :=
-- hX.basis_iff_finite_indep_card.mpr ⟨hI, hIX, hI.finite_of_subset_r_fin hIX hX, 
--     hr.antisymm' (hX.le_r_iff.mpr ⟨I, hIX, hI,rfl⟩)⟩
-- lemma r_fin.r_eq_zero_iff_subset_loops (hX : M.r_fin X) : M.r X = 0 ↔ X ⊆ M.cl ∅ :=
-- begin
--   obtain ⟨I, hI⟩ := M.exists_basis X,
--   rw [←cl_subset_cl_iff_subset_cl, ←hI.cl], 
--   rw hX.basis_iff_finite_indep_card at hI, 
--   rw [←hI.2.2.2, ncard_eq_zero hI.2.2.1], 
--   exact ⟨by { rintro rfl, exact subset.rfl }, 
--     λ h, hI.1.eq_empty_of_subset_loops ((M.subset_cl I hI.1.subset_ground).trans h)⟩,
-- end 
-- lemma r_fin.r_eq_r_diff_r_le_zero (hY : M.r_fin Y) (X) (hr : M.r Y ≤ 0) : M.r (X \ Y) = M.r X :=
-- by rw [←r_cl, cl_diff_eq_cl_of_subset_loops (hY.r_eq_zero_iff_subset_loops.mp (le_zero_iff.mp hr)), 
--   r_cl]
-- lemma r_fin.r_eq_r_union_r_le_zero (hY : M.r_fin Y) (X) (hr : M.r Y ≤ 0) : M.r (X ∪ Y) = M.r X :=
-- by rw [←r_cl, cl_union_eq_cl_of_subset_loops (hY.r_eq_zero_iff_subset_loops.mp (le_zero_iff.mp hr)), 
--   r_cl]
-- lemma r_fin.r_le_r_inter_add_r_diff (hX : M.r_fin X) (Y : set α) : 
--   M.r X ≤ M.r (X ∩ Y) + M.r (X \ Y) :=
-- begin
--   convert r_fin.r_union_le_add_r (hX.subset (inter_subset_left _ _)) (hX.subset (diff_subset _ _)), 
--   rw (inter_union_diff X Y), 
-- end 
-- lemma r_fin.r_le_r_add_r_diff (hX : M.r_fin X) (hYX : Y ⊆ X) : M.r X ≤ M.r Y + M.r (X \ Y) :=
-- begin
--   convert hX.r_le_r_inter_add_r_diff _, 
--   rw [inter_eq_self_of_subset_right hYX], 
-- end 
-- lemma r_fin.cl_eq_cl_of_subset_of_r_ge_r (hY : M.r_fin Y) (hXY : X ⊆ Y) (hr : M.r Y ≤ M.r X) : 
--   M.cl X = M.cl Y :=
-- begin
--   have hXE : X ⊆ M.E := hXY.trans hY.subset_ground, 
--   obtain ⟨I, hI⟩ := M.exists_basis X, 
--   obtain ⟨J, hJ, hIJ, hJfin⟩ := hI.indep.subset_finite_basis_of_subset_of_r_fin 
--     (hI.subset.trans hXY) hY, 
--   rw [←hI.cl, ←hJ.cl, eq_of_subset_of_ncard_le hIJ _ hJfin], 
--   rwa [hI.card, hJ.card],
-- end 
-- end r_fin
-- lemma le_r_iff [finite_rk M] : n ≤ M.r X ↔ ∃ I ⊆ X, M.indep I ∧ I.ncard = n := 
-- begin
--   rw [r_eq_r_inter_ground], 
--   convert (M.to_r_fin (X ∩ M.E)).le_r_iff,
--   ext I, 
--   simp only [exists_prop, subset_inter_iff, and.congr_left_iff, iff_self_and, and_imp], 
--   exact λ h _ _, h.subset_ground,  
-- end 
-- lemma r_le_iff [finite_rk M] : M.r X ≤ n ↔ (∀ I ⊆ X, M.indep I → I.ncard ≤ n) :=
-- begin
--   rw [r_eq_r_inter_ground], 
--   convert (M.to_r_fin (X ∩ M.E)).r_le_iff, 
--   simp only [subset_inter_iff, and_imp, eq_iff_iff], 
--   exact forall_congr (λ I, ⟨λ h hIX hIE hI, h hIX hI, λ h hIX hI, h hIX (by ssE) hI⟩), 
-- end 
-- lemma r_mono (M : matroid_in α) [finite_rk M] {X Y : set α} (hXY : X ⊆ Y) : M.r X ≤ M.r Y :=
-- begin
--   rw [r_eq_r_inter_ground, M.r_eq_r_inter_ground Y], 
--   exact (M.to_r_fin _).r_mono (inter_subset_inter_left _ hXY), 
-- end 
-- lemma basis_iff_indep_card [finite_rk M] (hX : X ⊆ M.E . ssE) : 
--   M.basis I X ↔ M.indep I ∧ I ⊆ X ∧ I.ncard = M.r X :=
-- begin
--   rw [r_eq_r_inter_ground, (M.to_r_fin X).basis_iff_finite_indep_card, and.congr_right_iff, 
--     and.congr_right_iff, r_eq_r_inter_ground, and_iff_right_iff_imp], 
--   exact λ h _ _, h.finite,  
-- end 
-- lemma r_le_rk (M : matroid_in α) [finite_rk M] (X : set α) : M.r X ≤ M.rk := 
-- by { rw [r_eq_r_inter_ground], exact M.r_mono (inter_subset_right _ _) }
-- lemma lt_rk_iff_ne_rk [finite_rk M] : M.r X < M.rk ↔ M.r X ≠ M.rk := (M.r_le_rk X).lt_iff_ne
-- lemma indep.card_le_r_of_subset [finite_rk M] (hI : M.indep I) (h : I ⊆ X) : 
--   I.ncard ≤ M.r X :=
-- by { rw [←hI.r], exact M.r_mono h }
-- lemma indep.card_le_rk [finite_rk M] (hI : M.indep I) : I.ncard ≤ M.rk :=
-- hI.r.symm.trans_le (M.r_le_rk I)
-- lemma base_iff_indep_r [finite_rk M] : M.base B ↔ M.indep B ∧ M.r B = M.rk :=
-- begin
--   refine ⟨λ h, ⟨h.indep, h.r⟩, λ h, base_iff_maximal_indep.mpr ⟨h.1, λ I hI hBI, _⟩⟩,
--   refine eq_of_le_of_not_lt hBI (λ hBI' : B ⊂ I, _),
--   cases h with hB hB',
--   rw [hB.r] at hB',
--   have := ncard_lt_ncard hBI' hI.finite,
--   rw [←hI.r, hB'] at this,
--   exact this.not_le (M.r_le_rk _), 
-- end
-- lemma base_iff_indep_card [finite_rk M] : M.base B ↔ M.indep B ∧ B.ncard = M.rk :=
-- ⟨λ h, ⟨h.indep, by rw ←h.card⟩, λ h, base_iff_indep_r.mpr ⟨h.1, by rw [←h.2, ←h.1.r]⟩⟩
-- lemma indep.base_of_rk_le_card [finite_rk M] (hI : M.indep I) (h : M.rk ≤ I.ncard) : M.base I :=
-- base_iff_indep_card.mpr ⟨hI, h.antisymm' (by {rw ←hI.r, apply r_le_rk})⟩
-- lemma basis.r_eq_r_insert (hIX : M.basis I X) (e : α) : M.r (insert e I) = M.r (insert e X) :=
-- by simp_rw [←union_singleton, hIX.r_eq_r_union]
-- lemma indep.basis_of_subset_of_r_le [finite_rk M] (hI : M.indep I) (hIX : I ⊆ X)
-- (h : M.r X ≤ M.r I) (hX : X ⊆ M.E . ssE) : M.basis I X :=
-- hI.basis_of_subset_of_r_le_of_r_fin hIX h (M.to_r_fin X)
-- /-- The submodularity axiom for the rank function -/
-- lemma r_inter_add_r_union_le_r_add_r (M : matroid_in α) [finite_rk M] (X Y : set α) :
--   M.r (X ∩ Y) + M.r (X ∪ Y) ≤ M.r X + M.r Y :=
-- begin
--   rw [r_eq_r_inter_ground, inter_inter_distrib_right, M.r_eq_r_inter_ground (X ∪ _), 
--     inter_distrib_right, M.r_eq_r_inter_ground X, M.r_eq_r_inter_ground Y], 
--   exact (M.to_r_fin _).r_inter_add_r_union_le_r_add_r (M.to_r_fin _), 
-- end 
-- alias r_inter_add_r_union_le_r_add_r ← r_submod 
-- lemma eq_of_r_eq_r_forall {M₁ M₂ : matroid_in α} [finite_rk M₁] (hE : M₁.E = M₂.E) 
--   (h : ∀ X ⊆ M₁.E, M₁.r X = M₂.r X) : M₁ = M₂ :=
-- begin
--   have h2 : ∀ I, M₂.indep I → I.finite, 
--   { refine λ I hI, by_contra (λ (hinf : I.infinite), _),  
--     obtain ⟨B₁,hB₁⟩ := M₁.exists_base, 
--     obtain ⟨I₁,hI₁I, hI₁fin, hI₁card⟩ := hinf.exists_subset_ncard_eq (M₁.rk + 1), 
--     rw [←(hI.subset hI₁I).r, ←h _ (hI₁I.trans (hI.subset_ground.trans_eq hE.symm)) ] at hI₁card, 
--     linarith [M₁.r_le_rk I₁] },
--   refine eq_of_indep_iff_indep_forall hE (λ I hI, (I.finite_or_infinite.symm.elim 
--     (λ hI, iff_of_false (λ h', hI h'.finite) (λ h', hI (h2 _ h') ) ) (λ hI, _))),  
--   rwa [indep_iff_r_eq_card_of_finite hI, h, indep_iff_r_eq_card_of_finite hI], 
-- end 
-- lemma r_le_r_of_subset (M : matroid_in α) [finite_rk M] (hXY : X ⊆ Y) : M.r X ≤ M.r Y :=
-- M.r_mono hXY
-- lemma r_inter_left_le_r (M : matroid_in α) [finite_rk M] (X Y : set α) : M.r (X ∩ Y) ≤ M.r X :=
-- M.r_mono (inter_subset_left X Y)
-- lemma r_inter_right_le_r (M : matroid_in α) [finite_rk M] (X Y : set α) : M.r (X ∩ Y) ≤ M.r Y :=
-- M.r_mono (inter_subset_right X Y)
-- lemma r_le_r_union_left (M : matroid_in α) [finite_rk M] (X Y : set α) : M.r X ≤ M.r (X ∪ Y) :=
-- M.r_mono (subset_union_left X Y)
-- lemma r_le_r_union_right (M : matroid_in α) [finite_rk M] (X Y : set α) : M.r Y ≤ M.r (X ∪ Y) :=
-- M.r_mono (subset_union_right X Y)
-- lemma r_diff_le_r (M : matroid_in α) [finite_rk M] (X Y : set α) : M.r (X \ Y) ≤ M.r X :=
-- by { rw diff_eq, apply r_inter_left_le_r }
-- lemma r_lt_card_iff_not_indep [M.finite] (hX : X ⊆ M.E . ssE) : (M.r X < X.ncard) ↔ ¬M.indep X :=
-- begin
--   rw [lt_iff_not_le, not_iff_not, indep_iff_r_eq_card],
--   exact ⟨(M.r_le_card X).antisymm, λ h, by rw h⟩ 
-- end
-- lemma nonempty_of_r_nonzero (hX : M.r X ≠ 0): X.nonempty :=
-- by {rw nonempty_iff_ne_empty, rintro rfl, exact hX M.r_empty}
-- lemma r_single_ub (M : matroid_in α) [finite_rk M] (e : α) : M.r {e} ≤ 1 :=
-- by { convert M.r_le_card_of_finite _; simp [ncard_singleton] }
-- lemma r_eq_r_of_subset_le [finite_rk M] (hXY : X ⊆ Y) (hYX : M.r Y ≤ M.r X) : M.r X = M.r Y :=
-- (M.r_mono hXY).antisymm hYX
-- lemma r_eq_r_diff_r_le_zero [finite_rk M] (X : set α) (hY : M.r Y ≤ 0) : M.r (X \ Y) = M.r X :=
-- begin
--   rw [r_eq_r_inter_ground] at hY, 
--   rw [r_eq_r_inter_ground, inter_diff_distrib_right, M.r_eq_r_inter_ground X, 
--     (M.to_r_fin (Y ∩ M.E)).r_eq_r_diff_r_le_zero _ hY], 
-- end 
-- lemma r_eq_r_union_r_le_zero [finite_rk M] (X : set α) (hY : M.r Y ≤ 0) : M.r (X ∪ Y) = M.r X :=
-- begin
--   rw [r_eq_r_inter_ground] at hY, 
--   rw [r_eq_r_inter_ground, inter_distrib_right, (M.to_r_fin _).r_eq_r_union_r_le_zero _ hY, 
--     ←r_eq_r_inter_ground], 
-- end 
-- lemma cl_eq_cl_of_subset_of_r_ge_r [finite_rk M] (hXY : X ⊆ Y) (hr : M.r Y ≤ M.r X) : 
--   M.cl X = M.cl Y :=
-- begin
--   rw [←M.r_cl Y, ←M.r_cl X] at hr,  
--   have hXY' := M.cl_subset hXY, 
--   convert (M.to_r_fin (M.cl Y)).cl_eq_cl_of_subset_of_r_ge_r hXY' hr using 1; simp,  
-- end 
-- lemma r_union_eq_of_subset_of_r_le_r [finite_rk M] (Z : set α) (hXY : X ⊆ Y) (hr : M.r Y ≤ M.r X) :
--   M.r (X ∪ Z) = M.r (Y ∪ Z) :=
-- by rw [←r_cl, ←cl_union_cl_left_eq, cl_eq_cl_of_subset_of_r_ge_r hXY hr, 
--     cl_union_cl_left_eq, r_cl]
-- -- lemma r_union_eq_of_subset_of_r_eqs (hX : X ⊆ X') (hY : Y ⊆ Y')
-- -- (hXX' : M.r X = M.r X') (hYY' : M.r Y = M.r Y') :
-- --   M.r (X ∪ Y) = M.r (X' ∪ Y') :=
-- -- by rw [r_union_eq_of_subset_of_r_eq Y hX hXX', union_comm, union_comm _ Y',
-- --        r_union_eq_of_subset_of_r_eq _ hY hYY']
-- -- lemma r_eq_of_inter_union (X Y A : set α) :
-- --   M.r (X ∩ A) = M.r X → M.r ((X ∩ A) ∪ Y) = M.r (X ∪ Y) :=
-- -- λ h, r_union_eq_of_subset_of_r_eq _ (inter_subset_left _ _) h
-- -- lemma r_eq_of_union_r_diff_eq (Z : set α) (hX : M.r (X \ Y) = M.r X) :
-- --   M.r (Z ∪ (X \ Y)) = M.r (Z ∪ X) :=
-- -- by {rw diff_eq at *, rw [union_comm _ X, ← r_eq_of_inter_union _ Z _ hX, union_comm Z]}
-- lemma r_union_le_add_r (M : matroid_in α) [finite_rk M] (X Y : set α) :
--   M.r (X ∪ Y) ≤ M.r X + M.r Y :=
-- by linarith [M.r_submod X Y]
-- lemma r_union_le_card_add_r (M : matroid_in α) [finite M] (X Y : set α) (hX : X ⊆ M.E . ssE) : 
--   M.r (X ∪ Y) ≤ X.ncard + M.r Y :=
-- (M.r_union_le_add_r X Y).trans (add_le_add_right (M.r_le_card X hX) _)
-- lemma r_union_le_r_add_card (M : matroid_in α) [finite M] (X Y : set α) (hY : Y ⊆ M.E . ssE) : 
--   M.r (X ∪ Y) ≤ M.r X + Y.ncard :=
-- by { rw [add_comm, union_comm], exact M.r_union_le_card_add_r Y X }
-- lemma rk_le_card_add_r_compl (M : matroid_in α) [finite M] (X : set α) (hX : X ⊆ M.E . ssE) :
--   M.rk ≤ X.ncard + M.r (M.E \ X) :=
-- begin
--   rw [rk], 
--   nth_rewrite 0 [←union_diff_cancel hX], 
--   apply r_union_le_card_add_r, 
-- end
-- lemma rank_eq_of_le_supset [finite_rk M] (h : X ⊆ Y) (hr : M.r Y ≤ M.r X) : M.r X = M.r Y :=
-- hr.antisymm' (M.r_mono h)
-- lemma r_le_r_insert (M : matroid_in α) (e : α) (X : set α) : M.r X ≤ M.r (insert e X) :=
-- begin
--   rw [r_eq_r_inter_ground, M.r_eq_r_inter_ground (insert _ _)], 
--   by_cases he : e ∈ M.E, 
--   refine (em (M.r_fin (X ∩ M.E))).elim (λ h, _) (λ h, _), 
--   { rw [insert_inter_of_mem he], 
--     exact (h.insert e he).r_mono (subset_insert _ _) },
--   { rw [r_eq_zero_of_not_r_fin h (inter_subset_right _ _)], apply zero_le }, 
--   rw [insert_inter_of_not_mem he], 
-- end 
-- lemma r_insert_eq_of_not_mem_ground (X : set α) (he : e ∉ M.E) : M.r (insert e X) = M.r X :=
-- by rw [r_eq_r_inter_ground, insert_inter_of_not_mem he, ←r_eq_r_inter_ground]
-- lemma r_diff_singleton_eq_of_not_mem_ground (X : set α) (he : e ∉ M.E) : M.r (X \ {e}) = M.r X :=
-- by rw [←r_insert_eq_of_not_mem_ground (X \ {e}) he, insert_diff_singleton, 
--   r_insert_eq_of_not_mem_ground _ he]
-- lemma r_insert_inter_ground (X : set α) (e : α) : 
--   M.r (insert e X) = M.r (insert e (X ∩ M.E)) :=
-- begin
--   rw r_eq_r_inter_ground, 
--   refine (em (e ∈ M.E)).elim (λ he, by rw insert_inter_of_mem he) (λ he, _), 
--   rw [r_insert_eq_of_not_mem_ground _ he, insert_inter_of_not_mem he],
-- end 
-- lemma r_eq_of_le_insert (h : M.r (insert e X) ≤ M.r X) : M.r (insert e X) = M.r X :=
-- h.antisymm (M.r_le_r_insert e X)
-- lemma r_insert_eq_add_one_of_r_ne (h : M.r (insert e X) ≠ M.r X) : M.r (insert e X) = M.r X + 1 :=
-- (nat.lt_iff_add_one_le.mp ((M.r_le_r_insert e X).lt_of_ne h.symm)).antisymm' 
--   (M.r_insert_le_add_one e X)
-- lemma r_insert_eq_add_one_iff_r_ne : M.r (insert e X) = M.r X + 1 ↔ M.r (insert e X) ≠ M.r X :=
-- ⟨by { intro h, rw h, exact (r M X).succ_ne_self } , r_insert_eq_add_one_of_r_ne⟩ 
-- lemma r_le_r_add_r_diff (M : matroid_in α) [finite_rk M] (X Y : set α) : M.r Y ≤ M.r X + M.r (Y \ X) :=
-- le_trans (M.r_mono (by simp)) (r_union_le_add_r M X (Y \ X))
-- lemma r_le_r_diff_singleton_add_one (M : matroid_in α) (e : α) (X : set α) :
--   M.r X ≤ M.r (X \ {e}) + 1 :=
-- begin
--   refine le_trans _ (M.r_insert_le_add_one e (X \ {e})),
--   rw [insert_diff_singleton], 
--   apply r_le_r_insert, 
-- end 
-- lemma r_diff_singleton_add_one_eq_r_of_ne (h_ne : M.r X ≠ M.r (X \ {e})) :
--   M.r X = M.r (X \ {e}) + 1 :=
-- begin
--   refine (em (e ∈ X)).symm.elim (λ h, (h_ne (by rw [diff_singleton_eq_self h])).elim) (λ he, _),
--   convert (@r_insert_eq_add_one_of_r_ne _ _ _ e _);
--   rwa [insert_diff_singleton, insert_eq_of_mem he],
-- end 
-- lemma r_le_r_add_card_diff_of_subset (M : matroid_in α) [finite M] (hXY : X ⊆ Y) 
-- (hYE : Y ⊆ M.E . ssE) : M.r Y ≤ M.r X + (Y \ X).ncard :=
-- by { nth_rewrite 0 ←union_diff_cancel hXY, apply r_union_le_r_add_card }
-- lemma r_add_card_le_r_add_card_of_subset (M : matroid_in α) [finite M] (hXY : X ⊆ Y) 
-- (hYE : Y ⊆ M.E . ssE):
--   M.r Y + X.ncard ≤ M.r X + Y.ncard :=
-- begin
--   rw ← ncard_diff_add_ncard_eq_ncard hXY (M.set_finite Y),  
--   linarith [M.r_le_r_add_card_diff_of_subset hXY],
-- end
-- lemma submod_three (M : matroid_in α) [finite_rk M] (X Y Y' : set α) :
--   M.r (X ∪ (Y ∪ Y')) + M.r (X ∪ (Y ∩ Y')) ≤ M.r (X ∪ Y) + M.r (X ∪ Y') :=
-- begin
--   have := M.r_submod (X ∪ Y) (X ∪ Y'),
--   rwa [←union_distrib_left, ←union_union_distrib_left, add_comm] at this,
-- end
-- lemma submod_three_right (M : matroid_in α) [finite_rk M] (X Y Y' : set α) :
--   M.r ((Y ∪ Y') ∪ X) + M.r ((Y ∩ Y') ∪ X) ≤ M.r (Y ∪ X) + M.r (Y' ∪ X) :=
-- by {simp_rw ←(union_comm X), apply submod_three}
-- lemma submod_three_disj (M : matroid_in α) [finite_rk M] (X Y Y' : set α) (hYY' : Y ∩ Y' = ∅) :
--   M.r (X ∪ (Y ∪ Y')) + M.r X ≤ M.r (X ∪ Y) + M.r (X ∪ Y') :=
-- by {have := submod_three M X Y Y', rwa [hYY', union_empty] at this}
-- lemma r_union_add_r_le_r_union_add_r_of_subset (M : matroid_in α) [finite_rk M] (hXY : X ⊆ Y) 
-- (Z : set α) : 
--   M.r (Y ∪ Z) + M.r X ≤ M.r (X ∪ Z) + M.r Y :=
-- begin
--   have hsm := M.r_submod (X ∪ Z) Y,
--   rw [union_right_comm, union_eq_right_iff_subset.mpr hXY, inter_distrib_right,
--     inter_eq_left_iff_subset.mpr hXY, add_comm] at hsm,
--   exact le_trans (add_le_add_left (M.r_le_r_union_left _ _) _) hsm,
-- end
-- lemma r_fin.augment_of_not_r_fin (hX : M.r_fin X) (hZ : ¬M.r_fin Z) (hZ : Z ⊆ M.E . ssE): 
--   ∃ z ∈ Z \ X, M.r (insert z X) = M.r X + 1 := 
-- begin
--   obtain ⟨J, hJ⟩ := M.exists_basis Z, 
--   have hJinf : J.infinite, by rwa [set.infinite, ←hJ.r_fin_iff_finite], 
--   obtain ⟨J', hJ'J, hJfin, hJcard⟩ := hJinf.exists_subset_ncard_eq (M.r X + 1), 
--   obtain ⟨z, ⟨hzJ',hzX⟩, h⟩ := hX.r_augment 
--     (M.r_fin_of_finite hJfin (hJ'J.trans hJ.subset_ground_left)) 
--     (((lt_add_one _).trans_eq hJcard.symm).trans_eq (hJ.indep.subset hJ'J).r.symm), 
--   exact ⟨z, ⟨hJ.subset (hJ'J hzJ'),hzX⟩, h⟩, 
-- end 
-- lemma r_union_eq_of_r_union_subset_le [finite_rk M] (hXY : X ⊆ Y) (h : M.r (X ∪ Z) ≤ M.r X) :
--   M.r (Y ∪ Z) = M.r Y :=
-- begin
--   have hsm := M.r_submod Y (X ∪ Z),
--   rw [←union_assoc, union_eq_left_iff_subset.mpr hXY, inter_distrib_left,
--     inter_eq_right_iff_subset.mpr hXY] at hsm,
--   linarith [M.r_le_r_union_left X (Y ∩ Z), M.r_le_r_union_left Y Z],
-- end
-- lemma r_insert_eq_of_r_insert_subset_le [finite_rk M] (hXY : X ⊆ Y) (h : M.r (insert e X) ≤ M.r X) :
--   M.r (insert e Y) = M.r Y :=
-- by {rw [←union_singleton] at *, rw [r_union_eq_of_r_union_subset_le hXY h],}
-- lemma r_eq_of_r_all_insert_le (hXY : X ⊆ Y) (hY : ∀ e ∈ Y, M.r (insert e X) ≤ M.r X) :
--    M.r X = M.r Y :=
-- begin
--   simp_rw [M.r_eq_r_inter_ground X, M.r_eq_r_inter_ground Y, M.r_eq_r_inter_ground (insert _ _)] 
--     at *,
--   refine (em' (M.r_fin (Y ∩ M.E))).elim (λ hY', _) (λ hY', _), 
--   { refine (em' (M.r_fin (X ∩ M.E))).elim (λ hX, _) (λ hX, _), 
--     { rw [r_eq_zero_of_not_r_fin hX, r_eq_zero_of_not_r_fin hY'] },
--     obtain ⟨z, hz, hr⟩ := hX.augment_of_not_r_fin hY', 
--     have h' := hY z hz.1.1, 
--     rw [←nat.lt_add_one_iff, ←hr, insert_inter_of_mem hz.1.2] at h', 
--     exact (h'.ne rfl).elim },
--   have hss : X ∩ M.E ⊆ Y ∩ M.E := (inter_subset_inter_left _ hXY), 
--   refine (hY'.r_mono hss).antisymm (le_of_not_lt (λ hlt, _)), 
--   obtain ⟨z, hz, hr⟩ := (hY'.subset hss).r_augment hY' hlt,  
--   have h' := hY z hz.1.1, 
--   rw [←nat.lt_add_one_iff, ←hr, insert_inter_of_mem hz.1.2] at h', 
--   exact h'.ne rfl, 
-- end
-- lemma r_union_eq_of_r_all_insert_le (hY : ∀ e ∈ Y, M.r (insert e X) ≤ M.r X) : 
--   M.r (X ∪ Y) = M.r X :=
-- begin
--   refine (r_eq_of_r_all_insert_le (subset_union_left X Y) _).symm,
--   rintro e (heX | heY),
--   { rw [insert_eq_of_mem heX]},
--   exact hY _ heY,
-- end
-- lemma r_eq_of_r_all_insert_eq (hXY : X ⊆ Y) (hY : ∀ e ∈ Y, M.r X = M.r (insert e X)) :
--    M.r X = M.r Y :=
-- r_eq_of_r_all_insert_le hXY (λ e h, (hY e h).symm.le)
-- lemma indep_inter_r_zero_eq_empty [finite_rk M] (hI : M.indep I) (hX : M.r X = 0) : I ∩ X = ∅ :=
-- begin
--   have h := hI.subset (inter_subset_left _ X),
--   rw [←ncard_eq_zero (hI.finite.subset (inter_subset_left _ _)), ←le_zero_iff], 
--   rw indep_iff_r_eq_card_of_finite (hI.finite.subset (inter_subset_left _ _)) at h, 
--   rw ←h, exact (M.r_mono (inter_subset_right I X)).trans_eq hX, 
-- end
-- lemma base_iff_indep_card_eq_r [finite_rk M] : M.base B ↔ M.indep B ∧ B.ncard = M.rk :=
-- begin
--   refine ⟨λ hB, ⟨hB.indep, hB.card⟩, 
--     λ h, base_iff_maximal_indep.mpr ⟨h.1, λ I hI hBI, eq_of_subset_of_ncard_le hBI _ hI.finite⟩⟩,
--   rw [h.2], exact hI.card_le_rk,
-- end
-- end basic 
-- section circuit 
-- variables {C : set α}
-- lemma circuit.finite_of_r_fin (hC : M.circuit C) (hCfin : M.r_fin C) : C.finite :=
-- begin
--   obtain ⟨e,he⟩ := hC.nonempty,
--   convert ((hC.diff_singleton_indep he).finite_of_r_fin (hCfin.subset (diff_subset _ _))).insert e, 
--   rw [insert_diff_singleton, insert_eq_of_mem he],  
-- end 
-- lemma circuit.r_fin_iff_finite (hC : M.circuit C) : M.r_fin C ↔ C.finite :=
-- ⟨hC.finite_of_r_fin, M.r_fin_of_finite⟩ 
-- lemma circuit.card_of_finite (hC : M.circuit C) (hfin : C.finite) : C.ncard = M.r C + 1 :=
-- begin
--   obtain ⟨e,he⟩ := hC.nonempty,
--   have hss : C \ {e} ⊂ C, by {refine ssubset_of_ne_of_subset _ (diff_subset _ _),
--     simpa only [ne.def, sdiff_eq_left, disjoint_singleton_right, not_not_mem]},
--   have hlb := (M.r_fin_of_finite hfin).r_mono hss.subset,
--   rw [(hC.ssubset_indep hss).r] at hlb,
--   linarith [ncard_diff_singleton_add_one he hfin, r_lt_card_of_dep_of_finite hfin hC.dep],
-- end 
-- lemma circuit.card [finitary M] (hC : M.circuit C) : C.ncard = M.r C + 1 :=
-- hC.card_of_finite hC.finite
-- /-- This lemma is phrased in terms of `nat` subtraction; it never underflows but is probably still
--   best avoided -/
-- lemma circuit.nat_r_eq [finitary M] (hC : M.circuit C) : M.r C = C.ncard - 1 :=
-- by rw [hC.card, nat.add_succ_sub_one, add_zero]
-- lemma circuit.cast_r_eq [finitary M] (hC : M.circuit C) : (M.r C : ℤ) = C.ncard - 1 :=
-- by rw [hC.card, nat.cast_add, nat.cast_one, add_tsub_cancel_right]
-- lemma exists_circuit_iff_card_lt_rk [finite M] : M.rk < M.E.ncard ↔ ∃ C, M.circuit C :=
-- begin
--   rw [rk, r_lt_card_iff_dep, dep_iff_supset_circuit], 
--   split, 
--   { rintro ⟨C, -, hC⟩, exact ⟨C, hC⟩}, 
--   rintro ⟨C, hC⟩, exact ⟨C, hC.subset_ground, hC⟩, 
-- end 
-- end circuit 
-- section cl_flat
-- variables {F F' F₁ F₂ H H₁ H₂ : set α}
-- lemma flat.r_insert_of_not_mem_of_r_fin (hF : M.flat F) (hfin : M.r_fin F) (he : e ∉ F) 
-- (heE : e ∈ M.E . ssE) :
--   M.r (insert e F) = M.r F + 1 :=
-- begin
--   obtain ⟨I, hI⟩ := M.exists_basis F, 
--   rw [←hF.cl, ←hI.cl, hI.indep.not_mem_cl_iff] at he, 
--   rw [←(hI.insert_basis_insert he.2).card, ←hI.card, 
--     ncard_insert_of_not_mem he.1 (hI.finite_of_r_fin hfin)],
-- end
-- lemma flat.r_insert_of_mem_compl_of_r_fin (hF : M.flat F) (he : e ∈ M.E \ F) (hfin : M.r_fin F) :
--   M.r (insert e F) = M.r F + 1 := hF.r_insert_of_not_mem_of_r_fin hfin he.2 he.1 
-- lemma flat.r_insert_of_mem_compl [finite_rk M] (hF : M.flat F) (he : e ∈ M.E \ F) :
--   M.r (insert e F) = M.r F + 1 := hF.r_insert_of_mem_compl_of_r_fin he (M.to_r_fin F)
-- lemma flat_iff_r_lt_r_insert_forall [finite_rk M] (hFE : F ⊆ M.E . ssE) : 
--   M.flat F ↔ ∀ e ∈ M.E \ F, M.r F < M.r (insert e F) :=
-- begin
--   refine ⟨λ hF e he, _, λ h, _⟩,
--   { rw [hF.r_insert_of_mem_compl he], norm_num },
--   rw [flat_iff_ssubset_cl_insert_forall], 
--   refine λ e he', (M.cl_subset (subset_insert _ _)).ssubset_of_ne (λ h_eq, (h e he').ne _), 
--   rw [←r_cl, h_eq, r_cl], 
-- end
-- lemma flat.mem_compl_iff_r_insert_of_r_fin (hF : M.flat F) (hfin : M.r_fin F) : 
--   e ∈ M.E \ F ↔ M.r (insert e F) = M.r F + 1 :=
-- begin
--   refine (em' (e ∈ M.E)).elim (λ h, iff_of_false (not_mem_subset (diff_subset _ _) h) _) (λ heE, _), 
--   { simp [r_insert_eq_of_not_mem_ground _ h] },
--   refine ⟨λ he, hF.r_insert_of_mem_compl_of_r_fin he hfin, λ h, _⟩,
--   rw [r_insert_eq_add_one_iff_r_ne] at h, 
--   refine by_contra (λ hss, h _), 
--   rw [mem_diff, not_and, not_not] at hss, 
--   rw [insert_eq_of_mem (hss heE)], 
-- end
-- lemma flat.mem_compl_iff_r_insert_eq [finite_rk M] (hF : M.flat F) : 
--   e ∈ M.E \ F ↔ M.r (insert e F) = M.r F + 1 :=
-- hF.mem_compl_iff_r_insert_of_r_fin (M.to_r_fin F)
-- lemma flat.r_lt_r_of_ssubset_of_r_fin (hF : M.flat F) (hFX : F ⊂ X) (hX : M.r_fin X) : 
--   M.r F < M.r X :=
-- begin
--   obtain ⟨e, heX, heF⟩ := exists_of_ssubset hFX, 
--   rw [nat.lt_iff_add_one_le, ←hF.r_insert_of_mem_compl_of_r_fin ⟨_, heF⟩ (hX.subset hFX.subset)], 
--   { exact hX.r_mono (insert_subset.mpr ⟨heX, hFX.subset⟩) },
--   exact hX.subset_ground heX,
-- end 
-- lemma flat.eq_of_r_le_r_subset_of_r_fin (hF : M.flat F) (hFfin : M.r_fin X) (hFX : F ⊆ X) 
-- (hr : M.r X ≤ M.r F) : 
--   F = X :=
-- by_contra (λ hne, (hF.r_lt_r_of_ssubset_of_r_fin (hFX.ssubset_of_ne hne) hFfin).not_le hr)
-- lemma flat.r_lt_r_of_ssubset [finite_rk M] (hF : M.flat F) (hFX : F ⊂ X) (hX : X ⊆ M.E . ssE) :
--   M.r F < M.r X := hF.r_lt_r_of_ssubset_of_r_fin hFX (M.to_r_fin X)
-- lemma flat.eq_of_le_r_subset [finite_rk M] (hF : M.flat F) (hFX : F ⊆ X) (hr : M.r X ≤ M.r F) 
-- (hXE : X ⊆ M.E . ssE) : F = X := hF.eq_of_r_le_r_subset_of_r_fin (M.to_r_fin X) hFX hr  
-- lemma flat.eq_ground_of_rk_le_r [finite_rk M] (hF : M.flat F) (hr : M.rk ≤ M.r F) : F = M.E :=
-- hF.eq_of_le_r_subset hF.subset_ground hr
-- lemma flat.r_eq_rk_iff_eq_ground [finite_rk M] (hF : M.flat F) : M.r F = M.rk ↔ F = M.E :=
-- ⟨λ h, hF.eq_ground_of_rk_le_r h.symm.le, by { rintro rfl, refl }⟩
-- lemma r_fin.mem_cl_iff_r_insert (hX : M.r_fin X) (he : e ∈ M.E . ssE) : 
--   e ∈ M.cl X ↔ M.r (insert e X) = M.r X :=
-- by rw [←not_iff_not, ←ne.def, not_mem_iff_mem_diff_of_mem he, ←r_insert_eq_add_one_iff_r_ne, 
--     ←r_insert_cl_eq_r_insert, ←M.r_cl X, (M.flat_of_cl X).mem_compl_iff_r_insert_of_r_fin hX.to_cl]
-- lemma r_fin.not_mem_cl_iff_r_insert (hX : M.r_fin X) :
--   e ∈ M.E \ M.cl X ↔ M.r (insert e X) = M.r X + 1 :=
-- begin
--   rw [r_insert_eq_add_one_iff_r_ne, ne.def], 
--   refine (em' (e ∈ M.E)).elim (λ he, iff_of_false (not_mem_subset (diff_subset _ _) he) 
--     (by simp [r_insert_eq_of_not_mem_ground _ he])) (λ he, _), 
--   rw [← hX.mem_cl_iff_r_insert, mem_diff, and_iff_right he], 
-- end
-- lemma mem_cl_iff_r_insert [finite_rk M] (X : set α) (he : e ∈ M.E . ssE) : 
--   e ∈ M.cl X ↔ M.r (insert e X) = M.r X :=
-- by rw [cl_eq_cl_inter_ground, r_eq_r_inter_ground, insert_inter_of_mem he, 
--       M.r_eq_r_inter_ground X, (M.to_r_fin (X ∩ M.E)).mem_cl_iff_r_insert]
-- lemma mem_compl_cl_iff_r_insert [finite_rk M] : e ∈ M.E \ M.cl X ↔ M.r (insert e X) = M.r X + 1 :=
-- by rw [r_insert_inter_ground, cl_eq_cl_inter_ground, M.r_eq_r_inter_ground X, 
--     (M.to_r_fin (X ∩ M.E)).not_mem_cl_iff_r_insert]
-- lemma subset_cl_iff_r_union_eq_r [finite_rk M] (hX : X ⊆ M.E . ssE) : 
--   X ⊆ M.cl Y ↔ M.r (Y ∪ X) = M.r Y :=
-- begin
--   refine ⟨λ h, _, λ h e heX, _⟩,
--   { rw [←r_union_cl_left_eq_r_union, union_eq_self_of_subset_right h, r_cl] }, 
--   rw [mem_cl_iff_r_insert _ (hX heX)], 
--   refine (M.r_mono (subset_insert _ _)).antisymm' ((M.r_mono _).trans_eq h),
--   exact insert_subset.mpr ⟨or.inr heX, subset_union_left _ _⟩,  
-- end
-- lemma r_insert_eq_add_one_of_not_mem_cl [finite_rk M] (h : e ∈ M.E \ M.cl X) :
--   M.r (insert e X) = M.r X + 1 := mem_compl_cl_iff_r_insert.mp h 
-- lemma mem_compl_cl_of_r_insert_gt [finite_rk M] (h : M.r X < M.r (insert e X)) : e ∈ M.E \ M.cl X :=
-- by { rw [mem_compl_cl_iff_r_insert, r_insert_eq_add_one_iff_r_ne], exact h.ne.symm  }
-- lemma mem_cl_of_r_insert_le [finite_rk M] (h : M.r (insert e X) ≤ M.r X) (he : e ∈ M.E . ssE) :
--   e ∈ M.cl X :=
-- by { rw [mem_cl_iff_r_insert], exact h.antisymm (M.r_mono (subset_insert _ _)) }
-- lemma spanning.r_eq (hX : M.spanning X) : M.r X = M.rk :=
-- by rw [←r_cl, hX.cl, rk]  
-- lemma r_eq_rk_iff_spanning [finite_rk M] (hX : X ⊆ M.E . ssE) : M.r X = M.rk ↔ M.spanning X :=
-- by rw [←r_cl, spanning_iff_cl, (M.flat_of_cl X).r_eq_rk_iff_eq_ground]
-- lemma spanning_iff_r_eq_rk [finite_rk M] : M.spanning X ↔ M.r X = M.rk ∧ X ⊆ M.E :=
-- by { rw [spanning, and.congr_left_iff], intro h, rw [←spanning_iff_cl, r_eq_rk_iff_spanning] }
-- lemma rk_le_r_iff_spanning [finite_rk M] (hX : X ⊆ M.E . ssE) : M.rk ≤ M.r X ↔ M.spanning X :=
-- by rw [←r_eq_rk_iff_spanning, le_iff_lt_or_eq, or_iff_right (M.r_le_rk X).not_lt, eq_comm]
-- lemma r_le_iff_cl {n : ℕ} [finite_rk M] (hX : X ⊆ M.E . ssE) : 
--   M.r X ≤ n ↔ ∃ I, X ⊆ M.cl I ∧ I.ncard ≤ n ∧ I.finite :=
-- begin
--   refine ⟨λ h, _, _⟩,
--   { obtain ⟨I,hI⟩ := M.exists_basis X,
--     exact ⟨I, hI.subset_cl, by rwa hI.card, hI.finite⟩ },
--   rintro ⟨I, hXI, hIn⟩,
--   refine (M.r_mono hXI).trans _, 
--   rw [r_cl],
--   exact (M.r_le_card_of_finite hIn.2).trans hIn.1,
-- end
-- lemma le_r_iff_cl {n : ℕ} [finite_rk M] (hX : X ⊆ M.E . ssE) : 
--   n ≤ M.r X ↔ ∀ I, X ⊆ M.cl I → I.finite → n ≤ I.ncard :=
-- begin
--   cases n, simp,
--   rw [←not_lt, ←not_iff_not, not_not, not_forall],
--   simp_rw [not_imp, not_le, nat.lt_succ_iff],
--   rw r_le_iff_cl,
--   tauto, 
-- end
-- lemma flat.covby_iff_r_of_r_fin (hF : M.flat F) (hFfin : M.r_fin F) (hF' : M.flat F') :
--   M.covby F F' ↔ F ⊆ F' ∧ M.r F' = M.r F + 1 :=
-- begin
--   rw hF.covby_iff_eq_cl_insert, 
--   refine ⟨_, λ h, _⟩, 
--   { rintro ⟨e, he, rfl⟩,
--     rw [and_iff_right 
--       (M.subset_cl_of_subset (subset_insert e F) (insert_subset.mpr ⟨he.1, hF.subset_ground⟩)), 
--       r_cl, (hF.mem_compl_iff_r_insert_of_r_fin hFfin).mp he],  }, 
--   have hss : F ⊂ F', from h.1.ssubset_of_ne (by { rintro rfl, simpa using h.2 }), 
--   obtain ⟨e, heF', heF⟩ := exists_of_ssubset hss, 
--   refine ⟨e, ⟨hF'.subset_ground heF',heF⟩, 
--     ((M.flat_of_cl _).eq_of_r_le_r_subset_of_r_fin _ _ _).symm⟩, 
--   { refine r_fin_of_r_ne_zero _, rw h.2, exact nat.succ_ne_zero _ },
--   { exact hF'.cl_subset_of_subset (insert_subset.mpr ⟨heF', h.1⟩) },
--   rw [h.2, r_cl, hF.r_insert_of_mem_compl_of_r_fin ⟨hF'.subset_ground heF',heF⟩ hFfin], 
-- end 
-- lemma flat.covby_iff_r [finite_rk M] (hF : M.flat F) (hF' : M.flat F') : 
--   M.covby F F' ↔ F ⊆ F' ∧ M.r F' = M.r F + 1 :=
-- hF.covby_iff_r_of_r_fin (M.to_r_fin F) hF'  
-- lemma hyperplane_iff_maximal_r [finite_rk M] (hH : H ⊆ M.E . ssE) : 
--   M.hyperplane H ↔ M.r H < M.rk ∧ ∀ X, H ⊂ X → X ⊆ M.E → M.r X = M.rk :=
-- begin
--   simp_rw [hyperplane_iff_maximal_nonspanning, mem_maximals_set_of_iff', not_and, not_not, 
--     lt_iff_not_le, and_iff_right hH, rk_le_r_iff_spanning, and.congr_right_iff], 
--   refine λ hH, ⟨λ h X hHX hXE, spanning.r_eq (h hHX hXE), λ h X hHX hXE, _⟩,
--   rw spanning_iff_r_eq_rk, 
--   exact ⟨h X hHX hXE, hXE⟩,
-- end 
-- lemma hyperplane.r_add_one [finite_rk M] (hH : M.hyperplane H) : M.r H + 1 = M.rk :=
-- by rw [←((hH.flat.covby_iff_r M.ground_flat).mp hH.covby).2, rk]
-- lemma hyperplane.cast_r [finite_rk M] (hH : M.hyperplane H) : (M.r H : ℤ) = M.rk - 1 := 
-- by simp [←hH.r_add_one]
-- lemma flat.hyperplane_of_r_add_one_eq_rk [finite_rk M] (hF : M.flat F) (h : M.r F + 1 = M.rk) :
--   M.hyperplane F :=
-- by rwa [hyperplane_iff_covby, hF.covby_iff_r M.ground_flat, and_iff_right hF.subset_ground, eq_comm]
-- lemma hyperplane_iff_flat_r_add_one_eq_r [finite_rk M] : 
--   M.hyperplane H ↔ M.flat H ∧ M.r H + 1 = M.rk :=
-- ⟨λ h, ⟨h.flat, h.r_add_one⟩, λ h, h.1.hyperplane_of_r_add_one_eq_rk h.2⟩
-- end cl_flat
-- section loop
-- lemma loop_iff_r (he : e ∈ M.E . ssE) : M.loop e ↔ M.r {e} = 0 :=
-- by rw [loop_iff_dep, ←r_lt_card_iff_dep_of_finite (finite_singleton e), ncard_singleton, 
--   nat.lt_one_iff]
-- lemma loop.r (he : M.loop e) : M.r {e} = 0 := loop_iff_r.mp he 
-- lemma r_eq_zero_iff_subset_loops [finite_rk M] (hX : X ⊆ M.E . ssE) : M.r X = 0 ↔ X ⊆ M.cl ∅ :=
-- (M.to_r_fin X).r_eq_zero_iff_subset_loops
-- lemma r_eq_zero_iff_inter_ground_subset_loops [finite_rk M] : M.r X = 0 ↔ X ∩ M.E ⊆ M.cl ∅ :=
-- by rw [←r_eq_zero_iff_subset_loops, r_eq_r_inter_ground]
-- lemma r_eq_zero_iff_forall_loop [finite_rk M] (hX : X ⊆ M.E . ssE) :
--   M.r X = 0 ↔ ∀ e ∈ X, M.loop e :=
-- r_eq_zero_iff_subset_loops
-- lemma r_eq_zero_of_subset_loops (h : X ⊆ M.cl ∅) : M.r X = 0 := 
-- by rw [←r_cl, cl_eq_loops_of_subset h, r_cl, r_empty]
-- lemma nonloop_iff_r : M.nonloop e ↔ M.r {e} = 1 :=
-- by rw [←indep_singleton, indep_iff_r_eq_card_of_finite (finite_singleton e), ncard_singleton]
-- lemma nonloop.r (he : M.nonloop e) : M.r {e} = 1 := nonloop_iff_r.mp he 
-- lemma coloop.r_compl_add_one [finite_rk M] (he : M.coloop e) : M.r (M.E \ {e}) + 1 = M.rk :=
-- begin
--   have := he.mem_ground,
--   rw [coloop_iff_cocircuit, ←compl_hyperplane_iff_cocircuit, hyperplane_iff_flat_r_add_one_eq_r] 
--     at he, 
--   exact he.2, 
-- end
-- lemma coloop_iff_r_compl_add_one_eq [finite_rk M] : M.coloop e ↔ M.r (M.E \ {e}) + 1 = M.rk :=
-- begin
--   refine ⟨coloop.r_compl_add_one, λ h, _⟩, 
--   have he : e ∈ M.E, 
--   { by_contra he', rw [r_diff_singleton_eq_of_not_mem_ground _ he', rk_def] at h, simpa using h },
--   rw [coloop_iff_cocircuit, ←compl_hyperplane_iff_cocircuit (singleton_subset_iff.mpr he), 
--     hyperplane_iff_flat_r_add_one_eq_r, and_iff_left h], 
--   simp_rw [flat_iff_r_lt_r_insert_forall, sdiff_sdiff_right_self, inf_eq_inter, 
--     ground_inter_right, mem_singleton_iff, forall_eq, insert_diff_singleton, insert_eq_of_mem he, 
--     ←rk_def, nat.lt_iff_add_one_le], 
--   rw h,
-- end
-- lemma coloop_iff_r_compl_lt [finite_rk M] : M.coloop e ↔ M.r (M.E \ {e}) < M.rk :=
-- by rw [coloop_iff_r_compl_add_one_eq, rk_def, nat.lt_iff_add_one_le, le_antisymm_iff, 
--     and_iff_left (M.r_le_r_diff_singleton_add_one e M.E)]
-- lemma coloop.cast_r_compl [finite_rk M] (he : M.coloop e) : (M.r (M.E \ {e}) : ℤ) = M.rk - 1 :=
-- by simp [←he.r_compl_add_one]
-- end loop 
-- section flat_of_r
-- variables {F F' P L : set α}
-- /-- `M.flat_of_r k F` means that `F` is a flat in `r` with finite rank `k`. -/
-- def flat_of_r (M : matroid_in α) (k : ℕ) (F : set α) := M.flat F ∧ M.r F = k ∧ M.r_fin F  
-- lemma flat_of_r.flat (h : M.flat_of_r k F) : M.flat F := h.1 
-- @[ssE_finish_rules] lemma flat_of_r.subset_ground (h : M.flat_of_r k F) : F ⊆ M.E :=
-- h.flat.subset_ground 
-- lemma flat_of_r.r (h : M.flat_of_r k F) : M.r F = k := h.2.1 
-- lemma flat_of_r.r_fin (h : M.flat_of_r k F) : M.r_fin F := h.2.2 
-- lemma flat.flat_of_r_of_ne_zero (hF : M.flat F) (hk : M.r F ≠ 0) : M.flat_of_r (M.r F) F :=
-- ⟨hF, rfl, r_fin_of_r_ne_zero hk⟩  
-- lemma flat.flat_of_r_of_ne_zero' (hF : M.flat F) (hr : M.r F = k) (hk : k ≠ 0) : 
--   M.flat_of_r (M.r F) F :=
-- hF.flat_of_r_of_ne_zero (by { subst hr, assumption } )   
-- lemma flat_of_r.nonempty (hF : M.flat_of_r k F) (hk : k ≠ 0) : F.nonempty := 
-- nonempty_of_r_nonzero (ne_of_eq_of_ne hF.r hk)
-- @[simp] lemma flat_of_r_zero_iff_loops : M.flat_of_r 0 F ↔ F = M.cl ∅ :=
-- begin
--   refine ⟨λ h,_, _⟩,
--   { obtain ⟨I, hI⟩ := M.exists_basis F, 
--     have hc := hI.card, 
--     rw [h.r, ncard_eq_zero (hI.finite_of_r_fin h.r_fin)] at hc, subst hc, 
--     rw [←h.flat.cl, hI.cl] },
--   rintro rfl, 
--   exact ⟨M.flat_of_cl _, by simp, M.r_fin_empty.to_cl⟩,   
-- end
-- lemma loops_flat_of_r_zero (M : matroid_in α) : M.flat_of_r 0 (M.cl ∅) :=
-- by rw flat_of_r_zero_iff_loops
-- lemma flat_of_r.covby_iff (hF : M.flat_of_r k F) : M.covby F F' ↔ M.flat_of_r (k+1) F' ∧ F ⊆ F' :=
-- begin
--   refine (em (M.flat F')).symm.elim (λ hF', iff_of_false (mt covby.flat_right hF') _) (λ hF', _), 
--   { exact mt (λ h, h.1.flat) hF' },
--   have hr := hF.r, subst hr, 
--   simp_rw [hF.flat.covby_iff_r_of_r_fin hF.r_fin hF', flat_of_r, and_comm, and.congr_right_iff, 
--     ← and_assoc, iff_and_self, and_iff_right hF'], 
--   refine λ h hF', r_fin_of_r_ne_zero _, 
--   rw hF', 
--   simp,  
-- end 
-- lemma flat_of_r.flat_of_r_add_one_of_covby (hF : M.flat_of_r k F) (hFF' : M.covby F F') : 
--   M.flat_of_r (k+1) F' := 
-- by { rw [hF.covby_iff] at hFF', exact hFF'.1 }
-- /-- A `point` is a rank-one flat -/
-- def point (M : matroid_in α) (P : set α) := M.flat_of_r 1 P 
-- /-- A `line` is a rank-two flat -/
-- def line (M : matroid_in α) (L : set α) := M.flat_of_r 2 L
-- /-- A `plane` is a rank-three flat -/
-- def plane (M : matroid_in α) (P : set α) := M.flat_of_r 3 P
-- lemma point.nonempty (hP : M.point P) : P.nonempty := flat_of_r.nonempty hP one_ne_zero
-- @[ssE_finish_rules] lemma point.subset_ground (hP : M.point P) : P ⊆ M.E := hP.flat.subset_ground 
-- lemma line.nonempty (hL : M.line L) : L.nonempty := flat_of_r.nonempty hL two_ne_zero
-- @[ssE_finish_rules] lemma line.subset_ground (hL : M.line L) : L ⊆ M.E := hL.flat.subset_ground 
-- lemma plane.nonempty (hP : M.plane P) : P.nonempty := flat_of_r.nonempty hP three_pos.ne.symm 
-- @[ssE_finish_rules] lemma plane.subset_ground (hP : M.plane P) : P ⊆ M.E := hP.flat.subset_ground 
-- lemma nonloop.cl_point (he : M.nonloop e) : M.point (M.cl {e}) := 
-- begin
--   rw [point, ←ncard_singleton e, ←he.indep.r, ←r_cl ],
--   exact (M.flat_of_cl _).flat_of_r_of_ne_zero (by { rw [r_cl, he.indep.r], simp }), 
-- end
-- lemma point.diff_loops_nonempty (hP : M.point P) : (P \ M.cl ∅).nonempty := 
-- nonempty_of_r_nonzero (by { rw [←r_cl, cl_diff_loops_eq_cl, r_cl, hP.r], exact one_ne_zero })
-- lemma point.exists_eq_cl_nonloop (hP : M.point P) : ∃ e, M.nonloop e ∧ P = M.cl {e} := 
-- begin
--   obtain ⟨I, hI⟩ := M.exists_basis P,
--   have hc := hI.card, 
--   rw [hP.r, ncard_eq_one] at hc, 
--   obtain ⟨e, rfl⟩ := hc, 
--   use e, 
--   rw [hI.cl, hP.flat.cl, and_iff_left rfl, nonloop_iff_r, hI.r, hP.r], 
-- end 
-- lemma point.eq_cl_nonloop (hP : M.point P) (heP : e ∈ P) (he : M.nonloop e) : P = M.cl {e} := 
-- begin
--   obtain ⟨I, hI, heI⟩ := he.indep.subset_basis_of_subset (singleton_subset_iff.mpr heP), 
--   have hc := hI.card, 
--   rw [hP.r, ncard_eq_one] at hc,  
--   obtain ⟨e', rfl⟩ := hc, 
--   simp only [subset_singleton_iff, mem_singleton_iff, forall_eq] at heI, 
--   rw [←hP.flat.cl, ←hI.cl, heI], 
-- end 
-- /-- The set of elements that span a point are precisely its nonloop members -/
-- lemma point.eq_cl_singleton_iff (h : M.point P) : M.cl {e} = P ↔ e ∈ P ∧ M.nonloop e :=
-- begin
--   simp only [nonloop, loop, ←mem_diff,  mem_preimage, mem_singleton_iff], 
--   refine ⟨_, λ hP, _⟩,
--   { rintro rfl, 
--     have hel : M.nonloop e,
--     { have he' := h.r, rwa [r_cl, ←nonloop_iff_r] at he',  }, 
--     exact ⟨M.mem_cl_self e, hel.not_loop, hel.mem_ground⟩ },
--   have he : M.nonloop e := hP.2, 
--   obtain ⟨J, hJ, heJ⟩ :=  he.indep.subset_basis_of_subset (singleton_subset_iff.mpr hP.1), 
--   have hJcard := hJ.card, 
--   rw [h.r, ncard_eq_one] at hJcard, 
--   obtain ⟨e', rfl⟩ := hJcard, 
--   simp only [subset_singleton_iff, mem_singleton_iff, forall_eq] at heJ, subst heJ,   
--   rw [←h.flat.cl, hJ.cl], 
-- end 
-- lemma point_iff_loops_covby : M.point P ↔ M.covby (M.cl ∅) P := 
-- begin
--   rw [flat_of_r.covby_iff M.loops_flat_of_r_zero, zero_add, point, iff_self_and],  
--   exact λ h, h.flat.loops_subset,  
-- end
-- end flat_of_r
-- -- section from_axioms
-- -- /-- There doesn't seem to be a nice way to axiomatize finite-rank matroids on infinite ground sets 
-- --   without a 'bases for sets exist'-type axiom. A troublesome example is the rank-1 non-matroid where 
-- --   the only rank-1 set is the (infinite) ground set, which satisfies finite versions of submodularity
-- --   but has no nonempty independent sets.  -/
-- -- lemma card_le_r_of_card_le_r_of_subset [finite E] (r : set α → ℕ) (r_le_card : ∀ X, r X ≤ X.ncard)
-- -- (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) {I J : set α} 
-- -- (hJ : J.ncard ≤ r J) (hIJ : I ⊆ J) :
-- --   I.ncard ≤ r I :=
-- -- begin
-- --   have hsm := r_submod I (J \ I), 
-- --   rw [inter_diff_self, union_diff_self, union_eq_self_of_subset_left hIJ] at hsm,  
-- --   linarith [r_le_card (J \ I), ncard_diff_add_ncard_eq_ncard hIJ], 
-- -- end    
-- -- lemma r_eq_r_of_maximal_indep [finite E] (r : set α → ℕ) (r_le_card : ∀ X, r X ≤ X.ncard)
-- -- (r_mono : ∀ ⦃X Y⦄, X ⊆ Y → r X ≤ r Y) (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) 
-- -- (I X : set α) (hI : I ∈ maximals (⊆) {J | J ⊆ X ∧ J.ncard ≤ r J}) : 
-- --   r I = r X :=
-- -- begin  
-- --   obtain ⟨J, ⟨hJX, hIJ, hJ⟩, hJmax⟩ :=
-- --     (to_finite X).maximals_nonempty_of_exists (λ J, I ⊆ J ∧ r J ≤ r I) hI.1.1 ⟨subset.rfl, rfl.le⟩,  
-- --   obtain (rfl | hss) := hJX.eq_or_ssubset, 
-- --   { exact hJ.antisymm' (r_mono hIJ) },
-- --   obtain ⟨e, heX, heJ⟩ := exists_of_ssubset hss, 
-- --   have hsm := r_submod (insert e I) J, 
-- --   rw [insert_union, union_eq_self_of_subset_left hIJ] at hsm, 
-- --   have heI : r (insert e I) ≤ r I,
-- --   { refine (em (e ∈ I)).elim (λ heI, by rw insert_eq_of_mem heI) (λ heI, le_of_not_lt (λ hlt, _)),
-- --     refine heI (hI.2 ⟨insert_subset.mpr ⟨heX, hI.1.1⟩, _⟩ (subset_insert e I) (mem_insert e I)),
-- --     linarith [hI.1.2, nat.lt_iff_add_one_le.mp hlt, ncard_insert_of_not_mem heI] },
-- --   have heJ : r I + 1 ≤ r (insert e J), 
-- --   { refine nat.add_one_le_iff.mpr (lt_of_not_le (λ hle, heJ _)), 
-- --     exact (hJmax ⟨insert_subset.mpr ⟨heX, hss.subset⟩, ⟨hIJ.trans (subset_insert e J), hle⟩⟩ 
-- --       (subset_insert e J) (mem_insert e J)) },
-- --   linarith [r_mono (subset_inter (subset_insert e I) hIJ)], 
-- -- end 
-- -- def matroid_of_r [finite E] (r : set α → ℕ) (r_le_card : ∀ X, r X ≤ X.ncard)
-- -- (r_mono : ∀ ⦃X Y⦄, X ⊆ Y → r X ≤ r Y) (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) : 
-- --   matroid_in α :=
-- -- matroid_of_indep_of_finite (λ I, I.ncard ≤ r I) (by { use ∅, simp,   })   
-- -- (λ I J, card_le_r_of_card_le_r_of_subset r ‹_› ‹_›)
-- -- (begin
-- --   intros I J hI hJ hIJ, 
-- --   by_contra' h', 
-- --   have con := r_eq_r_of_maximal_indep r ‹_› ‹_› ‹_› I (I ∪ J) ⟨⟨subset_union_left _ _, hI⟩, _⟩,     
-- --   { exact (r_le_card I).not_lt 
-- --       ((hIJ.trans_le (hJ.trans (r_mono (subset_union_right I J)))).trans_eq con.symm) },
-- --   exact λ K hK hIK e heK, by_contra (λ heI, 
-- --     ((card_le_r_of_card_le_r_of_subset r ‹_› ‹_› hK.2 (insert_subset.mpr ⟨heK, hIK⟩)).not_lt 
-- --       (h' _ ((hK.1 heK).elim (false.elim ∘ heI) id) heI ))), 
-- -- end) 
-- -- @[simp] lemma matroid_of_r_apply [finite E] (r : set α → ℕ) (r_le_card : ∀ X, r X ≤ X.ncard)
-- -- (r_mono : ∀ ⦃X Y⦄, X ⊆ Y → r X ≤ r Y) (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) :
-- -- (matroid_of_r r r_le_card r_mono r_submod).r  = r :=
-- -- begin
-- --   ext X, 
-- --   obtain ⟨I, hI⟩ := (matroid_of_r r ‹_› ‹_› ‹_›).exists_basis X, 
-- --   rw [←hI.card], 
-- --   simp_rw [matroid_of_r, basis_iff, matroid_of_indep_of_finite_apply] at hI,  
-- --   rw [hI.1.antisymm (r_le_card I), r_eq_r_of_maximal_indep r ‹_› ‹_› ‹_›], 
-- --   exact ⟨⟨hI.2.1,hI.1⟩, λ J hJ hIJ, (hI.2.2 J hJ.2 hIJ hJ.1).symm.subset⟩
-- -- end 
-- -- /-- Construction of a matroid from an `int`-valued rank function that is everywhere nonnegative,
-- --   rather than a `nat`-valued one. Useful for defining matroids whose rank function involves
-- --   subtraction. -/
-- -- def matroid_of_int_r [finite E] (r : set α → ℤ) (r_nonneg : ∀ X, 0 ≤ r X) 
-- -- (r_le_card : ∀ X, r X ≤ X.ncard) (r_mono : ∀ X Y, X ⊆ Y → r X ≤ r Y) 
-- -- (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) :
-- --   matroid_in α :=
-- -- matroid_of_r (int.nat_abs ∘ r)
-- --   (λ X, by {zify, convert r_le_card X, rw abs_eq_self, apply r_nonneg})
-- --   (λ X Y hXY, by {zify, convert r_mono X Y hXY, all_goals {rw abs_eq_self, apply r_nonneg}})
-- --   (λ X Y, by {zify, convert r_submod X Y, all_goals {rw abs_eq_self, apply r_nonneg}})
-- -- @[simp] lemma matroid_of_int_r_apply [finite E] (r : set α → ℤ) (r_nonneg : ∀ X, 0 ≤ r X)
-- -- (r_le_card : ∀ X, r X ≤ X.ncard) (r_mono : ∀ X Y, X ⊆ Y → r X ≤ r Y)
-- -- (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) (X : set α) :
-- --   ((matroid_of_int_r r r_nonneg r_le_card r_mono r_submod).r X : ℤ) = r X :=
-- -- by simpa [matroid_of_int_r] using r_nonneg _
-- -- end from_axioms
-- -- section dual
-- -- variables [finite E]
-- -- lemma coindep_iff_r : M.coindep X ↔ M.r Xᶜ = M.rk :=
-- -- begin
-- --   rw [coindep_iff_disjoint_base],
-- --   split,
-- --   { rintros ⟨B,hB,hBX⟩,
-- --     refine le_antisymm (M.r_le_rk _) _,
-- --     rw ←subset_compl_iff_disjoint_left at hBX,
-- --     rw [←hB.r],
-- --     exact M.r_mono hBX },
-- --   intro hr,
-- --   obtain ⟨B, hB⟩ := M.exists_basis Xᶜ,
-- --   refine ⟨B, hB.indep.base_of_rk_le_card _, subset_compl_iff_disjoint_left.mp hB.subset⟩,
-- --   rw [←hB.indep.r, hB.r, hr],
-- -- end
-- -- lemma dual_r_add_rk_eq (M : matroid_in α) (X : set α) : M﹡.r X + M.rk = ncard X + M.r Xᶜ  :=
-- -- begin
-- --   set r' : set α → ℤ := λ X, X.ncard + M.r Xᶜ - M.rk with hr',
-- --   have hr'_nonneg : ∀ X, 0 ≤ r' X,
-- --   { intro X, simp_rw hr', linarith [M.rk_le_card_add_r_compl X]},
-- --   have hr'_mono : ∀ X Y, X ⊆ Y → r' X ≤ r' Y,
-- --   { intros X Y hXY, simp_rw hr',
-- --     linarith [M.r_add_card_le_r_add_card_of_subset (compl_subset_compl.mpr hXY),
-- --        ncard_add_ncard_compl X, ncard_add_ncard_compl Y]},
-- --   have hr'_le_card : ∀ X, r' X ≤ X.ncard,
-- --   { intros X, simp_rw hr', linarith [M.r_le_rk Xᶜ] },
-- --   have hr'_submod : ∀ X Y, r' (X ∩ Y) + r' (X ∪ Y) ≤ r' X + r' Y,
-- --   { intros X Y, simp_rw [hr', compl_inter, compl_union],
-- --     linarith [ncard_inter_add_ncard_union X Y, M.r_submod Xᶜ Yᶜ]},
-- --   set M' := matroid_of_int_r r' hr'_nonneg hr'_le_card hr'_mono hr'_submod with hM',
-- --   have hM'M : M' = M﹡,
-- --   { refine eq_of_indep_iff_indep_forall (λ I, _),
-- --     rw [indep_iff_r_eq_card, dual_indep_iff_coindep, coindep_iff_r], zify,
-- --     simp_rw [hM', matroid_of_int_r_apply, hr'],
-- --     refine ⟨λ h, _, λ h, _⟩,
-- --     all_goals { simp only at h, linarith} },
-- --   rw [←hM'M], zify, simp_rw [hM', matroid_of_int_r_apply, hr'],
-- --   ring,
-- -- end
-- -- lemma dual_r_cast_eq (M : matroid_in α) (X : set α) : (M﹡.r X : ℤ) = ncard X + M.r Xᶜ - M.rk :=
-- -- by linarith [M.dual_r_add_rk_eq X]
-- -- end dual 
-- end matroid_in

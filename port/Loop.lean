import Oneshot.Basic
import Oneshot.Circuit

/-
  A `loop` of a matroid_in is a one-element circuit, or, definitionally, a member of `M.cl ∅`.  
  Thus, the set of loops of `M` is equal to `M.cl ∅`, and we prefer this notation instead of 
  `{e | M.loop e}` or similar. A `nonloop` is simply an element that is not a loop, but we give 
  it a definition for the sake of dot notation. 
-/
/-
  A `loop` of a matroid_in is a one-element circuit, or, definitionally, a member of `M.cl ∅`.  
  Thus, the set of loops of `M` is equal to `M.cl ∅`, and we prefer this notation instead of 
  `{e | M.loop e}` or similar. A `nonloop` is simply an element that is not a loop, but we give 
  it a definition for the sake of dot notation. 
-/
-- open_locale classical 
-- open_locale classical
variable {α : Type _} {M M₁ M₂ : MatroidIn α} {I C X Y Z K F F₁ F₂ : Set α} {e f x y z : α}

open Set

namespace MatroidIn

-- ### Loops
/-- A loop is a member of the closure of the empty set -/
def Loop (M : MatroidIn α) (e : α) : Prop :=
  e ∈ M.cl ∅
#align matroid_in.loop MatroidIn.Loop

theorem loop_iff_mem_cl_empty : M.Loop e ↔ e ∈ M.cl ∅ :=
  Iff.rfl
#align matroid_in.loop_iff_mem_cl_empty MatroidIn.loop_iff_mem_cl_empty

theorem cl_empty_eq_loops (M : MatroidIn α) : M.cl ∅ = {e | M.Loop e} :=
  rfl
#align matroid_in.cl_empty_eq_loops MatroidIn.cl_empty_eq_loops

@[ssE_finish_rules]
theorem Loop.mem_ground (he : M.Loop e) : e ∈ M.e :=
  cl_subset_ground M ∅ he
#align matroid_in.loop.mem_ground MatroidIn.Loop.mem_ground

theorem loop_iff_dep : M.Loop e ↔ M.Dep {e} := by
  rw [loop_iff_mem_cl_empty, M.empty_indep.mem_cl_iff_of_not_mem (not_mem_empty e),
    insert_emptyc_eq]
#align matroid_in.loop_iff_dep MatroidIn.loop_iff_dep

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem loop_iff_not_indep
    (he : e ∈ M.e := by
      run_tac
        ssE) :
    M.Loop e ↔ ¬M.indep {e} := by rw [loop_iff_dep, ← not_indep_iff]
#align matroid_in.loop_iff_not_indep MatroidIn.loop_iff_not_indep

theorem Loop.dep (he : M.Loop e) : M.Dep {e} :=
  loop_iff_dep.mp he
#align matroid_in.loop.dep MatroidIn.Loop.dep

theorem loop_iff_circuit : M.Loop e ↔ M.Circuit {e} :=
  by
  by_cases he : e ∈ M.E
  ·
    simp_rw [circuit_iff_forall_ssubset, ssubset_singleton_iff, forall_eq, empty_indep,
      and_true_iff, loop_iff_dep]
  exact iff_of_false (he ∘ loop.mem_ground) (he ∘ fun h => h.subset_ground rfl)
#align matroid_in.loop_iff_circuit MatroidIn.loop_iff_circuit

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem loop_iff_not_mem_base_forall
    (he : e ∈ M.e := by
      run_tac
        ssE) :
    M.Loop e ↔ ∀ B, M.base B → e ∉ B := by
  simp_rw [loop_iff_dep, ← not_indep_iff, indep_iff_subset_base, not_exists, not_and,
    singleton_subset_iff]
#align matroid_in.loop_iff_not_mem_base_forall MatroidIn.loop_iff_not_mem_base_forall

theorem Loop.circuit (he : M.Loop e) : M.Circuit {e} :=
  loop_iff_circuit.mp he
#align matroid_in.loop.circuit MatroidIn.Loop.circuit

theorem Loop.mem_cl (he : M.Loop e) (X : Set α) : e ∈ M.cl X :=
  M.cl_mono (empty_subset _) he
#align matroid_in.loop.mem_cl MatroidIn.Loop.mem_cl

theorem Loop.mem_flat (he : M.Loop e) {F : Set α} (hF : M.Flat F) : e ∈ F := by have := he.mem_cl F;
  rwa [hF.cl] at this 
#align matroid_in.loop.mem_flat MatroidIn.Loop.mem_flat

theorem Flat.loops_subset (hF : M.Flat F) : M.cl ∅ ⊆ F := fun e he => Loop.mem_flat he hF
#align matroid_in.flat.loops_subset MatroidIn.Flat.loops_subset

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Loop.dep_of_mem (he : M.Loop e) (h : e ∈ X)
    (hXE : X ⊆ M.e := by
      run_tac
        ssE) :
    M.Dep X :=
  he.Dep.supset (singleton_subset_iff.mpr h) hXE
#align matroid_in.loop.dep_of_mem MatroidIn.Loop.dep_of_mem

theorem Loop.not_indep_of_mem (he : M.Loop e) (h : e ∈ X) : ¬M.indep X := fun hX =>
  he.Dep.not_indep (hX.Subset (singleton_subset_iff.mpr h))
#align matroid_in.loop.not_indep_of_mem MatroidIn.Loop.not_indep_of_mem

theorem Loop.not_mem_of_indep (he : M.Loop e) (hI : M.indep I) : e ∉ I := fun h =>
  he.not_indep_of_mem h hI
#align matroid_in.loop.not_mem_of_indep MatroidIn.Loop.not_mem_of_indep

theorem Loop.eq_of_circuit_mem (he : M.Loop e) (hC : M.Circuit C) (h : e ∈ C) : C = {e} := by
  rw [he.circuit.eq_of_subset_circuit hC (singleton_subset_iff.mpr h)]
#align matroid_in.loop.eq_of_circuit_mem MatroidIn.Loop.eq_of_circuit_mem

theorem Indep.disjoint_loops (hI : M.indep I) : Disjoint I (M.cl ∅) :=
  by_contra fun h =>
    let ⟨e, ⟨heI, he⟩⟩ := not_disjoint_iff.mp h
    Loop.not_mem_of_indep he hI heI
#align matroid_in.indep.disjoint_loops MatroidIn.Indep.disjoint_loops

theorem Indep.eq_empty_of_subset_loops (hI : M.indep I) (h : I ⊆ M.cl ∅) : I = ∅ :=
  eq_empty_iff_forall_not_mem.mpr fun e he => Loop.not_mem_of_indep (h he) hI he
#align matroid_in.indep.eq_empty_of_subset_loops MatroidIn.Indep.eq_empty_of_subset_loops

theorem cl_eq_loops_of_subset (h : X ⊆ M.cl ∅) : M.cl X = M.cl ∅ :=
  (cl_subset_cl h).antisymm (M.cl_mono (empty_subset _))
#align matroid_in.cl_eq_loops_of_subset MatroidIn.cl_eq_loops_of_subset

theorem Loop.cl (he : M.Loop e) : M.cl {e} = M.cl ∅ :=
  cl_eq_loops_of_subset (singleton_subset_iff.mpr he)
#align matroid_in.loop.cl MatroidIn.Loop.cl

theorem loop_iff_cl_eq_cl_empty' : M.Loop e ↔ M.cl {e} = M.cl ∅ ∧ e ∈ M.e :=
  by
  rw [loop_iff_dep, dep_iff, singleton_subset_iff, and_congr_left_iff]
  intro he
  rw [not_indep_iff, ← loop_iff_dep]
  exact ⟨fun h => by rw [h.cl], fun h => by rw [loop_iff_mem_cl_empty, ← h]; exact M.mem_cl_self e⟩
#align matroid_in.loop_iff_cl_eq_cl_empty' MatroidIn.loop_iff_cl_eq_cl_empty'

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem loop_iff_cl_eq_cl_empty
    (he : e ∈ M.e := by
      run_tac
        ssE) :
    M.Loop e ↔ M.cl {e} = M.cl ∅ := by rw [loop_iff_cl_eq_cl_empty', and_iff_left he]
#align matroid_in.loop_iff_cl_eq_cl_empty MatroidIn.loop_iff_cl_eq_cl_empty

theorem cl_union_eq_cl_of_subset_loops {Y : Set α} (hY : Y ⊆ M.cl ∅) (X : Set α) :
    M.cl (X ∪ Y) = M.cl X := by
  rw [← cl_union_cl_right_eq, cl_eq_loops_of_subset hY, cl_union_cl_right_eq, union_empty]
#align matroid_in.cl_union_eq_cl_of_subset_loops MatroidIn.cl_union_eq_cl_of_subset_loops

theorem cl_diff_eq_cl_of_subset_loops {Y : Set α} (hY : Y ⊆ M.cl ∅) (X : Set α) :
    M.cl (X \ Y) = M.cl X := by
  rw [← cl_union_eq_cl_of_subset_loops hY, diff_union_self, cl_union_eq_cl_of_subset_loops hY]
#align matroid_in.cl_diff_eq_cl_of_subset_loops MatroidIn.cl_diff_eq_cl_of_subset_loops

-- ### Nonloops
/-- A `nonloop` is an element that is not a loop -/
def Nonloop (M : MatroidIn α) (e : α) : Prop :=
  ¬M.Loop e ∧ e ∈ M.e
#align matroid_in.nonloop MatroidIn.Nonloop

def nonloops (M : MatroidIn α) : Set α :=
  {e | M.Nonloop e}
#align matroid_in.nonloops MatroidIn.nonloops

@[ssE_finish_rules]
theorem Nonloop.mem_ground (h : M.Nonloop e) : e ∈ M.e :=
  h.2
#align matroid_in.nonloop.mem_ground MatroidIn.Nonloop.mem_ground

theorem Nonloop.not_loop (he : M.Nonloop e) : ¬M.Loop e :=
  he.1
#align matroid_in.nonloop.not_loop MatroidIn.Nonloop.not_loop

theorem Loop.not_nonloop (he : M.Loop e) : ¬M.Nonloop e := fun h => h.not_loop he
#align matroid_in.loop.not_nonloop MatroidIn.Loop.not_nonloop

@[simp]
theorem mem_nonloops_iff : e ∈ M.nonloops ↔ M.Nonloop e :=
  Iff.rfl
#align matroid_in.mem_nonloops_iff MatroidIn.mem_nonloops_iff

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
@[simp]
theorem not_loop_iff
    (he : e ∈ M.e := by
      run_tac
        ssE) :
    ¬M.Loop e ↔ M.Nonloop e :=
  (and_iff_left he).symm
#align matroid_in.not_loop_iff MatroidIn.not_loop_iff

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
@[simp]
theorem not_nonloop_iff
    (he : e ∈ M.e := by
      run_tac
        ssE) :
    ¬M.Nonloop e ↔ M.Loop e := by rw [← not_loop_iff, Classical.not_not]
#align matroid_in.not_nonloop_iff MatroidIn.not_nonloop_iff

theorem nonloops_eq_compl_cl_empty : M.nonloops = M.e \ M.cl ∅ := by ext;
  simp [nonloop, loop, and_comm']
#align matroid_in.nonloops_eq_compl_cl_empty MatroidIn.nonloops_eq_compl_cl_empty

@[simp]
theorem compl_nonloops_eq_cl_empty : M.e \ M.nonloops = M.cl ∅ := by
  simp [nonloops_eq_compl_cl_empty]
#align matroid_in.compl_nonloops_eq_cl_empty MatroidIn.compl_nonloops_eq_cl_empty

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem loop_or_nonloop (M : MatroidIn α) (e : α)
    (he : e ∈ M.e := by
      run_tac
        ssE) :
    M.Loop e ∨ M.Nonloop e := by rw [nonloop, and_iff_left he]; apply em
#align matroid_in.loop_or_nonloop MatroidIn.loop_or_nonloop

@[simp]
theorem indep_singleton : M.indep {e} ↔ M.Nonloop e :=
  by
  rw [nonloop, loop_iff_dep, dep_iff, not_and, not_imp_not, singleton_subset_iff]
  exact ⟨fun h => ⟨fun _ => h, singleton_subset_iff.mp h.subset_ground⟩, fun h => h.1 h.2⟩
#align matroid_in.indep_singleton MatroidIn.indep_singleton

alias indep_singleton ↔ indep.nonloop nonloop.indep
#align matroid_in.indep.nonloop MatroidIn.Indep.nonloop
#align matroid_in.nonloop.indep MatroidIn.Nonloop.indep

attribute [protected] indep.nonloop nonloop.indep

theorem Indep.nonloop_of_mem (hI : M.indep I) (h : e ∈ I) : M.Nonloop e := by rw [← not_loop_iff];
  exact fun he => (he.not_mem_of_indep hI) h
#align matroid_in.indep.nonloop_of_mem MatroidIn.Indep.nonloop_of_mem

theorem Cocircuit.nonloop_of_mem {K : Set α} (hK : M.Cocircuit K) (he : e ∈ K) : M.Nonloop e :=
  by
  have heE : e ∈ M.E := hK.subset_ground he
  rw [← not_loop_iff]
  intro hel
  rw [cocircuit_iff_mem_minimals, mem_minimals_setOf_iff] at hK 
  suffices : K = K \ {e}; exact (this.subset he).2 rfl
  apply hK.2 (fun B hB => _) (diff_subset _ _)
  rw [diff_eq, inter_right_comm, inter_assoc, ← diff_eq,
    diff_singleton_eq_self (hel.not_mem_of_indep hB.indep)]
  exact hK.1 B hB
#align matroid_in.cocircuit.nonloop_of_mem MatroidIn.Cocircuit.nonloop_of_mem

theorem Circuit.nonloop_of_mem_of_one_lt_card (hC : M.Circuit C) (h : 1 < C.ncard) (he : e ∈ C) :
    M.Nonloop e :=
  not_loop_iff.mp fun hlp => by simpa [hlp.eq_of_circuit_mem hC he] using h
#align matroid_in.circuit.nonloop_of_mem_of_one_lt_card MatroidIn.Circuit.nonloop_of_mem_of_one_lt_card

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem nonloop_of_not_mem_cl (h : e ∉ M.cl X)
    (he : e ∈ M.e := by
      run_tac
        ssE) :
    M.Nonloop e :=
  not_loop_iff.mp fun he => h (he.mem_cl X)
#align matroid_in.nonloop_of_not_mem_cl MatroidIn.nonloop_of_not_mem_cl

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem nonloop_iff_not_mem_cl_empty
    (he : e ∈ M.e := by
      run_tac
        ssE) :
    M.Nonloop e ↔ e ∉ M.cl ∅ := by rw [nonloop, loop_iff_mem_cl_empty, and_iff_left he]
#align matroid_in.nonloop_iff_not_mem_cl_empty MatroidIn.nonloop_iff_not_mem_cl_empty

theorem Nonloop.mem_cl_singleton (he : M.Nonloop e) (hef : e ∈ M.cl {f}) : f ∈ M.cl {e} :=
  by
  by_cases hf : f ∈ M.E
  · refine' (M.loop_or_nonloop f).elim (fun hf => hf.mem_cl _) fun hf => _
    rw [he.indep.mem_cl_iff, mem_singleton_iff]
    rwa [hf.indep.mem_cl_iff he.mem_ground, pair_comm, mem_singleton_iff, eq_comm] at hef 
  rw [cl_eq_cl_inter_ground, singleton_inter_eq_empty.mpr hf, ← loop_iff_mem_cl_empty] at hef 
  exact (he.not_loop hef).elim
#align matroid_in.nonloop.mem_cl_singleton MatroidIn.Nonloop.mem_cl_singleton

theorem Nonloop.mem_cl_comm (he : M.Nonloop e) (hf : M.Nonloop f) : f ∈ M.cl {e} ↔ e ∈ M.cl {f} :=
  ⟨hf.mem_cl_singleton, he.mem_cl_singleton⟩
#align matroid_in.nonloop.mem_cl_comm MatroidIn.Nonloop.mem_cl_comm

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Nonloop.nonloop_of_mem_cl (he : M.Nonloop e) (hef : e ∈ M.cl {f})
    (hf : f ∈ M.e := by
      run_tac
        ssE) :
    M.Nonloop f := by
  rw [nonloop, and_iff_left hf]
  exact fun hf => he.not_loop (by rwa [hf.cl] at hef )
#align matroid_in.nonloop.nonloop_of_mem_cl MatroidIn.Nonloop.nonloop_of_mem_cl

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic matroid_in.ssE -/
theorem Nonloop.cl_eq_of_mem_cl (he : M.Nonloop e) (hef : e ∈ M.cl {f}) : M.cl {e} = M.cl {f} :=
  by
  ext x
  obtain hxE | hxE := (em (x ∈ M.E)).symm
  · refine' iff_of_false (hxE ∘ _) (hxE ∘ _) <;> apply M.cl_subset_ground
  obtain hx | hx := M.loop_or_nonloop x
  · exact ⟨fun _ => hx.mem_cl _, fun _ => hx.mem_cl _⟩
  refine' ⟨fun h => _, fun h => he.mem_cl_singleton _⟩
  · rw [← singleton_subset_iff, ← cl_subset_cl_iff_subset_cl] at *
    exact h.trans hef
  have hfx := hx.mem_cl_singleton h
  rw [← singleton_subset_iff, ← cl_subset_cl_iff_subset_cl] at *
  · exact hef.trans hfx
  exact
    hfx.trans
      (by
        run_tac
          ssE)
#align matroid_in.nonloop.cl_eq_of_mem_cl MatroidIn.Nonloop.cl_eq_of_mem_cl

theorem Nonloop.cl_eq_cl_iff_dep (he : M.Nonloop e) (hf : M.Nonloop f) :
    M.cl {e} = M.cl {f} ↔ e = f ∨ ¬M.indep {e, f} :=
  by
  rw [← imp_iff_or_not]
  refine' ⟨fun hef => _, fun h => he.cl_eq_of_mem_cl (by rwa [hf.indep.mem_cl_iff])⟩
  have hf : f ∈ M.cl {e} := by rw [hef]; exact M.mem_cl_self f
  rw [pair_comm, eq_comm, ← mem_singleton_iff]
  exact he.indep.mem_cl_iff.mp hf
#align matroid_in.nonloop.cl_eq_cl_iff_dep MatroidIn.Nonloop.cl_eq_cl_iff_dep

theorem exists_nonloop_of_empty_not_base (h : ¬M.base ∅) : ∃ e, M.Nonloop e :=
  by
  obtain ⟨B, hB⟩ := M.exists_base
  obtain rfl | ⟨e, he⟩ := B.eq_empty_or_nonempty
  · exact (h hB).elim
  exact ⟨e, hB.indep.nonloop_of_mem he⟩
#align matroid_in.exists_nonloop_of_empty_not_base MatroidIn.exists_nonloop_of_empty_not_base

-- ### Coloops
/-- A coloop is a loop of the dual  -/
def Coloop (M : MatroidIn α) (e : α) : Prop :=
  M﹡.Loop e
#align matroid_in.coloop MatroidIn.Coloop

@[ssE_finish_rules]
theorem Coloop.mem_ground (he : M.Coloop e) : e ∈ M.e :=
  @Loop.mem_ground α (M﹡) e he
#align matroid_in.coloop.mem_ground MatroidIn.Coloop.mem_ground

theorem coloop_iff_mem_cl_empty : M.Coloop e ↔ e ∈ M﹡.cl ∅ :=
  Iff.rfl
#align matroid_in.coloop_iff_mem_cl_empty MatroidIn.coloop_iff_mem_cl_empty

theorem coloops_eq_dual_cl_empty : {e | M.Coloop e} = M﹡.cl ∅ :=
  rfl
#align matroid_in.coloops_eq_dual_cl_empty MatroidIn.coloops_eq_dual_cl_empty

theorem Coloop.dual_loop (he : M.Coloop e) : M﹡.Loop e :=
  he
#align matroid_in.coloop.dual_loop MatroidIn.Coloop.dual_loop

theorem Loop.dual_coloop (he : M.Loop e) : M﹡.Coloop e := by rwa [coloop, dual_dual]
#align matroid_in.loop.dual_coloop MatroidIn.Loop.dual_coloop

@[simp]
theorem dual_coloop_iff_loop : M﹡.Coloop e ↔ M.Loop e :=
  ⟨fun h => by rw [← dual_dual M]; exact h.dual_loop, Loop.dual_coloop⟩
#align matroid_in.dual_coloop_iff_loop MatroidIn.dual_coloop_iff_loop

@[simp]
theorem dual_loop_iff_coloop : M﹡.Loop e ↔ M.Coloop e :=
  ⟨fun h => by rw [← dual_dual M]; exact h.dual_coloop, Coloop.dual_loop⟩
#align matroid_in.dual_loop_iff_coloop MatroidIn.dual_loop_iff_coloop

theorem coloop_iff_forall_mem_base : M.Coloop e ↔ ∀ ⦃B⦄, M.base B → e ∈ B :=
  by
  obtain he | he := (em (e ∈ M.E)).symm
  · refine' iff_of_false (he ∘ coloop.mem_ground) (he ∘ fun h => _)
    obtain ⟨B, hB⟩ := M.exists_base
    exact hB.subset_ground (h hB)
  rw [← dual_loop_iff_coloop, loop_iff_not_mem_base_forall]
  simp_rw [dual_base_iff']
  refine' ⟨fun h B hB => _, fun h B hB heB => (h hB.1).2 heB⟩
  have he' := h (M.E \ B) ⟨_, diff_subset _ _⟩
  · simp only [mem_diff, not_and, not_not_mem] at he' ; exact he' he
  simp only [sdiff_sdiff_right_self, inf_eq_inter]
  rwa [inter_eq_self_of_subset_right hB.subset_ground]
#align matroid_in.coloop_iff_forall_mem_base MatroidIn.coloop_iff_forall_mem_base

theorem Base.mem_of_coloop {B : Set α} (hB : M.base B) (he : M.Coloop e) : e ∈ B :=
  coloop_iff_forall_mem_base.mp he hB
#align matroid_in.base.mem_of_coloop MatroidIn.Base.mem_of_coloop

theorem Coloop.mem_of_base (he : M.Coloop e) {B : Set α} (hB : M.base B) : e ∈ B :=
  coloop_iff_forall_mem_base.mp he hB
#align matroid_in.coloop.mem_of_base MatroidIn.Coloop.mem_of_base

theorem Coloop.nonloop (h : M.Coloop e) : M.Nonloop e :=
  let ⟨B, hB⟩ := M.exists_base
  hB.indep.nonloop_of_mem ((coloop_iff_forall_mem_base.mp h) hB)
#align matroid_in.coloop.nonloop MatroidIn.Coloop.nonloop

theorem Loop.not_coloop (h : M.Loop e) : ¬M.Coloop e :=
  by
  rw [← dual_loop_iff_coloop]; rw [← dual_dual M, dual_loop_iff_coloop] at h 
  exact h.nonloop.not_loop
#align matroid_in.loop.not_coloop MatroidIn.Loop.not_coloop

theorem Coloop.not_mem_circuit (he : M.Coloop e) (hC : M.Circuit C) : e ∉ C :=
  by
  intro heC
  rw [coloop_iff_forall_mem_base] at he 
  obtain ⟨B, hB, hCB⟩ := (hC.diff_singleton_indep heC).exists_base_supset
  have h := insert_subset.mpr ⟨he hB, hCB⟩
  rw [insert_diff_singleton, insert_eq_of_mem heC] at h 
  exact hC.dep.not_indep (hB.indep.subset h)
#align matroid_in.coloop.not_mem_circuit MatroidIn.Coloop.not_mem_circuit

theorem Circuit.not_coloop_of_mem (hC : M.Circuit C) (heC : e ∈ C) : ¬M.Coloop e := fun h =>
  h.not_mem_circuit hC heC
#align matroid_in.circuit.not_coloop_of_mem MatroidIn.Circuit.not_coloop_of_mem

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem coloop_iff_forall_mem_cl_iff_mem
    (he : e ∈ M.e := by
      run_tac
        ssE) :
    M.Coloop e ↔ ∀ X, e ∈ M.cl X ↔ e ∈ X :=
  by
  rw [coloop_iff_forall_mem_base]
  refine' ⟨fun h X => _, fun h B hB => (h B).mp (by rwa [hB.cl])⟩
  rw [cl_eq_cl_inter_ground]
  refine' ⟨fun hecl => _, fun heX => _⟩
  · obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
    obtain ⟨B, hB, hIB⟩ := hI.indep.exists_base_supset
    have heB := h hB
    rw [hI.mem_cl_iff, imp_iff_right (hB.indep.subset (insert_subset.mpr ⟨heB, hIB⟩))] at hecl 
    exact (hI.subset hecl).1
  exact mem_cl_of_mem' _ ⟨heX, he⟩
#align matroid_in.coloop_iff_forall_mem_cl_iff_mem MatroidIn.coloop_iff_forall_mem_cl_iff_mem

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (X «expr ⊆ » M.E) -/
theorem coloop_iff_forall_mem_cl_iff_mem' :
    M.Coloop e ↔ e ∈ M.e ∧ ∀ (X) (_ : X ⊆ M.e), e ∈ M.cl X ↔ e ∈ X :=
  by
  refine'
    ⟨fun h => ⟨h.mem_ground, fun X hX => ((coloop_iff_forall_mem_cl_iff_mem h.mem_ground).mp h) X⟩,
      _⟩
  · rintro ⟨he, h⟩
    apply (coloop_iff_forall_mem_cl_iff_mem he).mpr
    intro X
    have : X ∩ M.E ⊆ M.E := inter_subset_right _ _
    have := h (X ∩ M.E) this; rw [← cl_eq_cl_inter_ground] at this 
    rw [this]
    refine' ⟨fun h => h.1, fun h => _⟩
    · rw [mem_inter_iff]
      exact ⟨h, he⟩
#align matroid_in.coloop_iff_forall_mem_cl_iff_mem' MatroidIn.coloop_iff_forall_mem_cl_iff_mem'

theorem Coloop.mem_cl_iff_mem (he : M.Coloop e) : e ∈ M.cl X ↔ e ∈ X :=
  coloop_iff_forall_mem_cl_iff_mem.mp he X
#align matroid_in.coloop.mem_cl_iff_mem MatroidIn.Coloop.mem_cl_iff_mem

theorem Coloop.mem_of_mem_cl (he : M.Coloop e) (hX : e ∈ M.cl X) : e ∈ X := by
  rwa [← he.mem_cl_iff_mem]
#align matroid_in.coloop.mem_of_mem_cl MatroidIn.Coloop.mem_of_mem_cl

@[simp]
theorem cl_inter_coloops_eq (M : MatroidIn α) (X : Set α) : M.cl X ∩ M﹡.cl ∅ = X ∩ M﹡.cl ∅ :=
  by
  simp_rw [Set.ext_iff, mem_inter_iff, ← coloop_iff_mem_cl_empty, and_congr_left_iff]
  intro e he
  rw [he.mem_cl_iff_mem]
#align matroid_in.cl_inter_coloops_eq MatroidIn.cl_inter_coloops_eq

theorem cl_inter_eq_of_subset_coloops (X : Set α) (hK : K ⊆ M﹡.cl ∅) : M.cl X ∩ K = X ∩ K :=
  by
  rw [M.cl_eq_cl_inter_ground]
  nth_rw 2 [← inter_eq_self_of_subset_right (hK.trans (cl_subset_ground _ _))]
  rw [dual_ground, ← inter_assoc]
  refine' inter_eq_inter_iff_right.mpr ⟨(inter_subset_left _ _).trans (M.subset_cl _), _⟩
  refine' ((inter_subset_inter_right (M.cl _) hK).trans (M.cl_inter_coloops_eq _).Subset).trans _
  exact inter_subset_left _ _
#align matroid_in.cl_inter_eq_of_subset_coloops MatroidIn.cl_inter_eq_of_subset_coloops

theorem cl_union_eq_of_subset_coloops (X : Set α) {K : Set α} (hK : K ⊆ M﹡.cl ∅) :
    M.cl (X ∪ K) = M.cl X ∪ K :=
  by
  have hKE : K ⊆ M.E := hK.trans (cl_subset_ground _ _)
  rw [← cl_union_cl_left_eq]
  refine' (M.subset_cl _).antisymm' fun e he => _
  obtain he' | ⟨C, hC, heC, hCss⟩ := mem_cl_iff_exists_circuit.mp he; assumption
  have hCX : C \ {e} ⊆ M.cl X :=
    by
    rw [diff_subset_iff, singleton_union]
    exact fun f hfC =>
      (hCss hfC).elim Or.inl fun h' =>
        h'.elim Or.inr fun hfK => (hC.not_coloop_of_mem hfC).elim (hK hfK)
  exact Or.inl (cl_subset_cl hCX (hC.subset_cl_diff_singleton e heC))
#align matroid_in.cl_union_eq_of_subset_coloops MatroidIn.cl_union_eq_of_subset_coloops

theorem cl_eq_of_subset_coloops (hK : K ⊆ M﹡.cl ∅) : M.cl K = K ∪ M.cl ∅ := by
  rw [← empty_union K, cl_union_eq_of_subset_coloops _ hK, empty_union, union_comm]
#align matroid_in.cl_eq_of_subset_coloops MatroidIn.cl_eq_of_subset_coloops

theorem cl_diff_eq_of_subset_coloops (X : Set α) {K : Set α} (hK : K ⊆ M﹡.cl ∅) :
    M.cl (X \ K) = M.cl X \ K := by
  nth_rw 2 [← inter_union_diff X K]
  rw [union_comm, cl_union_eq_of_subset_coloops _ ((inter_subset_right X K).trans hK),
    union_diff_distrib, diff_eq_empty.mpr (inter_subset_right X K), union_empty, eq_comm,
    sdiff_eq_self_iff_disjoint, disjoint_iff_forall_ne]
  rintro e heK _ heX rfl
  have he : M.coloop e := hK heK
  rw [he.mem_cl_iff_mem] at heX 
  exact heX.2 heK
#align matroid_in.cl_diff_eq_of_subset_coloops MatroidIn.cl_diff_eq_of_subset_coloops

theorem cl_disjoint_of_disjoint_of_subset_coloops (hXK : Disjoint X K) (hK : K ⊆ M﹡.cl ∅) :
    Disjoint (M.cl X) K := by
  rwa [disjoint_iff_inter_eq_empty, cl_inter_eq_of_subset_coloops X hK, ←
    disjoint_iff_inter_eq_empty]
#align matroid_in.cl_disjoint_of_disjoint_of_subset_coloops MatroidIn.cl_disjoint_of_disjoint_of_subset_coloops

theorem cl_disjoint_coloops_of_disjoint_coloops (hX : Disjoint X (M﹡.cl ∅)) :
    Disjoint (M.cl X) (M﹡.cl ∅) :=
  cl_disjoint_of_disjoint_of_subset_coloops hX Subset.rfl
#align matroid_in.cl_disjoint_coloops_of_disjoint_coloops MatroidIn.cl_disjoint_coloops_of_disjoint_coloops

theorem cl_insert_coloop_eq (X : Set α) {he : M.Coloop e} : M.cl (insert e X) = insert e (M.cl X) :=
  by
  rw [← union_singleton, ← union_singleton, cl_union_eq_of_subset_coloops]
  rwa [singleton_subset_iff]
#align matroid_in.cl_insert_coloop_eq MatroidIn.cl_insert_coloop_eq

@[simp]
theorem cl_union_coloops_eq (M : MatroidIn α) (X : Set α) : M.cl (X ∪ M﹡.cl ∅) = M.cl X ∪ M﹡.cl ∅ :=
  cl_union_eq_of_subset_coloops _ Subset.rfl
#align matroid_in.cl_union_coloops_eq MatroidIn.cl_union_coloops_eq

theorem Coloop.not_mem_cl_of_not_mem (he : M.Coloop e) (hX : e ∉ X) : e ∉ M.cl X :=
  mt he.mem_cl_iff_mem.mp hX
#align matroid_in.coloop.not_mem_cl_of_not_mem MatroidIn.Coloop.not_mem_cl_of_not_mem

theorem Coloop.insert_indep_of_indep (he : M.Coloop e) (hI : M.indep I) : M.indep (insert e I) :=
  (em (e ∈ I)).elim (fun h => by rwa [insert_eq_of_mem h]) fun h => by
    rwa [hI.insert_indep_iff_of_not_mem h, he.mem_cl_iff_mem]
#align matroid_in.coloop.insert_indep_of_indep MatroidIn.Coloop.insert_indep_of_indep

theorem union_indep_iff_indep_of_subset_coloops (hK : K ⊆ M﹡.cl ∅) : M.indep (I ∪ K) ↔ M.indep I :=
  by
  refine' ⟨fun h => h.Subset (subset_union_left I K), fun h => _⟩
  obtain ⟨B, hB, hIB⟩ := h.exists_base_supset
  exact hB.indep.subset (union_subset hIB (hK.trans fun e he => coloop.mem_of_base he hB))
#align matroid_in.union_indep_iff_indep_of_subset_coloops MatroidIn.union_indep_iff_indep_of_subset_coloops

theorem diff_indep_iff_indep_of_subset_coloops (hK : K ⊆ M﹡.cl ∅) : M.indep (I \ K) ↔ M.indep I :=
  by
  rw [← union_indep_iff_indep_of_subset_coloops hK, diff_union_self,
    union_indep_iff_indep_of_subset_coloops hK]
#align matroid_in.diff_indep_iff_indep_of_subset_coloops MatroidIn.diff_indep_iff_indep_of_subset_coloops

theorem indep_iff_union_coloops_indep : M.indep I ↔ M.indep (I ∪ M﹡.cl ∅) :=
  (union_indep_iff_indep_of_subset_coloops Subset.rfl).symm
#align matroid_in.indep_iff_union_coloops_indep MatroidIn.indep_iff_union_coloops_indep

theorem indep_iff_diff_coloops_indep : M.indep I ↔ M.indep (I \ M﹡.cl ∅) :=
  (diff_indep_iff_indep_of_subset_coloops Subset.rfl).symm
#align matroid_in.indep_iff_diff_coloops_indep MatroidIn.indep_iff_diff_coloops_indep

theorem coloops_indep (M : MatroidIn α) : M.indep (M﹡.cl ∅) := by
  rw [indep_iff_diff_coloops_indep, diff_self]; exact M.empty_indep
#align matroid_in.coloops_indep MatroidIn.coloops_indep

theorem indep_of_subset_coloops (h : I ⊆ M﹡.cl ∅) : M.indep I :=
  M.coloops_indep.Subset h
#align matroid_in.indep_of_subset_coloops MatroidIn.indep_of_subset_coloops

theorem Coloop.cocircuit (he : M.Coloop e) : M.Cocircuit {e} := by
  rwa [← dual_loop_iff_coloop, loop_iff_circuit, dual_circuit_iff_cocircuit] at he 
#align matroid_in.coloop.cocircuit MatroidIn.Coloop.cocircuit

theorem coloop_iff_cocircuit : M.Coloop e ↔ M.Cocircuit {e} := by
  rw [← dual_loop_iff_coloop, loop_iff_circuit, dual_circuit_iff_cocircuit]
#align matroid_in.coloop_iff_cocircuit MatroidIn.coloop_iff_cocircuit

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (I «expr ⊆ » M₁.E) -/
/-- If two matroid_ins agree on loops and coloops, and have the same independent sets after 
  loops/coloops are removed, they are equal. -/
theorem eq_of_indep_iff_indep_forall_disjoint_loops_coloops {M₁ M₂ : MatroidIn α} (hE : M₁.e = M₂.e)
    (hl : M₁.cl ∅ = M₂.cl ∅) (hc : M₁﹡.cl ∅ = M₂﹡.cl ∅)
    (h : ∀ (I) (_ : I ⊆ M₁.e), Disjoint I (M₁.cl ∅ ∪ M₁﹡.cl ∅) → (M₁.indep I ↔ M₂.indep I)) :
    M₁ = M₂ := by
  refine' eq_of_indep_iff_indep_forall hE fun I hI => _
  rw [indep_iff_diff_coloops_indep, @indep_iff_diff_coloops_indep _ M₂, ← hc]
  obtain hdj | hndj := em (Disjoint I (M₁.cl ∅))
  · rw [h _ ((diff_subset _ _).trans hI)]
    rw [disjoint_union_right]
    exact ⟨disjoint_of_subset_left (diff_subset _ _) hdj, disjoint_sdiff_left⟩
  obtain ⟨e, heI, hel : M₁.loop e⟩ := not_disjoint_iff_nonempty_inter.mp hndj
  refine' iff_of_false (hel.not_indep_of_mem ⟨heI, hel.not_coloop⟩) _
  rw [loop_iff_mem_cl_empty, hl, ← loop_iff_mem_cl_empty] at hel ; rw [hc]
  exact hel.not_indep_of_mem ⟨heI, hel.not_coloop⟩
#align matroid_in.eq_of_indep_iff_indep_forall_disjoint_loops_coloops MatroidIn.eq_of_indep_iff_indep_forall_disjoint_loops_coloops

end MatroidIn


import Oneshot.Closure
import Oneshot.Restriction
import Oneshot.Mathlib.Data.Set.Basic
import Mathbin.Data.Nat.Lattice

noncomputable section

open scoped Classical

variable {α : Type _} {M M₁ M₂ : MatroidIn α} {I C C' C₁ C₂ X : Set α} {e f : α}

open Set

namespace MatroidIn

theorem Circuit.dep (hC : M.Circuit C) : M.Dep C :=
  hC.1
#align matroid_in.circuit.dep MatroidIn.Circuit.dep

@[ssE_finish_rules]
theorem Circuit.subset_ground (hC : M.Circuit C) : C ⊆ M.e :=
  hC.Dep.subset_ground
#align matroid_in.circuit.subset_ground MatroidIn.Circuit.subset_ground

theorem Circuit.sSubset_indep (hC : M.Circuit C) (hXC : X ⊂ C) : M.indep X :=
  by
  rw [← not_dep_iff (hXC.subset.trans hC.subset_ground)]
  rw [circuit, mem_minimals_setOf_iff] at hC 
  exact fun h => hXC.ne.symm (hC.2 h hXC.subset)
#align matroid_in.circuit.ssubset_indep MatroidIn.Circuit.sSubset_indep

theorem circuit_iff : M.Circuit C ↔ M.Dep C ∧ ∀ I, M.Dep I → I ⊆ C → I = C := by
  rw [circuit, mem_minimals_setOf_iff]; tauto
#align matroid_in.circuit_iff MatroidIn.circuit_iff

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (I «expr ⊂ » C) -/
theorem circuit_iff_forall_sSubset : M.Circuit C ↔ M.Dep C ∧ ∀ (I) (_ : I ⊂ C), M.indep I :=
  by
  simp_rw [circuit_iff, ssubset_iff_subset_ne, and_congr_right_iff]
  exact fun hC =>
    ⟨fun h I hIC =>
      indep_of_not_dep (hIC.2 ∘ fun hD => h _ hD hIC.1) (hIC.1.trans hC.subset_ground),
      fun h I hD hIC => by_contra fun hne => hD.not_indep (h _ ⟨hIC, hne⟩)⟩
#align matroid_in.circuit_iff_forall_ssubset MatroidIn.circuit_iff_forall_sSubset

theorem Circuit.diff_singleton_indep (hC : M.Circuit C) (he : e ∈ C) : M.indep (C \ {e}) :=
  hC.sSubset_indep (diff_singleton_sSubset.2 he)
#align matroid_in.circuit.diff_singleton_indep MatroidIn.Circuit.diff_singleton_indep

theorem Circuit.diff_singleton_basis (hC : M.Circuit C) (he : e ∈ C) : M.Basis (C \ {e}) C :=
  by
  refine' (hC.diff_singleton_indep he).basis_of_forall_insert (diff_subset _ _) fun f hf hI => _
  simp only [mem_diff, mem_singleton_iff, not_and, Classical.not_not] at hf 
  have := hf.2 hf.1; subst this
  rw [insert_diff_singleton, insert_eq_of_mem he] at hI 
  exact hC.dep.not_indep hI
#align matroid_in.circuit.diff_singleton_basis MatroidIn.Circuit.diff_singleton_basis

theorem circuit_iff_mem_minimals : M.Circuit C ↔ C ∈ minimals (· ⊆ ·) {X | M.Dep X} :=
  Iff.rfl
#align matroid_in.circuit_iff_mem_minimals MatroidIn.circuit_iff_mem_minimals

theorem Circuit.eq_of_dep_subset (hC : M.Circuit C) (hX : M.Dep X) (hXC : X ⊆ C) : X = C :=
  eq_of_le_of_not_lt hXC (hX.not_indep ∘ hC.sSubset_indep)
#align matroid_in.circuit.eq_of_dep_subset MatroidIn.Circuit.eq_of_dep_subset

theorem Circuit.not_sSubset (hC : M.Circuit C) (hC' : M.Circuit C') : ¬C' ⊂ C := fun h' =>
  h'.Ne <| hC.eq_of_dep_subset hC'.Dep h'.Subset
#align matroid_in.circuit.not_ssubset MatroidIn.Circuit.not_sSubset

theorem Circuit.nonempty (hC : M.Circuit C) : C.Nonempty := by rw [Set.nonempty_iff_ne_empty];
  rintro rfl; exact hC.1.1 M.empty_indep
#align matroid_in.circuit.nonempty MatroidIn.Circuit.nonempty

theorem empty_not_circuit (M : MatroidIn α) : ¬M.Circuit ∅ := fun h => by simpa using h.nonempty
#align matroid_in.empty_not_circuit MatroidIn.empty_not_circuit

theorem Circuit.finite [Finitary M] (hC : M.Circuit C) : C.Finite :=
  let ⟨h⟩ := ‹M.Finitary›
  h C hC
#align matroid_in.circuit.finite MatroidIn.Circuit.finite

theorem circuit_iff_dep_forall_diff_singleton_indep :
    M.Circuit C ↔ M.Dep C ∧ ∀ e ∈ C, M.indep (C \ {e}) :=
  by
  rw [circuit_iff_forall_ssubset, and_congr_right_iff]
  refine' fun hdep => ⟨fun h e heC => h _ <| diff_singleton_ssubset.2 heC, fun h I hIC => _⟩
  obtain ⟨e, heC, heI⟩ := exists_of_ssubset hIC
  exact (h e heC).Subset (subset_diff_singleton hIC.subset heI)
#align matroid_in.circuit_iff_dep_forall_diff_singleton_indep MatroidIn.circuit_iff_dep_forall_diff_singleton_indep

theorem Circuit.eq_of_dep_subset_self (hC : M.Circuit C) (hX : M.Dep X) (hXC : X ⊆ C) : C = X :=
  by_contra fun h => hX.not_indep (hC.sSubset_indep (ssubset_of_subset_of_ne hXC (Ne.symm h)))
#align matroid_in.circuit.eq_of_dep_subset_self MatroidIn.Circuit.eq_of_dep_subset_self

theorem Circuit.eq_of_subset_circuit (hC₁ : M.Circuit C₁) (hC₂ : M.Circuit C₂) (h : C₁ ⊆ C₂) :
    C₁ = C₂ :=
  (hC₂.eq_of_dep_subset_self hC₁.Dep h).symm
#align matroid_in.circuit.eq_of_subset_circuit MatroidIn.Circuit.eq_of_subset_circuit

theorem Circuit.circuit_restrict_of_subset (hC : M.Circuit C) (hCX : C ⊆ X) : (M ‖ X).Circuit C :=
  by
  rw [← restrict_inter_ground]
  have hCX' : C ⊆ (M ‖ (X ∩ M.E)).e := by rw [restrict_ground_eq];
    exact subset_inter hCX hC.subset_ground
  simp_rw [circuit_iff, restrict_dep_iff, subset_inter_iff, and_iff_right hCX,
    and_iff_left hC.subset_ground, and_iff_right hC.dep]
  exact fun D hD hDC => hC.eq_of_dep_subset hD.1 hDC
#align matroid_in.circuit.circuit_restrict_of_subset MatroidIn.Circuit.circuit_restrict_of_subset

/-- For an independent set `I` that spans a point `e ∉ I`, the unique circuit contained in 
`I ∪ {e}`. Has the junk value `{e}` if `e ∈ I` and `univ` if `e ∉ M.cl I`. -/
def fundCircuit (M : MatroidIn α) (e : α) (I : Set α) :=
  insert e (⋂₀ {J | J ⊆ I ∧ e ∈ M.cl J})
#align matroid_in.fund_circuit MatroidIn.fundCircuit

theorem fundCircuit_subset_ground (heI : e ∈ M.cl I) : M.fundCircuit e I ⊆ M.e :=
  by
  refine'
    insert_subset.mpr
      ⟨(cl_subset_ground _ _) heI, (sInter_subset_of_mem _).trans (inter_subset_right I M.E)⟩
  refine' ⟨inter_subset_left _ _, _⟩
  rwa [← cl_eq_cl_inter_ground]
#align matroid_in.fund_circuit_subset_ground MatroidIn.fundCircuit_subset_ground

theorem fundCircuit_subset_insert (he : e ∈ M.cl I) : M.fundCircuit e I ⊆ insert e I :=
  insert_subset_insert (sInter_subset_of_mem ⟨rfl.Subset, he⟩)
#align matroid_in.fund_circuit_subset_insert MatroidIn.fundCircuit_subset_insert

theorem mem_fundCircuit (M : MatroidIn α) (e : α) (I : Set α) : e ∈ fundCircuit M e I :=
  mem_insert _ _
#align matroid_in.mem_fund_circuit MatroidIn.mem_fundCircuit

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic matroid_in.ssE -/
/-- The fundamental circuit of `e` and `I` has the junk value `{e}` if `e ∈ I` -/
theorem Indep.fundCircuit_eq_of_mem (hI : M.indep I) (he : e ∈ I) : M.fundCircuit e I = {e} :=
  by
  rw [fund_circuit, ← union_singleton, union_eq_right_iff_subset]
  refine' sInter_subset_of_mem _
  simp only [mem_set_of_eq, singleton_subset_iff, and_iff_right he]
  exact
    mem_cl_of_mem _ (mem_singleton _)
      (singleton_subset_iff.mpr
        (by
          run_tac
            ssE))
#align matroid_in.indep.fund_circuit_eq_of_mem MatroidIn.Indep.fundCircuit_eq_of_mem

theorem Indep.fundCircuit_circuit (hI : M.indep I) (he : e ∈ M.cl I \ I) :
    M.Circuit (M.fundCircuit e I) :=
  by
  rw [circuit_iff_dep_forall_diff_singleton_indep, ←
    not_indep_iff (fund_circuit_subset_ground he.1), fund_circuit]
  have hu : M.indep (⋃₀ {J : Set α | J ⊆ I ∧ e ∈ M.cl J}) :=
    hI.subset (sUnion_subset fun J => And.left)
  have hI' : I ∈ {J : Set α | J ⊆ I ∧ e ∈ M.cl J} := ⟨rfl.subset, he.1⟩
  refine' ⟨fun hi => _, fun f hf => _⟩
  · rw [indep.insert_indep_iff_of_not_mem, ←
      bInter_cl_eq_cl_sInter_of_sUnion_indep _ ⟨I, hI'⟩ hu] at hi 
    · simpa using hi
    · exact hI.subset (sInter_subset_of_mem hI')
    exact fun heIs => he.2 (sInter_subset_of_mem hI' heIs)
  obtain rfl | hne := em (e = f)
  · refine' hu.subset _
    simp only [insert_diff_of_mem, mem_singleton]
    exact
      subset_trans (diff_subset _ _) ((sInter_subset_of_mem hI').trans (subset_sUnion_of_mem hI'))
  rw [mem_insert_iff, mem_sInter, eq_comm, iff_false_intro hne, false_or_iff] at hf 
  have hi : M.indep (⋂₀ {J : Set α | J ⊆ I ∧ e ∈ M.cl J} \ {f}) :=
    hI.subset ((diff_subset _ _).trans (sInter_subset_of_mem hI'))
  rw [← insert_diff_singleton_comm hne, hi.insert_indep_iff_of_not_mem]
  · intro hcl
    exact (hf _ ⟨(diff_subset _ _).trans (sInter_subset_of_mem hI'), hcl⟩).2 rfl
  exact fun h'e => he.2 ((diff_subset _ _).trans (sInter_subset_of_mem hI') h'e)
#align matroid_in.indep.fund_circuit_circuit MatroidIn.Indep.fundCircuit_circuit

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (C «expr ⊆ » X) -/
theorem exists_circuit_subset_of_dep (hX : M.Dep X) : ∃ (C : _) (_ : C ⊆ X), M.Circuit C :=
  by
  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain rfl | hss := (ssubset_or_eq_of_subset hI.subset).symm
  · exact (hX.not_indep hI.indep).elim
  obtain ⟨e, heX, heI⟩ := exists_of_ssubset hss
  have he : e ∈ M.cl I \ I := ⟨hI.subset_cl heX, heI⟩
  exact
    ⟨M.fund_circuit e I,
      (fund_circuit_subset_insert he.1).trans (insert_subset.mpr ⟨heX, hss.subset⟩),
      hI.indep.fund_circuit_circuit he⟩
#align matroid_in.exists_circuit_subset_of_dep MatroidIn.exists_circuit_subset_of_dep

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (C «expr ⊆ » X) -/
theorem dep_iff_supset_circuit
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.Dep X ↔ ∃ (C : _) (_ : C ⊆ X), M.Circuit C :=
  ⟨exists_circuit_subset_of_dep, by rintro ⟨C, hCX, hC⟩; exact hC.dep.supset hCX⟩
#align matroid_in.dep_iff_supset_circuit MatroidIn.dep_iff_supset_circuit

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (C «expr ⊆ » I) -/
theorem indep_iff_forall_subset_not_circuit' :
    M.indep I ↔ (∀ (C) (_ : C ⊆ I), ¬M.Circuit C) ∧ I ⊆ M.e :=
  by
  by_cases hI : I ⊆ M.E
  · rw [← not_iff_not, not_indep_iff]
    simp_rw [dep_iff_supset_circuit, and_iff_left hI, not_forall, Classical.not_not]
  exact iff_of_false (hI ∘ indep.subset_ground) (hI ∘ And.right)
#align matroid_in.indep_iff_forall_subset_not_circuit' MatroidIn.indep_iff_forall_subset_not_circuit'

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (C «expr ⊆ » I) -/
theorem indep_iff_forall_subset_not_circuit
    (hI : I ⊆ M.e := by
      run_tac
        ssE) :
    M.indep I ↔ ∀ (C) (_ : C ⊆ I), ¬M.Circuit C := by
  rw [indep_iff_forall_subset_not_circuit', and_iff_left hI]
#align matroid_in.indep_iff_forall_subset_not_circuit MatroidIn.indep_iff_forall_subset_not_circuit

theorem Circuit.subset_cl_diff_singleton (hC : M.Circuit C) (e : α) : C ⊆ M.cl (C \ {e}) :=
  by
  by_cases he : e ∈ C
  · rw [(hC.diff_singleton_basis he).cl]; exact M.subset_cl _
  rw [diff_singleton_eq_self he]; exact M.subset_cl _
#align matroid_in.circuit.subset_cl_diff_singleton MatroidIn.Circuit.subset_cl_diff_singleton

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem mem_cl_iff_exists_circuit
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    e ∈ M.cl X ↔ e ∈ X ∨ ∃ C, M.Circuit C ∧ e ∈ C ∧ C ⊆ insert e X :=
  by
  refine' ⟨fun h => _, _⟩
  · by_contra' h'
    obtain ⟨I, hI⟩ := M.exists_basis X
    have hIe : ¬M.indep (insert e I) := by
      intro hI'
      refine' indep_iff_not_mem_cl_diff_forall.mp hI' e (mem_insert _ _) _
      rwa [insert_diff_of_mem _ (mem_singleton _),
        diff_singleton_eq_self (not_mem_subset hI.subset h'.1), hI.cl]
    have heI : e ∈ M.cl I \ I := by rw [hI.cl]; exact ⟨h, not_mem_subset hI.subset h'.1⟩
    have hC := hI.indep.fund_circuit_circuit heI
    exact
      h'.2 _ hC (mem_fund_circuit _ _ _)
        ((fund_circuit_subset_insert heI.1).trans (insert_subset_insert hI.subset))
  rintro (heX | ⟨C, hC, heC, hCX⟩)
  apply mem_cl_of_mem _ heX
  refine' (M.cl_subset _) (hC.subset_cl_diff_singleton e heC)
  rwa [diff_subset_iff]
#align matroid_in.mem_cl_iff_exists_circuit MatroidIn.mem_cl_iff_exists_circuit

theorem mem_cl_iff_exists_circuit_of_not_mem (he : e ∉ X) :
    e ∈ M.cl X ↔ ∃ C, M.Circuit C ∧ e ∈ C ∧ C ⊆ insert e X :=
  by
  rw [cl_eq_cl_inter_ground, mem_cl_iff_exists_circuit, mem_inter_iff, iff_false_intro he,
    false_and_iff, false_or_iff]
  refine' exists_congr fun C => _
  simp_rw [and_congr_right_iff]
  refine' fun hC heC =>
    ⟨fun hCX => hCX.trans (insert_subset_insert (inter_subset_left _ _)), fun hCX => _⟩
  refine' (subset_inter hCX hC.subset_ground).trans _
  rw [insert_inter_distrib]
  exact inter_subset_inter_right _ (subset_insert _ _)
#align matroid_in.mem_cl_iff_exists_circuit_of_not_mem MatroidIn.mem_cl_iff_exists_circuit_of_not_mem

/-- A generalization of the strong circuit elimination axiom. For finite matroids, this is 
  equivalent to the case where `ι` is a singleton type, which is the usual two-circuit version. 
  The stronger version is required for axiomatizing infinite matroids via circuits. -/
theorem Circuit.strong_multi_elimination {ι : Type _} (hC : M.Circuit C) (x : ι → α)
    (Cs : ι → Set α) (hCs : ∀ i, M.Circuit (Cs i)) (h_mem : ∀ i, x i ∈ C ∩ Cs i)
    (h_unique : ∀ i i', x i ∈ Cs i' → i = i') {z : α} (hz : z ∈ C \ ⋃ i, Cs i) :
    ∃ C', M.Circuit C' ∧ z ∈ C' ∧ C' ⊆ (C ∪ ⋃ i, Cs i) \ range x :=
  by
  set Y := (C ∪ ⋃ x, Cs x) \ insert z (range x) with hY
  have hYE : Y ⊆ M.E :=
    by
    refine' (diff_subset _ _).trans (union_subset hC.subset_ground _)
    exact Union_subset fun i => (hCs i).subset_ground
  have h₁ : range x ⊆ M.cl (⋃ i, (Cs i \ {x i}) \ insert z (range x)) :=
    by
    rintro e ⟨i, rfl⟩
    have h' := (hCs i).subset_cl_diff_singleton (x i) (h_mem i).2
    refine' mem_of_mem_of_subset h' (M.cl_subset _)
    refine' subset_Union_of_subset i (subset_diff.mpr ⟨rfl.subset, _⟩)
    rw [disjoint_iff_forall_ne]
    rintro y hy z (rfl | ⟨j, rfl⟩) rfl
    · exact hz.2 (mem_Union_of_mem i hy.1)
    refine' hy.2 (mem_singleton_iff.mpr _)
    rw [h_unique _ _ hy.1]
  have h₂ : range x ⊆ M.cl Y :=
    by
    refine' h₁.trans (M.cl_subset (Union_subset fun x => _))
    refine' diff_subset_diff_left (subset_union_of_subset_right _ _)
    exact subset_Union_of_subset x (diff_subset _ _)
  have h₃ : C \ {z} ⊆ M.cl Y :=
    by
    suffices C \ {z} ⊆ C \ insert z (range x) ∪ range x
      by
      rw [union_diff_distrib] at hY 
      convert this.trans (union_subset_union ((subset_union_left _ _).trans_eq hY.symm) h₂)
      rw [union_eq_right_iff_subset.mpr]
      exact M.subset_cl Y
    rw [← union_singleton, ← diff_diff, diff_subset_iff, singleton_union, ← insert_union,
      insert_diff_singleton, ← singleton_union, union_assoc, diff_union_self]
    exact subset_union_of_subset_right (subset_union_left _ _) _
  rw [← cl_subset_cl_iff_subset_cl] at h₃ 
  have h₄ := h₃ (hC.subset_cl_diff_singleton z hz.1)
  obtain hzY | ⟨C', hC', hzC', hCzY⟩ := mem_cl_iff_exists_circuit.mp h₄
  · exact ((hY.subset hzY).2 (mem_insert z _)).elim
  refine' ⟨C', hC', hzC', subset_diff.mpr ⟨_, _⟩⟩
  · exact hCzY.trans (insert_subset.mpr ⟨Or.inl hz.1, diff_subset _ _⟩)
  refine' disjoint_of_subset_left hCzY _
  rw [← singleton_union, disjoint_union_left, disjoint_singleton_left]
  refine' ⟨not_mem_subset _ hz.2, _⟩
  · rintro x' ⟨i, rfl⟩; exact mem_Union_of_mem i (h_mem i).2
  exact disjoint_of_subset_right (subset_insert z _) disjoint_sdiff_left
#align matroid_in.circuit.strong_multi_elimination MatroidIn.Circuit.strong_multi_elimination

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (C «expr ⊆ » «expr \ »(«expr ∪ »(C₁, C₂), {e})) -/
/-- The strong circuit elimination axiom. For any two circuits `C₁,C₂` and all `e ∈ C₁ ∩ C₂` and 
  `f ∈ C₁ \ C₂`, there is a circuit `C` with `f ∈ C ⊆ (C₁ ∪ C₂) \ {e}`. -/
theorem Circuit.strong_elimination (hC₁ : M.Circuit C₁) (hC₂ : M.Circuit C₂) (he : e ∈ C₁ ∩ C₂)
    (hf : f ∈ C₁ \ C₂) : ∃ (C : _) (_ : C ⊆ (C₁ ∪ C₂) \ {e}), M.Circuit C ∧ f ∈ C :=
  by
  obtain ⟨C, hC, hfC, hCss⟩ :=
    @circuit.strong_multi_elimination _ M C₁ Unit hC₁ (fun _ => e) (fun _ => C₂) (by simpa)
      (by simpa) (by simp) f (by simpa)
  simp only [range_const, Union_const] at hCss 
  exact ⟨C, hCss, hC, hfC⟩
#align matroid_in.circuit.strong_elimination MatroidIn.Circuit.strong_elimination

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (C «expr ⊆ » «expr \ »(«expr ∪ »(C₁, C₂), {e})) -/
/-- The circuit eliminiation axiom : for any pair of distinct circuits `C₁,C₂` and any `e`, some
  circuit is contained in `C₁ ∪ C₂ \ {e}`. Traditionally this is stated with the assumption that 
  `e ∈ C₁ ∩ C₂`, but it is also true without it. -/
theorem Circuit.elimination (hC₁ : M.Circuit C₁) (hC₂ : M.Circuit C₂) (h : C₁ ≠ C₂) (e : α) :
    ∃ (C : _) (_ : C ⊆ (C₁ ∪ C₂) \ {e}), M.Circuit C :=
  by
  by_contra' h'
  have he : e ∈ C₁ ∩ C₂ := by
    by_contra he
    refine' h' C₁ (by_contra fun h₁ => _) hC₁
    refine' h' C₂ (by_contra fun h₂ => he _) hC₂
    rw [subset_diff, not_and, disjoint_singleton_right, not_not_mem] at h₁ h₂ 
    exact ⟨h₁ (subset_union_left _ _), h₂ (subset_union_right _ _)⟩
  have hf : (C₁ \ C₂).Nonempty :=
    by
    rw [nonempty_iff_ne_empty, Ne.def, diff_eq_empty]
    refine' fun hss => h _
    exact hC₁.eq_of_subset_circuit hC₂ hss
  obtain ⟨f, hf⟩ := hf
  obtain ⟨C, hCss, hC, -⟩ := hC₁.strong_elimination hC₂ he hf
  exact h' C hCss hC
#align matroid_in.circuit.elimination MatroidIn.Circuit.elimination

theorem Circuit.eq_fundCircuit_of_subset_insert_indep (hC : M.Circuit C) (hI : M.indep I)
    (hCI : C ⊆ insert e I) : C = M.fundCircuit e I :=
  by
  by_cases heE : e ∈ M.E
  · by_contra' hne
    have he : e ∉ I := by
      intro heI; rw [insert_eq_of_mem heI] at hCI 
      exact hC.dep.not_indep (hI.subset hCI)
    have heI : e ∈ M.cl I \ I :=
      by
      rw [mem_diff, hI.mem_cl_iff_of_not_mem he, dep_iff_supset_circuit, and_iff_left he]
      exact ⟨C, hCI, hC⟩
    obtain ⟨C', hC'ss, hC'⟩ := hC.elimination (hI.fund_circuit_circuit heI) hne e
    refine' hC'.dep.not_indep (hI.subset (hC'ss.trans _))
    rw [diff_subset_iff, singleton_union]
    exact union_subset hCI (fund_circuit_subset_insert heI.1)
  refine' (hC.dep.not_indep (hI.subset fun x hxC => (hCI hxC).elim _ id)).elim
  rintro rfl
  exact (heE (hC.subset_ground hxC)).elim
#align matroid_in.circuit.eq_fund_circuit_of_subset_insert_indep MatroidIn.Circuit.eq_fundCircuit_of_subset_insert_indep

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (C «expr ⊆ » M₁.E) -/
theorem eq_of_circuit_iff_circuit_forall {M₁ M₂ : MatroidIn α} (hE : M₁.e = M₂.e)
    (h : ∀ (C) (_ : C ⊆ M₁.e), M₁.Circuit C ↔ M₂.Circuit C) : M₁ = M₂ :=
  by
  refine' eq_of_indep_iff_indep_forall hE fun I hI => _
  simp_rw [indep_iff_forall_subset_not_circuit', ← hE, and_iff_left hI]
  exact
    ⟨fun h' C hCI => by rw [← h _ (hCI.trans hI)]; exact h' _ hCI, fun h' C hCI => by
      rw [h _ (hCI.trans hI)]; exact h' _ hCI⟩
#align matroid_in.eq_of_circuit_iff_circuit_forall MatroidIn.eq_of_circuit_iff_circuit_forall

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (J «expr ⊆ » I) -/
theorem indep_iff_forall_finite_subset_indep [Finitary M] :
    M.indep I ↔ ∀ (J) (_ : J ⊆ I), J.Finite → M.indep J :=
  by
  refine' ⟨fun h J hJI hJ => h.Subset hJI, _⟩
  rw [indep_iff_forall_subset_not_circuit']
  exact fun h =>
    ⟨fun C hCI hC => hC.dep.not_indep (h _ hCI hC.Finite), fun e heI =>
      singleton_subset_iff.mp (h _ (singleton_subset_iff.mpr heI) (to_finite _)).subset_ground⟩
#align matroid_in.indep_iff_forall_finite_subset_indep MatroidIn.indep_iff_forall_finite_subset_indep

section Dual

/-- A cocircuit is the complement of a hyperplane -/
def Cocircuit (M : MatroidIn α) (K : Set α) : Prop :=
  M﹡.Circuit K
#align matroid_in.cocircuit MatroidIn.Cocircuit

@[simp]
theorem dual_circuit_iff_cocircuit {K : Set α} : M﹡.Circuit K ↔ M.Cocircuit K :=
  Iff.rfl
#align matroid_in.dual_circuit_iff_cocircuit MatroidIn.dual_circuit_iff_cocircuit

@[ssE_finish_rules]
theorem Cocircuit.subset_ground (hC : M.Cocircuit C) : C ⊆ M.e := by
  rw [← dual_circuit_iff_cocircuit] at hC ; rw [← dual_ground]; exact hC.subset_ground
#align matroid_in.cocircuit.subset_ground MatroidIn.Cocircuit.subset_ground

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (K «expr ⊆ » X) -/
theorem coindep_iff_forall_subset_not_cocircuit' :
    M.Coindep X ↔ (∀ (K) (_ : K ⊆ X), ¬M.Cocircuit K) ∧ X ⊆ M.e := by
  simp [← dual_indep_iff_coindep, indep_iff_forall_subset_not_circuit']
#align matroid_in.coindep_iff_forall_subset_not_cocircuit' MatroidIn.coindep_iff_forall_subset_not_cocircuit'

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (K «expr ⊆ » X) -/
theorem coindep_iff_forall_subset_not_cocircuit
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.Coindep X ↔ ∀ (K) (_ : K ⊆ X), ¬M.Cocircuit K := by
  rw [coindep_iff_forall_subset_not_cocircuit', and_iff_left hX]
#align matroid_in.coindep_iff_forall_subset_not_cocircuit MatroidIn.coindep_iff_forall_subset_not_cocircuit

theorem cocircuit_iff_mem_minimals {K : Set α} :
    M.Cocircuit K ↔ K ∈ minimals (· ⊆ ·) {X | ∀ B, M.base B → (X ∩ B).Nonempty} :=
  by
  simp_rw [cocircuit, circuit, mem_minimals_setOf_iff, dep_iff, dual_indep_iff_coindep, dual_ground,
    and_imp, coindep, not_and, not_exists, not_and, not_disjoint_iff_nonempty_inter, inter_comm K]
  constructor
  · rintro ⟨⟨h, hKE⟩, h'⟩; refine' ⟨h hKE, fun X hX hXK => h' (fun _ => hX) (hXK.trans hKE) hXK⟩
  rintro ⟨h1, h2⟩
  have hKE : K ⊆ M.E := by
    rw [← inter_eq_left_iff_subset, eq_comm]
    apply h2 (fun B hB => _) (inter_subset_left _ _)
    rw [inter_assoc, inter_eq_self_of_subset_right hB.subset_ground, inter_comm]
    exact h1 B hB
  exact ⟨⟨fun _ => h1, hKE⟩, fun X hX hXE hXK => h2 (hX hXE) hXK⟩
#align matroid_in.cocircuit_iff_mem_minimals MatroidIn.cocircuit_iff_mem_minimals

theorem cocircuit_iff_mem_minimals_compl_nonspanning {K : Set α} :
    M.Cocircuit K ↔ K ∈ minimals (· ⊆ ·) {X | ¬M.Spanning (M.e \ X)} :=
  by
  convert cocircuit_iff_mem_minimals
  ext X
  simp_rw [spanning_iff_supset_base, not_exists, not_and, subset_diff, not_and,
    not_disjoint_iff_nonempty_inter, ← and_imp, and_iff_left_of_imp base.subset_ground,
    inter_comm X]
#align matroid_in.cocircuit_iff_mem_minimals_compl_nonspanning MatroidIn.cocircuit_iff_mem_minimals_compl_nonspanning

theorem Cocircuit.finite [Finitary (M﹡)] {K : Set α} (hK : M.Cocircuit K) : K.Finite :=
  (dual_circuit_iff_cocircuit.mpr hK).Finite
#align matroid_in.cocircuit.finite MatroidIn.Cocircuit.finite

end Dual

section Girth

variable {k : ℕ}

-- Todo : `finitary` versions without finiteness in the statements
/-- The girth of a matroid_in is the size of its smallest finite circuit 
  (or zero if there is no finite circuit)-/
def girth (M : MatroidIn α) : ℕ :=
  sInf (ncard '' {C | M.Circuit C ∧ C.Finite})
#align matroid_in.girth MatroidIn.girth

theorem girth_eq_zero_iff : M.girth = 0 ↔ ∀ C, M.Circuit C → C.Infinite :=
  by
  simp_rw [girth, Nat.sInf_eq_zero, mem_image, mem_set_of_eq, image_eq_empty, Set.Infinite, ←
    not_nonempty_iff_eq_empty, imp_iff_or_not, ← imp_iff_or_not, nonempty_def, mem_set_of]
  rw [imp_iff_not]
  · simp
  simp only [not_exists, not_and, and_imp]
  intro C hC hCfin hc
  rw [ncard_eq_zero hCfin] at hc ; subst hc
  exact M.empty_not_circuit hC
#align matroid_in.girth_eq_zero_iff MatroidIn.girth_eq_zero_iff

theorem Circuit.girth_le (hC : M.Circuit C) (hCfin : C.Finite) : M.girth ≤ C.ncard :=
  Nat.sInf_le ⟨C, ⟨hC, hCfin⟩, rfl⟩
#align matroid_in.circuit.girth_le MatroidIn.Circuit.girth_le

theorem exists_circuit_girth (h : M.girth ≠ 0) : ∃ C, M.Circuit C ∧ C.Finite ∧ C.ncard = M.girth :=
  by
  simp_rw [Ne.def, girth_eq_zero_iff, not_forall, exists_prop, not_infinite] at h 
  obtain ⟨C, ⟨hC, hCfin⟩, hc⟩ :=
    Nat.sInf_mem (nonempty.image ncard (h : {C | M.circuit C ∧ C.Finite}.Nonempty))
  exact ⟨C, hC, hCfin, hc⟩
#align matroid_in.exists_circuit_girth MatroidIn.exists_circuit_girth

theorem girth_eq_iff (hk : k ≠ 0) :
    M.girth = k ↔
      (∀ C, M.Circuit C → C.Finite → k ≤ C.ncard) ∧ ∃ C, M.Circuit C ∧ C.Finite ∧ C.ncard = k :=
  by
  constructor
  · rintro rfl
    refine' ⟨fun C hC hCfin => hC.girth_le hCfin, (exists_circuit_girth hk).imp fun C => id⟩
  rintro ⟨h, C, ⟨hC, hCfin, rfl⟩⟩
  have hg : M.girth ≠ 0 :=
    by
    simp_rw [Ne.def, girth_eq_zero_iff, not_forall, exists_prop, not_infinite]
    exact ⟨C, hC, hCfin⟩
  obtain ⟨C', hC', hC'fin, hC'card⟩ := exists_circuit_girth hg
  rw [← hC'card, le_antisymm_iff, and_iff_left (h _ hC' hC'fin)]
  convert hC.girth_le hCfin
#align matroid_in.girth_eq_iff MatroidIn.girth_eq_iff

theorem girth_le_iff (h : M.girth ≠ 0) : M.girth ≤ k ↔ ∃ C, M.Circuit C ∧ C.Finite ∧ C.ncard ≤ k :=
  by
  obtain ⟨C, hC, hCfin, hCcard⟩ := exists_circuit_girth h
  refine' ⟨fun h => ⟨C, hC, hCfin, hCcard.trans_le h⟩, _⟩
  rintro ⟨C', hC', hC'fin, hC'card⟩
  exact (hC'.girth_le hC'fin).trans hC'card
#align matroid_in.girth_le_iff MatroidIn.girth_le_iff

theorem le_girth_iff (h : M.girth ≠ 0) : k ≤ M.girth ↔ ∀ C, M.Circuit C → C.Finite → k ≤ C.ncard :=
  by
  refine' ⟨fun h C hC hCfin => h.trans (hC.girth_le hCfin), fun h' => _⟩
  obtain ⟨C, hC, hCfin, hCc⟩ := exists_circuit_girth h
  exact (h' C hC hCfin).trans_eq hCc
#align matroid_in.le_girth_iff MatroidIn.le_girth_iff

end Girth

section BasisExchange

variable {B₁ B₂ I₁ I₂ : Set α}

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic matroid_in.ssE -/
theorem Indep.rev_exchange_indep_iff (hI : M.indep I) (he : e ∈ M.cl I \ I) (hf : f ∈ I) :
    M.indep (insert e I \ {f}) ↔ f ∈ M.fundCircuit e I :=
  by
  have heE : e ∈ M.E := (M.cl_subset_ground I) he.1
  have h' : insert e I \ {f} ⊆ M.E :=
    (diff_subset _ _).trans
      (by
        run_tac
          ssE)
  rw [← not_iff_not, not_indep_iff, dep_iff_supset_circuit]
  refine'
    ⟨_, fun h =>
      ⟨M.fund_circuit e I, subset_diff_singleton (fund_circuit_subset_insert he.1) h,
        hI.fund_circuit_circuit he⟩⟩
  rintro ⟨C, hCss, hC⟩ hf
  have := hC.eq_fund_circuit_of_subset_insert_indep hI (hCss.trans (diff_subset _ _))
  subst this
  exact (hCss hf).2 rfl
#align matroid_in.indep.rev_exchange_indep_iff MatroidIn.Indep.rev_exchange_indep_iff

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic matroid_in.ssE -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic matroid_in.ssE -/
/- Given two bases `B₁,B₂` of `M` and an element `e` of `B₁ \ B₂`, we can find an `f ∈ B₂ \ B₁`
  so that swapping `e` for `f` in yields bases in both `B₁` and `B₂`.  -/
theorem Base.strong_exchange (hB₁ : M.base B₁) (hB₂ : M.base B₂) (he : e ∈ B₁ \ B₂) :
    ∃ f ∈ B₂ \ B₁, M.base (insert e B₂ \ {f}) ∧ M.base (insert f B₁ \ {e}) :=
  by
  suffices ∃ f ∈ B₂ \ B₁, M.indep (insert e B₂ \ {f}) ∧ M.indep (insert f B₁ \ {e})
    by
    obtain ⟨f, hf, h₁, h₂⟩ := this
    exact
      ⟨f, hf, hB₂.exchange_base_of_indep' hf.1 he.2 h₁, hB₁.exchange_base_of_indep' he.1 hf.2 h₂⟩
  by_contra' h'
  have hecl : e ∈ M.cl B₂ \ B₂ := ⟨by rw [hB₂.cl]; exact hB₁.subset_ground he.1, he.2⟩
  set C := M.fund_circuit e B₂
  have hC : M.circuit C := indep.fund_circuit_circuit hB₂.indep hecl
  have h : C \ B₁ ⊆ M.cl (B₁ \ {e}) := by
    intro f hf
    have hne : f ≠ e := by rintro rfl; exact hf.2 he.1
    have hfB₂ : f ∈ B₂ := ((fund_circuit_subset_insert hecl.1) hf.1).elim (False.elim ∘ hne) id
    rw [mem_diff, ← hB₂.indep.rev_exchange_indep_iff hecl hfB₂] at hf 
    rw [(hB₁.indep.diff _).mem_cl_iff_of_not_mem (not_mem_subset (diff_subset _ _) hf.2),
      insert_diff_singleton_comm hne, ← not_indep_iff]
    --, and_iff_right (hB₂.subset_ground hfB₂)],
    · exact h' f ⟨hfB₂, hf.2⟩ hf.1
    exact
      (diff_subset _ _).trans
        (insert_subset.mpr
          ⟨by
            run_tac
              ssE,
            by
            run_tac
              ssE⟩)
  nth_rw 1 [← union_diff_cancel (singleton_subset_iff.mpr he.1)] at h 
  rw [diff_subset_iff, union_assoc, union_eq_self_of_subset_left (M.subset_cl (B₁ \ {e})), ←
    diff_subset_iff, ← cl_subset_cl_iff_subset_cl] at h 
  have heB₁ := (hC.subset_cl_diff_singleton e).trans h (mem_fund_circuit _ _ _)
  exact indep_iff_not_mem_cl_diff_forall.mp hB₁.indep e he.1 heB₁
#align matroid_in.base.strong_exchange MatroidIn.Base.strong_exchange

/- Given two bases `I₁,I₂` of `X` and an element `e` of `I₁ \ I₂`, we can find an `f ∈ I₂ \ I₁`
  so that swapping `e` for `f` in yields bases in both `I₁` and `I₂`.  -/
theorem Basis.strong_exchange (hI₁ : M.Basis I₁ X) (hI₂ : M.Basis I₂ X) (he : e ∈ I₁ \ I₂) :
    ∃ f ∈ I₂ \ I₁, M.Basis (insert e I₂ \ {f}) X ∧ M.Basis (insert f I₁ \ {e}) X := by
  convert hI₁.base_restrict.strong_exchange hI₂.base_restrict he; simp
#align matroid_in.basis.strong_exchange MatroidIn.Basis.strong_exchange

theorem Base.rev_exchange (hB₁ : M.base B₁) (hB₂ : M.base B₂) (he : e ∈ B₁ \ B₂) :
    ∃ f ∈ B₂ \ B₁, M.base (insert e B₂ \ {f}) :=
  (hB₁.strong_exchange hB₂ he).imp fun f ⟨hf, h, h'⟩ => ⟨hf, h⟩
#align matroid_in.base.rev_exchange MatroidIn.Base.rev_exchange

theorem Basis.rev_exchange (hI₁ : M.Basis I₁ X) (hI₂ : M.Basis I₂ X) (he : e ∈ I₁ \ I₂) :
    ∃ f ∈ I₂ \ I₁, M.Basis (insert e I₂ \ {f}) X :=
  (hI₁.strong_exchange hI₂ he).imp (by simp_rw [exists_prop]; tauto)
#align matroid_in.basis.rev_exchange MatroidIn.Basis.rev_exchange

end BasisExchange

-- section from_axioms TODO : Fix this for `matroid_in`.  
-- /-- A collection of sets satisfying the circuit axioms determines a matroid_in -/
-- def matroid_in_of_circuit_of_finite [finite E] (circuit : set α → Prop) 
-- (empty_not_circuit : ¬ circuit ∅) (antichain : ∀ C₁ C₂, circuit C₁ → circuit C₂ → C₁ ⊆ C₂ → C₁ = C₂)
-- (elimination : ∀ C₁ C₂ e,
--     circuit C₁ → circuit C₂ → C₁ ≠ C₂ → e ∈ C₁ ∩ C₂ → ∃ C ⊆ (C₁ ∪ C₂) \ {e}, circuit C) :
-- matroid_in α :=
-- matroid_in_of_indep_of_finite (λ I, ∀ C ⊆ I, ¬circuit C) ⟨∅, λ C hC, (by rwa subset_empty_iff.mp hC)⟩
-- (λ I J hIJ hJ C hCI, hIJ C (hCI.trans hJ))
-- begin
--   by_contra' h,
--   obtain ⟨I,J,hI,hJ,hIJ,Hbad⟩ := h,
--   set indep := (λ I, ∀ C ⊆ I, ¬circuit C) with hi,
--   /- Choose an independent set `K ⊆ I ∪ J`, larger than `I`, for which `I \ K` is minimized -/
--   set sbad := {K : set α | indep K ∧ K ⊆ I ∪ J ∧ I.ncard < K.ncard} with hsbad,
--   have hbad_ne : sbad.nonempty := ⟨J, hJ, subset_union_right _ _, hIJ⟩,
--   obtain ⟨K, ⟨hK, hKIJ, hIK⟩, hKmin⟩ :=
--     @set.finite.exists_minimal_wrt (set α) _ _ (λ X, (I \ X).ncard) sbad (to_finite sbad) hbad_ne,
--   simp only [hsbad, mem_set_of_eq, and_imp] at hKmin,
--   obtain hIK_empty | ⟨e, heI, heK⟩ := (I \ K).eq_empty_or_nonempty,
--   /- If `I \ K` is empty then we get an easy contradiction by augmenting `I` into `K`. -/
--   { obtain ⟨e,heK,heI⟩ := exists_mem_not_mem_of_ncard_lt_ncard hIK,
--     have heJ : e ∈ J := by_contra (λ heJ, not_or heI heJ (hKIJ heK)),
--     obtain ⟨C, hCeI, hC⟩ := Hbad e heJ heI,
--     exact hK C (hCeI.trans (insert_subset.mpr ⟨heK, diff_eq_empty.mp hIK_empty⟩)) hC},
--   have hCf : ∀ f ∈ K \ I, ∃ Cf ⊆ (insert e K), circuit Cf ∧ f ∉ Cf ∧ e ∈ Cf,
--   { rintro f ⟨hfK,hfI⟩,
--     have hef : e ≠ f, from λ h, hfI (h ▸heI ),
--     set T := ((insert e K) \ {f}) with hT,
--     have hTIJ : T ⊆ I ∪ J, from
--       ((diff_subset _ _).trans (insert_subset.mpr ⟨or.inl heI,hKIJ⟩)),
--     have hTcard : T.ncard = K.ncard, by rw [hT, ncard_exchange' heK hfK],
--     have hITcard : (I \ T).ncard < (I \ K).ncard,
--     { rw [nat.lt_iff_add_one_le, hT, ←insert_diff_singleton_comm hef, ←union_singleton, ←diff_diff,
--         ncard_diff_singleton_add_one ],
--       { convert rfl.le using 2,
--         rw [diff_eq_compl_inter, diff_eq_compl_inter, diff_eq_compl_inter, compl_inter,
--           inter_distrib_right, compl_compl, singleton_inter_eq_empty.mpr hfI, empty_union]},
--       exact ⟨heI,λ he', heK he'.1⟩},
--     have hTi : ¬indep T, from
--       λ hTi, hITcard.ne (hKmin _ hTi hTIJ (hIK.trans_eq hTcard.symm) hITcard.le).symm,
--     push_neg at hTi,
--     obtain ⟨Cf, hCfT, hCf⟩ := hTi,
--     refine ⟨Cf, hCfT.trans (diff_subset _ _), hCf, _, _⟩,
--     { exact mt (@hCfT f) (not_mem_diff_of_mem (mem_singleton f))},
--     refine by_contra (λ heCf, hK Cf (λ x hxCf, _) hCf),
--     exact mem_of_mem_insert_of_ne (hCfT hxCf).1 (by {rintro rfl, exact heCf hxCf})},
--   obtain ⟨g,hgK,hgI⟩ := exists_mem_not_mem_of_ncard_lt_ncard hIK,
--   obtain ⟨Cg, hCgss, hCg, hgCg, heCg⟩ := hCf g ⟨hgK,hgI⟩,
--   have hg_ex : ∃ g', g' ∈ Cg ∧ g' ∈ K \ I,
--   { by_contra' hg',
--     exact hI _ (λ x hx,
--       or.elim (hCgss hx) (λ h, h.symm ▸ heI) (λ hxK, by_contra (λ hxI, hg' _ hx ⟨hxK, hxI⟩))) hCg},
--   obtain ⟨g', hg', hg'KI⟩ := hg_ex,
--   obtain ⟨Cg', hCg'ss, hCg', hgCg', heCg'⟩ := hCf g' hg'KI,
--   have hne : Cg ≠ Cg',
--   { intro heq, rw ←heq at hgCg', exact hgCg' hg', },
--   obtain ⟨C, hCss, hC⟩ := elimination _ _ e hCg hCg' hne ⟨heCg, heCg'⟩,
--   refine hK C (hCss.trans _) hC,
--   rw [diff_subset_iff, singleton_union],
--   exact union_subset hCgss hCg'ss,
-- end
-- @[simp] lemma matroid_in_of_circuit_of_finite_apply [finite E] (circuit : set α → Prop)
--   (empty_not_circuit : ¬ circuit ∅)
--   (antichain : ∀ C₁ C₂, circuit C₁ → circuit C₂ → C₁ ⊆ C₂ → C₁ = C₂)
--   (elimination : ∀ C₁ C₂ e,
--     circuit C₁ → circuit C₂ → C₁ ≠ C₂ → e ∈ C₁ ∩ C₂ → ∃ C ⊆ (C₁ ∪ C₂) \ {e}, circuit C) :
--   (matroid_in_of_circuit_of_finite circuit empty_not_circuit antichain elimination).circuit = circuit :=
-- begin
--   ext C,
--   simp_rw [matroid_in_of_circuit_of_finite, matroid_in.circuit_iff_forall_ssubset,
--    matroid_in_of_indep_of_finite_apply, 
-- not_forall, not_not, exists_prop],
--   refine ⟨λ h, _,λ h, ⟨⟨_,rfl.subset, h⟩,λ I hIC C' hC'I hC',
--     hIC.not_subset ((antichain C' C hC' h (hC'I.trans hIC.subset)) ▸ hC'I )⟩⟩,
--   obtain ⟨⟨C₀,hC₀C, hC₀⟩,hI⟩ := h,
--   obtain rfl | hC₀C := eq_or_ssubset_of_subset hC₀C,
--     assumption,
--   exact (hI _ hC₀C _ rfl.subset hC₀).elim,
-- end
-- end from_axioms
end MatroidIn


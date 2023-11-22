import data.zmod.basic
import linear_algebra.basis
import linear_algebra.linear_independent
import m_in.minor m_in.constructions
import m_in.erank
import m_in.equiv
import .m_in_rep .rep_constructions
-- make new lean project, mwe for this theorem

-- intro should have section of formalization, history of formalization, context of lean & mathlib
-- four color theorem, liquid tensor experiment, goal for undergrad formalization
-- moving stuff from lean 3 to lean 4
-- matroids, representations, tutte's 1959 theorem
-- search up all matroid formalization attempts (michael stoll, brian chen)

-- ch 2 is design stuff

-- ch 3 is actual proof

universe u 
variables {α γ : Type} {β 𝔽 : Type*} {M : matroid_in α} {I B : set α} {x : α}
variables {W W' : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] [add_comm_group W'] [module 𝔽 W'] 

open function set submodule finite_dimensional

noncomputable theory

 
open_locale classical


-- we should have semiring 𝔽 by default, idk why it doesn't see it
-- why did we have finite E and not fintype E?

namespace matroid_in

namespace rep

variables [fintype α]

open_locale big_operators

lemma coindep_excluded_minor (M : matroid_in α) 
(hM : excluded_minor {N : matroid_in α | N.is_representable 𝔽} M) (x y : α) (hxy : x ≠ y) 
(hx : {x, y} ⊆ M.E) 
  : M.coindep {x, y} :=
begin
  by_contra,
  rw coindep_iff_forall_subset_not_cocircuit at h,
  push_neg at h,
  obtain ⟨K, hK1, hK2⟩ := h,
  have h2 := (dual_circuit_iff_cocircuit.2 hK2).nonempty,
  cases ssubset_or_eq_of_subset hK1 with hKs hKeq,
  obtain ⟨a, ⟨ha1, ha2⟩⟩ := ssubset_iff_subset_diff_singleton.1 hKs,
  obtain ⟨rfl | h2⟩ := (mem_insert_iff.1 ha1),
  -- duplicate code
  -- use add_coloop_rep,
  { simp only [insert_diff_of_mem, mem_singleton, diff_singleton_eq_self 
      (mem_singleton_iff.1.mt hxy), subset_singleton_iff_eq] at ha2,
    cases ha2 with hempty hs,
    { apply (nonempty_iff_ne_empty.1 h2) hempty },
    rw hs at *,
    rw [← ground_inter_left (subset_trans hK1 hx)] at h2,
    obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := hM.delete_mem h2,
    have hyMy : y ∉ (M ⟋ y).E,
      rw [contract_elem, contract_ground],
      apply not_mem_diff_of_mem (mem_singleton _),
    have φM := add_coloop_rep φ hyMy,
    simp only [excluded_minor, mem_minimals_prop_iff] at hM,
    apply hM.1,
    rw [contract_elem, contract_ground, ← delete_ground ] at hyMy,
    rw (add_coloop_eq (M ⟍ {y}) M hyMy).2 ⟨coloop_iff_cocircuit.2 hK2, delete_elem M y⟩,
    apply is_representable_of_rep φM, },
  { rw mem_singleton_iff.1 h at *,
    rw [← union_singleton, union_comm, union_singleton] at *,
    simp only [insert_diff_of_mem, mem_singleton, diff_singleton_eq_self 
      (mem_singleton_iff.1.mt (ne.symm hxy)), subset_singleton_iff_eq] at ha2,
    cases ha2 with hempty hs,
    { apply (nonempty_iff_ne_empty.1 h2) hempty },
    rw hs at *,
    rw [← ground_inter_left (subset_trans hK1 hx)] at h2,
    obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := hM.delete_mem h2,
    have hyMy : x ∉ (M ⟋ x).E,
      rw [contract_elem, contract_ground],
      apply not_mem_diff_of_mem (mem_singleton _),
    have φM := add_coloop_rep φ hyMy,
    simp only [excluded_minor, mem_minimals_prop_iff] at hM,
    apply hM.1,
    rw [contract_elem, contract_ground, ← delete_ground] at hyMy,
    rw (add_coloop_eq (M ⟍ {x}) M hyMy).2 ⟨coloop_iff_cocircuit.2 hK2, delete_elem M x⟩,
    apply is_representable_of_rep φM },
  rw hKeq at *,
  have hyy := singleton_nonempty y,
  rw ← ground_inter_left (insert_subset.1 hx).2 at hyy,
  --rw [ground_inter_left _] at hyy,
  have h3 := hM.contract_mem hyy,
  obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := h3,
  rw ← M.contract_elem y at φ, 
  have hxMy : x ∈ (M ⟋ y).E,
    rw [contract_elem, contract_ground],
    apply (mem_diff x).2,
    refine ⟨_, mem_singleton_iff.1.mt hxy⟩,
    apply mem_of_subset_of_mem hx,
    simp only [mem_insert_iff, eq_self_iff_true, true_or],
  have hyMy : y ∉ (M ⟋ y).E,
    rw [contract_elem, contract_ground],
    apply not_mem_diff_of_mem (mem_singleton _),
 --have hf := series_extend_eq (M ⟋ y) M hK2 hxMy rfl hyMy,
  simp only [excluded_minor, mem_minimals_prop_iff] at hM,
  apply hM.1,
  have hMx : ¬(M ⟋ y).coloop x,
    rw [contract_elem, coloop, contract_dual_eq_dual_delete, not_loop_iff, delete_nonloop_iff],
    rw [cocircuit, circuit_iff_dep_forall_diff_singleton_indep] at hK2,
    cases hK2 with hxy2 hin,
    specialize hin y (mem_insert_of_mem _ (mem_singleton y)),
    rw [insert_eq, union_comm, ← insert_eq, insert_diff_of_mem _ (mem_singleton _),
      diff_singleton_eq_self (mem_singleton_iff.1.mt (ne.symm hxy))] at hin,
    refine ⟨indep_singleton.1 hin, mem_singleton_iff.1.mt hxy⟩,
  rw [(eq_series_extend_iff hxMy hMx hyMy).2 ⟨hK2, rfl⟩, mem_set_of],
  obtain φM := series_extend_rep φ hxMy hyMy hMx,
  exact is_representable_of_rep φM, 
end

lemma excluded_minor_nonloop (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor matroid_in.is_binary M) {f : α} (hf : f ∈ M.E) : M.nonloop f :=
begin
  by_contra,
  have hfM : ({f} ∩ M.E).nonempty,
    simp only [ground_inter_left, singleton_nonempty],
  obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := hM.delete_mem hfM,
  rw [excluded_minor, mem_minimals_prop_iff] at hM,
  simp only [not_nonloop_iff] at h,
  apply hM.1,
  apply is_representable_of_rep (rep_of_loop M h φ),
end

lemma excluded_minor_nonpara (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor matroid_in.is_binary M) {x y : α} (hxy : x ≠ y) :
  ¬ M.circuit {x, y}  :=
begin
  by_contra,
  have hfM : ({y} ∩ M.E).nonempty,
    simp only [singleton_inter_nonempty],
    apply mem_of_subset_of_mem h.subset_ground,
    simp only [mem_insert_iff, mem_singleton, or_true],
  obtain  ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := hM.delete_mem hfM,
  rw [excluded_minor, mem_minimals_prop_iff] at hM,
  apply hM.1,
  have hx : (M ⟍ y).nonloop x,
    rw [delete_elem, delete_nonloop_iff],
    rw circuit_iff_dep_forall_diff_singleton_indep at h,
    cases h with hxy2 hin,
    specialize hin y (mem_insert_of_mem _ (mem_singleton y)),
    rw [insert_eq, union_comm, ← insert_eq, insert_diff_of_mem _ (mem_singleton _),
      diff_singleton_eq_self (mem_singleton_iff.1.mt (ne.symm hxy))] at hin,
    refine ⟨indep_singleton.1 hin, mem_singleton_iff.1.mt hxy⟩,
  have hy : y ∉ (M ⟍ y).E,
    rw [delete_elem, delete_ground],
    apply not_mem_diff_singleton,
  obtain φM := parallel_extend_rep φ hx hy,
  simp_rw ← delete_elem at φM,
  rw ← (eq_parallel_extend_iff hx hy).2 ⟨h, rfl⟩ at φM,
  apply is_representable_of_rep (rep_of_congr (rep_of_matroid_of_module_fun (zmod 2) (B →₀ zmod 2) 
    (λ (e : α), ite (e = y) (-φ x) (φ e)) (insert y (M ⟍ y).E)) φM),
  --rw parallel_extend_eq,
end

lemma excluded_minor_simple (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor matroid_in.is_binary M) : simple M :=
begin
  intros e he f hf, 
  rw indep_iff_forall_subset_not_circuit,
  intros C hC,
  by_cases hef : e = f,
  { rw hef at *,
    rw insert_eq_of_mem (mem_singleton f) at hC,
    cases ssubset_or_eq_of_subset hC with hempty heq,
    { rw ssubset_singleton_iff.1 hempty,
      apply empty_not_circuit },
    { rw heq,
      rw ← loop_iff_circuit,
      apply (excluded_minor_nonloop M hM hf).1 } },
  { cases ssubset_or_eq_of_subset hC with hC2 heq,
    { rw ssubset_iff_subset_diff_singleton at hC2,
      obtain ⟨x, ⟨hx1, hx2⟩⟩ := hC2,
      simp at hx1,
      obtain ⟨rfl | rfl⟩ := hx1,
      { simp at hx2,
        rw subset_diff at hx2,
        cases (subset_iff_ssubset_or_eq.1 hx2.1) with hempty heq,
        rw ssubset_singleton_iff.1 hempty,
        apply empty_not_circuit,
        rw heq,
        rw ← loop_iff_circuit,
        apply (excluded_minor_nonloop M hM hf).1 }, 
      { rw hx1 at *,
        rw [← union_singleton, union_comm, union_singleton] at hx2,
        simp at hx2,
        rw subset_diff at hx2,
        cases (subset_iff_ssubset_or_eq.1 hx2.1) with hempty heq,
        rw ssubset_singleton_iff.1 hempty,
        apply empty_not_circuit,
        rw [heq, ← loop_iff_circuit],
        apply (excluded_minor_nonloop M hM he).1 } },
    rw heq,
    apply excluded_minor_nonpara M hM hef },
  apply insert_subset.2 ⟨he, singleton_subset_iff.2 hf⟩,
end

-- should be an instance but i can't figure it out rn
lemma nontrivial_excluded_minor (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor matroid_in.is_binary M) : nontrivial M.E := 
begin
  by_contra,
  simp only [nontrivial_coe_sort, not_nontrivial_iff] at h,
  rw [excluded_minor, mem_minimals_prop_iff] at hM,
  apply hM.1,
  cases h.eq_empty_or_singleton with hempty hsing,
  { apply is_representable_of_rep (rep_empty (zmod 2) M hempty) },
  { obtain ⟨x, hx⟩ := hsing,
    apply is_representable_of_rep (rep_singleton (zmod 2) M hx) },
end

lemma excluded_minor_binary_unif (hM : excluded_minor matroid_in.is_binary M) 
  (ψ : M ≃i unif 2 M.E.ncard) (h2 : 2 ≤ M.E.ncard) : 4 ≤ M.E.ncard :=
begin
  rw [excluded_minor, mem_minimals_prop_iff] at hM,
  rw le_iff_eq_or_lt at h2,
  cases h2 with h2 h3,
  { by_contra,
    apply hM.1,
    rw ← h2 at ψ, 
    obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := U22_binary,
    apply is_representable_of_rep (iso.rep _ _ ψ φ) },
  { have h2 := nat.add_one_le_iff.2 h3,
    rw le_iff_eq_or_lt at h2,
    cases h2 with h2 h3,
    { by_contra, 
      apply hM.1,
      rw ← h2 at ψ, 
      obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := U23_binary,
      apply is_representable_of_rep (iso.rep _ _ ψ φ) },
    { apply nat.add_one_le_iff.2 h3 } },
end

lemma excluded_minor_binary_rk2 (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor (set_of matroid_in.is_binary) M) : M.rk = 2 :=
begin
  haveI hME := nontrivial_excluded_minor M hM,
  rw [nontrivial_coe_sort, nontrivial_iff_pair_subset] at hME,
  obtain ⟨x, ⟨y, ⟨hxy1, hxy2⟩⟩⟩ := hME,
  have h2 := coindep_excluded_minor M hM x y hxy1 hxy2,

  have hxyr : matroid_in.is_binary (M ⟍ ({x, y} : set α)),
    apply excluded_minor.delete_mem hM,
    rw ground_inter_left,
    apply insert_nonempty,

  obtain ⟨B, ⟨hBxy, ⟨φ⟩⟩⟩ := hxyr,

  obtain ⟨Bx, ⟨hBx, ⟨φx⟩⟩⟩ := (((excluded_minor_iff _ (@minor_closed_rep _ (zmod 2) _)).1 hM).2 x 
    (hxy2 (mem_union_left {y} (mem_singleton x)))).2,

  obtain ⟨By, ⟨hBy, ⟨φy⟩⟩⟩ := (((excluded_minor_iff _ (@minor_closed_rep _ (zmod 2) _)).1 hM).2 y 
    (hxy2 (mem_union_right {x} (mem_singleton y)))).2,
  
  have hB := coindep.base_of_basis_del h2 (delete_base_iff.1 hBxy),

  have hBy : (M ⟍ y).base B,
    rw [delete_elem, delete_base_iff],
    apply hB.basis_of_subset _,
    apply subset.trans,
    apply hBxy.subset_ground,
    rw [delete_ground, ← union_singleton, union_comm, ← diff_diff],
    apply diff_subset_diff_left (diff_subset _ _),
    apply diff_subset M.E ({y} : set α),
  
  have hBx : (M ⟍ x).base B,
    rw [delete_elem, delete_base_iff],
    apply hB.basis_of_subset _,
    apply subset.trans,
    apply hBxy.subset_ground,
    rw [delete_ground, ← union_singleton, ← diff_diff],
    apply diff_subset_diff_left (diff_subset _ _),
    apply diff_subset M.E ({x} : set α),
  
  have hMM'E : M.E = (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E).E,
    rw matroid_of_module_fun.ground,
  have hMM'x := delete_elem_eq_of_binary hBxy hBx hB φ φx,
  have hByx := hBxy,
  have hxyyx : M ⟍ {x, y} = M ⟍ {y, x},
    rw [← union_singleton, union_comm, union_singleton],
  rw [← union_singleton, union_comm, union_singleton] at hByx,
  have hMM'y := delete_elem_eq_of_binary hByx hBy hB (rep_of_congr φ hxyyx) φy,
  have hφ : ∀ (a : α), ((rep_of_congr φ hxyyx).standard_rep hByx) a = (φ.standard_rep hBxy) a,
  { intros a,
    rw φ.standard_rep_eq_of_congr hxyyx },
  simp_rw [λ (a : α), hφ a] at hMM'y,
  have hB' : (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E).base B,
  { rw hMM'x at hBx,
    rw hMM'y at hBy,
    rw [base_iff_basis_ground, ← @diff_empty _ (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E).E, 
      ← singleton_inter_eq_empty.2 (mem_singleton_iff.1.mt hxy1), diff_inter], 
    rw [delete_elem, delete_base_iff] at hBx hBy,
    apply basis.basis_union hBx hBy },
  have hMM'r : M.rk = (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E).rk,
  { rw [← hB'.card, hB.card] },
  have hnxy : ({x, y} : set α).ncard = 2,
    { rw ncard_eq_to_finset_card,
      simp only [finite.to_finset_insert, finite.to_finset_singleton],
      apply finset.card_insert_of_not_mem (finset.not_mem_singleton.2 hxy1) },
  have hMM' : M ≠ (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
    (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E),
    { by_contra,
      rw [excluded_minor, mem_minimals_prop_iff] at hM,
      apply hM.1,
      rw [h, mem_def],
      apply is_representable_of_rep (rep_of_matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
        (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E) },
    rw [ne.def, eq_iff_indep_iff_indep_forall, matroid_of_module_fun.ground] at hMM', 
    simp only [eq_self_iff_true, true_and, not_forall, exists_prop] at hMM',
    obtain ⟨Z, ⟨hZM, hZ⟩⟩ := hMM',
    rw [iff_def, not_and_distrib] at hZ,
    push_neg at hZ,
    cases hZ with hMZ hM'Z,
    { have hJZ : ∀ (J : set α), M.indep J → Z ⊆ J → J = {x, y}, 
      { intros J hMJ hZJ,
        -- duplicate code
        have hZx : x ∈ Z,
          { by_contra,
            have hZs : (M ⟍ x).indep Z,
            { rw [delete_elem, delete_indep_iff],
              refine ⟨hMZ.1, disjoint_singleton_right.2 h⟩ },
            rw [hMM'x, delete_elem] at hZs,
            apply hMZ.2 hZs.of_delete },
        have hZy : y ∈ Z,
          { by_contra,
            have hZs : (M ⟍ y).indep Z,
            { rw [delete_elem, delete_indep_iff],
              refine ⟨hMZ.1, disjoint_singleton_right.2 h⟩ },
            rw [hMM'y, delete_elem] at hZs,
            apply hMZ.2 hZs.of_delete },
        have hZxy := union_subset (singleton_subset_iff.2 hZy) (singleton_subset_iff.2 hZx),
        rw union_singleton at hZxy,
        by_contra,
        have hJxyM : ((J \ {x, y}) ∩ M.E).nonempty,
        { simp only [ground_inter_left],
          apply nonempty_iff_ne_empty.2,
          apply diff_eq_empty.1.mt, 
          by_contra h2,
          apply h (eq_of_subset_of_subset h2 (subset_trans hZxy hZJ)) },
        obtain ⟨BN, ⟨hBN, ⟨φN⟩⟩⟩ := hM.contract_mem hJxyM,
        have φN' := rep_of_contr _ (rep_of_matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
          (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E) (J \ {x, y})
          (by { rw matroid_of_module_fun.ground, apply subset_trans (diff_subset _ _) 
          hMJ.subset_ground }),
        apply h (indep_eq_doubleton_of_subset M (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
          (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E) hMM'r hMM'E 
          x y hxy1 (by { left, apply h2 }) hMM'x hMM'y hZx hZy hMZ.1 hMZ.2 hZJ hMJ φN φN') },
      obtain ⟨BZ, hBZ⟩ := hMZ.1,
      specialize hJZ BZ hBZ.1.indep hBZ.2,
      rw hJZ at *,
      rw [← hBZ.1.card, hnxy] },
  { have hJZ : ∀ (J : set α), (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E).indep J 
      → Z ⊆ J → J = {x, y}, 
    { intros J hMJ hZJ,
      have hZx : x ∈ Z,
        { by_contra,
        have hZs : ((matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
          (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, 
          (standard_rep φ hBxy) i) M.E) ⟍ x).indep Z,
        { rw [delete_elem, delete_indep_iff],
          refine ⟨hM'Z.1, disjoint_singleton_right.2 h⟩ },
        rw [← hMM'x, delete_elem] at hZs,
        apply hM'Z.2 hZs.of_delete },
      have hZy : y ∈ Z,
        { by_contra,
          have hZs : ((matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
            (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, 
            (standard_rep φ hBxy) i) M.E) ⟍ y).indep Z,
          { rw [delete_elem, delete_indep_iff],
            refine ⟨hM'Z.1, disjoint_singleton_right.2 h⟩ },
          rw [← hMM'y, delete_elem] at hZs,
          apply hM'Z.2 hZs.of_delete },
      have hZxy := union_subset (singleton_subset_iff.2 hZy) (singleton_subset_iff.2 hZx),
      rw union_singleton at hZxy,
      by_contra,
      have hJxyM' : ((J \ {x, y}) ∩ (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
            (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, 
            (standard_rep φ hBxy) i) M.E).E).nonempty,
      { simp only [ground_inter_left],
        apply nonempty_iff_ne_empty.2,
        apply diff_eq_empty.1.mt, 
        by_contra h2,
        apply h (eq_of_subset_of_subset h2 (subset_trans hZxy hZJ)) },
      obtain ⟨BN, ⟨hBN, ⟨φN⟩⟩⟩ := hM.contract_mem hJxyM',
      have φN' := rep_of_contr _ (rep_of_matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
        (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E) (J \ {x, y})
        (by { rw matroid_of_module_fun.ground, apply subset_trans (diff_subset _ _) 
        hMJ.subset_ground }),
      apply h (indep_eq_doubleton_of_subset (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
        (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E) M 
        (eq.symm hMM'r) (eq.symm hMM'E) x y hxy1 (by { right, apply h2 }) (eq.symm hMM'x)
        (eq.symm hMM'y) hZx hZy hM'Z.1 hM'Z.2 hZJ hMJ φN' φN) },
    obtain ⟨BZ, hBZ⟩ := hM'Z.1,
    specialize hJZ BZ hBZ.1.indep hBZ.2,
    rw hJZ at *,
    rw [hMM'r, ← hBZ.1.card, hnxy] },
end

lemma excluded_minor_binary_ncard (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor (set_of matroid_in.is_binary) M) : 2 ≤ M.E.ncard :=
by { rw [← excluded_minor_binary_rk2 M hM, rk_def], apply r_le_card }

lemma excluded_minor_binary (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor (set_of matroid_in.is_binary) M) : unif 2 4 ≤i M := 
begin
  obtain ⟨ψ⟩ := (iso_line_iff (excluded_minor_binary_ncard M hM)).2 ⟨excluded_minor_simple M hM,
    ⟨excluded_minor_binary_rk2 M hM, ⟨to_finite M.E, rfl⟩⟩⟩,
  apply iso_minor.trans (unif_iso_minor (excluded_minor_binary_unif hM ψ 
    (excluded_minor_binary_ncard M hM))) (ψ.symm.trans_iso_minor (minor.refl.iso_minor)),
end

lemma excluded_minor_binary_iso_unif (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor (set_of matroid_in.is_binary) M) : nonempty (M ≃i (unif 2 M.E.ncard)) := 
(iso_line_iff (excluded_minor_binary_ncard M hM)).2 ⟨excluded_minor_simple M hM,
⟨excluded_minor_binary_rk2 M hM, ⟨to_finite M.E, rfl⟩⟩⟩

lemma excluded_minor_binary_ncard4 (hM : excluded_minor matroid_in.is_binary M) : 4 = M.E.ncard :=
begin
  obtain ⟨ψ⟩ := excluded_minor_binary_iso_unif M hM,
  have h3 := excluded_minor_binary_unif hM ψ (excluded_minor_binary_ncard M hM),
  rw le_iff_eq_or_lt at h3,
  cases h3 with h3 h4,
  { apply h3 },
  { by_contra,
    obtain ⟨ψ2⟩ := (iso_line_iff (excluded_minor_binary_ncard M hM)).2 ⟨excluded_minor_simple M hM, ⟨excluded_minor_binary_rk2 M hM, 
      ⟨to_finite M.E, rfl⟩⟩⟩,
    have h4 := (excluded_minor_iff matroid_in.is_binary (@minor_closed_rep _ (zmod 2) _)).1 hM,
    have h5 := iso_minor.trans (@unif_iso_minor _ _ 2 (excluded_minor_binary_unif hM ψ2 
      (excluded_minor_binary_ncard M hM))) (ψ2.symm.iso_minor),
    rw iso_minor at h5,
    obtain ⟨M', ⟨hM'M, ⟨g⟩⟩⟩ := h5,
    have h8 := ncard_le_of_subset hM'M.ground_subset,
    rw le_iff_eq_or_lt at h8,
    cases h8 with hcontra hlt,
    { rw ncard_eq_to_finset_card M.E at hcontra,
      have h9 := (fintype.bijective_iff_injective_and_card ψ2).1 ψ2.bijective,
      apply h,
      rw [← to_finset_card, ← finite.to_finset_eq_to_finset, ← ncard_eq_to_finset_card M.E] at h9,
      rw h9.2,
      have h10 := (fintype.bijective_iff_injective_and_card g).1 g.bijective,
      rw [← to_finset_card M'.E, ← finite.to_finset_eq_to_finset, 
        ← ncard_eq_to_finset_card M'.E] at h10,
      rw [← ncard_eq_to_finset_card M.E] at hcontra,
      rw [← hcontra, ← h10.2, unif_ground_eq, ← to_finset_card univ, to_finset_univ, 
        finset.card_univ, fintype.card_fin, unif_ground_eq, ← to_finset_card univ, to_finset_univ, 
        finset.card_univ, fintype.card_fin] },
    { obtain ⟨e, ⟨heM, heM'⟩⟩ := exists_mem_not_mem_of_ncard_lt_ncard hlt, 
      have h7 := hM'M.minor_contract_or_minor_delete ((mem_diff e).2 ⟨heM, heM'⟩),
      apply U24_nonbinary,
      cases h7 with hMe hMe,
      { obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := is_rep_of_minor_of_is_rep _ hMe (h4.2 e heM).1,
        apply is_representable_of_rep (iso.rep _ _ g φ) },
      { obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := is_rep_of_minor_of_is_rep _ hMe (h4.2 e heM).2,
        apply is_representable_of_rep (iso.rep _ _ g φ) } } },
end

lemma excluded_minor_binary_iso_unif24 (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor (set_of matroid_in.is_binary) M) : nonempty (M ≃i (unif 2 4)) := 
by { rw excluded_minor_binary_ncard4 hM, apply excluded_minor_binary_iso_unif M hM }  

lemma U24_excluded_minor : excluded_minor (set_of matroid_in.is_binary) (unif 2 4) :=
begin
  rw excluded_minor_iff (set_of matroid_in.is_binary) (@minor_closed_rep _ (zmod 2) _),
  refine ⟨U24_nonbinary, _⟩,
  intros e he,
  refine ⟨_, _⟩,
  -- i have U1k representable and U23 representable, what's the best way to show this
  sorry,
  sorry
end

/-def excluded_minor_binary_unif24 (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor (set_of matroid_in.is_binary) M) : M ≃i (unif 2 4) := 
{ to_fun := sorry,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry,
  on_base' := sorry }-/

/-lemma binary_iff_no_24_minor (M : matroid_in α) [finite_rk M] : 
  matroid_in.is_binary M ↔ ¬ unif 2 4 ≤i M :=
begin
  rw matroid_in.is_binary,
  refine ⟨λ hfM, _, _⟩,
  by_contra,
  rw iso_minor at h,
  obtain ⟨M', ⟨hM'M, ⟨φ⟩⟩⟩ := h,
  apply (@mem_iff_no_excluded_minor_minor _ M _ (matroid_in.is_binary) 
    (@minor_closed_rep _ (zmod 2) _)).1 hfM M' _ hM'M,
  sorry,
  have h2 :=  (@mem_iff_no_excluded_minor_minor _ M _ (matroid_in.is_binary) 
    (@minor_closed_rep _ (zmod 2) _)).2,
  contrapose,
  intros hM,
  push_neg,
  sorry,
end-/

end rep

end matroid_in
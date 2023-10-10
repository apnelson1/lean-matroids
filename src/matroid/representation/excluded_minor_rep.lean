import analysis.inner_product_space.gram_schmidt_ortho
import data.zmod.basic
import linear_algebra.basis
import linear_algebra.linear_independent
import m_in.minor m_in.constructions
import m_in.erank
import m_in.equiv
import .m_in_rep .rep_m_constructions


universe u 
variables {α : Type} {β 𝔽 : Type*} {M : matroid_in α} {I B : set α} {x : α}
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
(hM : excluded_minor (λ (N : matroid_in α), N.is_representable 𝔽) M) (x y : α) (hxy : x ≠ y) 
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
    obtain ⟨W, h3⟩ := hM.delete_mem h2,
    casesI h3 with hW ha,
    casesI ha with hFW hb,
    casesI hb with φ,
    have hyMy : y ∉ (M ⟋ y).E,
      rw [contract_elem, contract_ground],
      apply not_mem_diff_of_mem (mem_singleton _),
    have φM := add_coloop_rep φ hyMy,
    simp only [excluded_minor, mem_minimals_prop_iff] at hM,
    apply hM.1,
    --obtain ⟨B, hB⟩ := (add_coloop (M ⟍ {y}) hyMy).exists_base,
    --refine ⟨(W × 𝔽 : Type*), _⟩,
    sorry,
    --use W × 𝔽,
    --obtain ⟨W, hW⟩ := φM,
    /-obtain ⟨B, hB⟩ := (M ⟍ ({y} : set α)).exists_base,
    rw ← delete_elem at *, 
    have hmem := (mem_diff x).2 ⟨(mem_of_subset_of_mem hx ha1), mem_singleton_iff.1.mt hxy⟩,
    rw [← @ground_inter_left _ (M.E \ {y}) _ (diff_subset _ _)] at hmem,
    obtain ⟨W', h3'⟩ := hM.delete_mem (nonempty_of_mem hmem),
    casesI h3' with hW' ha',
    casesI ha' with hFW' hb',
    casesI hb' with φy,
    rw ← restrict_ground_diff at φy,
    simp only [sdiff_sdiff_right_self, inf_eq_inter, ground_inter_right] at φy,
    have φM := rep_cocircuit_singleton y B φ φy hK2 hB,
    simp only [excluded_minor, mem_minimals_prop_iff] at hM,
    apply hM.1,
    refine ⟨W × W', ⟨by {apply_instance}, ⟨_, ⟨φM⟩⟩⟩⟩-/ },
  { rw mem_singleton_iff.1 h at *,
    rw [← union_singleton, union_comm, union_singleton] at *,
    simp only [insert_diff_of_mem, mem_singleton, diff_singleton_eq_self 
      (mem_singleton_iff.1.mt (ne.symm hxy)), subset_singleton_iff_eq] at ha2,
    cases ha2 with hempty hs,
    { apply (nonempty_iff_ne_empty.1 h2) hempty },
    rw hs at *,
    rw [← ground_inter_left (subset_trans hK1 hx)] at h2,
    obtain ⟨W, h3⟩ := hM.delete_mem h2,
    casesI h3 with hW ha,
    casesI ha with hFW hb,
    casesI hb with φ,
    obtain ⟨B, hB⟩ := (M ⟍ ({x} : set α)).exists_base,
    rw ← delete_elem at *, 
    have hmem := (mem_diff y).2 ⟨(mem_of_subset_of_mem hx ha1), mem_singleton_iff.1.mt 
      (ne.symm hxy)⟩,
    rw [← @ground_inter_left _ (M.E \ {x}) _ (diff_subset _ _)] at hmem,
    obtain ⟨W', h3'⟩ := hM.delete_mem (nonempty_of_mem hmem),
    casesI h3' with hW' ha',
    casesI ha' with hFW' hb',
    casesI hb' with φx,
    rw ← restrict_ground_diff at φx,
    simp only [sdiff_sdiff_right_self, inf_eq_inter, ground_inter_right] at φx,
    have φM := rep_cocircuit_singleton x B φ φx hK2 hB,
    simp only [excluded_minor, mem_minimals_prop_iff] at hM,
    apply hM.1,
    refine ⟨W × W', ⟨by {apply_instance}, ⟨_, ⟨φM⟩⟩⟩⟩ },
  have hyy : ({y} ∩ M.E).nonempty,
    sorry,
  --rw [ground_inter_left _] at hyy,
  have h3 := hM.contract_mem hyy,
  rw hKeq at *,
  obtain ⟨W, _⟩ := h3,
  casesI h3_h with hW ha,
  casesI ha with hFW hb,
  casesI hb with φ,
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
  rw series_extend_eq (M ⟋ y) M hK2 hxMy rfl hyMy,
  obtain φM := series_extend_rep φ hxMy hyMy,
  --refine ⟨W × 𝔽, ⟨by {apply_instance}, ⟨_, ⟨φM⟩⟩⟩⟩,
  --obtain ⟨B, hB⟩ := (M ⟍ K).exists_base,
  --have hrep := rep_cocircuit_doubleton x y hxy,
  /-
  have f := λ a : α, if a = x then (⟨0, 1⟩ : W × 𝔽) else ⟨φ a, 0⟩,
  have h1 : add_comm_group W × 𝔽,
    sorry,  
  have h2 : module 𝔽 (W × 𝔽), 
    sorry,
  have h3 : M.is_representable 𝔽,
  rw is_representable,
  have h4 : rep 𝔽 (W × 𝔽) M,
  -/
  sorry,
end

lemma excluded_minor_nonloop (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor matroid_in.is_binary M) {f : α} (hf : f ∈ M.E) : M.nonloop f :=
begin
  by_contra,
  have hfM : ({f} ∩ M.E).nonempty,
    simp only [ground_inter_left, singleton_nonempty],
  obtain ⟨W, hW⟩ := hM.delete_mem hfM,
  casesI hW with hW hFW,
  casesI hFW with hFW h,
  casesI h with φ,
  rw [excluded_minor, mem_minimals_prop_iff] at hM,
  simp only [not_nonloop_iff] at h,
  apply hM.1,
  refine ⟨W, ⟨by { apply_instance }, ⟨by { apply_instance }, ⟨rep_of_loop M h φ⟩⟩⟩⟩,
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
  obtain ⟨W, hW⟩ := hM.delete_mem hfM,
  casesI hW with hW hFW,
  casesI hFW with hFW h,
  casesI h with φ,
  rw [excluded_minor, mem_minimals_prop_iff] at hM,
  apply hM.1,
  refine ⟨W, ⟨by { apply_instance }, ⟨by { apply_instance }, ⟨rep_of_parallel M hxy h φ⟩⟩⟩⟩,
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
    { refine ⟨(zmod 2), ⟨by { apply_instance}, ⟨by { apply_instance}, 
        ⟨rep_empty (zmod 2) M hempty⟩⟩⟩⟩ },
    { obtain ⟨x, hx⟩ := hsing,
      refine ⟨(zmod 2), ⟨by { apply_instance}, ⟨by { apply_instance}, 
        ⟨rep_singleton (zmod 2) M hx⟩⟩⟩⟩ },
end

lemma excluded_minor_binary_unif (hM : excluded_minor matroid_in.is_binary M) 
  (ψ : M ≃i unif 2 M.E.ncard) (h2 : 2 ≤ M.E.ncard) : 4 ≤ M.E.ncard :=
begin
 -- rw le_iff_eq_or_lt at h2,
  sorry,
end

lemma excluded_minor_binary_unif24 (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor matroid_in.is_binary M) : iso_minor (unif 2 4) M :=
begin
  haveI hME := nontrivial_excluded_minor M hM,
  rw [nontrivial_coe_sort, nontrivial_iff_pair_subset] at hME,
  obtain ⟨x, ⟨y, ⟨hxy1, hxy2⟩⟩⟩ := hME,
  have h2 := coindep_excluded_minor M hM x y hxy1 hxy2,
  have hxyr : matroid_in.is_binary (M ⟍ ({x, y} : set α)),
    sorry,
  obtain ⟨W, _⟩ := hxyr,
  casesI hxyr_h with hW ha,
  casesI ha with hFW hb,
  casesI hb with φ,
  obtain ⟨B, hBxy⟩ := (M ⟍ ({x, y} : set α)).exists_base,

  obtain ⟨Wx, _⟩ := (((excluded_minor_iff _).1 hM).2 x (hxy2 (mem_union_left {y} (mem_singleton x)))).2,
  casesI h with hWx ha,
  casesI ha with hFWx hb,
  casesI hb with φx,

  obtain ⟨Wy, _⟩ := (((excluded_minor_iff _).1 hM).2 y (hxy2 (mem_union_right {x} (mem_singleton y)))).2,
  casesI h with hWy ha,
  casesI ha with hFWy hb,
  casesI hb with φy,
  
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
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (std_rep φ hBxy) i) M.E).E,
    rw matroid_of_module_fun.ground,
  have hMM'x := delete_elem_eq_of_binary hBxy hBx hB φ φx,
  have hByx := hBxy,
  have hxyyx : M ⟍ {x, y} = M ⟍ {y, x},
    rw [← union_singleton, union_comm, union_singleton],
  rw [← union_singleton, union_comm, union_singleton] at hByx,
  have hMM'y := delete_elem_eq_of_binary hByx hBy hB (rep_of_congr φ hxyyx) φy,
  have hφ : ∀ (a : α), ((rep_of_congr φ hxyyx).std_rep hByx) a = (φ.std_rep hBxy) a,
  { intros a,
    rw φ.std_rep_eq_of_congr hxyyx },
  simp_rw [λ (a : α), hφ a] at hMM'y,
  have hB' : (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (std_rep φ hBxy) i) M.E).base B,
    { rw hMM'x at hBx,
      rw hMM'y at hBy,
      rw [base_iff_basis_ground, ← @diff_empty _ (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
        (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (std_rep φ hBxy) i) M.E).E, 
        ← singleton_inter_eq_empty.2 (mem_singleton_iff.1.mt hxy1), diff_inter], 
      rw [delete_elem, delete_base_iff] at hBx hBy,
      apply basis.basis_union hBx hBy },
  have hMM'r : M.rk = (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (std_rep φ hBxy) i) M.E).rk,
    { rw [← hB'.card, hB.card] },
    have hMM' : M ≠ (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (std_rep φ hBxy) i) M.E),
    { by_contra,
      rw [excluded_minor, mem_minimals_prop_iff] at hM,
      apply hM.1,
      rw [h, mem_def, matroid_in.is_binary, is_representable],
      refine ⟨B →₀ zmod 2, ⟨_, ⟨_, ⟨(rep_of_matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
        (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (std_rep φ hBxy) i) M.E)⟩⟩⟩⟩ },
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
        casesI hM.contract_mem hJxyM with W hW,
        casesI hW with hW hFW,
        casesI hFW with hFW hN,
        casesI hN with φN,
        have φN' := rep_of_contr _ (rep_of_matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
          (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (std_rep φ hBxy) i) M.E) (J \ {x, y})
          (by { rw matroid_of_module_fun.ground, apply subset_trans (diff_subset _ _) hMJ.subset_ground }),
        apply h (indep_eq_doubleton_of_subset M (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
          (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (std_rep φ hBxy) i) M.E) hMM'r hMM'E 
          x y hxy1 (by { left, apply h2 }) hMM'x hMM'y hZx hZy hMZ.1 hMZ.2 hZJ hMJ φN φN') },
        have hnxy : ({x, y} : set α).ncard = 2,
        { rw ncard_eq_to_finset_card,
          simp only [finite.to_finset_insert, finite.to_finset_singleton],
          apply finset.card_insert_of_not_mem (finset.not_mem_singleton.2 hxy1) },
        { obtain ⟨BZ, hBZ⟩ := hMZ.1,
          specialize hJZ BZ hBZ.1.indep hBZ.2,
          rw hJZ at *,
          have hcard : 2 ≤ M.E.ncard,
            rw ← hnxy,
            apply ncard_le_of_subset hxy2, 
          obtain ⟨ψ⟩ := (iso_line_iff hcard).2 ⟨excluded_minor_simple M hM, _⟩,
          have hcard4 := excluded_minor_binary_unif hM ψ hcard,
          -- need unif_iso_minor lemma to finish this
          have hψ := ψ.symm.trans_iso_minor (minor.refl.iso_minor),
          sorry,
          rw [← hBZ.1.card, hnxy],
          refine ⟨rfl, ⟨_, rfl⟩⟩,
          sorry }, },
      { have hJZ : ∀ (J : set α), (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
          (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (std_rep φ hBxy) i) M.E).indep J 
          → Z ⊆ J → J = {x, y}, 
        { intros J hMJ hZJ,
          sorry },
        sorry },
end

end rep

end matroid_in
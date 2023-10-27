import analysis.inner_product_space.gram_schmidt_ortho
import data.zmod.basic data.finsupp.fintype
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

variables

variables [fintype α]


open_locale big_operators


def parallel_extend_rep (φ : rep 𝔽 W M) {x y : α} (hx : x ∈ M.E)
  (hy : y ∉ M.E) (hMx : ¬ M.loop x) : rep 𝔽 W (parallel_extend M hx hy hMx) := 
{ to_fun := λ (e : α), 
    if e = y then φ x else φ e,
  valid' := λ I hI, 
    begin
      refine ⟨_, λ h2, _⟩,
      { contrapose,
      intros h2,
      rw linear_dependent_comp_subtype',
      rw not_indep_iff at h2,
      obtain ⟨C, ⟨hCI, hCcct⟩⟩ := exists_circuit_subset_of_dep h2,
      by_cases hyC : y ∈ C, 
      { by_cases hxC : x ∈ C,
        { have h4 := parallel_extend_circuit M hx hMx hy,
          have h5 := hCcct.eq_of_dep_subset (parallel_extend_circuit M hx hMx hy).dep 
            (insert_subset.2 ⟨hxC, singleton_subset_iff.2 hyC⟩),
          refine ⟨(⟨{x, y}, (λ e : α, if e = y then - 1 else (if e = x then 1 else 0)), λ a, 
            ⟨λ ha, _, λ ha, _⟩⟩ : α →₀ 𝔽), _⟩,
          sorry,
          sorry,
          sorry },
        { obtain ⟨C2, ⟨hC2, ⟨hC3, hC4⟩⟩⟩ := (parallel_extend_circuit M hx hMx hy).strong_elimination hCcct 
            (mem_inter (mem_insert_of_mem x (mem_singleton y)) hyC) 
            (mem_diff_of_mem (mem_insert x {y}) hxC),
          have hC2y : disjoint C2 {y},
            sorry,
          have h2 := delete_circuit_iff.2 ⟨hC3, hC2y⟩,
          rw ← delete_elem at h2,
          rw [← parallel_extend_delete_eq] at h2,
          obtain ⟨f, ⟨rfl, ⟨hftot, hfne0⟩⟩⟩ := rep.circuit φ h2,
          refine ⟨(⟨(insert y (f.support \ {x})), (λ e : α, if e = x then 0 else 
            (if e = y then f x else f e)), λ a, ⟨λ ha, _, λ ha, _⟩⟩ : α →₀ 𝔽), _⟩,
          rw if_neg,
          rw finset.mem_insert at ha,
          cases ha with hay ha,
          { rw if_pos hay,
            apply finsupp.mem_support_iff.1 hC4 },
          { rw if_neg,
            apply finsupp.mem_support_iff.1 (finset.mem_sdiff.1 ha).1,
            apply ne_of_mem_of_not_mem (finset.mem_sdiff.1 ha).1,
            apply not_mem_subset hC2 (not_mem_diff_of_mem (mem_singleton y)) },
          --have hf := finsupp.mem_support_iff,
          --obtain ⟨f, ⟨hC, ⟨hftot, hfne0⟩⟩⟩ := rep.circuit φ hC3.1,
          sorry,
          sorry,
          refine ⟨_, ⟨_, _⟩⟩,
          { rw finsupp.mem_supported,
            simp only [finset.coe_insert],
            apply insert_subset.2 ⟨mem_of_subset_of_mem hCI hyC, _⟩,
            simp only [finset.coe_sdiff, finset.coe_singleton, diff_singleton_subset_iff],
            sorry },
          { dsimp [finsupp.total_apply, finsupp.sum],
            dsimp [finsupp.total_apply, finsupp.sum] at hftot,
            simp only [← ite_apply],
            simp_rw [ite_smul, zero_smul],
            rw [finset.sum_ite_of_false _ _ _],
            sorry,
            --simp only [prod.ext_iff],
            sorry },
          sorry },
        /-have hyC := (series_pair_mem_circuit _ _ _ hCcct 
          (parallel_extend_circuit M hx hMx hy)).1 hxC,
        rw [← @union_diff_cancel _ {y} C (singleton_subset_iff.2 hyC), union_comm, 
          union_singleton] at hCcct,
        have hMcct := contract_circuit_of_insert_circuit y (C \ {y}) hyindep 
          (not_mem_diff_singleton _ _) hCcct,
        rw [← parallel_extend_contr_eq] at hMcct,
        obtain ⟨f, ⟨hC, ⟨hftot, hfne0⟩⟩⟩ := rep.circuit φ hMcct,
        rw ← hC at hCcct hMcct,
        refine ⟨(⟨(insert y f.support), (λ e : α, if e = y then - f x else f e), λ a, 
          ⟨λ ha, _, λ ha, _⟩⟩ : α →₀ 𝔽), _⟩,
        { obtain ⟨rfl | ha⟩ := finset.mem_insert.1 ha,
          { simp only [eq_self_iff_true, if_true, ne.def, neg_eq_zero],
            rw [← ne.def, ← finsupp.mem_support_iff, ← finset.mem_coe, hC],
            apply mem_diff_of_mem hxC (mem_singleton_iff.1.mt (ne_of_mem_of_not_mem hx hy)) },
          { rw if_neg (ne_of_mem_of_not_mem (finset.mem_coe.2 h) 
              (not_mem_subset (subset_of_eq hC) (not_mem_diff_singleton _ _))),
            apply finsupp.mem_support_iff.1 h } },
        { apply finset.mem_insert.2,
          by_cases hay : a = y,
          { apply or.intro_left _ hay },
          { rw if_neg hay at ha,
            apply or.intro_right _ (finsupp.mem_support_iff.2 ha) } },
        refine ⟨_, ⟨_, _⟩⟩,
        { rw finsupp.mem_supported,
          simp only [finset.coe_insert, hC],
          apply insert_subset.2 ⟨mem_of_subset_of_mem hCI hyC, subset_trans (diff_subset _ _) hCI⟩},
        { simp_rw finset.insert_eq y f.support,
          dsimp [finsupp.total_apply, finsupp.sum],
          dsimp [finsupp.total_apply, finsupp.sum] at hftot,
          simp only [← ite_apply],
          simp_rw [ite_smul, smul_ite],
          simp only [prod.ext_iff, prod.smul_mk, zero_add, add_zero, algebra.id.smul_eq_mul, 
            mul_one, smul_zero],
          rw [finset.sum_union, ← @finset.sdiff_union_of_subset _ _ ({x} : finset α) f.support _, 
            finset.sum_union, finset.sum_singleton],
          simp only [if_pos rfl, if_neg (ne_of_mem_of_not_mem hx hy), 
            if_neg (ne.symm (ne_of_mem_of_not_mem hx hy)), ← prod_mk_sum],
          have hx2 : ∀ (e : α), e ∈ ({x} : finset α) → e ≠ y,
            intros e he,
            rw [finset.mem_singleton.1 he],
            apply ne_of_mem_of_not_mem hx hy,
          have hx3 : ∀ (e : α), e ∈ ({x} : finset α) → e = x,
            intros e he,
            rw [finset.mem_singleton.1 he],
          
          rw [finset.sum_ite_of_false _ _ hx2, finset.sum_ite_of_true _ _ hx3],
          simp only [neg_smul, eq_self_iff_true, if_true, pi.add_apply, 
            prod.mk_add_mk, add_zero, zero_add, prod.smul_mk, algebra.id.smul_eq_mul, mul_one, 
            prod.neg_mk],
          
          simp only [prod.fst_add, zero_add, prod.fst_zero, prod.snd_add, prod.snd_zero],
          rw [finset.sum_ite_of_false _ _ (λ e he, _), finset.sum_ite_of_false _ _ (λ e he, _)],
          simp only [finset.sum_ite_of_false _ _ (λ e he, _), ← prod_mk_sum], 
          rw finset.sum_ite_of_false _ _ (λ e he, _),
          rw [← prod_mk_sum, finset.sum_const_zero, zero_add],
          simp only,
          rw ← finset.sum_union, --(finset.sdiff_disjoint), 
          simp only [finset.sdiff_union_self_eq_union, finset.sum_singleton, add_left_neg, 
            eq_self_iff_true, and_true],
          rw [finset.union_comm, ← finset.insert_eq, finset.insert_eq_of_mem],
          apply hftot,
          rw [← finset.mem_coe, hC],
          apply mem_diff_singleton.2 ⟨hxC, ne_of_mem_of_not_mem hx hy⟩,
          simp only [finset.disjoint_singleton_right, finset.mem_sdiff, finset.mem_singleton, 
            eq_self_iff_true, not_true, and_false, not_false_iff], -- avoiding decidable_eq instance
          rw [← finset.mem_coe, finset.coe_sdiff, hC, mem_diff, mem_diff] at he,
          apply mem_singleton_iff.2.mt he.1.2,
          rw [finset.mem_sdiff, finset.mem_singleton] at he,
          apply he.2,
          rw [← finset.mem_coe, finset.coe_sdiff, hC, mem_diff, mem_diff] at he,
          apply mem_singleton_iff.2.mt he.1.2,
          simp only [finset.disjoint_singleton_right, finset.mem_sdiff, finset.mem_singleton, 
            eq_self_iff_true, not_true, and_false, not_false_iff],
          rw [finset.singleton_subset_iff, ← finset.mem_coe, hC],
          apply mem_diff_singleton.2 ⟨hxC, ne_of_mem_of_not_mem hx hy⟩,
          rw [← finset.disjoint_coe, hC],
          simp only [finset.coe_singleton, disjoint_singleton_left, not_mem_diff_singleton, 
            not_false_iff] },
        rw ne.def,
        rw finsupp.ext_iff,
        push_neg,
        use x,
        simp only [ne.def, finsupp.coe_mk, finsupp.coe_zero, pi.zero_apply],
        rw if_neg (ne_of_mem_of_not_mem hx hy),
        apply finsupp.mem_support_iff.1,
        rw [← finset.mem_coe, hC],
        apply mem_diff_singleton.2 ⟨hxC, ne_of_mem_of_not_mem hx hy⟩-/ },
      { /-have hyC := (series_pair_mem_circuit _ _ _ hCcct 
          (parallel_extend_circuit M hx hMx hy)).2.mt hxC,
        have h4 := (@indep.of_contract _ _ {y} _).mt (not_indep_iff.2 hCcct.dep),
        rw [← contract_elem, ← parallel_extend_contr_eq, ← φ.valid, 
          linear_dependent_comp_subtype'] at h4, 
        obtain ⟨f, ⟨hC, ⟨hftot, hfne0⟩⟩⟩ := h4,
        refine ⟨f, ⟨subset_trans hC hCI, ⟨_, hfne0⟩⟩⟩,
        dsimp [finsupp.total_apply, finsupp.sum],
        dsimp [finsupp.total_apply, finsupp.sum] at hftot,
        simp_rw smul_ite,
        rw [finset.sum_ite_of_false _ _ (λ e he, _), 
          finset.sum_ite_of_false _ _ (λ e he, _)],
        simp only [prod.smul_mk, algebra.id.smul_eq_mul, mul_zero, ← prod_mk_sum, hftot, 
          finset.sum_const_zero, prod.mk_eq_zero, eq_self_iff_true, and_self],
        { apply ne_of_mem_of_not_mem (finset.mem_coe.2 he) 
            (not_mem_subset ((f.mem_supported _).1 hC) hyC) },
        { apply ne_of_mem_of_not_mem (finset.mem_coe.2 he) 
            (not_mem_subset ((f.mem_supported _).1 hC) hxC) },
        apply (subset_insert_iff_of_not_mem hyC).1 hCcct.subset_ground } },
      { simp_rw [linear_independent_comp_subtype, finsupp.total_apply, smul_ite],
        dsimp [finsupp.sum],
        simp only [add_zero, zero_add, mul_one, smul_zero, mul_zero, finset.sum_ite, prod.ext_iff,
          finset.filter_congr_decidable, prod.fst_add, prod.fst_zero, prod.snd_add, 
          prod.snd_zero, finset.filter_eq', finset.filter_ne', ← prod_mk_sum, 
          finset.sum_const_zero, zero_add, add_zero],
        intros l hl hl0,
        by_cases hyI : (parallel_extend M hx hy hMx).indep ({y} ∪ I : set α),
        { have hyI2 := (hyI.subset (subset_union_left _ _)).union_indep_iff_contract_indep.1 hyI,
          rw [← contract_elem, ← parallel_extend_contr_eq, ← φ.valid, 
            linear_independent_comp_subtype] at hyI2,
          simp_rw [finsupp.total_apply] at hyI2,
          have hxl : x ∉ l.support,
          { by_contra hxl,
            rw [if_pos hxl] at hl0,
            specialize hyI2 (l.filter (≠ y)) _ _,
            { rw [finsupp.mem_supported, finsupp.support_filter, finset.filter_ne', 
                finset.coe_erase],
              apply diff_subset_diff_left ((l.mem_supported _).1 hl) },
            { rw [finsupp.sum_filter_index, finsupp.support_filter, finset.filter_ne',
                finset.sum_eq_add_sum_diff_singleton (finset.mem_erase.2 
                ⟨ne_of_mem_of_not_mem hx hy, hxl⟩), ← finset.erase_eq],
              rw [finset.erase_right_comm, finset.sum_singleton] at hl0,
              apply hl0.1 },
            apply finsupp.mem_support_iff.1 hxl,
            rw [← l.filter_apply_pos (≠ y) (ne_of_mem_of_not_mem hx hy), hyI2], 
            simp only [finsupp.coe_zero, pi.zero_apply] },
          simp only [if_neg hxl, finset.sum_empty, zero_add] at hl0,
          have hyl : y ∉ l.support,
          { by_contra hyl,
            rw [if_pos (finset.mem_erase.2 ⟨ne.symm (ne_of_mem_of_not_mem hx hy), hyl⟩), 
              finset.sum_singleton] at hl0,
             apply finsupp.mem_support_iff.1 hyl,
             apply hl0.2 },
          specialize hyI2 l _ _,
          { rw [finsupp.mem_supported],
            apply subset_diff_singleton ((l.mem_supported 𝔽).2 hl) hyl },
          { dsimp [finsupp.sum],
            rw [finset.erase_eq_of_not_mem hxl, finset.erase_eq_of_not_mem hyl] at hl0,
            apply hl0.1 },
          apply hyI2,
          apply hyI2.subset_ground },
      { have hyl : y ∉ l.support,
        { by_contra,
          rw [singleton_union, insert_eq_of_mem (mem_of_subset_of_mem 
            ((l.mem_supported _).1 hl) h)] at hyI,
          apply hyI h2 },
        rw [if_neg (finset.mem_erase.1.mt (not_and_distrib.2 (or.intro_right _ hyl))), 
          finset.sum_empty, add_zero] at hl0,
        have hxl : x ∉ l.support,
        { by_contra hxl,
          simp only [if_pos hxl, finset.sum_singleton] at hl0,
          apply finsupp.mem_support_iff.1 hxl,
          apply hl0.2 },
        rw [if_neg hxl, finset.sum_empty, zero_add] at hl0,
        rw not_indep_iff _ at hyI,
        have hIxy : (parallel_extend M hx hy hMx).indep ({y} ∪ (I \ {x}) : set α),  
        { by_contra hIyxn, 
          obtain ⟨C, ⟨hC, hC2⟩⟩ := exists_circuit_subset_of_dep ((not_indep_iff _).1 hIyxn),
          have hyC : y ∈ C,
          { by_contra hyC,
            rw [singleton_union, subset_insert_iff_of_not_mem hyC] at hC,
            apply hC2.dep.not_indep (h2.subset (subset_trans hC (diff_subset _ _))) },
          rw ← series_pair_mem_circuit _ _ _ hC2 (parallel_extend_circuit M hx hMx hy) at hyC,
          apply (not_mem_subset hC ((mem_union _ _ _).1.mt 
            (not_or_distrib.2 ⟨mem_singleton_iff.1.mt (ne_of_mem_of_not_mem hx hy), 
            not_mem_diff_singleton _ _⟩))) hyC,
          apply subset_trans (union_subset_union_right _ (diff_subset I {x})) hyI.subset_ground },
        have hyx := (hIxy.subset (subset_union_left _ _)).union_indep_iff_contract_indep.1 hIxy,
        rw [← contract_elem, ← parallel_extend_contr_eq, ← φ.valid, 
          linear_independent_comp_subtype] at hyx,
        rw [finset.erase_eq_of_not_mem hxl, finset.erase_eq_of_not_mem hyl] at hl0,
        apply hyx l ((l.mem_supported _).2 
          (subset_diff_singleton (subset_diff_singleton ((l.mem_supported _).1 hl) hxl) hyl)) hl0.1,
      apply hyx.subset_ground,
      simp only [singleton_union, auto_param_eq],
      apply insert_subset.2 ⟨mem_insert _ _, hI⟩ -/ 
      sorry } }, 
      { 
        sorry },
    end,
  support := λ e he, sorry }

end rep

end matroid_in
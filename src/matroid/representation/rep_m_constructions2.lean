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


def series_extend_rep (φ : rep 𝔽 W M) {x y : α} (hx : x ∈ M.E)
  (hy : y ∉ M.E) : rep 𝔽 (W × 𝔽) (series_extend M hx hy) := 
{ to_fun := λ (e : α), 
    if e = x
    then 
      (linear_map.inl 𝔽 W 𝔽 ∘ φ + linear_map.inr 𝔽 W 𝔽 ∘ (λ e : α, 1)) e
    else 
      if e = y then linear_map.inr 𝔽 W 𝔽 1 else (linear_map.inl 𝔽 W 𝔽 ∘ φ) e,
  valid' := λ I hI, 
    begin
      have hyindep : (series_extend M hx hy).nonloop y,
        sorry,
      refine ⟨_, λ h2, _⟩,
      { contrapose,
      intros h2,
      rw linear_dependent_comp_subtype',
      rw not_indep_iff at h2,
      obtain ⟨C, ⟨hCI, hCcct⟩⟩ := exists_circuit_subset_of_dep h2,
      by_cases hxC : x ∈ C, 
      { have hyC := (series_pair_mem_circuit _ _ _ hCcct 
          (series_extend_cocircuit M hx sorry hy)).1 hxC,
        rw [← @union_diff_cancel _ {y} C (singleton_subset_iff.2 hyC), union_comm, 
          union_singleton] at hCcct,
        have hMcct := contract_circuit_of_insert_circuit y (C \ {y}) hyindep 
          (not_mem_diff_singleton _ _) hCcct,
        rw [← series_extend_contr_eq] at hMcct,
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
          simp only [neg_smul, finset.sum_singleton, eq_self_iff_true, if_true, pi.add_apply, 
            prod.mk_add_mk, add_zero, zero_add, prod.smul_mk, algebra.id.smul_eq_mul, mul_one, 
            prod.neg_mk],
          
          simp only [prod.fst_add, zero_add, prod.fst_zero, prod.snd_add, prod.snd_zero],
          rw [finset.sum_ite_of_false _ _ (λ e he, _), finset.sum_ite_of_false _ _ (λ e he, _)],
          simp_rw [if_neg (ne_of_mem_of_not_mem hx hy)],
          rw [finset.sum_ite_of_false _ _ (λ e he, _), ← prod_mk_sum], 
          simp only [finset.sum_const_zero, zero_add, add_left_neg, eq_self_iff_true, and_true],
          
          

          
          /-rw [finset.sum_ite_of_false _ _ (λ e he, _), 
            finset.sum_ite_of_false _ _ (λ e he, _)],-/
         /- simp only [prod.smul_mk, prod.ext_iff, finset.sum_singleton, if_pos rfl, 
            if_neg (ne_of_mem_of_not_mem hx hy), if_neg (ne.symm (ne_of_mem_of_not_mem hx hy)),
            smul_zero, zero_add],
          simp only [algebra.id.smul_eq_mul, mul_one, prod.fst_add, prod.fst_zero, prod.snd_add, 
            prod.snd_zero, ← prod_mk_sum],
          simp only [pi.add_apply, prod.mk_add_mk, add_zero, zero_add, prod.smul_mk, 
            algebra.id.smul_eq_mul, mul_one, neg_add_cancel_comm_assoc],-/
           /-eq_self_iff_true, if_true, neg_smul, pi.add_apply, 
            prod.mk_add_mk, add_zero, zero_add, prod.smul_mk, algebra.id.smul_eq_mul, mul_one,
            ite_apply, pi.add_apply, prod.mk_add_mk, add_zero, zero_add, eq_self_iff_true, 
            if_true], -/--iff_false_intro h8, iff_false_intro h8.symm, if_false],
          sorry,
          sorry,
          sorry,
          sorry, },
        
        /-
        have h9 : ∀ (e : α), e ∈ (f.support \ {x}) → ¬ (e = y),
          sorry,
        simp_rw ite_smul,
        rw finset.sum_ite_of_false _ _ h9,
        simp_rw smul_ite,
        have h10 : ∀ (e : α), e ∈ (f.support \ {x}) → ¬ (e = x),
          sorry,
        rw [finset.sum_ite_of_false _ _ h10, finset.sum_ite_of_false _ _ h9],
        simp only [prod.smul_mk, smul_zero, algebra.id.smul_eq_mul, mul_one, prod.neg_mk, neg_zero, 
          mul_zero],
        rw [add_comm ((0 : W), -f x) _, add_assoc],
        simp only [prod.mk_add_mk, add_zero, add_right_neg],
        have h11 : (λ e : α, (f e • φ e, (0 : 𝔽))) x = (f x • φ x, (0 : 𝔽)),
          sorry,
        rw [← h11, ← @finset.sum_singleton _ _ x (λ e : α, (f e • φ e, (0 : 𝔽)))], 
        simp_rw h11,
        rw [← finset.sum_union, @finset.sdiff_union_of_subset _ _ ({x} : finset α) f.support _],
        have h30 : ∑ (x : α) in f.support, (f x • φ x, (0 : 𝔽)) = 
          (∑ (x : α) in f.support, f x • φ x, (0 : 𝔽)),
          sorry,
        rw [h30, prod.mk_eq_zero],
        refine ⟨hftot, rfl⟩,
        rw [finset.singleton_subset_iff, ← finset.mem_coe, hC, mem_diff_singleton],
        refine ⟨hxC, h8⟩,
        rw [← finset.disjoint_coe, finset.coe_sdiff],
        apply disjoint_sdiff_left,
        rw [← finset.disjoint_coe, finset.coe_sdiff],
        apply disjoint_sdiff_left,
        rw [finset.singleton_subset_iff, ← finset.mem_coe, hC, mem_diff_singleton],
        refine ⟨hxC, h8⟩,
        rw [← finset.disjoint_coe, hC],
        simp only [finset.coe_singleton, disjoint_singleton_left, not_mem_diff_singleton, 
          not_false_iff],
        by_contra,
        apply hfne0,
        ext,
        rw ← h,
        simp only [finsupp.coe_mk],-/
        sorry },
      { have hyC := (series_pair_mem_circuit _ _ _ hCcct 
          (series_extend_cocircuit M hx sorry hy)).2.mt hxC,
        have h4 := (@indep.of_contract _ _ {y} _).mt (not_indep_iff.2 hCcct.dep),
        rw [← contract_elem, ← series_extend_contr_eq, ← φ.valid, 
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
        by_cases hyI : (series_extend M hx hy).indep ({y} ∪ I : set α),
        { have hyI2 := (hyI.subset (subset_union_left _ _)).union_indep_iff_contract_indep.1 hyI,
          rw [← contract_elem, ← series_extend_contr_eq, ← φ.valid, 
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
        have hIxy : (series_extend M hx hy).indep ({y} ∪ (I \ {x}) : set α),  
        { by_contra hIyxn, 
          obtain ⟨C, ⟨hC, hC2⟩⟩ := exists_circuit_subset_of_dep ((not_indep_iff _).1 hIyxn),
          have hyC : y ∈ C,
          { by_contra hyC,
            rw [singleton_union, subset_insert_iff_of_not_mem hyC] at hC,
            apply hC2.dep.not_indep (h2.subset (subset_trans hC (diff_subset _ _))) },
          rw ← series_pair_mem_circuit _ _ _ hC2 (series_extend_cocircuit M hx sorry hy) at hyC,
          apply (not_mem_subset hC ((mem_union _ _ _).1.mt 
            (not_or_distrib.2 ⟨mem_singleton_iff.1.mt (ne_of_mem_of_not_mem hx hy), 
            not_mem_diff_singleton _ _⟩))) hyC,
          apply subset_trans (union_subset_union_right _ (diff_subset I {x})) hyI.subset_ground },
        have hyx := (hIxy.subset (subset_union_left _ _)).union_indep_iff_contract_indep.1 hIxy,
        rw [← contract_elem, ← series_extend_contr_eq, ← φ.valid, 
          linear_independent_comp_subtype] at hyx,
        rw [finset.erase_eq_of_not_mem hxl, finset.erase_eq_of_not_mem hyl] at hl0,
        apply hyx l ((l.mem_supported _).2 
          (subset_diff_singleton (subset_diff_singleton ((l.mem_supported _).1 hl) hxl) hyl)) hl0.1,
      apply hyx.subset_ground,
      sorry } }, 
    end,
  support := sorry }

end rep

end matroid_in
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
      refine ⟨_, λ h2, _⟩,
      { contrapose,
      intros h2,
      rw linear_dependent_comp_subtype',
      rw not_indep_iff at h2,
      obtain ⟨C, ⟨hCI, hCcct⟩⟩ := exists_circuit_subset_of_dep h2,
      by_cases hxC : x ∈ C, 
      { have hyC := (series_pair_mem_circuit _ _ _ hCcct 
          (series_extend_cocircuit M hx sorry hy)).1 hxC,
        have hyindep : (series_extend M hx hy).nonloop y,
          sorry,
        rw [← @union_diff_cancel _ {y} C (singleton_subset_iff.2 hyC), union_comm, 
          union_singleton] at hCcct,
        have hMcct := contract_circuit_of_insert_circuit y (C \ {y}) hyindep 
          (not_mem_diff_singleton _ _) hCcct,
        rw ← series_extend_contr_eq at hMcct,
        obtain ⟨f, ⟨hC, ⟨hftot, hfne0⟩⟩⟩ := rep.circuit φ hMcct,
        rw ← hC at *,
        have h8 := ne_of_mem_of_not_mem hx hy,
        refine ⟨(⟨(insert y f.support), (λ e : α, if e = y then - f x else f e), λ a, 
          ⟨λ ha, _, _⟩⟩ : α →₀ 𝔽), _⟩,
        obtain ⟨rfl | ha⟩ := finset.mem_insert.1 ha,
        simp only [eq_self_iff_true, if_true, ne.def, neg_eq_zero],
        rw [← ne.def, ← finsupp.mem_support_iff],
        have hxCy : x ∈ C \ {y},
          sorry,
        rw ← hC at hxCy,
        apply hxCy, 
        have h2 : ite (a = y) (-f x) (f a) = f a,
          rw ite_eq_iff,
          right,
          refine ⟨_, rfl⟩,
          sorry,
        rw h2,
        apply finsupp.mem_support_iff.1 h,
        by_cases a = y,
        sorry,
        sorry,
        refine ⟨_, _⟩,
        have hfI : ((insert y f.support : finset α) : set α) ⊆ I,
          sorry,
        apply hfI,
        refine ⟨_, _⟩,
        rw finsupp.total_apply at *,
        simp only [← ite_apply],
        simp_rw finset.insert_eq y f.support,
        dsimp [finsupp.sum],
        dsimp [finsupp.sum] at hftot,
        rw [finset.sum_union, ← @finset.sdiff_union_of_subset _ _ ({x} : finset α) f.support _, 
          finset.sum_union],
        simp only [finset.sum_singleton, eq_self_iff_true, if_true, neg_smul, pi.add_apply, 
          prod.mk_add_mk, add_zero, zero_add, prod.smul_mk, algebra.id.smul_eq_mul, mul_one,
          ite_apply, pi.add_apply, prod.mk_add_mk, add_zero, zero_add, eq_self_iff_true, 
          if_true, iff_false_intro h8, iff_false_intro h8.symm, if_false],
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
        simp only [finsupp.coe_mk],
        sorry },
      { have hyC := (series_pair_mem_circuit _ _ _ hCcct 
          (series_extend_cocircuit M hx sorry hy)).2.mt hxC,
        have h4 := (@indep.of_contract _ _ {y} _).mt (not_indep_iff.2 hCcct.dep),
        rw [← contract_elem, ← series_extend_contr_eq, ← φ.valid, 
          linear_dependent_comp_subtype'] at h4, 
        obtain ⟨f, ⟨hC, ⟨hftot, hfne0⟩⟩⟩ := h4,
        refine ⟨f, ⟨subset_trans hC hCI, ⟨_, hfne0⟩⟩⟩,
        rw finsupp.total_apply at *,
        dsimp [finsupp.sum],
        dsimp [finsupp.sum] at hftot,
        have h9 : ∀ (e : α), e ∈ f.support → ¬ (e = y),
          sorry,
        have h10 : ∀ (e : α), e ∈ f.support → ¬ (e = x),
          sorry,
        simp_rw smul_ite,
        rw [finset.sum_ite_of_false _ _ h10, finset.sum_ite_of_false _ _ h9],
        simp only [prod.smul_mk, algebra.id.smul_eq_mul, mul_zero, ← prod_mk_sum, hftot, 
          finset.sum_const_zero, prod.mk_eq_zero, eq_self_iff_true, and_self],
        have Csub := hCcct.subset_ground,
        
        
        sorry } },
      { simp_rw [linear_independent_comp_subtype, finsupp.total_apply, smul_ite],
        dsimp [finsupp.sum],
        simp only [add_zero, zero_add, mul_one, smul_zero, mul_zero],
        intros l hl hl0,
        rw [finset.sum_ite, finset.sum_ite] at hl0,
        --dsimp [finsupp.sum] at hyI2,
        rw prod.ext_iff at hl0,
        --have hl02 := hl0.1,
        simp only [finset.filter_congr_decidable, prod.fst_add, prod.fst_zero, prod.snd_add, 
          prod.snd_zero] at hl0,
        simp only [finset.filter_eq', finset.filter_ne', ← prod_mk_sum, 
          finset.sum_const_zero] at hl0,
        rw [zero_add, add_zero] at hl0,
        by_cases hyI : (series_extend M hx hy).indep ({y} ∪ I : set α),
        { --have hyI3 := hyI.subset (subset_union_left _ _),
          have hyI2 := (hyI.subset (subset_union_left _ _)).union_indep_iff_contract_indep.1 hyI,
          rw [← contract_elem, ← series_extend_contr_eq, ← φ.valid, 
            linear_independent_comp_subtype] at hyI2,
          simp_rw [finsupp.total_apply] at hyI2,
          rw finset.erase_right_comm at hl0,
          have hk : disjoint (ite (x ∈ l.support) {x} ∅) ((l.support.erase y).erase x),
            sorry,
          rw [← finset.sum_disj_union hk, finset.disj_union_eq_union] at hl0,
          by_cases hxl : x ∈ l.support,
            { rw [if_pos hxl, ← finset.insert_eq, finset.insert_erase, finset.erase_eq] at hl0,
              specialize hyI2 (⟨(l.support \ {y}), (λ e : α, if e = y then 0 else l e), λ a, 
                _⟩ : α →₀ 𝔽) _ _,
                simp only [finset.mem_sdiff, finsupp.mem_support_iff, ne.def, 
                  finset.mem_singleton, ite_eq_left_iff, not_forall, exists_prop, and_comm],
              { rw finsupp.mem_supported at hl,
                have h5 := @diff_subset_diff_left _ _ _ ↑({y} : finset α) hl,
                rw [← finset.coe_sdiff, finset.coe_singleton] at h5,
                apply h5 },
              { have h9 : ∀ (e : α), e ∈ (l.support \ {y}) → ¬ (e = y),
                  sorry,
                dsimp [finsupp.sum],
                simp_rw ite_smul,
                --rw finset.sum_smul,
                rw finset.sum_ite_of_false _ _ h9,
                apply hl0.1 },
              by_contra,
              apply finsupp.mem_support_iff.1 hxl,
              have h11 : (⟨(l.support \ {y}), (λ e : α, if e = y then 0 else l e), λ a, 
                _⟩ : α →₀ 𝔽) x = l x,
                /-rw ite_eq_iff,
                right,
                refine ⟨ne_of_mem_of_not_mem hx hy, rfl⟩,-/
                sorry,
              rw ← h11,
              rw hyI2,
              simp only [finsupp.coe_zero, pi.zero_apply],
              sorry },
            { simp only [if_neg hxl, finset.sum_empty, zero_add, finset.empty_union _] at hl0,
              specialize hyI2 (⟨(l.support \ {y}), (λ e : α, if e = y then 0 else l e), λ a, 
                _⟩ : α →₀ 𝔽) _ _,
                simp only [finset.mem_sdiff, finsupp.mem_support_iff, ne.def, 
                  finset.mem_singleton, ite_eq_left_iff, not_forall, exists_prop, and_comm],
                { rw finsupp.mem_supported at hl,
                  have h5 := @diff_subset_diff_left _ _ _ ↑({y} : finset α) hl,
                  rw [← finset.coe_sdiff, finset.coe_singleton] at h5,
                  apply h5 },
                { have h9 : ∀ (e : α), e ∈ (l.support \ {y}) → ¬ (e = y),
                    sorry,
                  dsimp [finsupp.sum],
                  simp_rw ite_smul, 
                  --rw finset.sum_smul,
                  simp_rw finset.sum_ite_of_false _ _ h9,
                  rw finset.erase_right_comm at hl0,
                  rw finset.erase_eq_of_not_mem hxl at hl0,
                  rw finset.erase_eq at hl0,
                  apply hl0.1 },
              ext;
              rw finset.erase_eq_of_not_mem hxl at hl0,
              by_cases a = y,
              { simp only [finsupp.coe_zero, pi.zero_apply],
                rw h,
                by_cases hyl : y ∈ l.support,
                { rw [← hl0.2, if_pos hyl, finset.sum_singleton] },
                { apply not_ne_iff.1 (finsupp.mem_support_iff.2.mt hyl) } },
              { rw ← hyI2, 
                simp,
                apply eq.symm,
                rw ite_eq_iff,
                right,
                refine ⟨h, rfl⟩ } },
              apply hyI2.subset_ground },
            have hyl : y ∉ l.support,
              -- l.support ⊆ I, y ∉ I
              sorry,
            rw not_indep_iff _ at hyI,
            have hIxy : (series_extend M hx hy).indep ({y} ∪ (I \ {x}) : set α),  
            { by_contra hIyxn, 
              rw not_indep_iff _ at hIyxn,
              obtain ⟨C, ⟨hC, hC2⟩⟩ := exists_circuit_subset_of_dep hIyxn,
              have hyC : y ∈ C,
                sorry,
              rw ← series_pair_mem_circuit _ _ _ hC2 (series_extend_cocircuit M hx sorry hy) at hyC,
              apply not_mem_subset hC ((mem_union _ _ _).1.mt 
                  (not_or_distrib.2 ⟨mem_singleton_iff.1.mt (ne_of_mem_of_not_mem hx hy), 
                  not_mem_diff_singleton _ _⟩)),
              apply hyC,
              apply subset_trans _ hyI.subset_ground,
              apply union_subset_union_right,
              apply diff_subset I {x} },
            have hyx := (hIxy.subset (subset_union_left _ _)).union_indep_iff_contract_indep.1 hIxy,
            rw [← contract_elem, ← series_extend_contr_eq, ← φ.valid, 
              linear_independent_comp_subtype] at hyx,
            rw [finset.erase_eq_of_not_mem ((@finset.mem_of_mem_erase _ _ _ x _).mt hyl), 
              if_neg ((@finset.mem_of_mem_erase _ _ _ x _).mt hyl), finset.sum_empty,
              add_zero] at hl0,
            have hxl : x ∉ l.support,
            { by_contra hxl,
              apply finsupp.mem_support_iff.1 hxl,
              rw [if_pos hxl, finset.sum_singleton, finset.sum_singleton] at hl0, --← hl0.2],
              simp only [finsupp.coe_zero, pi.zero_apply],
              rw ← hl0.2 },
            rw [finset.erase_eq_of_not_mem hxl] at hl0, 
            rw [if_neg hxl] at hl0,
            rw finset.sum_empty at hl0,
            rw zero_add at hl0,
            specialize hyx l _ _,
            { rw finsupp.mem_supported,
              /-have h5 := @diff_subset_diff_left _ _ _ ↑({y} : finset α) hl,
              rw [← finset.coe_sdiff, finset.coe_singleton] at h5,-/
              sorry },
            { rw finsupp.total_apply,
              dsimp [finsupp.sum],
              apply hl0.1 },
            apply hyx,
          apply hyx.subset_ground,
          sorry }, 
    end,
  support := sorry }

end rep

end matroid_in
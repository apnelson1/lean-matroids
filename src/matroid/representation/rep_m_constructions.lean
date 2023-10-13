import analysis.inner_product_space.gram_schmidt_ortho
import data.zmod.basic data.finsupp.fintype
import linear_algebra.basis
import linear_algebra.linear_independent
import m_in.minor m_in.constructions
import m_in.erank
import m_in.equiv
import .m_in_rep


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

def rep_of_del (N : matroid_in α) (φ : rep 𝔽 W N) (D : set α) : 
rep 𝔽 W (N ⟍ D) := 
{ to_fun := λ x, if x ∈ D then 0 else φ.to_fun x,
  valid' := λ I hI, by { rw delete_ground at hI, 
    have h2 : ∀ x : I, ite ((x : α) ∈ D) 0 (φ.to_fun x) = φ.to_fun x,
      intros x,
      rw ite_eq_iff,
      right,
      refine ⟨((mem_diff x.1).1 (mem_of_subset_of_mem hI x.2)).2, rfl⟩,
    have h8 : ((λ (e : α), ite ((e : α) ∈ D) 0 (φ.to_fun e)) ∘ coe) = 
          (λ (e : I), ite ((e : α) ∈ D) 0 (φ.to_fun e)),
      simp only [eq_self_iff_true],
    rw h8,
    simp_rw [λ (e : I), h2 e],
    refine ⟨λ h, delete_indep_iff.2 ⟨((φ.valid' I (subset_trans hI (diff_subset N.E D))).1 h), 
    (subset_diff.1 hI).2⟩, λ h, (φ.valid' I (subset_trans hI (diff_subset N.E D))).2 
      (matroid_in.delete_indep_iff.1 h).1⟩ },
  support := λ e he,
    begin
      simp only [ite_eq_iff],
      by_cases e ∈ D,
      left,
      refine ⟨h, rfl⟩,
      right,
      have h2 : e ∉ N.E,
        rw delete_ground at he,
        have h3 : N.E ⊆ (N.E \ D) ∪ D, 
          simp only [diff_union_self, subset_union_left],
        apply not_mem_subset h3,
        rw mem_union,
        push_neg,
        refine ⟨he, h⟩,
      refine ⟨h, φ.support e h2⟩,
    end  }

def rep_of_contr (N : matroid_in α) (φ : matroid_in.rep 𝔽 W N) (C : set α) (hC : C ⊆ N.E):
  matroid_in.rep 𝔽 (W ⧸ span 𝔽 (φ.to_fun '' C)) (N ⟋ C) := 
{ to_fun := λ x, submodule.quotient.mk (φ.to_fun x),
  valid' := λ I hI,
    begin
      rw contract_ground at hI,
      have h21 : (λ (x : ↥I), φ.to_fun ↑x) '' univ = φ.to_fun '' I,
        { simp only [to_fun_eq_coe, image_univ],
          ext;
          simp only [mem_range, set_coe.exists, subtype.coe_mk, exists_prop, mem_image] },
      obtain ⟨J, hJ⟩ := exists_basis N C hC,
      rw [basis.contract_eq_contract_delete hJ, delete_indep_iff, 
        indep.contract_indep_iff hJ.indep],
      have h10 := span_basis φ hJ,
      refine ⟨λ h, _, λ h, _⟩,  
      simp only at h,
      simp_rw [← mkq_apply _] at h,
      rw ← φ.valid' _ (union_subset (subset_trans hI (diff_subset _ _)) hJ.subset_ground_left),
      have h30 : disjoint (span 𝔽 (φ.to_fun '' I)) (span 𝔽 (φ.to_fun '' J)),
      { simp_rw [← to_fun_eq_coe] at h10,
        rw h10,
        simp_rw [← to_fun_eq_coe],
        rw ← ker_mkq (span 𝔽 (φ.to_fun '' C)),
        rw [linear_map.linear_independent_iff, ← image_univ, h21, disjoint.comm] at h,
        exact h.2 },
      have h7 := linear_independent.image 
        (linear_independent.of_comp ((span 𝔽 (φ '' C)).mkq) h),
      have h8 := linear_independent.image ((φ.valid' J hJ.subset_ground_left).2 (hJ.indep)),
      have h6 := linear_independent.union h7 h8 h30,
      rw [linear_independent_image, image_union],
      refine ⟨⟨_root_.disjoint.of_image (linear_independent.union' h7 h8 h30 h6), h6⟩, _⟩,
      apply @_root_.disjoint.of_image _ _ φ,
      rw disjoint_iff_forall_ne,
      intros x hxI y hyC, 
      by_contra h2,
      rw ← h2 at *,
      rw [submodule.disjoint_def, to_fun_eq_coe, h10] at h30,
      specialize h30 x (set_like.mem_coe.1 (mem_of_subset_of_mem subset_span hxI))
        (set_like.mem_coe.1 (mem_of_subset_of_mem 
        (subset_trans (image_subset _ (diff_subset _ _)) subset_span) hyC)),
      have h31 := mem_of_subset_of_mem 
        (image_subset _ (diff_subset _ _)) hyC,
      obtain ⟨e, ⟨he, rfl⟩⟩ := (mem_image φ I x).1 hxI,
      rw to_fun_eq_coe at h7,
      apply @linear_independent.ne_zero _ 𝔽 W _ _ _ _ _ (⟨φ e, hxI⟩ : φ '' I) h7,
      simp_rw h30,
      simp only [subtype.coe_mk],
      rw inj_on_union (_root_.disjoint.of_image (linear_independent.union' h7 h8 h30 h6)),
      refine ⟨φ.inj_on_of_indep ((φ.valid' I (subset_trans hI (diff_subset _ _))).1 
        (linear_independent.of_comp ((span 𝔽 (φ '' C)).mkq) h)), 
        ⟨φ.inj_on_of_indep (hJ.indep), λ x hx y hy, set.disjoint_iff_forall_ne.1 
        (linear_independent.union' h7 h8 h30 h6) (φ x) (mem_image_of_mem φ hx) 
        (φ y) (mem_image_of_mem φ hy)⟩⟩,
      simp_rw [← mkq_apply _],
      rw linear_map.linear_independent_iff,
      refine ⟨(φ.valid' I (indep.subset h.1.2 (subset_union_left I J)).subset_ground).2 
        (indep.subset h.1.2 (subset_union_left I J)), _⟩,
      rw ker_mkq (span 𝔽 (φ.to_fun '' C)),
      have h60 := linear_independent.image ((φ.valid' _ h.1.2.subset_ground).2 h.1.2),
      rw image_union at h60,
      rw [← image_univ, h21],
      simp_rw [to_fun_eq_coe],
      simp only [← h10],
      apply linear_independent.union'',
      { apply linear_independent.image 
          ((φ.valid' J (indep.subset h.1.2 (subset_union_right I J)).subset_ground).2 
            (indep.subset h.1.2 (subset_union_right I J))) },
      { apply linear_independent.image 
          ((φ.valid' I (indep.subset h.1.2 (subset_union_left I J)).subset_ground).2 
          (indep.subset h.1.2 (subset_union_left I J))) },
      { rw disjoint.comm,
        apply disjoint_image_image,
        have h200 := inj_on_of_indep φ h.1.2,
        rw inj_on at h200,
        intros x hx y hy,
        specialize h200 (mem_of_subset_of_mem (subset_union_left I J) hx) 
          (mem_of_subset_of_mem (subset_union_right I J) hy),
        apply mt h200,
        apply disjoint_iff_forall_ne.1 h.1.1 x hx y hy },
      rw [to_fun_eq_coe, union_comm _ _] at h60,
      apply h60,
    end,
  support := λ e he, 
    begin
      rw contract_ground at he,
      by_cases e ∈ C,
      rw quotient.mk_eq_zero,
      apply mem_of_subset_of_mem subset_span (mem_image_of_mem _ h),
      rw [φ.support, quotient.mk_zero],
      rw ← union_diff_cancel hC,
      apply (mem_union _ _ _).1.mt (not_or_distrib.2 ⟨h, he⟩),
    end }

/-def rep_of_dual {𝔽 W : Type*} [is_R_or_C 𝔽] [normed_add_comm_group W] [inner_product_space 𝔽 W] 
  (M : matroid_in α) (φ : rep 𝔽 W M) : rep 𝔽 (φ.to_submodule)ᗮ M﹡ := 
{ to_fun := λ e, _,
  valid' := _,
  support := _ }-/

def is_rep_of_minor_of_is_rep (N : matroid_in α) (hNM : N ≤m M) (hM : M.is_representable 𝔽) : 
  N.is_representable 𝔽 := 
begin
  obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := hM,
  obtain ⟨C, ⟨D, ⟨hC, ⟨hD, ⟨hCD, rfl⟩⟩⟩⟩⟩ := minor.exists_contract_indep_delete_coindep hNM,
  apply is_representable_of_rep (rep_of_del (M ⟋ C) (rep_of_contr M φ C hC.subset_ground) D),
end

variables [fintype α]


open_locale big_operators

def add_coloop_rep (φ : rep 𝔽 W M) {f : α} (hf : f ∉ M.E) : 
  rep 𝔽 (W × 𝔽) (add_coloop M hf) := 
{ to_fun := λ (e : α), if e ∈ ({f} : set α) then linear_map.inr 𝔽 W 𝔽 ((λ e : α, 1) e) else 
    linear_map.inl 𝔽 W 𝔽 (φ e),
  valid' := λ I hI, 
    begin
      by_cases f ∈ I,
      { rw [← union_diff_cancel (singleton_subset_iff.2 h), union_comm],
        simp only [← ite_apply _ (linear_map.inr 𝔽 W 𝔽 ∘ (λ e : α, 1)) (linear_map.inl 𝔽 W 𝔽 ∘ φ)],
        refine ⟨λ h2, _, λ h2, _⟩,
        { have h11 := linear_independent.image h2,
          rw image_union at h11,
          have hM : M.indep (I \ {f} : set α),
            { have h10 := linear_independent.mono (subset_union_left _ _) h11,
                rw ← linear_independent_image at h10,
                have h12 : ∀ e : ((I \ {f}) : set α), (ite ((e : α) ∈ ({f} : set α)) 
                  ((linear_map.inr 𝔽 W 𝔽) ↑1) ((linear_map.inl 𝔽 W 𝔽) (φ e)) 
                  = ((linear_map.inl 𝔽 W 𝔽) ∘ φ) e),
                { intros e,
                  rw ite_eq_iff,
                  right,
                  refine ⟨not_mem_of_mem_diff e.2, rfl⟩ },
              simp_rw [λ (e : (I \ {f} : set α)), h12 e, 
                @_root_.linear_map.linear_independent_iff _ _ _ _ _ _ _ _ _ _ (linear_map.inl 𝔽 W 𝔽) 
                (linear_map.ker_eq_bot_of_injective linear_map.inl_injective)] at h10,
              rw φ.valid at h10, 
              apply h10,
              rw [diff_subset_iff, union_comm],
              apply hI,
              { intros a ha b hb hab,
                have h13 := h2.injective,
                rw [← restrict_eq, ← inj_on_iff_injective] at h13,
                apply h13 (mem_union_left {f} ha) (mem_union_left {f} hb) hab } },
            obtain ⟨B2, hB2⟩ := hM, 
            refine ⟨B2 ∪ {f}, ⟨⟨_, mem_union_right _ (mem_singleton f)⟩, 
              union_subset_union hB2.2 (subset_refl _)⟩⟩,
            simp only [union_singleton, insert_diff_of_mem, mem_singleton],
            rw diff_singleton_eq_self (not_mem_subset hB2.1.subset_ground hf),
            apply hB2.1 },  
        { rw [linear_independent_image, image_union],
          have h12 : (λ (e : α), ite (e ∈ ({f} : set α)) ((linear_map.inr 𝔽 W 𝔽) ↑1) 
            ((linear_map.inl 𝔽 W 𝔽) (φ e))) '' (I \ {f}) = 
            (linear_map.inl 𝔽 W 𝔽) '' (φ '' (I \ {f})),
            { ext;
              simp only [mem_image, mem_diff, mem_singleton_iff, comp_app],
              refine ⟨λ h, _, λ h, _⟩,  
              { obtain ⟨x, ⟨⟨hx1, hx3⟩, hx2⟩⟩ := h,
                refine ⟨φ x, ⟨⟨x, ⟨⟨hx1, hx3⟩, rfl⟩⟩, _⟩⟩,
                rw [← hx2, eq_comm, ite_eq_iff],
                right,
                refine ⟨hx3, rfl⟩ },
              { obtain ⟨x, ⟨⟨x2, ⟨⟨hx3, hx4⟩, rfl⟩⟩, hx2⟩⟩ := h,
                refine ⟨x2, ⟨⟨hx3, hx4⟩, _⟩⟩,
                rw [← hx2, ite_eq_iff],
                right,
                refine ⟨hx4, rfl⟩ } },
          have h13 : (λ (e : α), ite (e ∈ ({f} : set α)) ((linear_map.inr 𝔽 W 𝔽) ↑1) 
            ((linear_map.inl 𝔽 W 𝔽) (φ e))) '' {f} = (linear_map.inr 𝔽 W 𝔽) '' (↑1 '' ({f} : set α)),
            { simp_rw [image_singleton, singleton_eq_singleton_iff, ite_eq_iff],
              left,
              refine ⟨mem_singleton _, rfl⟩ },
          rw [h12, h13],
          apply linear_independent.inl_union_inr,
          { have h6 := (h2.subset (subset_union_left _ _)).indep_delete_of_disjoint 
              (disjoint_sdiff_left),
            rw [← delete_elem, ← add_coloop_del_equal, ← φ.valid] at h6,
            apply h6.image,
            apply h6.subset_ground },
          { rw image_singleton,
            apply linear_independent_singleton,
            simp only [algebra_map.coe_one, pi.one_apply, ne.def, one_ne_zero, not_false_iff] },
          rw inj_on_union (disjoint_sdiff_left),
          refine ⟨_, ⟨inj_on_singleton _ _, _⟩⟩,
          { intros a ha b hb hab,
            simp only [if_neg (not_mem_of_mem_diff ha), if_neg (not_mem_of_mem_diff hb)] at hab,
            have hab2 := linear_map.inl_injective hab,
            have h4 := (h2.subset (subset_union_left _ _)).indep_delete_of_disjoint 
              (disjoint_sdiff_left),
            rw [← delete_elem, ← add_coloop_del_equal] at h4,
            apply (inj_on_of_indep φ h4) ha hb (linear_map.inl_injective hab) },
          intros a ha b hb,
          simp only [if_pos hb, if_neg (not_mem_of_mem_diff ha)],
          simp only [linear_map.coe_inl, linear_map.coe_inr, ne.def, prod.mk.inj_iff, not_and],
          intros hc,
          by_contra,
          have h6 := (h2.subset (subset_union_left _ _)).indep_delete_of_disjoint 
              (disjoint_sdiff_left),
          rw [← delete_elem, ← add_coloop_del_equal] at h6,
          apply φ.ne_zero_of_nonloop (h6.nonloop_of_mem ha),
          rw hc } },
      { have h8 : ((λ (e : α), ite (e ∈ ({f} : set α)) ((linear_map.inr 𝔽 W 𝔽) ↑((λ (e : α), 1) e)) 
          ((linear_map.inl 𝔽 W 𝔽) (φ e))) ∘ coe) = 
          (λ (e : I), ite ((e : α) ∈ ({f} : set α)) ((linear_map.inr 𝔽 W 𝔽) ↑((λ (e : α), 1) e))
          ((linear_map.inl 𝔽 W 𝔽) (φ e))),
          simp only [eq_self_iff_true],
        rw h8,
        have h3 : ∀ (e : I), (ite ((e : α) ∈ ({f} : set α)) 
          ((linear_map.inr 𝔽 W 𝔽) ↑((λ (e : α), 1) e)) ((linear_map.inl 𝔽 W 𝔽) (φ e))) = 
              ((linear_map.inl 𝔽 W 𝔽) ∘ φ) e,
        { intros,
          simp_rw [ite_eq_iff],
          right,
          refine ⟨mem_singleton_iff.1.mt (ne_of_mem_of_not_mem e.2 h), rfl⟩ },
        simp_rw [λ (e : I), h3 e],
        rw [@_root_.linear_map.linear_independent_iff _ _ _ _ _ _ _ _ _ _ 
          (linear_map.inl 𝔽 W 𝔽) 
          (linear_map.ker_eq_bot_of_injective linear_map.inl_injective), φ.valid],
        refine ⟨λ h2, _, λ h2, _⟩,
        { obtain ⟨B, hB⟩ := h2,
          refine ⟨(B ∪ {f} : set α), ⟨⟨_, _⟩, _⟩⟩,
          rw union_diff_cancel_right,
          apply hB.1,
          rw inter_comm,
          rw subset_empty_iff,
          apply singleton_inter_eq_empty.2,
          apply not_mem_subset hB.1.subset_ground hf,
          apply mem_union_right _ (mem_singleton _), 
          apply subset_union_of_subset_left hB.2 },
        { obtain ⟨B, ⟨⟨hB1, hB2⟩, hB3⟩⟩ := h2,
          refine ⟨(B \ {f} : set α), ⟨hB1, subset_diff_singleton hB3 h⟩⟩ },
        rw ← union_diff_cancel_right (subset_empty_iff.2 (inter_singleton_eq_empty.2 hf)),
        apply subset_diff_singleton hI h },
    end,
  support := λ e he, 
    begin
      by_cases e ∈ {f},
      { by_contra h2,
        apply he,
        rw mem_singleton_iff.1 h,
        rw ← singleton_subset_iff,
        apply subset_union_right },
      { have he2 := not_mem_subset (subset_union_left _ _) he,
        rw ite_eq_iff,
        right,
        refine ⟨h, _⟩,
        simp only [linear_map.coe_inl, prod.mk_eq_zero, eq_self_iff_true, 
          and_true],
        apply φ.support e he2 },
    end }

lemma U23_binary : matroid_in.is_binary (unif 2 3) :=
begin
  have hcard3 : fintype.card ((set.univ \ {0}) : set (fin 2 → zmod 2)) = 3, 
  { rw [← to_finset_card, to_finset_diff, finset.card_sdiff, to_finset_univ, finset.card_univ, 
      to_finset_card, card_singleton, @fintype.card_fun (fin 2) (zmod 2) _ _ _, zmod.card 2, 
      fintype.card_fin, pow_two, nat.sub_one, nat.pred_eq_succ_iff, two_mul],
    simp only [to_finset_univ, to_finset_subset, finset.coe_univ, singleton_subset_iff] },
  have f := equiv.symm (fintype.equiv_fin_of_card_eq hcard3),
  have φ := @rep.mk _ (zmod 2) (fin 2 → zmod 2) _ _ _ (unif 2 3) (λ x, (f x)) (λ I hI, _) 
    (by { simp only [unif_ground_eq, mem_univ, not_true, is_empty.forall_iff, forall_const]}),
  { rw [matroid_in.is_binary, is_representable],
    apply is_representable_of_rep φ },
  rw [unif_indep_iff],
  refine ⟨λ h, _, λ h, _⟩,  
  -- now the possible sizes of vector families for h are 0, 1, 2.
  { rw [ncard, nat.card_eq_fintype_card, ← @finrank_fin_fun (zmod 2) _ _ 2],
    apply fintype_card_le_finrank_of_linear_independent h },
  rw [linear_independent_image (λ x hx y hy hxy, 
    (f.injective.inj_on I) hx hy (subtype.coe_inj.1 hxy))],
  cases le_iff_lt_or_eq.1 h with h1 h2,
  cases le_iff_lt_or_eq.1 (nat.le_of_lt_succ h1) with h0 h1,
  { rw [ncard_eq_zero.1 (nat.lt_one_iff.1 h0), image_empty],
    apply linear_independent_empty (zmod 2) _ },
  
  { obtain ⟨a, rfl⟩ := ncard_eq_one.1 h1,
    rw [image_singleton],
    apply linear_independent_singleton,
    -- if i plug this in directly it wants me to provide a nontrivial (zmod 2) instance
    apply (mem_diff_singleton.1 (f a).2).2 },

  { obtain ⟨x, ⟨y, ⟨hxy, rfl⟩⟩⟩ := ncard_eq_two.1 h2,
    rw [image_insert_eq, image_singleton, linear_independent_insert, mem_span_singleton, not_exists],
    refine ⟨linear_independent_singleton ((mem_diff_singleton.1 (f y).2).2), λ a, _⟩,
    cases le_iff_lt_or_eq.1 (nat.le_of_lt_succ (zmod.val_lt a)) with h0 h1,
    { rw [(zmod.val_eq_zero a).1 (nat.lt_one_iff.1 h0), zero_smul],
      apply ne.symm (mem_diff_singleton.1 (f x).2).2 },
      rw [← zmod.nat_cast_zmod_val a, h1, algebra_map.coe_one, one_smul], 
      by_contra,
      apply hxy (f.injective (subtype.coe_inj.1 (eq.symm h))),
      by_contra,
      apply hxy (mem_singleton_iff.2 (f.injective (subtype.coe_inj.1 (h)))) },
end

lemma U22_binary : matroid_in.is_binary (unif 2 2) := 
begin
  sorry,
end

lemma U24_simple : (unif 2 4).simple := sorry

lemma U24_nonbinary : ¬ matroid_in.is_binary (unif 2 4) :=
begin
  by_contra h2,
  rw [matroid_in.is_binary, is_representable] at h2,
  obtain ⟨B, ⟨hB, ⟨φ'⟩⟩⟩ := h2,
  { have h8 := (φ'.subset_nonzero_of_simple U24_simple),
    have h50 := @span_mono (zmod 2) _ _ _ _ _ _ (subset_univ (φ' '' (unif 2 4).E)),
    rw ← span_span at h50,
    have h70 := subset_trans h8 (@diff_subset_diff_left _ _ _ 
      ({0} : set (B →₀ zmod 2)) (span_le.1 h50)),
    -- need basis
    have h11 := ((valid'' φ' hB.subset_ground).2 hB.indep),
    have h20 : (finrank (zmod 2) (B →₀ zmod 2)) = 2,
      simp only [finrank_finsupp, fintype.card_of_finset, finset.filter_congr_decidable],
      rw unif_base_iff at hB,
      rw filter_mem_univ_eq_to_finset,
      simp_rw ← hB, 
      rw [ncard_def, nat.card_eq_fintype_card, to_finset_card],
      simp only [bit0_le_bit0, nat.one_le_bit0_iff, nat.lt_one_iff],
    have h10 := finite_dimensional.fin_basis (zmod 2) (B →₀ zmod 2),
    rw h20 at h10,
    haveI : fintype (B →₀ zmod 2),
      apply finsupp.fintype,
    have h9 := @module.card_fintype _ (zmod 2) (B →₀ zmod 2) _ _ _ _ h10 _ _,
    simp only [zmod.card, fintype.card_fin] at h9,
    have h12 := fintype.card_le_of_embedding (embedding_of_subset _ _ h70),
    simp_rw [← to_finset_card, to_finset_diff] at h12,
    rw [finset.card_sdiff, span_univ, top_coe, to_finset_univ, finset.card_univ, h9,
      to_finset_card, to_finset_singleton, finset.card_singleton] at h12,
    have h80 : fintype.card (φ' '' (unif 2 4).E) = fintype.card (fin 4),
    { rw card_image_of_inj_on (φ'.inj_on_ground_of_simple U24_simple),
      simp only [unif_ground_eq, ← to_finset_card, to_finset_univ, finset.card_univ] },
    rw [h80, fintype.card_fin] at h12,
    rw [pow_two, two_mul, nat.succ_add_sub_one] at h12,
    linarith,
    simp only [span_univ, top_coe, to_finset_univ, to_finset_subset, 
      finset.coe_univ, singleton_subset_iff], },
end

def rep_of_loop (M : matroid_in α) [finite_rk M] {f : α} (hf : M.loop f) 
  (φ : rep 𝔽 W (M ⟍ f)) : rep 𝔽 W M := 
{ to_fun := φ,
  valid' := λ I hI, 
    begin
      by_cases f ∈ I,
      { rw ← not_iff_not,
        refine ⟨λ h2, _, λ h2, _⟩,
        { apply indep.nonloop_of_mem.mt,
          simp only [not_forall, exists_prop],
          refine ⟨h, not_nonloop_iff.2 hf⟩ },
        have hfφ := φ.support f,
        by_contra h3,
        have h4 : linear_independent 𝔽 (φ ∘ coe) = linear_independent 𝔽 (λ (i : I), φ i),
          simp only [eq_iff_iff],
        rw h4 at h3,
        apply @linear_independent.ne_zero _ 𝔽 W ((λ (i : I), φ i.1)) _ _ _ _ ⟨f, h⟩ h3,
        simp only,
        apply hfφ,
        rw [delete_elem, delete_ground],
        apply not_mem_diff_singleton },
      have hIf := subset_diff_singleton hI h,
      rw φ.valid,
      simp only [delete_elem, delete_indep_iff, disjoint_singleton_right, and_iff_left_iff_imp],
      intros hf2,
      apply h,
      rw [delete_elem, delete_ground],
      apply hIf,
    end,
  support := λ e he, 
    begin
      by_cases e = f,
      rw h,
      apply φ.support,
      simp only [delete_elem, delete_ground, not_mem_diff_singleton, not_false_iff],
      apply φ.support,
      simp only [delete_elem, delete_ground, mem_diff, mem_singleton_iff, not_and, not_not],
      contrapose,
      intros,
      apply he
    end } 

-- use matroid_of_module_func and write parallel_extend_rep
def rep_of_parallel (M : matroid_in α) [finite_rk M] {x y : α} (hxy : x ≠ y) 
  (hf : M.circuit {x, y}) (φ : rep 𝔽 W (M ⟍ ({y} : set α))) : rep 𝔽 W M := 
{ to_fun := λ (e : α), if e = y then φ x else φ e,
  valid' := λ I hI, 
    begin
      by_cases y ∈ I,
      { rw ← not_iff_not,
        refine ⟨λ h2, _, λ h2, _⟩,
        rw not_indep_iff,
        rw dep_iff_supset_circuit,
        sorry,
        sorry },
      { have h8 : ((λ (e : α), ite (e = y) (φ x) (φ e)) ∘ (coe : I → α)) = 
        ((λ (e : α), (φ e)) ∘ coe),
          sorry,
        rw h8,
        refine ⟨λ h2, _, λ h2, _⟩,
        apply indep.of_delete (φ.valid.1 h2),
        rw delete_ground,
        apply subset_diff_singleton hI h,
        rw [φ.valid, delete_indep_iff],
        refine ⟨h2, disjoint_singleton_right.2 h⟩,
        rw delete_ground,
        apply subset_diff_singleton hI h, },
    end,
  support := sorry }

def rep_empty (𝔽 : Type*) [field 𝔽] (M : matroid_in α) 
  (hM : M.E = ∅) : rep 𝔽 𝔽 M := 
{ to_fun := λ e, 0,
  valid' := λ I hI, 
    begin
      rw [hM, subset_empty_iff] at hI,
      rw [hI, @linear_independent_image _ _ _ _ _ _ (∅ : set α) _ (inj_on_empty _),
          image_empty],
        simp only [empty_indep, linear_independent_empty 𝔽 𝔽, iff_true]
    end,
  support := λ e he, rfl }

def rep_singleton (𝔽 : Type*) [field 𝔽] (M : matroid_in α) {x : α} (hMx : M.E = {x}) : 
  rep 𝔽 𝔽 M := 
{ to_fun := λ e, if hMx : M.nonloop x ∧ e = x then (1 : 𝔽) else (0 : 𝔽),
  valid' := λ I hI, 
    begin 
      rw hMx at *,
      cases ssubset_or_eq_of_subset hI with hIempty hIsing,
      { rw ssubset_singleton_iff.1 hIempty,
        rw [@linear_independent_image _ _ _ _ _ _ (∅ : set α) _ (inj_on_empty _),
          image_empty],
        simp only [empty_indep, linear_independent_empty 𝔽 𝔽, iff_true] },
      rw hIsing,
      by_cases M.loop x,
      { have hd : (λ (e : α), dite (M.nonloop x ∧ e = x) (λ (hMx : M.nonloop x ∧ e = x), (1 : 𝔽)) 
        (λ (hMx : ¬(M.nonloop x ∧ e = x)), (0 : 𝔽))) ∘ (coe : ({x} : set α) → α)
        = λ x : ({x} : set α), (0 : 𝔽),
          ext;
          simp only [dite_eq_iff],
          right,
          simp_rw not_and_distrib,
          refine ⟨(or.intro_left (¬↑x_1 = x)) h.not_nonloop, rfl⟩,
        rw [hd, ← not_iff_not],
        refine ⟨λ h2, h.dep.not_indep, λ h2, _⟩,
        by_contra,
        apply @linear_independent.ne_zero _ 𝔽 _ ((λ (e : α), (0 : 𝔽)) ∘ (coe : ({x} : set α) → α)) 
          _ _ _ _ ⟨x, mem_singleton x⟩ h,
        simp only },
      { have hd : (λ (e : α), dite (M.nonloop x ∧ e = x) (λ (hMx : M.nonloop x ∧ e = x), (1 : 𝔽)) 
        (λ (hMx : ¬(M.nonloop x ∧ e = x)), (0 : 𝔽))) ∘ (coe : ({x} : set α) → α)
        = λ x : ({x} : set α), (1 : 𝔽),
          ext;
          simp only [dite_eq_iff],
          left,
          have h2 := mem_singleton_iff.1 x_1.2,
          simp only [subtype.val_eq_coe] at h2,
          refine ⟨⟨(not_loop_iff (by {rw hMx, apply mem_singleton _})).1 h, h2⟩, rfl⟩,
        rw hd,
        refine ⟨λ h2, indep_singleton.2 ((not_loop_iff (by {rw hMx, apply mem_singleton _})).1 h), 
          λ h2, _⟩,
        rw [@linear_independent_image _ _ _ _ _ _ ({x} : set α) (λ e : α, (1 : 𝔽)) 
          (inj_on_singleton _ _), image_singleton],
        apply linear_independent_singleton,
        simp only [ne.def, one_ne_zero, not_false_iff] },
    end,
  support := λ e he, 
    begin
      simp only [dite_eq_iff],
      right,
      simp_rw not_and_distrib,
      rw [hMx, mem_singleton_iff] at he,
      refine ⟨(or.intro_right (¬ M.nonloop x)) he, rfl⟩,
    end }

end rep

end matroid_in
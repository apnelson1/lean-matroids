import ..dual

open set

-- open_locale classical
noncomputable theory
namespace matroid

variables {E : Type*} [finite E] {s t : ℕ} {I : set E} {M : matroid E}

/-- Truncate a matroid to rank `t`. Every rank above `t` drops to `t`. -/
def tr (M : matroid E) (t : ℕ) :=
  matroid_of_r (λ X, min t (M.r X))
  (λ X, (min_le_right _ _).trans (M.r_le_card _))
  (λ X Y hXY, le_min (min_le_left _ _) ((min_le_right _ _).trans (M.r_mono hXY)))
  (λ X Y,
  (begin
    wlog hXY : M.r X ≤ M.r Y generalizing X Y,
    { obtain (h | h) := le_or_lt (M.r X) (M.r Y),
      { exact this _ _ h},
      rw [add_comm (min t (M.r X)), inter_comm, union_comm],
      exact this _ _ h.le},
    cases le_or_lt t (M.r Y) with ht ht,
    { rw [min_eq_left ht, min_eq_left (ht.trans (M.r_le_r_union_right _ _))],
      linarith [min_le_min (rfl.le : t ≤ t) (M.r_inter_left_le_r X Y)]},
    rw [min_eq_right_of_lt ht, min_eq_right (hXY.trans ht.le)],
    linarith [min_le_right t (M.r (X ∩ Y)), min_le_right t (M.r (X ∪ Y)), M.r_submod X Y],
  end))

@[simp] lemma tr_r (t : ℕ) (X : set E) :
  (M.tr t).r X = min t (M.r X) :=
by simp only [tr, matroid_of_r_apply]

@[simp] lemma tr_indep_iff :
  (M.tr t).indep I ↔ M.indep I ∧ I.ncard ≤ t :=
begin
  simp_rw [indep_iff_r_eq_card, tr_r],
  obtain (hle | hlt) := le_or_lt t (M.r I),
  { rw [min_eq_left hle],
    exact ⟨by {rintro rfl, exact ⟨hle.antisymm' (M.r_le_card _), rfl.le⟩},
      λ h, (hle.trans_eq h.1).antisymm h.2⟩},
  rw [min_eq_right hlt.le],
  simp only [iff_self_and],
  exact λ h, h.symm.trans_le hlt.le,
end

end matroid

/- An attempted definition of truncation (by one) that doesn't rely on rank. I don't know to what
  extent truncation is defined for infinite matroids. TODO -/
-- def tr' (M : matroid E) :
--   matroid E :=
-- matroid_of_flat (λ F, M.flat F ∧ ¬ M.hyperplane F)
--   ⟨M.univ_flat, M.univ_not_hyperplane⟩
-- (begin
--   refine λ F₁ F₂ hF₁ hF₂, ⟨hF₁.1.inter hF₂.1, λ h, _⟩,
--   obtain (rfl | h₁) := eq_or_ne F₁ univ,
--   { rw [univ_inter] at h, exact hF₂.2 h},
--   refine h₁ (h.ssupset_eq_univ_of_flat hF₁.1 (ssubset_of_ne_of_subset (λ h_eq, _)
--     (inter_subset_left _ _))),
--   rw [h_eq] at h,
--   exact hF₁.2 h,
-- end)
-- (begin
--   rintro F₀ e ⟨hF₀,hhF₀⟩ heF₀,
--   have hne : F₀ ≠ univ,
--   { rw [ne.def, eq_univ_iff_forall, not_forall], exact ⟨_,heF₀⟩, },
--   obtain ⟨F₁,⟨heF₁,hcov⟩,hunique⟩ := hF₀.exists_unique_flat_of_not_mem heF₀,
--   -- obtain ⟨heF₁,hF₀F₁⟩ := insert_subset.mp heF₀F₁,
--   by_cases hhF₁ : M.hyperplane F₁,
--   { refine ⟨univ, ⟨⟨M.univ_flat,M.univ_not_hyperplane⟩,(subset_univ _),λ F hF hF₀F hFss, _⟩,_⟩,
--     { obtain ⟨H,hH,hFH⟩ := hF.1.subset_hyperplane_of_ne_univ hFss.ne,
--       obtain (rfl | hne) := eq_or_ne H F₁,
--       { exact (hcov.eq_or_eq hF.1 hF₀F hFH).elim eq.symm (by {rintro rfl, exact (hF.2 hhF₁).elim})},
--       have hF₁ := hcov.flat_right,
--       obtain (hinter | h_eq) := hcov.eq_or_eq (hH.flat.inter hF₁)
--         (subset_inter (hF₀F.trans hFH) hcov.subset) (inter_subset_right _ _),
--       { subst hinter,
--         rw [←hH.inter_covby_comm hhF₁] at hcov,
--         rw hcov.eq_of_subset_of_ssubset hF.1 hF₀F (hFH.ssubset_of_ne _),
--         rintro rfl,
--         exact hF.2 hH},
--       rw inter_eq_right_iff_subset at h_eq,
--       have := hhF₁.eq_of_subset hH h_eq, subst this,
--       exact (hne rfl).elim},
--     rintro F₂ ⟨hF₂, hF₂h, hmax⟩,
--     by_contra' hF₂univ,
--     obtain ⟨H,hH,hFH⟩ := hF₂.1.subset_hyperplane_of_ne_univ hF₂univ,

--     sorry,
--   },

-- end)



/-def indep (M : indep_family E) (n : ℤ) : set E → Prop := 
  λ X, M.indep X ∧ size X ≤ max 0 n

lemma I1 (M : indep_family E) (n : ℤ) :
  satisfies_I1 (trunc.indep M n) :=
⟨M.I1, by {rw size_empty, apply le_max_left, }⟩

lemma I2 (M : indep_family E) (n : ℤ) :
  satisfies_I2 (trunc.indep M n) :=
λ I J hIJ hJ, ⟨M.I2 I J hIJ hJ.1, le_trans (size_monotone hIJ) hJ.2⟩

lemma I3 (M : indep_family E) (n : ℤ) :
  satisfies_I3 (trunc.indep M n) :=
begin
  intros I J hIJ hI hJ,
  cases (M.I3 _ _ hIJ hI.1 hJ.1) with e he,
  refine ⟨e, ⟨he.1, ⟨he.2,_ ⟩ ⟩⟩,
  by_contra h_con, push_neg at h_con,
  rw [(size_union_nonmem_singleton (mem_diff_iff.mp he.1).2)] at h_con,
  linarith [int.le_of_lt_add_one h_con, hIJ, hJ.2],
end-/

/-def tr (M : matroid E) (n : ℤ) : matroid E :=
  let M_ind := M.to_indep_family in
  matroid.of_indep_family ⟨indep M_ind n, I1 M_ind n, I2 M_ind n, I3 M_ind n⟩-/
/-def tr'' (M : matroid E) (n : ℕ) [decidable_eq E] (h : n ≤ M.rk) : matroid E :=
{ base := λ X, M.indep X ∧ nat.card X = n,
  exists_base' :=
    begin
      cases M.exists_base' with B h2,
      rw base_iff_indep_r at h2,
      cases h2 with h1 h2,
      rw indep_iff_r_eq_card at h1,
      rw h2 at h1,
     
      sorry,
    end,
  base_exchange' := _ }-/
-- do we need the assumption that n ≤ M.r? i think so

-- -- tried my hand at defining truncation w.r.t rank
-- def matroid.tr_r (M : matroid E) (n : ℕ) : set E → ℕ := λ X, min (M.r X) n

-- lemma tr_r_le_card (M : matroid E) (n : ℕ) : ∀ X, (M.tr_r n X) ≤ nat.card X := λ X,
-- begin
--   rw matroid.tr_r,
--   simp,
--   left,
--   apply M.r_le_card,
-- end

-- lemma tr_r_mono (M : matroid E) (n : ℕ) : ∀ X Y, X ⊆ Y → M.tr_r n X ≤ M.tr_r n Y :=
-- begin
--   intros X Y hXY,
--   rw matroid.tr_r,
--   simp,
--   by_cases hX : M.r X < n,
--   { by_cases hY : M.r Y < n,
--     { left,
--       refine ⟨M.r_mono hXY, le_of_lt hX⟩ },
--     { right,
--       push_neg at hY,
--       exact hY } },
--   { by_cases hY : M.r Y < n,
--     { by_contra,
--       apply hX (lt_of_le_of_lt (M.r_mono hXY) hY) },
--     { right,
--       push_neg at hY,
--       exact hY } },
-- end

-- theorem set.inter_subset_union (s t : set E) : s ∩ t ⊆ s ∪ t := λ x h, (mem_union_left t) (mem_of_mem_inter_left h)

-- lemma tr_r_submod (M : matroid E) (n : ℕ) :
--   ∀ X Y, M.tr_r n (X ∩ Y) + M.tr_r n (X ∪ Y) ≤ M.tr_r n X + M.tr_r n Y :=
-- begin
--   intros X Y,
--   rw matroid.tr_r,
--   simp,
--   simp_rw ← min_add_add_right,
--   simp,
--   simp_rw ← min_add_add_left,
--   simp,
--   by_cases hInter : (M.r (X ∩ Y) < n),
--   { left,
--     by_cases hUnion : (M.r (X ∪ Y) < n),
--     { by_cases hX : (M.r (X) < n),
--       { by_cases hY : (M.r (Y) < n),
--         { split,
--           { left,
--             refine ⟨M.r_inter_add_r_union_le_r_add_r X Y,
--             le_trans (M.r_inter_add_r_union_le_r_add_r X Y)
--             (le_of_lt ((add_lt_add_iff_left (M.r X)).2 hY))⟩ },
--           { left,
--             refine ⟨le_trans (M.r_inter_add_r_union_le_r_add_r X Y)
--             (le_of_lt ((add_lt_add_iff_right (M.r Y)).2 hX)), _⟩,
--             apply le_of_lt,
--             linarith } },
--         { by_contra,
--           apply hY (lt_of_le_of_lt (M.r_mono (subset_union_right X Y)) hUnion) } },
--       { by_contra,
--         apply hX (lt_of_le_of_lt (M.r_mono (subset_union_left X Y)) hUnion) } },
--     by_cases hX : (M.r (X) < n),
--     { push_neg at hUnion,
--       by_cases hY : (M.r (Y) < n),
--       { split,
--         { right,
--           refine ⟨le_trans (add_le_add le_rfl hUnion) (M.r_inter_add_r_union_le_r_add_r X Y), M.r_mono (inter_subset_left X Y)⟩ },
--         { right,
--           split,
--           rw add_comm,
--           apply add_le_add (le_refl n) (M.r_mono (inter_subset_right X Y)),
--           apply le_of_lt hInter } },
--       { push_neg at hY,
--         have h2 := add_le_add (M.r_mono (inter_subset_left X Y)) (le_refl n),
--         split,
--         { right,
--           split,
--           linarith,
--           apply M.r_mono (inter_subset_left X Y) },
--         { right,
--           split,
--           linarith,
--           linarith } } },
--     { push_neg at hUnion,
--       push_neg at hX,
--       have h2 := M.r_inter_add_r_union_le_r_add_r X Y,
--       split,
--       right,
--       split,
--       linarith,
--       linarith,
--       right,
--       split,
--       rw add_comm,
--       simp,
--       apply M.r_mono (inter_subset_right X Y),
--       linarith } },
--   { by_cases hUnion : (M.r (X ∪ Y) < n),
--     { by_contra,
--       apply hInter (lt_of_le_of_lt (M.r_mono (set.inter_subset_union X Y)) hUnion) },
--     { by_cases hX : (M.r (X) < n),
--       { by_contra,
--         apply hInter (lt_of_le_of_lt (M.r_mono (inter_subset_left X Y)) hX) },
--       { by_cases hY : (M.r (Y) < n),
--         { by_contra,
--           apply hInter (lt_of_le_of_lt (M.r_mono (inter_subset_right X Y)) hY) },
--        {  push_neg at hInter,
--           push_neg at hUnion,
--           push_neg at hX,
--           push_neg at hY,
--           right,
--           split,
--           right,
--           split,
--           linarith,
--           linarith,
--           right,
--           exact hY } } } },
-- end

-- def tr (M : matroid E) (n : ℕ) : matroid E :=
--   matroid_of_r (M.tr_r n) (tr_r_le_card M n) (tr_r_mono M n) (tr_r_submod M n)

/-lemma weak_image (M : matroid E){n : ℕ} (hn : 0 ≤ n) :
  (tr M n) ≤ M :=
λ X, by {rw r_eq, simp, tauto, tauto }-/

-- in retrospect it would probably have been easier to define truncation in terms of rank. This is at least possible though.
-- lemma r_eq (M : matroid E){n : ℕ} (hn : 0 ≤ n) (X : set E) :
--   (tr M n).r X = min n (M.r X) :=
-- begin
--   rw tr,
--   simp,
--   rw matroid.tr_r,
--   simp,
--   rw min_comm,
-- end



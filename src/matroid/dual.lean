import .loop

noncomputable theory

open_locale classical

variables {E : Type*} [finite E] {M M₁ M₂ : matroid E} {B B₁ B₂ X Y Z : set E} {e f x y z : E}

open set
namespace matroid

section dual

/-- The dual of a matroid. Its bases are the complements of bases -/
def dual (M : matroid E) : matroid E :=
{ base := λ B, M.base Bᶜ,
  exists_base' := exists.elim M.exists_base (λ B hb, ⟨Bᶜ, by rwa compl_compl⟩),
  base_exchange' :=
  begin
    rintro B₁ B₂ hB₁ hB₂ x ⟨hx₁,hx₂⟩,
    rw [←mem_compl_iff] at hx₂,
    rw [←not_mem_compl_iff] at hx₁,
    obtain ⟨y,hy,hB⟩ := hB₂.rev_exchange hB₁ ⟨hx₂, hx₁⟩,
    rw [diff_eq_compl_inter, compl_compl] at hy,
    refine ⟨y,hy, _⟩,
    rwa [←union_singleton, compl_union, diff_eq_compl_inter, compl_inter, compl_compl,
      singleton_union, inter_comm, ←diff_eq_compl_inter, ←insert_diff_singleton_comm],
    rintro rfl,
    exact hx₁ hy.2,
  end }

@[simp] lemma dual_base_iff :
  M.dual.base B ↔ M.base Bᶜ :=
iff.rfl

@[simp] lemma dual_dual (M : matroid E):
  M.dual.dual = M :=
by {ext, simp}

lemma dual_inj (h : M₁.dual = M₂.dual) :
  M₁ = M₂ :=
by {ext B, rw [←compl_compl B, ←dual_base_iff, h, dual_base_iff]}

@[simp] lemma dual_inj_iff :
  M₁.dual = M₂.dual ↔ M₁ = M₂ :=
⟨dual_inj, congr_arg _⟩

end dual

lemma dual_indep_iff :
  M.dual.indep X ↔ ∃ B, M.base B ∧ disjoint B X :=
begin
  simp_rw [indep_iff_subset_base, dual_base_iff],
  split,
  { rintro ⟨B, hB, hXB⟩,
    exact ⟨_,hB,by rwa [←subset_compl_iff_disjoint_left, compl_compl]⟩},
  rintro ⟨B,hB,hBX⟩,
  exact ⟨Bᶜ,by rwa compl_compl,subset_compl_iff_disjoint_left.mpr hBX⟩,
end

lemma dual_indep_iff_coindep :
  M.dual.indep X ↔ M.coindep X :=
begin
  rw [dual_indep_iff, ←compl_compl X],
  set Y := Xᶜ with hY,
  simp_rw [disjoint_compl_right_iff_subset, coindep, not_exists, cocircuit],
  rw [(by {split, tauto, tauto} : (∃ (B : set E), M.base B ∧ B ⊆ Y) ↔ (∃ B ⊆ Y, M.base B)),
    base_subset_iff_cl_eq_univ],

  split,
  { intros hYcl K hKY hK,
    rw subset_compl_comm at hKY,
    exact ((hYcl.symm.trans_subset (M.cl_mono hKY)).trans_eq
      (hK.flat.cl)).not_ssubset (hK.ssubset_univ)},
  rintro h, by_contra h',
  rw [←ne.def, subset_hyperplane_iff_cl_ne_univ] at h',
  obtain ⟨H, hH, hYH⟩ := h',
  refine h Hᶜ (compl_subset_compl.mpr hYH) (by rwa compl_compl),
end

lemma dual_indep_iff_r :
  M.dual.indep X ↔ M.r Xᶜ = M.rk :=
begin
  rw [dual_indep_iff],
  split,
  { rintros ⟨B,hB,hBX⟩,
    refine le_antisymm (M.r_le_rk _) _,
    rw ←subset_compl_iff_disjoint_right at hBX,
    rw [←hB.r],
    exact M.r_mono hBX},
  intro hr,
  obtain ⟨B, hB⟩ := M.exists_basis Xᶜ,
  refine ⟨B, hB.indep.base_of_rk_le_card _, subset_compl_iff_disjoint_right.mp hB.subset⟩,
  rw [←hB.indep.r, hB.r, hr],
end

lemma loop.dual_coloop (he : M.loop e) :
  M.dual.coloop e :=
begin
  intros B hB,
  rw dual_base_iff at hB,
  simpa using he.not_mem_indep hB.indep,
end

lemma coloop.dual_loop (he : M.coloop e) :
  M.dual.loop e :=
begin
  rw [loop_def, circuit_def, dual_indep_iff],
  simp only [ssubset_singleton_iff, disjoint_singleton_right, not_exists, not_and, not_not_mem,
    forall_eq],
  exact ⟨he, empty_indep _⟩,
end

@[simp] lemma dual_coloop_if_loop :
  M.dual.coloop e ↔ M.loop e :=
⟨λ h, by {rw ← dual_dual M, exact h.dual_loop}, loop.dual_coloop⟩

@[simp] lemma dual_loop_iff_coloop :
  M.dual.loop e ↔ M.coloop e :=
⟨λ h, by {rw ←dual_dual M, exact h.dual_coloop}, coloop.dual_loop⟩

lemma dual_r_add_rk_eq (M : matroid E) (X : set E) :
  M.dual.r X + M.rk = ncard X + M.r Xᶜ  :=
begin
  set r' : set E → ℤ := λ X, X.ncard + M.r Xᶜ - M.rk with hr',

  have hr'_nonneg : ∀ X, 0 ≤ r' X,
  { intro X, simp_rw hr', linarith [M.rk_le_card_add_r_compl X]},
  have hr'_mono : ∀ X Y, X ⊆ Y → r' X ≤ r' Y,
  { intros X Y hXY, simp_rw hr',
    linarith [M.r_add_card_le_r_add_card_of_subset (compl_subset_compl.mpr hXY),
       ncard_add_ncard_compl X, ncard_add_ncard_compl Y]},
  have hr'_le_card : ∀ X, r' X ≤ X.ncard,
  { intros X, simp_rw hr', linarith [M.r_le_rk Xᶜ] },
  have hr'_submod : ∀ X Y, r' (X ∩ Y) + r' (X ∪ Y) ≤ r' X + r' Y,
  { intros X Y, simp_rw [hr', compl_inter, compl_union],
    linarith [ncard_inter_add_ncard_union X Y, M.r_submod Xᶜ Yᶜ]},

  set M' := matroid_of_int_r r' hr'_nonneg hr'_le_card hr'_mono hr'_submod with hM',

  have hM'M : M' = M.dual,
  { refine eq_of_indep_iff_indep_forall (λ I, _),
    rw [indep_iff_r_eq_card, dual_indep_iff_r], zify,
    simp_rw [hM', matroid_of_int_r_apply, hr'],
    refine ⟨λ h, _, λ h, _⟩,
    all_goals { simp only at h, linarith}},

  rw [←hM'M], zify, simp_rw [hM', matroid_of_int_r_apply, hr'],
  ring,
end

lemma dual_rank_cast_eq (M : matroid E) (X : set E) :
  (M.dual.r X : ℤ) = ncard X + M.r Xᶜ - M.rk :=
by linarith [M.dual_r_add_rk_eq X]


section rank



end rank

end matroid 
import .loop

noncomputable theory

open_locale classical

variables {E : Type*} {M M₁ M₂ : matroid E} {B B₁ B₂ X Y Z : set E} {e f x y z : E}

open set
namespace matroid

section dual



@[class] structure has_matroid_dual (α : Type*) := (dual : α → α)

postfix `﹡`:(max+1) := has_matroid_dual.dual 

instance matroid_dual {E : Type*} : has_matroid_dual (matroid E) := ⟨matroid.dual⟩ 

@[simp] lemma dual_base_iff : M﹡.base B ↔ M.base Bᶜ := base_dual_iff' 

lemma base_iff_dual_base_compl : M.base B ↔ M﹡.base Bᶜ :=
by rw [←compl_compl B, dual_base_iff, compl_compl, compl_compl]

@[simp] lemma dual_dual (M : matroid E) : M﹡﹡ = M := dual_dual' M

@[simp] lemma dual_indep_iff_coindep : M﹡.indep X ↔ M.coindep X := dual_indep_iff_coindep'

lemma base.compl_base_dual (hB : M.base B) : M﹡.base Bᶜ := hB.compl_base_dual'

lemma base.compl_inter_basis_of_inter_basis (hB : M.base B) (hBX : M.basis (B ∩ X) X) :
  M﹡.basis (Bᶜ ∩ Xᶜ) Xᶜ := hB.compl_inter_basis_of_inter_basis' hBX

lemma base.inter_basis_iff_compl_inter_basis_dual (hB : M.base B) : 
  M.basis (B ∩ X) X ↔ M﹡.basis (Bᶜ ∩ Xᶜ) Xᶜ :=
hB.inter_basis_iff_compl_inter_basis_dual'
 
lemma dual_inj (h : M₁﹡ = M₂﹡) : M₁ = M₂ :=
by {ext B, rw [←compl_compl B, ←dual_base_iff, h, dual_base_iff]}

@[simp] lemma dual_inj_iff : M₁﹡ = M₂﹡ ↔ M₁ = M₂ := ⟨dual_inj, congr_arg _⟩

end dual

lemma coindep_iff_disjoint_base : M.coindep X ↔ ∃ B, M.base B ∧ disjoint X B := iff.rfl 

lemma coindep_iff_r [finite E] : M.coindep X ↔ M.r Xᶜ = M.rk :=
begin
  rw [coindep_iff_disjoint_base],
  split,
  { rintros ⟨B,hB,hBX⟩,
    refine le_antisymm (M.r_le_rk _) _,
    rw ←subset_compl_iff_disjoint_left at hBX,
    rw [←hB.r],
    exact M.r_mono hBX},
  intro hr,
  obtain ⟨B, hB⟩ := M.exists_basis Xᶜ,
  refine ⟨B, hB.indep.base_of_rk_le_card _, subset_compl_iff_disjoint_left.mp hB.subset⟩,
  rw [←hB.indep.r, hB.r, hr],
end

lemma loop.dual_coloop (he : M.loop e) : M﹡.coloop e :=
by { intros B hB, rw dual_base_iff at hB, simpa using he.not_mem_indep hB.indep }

lemma coloop.dual_loop (he : M.coloop e) : M﹡.loop e :=
begin
  simp_rw [loop_iff_dep, dual_indep_iff_coindep, coindep_iff_disjoint_base, not_exists, 
    not_and, disjoint_singleton_left, not_not], 
  exact he, 
end 

@[simp] lemma dual_coloop_iff_loop :
  M﹡.coloop e ↔ M.loop e :=
⟨λ h, by {rw ← dual_dual M, exact h.dual_loop}, loop.dual_coloop⟩

@[simp] lemma dual_loop_iff_coloop :
  M﹡.loop e ↔ M.coloop e :=
⟨λ h, by {rw ←dual_dual M, exact h.dual_coloop}, coloop.dual_loop⟩

lemma dual_r_add_rk_eq [finite E] (M : matroid E) (X : set E) :
  M﹡.r X + M.rk = ncard X + M.r Xᶜ  :=
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

  have hM'M : M' = M﹡,
  { refine eq_of_indep_iff_indep_forall (λ I, _),
    rw [indep_iff_r_eq_card, dual_indep_iff_coindep, coindep_iff_r], zify,
    simp_rw [hM', matroid_of_int_r_apply, hr'],
    refine ⟨λ h, _, λ h, _⟩,
    all_goals { simp only at h, linarith} },

  rw [←hM'M], zify, simp_rw [hM', matroid_of_int_r_apply, hr'],
  ring,
end

lemma dual_rank_cast_eq [finite E] (M : matroid E) (X : set E) :
  (M﹡.r X : ℤ) = ncard X + M.r Xᶜ - M.rk :=
by linarith [M.dual_r_add_rk_eq X]

end matroid 
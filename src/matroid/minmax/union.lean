import .inter
import ..constructions.direct_sum
import ..maps.equiv
import algebra.big_operators.finprod

open_locale classical
open_locale big_operators

open matroid set equiv


section partitionable

variables {ι E : Type*} [finite E] [finite ι] {M : ι → matroid E} {I A X : set E}

/-- A set is partitionable with respect to a collection of matroids on `E` if it admits a partition
  into sets that are independent in these matroids  -/
-- def partitionable (M : ι → matroid E) (I : set E) : Prop :=
--   ∃ f : I → ι, ∀ i, (M i).indep (I ∩ (coe '' (f⁻¹' {i})))

def partitionable (M : ι → matroid E) (I : set E) : Prop :=
  ∃ (f : ι → set E), (I = ⋃ i, f i) ∧ (∀ i, (M i).indep (f i)) ∧ pairwise (disjoint on f)

lemma partitionable_iff_is_Union :
  partitionable M I ↔ ∃ (f : ι → set E), (I = ⋃ i, f i) ∧ (∀ i, (M i).indep (f i)) :=
begin
  refine ⟨λ ⟨f, h, hf, h'⟩, ⟨f, h, hf⟩, _⟩,
  rintro ⟨f,rfl,hf⟩,
  have hinv : ∀ (e : ⋃ (i : ι), f i), ∃ i, (e : E) ∈ f i,
  { rintro ⟨e,he⟩, exact mem_Union.mp he},

  choose g hg using hinv,
  have hss : ∀ i, coe '' (g ⁻¹' {i}) ⊆ f i,
  { rintro i x ⟨y,hy,rfl⟩,
    rw [mem_preimage, mem_singleton_iff] at hy, subst hy,
    exact hg y},

  refine ⟨λ i, coe '' (g ⁻¹' {i}), subset_antisymm _ _, λ i, (hf i).subset (hss i), _⟩,
  { refine Union_subset (λ i x hx, mem_Union_of_mem (g ⟨x, mem_Union_of_mem _ hx⟩) _),
    simp only [mem_Union, mem_image, mem_preimage, mem_singleton_iff, set_coe.exists,
      subtype.coe_mk, exists_and_distrib_right, exists_eq_right, eq_self_iff_true, exists_prop,
      and_true],
    exact ⟨_, hx⟩},
  { exact Union_subset (λ i, subset_Union_of_subset i (hss i))},
  rintro i j hij s (h1 : s ⊆ _) (h2 : s ⊆ _) i his,
  have h1' := h1 his,
  have h2' := h2 his,
  simp only [mem_Union, mem_image, mem_preimage, mem_singleton_iff, set_coe.exists,
    subtype.coe_mk, exists_and_distrib_right, exists_eq_right] at h1' h2',
  obtain ⟨⟨i₁,hi₁⟩,rfl⟩ := h1',
  obtain ⟨⟨i₂,hi₂⟩,rfl⟩ := h2',
  exfalso,
  simpa using hij,
end

lemma partitionable_ub {M : ι → matroid E} {I : set E} (X : set E) (h : partitionable M I) :
  I.ncard ≤ ∑ᶠ i, (M i).r X + Xᶜ.ncard :=
begin
  rw [←ncard_inter_add_ncard_diff_eq_ncard I X],
  refine add_le_add _
    (ncard_le_of_subset (by {rw compl_eq_univ_diff, exact diff_subset_diff_left (subset_univ _)})),

  obtain ⟨J, rfl, hJ, -⟩ :=  h,
  rw [Union_inter],
  refine (ncard_Union_le _ (λ _, to_finite _)).trans _,
  refine finsum_le_finsum (to_finite _) (to_finite _) (λ i, _),
  rw [←((hJ i).inter_right _).r],
  apply r_inter_right_le_r,
end

theorem matroid_union (M : ι → matroid E) :
  ∃ I X, partitionable M I ∧ I.ncard = ∑ᶠ i, (M i).r X + Xᶜ.ncard :=
begin
  suffices h : ∃ I X : set E, partitionable M I ∧ ∑ᶠ i, (M i).r Xᶜ + X.ncard ≤ I.ncard,
  { obtain ⟨I, X, hI, hle⟩ := h,
    refine ⟨I, Xᶜ, hI, _⟩,
    rw compl_compl,
    refine hle.antisymm' _,
    have := (partitionable_ub Xᶜ hI),
    rwa compl_compl at this},

  set M₁ := (direct_sum M).congr_equiv (sigma_equiv_prod ι E) with hM₁,
  set M₂ := (partition_matroid (λ (e : E), ι) 1).congr_equiv
    ((sigma_equiv_prod E ι).trans (prod_comm _ _)) with hM₂,

  obtain ⟨I,X, hI₁,hI₂, hIX, hF⟩ := exists_common_ind_with_flat_right M₁ M₂,

  simp only [congr_equiv_apply_flat, equiv.coe_trans, coe_prod_comm, preimage_compl,
    partition_one_flat_iff] at hF,

  simp_rw [← disjoint_compl_left_iff_subset, compl_compl, disjoint_compl_left_iff_subset] at hF,

  refine ⟨prod.snd '' I, prod.snd '' Xᶜ, _, _⟩,
  { rw partitionable_iff_is_Union,
    refine ⟨λ i, prod.snd '' (I ∩ (prod.fst ⁻¹' {i})), _, λ i, _⟩,
    { rw [←image_Union, ←inter_Union, ←bUnion_univ, bUnion_preimage_singleton, preimage_univ,
      inter_univ]},
    simp only [congr_equiv_apply_indep, direct_sum_indep_iff] at hI₁,
    convert hI₁ i, ext, simp},

  have hI : (prod.snd '' I).ncard = I.ncard,
  { refine ncard_image_of_inj_on _,
    rintro ⟨i₁,e⟩ h₁ ⟨i₂,e'⟩ h₂ (rfl : e = e'),
    simp only [prod.mk.inj_iff, eq_self_iff_true, and_true],
    simp only [congr_equiv_apply_indep, equiv.coe_trans, coe_prod_comm, partition_matroid_indep_iff,
      pi.one_apply, ncard_le_one_iff, mem_inter_iff, mem_preimage, function.comp_app,
      sigma_equiv_prod_apply, prod.swap_prod_mk, mem_singleton_iff, and_imp, sigma.forall] at hI₂,
    simpa using (@hI₂ e e i₂ ⟨e,i₁⟩ h₂ rfl h₁ rfl).symm},

  rw hI,
  refine le_of_le_of_eq (add_le_add (le_of_eq _) _) hIX.symm,

  { simp only [congr_equiv_apply_r, direct_sum_r_eq],
    convert rfl, ext i, convert rfl, ext e,
    simp only [mem_compl_iff, mem_image, prod.exists, exists_eq_right, not_exists_not,
      mem_preimage, sigma_equiv_prod_apply],
    refine ⟨λ h, h _, λ hie x, _⟩,
    obtain (hdj | hss) := hF e,
    { exact (@disjoint.ne_of_mem _ _ _ hdj ⟨e,i⟩ ⟨e,i⟩ (by simpa) rfl rfl).elim},
    exact @hss ⟨e,x⟩ rfl},

  simp only [congr_equiv_apply_r, equiv.coe_trans, coe_prod_comm, preimage_compl,
    partition_matroid_r_eq, pi.one_apply, ←finsum_mem_one],

  nth_rewrite_rhs 0 ←finsum_mem_univ,
  refine (finsum_mem_le_finsum_mem (to_finite _) (to_finite _) _).trans
    (finsum_le_finsum_of_subset (subset_univ (prod.snd '' Xᶜ)) (to_finite _)),

  rintro i ⟨⟨x1,x2⟩,hx, rfl⟩,
  simp only [mem_inter_iff, mem_compl_iff, mem_preimage, function.comp_app,
    sigma_equiv_prod_apply, prod.swap_prod_mk, mem_singleton_iff, le_min_iff, le_refl, true_and],


  conv_rhs {congr, funext, rw finsum_eq_if,  },

  rw ←finsum_mem_univ,

  refine le_trans _ (mem_le_finsum (mem_univ ((sigma_equiv_prod _ _).symm ⟨x2,x1⟩))
    (to_finite _)),

  rw [sigma_equiv_prod_symm_apply, if_pos],
  simp only [eq_self_iff_true, and_true],
  rwa mem_compl_iff at hx,
end

end partitionable




section partitionable_sets

variables {ι E : Type*} [finite E] [finite ι] {M : ι → matroid E} {I A X S : set E}

lemma partitionable_ub_subset (hX : I ⊆ S) (h : partitionable M I) :
  I.ncard ≤ ∑ᶠ i, (M i).r X + (S \ X).ncard :=
begin
  rw [←ncard_inter_add_ncard_diff_eq_ncard I X],
   refine add_le_add _ (ncard_le_of_subset (diff_subset_diff_left hX) (to_finite _)),
  obtain ⟨J, rfl, hJ⟩ := partitionable_iff_is_Union.mp h,
  rw [Union_inter],
  refine (ncard_Union_le _ (λ _, to_finite _)).trans _,
  refine finsum_le_finsum (to_finite _) (to_finite _) (λ i, _),
  rw [←((hJ i).inter_right _).r],
  apply r_inter_right_le_r,
end

/-- A version of matroid union that is relative to a subset. -/
theorem matroid_union_subset (M : ι → matroid E) (S : set E):
  ∃ (I ⊆ S) (X ⊆ S), partitionable M I ∧ I.ncard = ∑ᶠ i, (M i).r X + (S \ X).ncard :=
begin
  suffices : ∃ (I ⊆ S) (X ⊆ S), partitionable M I ∧ ∑ᶠ i, (M i).r X + (S \ X).ncard ≤ I.ncard,
  { obtain ⟨I, hIS, X, hXS, hI, h⟩ := this,
    exact ⟨I, hIS, X, hXS, hI, (partitionable_ub_subset hIS hI).antisymm h⟩},
  obtain ⟨I, X, hpart, hcard⟩ := matroid_union (λ i, M i ‖ S),
  use I,

  obtain ⟨J, rfl, hJ⟩ := partitionable_iff_is_Union.mp hpart,
  simp only [lrestr.indep_iff] at hJ,  
  simp_rw [lrestr.r] at hcard,

  refine ⟨Union_subset (λ i, (hJ i).2 ), X ∩ S, inter_subset_right _ _, _, _⟩,
  { rw partitionable_iff_is_Union,
    exact ⟨_,rfl,λi, (hJ i).1⟩ },

  simp only [hcard, diff_inter_self_eq_diff, add_le_add_iff_left, compl_eq_univ_diff],
  exact ncard_le_of_subset (diff_subset_diff_left (subset_univ _)),     
end

noncomputable def max_partitionable_set (M : ι → matroid E) (X : set E) : ℕ :=
  ⨅ A, ∑ᶠ i, (M i).r A + (X \ A).ncard



-- noncomputable def partitionable_sets_matroid (M : ι → matroid E) :
--   matroid E :=
-- matroid_of_r (max_partitionable_set M)
-- (λ X, by {convert cinfi_le' _ (∅ : set E), simp})
-- (λ X Y hXY, le_cinfi (λ Z, (cinfi_le' _ Z).trans
--   (add_le_add_left (ncard_le_of_subset (diff_subset_diff_left hXY) (to_finite _)) _)))
-- (begin
--   simp only [max_partitionable_set],
--   intros X Y,
-- end )

-- lemma ncard_max_partitionable_subset_eq (M : ι → matroid E)


def partitionable_sets_matroid (M : ι → matroid E) :
  matroid E :=
matroid_of_indep (partitionable M)
⟨∅, partitionable_iff_is_Union.mpr ⟨λ i, ∅, by simp, λ _, empty_indep _⟩⟩
(begin
  simp_rw partitionable_iff_is_Union,
  rintro I J hIJ ⟨s, rfl, hi⟩,
  refine ⟨λ i, (s i) ∩ I, _, λ i, (hi i).subset (inter_subset_left _ _)⟩,
  rwa [←Union_inter, eq_comm, inter_eq_right_iff_subset],
end )
(begin
  --simp_rw partitionable_iff_is_Union,
  rintro I J ⟨I, rfl, hI, hIdj⟩ ⟨J, rfl, hJ, hJdj⟩ hlt,
  by_contra' h',

  have hss : (⋃ i, J i) ⊆ ⋃ i, (M i).cl (I i),
  { rintro e ⟨J₀,⟨k,rfl⟩,(hek : e ∈ J k)⟩,
    obtain (⟨I₀,⟨i,rfl⟩,(hei : e ∈ I i)⟩ | hne) := em (e ∈ ⋃ i, I i),
    { exact mem_Union_of_mem i (((M i).subset_cl _) hei)},
    by_contra h'',
    apply h' e (mem_Union_of_mem _ hek) hne,
    rw partitionable_iff_is_Union,
    refine ⟨I.update k (insert e (I k)), _, _⟩,
    { simp only [subset_antisymm_iff, insert_subset,mem_Union, Union_subset_iff,
        function.update_apply],
      refine ⟨⟨⟨k,by simp⟩,λ i, subset_Union_of_subset i _⟩,λ i, _⟩,
      { split_ifs, subst h, simp, },
      split_ifs,
      { subst h, exact insert_subset_insert (subset_Union _ _)},
      exact (subset_Union _ _).trans (subset_insert _ _)},
    intro i,
    simp_rw function.update_apply,
    split_ifs,
    { subst h,
      have hei := not_mem_subset (subset_Union _ i) h'',
      exact ((hI i).not_mem_cl_iff.mp hei).2},
    apply hI},
  sorry

      -- refine ⟨⟨k, by simp⟩ , λ i, subset_Union_of_subset i _⟩,
      -- split_ifs,
      -- { subst h, simp},

    -- by_contra h'', rw [not_mem_iff] at h'',

  -- have h_ex : ∃ i, (I i).ncard < (J i).ncard,
  -- { by_contra' h,
  --   simp_rw [←finsum_mem_one, finsum_mem_Union hIdj (λ i, to_finite _),
  --     finsum_mem_Union hJdj (λ i, to_finite _), finsum_mem_one] at hlt,
  --   exact hlt.not_le (finsum_le_finsum (to_finite _) (to_finite _) h)},
  -- obtain ⟨i, hi⟩ := h_ex,
  -- obtain ⟨e ,heJ, heI, he⟩ := (hI i).augment (hJ i) hi,
  -- refine ⟨e, mem_Union_of_mem _ heJ, _ , _⟩,
  -- { rintro ⟨x, ⟨⟨j,rfl⟩,h⟩⟩,simp at h,   },


end)











end partitionable_sets



import .indep

noncomputable theory
open_locale classical
-- open_locale big_operators

open set

variables {E : Type*} [finite E] {M : matroid E} {B X Y X' Y' Z I J : set E} {e f x y z : E}

namespace matroid

/-- The rank function of a matroid. This is defined using `ncard`, to avoid a fintype instance
  so as not to carry around data (it has the junk value `0` if `X` is infinite) -/
noncomputable def r {E : Type*} (M : matroid E) : set E → ℕ :=
  λ X, nat.find_greatest (λ n, ∃ I, I ⊆ X ∧ M.indep I ∧ n = I.ncard) X.ncard

/-- The rank `M.rk` of a matroid `M` is the rank of its ground set -/
@[reducible] noncomputable def rk (M : matroid E) := M.r univ

lemma rk_def (M : matroid E) :
  M.rk = M.r univ :=
rfl

/-- This is the useful definition of rank -/
lemma eq_r_iff {n : ℕ} : M.r X = n ↔ ∃ I, M.basis I X ∧ I.ncard = n :=
begin
  simp_rw [matroid.r, nat.find_greatest_eq_iff, ne.def, ←or_iff_not_imp_left, not_exists], push_neg,
  split,
  { rintros ⟨hnX, rfl | ⟨I, hIX, hI, rfl⟩, h⟩,
    { simp_rw [pos_iff_ne_zero, ←or_iff_not_imp_left] at h,
      obtain ⟨I, hI⟩ := M.exists_basis X,
      exact ⟨I, hI, (@h I.ncard).elim id
        (λ h', false.elim (h' (ncard_le_of_subset hI.subset) _ hI.subset hI.indep rfl))⟩},
    refine ⟨I, ⟨hI, hIX, λ J hJ hIJ hJX,
      (eq_or_ssubset_of_subset hIJ).elim id (λ hIssJ, false.elim _)⟩, rfl⟩,
    exact h (ncard_lt_ncard hIssJ) (ncard_mono hJX) J hJX hJ rfl},
  rintros ⟨I, ⟨hIX, rfl⟩⟩,
  refine ⟨ncard_mono (by simpa using hIX.subset),or.inr ⟨I,hIX.subset,hIX.indep,rfl⟩,_⟩,
  rintro n hIn hnX J hJX hJ rfl,
  exact hIn.not_le (hJ.le_card_basis hJX hIX),
end

lemma le_r_iff {X : set E} {n : ℕ} : n ≤ M.r X ↔ ∃ I, M.indep I ∧ I ⊆ X ∧ I.ncard = n :=
begin
  obtain ⟨J, hJ⟩ := eq_r_iff.mp (@rfl _ (M.r X)),
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨I', hI', rfl⟩ := exists_smaller_set _ _ (h.trans_eq hJ.2.symm),
    exact ⟨I', hJ.1.indep.subset hI', hI'.trans hJ.1.subset, by simp⟩},
  obtain ⟨I, hI, hIX, rfl⟩ := h,
  rw ←hJ.2,
  exact hI.le_card_basis hIX hJ.1,
end

lemma r_le_iff {X : set E} {n : ℕ} :
  M.r X ≤ n ↔ (∀ I, M.indep I → I ⊆ X → I.ncard ≤ n) :=
begin
  obtain ⟨I, hIX, hI⟩ := eq_r_iff.mp (@rfl _ (M.r X)),
  refine ⟨λ h J hJ hJX, (hJ.le_card_basis hJX hIX).trans (by rwa hI), λ h, _⟩,
  have := h I hIX.indep hIX.subset, rwa ←hI,
end

lemma r_mono (M : matroid E) {X Y : set E} (hXY : X ⊆ Y) :
  M.r X ≤ M.r Y :=
by {simp_rw [r_le_iff, le_r_iff], exact λ I hI hIX, ⟨I,hI,hIX.trans hXY,rfl⟩}

lemma basis.card (hIX : M.basis I X) :
  I.ncard = M.r X :=
by {rw [eq_comm, eq_r_iff], exact ⟨_, hIX, rfl⟩}

lemma indep.r (hI : M.indep I) :
  M.r I = I.ncard :=
eq_r_iff.mpr ⟨I, ⟨hI, subset_refl _, λ _ _, subset_antisymm⟩, rfl⟩

lemma basis.r (hIX : M.basis I X) :
  M.r I = M.r X :=
by rw [←hIX.card, hIX.indep.r]

lemma base.r (hB : M.base B) :
  M.r B = M.rk :=
by {rw base_iff_basis_univ at hB, rw hB.r}

lemma base.card (hB : M.base B) :
  B.ncard = M.rk :=
by {rw base_iff_basis_univ at hB, rw hB.card}

lemma indep_iff_r_eq_card :
  M.indep I ↔ M.r I = I.ncard :=
begin
  refine ⟨indep.r ,λ h, _⟩,
  obtain ⟨J, hJ, hJI, hJcard⟩ := le_r_iff.mp h.symm.le,
  suffices hIJ : J = I, rwa ←hIJ,
  exact eq_of_subset_of_ncard_le hJI hJcard.symm.le,
end

lemma basis_iff_indep_card :
  M.basis I X ↔ M.indep I ∧ I ⊆ X ∧ I.ncard = M.r X :=
begin
  refine ⟨λ hI, ⟨hI.indep, hI.subset, hI.card⟩, _⟩,
  rintro ⟨hI, hIX, hIcard⟩,
  obtain ⟨I', hII', hI'X⟩ := hI.subset_basis_of_subset hIX,
  rw [eq_comm, ←hI.r] at hIcard,
  have h := ((M.r_mono hI'X.subset).trans_eq hIcard).antisymm (M.r_mono hII'),
  rw [hI.r, hI'X.indep.r] at h,
  rwa [eq_of_subset_of_ncard_le hII' h.le],
end

@[simp] lemma r_empty (M : matroid E) :
  M.r ∅ = 0 :=
by rw [M.empty_indep.r, ncard_empty]

lemma r_le_card (M : matroid E) (X : set E) :
  M.r X ≤ X.ncard :=
r_le_iff.mpr (λ I hI, ncard_le_of_subset)

lemma rk_le_card (M : matroid E) :
  M.rk ≤ nat.card E :=
by {rw [←ncard_univ], exact M.r_le_card univ}

lemma r_lt_card_of_dep (hX : ¬ M.indep X) :
  M.r X < X.ncard :=
lt_of_le_of_ne (M.r_le_card X) (by rwa indep_iff_r_eq_card at hX)

lemma r_lt_card_iff_dep :
  M.r X < X.ncard ↔ ¬M.indep X :=
⟨λ h hI, (h.ne hI.r),r_lt_card_of_dep⟩

lemma r_le_rk (M : matroid E) (X : set E) :
  M.r X ≤ M.rk :=
M.r_mono (subset_univ _)

lemma indep.card_le_rk (hI : M.indep I) :
  I.ncard ≤ M.rk :=
by {rw [←hI.r], exact M.r_mono (subset_univ I)}

lemma base_iff_indep_r :
  M.base B ↔ M.indep B ∧ M.r B = M.rk :=
begin
  refine ⟨λ h, ⟨h.indep, h.r⟩, λ h, base_iff_maximal_indep.mpr ⟨h.1, λ I hI hBI, _⟩⟩,
  refine eq_of_le_of_not_lt hBI (λ hBI' : B ⊂ I, _),
  cases h with hB hB',
  rw [hB.r] at hB',
  have := ncard_lt_ncard hBI',
  rw [←hI.r, hB'] at this,
  exact (M.r_mono (subset_univ _)).not_lt this,
end

lemma base_iff_indep_card :
  M.base B ↔ M.indep B ∧ B.ncard = M.rk :=
⟨λ h, ⟨h.indep, by rw ←h.card⟩, λ h, base_iff_indep_r.mpr ⟨h.1, by rw [←h.2, ←h.1.r]⟩⟩

lemma indep.base_of_rk_le_card (hI : M.indep I) (h : M.rk ≤ I.ncard) :
  M.base I :=
base_iff_indep_card.mpr ⟨hI, h.antisymm' (by {rw ←hI.r, apply r_le_rk})⟩

lemma basis.r_eq_r_union (hIX : M.basis I X) (Y : set E) :
  M.r (I ∪ Y) = M.r (X ∪ Y) :=
begin
  refine (M.r_mono (union_subset_union_left _ hIX.subset)).antisymm _,
  obtain ⟨I', hII', hI'⟩ :=
    hIX.indep.subset_basis_of_subset (hIX.subset.trans (subset_union_left _ Y)),
  rw [←hI'.r],
  refine M.r_mono (λ z hz, by_contra (λ hz', _)),
  rw [mem_union, decidable.not_or_iff_and_not] at hz',
  have hzX : z ∈ X, {cases (mem_of_mem_of_subset hz hI'.subset); tauto},

  have := hIX.eq_of_subset_indep
    (hI'.indep.subset (insert_subset.mpr ⟨hz,hII'⟩))
    (subset_insert z I) (insert_subset.mpr ⟨hzX, hIX.subset⟩),
  rw [eq_comm, insert_eq_self] at this,
  exact hz'.1 this,
end

lemma basis.r_eq_r_insert (hIX : M.basis I X) (e : E) :
  M.r (insert e I) = M.r (insert e X) :=
by simp_rw [←union_singleton, hIX.r_eq_r_union]

lemma indep.basis_of_subset_of_r_le (hI : M.indep I) (hIX : I ⊆ X) (h : M.r X ≤ M.r I) :
  M.basis I X :=
begin
  refine ⟨hI, hIX, λ J hJ hIJ hJX, eq_of_subset_of_ncard_le hIJ _⟩,
  rw [←hI.r, ←hJ.r],
  exact (M.r_mono hJX).trans h,
end

/-- The submodularity axiom for the rank function -/
lemma r_inter_add_r_union_le_r_add_r (M : matroid E) (X Y : set E) :
  M.r (X ∩ Y) + M.r (X ∪ Y) ≤ M.r X + M.r Y :=
begin
  obtain ⟨Ii, hIi⟩ := M.exists_basis (X ∩ Y),
  obtain ⟨IX, hIX, hIX'⟩ :=
    hIi.indep.subset_basis_of_subset (hIi.subset.trans (inter_subset_left _ _)),
  obtain ⟨IY, hIY, hIY'⟩ :=
    hIi.indep.subset_basis_of_subset (hIi.subset.trans (inter_subset_right _ _)),
  rw [←hIX'.r_eq_r_union, union_comm, ←hIY'.r_eq_r_union, ←hIi.card, ←hIX'.card, ←hIY'.card,
    union_comm, ←ncard_union_add_ncard_inter, add_comm],
  exact add_le_add (M.r_le_card _) (ncard_mono (subset_inter hIX hIY)),
end

lemma eq_of_r_eq_r_forall {M₁ M₂ : matroid E} (h : ∀ X, M₁.r X = M₂.r X) :
  M₁ = M₂ :=
eq_of_indep_iff_indep_forall (λ I, by simp_rw [indep_iff_r_eq_card,h I])

lemma r_le_r_of_subset (M : matroid E) (hXY : X ⊆ Y) :
  M.r X ≤ M.r Y :=
M.r_mono hXY

lemma r_submod (M : matroid E) (X Y : set E) :
  M.r (X ∪ Y) + M.r (X ∩ Y) ≤ M.r X + M.r Y :=
by {rw add_comm, exact M.r_inter_add_r_union_le_r_add_r X Y}

lemma r_submod' (M : matroid E) (X Y : set E) :
  M.r (X ∩ Y) + M.r (X ∪ Y) ≤ M.r X + M.r Y :=
M.r_inter_add_r_union_le_r_add_r _ _

lemma r_inter_left_le_r (M : matroid E) (X Y : set E) :
  M.r (X ∩ Y) ≤ M.r X :=
M.r_mono (inter_subset_left X Y)

lemma r_inter_right_le_r (M : matroid E) (X Y : set E) :
  M.r (X ∩ Y) ≤ M.r Y :=
M.r_mono (inter_subset_right X Y)

lemma r_le_r_union_left (M : matroid E) (X Y : set E) :
  M.r X ≤ M.r (X ∪ Y) :=
M.r_mono (subset_union_left X Y)

lemma r_le_r_union_right (M : matroid E) (X Y : set E) :
  M.r Y ≤ M.r (X ∪ Y) :=
M.r_mono (subset_union_right X Y)

lemma r_diff_le_r (M : matroid E) (X Y : set E) :
  M.r (X \ Y) ≤ M.r X :=
by {rw diff_eq, apply r_inter_left_le_r}

lemma r_zero_of_subset_r_zero (hXY : X ⊆ Y) (hY : M.r Y = 0) :
  M.r X = 0 :=
nat.eq_zero_of_le_zero ((M.r_mono hXY).trans_eq hY)

lemma r_zero_of_inter_r_zero (X : set E) :
  M.r Y = 0 → M.r (X ∩ Y) = 0 :=
λ hY, by {apply r_zero_of_subset_r_zero _ hY, simp }

lemma r_lt_card_iff_not_indep :
  (M.r X < X.ncard) ↔ ¬M.indep X :=
begin
  rw [lt_iff_not_le, not_iff_not, indep_iff_r_eq_card],
  exact ⟨(M.r_le_card X).antisymm, λ h, by rw h⟩,
end

lemma nonempty_of_r_lt_card (hX : M.r X < X.ncard) :
  X.nonempty :=
by {rw r_lt_card_iff_not_indep at hX, rw nonempty_iff_ne_empty, rintro rfl, exact hX M.empty_indep}

lemma nonempty_of_r_nonzero (hX : M.r X ≠ 0):
  X.nonempty :=
by {rw nonempty_iff_ne_empty, rintro rfl, exact hX M.r_empty}

lemma r_single_ub (M : matroid E) (e : E) :
  M.r {e} ≤ 1 :=
by {convert M.r_le_card _, simp}

lemma r_le_univ (M : matroid E) (X : set E) :
  M.r X ≤ M.r univ :=
M.r_mono (subset_univ X)

lemma r_compl_univ (M : matroid E) :
  M.r (univᶜ) = 0 :=
by rw [compl_univ, r_empty]

lemma r_eq_r_of_subset_le (hXY : X ⊆ Y) (hYX : M.r Y ≤ M.r X) :
  M.r X = M.r Y :=
(M.r_mono hXY).antisymm hYX

lemma r_eq_of_r_union_le (hle : M.r (X ∪ Y) ≤ M.r X):
  M.r (X ∪ Y) = M.r X :=
((r_eq_r_of_subset_le ((subset_union_left _ _))) hle).symm

lemma r_eq_of_r_le_inter (hle : M.r X ≤ M.r (X ∩ Y)):
   M.r (X ∩ Y) = M.r X :=
(r_eq_r_of_subset_le (inter_subset_left _ _) hle)

-- lemma r_eq_of_not_lt_supset :
--   X ⊆ Y → ¬(M.r X < M.r Y) → M.r X = M.r Y :=
-- λ h h', r_eq_of_le_supset h (int.le_of_not_gt' h')

-- lemma r_eq_of_not_lt_union :
--   ¬ (M.r X < M.r (X ∪ Y)) → M.r (X ∪ Y) = M.r X :=
-- λ h', r_eq_of_le_union (int.le_of_not_gt' h')

lemma r_eq_r_union_r_zero (X : set E) (hY : M.r Y = 0) :
  M.r (X ∪ Y) = M.r X :=
r_eq_of_r_union_le (by linarith [M.r_submod X Y])

lemma r_eq_r_diff_r_zero (X : set E) (hY : M.r Y = 0) :
  M.r (X \ Y) = M.r X :=
begin
  refine le_antisymm (r_diff_le_r _ _ _) _,
  rw ←r_eq_r_union_r_zero (X \ Y) hY,
   exact r_mono _ (λ x hx, by {rw [mem_union, mem_diff], tauto,}),
end

lemma r_zero_of_union_r_zero (hX : M.r X = 0) (hY : M.r Y = 0):
  M.r (X ∪ Y) = 0 :=
by rwa (r_eq_r_union_r_zero _ hY)

lemma r_union_eq_of_subset_of_r_eq (Z : set E) (hXY : X ⊆ Y) (hr : M.r X = M.r Y):
  M.r (X ∪ Z) = M.r (Y ∪ Z) :=
begin
  apply r_eq_r_of_subset_le (union_subset_union_left Z hXY),
  have : M.r ((X ∪ Z) ∩ Y) = _ := by rw [inter_distrib_right, inter_eq_left_iff_subset.mpr hXY] ,
  have : M.r ((X ∪ Z) ∪ Y) = _ := by rw [union_assoc, union_comm Z Y, ←union_assoc,
                                      union_eq_right_iff_subset.mpr hXY ],
  linarith [M.r_submod (X ∪ Z) Y , M.r_le_r_union_left X (Z ∩ Y) ],
end

lemma r_union_eq_of_subset_of_r_eqs (hX : X ⊆ X') (hY : Y ⊆ Y')
(hXX' : M.r X = M.r X') (hYY' : M.r Y = M.r Y') :
  M.r (X ∪ Y) = M.r (X' ∪ Y') :=
by rw [r_union_eq_of_subset_of_r_eq Y hX hXX', union_comm, union_comm _ Y',
       r_union_eq_of_subset_of_r_eq _ hY hYY']

lemma r_eq_of_inter_union (X Y A : set E) :
  M.r (X ∩ A) = M.r X → M.r ((X ∩ A) ∪ Y) = M.r (X ∪ Y) :=
λ h, r_union_eq_of_subset_of_r_eq _ (inter_subset_left _ _) h

lemma r_eq_of_union_r_diff_eq (Z : set E) (hX : M.r (X \ Y) = M.r X) :
  M.r (Z ∪ (X \ Y)) = M.r (Z ∪ X) :=
by {rw diff_eq at *, rw [union_comm _ X, ← r_eq_of_inter_union _ Z _ hX, union_comm Z]}

lemma r_union_le_add_r (M : matroid E) (X Y : set E) :
  M.r (X ∪ Y) ≤ M.r X + M.r Y :=
by linarith [M.r_submod X Y]

lemma r_union_le_card_add_r (M : matroid E) (X Y : set E) :
  M.r (X ∪ Y) ≤ X.ncard + M.r Y :=
(M.r_union_le_add_r X Y).trans (add_le_add_right (M.r_le_card _) _)

lemma r_union_le_r_add_card (M : matroid E) (X Y : set E) :
  M.r (X ∪ Y) ≤ M.r X + Y.ncard :=
(M.r_union_le_add_r X Y).trans (add_le_add_left (M.r_le_card _) _)

lemma rk_le_card_add_r_compl (M : matroid E) (X : set E) :
  M.rk ≤ X.ncard + M.r Xᶜ :=
begin
  rw [rk_def, ←union_compl_self X],
  exact (M.r_union_le_add_r _ _).trans (add_le_add_right (M.r_le_card _) _),
end

lemma rank_eq_of_le_supset (h : X ⊆ Y) (hr : M.r Y ≤ M.r X) :
  M.r X = M.r Y :=
hr.antisymm' (M.r_mono h)

lemma rank_eq_of_le_union :
  M.r (X ∪ Y) ≤ M.r X → M.r (X ∪ Y) = M.r X :=
λ h, ((rank_eq_of_le_supset ((subset_union_left _ _))) h).symm

lemma rank_eq_of_le_inter :
  M.r X ≤ M.r (X ∩ Y) →  M.r (X ∩ Y) = M.r X :=
λ h, (rank_eq_of_le_supset (inter_subset_left _ _) h)


/- Probably `finsum` is fight for this  -/

-- lemma r_union_le_add_r_sUnion (M : matroid E) (S : finset (set E)) :
--   M.r (S.bUnion id) ≤ ∑ x in s, f x :=
-- begin
--   set P := λ (S : set (set E)), M.r (⋃₀ S) ≤ ∑ᶠ X in S, M.r X with hP,
--   refine induction_set_size_insert P (by {rw hP, simp}) (λ X A hA hX, _) _,
--   rw [hP, sUnion_insert, fin.finsum_in_insert _ hA],
--   exact le_trans (r_union_le_add_r M _ _) (int.add_le_add_left hX _),
-- end

lemma r_le_r_insert (M : matroid E) (X : set E) (e : E) :
  M.r X ≤ M.r (insert e X) :=
M.r_mono (subset_insert _ _)

lemma r_insert_le_add_one (M : matroid E) (X : set E) (e : E) :
  M.r (insert e X) ≤ M.r X + 1 :=
by {rw ←union_singleton, linarith [r_union_le_add_r M X {e}, r_single_ub M e]}

lemma r_insert_eq_add_one_of_r_ne (h : M.r (insert e X) ≠ M.r X):
  M.r (insert e X) = M.r X + 1 :=
(r_insert_le_add_one M X e).antisymm
  (nat.add_one_le_iff.mpr ((M.r_mono (subset_insert _ _)).lt_of_ne h.symm))

lemma r_eq_of_le_insert (h : M.r (insert e X) ≤ M.r X):
  M.r (insert e X) = M.r X :=
by {rw ←union_singleton at *, exact le_antisymm h (r_le_r_union_left _ _ _) }

lemma r_le_r_add_r_diff (M : matroid E) (X Y : set E) :
  M.r Y ≤ M.r X + M.r (Y \ X) :=
le_trans (M.r_mono (by simp)) (r_union_le_add_r M X (Y \ X))

lemma r_le_r_diff_singleton_add_one (M : matroid E) (X : set E) (e : E) :
  M.r X ≤ M.r (X \ {e}) + 1 :=
by linarith [r_le_r_add_r_diff M {e} X, r_single_ub M e]

lemma r_diff_singleton_add_one_eq_r_of_ne (h_ne : M.r X ≠ M.r (X \ {e})) :
  M.r (X \ {e}) + 1 = M.r X :=
(nat.add_one_le_iff.mpr (lt_of_le_of_ne (M.r_diff_le_r X {e}) h_ne.symm)).antisymm
    (M.r_le_r_diff_singleton_add_one _ _)

lemma r_le_r_add_card_diff_of_subset (M : matroid E) (hXY : X ⊆ Y) :
  M.r Y ≤ M.r X + (Y \ X).ncard :=
(M.r_le_r_add_r_diff X Y).trans (add_le_add_left (by convert M.r_le_card (Y \ X)) _)

lemma r_add_card_le_r_add_card_of_subset (M : matroid E) (hXY : X ⊆ Y) :
  M.r Y + X.ncard ≤ M.r X + Y.ncard :=
begin
  have := M.r_le_r_add_card_diff_of_subset hXY,
  linarith [ncard_diff_add_ncard_eq_ncard hXY],
end

lemma submod_three (M : matroid E) (X Y Y' : set E) :
  M.r (X ∪ (Y ∪ Y')) + M.r (X ∪ (Y ∩ Y')) ≤ M.r (X ∪ Y) + M.r (X ∪ Y') :=
begin
  have := M.r_submod (X ∪ Y) (X ∪ Y'),
  rwa [←union_distrib_left, ←union_union_distrib_left] at this,
end

lemma submod_three_right (M : matroid E) (X Y Y' : set E) :
  M.r ((Y ∪ Y') ∪ X) + M.r ((Y ∩ Y') ∪ X) ≤ M.r (Y ∪ X) + M.r (Y' ∪ X) :=
by {simp_rw ←(union_comm X), apply submod_three}

lemma submod_three_disj (M : matroid E) (X Y Y' : set E) (hYY' : Y ∩ Y' = ∅) :
  M.r (X ∪ (Y ∪ Y')) + M.r (X) ≤ M.r (X ∪ Y) + M.r (X ∪ Y') :=
by {have := submod_three M X Y Y', rwa [hYY', union_empty] at this}

theorem r_augment (h : M.r X < M.r Z) :
  ∃ z ∈ Z, M.r X < M.r (insert z X) :=
begin
  obtain ⟨I, hI⟩ := M.exists_basis X,
  obtain ⟨J, hIJ, hJ⟩ := hI.indep.subset_basis_of_subset (hI.subset.trans (subset_union_left X Z)),
  have hXZ := h.trans_le (M.r_mono (subset_union_right X Z)),

  rw [←hI.card, ←hJ.card] at hXZ,
  obtain ⟨e,heJ,heI⟩ := exists_mem_not_mem_of_ncard_lt_ncard hXZ,

  have hlt : M.r X < M.r (insert e X),
  { refine lt_of_lt_of_le _ (M.r_mono (@insert_subset_insert _ e _ _ hI.subset)),
    rw [←hI.card, (hJ.indep.subset (insert_subset.mpr ⟨heJ,hIJ⟩)).r, ncard_insert_of_not_mem heI,
      nat.lt_iff_add_one_le]},
  have heX : e ∉ X,
  { refine λ heX, hlt.ne _, rw [insert_eq_of_mem heX], },
  have heZ : e ∈ Z,
    from or.resolve_left (hJ.subset heJ) heX,
  exact ⟨e,heZ,hlt⟩,
end

lemma r_union_eq_of_r_union_subset_le (hXY : X ⊆ Y) (h : M.r (X ∪ Z) ≤ M.r X) :
  M.r (Y ∪ Z) = M.r Y :=
begin
  have hsm := M.r_submod Y (X ∪ Z),
  rw [←union_assoc, union_eq_left_iff_subset.mpr hXY, inter_distrib_left,
    inter_eq_right_iff_subset.mpr hXY] at hsm,
  linarith [M.r_le_r_union_left X (Y ∩ Z), M.r_le_r_union_left Y Z],
end

lemma r_insert_eq_of_r_insert_subset_le (hXY : X ⊆ Y) (h : M.r (insert e X) ≤ M.r X) :
  M.r (insert e Y) = M.r Y :=
by {rw [←union_singleton] at *, rw [r_union_eq_of_r_union_subset_le hXY h],}

lemma r_eq_of_r_all_insert_le (hXY : X ⊆ Y) (hY : ∀ e ∈ Y, M.r (insert e X) ≤ M.r X) :
   M.r X = M.r Y :=
begin
  refine (M.r_mono hXY).antisymm (le_of_not_lt (λ hlt, _)),
  obtain ⟨e,he,hlt'⟩ := r_augment hlt,
  exact hlt'.not_le (hY _ he),
end

lemma r_union_eq_of_r_all_insert_le (hY : ∀ e ∈ Y, M.r (insert e X) ≤ M.r X) :
  M.r (X ∪ Y) = M.r X :=
begin
  refine (r_eq_of_r_all_insert_le (subset_union_left X Y) _).symm,
  rintro e (heX | heY),
  { rw [insert_eq_of_mem heX]},
  exact hY _ heY,
end

lemma r_eq_of_r_all_insert_eq (hXY : X ⊆ Y) (hY : ∀ e ∈ Y, M.r X = M.r (insert e X)) :
   M.r X = M.r Y :=
r_eq_of_r_all_insert_le hXY (λ e h, (hY e h).symm.le)

lemma r_eq_zero_of_loopy (he : (∀ e ∈ X, M.r {e} = 0)) :
  M.r X = 0 :=
begin
  rw [←M.r_empty, eq_comm],
  exact r_eq_of_r_all_insert_eq (empty_subset _)
    (λ e heX, by {rw [M.r_empty, eq_comm, insert_emptyc_eq], exact he e heX}),
end

lemma indep_inter_r_zero_eq_empty (hI : M.indep I) (hX : M.r X = 0) :
   I ∩ X = ∅ :=
begin
  have h := hI.subset (inter_subset_left _ X),
  rwa [indep_iff_r_eq_card, r_zero_of_subset_r_zero (inter_subset_right _ _) hX, eq_comm,
    ncard_eq_zero] at h,
end

lemma base_iff_indep_card_eq_r :
  M.base B ↔ M.indep B ∧ B.ncard = M.rk :=
begin
  refine ⟨λ hB, ⟨hB.indep, hB.card⟩ ,
    λ h, base_iff_maximal_indep.mpr ⟨h.1, λ I hI hBI, eq_of_subset_of_ncard_le hBI _⟩⟩,
  rw [h.2], exact hI.card_le_rk,
end

/- Nullity -/

/-- The nullity of a set is its cardinality minus its rank. Maybe not needed... -/
def nullity (M : matroid E) (X : set E) : ℕ :=
  X.ncard - M.r X

lemma nullity_add_rank_eq (M : matroid E) (X : set E) :
  M.nullity X + M.r X = X.ncard :=
by rw [nullity, tsub_add_cancel_of_le (M.r_le_card X)]

lemma cast_nullity (M : matroid E) (X : set E) :
  (M.nullity X : ℤ) = X.ncard - M.r X :=
by rw [←M.nullity_add_rank_eq, nat.cast_add, add_tsub_cancel_right]

lemma nullity_supermod (X Y : set E) :
  M.nullity X + M.nullity Y ≤ M.nullity (X ∩ Y) + M.nullity (X ∪ Y) :=
begin
  zify,
  simp_rw [cast_nullity],
  linarith [M.r_submod X Y, ncard_inter_add_ncard_union X Y],
end

lemma nullity_le_card (M : matroid E) (X : set E) :
  M.nullity X ≤ X.ncard :=
nat.sub_le _ _

lemma nullity_mono (hXY : X ⊆ Y) :
  M.nullity X ≤ M.nullity Y :=
by {zify, simp_rw [cast_nullity], linarith [M.r_add_card_le_r_add_card_of_subset hXY]}

/- -/

end matroid

section from_axioms

lemma r_eq_card_of_subset_of_r_le_card_submod
(r : set E → ℕ) (r_le_card : ∀ X, r X ≤ X.ncard)
(r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y)
{I J : set E} (hIJ : I ⊆ J) (hJ : r J = J.ncard) :
  r I = I.ncard :=
begin
  refine le_antisymm (r_le_card I) _,
  have rdiff := r_le_card (J \ I),

  have h := r_submod I (J \ I),
  have r_empt : r ∅ = 0, simpa using ((r_le_card ∅).antisymm (by simp)),
  rw [inter_diff_self, r_empt, zero_add, union_diff_cancel hIJ, hJ] at h,
  have := ncard_diff_add_ncard_eq_ncard hIJ,
  linarith,
end

lemma extend_to_basis_of_r (r : set E → ℕ) (r_le_card : ∀ X, r X ≤ X.ncard)
(r_mono : ∀ X Y, X ⊆ Y → r X ≤ r Y) (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y)
(I X : set E) (hI : r I = I.ncard) (hIX : I ⊆ X) :
  ∃ J, I ⊆ J ∧ J ⊆ X ∧ r J = J.ncard ∧ r J = r X :=
begin

  obtain ⟨J, ⟨hIJ, hJX, hJ₀⟩, hJ'⟩ :=
   finite.exists_maximal (λ J, I ⊆ J ∧ J ⊆ X ∧ J.ncard ≤ r J) (⟨I, rfl.subset, hIX, hI.symm.le⟩),
  have hJ := hJ₀.antisymm' (r_le_card _),
  refine ⟨J, hIJ, hJX, hJ, hJX.ssubset_or_eq.elim (λ hJX', _) (congr_arg _)⟩,
  obtain ⟨Y, ⟨hJY,hYX,hYr⟩, hYmax⟩ :=
   finite.exists_maximal (λ Y, J ⊆ Y ∧ Y ⊆ X ∧ r Y ≤ r J) ⟨J, rfl.subset, hJX, rfl.le⟩,
  refine hYX.ssubset_or_eq.elim (λ hYX, false.elim _)
    (by {rintro rfl, exact (r_mono _  _ hJX).antisymm hYr,}),
  obtain ⟨e,heX,heY⟩ := exists_of_ssubset hYX,
  have heJ : e ∉ J := λ heJ, heY (mem_of_mem_of_subset heJ hJY),
  have hsm := r_submod (J ∪ {e}) Y,

  rw [inter_distrib_right, singleton_inter_eq_empty.mpr heY, union_empty,
    inter_eq_self_of_subset_left hJY, union_right_comm, union_eq_self_of_subset_left hJY] at hsm,

  have hYe : r Y < r (Y ∪ {e}),
  { rw [lt_iff_not_le],
    intro hYe,
    rw  hYmax (Y ∪ {e})
     ⟨hJY.trans (subset_union_left _ _),union_subset hYX.subset (singleton_subset_iff.mpr heX),
     (hYe.trans hYr)⟩ (subset_union_left _ _) at heY,
    simpa using heY},
  have hJe : r (J ∪ {e}) ≤ r J,
  { refine le_of_not_lt (λ h',  h'.ne _),
    rw ←(hJ' (J ∪ {e}) ⟨subset_union_of_subset_left hIJ _,union_subset hJX (by simpa),_⟩
      (subset_union_left _ _)),
    rwa [union_singleton, ncard_insert_of_not_mem heJ, nat.add_one_le_iff, ←hJ, ←union_singleton]},
  linarith,
end

/-- A function `r` satisfying the rank axioms determines a matroid -/
def matroid_of_r (r : set E → ℕ) (r_le_card : ∀ X, r X ≤ X.ncard)
(r_mono : ∀ X Y, X ⊆ Y → r X ≤ r Y) (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) :
  matroid E :=
matroid_of_indep (λ I, r I = I.ncard)
⟨∅, (r_le_card _).antisymm (by simp)⟩
(λ _ _, r_eq_card_of_subset_of_r_le_card_submod r r_le_card r_submod)
(begin
  intros I J hI hJ hIJ,
  obtain ⟨K,hIK, hKIJ, hK, hrK⟩ :=
   extend_to_basis_of_r r r_le_card r_mono r_submod _ _ hI (subset_union_left _ J),
  refine (ssubset_or_eq_of_subset hIK).elim (λ hss, _) _,
  { refine (exists_of_ssubset hss).imp _,
    rintro e ⟨heK,heI⟩,
    have heJ : e ∈ J, { by_contra, cases (hKIJ heK); tauto },
    refine ⟨heJ, heI, _⟩,
    exact r_eq_card_of_subset_of_r_le_card_submod r r_le_card r_submod
      (insert_subset.mpr ⟨heK, hIK⟩) hK},
  rintro rfl,
  simp_rw [←hI, ←hJ, hrK] at hIJ,
  exact (hIJ.not_le (r_mono _ _ (subset_union_right _ _))).elim,
end)

@[simp] lemma matroid_of_r_apply (r : set E → ℕ) (r_le_card : ∀ X, r X ≤ X.ncard)
(r_mono : ∀ X Y, X ⊆ Y → r X ≤ r Y) (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) :
  (matroid_of_r r r_le_card r_mono r_submod).r = r :=
begin
  ext X,
  simp_rw [matroid_of_r, matroid.eq_r_iff, matroid.basis_iff, matroid_of_indep_apply],
  obtain ⟨I,-,hIX,hI,hIX'⟩ :=
   extend_to_basis_of_r r r_le_card r_mono r_submod ∅ X (by simpa using r_le_card ∅)
    (empty_subset _),
  refine ⟨I, ⟨⟨hI,hIX,λJ hJ hIJ hJX,
    (ssubset_or_eq_of_subset hIJ).elim (λ hIJ',false.elim _) id⟩,
      by rwa [←hIX', eq_comm]⟩⟩,

  have h' := r_mono _ _ hJX,
  have hlt := ncard_lt_ncard hIJ',
  rw [←hI, ←hJ] at hlt,
  linarith,
end

/-- Construction of a matroid from an `int`-valued rank function that is everywhere nonnegative,
  rather than a `nat`-valued one. Useful for defining matroids whose rank function involves
  subtraction. -/
def matroid_of_int_r (r : set E → ℤ) (r_nonneg : ∀ X, 0 ≤ r X) (r_le_card : ∀ X, r X ≤ X.ncard)
(r_mono : ∀ X Y, X ⊆ Y → r X ≤ r Y) (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) :
matroid E :=
matroid_of_r (int.nat_abs ∘ r)
  (λ X, by {zify, convert r_le_card X, rw abs_eq_self, apply r_nonneg})
  (λ X Y hXY, by {zify, convert r_mono X Y hXY, all_goals {rw abs_eq_self, apply r_nonneg}})
  (λ X Y, by {zify, convert r_submod X Y, all_goals {rw abs_eq_self, apply r_nonneg}})

@[simp] lemma matroid_of_int_r_apply (r : set E → ℤ) (r_nonneg : ∀ X, 0 ≤ r X)
(r_le_card : ∀ X, r X ≤ X.ncard) (r_mono : ∀ X Y, X ⊆ Y → r X ≤ r Y)
(r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) (X : set E) :
  ((matroid_of_int_r r r_nonneg r_le_card r_mono r_submod).r X : ℤ) = r X :=
by simpa [matroid_of_int_r] using r_nonneg _



end from_axioms



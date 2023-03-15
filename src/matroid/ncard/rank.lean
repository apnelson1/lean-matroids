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

lemma basis.card (hIX : M.basis I X) : 
  I.ncard = M.r X := 
by {rw [eq_comm, eq_r_iff], exact ⟨_, hIX, rfl⟩}

lemma indep.r (hI : M.indep I) : 
  M.r I = I.ncard := 
eq_r_iff.mpr ⟨I, ⟨hI, subset_refl _, λ _ _, subset_antisymm⟩, rfl⟩

lemma basis.r (hIX : M.basis I X) : 
  M.r I = M.r X := 
by rw [←hIX.card, hIX.indep.r]

lemma indep_iff_r_eq_card : 
  M.indep I ↔ M.r I = I.ncard := 
begin
  refine ⟨indep.r ,λ h, _⟩, 
  obtain ⟨J, hJ, hJI, hJcard⟩ := le_r_iff.mp h.symm.le, 
  suffices hIJ : J = I, rwa ←hIJ, 
  exact eq_of_subset_of_ncard_le hJI hJcard.symm.le,
end 

@[simp] lemma r_empty (M : matroid E) : 
  M.r ∅ = 0 :=
by rw [M.empty_indep.r, ncard_empty] 

lemma r_le_card (M : matroid E) (X : set E) : 
  M.r X ≤ X.ncard :=
r_le_iff.mpr (λ I hI, ncard_le_of_subset)

lemma r_lt_card_of_dep (hX : ¬ M.indep X) : 
  M.r X < X.ncard :=
lt_of_le_of_ne (M.r_le_card X) (by rwa indep_iff_r_eq_card at hX)

lemma r_lt_card_iff_dep :
  M.r X < X.ncard ↔ ¬M.indep X :=
⟨λ h hI, (h.ne hI.r),r_lt_card_of_dep⟩ 

lemma r_mono (M : matroid E) {X Y : set E} (hXY : X ⊆ Y) : 
  M.r X ≤ M.r Y :=
by {simp_rw [r_le_iff, le_r_iff], exact λ I hI hIX, ⟨I,hI,hIX.trans hXY,rfl⟩}

lemma base.r (hB : M.base B) : 
  M.r B = M.rk := 
by {rw [base_iff_basis_univ] at hB, rw hB.r}

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

lemma r_inter_le_r_left (M : matroid E) (X Y : set E) : 
  M.r (X ∩ Y) ≤ M.r X := 
M.r_mono (inter_subset_left X Y)

lemma r_inter_le_r_right (M : matroid E) (X Y : set E) : 
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
by {rw diff_eq, apply r_inter_le_r_left} 

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

/- Probably `finsum` is fight for this  -/

-- lemma r_union_le_add_r_sUnion (M : matroid E) (S : finset (set E)) :
--   M.r (S.bUnion id) ≤ ∑ x in s, f x := 
-- begin
--   set P := λ (S : set (set E)), M.r (⋃₀ S) ≤ ∑ᶠ X in S, M.r X with hP, 
--   refine induction_set_size_insert P (by {rw hP, simp}) (λ X A hA hX, _) _, 
--   rw [hP, sUnion_insert, fin.finsum_in_insert _ hA],
--   exact le_trans (r_union_le_add_r M _ _) (int.add_le_add_left hX _), 
-- end 

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

end matroid

section from_axioms

lemma r_eq_card_of_subset_of_r_le_card_submod (r : set E → ℕ) (r_le_card : ∀ X, r X ≤ X.ncard) 
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

end from_axioms



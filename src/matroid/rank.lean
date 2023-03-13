import matroid.basic

noncomputable theory
open_locale classical
open_locale big_operators

open set 

variables {E : Type*} [fintype E] {M : matroid E} {X Y X' Y' Z I J : set E} {e f x y z : E}

namespace matroid 

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
  (M.r X < X.to_finset.card) ↔ ¬M.indep X :=
begin
  rw [lt_iff_not_le, not_iff_not, indep_iff_r_eq_card],
  exact ⟨(M.r_le_card X).antisymm, λ h, by rw h⟩,
end 

lemma nonempty_of_r_lt_card (hX : M.r X < X.to_finset.card) : 
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

/- Figure this out - are finsets or sets better here? -/

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
  M.r Y ≤ M.r X + (Y \ X).to_finset.card :=
(M.r_le_r_add_r_diff X Y).trans (add_le_add_left (by convert M.r_le_card (Y \ X)) _)
  
lemma r_add_card_le_r_add_card_of_subset (M : matroid E) (hXY : X ⊆ Y) :
  M.r Y + X.to_finset.card ≤ M.r X + Y.to_finset.card :=
begin
  have := M.r_le_r_add_card_diff_of_subset hXY, 
  rw ←to_finset_subset_to_finset at hXY, 
  rw [to_finset_diff] at this, 
  linarith [finset.card_sdiff_add_card_eq_card hXY], 
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
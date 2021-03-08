/- A matroid is defined as a rank function, so this file is the biggest part of the
   matroid API. 
-/

import matroid.axioms  matroid.dual 
import prelim.collections prelim.minmax 
open set 
--open ftype_induction 

open_locale classical 
open_locale big_operators 
noncomputable theory 
----------------------------------------------------------------
namespace matroid 
variables {α : Type}[fintype α]{M : matroid α}{e f x y z : α}{X Y Z X' Y' Z' F B I C C₁ C₂ F₁ F₂ P : set α}
-- probably split up these set notations by section...

section /- rank -/ rank


def rank (M : matroid α) := M.r univ 

/-- rank is nonnegative -/
lemma rank_nonneg (M : matroid α)(X : set α):
  0 ≤ M.r X := 
M.R0 X 

/-- rank is bounded above by size -/
lemma rank_le_size (M : matroid α)(X : set α):
  M.r X ≤ size X := 
M.R1 X 

/-- rank is monotone wrt set inclusion -/
lemma rank_mono (M : matroid α):
  X ⊆ Y → M.r X ≤ M.r Y := 
M.R2 X Y

/-- rank is submodular -/
lemma rank_submod (M : matroid α)(X Y : set α):
  M.r (X ∪ Y) + M.r (X ∩ Y) ≤ M.r X + M.r Y := 
M.R3 X Y 

lemma rank_mono_inter_left (M : matroid α)(X Y : set α): 
  M.r (X ∩ Y) ≤ M.r X := 
M.rank_mono (inter_subset_left X Y)

lemma rank_mono_union_left (M : matroid α)(X Y : set α) : 
  M.r X ≤ M.r (X ∪ Y) := 
M.rank_mono (subset_union_left X Y)

lemma rank_mono_inter_right (M : matroid α)(X Y : set α): 
  M.r (X ∩ Y) ≤ M.r Y := 
M.rank_mono (inter_subset_right X Y)

lemma rank_mono_union_right (M : matroid α)(X Y : set α) : 
  M.r Y ≤ M.r (X ∪ Y) := 
M.rank_mono (subset_union_right X Y)

lemma rank_mono_diff (M : matroid α)(X Y : set α):
  M.r (X \ Y) ≤ M.r X := 
by {rw diff_eq, apply rank_mono_inter_left}

lemma rank_eq_zero_of_le_zero :
  M.r X ≤ 0 → M.r X = 0 := 
λ h, le_antisymm h (M.rank_nonneg X)

lemma rank_zero_of_subset_rank_zero : 
  X ⊆ Y → M.r Y = 0 → M.r X = 0 := 
λ hXY hY, by {apply rank_eq_zero_of_le_zero, rw ←hY, exact rank_mono M hXY}

lemma rank_zero_of_inter_rank_zero (X : set α):
  M.r Y = 0 → M.r (X ∩ Y) = 0 :=
λ hY, by {apply rank_zero_of_subset_rank_zero _ hY, simp }

@[simp] lemma rank_empty (M : matroid α): 
  M.r ∅ = 0 := 
rank_eq_zero_of_le_zero (by {convert M.rank_le_size _, rw size_empty })

lemma rank_lt_size_ne_empty : 
  M.r X < size X → X ≠ ∅ := 
λ h hX, by {rw [hX, size_empty, rank_empty] at h, from lt_irrefl _ h,  }

lemma rank_single_ub (M : matroid α)(e : α):
  M.r {e} ≤ 1 := 
by {rw ←(size_singleton e), exact M.rank_le_size {e}}

lemma rank_le_univ (M : matroid α)(X : set α) : 
  M.r X ≤ M.r univ := 
M.rank_mono (subset_univ X)

lemma rank_compl_univ (M : matroid α): 
  M.r (univᶜ) = 0 := 
by rw [compl_univ, rank_empty]

lemma rank_gt_zero_of_ne :
  M.r X ≠ 0 → 0 < M.r X := 
λ h, lt_of_le_of_ne (M.rank_nonneg X) (ne.symm h)

lemma rank_eq_of_le_supset :
  X ⊆ Y → (M.r Y ≤ M.r X) → M.r X = M.r Y :=
λ h h', (le_antisymm (M.rank_mono h) h') 

lemma rank_eq_of_le_union :
  M.r (X ∪ Y) ≤ M.r X → M.r (X ∪ Y) = M.r X :=
λ h, ((rank_eq_of_le_supset ((subset_union_left X Y))) h).symm

lemma rank_eq_of_le_inter :
  M.r X ≤ M.r (X ∩ Y) →  M.r (X ∩ Y) = M.r X :=
λ h, (rank_eq_of_le_supset (inter_subset_left _ _) h)

lemma rank_eq_of_not_lt_supset :
  X ⊆ Y → ¬(M.r X < M.r Y) → M.r X = M.r Y :=
λ h h', rank_eq_of_le_supset h (int.le_of_not_gt' h')

lemma rank_eq_of_not_lt_union :
  ¬ (M.r X < M.r (X ∪ Y)) → M.r (X ∪ Y) = M.r X :=
λ h', rank_eq_of_le_union (int.le_of_not_gt' h')
@[simp] lemma rank_eq_rank_union_rank_zero (X : set α){Y :set α}(hY : M.r Y = 0):
  M.r (X ∪ Y) = M.r X := 
by {apply rank_eq_of_le_union, linarith [M.rank_nonneg (X ∩ Y ), M.rank_submod X Y],} 

lemma rank_eq_rank_diff_rank_zero (X : set α)(hY : M.r Y = 0): 
  M.r (X \ Y) = M.r X :=
begin
  refine le_antisymm (rank_mono_diff _ _ _) _,
  rw ←rank_eq_rank_union_rank_zero (X \ Y) hY, 
   exact rank_mono _ (λ x hx, by {rw [mem_union, mem_diff ], tauto,}), 
end

lemma rank_zero_of_union_rank_zero :
  M.r X = 0 → M.r Y = 0 → M.r (X ∪ Y) = 0 :=
λ hX hY, by {rw (rank_eq_rank_union_rank_zero _ hY), exact hX }

lemma rank_eq_of_union_eq_rank_subset (Z: set α):
  X ⊆ Y → M.r X = M.r Y → M.r (X ∪ Z) = M.r (Y ∪ Z) := 
begin
  intros hXY hr, apply rank_eq_of_le_supset (subset_union_subset_left X Y Z hXY), 
  have : M.r ((X ∪ Z) ∩ Y) = _ := by rw [inter_distrib_right, subset_iff_inter_eq_left.mp hXY] ,
  have : M.r ((X ∪ Z) ∪ Y) = _ := by rw [union_assoc, union_comm Z Y, ←union_assoc, subset_iff_union_eq_left.mp hXY ],
  linarith [M.rank_submod (X ∪ Z) Y , M.rank_mono_union_left X (Z ∩ Y) ], 
end 

lemma rank_eq_of_union_eq_rank_subsets (hX : X ⊆ X')(hY : Y ⊆ Y')
(hXX' : M.r X = M.r X')(hYY' : M.r Y = M.r Y'):
  M.r (X ∪ Y) = M.r (X' ∪ Y'):=
by rw [rank_eq_of_union_eq_rank_subset Y hX hXX', union_comm, union_comm _ Y',
       rank_eq_of_union_eq_rank_subset _ hY hYY']  



/-
lemma rank_union_eq_of_rank_union_supset_eq {X S T : set α}(hXT : M.r (X ∪ T) = M.r X)
(hST : S ⊆ T):
  M.r (X ∪ S) = M.r X :=
begin
  have : X ∪ S ⊆ X ∪ T := sorry,  
  have := rank_eq_of_union_eq_rank_subset X this,  
  --have := rank_eq_of_union_eq_rank_subset (_ : )  
end
-/

lemma rank_eq_of_inter_union (X Y A : set α):
  M.r (X ∩ A) = M.r X → M.r ((X ∩ A) ∪ Y) = M.r (X ∪ Y) :=
λ h, rank_eq_of_union_eq_rank_subset _ (inter_subset_left _ _) h 
  
lemma rank_eq_of_union_rank_diff_eq (Z : set α)(hX : M.r (X \ Y) = M.r X):
  M.r (Z ∪ (X \ Y)) = M.r (Z ∪ X) := 
by {rw diff_eq at *, rw [union_comm _ X, ← rank_eq_of_inter_union _ Z _ hX, union_comm Z]} 

lemma rank_subadditive (M : matroid α)(X Y : set α) : 
  M.r (X ∪ Y) ≤ M.r X + M.r Y :=
by linarith [M.rank_submod X Y, M.rank_nonneg (X ∩ Y)]

lemma rank_subadditive_sUnion (M : matroid α)(S : set (set α)):
  M.r (⋃₀ S) ≤ ∑ᶠ X in S, M.r X := 
begin
  set P := λ (S : set (set α)), M.r (⋃₀ S) ≤ ∑ᶠ X in S, M.r X with hP, 
  refine induction_set_size_insert P (by {rw hP, simp}) (λ X A hA hX, _) _, 
  rw [hP, sUnion_insert, fin.finsum_in_insert _ hA],
  exact le_trans (rank_subadditive M _ _) (int.add_le_add_left hX _), 
end 

lemma rank_augment_single_ub (M : matroid α)(X : set α)(e : α): 
  M.r (X ∪ {e}) ≤ M.r X + 1 := 
by linarith [rank_subadditive M X {e}, rank_single_ub M e]

lemma rank_eq_add_one_of_ne_aug :
  M.r (X ∪ {e}) ≠ M.r X → M.r (X ∪ {e}) = M.r X + 1 := 
begin
  intro h, apply le_antisymm,
  from (rank_augment_single_ub M X e), 
  from (int.add_one_le_of_lt (lt_of_le_of_ne (rank_mono_union_left M _ _) (ne.symm h))),
end

lemma rank_eq_of_le_aug :
  M.r (X ∪ {e}) ≤ M.r X → M.r (X ∪ {e}) = M.r X :=  
λ h, le_antisymm h (rank_mono_union_left _ _ _) 

lemma rank_diff_subadditive (M : matroid α)(X Y : set α) :
  M.r Y ≤ M.r X + M.r (Y \ X) := 
le_trans (M.rank_mono (by simp)) (rank_subadditive M X (Y \ X))

lemma rank_remove_single_lb (M : matroid α)(X : set α)(e : α):
  M.r X - 1 ≤ M.r (X \ {e}) :=
by linarith [rank_diff_subadditive M {e} X, rank_single_ub M e]

lemma rank_eq_sub_one_of_ne_remove (M : matroid α)(X : set α)(e : α):
  M.r X ≠ M.r (X \ {e}) → M.r (X \ {e}) = M.r X - 1 :=
begin
  intro h, apply le_antisymm  _ (rank_remove_single_lb M X e), 
  apply int.le_sub_one_of_le_of_ne _ (ne.symm h), 
  apply rank_mono_diff, 
end

lemma rank_diff_le_size_diff (M : matroid α)(hXY : X ⊆ Y) :
  M.r Y - M.r X ≤ size Y - size X := 
by linarith [rank_diff_subadditive M X Y, diff_size hXY, M.rank_le_size (Y \ X )]
  

lemma submod_three_sets (M : matroid α)(X Y Y' : set α) :
  M.r (X ∪ (Y ∪ Y')) + M.r (X ∪ (Y ∩ Y')) ≤ M.r (X ∪ Y) + M.r (X ∪ Y') := 
by {have := M.rank_submod (X ∪ Y) (X ∪ Y'), rw [←union_distrib_left, ←union_distrib_union_right] at this, exact this}

lemma submod_three_sets_right (M : matroid α)(X Y Y' : set α) :
  M.r ((Y ∪ Y') ∪ X) + M.r ((Y ∩ Y') ∪ X) ≤ M.r (Y ∪ X) + M.r (Y' ∪ X) := 
by {simp_rw ←(union_comm X), apply submod_three_sets} 

lemma submod_three_sets_disj (M : matroid α)(X Y Y' : set α)(hYY' : Y ∩ Y' = ∅) :
  M.r (X ∪ (Y ∪ Y')) + M.r (X) ≤ M.r (X ∪ Y) + M.r (X ∪ Y') := 
by {have := submod_three_sets M X Y Y', rw [hYY', union_empty] at this, exact this}

/-lemma union_rank_diff_le_rank_diff (M : matroid α)(X Y Z : set α)(hXY : X ⊆ Y):
  M.r (Y ∪ Z) - M.r (X ∪ Z) ≤ M.r Y - M.r X :=
begin
  have := rank_submod M Y Z, 
  have := rank_submod M X Z, 
end -/


theorem rank_augment  {X Z : set α} : (M.r X < M.r Z) → 
  ∃ (z : α), z ∈ Z ∧ M.r X < M.r (X ∪ {z}) := 
let P : set α → Prop := λ X', 
  (M.r X' = M.r X) ∧ (X' ⊆ X ∪ Z) ∧ (∀ (e:α), e ∈ X ∪ Z → M.r (X' ∪ {e}) = M.r X') in  
begin
  intro hXZ, 
  
  by_contra h_con, push_neg at h_con, 
  replace h_con : ∀ (z:α), z ∈ X ∪ Z → M.r (X ∪ {z}) = M.r X := 
  by {
        intros z hz, rw elem_union_iff at hz, cases hz, 
        rw add_elem hz, 
        from (rank_eq_of_le_supset (subset_union_left _ _) (h_con z hz)).symm
        },

  rcases maximal_example_aug P ⟨rfl, ⟨subset_union_left _ _, h_con⟩⟩ 
    with ⟨Y, ⟨hXY,⟨⟨hYX, ⟨hYXZ, h_aug⟩⟩ , hYmax⟩⟩⟩, 
  by_cases Y = X ∪ Z, 
  rw h at hYX,
  linarith [M.rank_mono_union_right X Z],  
  cases elem_diff_ssubset (ssubset_of_subset_ne hYXZ h) with e he,
  rw elem_diff_iff at he, 
  have h_aug_e := h_aug e he.1, 
  have hYe := hYmax e he.2, push_neg at hYe,
  rcases hYe (eq.trans h_aug_e hYX) (union_of_subsets hYXZ (singleton_subset_iff.mpr he.1))
    with ⟨f, ⟨hf, h_aug_ef⟩⟩, 
  replace h_aug_ef := rank_eq_add_one_of_ne_aug h_aug_ef,
  rw union_assoc at h_aug_ef, 
  have h_aug_f := h_aug f hf, 
  
  have hef : ({e} ∩ {f} : set α) = ∅ := inter_distinct_singles
    (λ h, by {rw [h, union_self] at h_aug_ef, linarith}),
  
  linarith [submod_three_sets_disj M Y {e} {f} hef],
end

lemma rank_eq_of_rank_all_insert_eq (hXY : X ⊆ Y) :
  (∀ e : Y, M.r X = M.r (X ∪ {e})) → M.r X = M.r Y := 
begin
  refine (λ h, rank_eq_of_le_supset hXY (by_contra (λ hn, _))),
  obtain ⟨f,hfY,hf⟩ := rank_augment (not_le.mp hn), 
  specialize h ⟨f, hfY⟩, rw [subtype.coe_mk] at h, linarith, 
end  

lemma rank_eq_of_rank_all_insert_le (hXY : X ⊆ Y) :
  (∀ e : Y, M.r (X ∪ {e}) ≤ M.r X) → M.r X = M.r Y := 
begin
  refine (λ h, rank_eq_of_le_supset hXY (by_contra (λ hn, _))),
  obtain ⟨f,hfY,hf⟩ := rank_augment (not_le.mp hn), 
  specialize h ⟨f, hfY⟩, rw [subtype.coe_mk] at h, linarith, 
end  

lemma loopy_rank_zero  (he : (∀ (e:α), e ∈ X → M.r {e} = 0)) : 
  M.r X = 0 :=
begin
  by_contra h, 
  replace h := rank_gt_zero_of_ne h, 
  rcases rank_augment (by linarith [rank_empty M] : M.r ∅ < M.r X) with ⟨f,hf, hf'⟩,
  rw [empty_union, rank_empty, he _ hf] at hf', 
  apply lt_irrefl _ hf', 
end 

end rank 

-- Independence 

section indep

/-- is independent in M; rank equals size -/
def is_indep (M : matroid α) : set α → Prop :=
  λ X, M.r X = size X

/-- independent set type -/ 
def indep (M : matroid α) := {I : set α // M.is_indep I}

instance coe_indep : has_coe (M.indep) (set α) := 
  coe_subtype   


instance fintype_indep : fintype (M.indep) := 
by {unfold indep, apply_instance }


def is_indep_subset_of (M : matroid α)(X : set α) : set α → Prop := 
  λ I, I ⊆ X ∧ M.is_indep I 

def indep_subset_of (M : matroid α)(X : set α) := {I : set α // M.is_indep_subset_of X I}


/-- is dependent in M; negation of independence -/
def is_dep (M : matroid α) : set α → Prop := 
   λ X, ¬(M.is_indep X)

lemma indep_iff_r : 
  M.is_indep X ↔ M.r X = size X := 
by refl 

lemma r_indep :
  M.is_indep X → M.r X = size X :=
indep_iff_r.mp 

lemma dep_iff_r :
  is_dep M X ↔ M.r X < size X := 
by {unfold is_dep, rw indep_iff_r, exact ⟨λ h, (ne.le_iff_lt h).mp (M.rank_le_size X), λ h, by linarith⟩}

--instance coe_coindep : has_coe (coindep M) α := ⟨λ I, I.val⟩  

lemma indep_or_dep (M : matroid α) (X : set α): 
  M.is_indep X ∨ M.is_dep X := 
by {rw [dep_iff_r, indep_iff_r], exact eq_or_lt_of_le (M.rank_le_size X)}

lemma dep_iff_not_indep : 
  M.is_dep X ↔ ¬M.is_indep X := 
by {rw [indep_iff_r, dep_iff_r], exact ⟨λ h, by linarith, λ h, (ne.le_iff_lt h).mp (M.rank_le_size X)⟩}

lemma not_indep_iff_r :
  ¬is_indep M X ↔ M.r X < size X := 
by {rw ←dep_iff_not_indep, apply dep_iff_r, }

lemma indep_iff_not_dep : 
  M.is_indep X ↔ ¬M.is_dep X := 
by {rw dep_iff_not_indep, simp}

lemma coindep_iff_r  :
  (dual M).is_indep X ↔ (M.r Xᶜ = M.r univ) := 
by {unfold is_indep dual, dsimp only, split; {intros h, linarith}}

lemma codep_iff_r  : 
  is_dep (dual M) X ↔ (M.r Xᶜ < M.r univ) := 
by {rw [dep_iff_not_indep, coindep_iff_r], exact ⟨λ h, (ne.le_iff_lt h).mp (rank_le_univ M Xᶜ), λ h, by linarith⟩}
    
lemma not_coindep_iff_r :
  ¬is_indep (dual M) X ↔ (M.r Xᶜ < M.r univ) := 
by rw [←dep_iff_not_indep, codep_iff_r] 

lemma empty_indep (M : matroid α) :
  M.is_indep ∅ :=  
by rw [indep_iff_r, size_empty, rank_empty]

lemma dep_nonempty   (hdep : is_dep M X ):
  X ≠ ∅ := 
λ h, let h' := empty_indep M in by {rw ←h at h', exact hdep h'}

lemma subset_indep : 
  X ⊆ Y → M.is_indep Y → M.is_indep X := 
begin 
  intro hXY, simp_rw indep_iff_r, intro hY, 
  linarith [M.rank_le_size X, M.rank_le_size (Y \ X ), diff_size hXY, rank_diff_subadditive M X Y]
end 

lemma indep_aug : 
  size X < size Y → M.is_indep X → M.is_indep Y → (∃ (e:α), e ∈ Y ∧ e ∉ X ∧ M.is_indep (X ∪ {e})) := 
begin
  simp_rw indep_iff_r,
  intros hXY hIX hIY,
  rcases rank_augment (by linarith : M.r X < M.r Y) with ⟨e,⟨h₁, h₂⟩⟩, 
  have hx : ¬({e} ⊆ X),
  { exact (λ he, by {rw [union_comm, subset_iff_union_eq_left.mp he] at h₂, linarith})}, 
  rw singleton_subset_iff at hx,
  refine ⟨e,⟨h₁,hx,_⟩⟩, 
  have hs := (size_modular X {e}),
  rw [ eq.trans (inter_comm X {e}) (nonmem_disjoint hx), size_empty] at hs, 
  linarith [size_singleton e, M.rank_le_size (X ∪ {e}), int.add_one_le_iff.mpr h₂],  
end

lemma indep_aug_diff : 
  size X < size Y → M.is_indep X → M.is_indep Y  → (∃ (e:α), e ∈ Y \ X  ∧ M.is_indep (X ∪ {e})) := 
λ h₁ h₂ h₃, by {simp_rw elem_diff_iff, simp_rw and_assoc, exact indep_aug h₁ h₂ h₃}

lemma indep_of_indep_aug :
  M.is_indep I → M.r I < M.r (I ∪ {e}) → M.is_indep (I ∪ {e}) :=
begin
  intros hI h, 
  rw indep_iff_r at *, 
  apply le_antisymm (M.rank_le_size _ ),
  refine le_trans (size_insert_ub) _, 
  rw hI at h, convert h, 
end


lemma dep_subset : 
  X ⊆ Y → is_dep M X → is_dep M Y := 
by {intro hXY, repeat {rw dep_iff_not_indep}, contrapose!, exact subset_indep hXY}

lemma empty_indep_r (M : matroid α) :
   M.r ∅ = size (∅ : set α) :=
(empty_indep M)

lemma subset_indep_r : 
  X ⊆ Y → M.r Y = size Y → M.r X = size X := 
λ h, by {have := subset_indep h, rw [indep_iff_r, indep_iff_r] at this, assumption} 


lemma elem_indep_r (he : e ∈ I)(hI : M.is_indep I):
  M.r {e} = 1 := 
begin 
  rw [←singleton_subset_iff] at he, 
  rw [←size_singleton e, ←indep_iff_r], 
  exact subset_indep_r he hI, 
end

instance nonempty_indep : nonempty (M.indep) := 
by {apply nonempty_subtype.mpr, from ⟨∅, M.empty_indep⟩}

lemma indep_of_subset_indep : 
  X ⊆ Y → M.is_indep Y → M.is_indep X := 
begin 
  intro hXY, simp_rw indep_iff_r, intro hY, 
  linarith [M.rank_le_size X, M.rank_le_size (Y \ X ), 
  diff_size hXY, rank_diff_subadditive M X Y]
end 

lemma inter_indep_of_indep_right (X Y : set α):
  M.is_indep Y → M.is_indep (X ∩ Y) :=
λ h, indep_of_subset_indep (inter_subset_right _ _) h 

lemma inter_indep_of_indep_left (X Y : set α):
  M.is_indep X → M.is_indep (X ∩ Y) :=
λ h, indep_of_subset_indep (inter_subset_left _ _) h 

lemma indep_of_union_indep_right :
  M.is_indep (X ∪ Y) → M.is_indep Y :=
λ h, indep_of_subset_indep (subset_union_right _ _) h

lemma indep_of_union_indep_left :
  M.is_indep (X ∪ Y) → M.is_indep X :=
λ h, indep_of_subset_indep (subset_union_left _ _) h 

lemma I3 : 
  size X < size Y → M.is_indep X → M.is_indep Y → (∃ (e:α), e ∈ Y \ X ∧ M.is_indep (X ∪ {e})) := 
  indep_aug_diff 

lemma indep_inter_rank_zero (hI : M.is_indep I)(hX : M.r X = 0): 
   I ∩ X = ∅ :=
begin
  have h := inter_indep_of_indep_left I X hI, 
  rwa [indep_iff_r,rank_zero_of_inter_rank_zero I hX, eq_comm, size_zero_iff_empty] at h, 
end

/-- converts a matroid to an independence family -/
def to_indep_family (M : matroid α) : indep_family α := 
  ⟨M.is_indep, empty_indep M, @indep_of_subset_indep _ _ M, @I3 _ _ M⟩


instance nonempty_indep_subset_of (M : matroid α)(X : set α) : nonempty (indep_subset_of M X) :=
by {apply nonempty_subtype.mpr, exact ⟨∅,⟨empty_subset _, M.empty_indep⟩ ⟩, }

instance fintype_indep_subset_of (M : matroid α)(X : set α) : fintype (indep_subset_of M X) :=
by {unfold indep_subset_of, apply_instance, } 



end indep 

section /-Circuits-/ circuit

/-- is a circuit of M : minimally dependent -/
def is_circuit (M : matroid α) : set α → Prop := 
  λ X, (¬is_indep M X ∧  ∀ Y: set α, Y ⊂ X → M.is_indep Y)

/-- circuit type -/
def circuit (M : matroid α) := { C : set α // M.is_circuit C }

instance coe_circuit : has_coe (M.circuit) (set α) := 
  coe_subtype    

instance fintype_circuit : fintype (M.circuit) := 
by {unfold circuit, apply_instance }

/-- is a cocircuit of M: circuit of the dual -/
def is_cocircuit (M : matroid α) : set α → Prop := 
  is_circuit (dual M)

/-- cocircuit type -/ 
def cocircuit (M : matroid α) := { C : set α // M.is_cocircuit C }

instance coe_cocircuit : has_coe (cocircuit M) (set α) := 
  coe_subtype    
instance fintype_cocircuit : fintype (cocircuit M) := 
by {unfold cocircuit, apply_instance}   

lemma circuit_iff_i : 
  M.is_circuit X ↔ ¬is_indep M X ∧  ∀ Y: set α, Y ⊂ X → M.is_indep Y :=
by rw is_circuit 


lemma circuit_iff_r  (X : set α) :
  M.is_circuit X ↔ (M.r X = size X - 1) ∧ (∀ Y: set α, Y ⊂ X → M.r Y = size Y) := 
begin
  unfold is_circuit,
  rw not_indep_iff_r, simp_rw indep_iff_r, 
  split, rintros ⟨hr, hmin⟩,
  split, rcases nonempty_has_sub_one_size_ssubset (rank_lt_size_ne_empty hr) with ⟨Y, ⟨hY₁, hY₂⟩⟩, specialize hmin Y hY₁,
  linarith [M.rank_mono hY₁.1],  
  intros Y hY, exact hmin _ hY, 
  rintros ⟨h₁, h₂⟩, refine ⟨by linarith, λ Y hY, _ ⟩,  
  from h₂ _ hY, 
end

lemma r_cct  :
  M.is_circuit C → M.r C = size C - 1 := 
λ hC, ((circuit_iff_r C).mp hC).1
  
lemma r_cct_ssub  {C Y : set α} : 
  M.is_circuit C → (Y ⊂ C) → M.r Y = size Y :=
λ hC hYC, (((circuit_iff_r C).mp hC).2 Y hYC)

lemma cocircuit_iff_r  (X : set α):
  M.is_cocircuit X ↔ (M.r Xᶜ = M.r univ - 1) ∧ (∀ Y: set α, Y ⊂ X → M.r Yᶜ = M.r univ) := 
begin 
  simp_rw [is_cocircuit, is_circuit, not_coindep_iff_r, coindep_iff_r],
  split, rintros ⟨h₁, h₂⟩, split, 
  have h_nonempty : X ≠ ∅ := by {intros h, rw [h,compl_empty] at h₁, exact int.lt_irrefl _ h₁}, 
  rcases (nonempty_has_sub_one_size_ssubset h_nonempty) with ⟨Y,⟨hY₁, hY₂⟩⟩ ,
  specialize h₂ _ hY₁,  
  rw [←compl_compl Y, ←compl_compl X, compl_size, compl_size Xᶜ] at hY₂, 
  linarith[M.rank_diff_le_size_diff (compl_subset_compl.mpr hY₁.1)], 
  exact h₂, rintros ⟨h₁, h₂⟩, exact ⟨by linarith, h₂⟩, 
end 

lemma dep_iff_contains_circuit  :
  is_dep M X ↔ ∃ C, M.is_circuit C ∧ C ⊆ X := 
begin
  refine ⟨λ h, _, λ h, _ ⟩, 
  rcases (minimal_example _ h) with ⟨Z,⟨h₁Z,h₂Z, h₃Z⟩⟩, 
  refine ⟨Z, ⟨⟨h₂Z, (λ Y hY, _)⟩, h₁Z⟩⟩, 
  rw indep_iff_not_dep, exact h₃Z Y hY,  
  cases h with C hC, exact dep_subset hC.2 hC.1.1, 
end 

/-- circuits nonempty unless matroid is free -/
instance nonempty_circuit (hM : M.r univ < size univ) : nonempty (M.circuit) := 
begin 
  apply nonempty_subtype.mpr, 
  rw [←dep_iff_r, dep_iff_contains_circuit] at hM, 
  cases hM with C hC, 
  from ⟨C,hC.1⟩, 
end 

/-- cocircuits nonempty unless matroid is loopy -/
instance nonempty_cocircuit (hM : 0 < M.r univ) : nonempty (cocircuit M) := 
begin
  refine matroid.nonempty_circuit (_ : (dual M).r univ < size univ), 
  rw [dual_r, compl_univ, M.rank_empty], linarith, 
end

lemma circuit_dep :
  M.is_circuit C → M.is_dep C := 
λ h, dep_iff_contains_circuit.mpr ⟨C,h,subset_refl _⟩ 

lemma indep_iff_contains_no_circuit : 
  M.is_indep X ↔ ¬∃ C, M.is_circuit C ∧ C ⊆ X :=
by rw [←not_iff_not, ←dep_iff_not_indep, dep_iff_contains_circuit, not_not]


lemma empty_not_cct (M : matroid α): 
  ¬M.is_circuit ∅ := 
by {rw circuit_iff_r, intros h, have := h.1, linarith [rank_empty M, size_empty α]}

lemma nested_circuits_equal (M : matroid α) : 
  C₁ ⊆ C₂ → M.is_circuit C₁ → M.is_circuit C₂ → C₁ = C₂ := 
begin 
  intros hC₁C₂ hC₁ hC₂, 
  rw circuit_iff_r at hC₁ hC₂, 
  by_contra a, 
  linarith [hC₂.2 _ (ssubset_of_subset_ne hC₁C₂ a)],
end 

lemma circuit_not_ssubset_circuit :
  M.is_circuit C₁ → M.is_circuit C₂ → ¬(C₁ ⊂ C₂) :=
  λ hC₁ hC₂ hC₁C₂, ne_of_ssubset hC₁C₂ (nested_circuits_equal M hC₁C₂.1 hC₁ hC₂)

lemma not_circuit_of_ssubset_circuit {X C : set α}(hXC : X ⊂ C)(hC : M.is_circuit C):
  ¬M.is_circuit X := 
by_contra (λ hX, by {rw not_not at hX, exact circuit_not_ssubset_circuit hX hC hXC, })


lemma inter_circuits_ssubset :
  M.is_circuit C₁ → M.is_circuit C₂ → C₁ ≠ C₂ → C₁ ∩ C₂ ⊂ C₁ := 
begin
  intros hC₁ hC₂ hC₁C₂, 
  refine ssubset_of_subset_ne (inter_subset_left _ _) (λ h, _), 
  rw ←subset_iff_inter_eq_left at h, exact hC₁C₂ (nested_circuits_equal M h hC₁ hC₂ ),
end

lemma circuit_elim : 
   C₁ ≠ C₂ → M.is_circuit C₁ → M.is_circuit C₂ → e ∈ C₁ ∩ C₂ → ∃ C, M.is_circuit C ∧ C ⊆ ((C₁ ∪ C₂) \ {e}) := 
begin
  intros hC₁C₂ hC₁ hC₂ he, 
  rw [←dep_iff_contains_circuit, dep_iff_r], 
  have hI : C₁ ∩ C₂ ⊂ C₁ := inter_circuits_ssubset hC₁ hC₂ hC₁C₂, 
  have heα := mem_of_mem_of_subset he (inter_subset_union C₁ C₂),
  have hcalc : M.r ((C₁ ∪ C₂) \ {e}) ≤ size ((C₁ ∪ C₂) \ {e}) -1 := 
  by linarith [M.rank_mono (diff_subset (C₁ ∪ C₂) {e} ), M.rank_submod C₁ C₂, 
        r_cct hC₁, r_cct hC₂, r_cct_ssub hC₁ hI, size_modular C₁ C₂, size_remove_mem heα],
  from int.le_sub_one_iff.mp hcalc,
end 

/-lemma circuit_elemination_subtype  {C₁ C₂ : circuit M} : 
  C₁ ≠ C₂ → e ∈ (C₁ ∩ C₂ : set α) → ∃ (C : circuit M), (C : set α) ⊆ (C₁ ∪ C₂) \ {e} := 
  by{intros hne he, cases circuit_elemination _ C₁.2 C₂.2 he with C hC, use ⟨C, hC.1⟩, exact hC.2, exact λ h, hne (subtype.eq h)}-/

def matroid_to_cct_family (M : matroid α) : cct_family α := 
  ⟨λ X, M.is_circuit X, 
   empty_not_cct M, 
   λ C₁ C₂, circuit_not_ssubset_circuit, 
   λ C₁ C₂ h, circuit_elim ⟩


end circuit

section closure

/-- is spanning in M: closure is univ -/
@[simp] def is_spanning (M : matroid α) : set α → Prop := 
  λ X, M.r X = M.r univ 

/-- X spans Y if the rank of X is the rank of X ∪ Y -/
def spans (M : matroid α) : set α → set α → Prop := 
  λ X Y, M.r (X ∪ Y) = M.r X 

lemma spanning_iff_r :
  M.is_spanning X ↔ M.r X = M.r univ := 
by refl 

lemma spans_iff_r  :
  M.spans X Y ↔ M.r (X ∪ Y) = M.r X :=
by refl 

lemma not_spans_iff_r : 
  ¬M.spans X Y ↔ M.r X < M.r (X ∪ Y) :=
by {rw [spans_iff_r, eq_comm], exact ⟨λ h, lt_of_le_of_ne (rank_mono_union_left M _ _) h, λ h, ne_of_lt h⟩}

lemma spanned_union (M : matroid α){X Y Y' : set α} :
  M.spans X Y → M.spans X Y' → M.spans X (Y ∪ Y') := 
begin
  unfold spans, intros h h', 
  linarith [submod_three_sets M X Y Y', M.rank_mono_union_left X (Y ∩ Y'), M.rank_mono_union_left X (Y ∪ Y')],
end

lemma spanned_union_closed (M : matroid α)(X : set α):
   union_closed (λ Y, spans M X Y) :=
begin
  refine ⟨_, λ Y Y' hY hY', spanned_union M hY hY'⟩, 
  have : M.r (X ∪ ∅) = M.r X := by rw union_empty, assumption, 
end

lemma spans_refl (M : matroid α) (X : set α): 
  M.spans X X :=
by {unfold spans, rw [union_self]} 

lemma spans_subset (M : matroid α): 
  Y ⊆ Y' → M.spans X Y' → M.spans X Y :=
begin
  unfold spans, intros hYY' hXY, 
  linarith [M.rank_mono_union_left X Y,  M.rank_mono (subset_union_subset_right _ _ X hYY')], 
end

lemma spans_rank_zero (X : set α){L : set α}(hL : M.r L = 0):
  M.spans X L := 
by rw [spans_iff_r, rank_eq_rank_union_rank_zero X hL] 

/-- closure of X in M : union of all sets spanned by X -/
def cl (M : matroid α) : set α → set α :=
  λ X, max_of_union_closed (spanned_union_closed M X)

-- cl X is the (unique) maximal set that is spanned by X
lemma cl_iff_max {X F : set α} : 
  M.cl X = F ↔ M.spans X F ∧ ∀ Y, F ⊂ Y → ¬M.spans X Y :=
let huc := spanned_union_closed M X, 
   h_eq := (union_closed_max_iff_in_and_ub huc F) in 
by {dsimp at h_eq, unfold is_maximal at h_eq, rw [h_eq], 
      unfold cl, rw [eq_comm, ←is_max_of_union_closed_iff huc]}
  
-- cl X is also the set spanned by X that contains all sets spanned by X
lemma cl_iff_spanned_ub {X F : set α}:
   M.cl X = F ↔ M.spans X F ∧ ∀ Y, M.spans X Y → Y ⊆ F := 
by {unfold cl, rw [eq_comm, is_max_of_union_closed_iff], refl}

lemma cl_iff_spanned_ub_r {X F : set α}:
   M.cl X = F ↔ M.r (X ∪ F) = M.r X ∧ ∀ Y, (M.r (X ∪ Y) = M.r X) → Y ⊆ F := 
by {unfold cl, rw [eq_comm, is_max_of_union_closed_iff], refl}

lemma cl_is_max :
  M.spans X (M.cl X) ∧ ∀ Y, (M.cl X) ⊂ Y → ¬M.spans X Y :=
cl_iff_max.mp rfl

lemma cl_is_ub :
  ∀ Y, M.spans X Y → Y ⊆ (M.cl X) := 
(cl_iff_spanned_ub.mp rfl).2 

lemma subset_cl (M : matroid α)(X : set α) : 
  X ⊆ M.cl X := 
(cl_iff_spanned_ub.mp rfl).2 _ (spans_refl M X)

lemma spans_cl (M : matroid α)(X : set α) :
  M.spans X (M.cl X) := 
(cl_iff_max.mp rfl).1 

lemma supset_cl (X : set α) :
  ∀ Y, (M.cl X ⊂ Y) → ¬M.spans X Y := 
(cl_iff_max.mp rfl).2

lemma spanned_subset_cl : 
  M.spans X Y → Y ⊆ M.cl X := 
λ h, cl_is_ub Y h 

lemma rank_zero_subset_cl (X : set α){L : set α}(hL : M.r L = 0):
  L ⊆ M.cl X := 
spanned_subset_cl (spans_rank_zero X hL)

lemma subset_cl_iff (X Y: set α) :
  Y ⊆ M.cl X ↔ M.spans X Y := 
⟨λ h, spans_subset M h (spans_cl _ _ ), λ h, spanned_subset_cl h⟩ 

lemma subset_cl_iff_r (X Y : set α) :
  Y ⊆ M.cl X ↔ M.r (X ∪ Y) = M.r X :=
by {rw subset_cl_iff, refl}

lemma spanning_iff_cl_univ (X : set α):
  M.is_spanning X ↔ M.cl X = univ :=
begin
  rw cl_iff_spanned_ub, unfold spans is_spanning, refine ⟨λ h, ⟨_,λ Y hY, _⟩, λ h, _⟩, 
  rw [h, union_univ], apply subset_univ, rw [←h.1, union_univ], 
end   
  
lemma cl_univ (M : matroid α):
  M.cl univ = univ := 
by {rw ←spanning_iff_cl_univ, obviously}

@[simp] lemma rank_cl (M : matroid α)(X : set α) : 
  M.r (cl M X) = M.r X := 
begin
  have : M.r (X ∪ M.cl X) = M.r X := M.spans_cl X,
  linarith [M.rank_mono_union_right X (M.cl X), M.rank_mono (M.subset_cl X)], 
end 

lemma union_cl_rank_left (M : matroid α)(X Y : set α) :
  M.r ((M.cl X) ∪ Y) = M.r (X ∪ Y) := 
by {rw eq_comm, exact rank_eq_of_union_eq_rank_subset _ (subset_cl _ _) (rank_cl _ _).symm}
  
lemma union_cl_rank_right (M : matroid α)(X Y : set α) :
  M.r (X ∪ (M.cl Y)) = M.r (X ∪ Y) :=
by {rw [union_comm, union_comm _ Y], apply union_cl_rank_left} 

lemma cl_idem (M : matroid α)(X : set α) :
  cl M (cl M X) = cl M X := 
begin
  rw cl_iff_spanned_ub, refine ⟨by apply spans_refl, λ Y hY, _⟩,  
  rw subset_cl_iff, unfold spans, unfold spans at hY, 
  apply rank_eq_of_le_union, 
  linarith [M.rank_cl X, M.union_cl_rank_left X Y], 
end

lemma spans_iff_cl_spans :
  M.spans X Y ↔ M.spans (M.cl X) Y :=
begin   
  repeat {rw spans_iff_r}, 
  rw [rank_eq_of_union_eq_rank_subset, rank_cl],  
  apply subset_cl, exact (rank_cl _ _).symm,  
end

lemma cl_monotone (M : matroid α):
  X ⊆ Y → M.cl X ⊆ M.cl Y :=
λ h, by {rw subset_cl_iff_r, apply rank_eq_of_le_union, 
          rw [union_cl_rank_right, union_comm, subset_iff_union_eq_left.mp h]}
  
lemma nonmem_cl_iff_r :
  e ∉ M.cl X ↔ M.r (X ∪ {e}) = M.r X + 1 :=
begin
  rw [←singleton_subset_iff, subset_cl_iff_r], refine ⟨λ h, _, λ _, λ _, by linarith⟩, 
  linarith [rank_augment_single_ub M X e, 
  int.add_one_le_iff.mpr ((ne.symm h).le_iff_lt.mp (rank_mono_union_left M X {e}))],
end

lemma mem_cl_iff_r : 
  e ∈ M.cl X ↔ M.r (X ∪ {e}) = M.r X := 
by rw [←singleton_subset_iff, subset_cl_iff_r]

lemma mem_cl_iff_spans :
  e ∈ M.cl X ↔ M.spans X {e} :=
by rw [spans_iff_r,mem_cl_iff_r]

lemma nonmem_cl_iff_nonspans :
  e ∉ M.cl X ↔ ¬M.spans X {e} :=
⟨λ h, λ hn, h (mem_cl_iff_spans.mpr hn), λ h, λ hn, h (mem_cl_iff_spans.mp hn)⟩

lemma rank_removal_iff_closure (X : set α)(e : α)(h : e ∈ X):
  M.r (X \ {e}) = M.r X ↔ e ∈ M.cl (X \ {e}) :=
by rw [mem_cl_iff_r, remove_add_elem h, eq_comm]
  

lemma cl4 (M : matroid α)(X : set α)(e f : α) : 
  e ∈ M.cl (X ∪ {f}) \ M.cl X  → f ∈ M.cl (X ∪ {e}) \ M.cl X := 
begin 
  repeat {rw [elem_diff_iff, nonmem_cl_iff_r, mem_cl_iff_r]}, 
  rw union_right_comm, refine λ h, ⟨_,_⟩, 
  apply rank_eq_of_le_union, linarith [rank_augment_single_ub M X f],  
  cases h with h1 h2, 
  linarith [h2, rank_augment_single_ub M X f, rank_mono_union_left M (X ∪ {e}) {f}],  
end


end closure 


section /-Flats-/ flat

/-- set for which all proper supersets have larger rank -/
def is_flat (M : matroid α) : set α → Prop := 
  λ F, ∀ (X : set α), F ⊂ X → M.r F < M.r X

/-- subtype of flats of M -/
def flat (M : matroid α) := { F : set α // M.is_flat F }  

instance coe_flat : has_coe (M.flat) (set α) := 
  coe_subtype   
  
instance fintype_flat : fintype (flat M) := 
by {unfold flat, apply_instance }


/-- flat of rank k -/
def is_rank_k_flat (M : matroid α) (k : ℤ) : set α → Prop := 
  λ F, M.is_flat F ∧ M.r F = k 

/-- the unique rank zero flat -/
def loops : matroid α → set α := 
  λ M, M.cl ∅ 

lemma loops_def :
  M.loops = M.cl ∅ := 
rfl 

/-- is a rank -one flat -/
def is_point (M : matroid α) : set α → Prop := 
  λ F, M.is_rank_k_flat 1 F


/-- is a rank-two flat -/
def is_line (M : matroid α) : set α → Prop := 
  λ F, M.is_rank_k_flat 2 F

/-- is a rank-three flat -/
def is_plane (M : matroid α) : set α → Prop := 
  λ F, M.is_rank_k_flat 3 F

/-- flat of rank r M - 1 -/
def is_hyperplane (M : matroid α) : set α → Prop := 
  λ H, M.is_rank_k_flat (M.r univ - 1) H 

def point (M : matroid α): Type := {P : set α // M.is_point P}

instance point_fin : fintype M.point := 
by {unfold point, apply_instance}

instance point_coe : has_coe M.point (set α) := ⟨subtype.val⟩ 

def line (M : matroid α): Type := {L : set α // M.is_line L}

instance line_fin : fintype M.line := 
by {unfold line, apply_instance}

def plane (M : matroid α): Type := {P : set α // M.is_plane P}

instance plane_fin : fintype M.plane := 
by {unfold plane, apply_instance}


lemma rank_loops (M: matroid α): 
  M.r (M.loops) = 0 := 
by rw [loops, rank_cl, rank_empty]

lemma rank_zero_iff_subset_loops :
  M.r X = 0 ↔ X ⊆ M.loops :=
begin
  refine ⟨λ h, _, λ h, rank_eq_zero_of_le_zero _ ⟩,  
  rw [loops, subset_cl_iff_r], 
  simp, from h, 
  convert M.rank_mono h, 
  from eq.symm (rank_loops M), 
end

lemma spans_loops (M : matroid α)(X : set α):
  M.spans X M.loops := 
spans_rank_zero X (rank_loops M)

lemma loops_subset_cl (M : matroid α)(X : set α):
  M.loops ⊆ M.cl X := 
rank_zero_subset_cl X (rank_loops M)

lemma rank_zero_iff_cl_eq_loops :
  M.r X = 0 ↔ M.cl X = M.loops := 
begin
  rw rank_zero_iff_subset_loops, 
  refine ⟨λ h, subset.antisymm _ (M.loops_subset_cl _), λ h, _⟩, 
  { rw [loops_def] at *, rw [← M.cl_idem ∅], exact M.cl_monotone h,  }, 
  rw ←h, 
  exact subset_cl M X, 
end

lemma flat_iff_r  (X : set α) :
  M.is_flat X ↔ ∀ Y, X ⊂ Y → M.r X < M.r Y := 
by refl 

lemma cl_is_flat (M : matroid α) (X : set α): 
  M.is_flat (cl M X) := 
begin
  rw flat_iff_r, intros Y hY, have hne := cl_is_max.2 _ hY, 
  rw [spans_iff_cl_spans, spans_iff_r] at hne, 
  rw ←subset_iff_union_eq_left.mp hY.1, 
  from lt_of_le_of_ne (M.rank_mono_union_left (cl M X) Y) (ne.symm hne), 
end

lemma flat_iff_own_cl :
  M.is_flat F ↔ M.cl F = F :=
begin
  refine ⟨λ h, _, λ h, by {have := cl_is_flat M F, rw h at this, exact this}⟩,
  rw [cl_iff_max, spans_iff_r], simp_rw not_spans_iff_r,  
  from ⟨by rw union_self, λ Y hFY, lt_of_lt_of_le (h Y hFY) (by {rw union_comm, apply rank_mono_union_left})⟩,
end 

lemma loops_subset_flat (M : matroid α)(hF : M.is_flat F):
  M.loops ⊆ F := 
by {rw ←flat_iff_own_cl.mp hF, apply loops_subset_cl}


lemma flat_iff_is_cl : 
  M.is_flat  F ↔ ∃ X : set α, cl M X = F := 
⟨λ h, ⟨F, flat_iff_own_cl.mp h⟩, λ h, 
    by {cases h with X hX, rw flat_iff_own_cl, rw ←hX, apply cl_idem}⟩


lemma subset_flat (X F : set α):
  X ⊆ F → M.is_flat F → M.cl X ⊆ F :=
begin
  rw flat_iff_own_cl, 
  intros hXF hF, 
  rw ←hF, apply cl_monotone _ hXF, 
end

lemma flat_iff_add_r :
  M.is_flat F ↔ ∀ e, e ∉ F → M.r F < M.r (F ∪ {e}) :=
begin
  rw flat_iff_r, 
  refine ⟨λ h, λ e he, h _ (ssub_of_add_nonmem he), λ h, λ Y hY, _⟩,
  cases add_from_nonempty_diff.mp hY with e he, 
  exact lt_of_lt_of_le (h e he.1) (M.rank_mono he.2), 
end

lemma flat_iff_add :
  M.is_flat F ↔ ∀ (e : α), e ∉ F → ¬M.spans F {e} := 
by {rw [flat_iff_add_r], simp_rw not_spans_iff_r}

lemma fullrank_flat_is_univ :
  M.is_flat F → M.r F = M.r univ → F = univ := 
begin
  intros hF hFr, 
  rw [flat_iff_own_cl] at hF, 
  rw [←hF, ←spanning_iff_cl_univ], 
  from hFr, 
end

lemma flats_eq_of_nested_ge_rank 
(hF₁ : M.is_flat F₁)(hF₂ : M.is_flat F₂)(hF₁F₂ : F₁ ⊆ F₂)(hr : M.r F₂ ≤ M.r F₁):
  F₁ = F₂ :=
begin
  suffices h' : F₂ ⊆ F₁, exact subset.antisymm hF₁F₂ h', 
  by_contra hn, 
  rw [subset_def] at hn, 
  push_neg at hn, 
  obtain ⟨x, h₂, h₁⟩ := hn, 
  linarith [
    flat_iff_add_r.mp hF₁ _ h₁, 
    M.rank_mono (union_subset hF₁F₂ (singleton_subset_iff.mpr h₂))], 
end

lemma hyperplane_iff_r  (X : set α) :
  M.is_hyperplane X ↔ M.r X = M.r univ - 1 ∧ ∀ Y, X ⊂ Y → M.r Y = M.r univ := 
begin
  unfold is_hyperplane is_rank_k_flat, rw flat_iff_r, 
  refine ⟨λ h, ⟨h.2, λ Y hXY, _ ⟩, λ h, ⟨λ Y hXY, _, h.1⟩ ⟩,
  have := h.1 Y hXY, rw h.2 at this, linarith [rank_le_univ M Y],  
  rw [h.1,h.2 Y hXY], exact sub_one_lt _,   
end

lemma hyperplane_iff_maximal_nonspanning  (X : set α): 
  M.is_hyperplane X ↔ ¬M.is_spanning X ∧ ∀ (Y: set α), X ⊂ Y → M.is_spanning Y :=
begin
  rw hyperplane_iff_r, split, 
  intro h, simp only [is_spanning], split, linarith [h.2],
  intros Y hXY, linarith [h.2 Y hXY, h.2, rank_le_univ M Y],
  simp only [is_spanning], 
  refine λ h, ⟨_,h.2⟩, cases h with h1 h2,  
  rcases ne_univ_has_add_one_size_ssupset (λ h', by {rw h' at h1, from h1 rfl} : X ≠ univ) with ⟨Y,hY₁, hY₂⟩,
  linarith [rank_diff_le_size_diff M hY₁.1, h2 _ hY₁, 
            int.le_sub_one_of_le_of_ne (rank_le_univ M X) h1],   
end 

lemma hyperplane_iff_maximal_subflat  (H : set α):
  M.is_hyperplane H ↔ H ≠ univ ∧ M.is_flat H ∧ (∀ X, M.is_flat X → H ⊂ X → X = univ) := 
begin
  refine ⟨λ h, ⟨λ hH, _,⟨h.1, λ X hX hHX, _⟩⟩, λ h, ⟨h.2.1,_⟩⟩,  
  rw [hH, hyperplane_iff_r] at h, linarith, 
  cases h with hHf hHr, 
  rw flat_iff_r at hHf, 
  rw [←(flat_iff_own_cl.mp hX), ←spanning_iff_cl_univ, is_spanning], 
  linarith [hHf _ hHX, rank_le_univ M X],   
  
  rcases h with ⟨h_univ, h_flat, hmax⟩, 
  by_cases h1 : M.r H ≤ M.r univ - 2, 
  rcases ne_univ_has_add_one_size_ssupset_element h_univ with ⟨e, he₁, he₂⟩,
  have := hmax (cl M (H ∪ {e})) (cl_is_flat _ _) (subset.lt_of_lt_of_le he₁ _),
  rw [←spanning_iff_cl_univ, spanning_iff_r] at this,  
  linarith [rank_augment_single_ub M H e],
  apply subset_cl, 
  push_neg at h1, 

  by_cases h2: (M.r H < M.r univ), 
  from le_antisymm (int.le_sub_one_of_lt h2) (by linarith only [h1]), 

  have : M.r H = M.r univ := by linarith [rank_le_univ M H],
  from false.elim (h_univ (fullrank_flat_is_univ h_flat this)), 
end

lemma cocircuit_iff_compl_hyperplane  (X : set α): 
  M.is_cocircuit X ↔ M.is_hyperplane Xᶜ := 
begin
  rw [cocircuit_iff_r, hyperplane_iff_r], 
  refine ⟨λ h, ⟨h.1,λ Y hXY, _⟩ , λ h, ⟨h.1,λ Y hXY, h.2 _ (scompl_subset_compl.mpr hXY)⟩⟩, 
  rw [←(h.2 _ (scompl_subset_comm.mp hXY)), compl_compl], 
end

lemma inter_flats_is_flat (M : matroid α) (F₁ F₂ : set α) :
  M.is_flat F₁ → M.is_flat F₂ → M.is_flat (F₁ ∩ F₂) := 
begin 
  repeat {rw [flat_iff_add]}, simp_rw ←nonmem_cl_iff_nonspans, 
  intros h₁ h₂ e he, rw nonmem_inter_iff at he, cases he, 
  exact λ h, (h₁ e he) (mem_of_mem_of_subset h (cl_monotone M (inter_subset_left F₁ F₂))), 
  exact λ h, (h₂ e he) (mem_of_mem_of_subset h (cl_monotone M (inter_subset_right F₁ F₂))), 
end

/-- is both a circuit and a hyperplane -/
def is_circuit_hyperplane (M : matroid α)(C : set α) := 
  M.is_circuit C ∧ M.is_hyperplane C 

lemma circuit_hyperplane_rank (hC : is_circuit_hyperplane M C) :
  M.r C = M.r univ - 1 := 
by {simp_rw [is_circuit_hyperplane, hyperplane_iff_r] at hC, from hC.2.1}

lemma circuit_hyperplane_size (hC : is_circuit_hyperplane M C) :
  size C = M.r univ := 
by {have := circuit_hyperplane_rank hC, simp_rw [is_circuit_hyperplane, circuit_iff_r] at hC, linarith [hC.1.1]}

lemma circuit_hyperplane_rank_size (hC : is_circuit_hyperplane M C) :
  M.r C = size C - 1 := 
by linarith [circuit_hyperplane_size hC, circuit_hyperplane_rank hC]

lemma circuit_hyperplane_ssubset_rank {C X : set α}(hC : is_circuit_hyperplane M C):
  X ⊂ C → M.r X = size X := 
λ hXC, by {simp_rw [is_circuit_hyperplane, circuit_iff_r] at hC, from hC.1.2 _ hXC,}

lemma circuit_hyperplane_ssupset_rank {C X : set α}(hC : is_circuit_hyperplane M C) :
  C ⊂ X → M.r X = M.r univ := 
λ hXC, by {simp_rw [is_circuit_hyperplane, hyperplane_iff_r] at hC, from hC.2.2 _ hXC,}

lemma circuit_hyperplane_dual :
  M.is_circuit_hyperplane C ↔ (dual M).is_circuit_hyperplane Cᶜ := 
begin
  simp_rw [is_circuit_hyperplane, ←cocircuit_iff_compl_hyperplane, is_cocircuit],  
  rw [dual_dual, ←is_cocircuit, cocircuit_iff_compl_hyperplane, compl_compl, and_comm], 
end


--lemma closure_eq_iff_flat  {X F : set α} : 
--  cl M X = F ↔ X ⊆ F ∧ is_flat M F ∧ ∀ F', is_flat 

end flat

section loopnonloop
/-- is a rank-zero element -/
def is_loop (M : matroid α) : α → Prop := 
  λ e, M.r {e} = 0 

/-- is a rank-one element -/
def is_nonloop (M : matroid α) : α → Prop := 
  λ e, M.r {e} = 1 

/-- is a loop of the dual -/
def is_coloop (M : matroid α) : α → Prop := 
  is_loop (dual M) 

/-- is not a coloop of the dual -/
def is_noncoloop (M : matroid α) : α → Prop := 
  is_coloop (dual M)

lemma nonloop_iff_r :
  M.is_nonloop e ↔ M.r {e} = 1 := 
iff.rfl 

lemma loop_iff_r :
  M.is_loop e ↔ M.r {e} = 0 := 
iff.rfl 

lemma loop_iff_circuit :
  M.is_loop e ↔ M.is_circuit {e} :=
by simp [loop_iff_r, circuit_iff_r, size_singleton, ssubset_singleton_iff_empty] 

lemma nonloop_iff_indep :
  M.is_nonloop e ↔ M.is_indep {e} := 
by rw [is_nonloop, indep_iff_r, size_singleton] 

lemma rank_nonloop :
  M.is_nonloop e → M.r {(e : α)} = 1 :=
by {unfold is_nonloop, from λ h, h}

lemma rank_loop :
  M.is_loop e → M.r {e} = 0 :=
by {unfold is_loop, from λ h, h}

lemma cl_loop_eq_loops (he : M.is_loop e):
  M.cl {e} = M.loops := 
rank_zero_iff_cl_eq_loops.mp (rank_loop he)

lemma loop_iff_mem_loops  : 
  M.is_loop e ↔ e ∈ M.loops := 
by {simp_rw [is_loop, ←singleton_subset_iff], from rank_zero_iff_subset_loops}  

lemma nonloop_iff_not_elem_loops : 
  M.is_nonloop e ↔ e ∉ M.loops := 
begin
  simp_rw [is_nonloop, ←singleton_subset_iff, ←rank_zero_iff_subset_loops], 
  refine ⟨λ h h', by linarith, λ h, _⟩, 
  linarith [rank_single_ub M e, rank_gt_zero_of_ne h], 
end

lemma nonloop_iff_not_loop  : 
  M.is_nonloop e ↔ ¬ M.is_loop e := 
begin 
  unfold is_loop is_nonloop, refine ⟨λ h, _ ,λ h, _⟩,rw h ,
  simp only [not_false_iff, one_ne_zero], 
  have := M.rank_le_size {e}, rw size_singleton at this,       
  linarith [(ne.le_iff_lt (ne.symm h)).mp (M.rank_nonneg {e})],  
end

lemma loop_iff_not_nonloop  : 
  M.is_loop e ↔ ¬ M.is_nonloop e := 
by simp [nonloop_iff_not_loop]

lemma loop_or_nonloop (M : matroid α)(e : α):
  M.is_loop e ∨ M.is_nonloop e :=
by {rw [loop_iff_not_nonloop], tauto}

lemma rank_eq_rank_insert_loop (X : set α)(he : M.is_loop e):
  M.r (X ∪ {e}) = M.r X := 
rank_eq_rank_union_rank_zero _ (loop_iff_r.mp he)

lemma rank_eq_rank_remove_loop (X : set α)(he : M.is_loop e):
  M.r (X \ {e}) = M.r X := 
rank_eq_rank_diff_rank_zero _ (loop_iff_r.mp he)

lemma nonloop_of_one_le_rank (h : 1 ≤ M.r {e}): 
  M.is_nonloop e :=
by {rw [nonloop_iff_r, eq_comm], exact le_antisymm h (by {convert M.rank_le_size _, simp, })} 

lemma nonloop_of_rank_lt_insert (h : M.r X < M.r (X ∪ {e})):
  M.is_nonloop e :=
by_contra (λ hn,
  by {rw rank_eq_rank_insert_loop _ (loop_iff_not_nonloop.mpr hn) at h, exact lt_irrefl _ h,})

lemma coloop_iff_r  (e : α) :
  M.is_coloop e ↔ M.r {e}ᶜ = M.r univ - 1 := 
begin
  unfold is_coloop is_loop, rw [dual_r,size_singleton],
  exact ⟨λh, by linarith,λ h, by linarith⟩,   
end

lemma coloop_iff_r_less  (e : α) :
  M.is_coloop e ↔ M.r {e}ᶜ < M.r univ := 
begin
  unfold is_coloop is_loop, rw [dual_r,size_singleton],
  refine ⟨λh,by linarith,λ h,_⟩, 
  have := rank_diff_le_size_diff M (subset_univ {e}ᶜ), 
  rw [←size_compl, size_singleton] at this, 
  linarith [int.le_sub_one_iff.mpr h],
end

lemma point_eq_cl_mem 
(hP : M.is_point P)(he : M.is_nonloop e)(heP : e ∈ P):
  M.cl {e} = P := 
begin
  apply flats_eq_of_nested_ge_rank (M.cl_is_flat {e}) hP.1,
  { rw ← singleton_subset_iff at heP, 
    rw ← flat_iff_own_cl.mp hP.1,  
    apply M.cl_monotone heP,},  
  rw [hP.2, rank_cl, rank_nonloop he], 
end
  

/-- nonloop as subtype -/
def nonloop (M : matroid α) : Type := { e : α // is_nonloop M e}

instance coe_nonloop : has_coe (nonloop M) (α) := ⟨λ e, e.val⟩  
--def noncoloop (M : matroid α) : Type := { e : α // is_nonloop (dual M) e}

instance fin_nonloop : fintype M.nonloop := 
by {unfold nonloop, apply_instance}

lemma eq_nonloop_coe (h : M.is_nonloop e): 
  e = coe (⟨e, h⟩ : M.nonloop) := 
rfl 

lemma rank_coe_nonloop (e : nonloop M) : 
  M.r {(e : α)} = 1 := 
rank_nonloop (e.2)

lemma coe_nonloop_indep (e : nonloop M) :
  M.is_indep {(e : α)} := 
by {rw [indep_iff_r], simp only [size_singleton, coe_coe], apply rank_coe_nonloop e,}

lemma rank_two_nonloops_lb  (e f : nonloop M) :
  1 ≤ M.r ({e,f}) := 
begin
  rw ←union_singletons_eq_pair, 
  linarith [rank_coe_nonloop e, M.rank_mono_union_left {e} {f}],
end 

lemma rank_two_nonloops_ub  (e f : nonloop M) : 
  M.r ({e,f}) ≤ 2 := 
begin
  rw ←union_singletons_eq_pair, 
  linarith [rank_coe_nonloop e, rank_coe_nonloop f, 
    M.rank_nonneg ({e} ∩ {f}), M.rank_submod {e} {f}], 
end 

/-- a version of rank_augment where the conclusion asserts that z is a nonloop -/
theorem rank_augment_nonloop (h : M.r X < M.r Z):
  ∃ (z ∈ Z), M.is_nonloop z ∧ M.r X < M.r (X ∪ {z}) := 
begin
  obtain ⟨z, hz, hr⟩ := rank_augment h, 
  refine ⟨z,hz, nonloop_iff_not_loop.mpr (λ hz', _), hr⟩, 
  rw rank_eq_rank_insert_loop _ hz' at hr, 
  exact lt_irrefl _ hr, 
end

end loopnonloop

section /-Bases-/ basis


/-- B is a basis of X : an independent subset of X spanning X -/
def is_basis_of (M : matroid α)(B X : set α) : Prop := 
  B ⊆ X ∧ M.r B = size B ∧ M.r B = M.r X 

/-- B is a basis of M: an independent set spanning M -/
def is_basis (M : matroid α)(B : set α) : Prop := 
  M.is_basis_of B univ 

/-- basis type -/
def basis (M : matroid α) := {B : set α // M.is_basis B}

instance coe_subtype_basis : has_coe (M.basis) (set α) :=
  coe_subtype

instance finite_basis : fintype (M.basis) := 
by {unfold basis, apply_instance }

/-- basis of set X type -/
def basis_of (M : matroid α)(X : set α) := {B : set α // M.is_basis_of B X}

instance coe_subtype_basis_of (X : set α) : has_coe (M.basis_of X) (set α) :=
  coe_subtype

instance fintype_basis_of (X : set α) : fintype (M.basis_of X) := 
by {unfold basis_of, apply_instance }



lemma size_basis_of  {B X : set α}:
  M.is_basis_of B X → size B = M.r X :=
  λ h, by {rw is_basis_of at h, linarith}

lemma size_basis :
  M.is_basis B → size B = M.r univ := 
size_basis_of 

lemma bases_of_equicardinal (M : matroid α){B₁ B₂ X: set α}:
  M.is_basis_of B₁ X → M.is_basis_of B₂ X → size B₁ = size B₂ := 
λ h₁ h₂, by rw[size_basis_of h₁, size_basis_of h₂]

lemma bases_equicardinal (M : matroid α){B₁ B₂ : set α}:
  M.is_basis B₁ → M.is_basis B₂ → size B₁ = size B₂ := 
bases_of_equicardinal M 

lemma basis_iff_r  :
  M.is_basis B ↔ M.r B = size B ∧ M.r B = M.r univ :=
⟨λ h, h.2, λ h, ⟨subset_univ B,h⟩⟩

/-- is a basis of the dual -/
def is_cobasis (M : matroid α): set α → Prop := 
  λ B, (dual M).is_basis B 

def cobasis (M : matroid α) := {B : set α // M.is_cobasis B}

@[simp] lemma cobasis_iff  :
  M.is_cobasis B ↔ (dual M).is_basis B :=
by rw is_cobasis

@[simp] lemma basis_of_iff_augment : 
  M.is_basis_of B X ↔ B ⊆ X ∧ M.r B = size B ∧ ∀ (e:α), e ∈ X → M.r (B ∪ {e}) = M.r B := 
begin
  refine ⟨λ h, ⟨h.1,⟨h.2.1,λ e he, _⟩⟩, λ h, ⟨h.1,⟨h.2.1,_⟩⟩⟩, 
  { linarith [h.2.2, 
      M.rank_mono (union_of_subsets h.1 (singleton_subset_iff.mpr he)), 
      M.rank_mono (subset_union_left B {e})]}, 
  refine rank_eq_of_not_lt_supset h.1 (λ hBX, _), 
  cases rank_augment hBX with e he, 
  linarith [h.2.2 e he.1, he.2],   
end

lemma basis_iff_augment :
  M.is_basis B ↔ M.r B = size B ∧ ∀ (e:α), M.r (B ∪ {e}) = M.r B := 
begin
  unfold is_basis, rw basis_of_iff_augment, 
  refine ⟨λ h, ⟨h.2.1,λ e, h.2.2 e (mem_univ e)⟩, λ h, ⟨subset_univ B, ⟨h.1,λ e he,h.2 e⟩⟩ ⟩, 
end

lemma basis_of_iff_augment_i : 
  M.is_basis_of B X ↔ B ⊆ X ∧ M.is_indep B ∧ ∀ (e:α), e ∈ X \ B → ¬M.is_indep (B ∪ {e}) :=
begin
  rw basis_of_iff_augment, 
  refine ⟨λ h, ⟨h.1,⟨h.2.1,λ e he hi, _⟩⟩, λ h, ⟨h.1,⟨h.2.1,λ e he, _⟩ ⟩⟩, 
  rw indep_iff_r at hi, 
  rw elem_diff_iff at he, 
  linarith [h.2.2 e he.1, size_insert_nonmem he.2], 
  by_cases heB: e ∈ B, 
  rw (add_elem heB), 
  have : e ∈ X \ B := by {rw elem_diff_iff, from ⟨he,heB⟩},
  have := h.2.2 _ this, 
  rw not_indep_iff_r at this, 
  have hi := h.2.1, rw indep_iff_r at hi, 
  linarith [size_insert_nonmem heB, M.rank_mono (subset_union_left B {e})], 
end 

lemma basis_iff_augment_i : 
  is_basis M B ↔ M.is_indep B ∧ ∀ (e:α), e ∉ B → ¬M.is_indep (B ∪ {e}) := 
begin
  simp_rw [is_basis, basis_of_iff_augment_i, ←mem_compl_iff, univ_diff], 
  from ⟨λ h, ⟨h.2.1,λ e he, h.2.2 _ he⟩, λ h, ⟨subset_univ B, h⟩⟩, 
end

lemma basis_of_iff_indep_full_rank {B X : set α} :
  M.is_basis_of B X ↔ B ⊆ X ∧ M.is_indep B ∧ size B = M.r X := 
begin
  simp_rw [is_basis_of, indep_iff_r], 
  refine ⟨λ h, ⟨h.1, ⟨_,_⟩⟩, λ h, ⟨h.1,⟨_,_⟩⟩⟩; 
  linarith, 
end

lemma basis_iff_indep_full_rank :
  M.is_basis B ↔ M.is_indep B ∧ size B = M.r univ :=
begin
  simp_rw [basis_iff_r, indep_iff_r], 
  refine ⟨λ h, ⟨h.1, _⟩, λ h, ⟨h.1,_⟩⟩;
  linarith, 
end

lemma basis_is_indep : 
  M.is_basis B → M.is_indep B := 
  λ h, (basis_iff_indep_full_rank.mp h).1 

lemma cobasis_iff_r :
  M.is_cobasis B ↔ M.r Bᶜ = size Bᶜ ∧ M.r Bᶜ = M.r univ := 
begin
  simp_rw [is_cobasis, basis_iff_r, dual],
  refine ⟨λ _, ⟨_,_⟩, λ _, ⟨_,_⟩⟩;
  linarith [size_compl B, rank_compl_univ M], 
end

lemma cobasis_iff_compl_basis :
  M.is_cobasis B ↔ M.is_basis Bᶜ := 
by rw [cobasis_iff_r, basis_iff_r] 

lemma compl_cobasis_iff_basis :
  M.is_cobasis Bᶜ ↔ M.is_basis B := 
by rw [cobasis_iff, ←cobasis_iff_compl_basis, cobasis_iff, dual_dual]

lemma basis_exchange (M : matroid α){B₁ B₂ : set α}(hB₁ : M.is_basis B₁)
(hB₂ : M.is_basis B₂)(he : e ∈ B₁ \ B₂):
  ∃ (f : α), f ∈ (B₂ \ B₁) ∧ M.is_basis (B₁ \ {e} ∪ {f}) :=
begin
  rw basis_iff_indep_full_rank at hB₁ hB₂, 
  simp_rw basis_iff_indep_full_rank,   
  cases elem_diff_iff.mp he with he₁ he₂, 
  have h' : M.is_indep (B₁ \ {e}) := subset_indep (diff_subset _ _) hB₁.1, 
  rcases indep_aug_diff (by { rw size_remove_mem he₁, linarith, }) h' hB₂.1 
    with ⟨f,⟨hf, hf_aug⟩⟩, 
  have h'' : B₂ \ (B₁ \ {e}) = B₂ \ B₁, 
  { repeat {rw diff_eq}, 
    rw [compl_inter, compl_compl, inter_distrib_left, 
    inter_comm _ {e}, nonmem_disjoint_iff.mp he₂, union_empty]},
  rw h'' at hf, 
  cases elem_diff_iff.mp hf with hf₁ hf₂, 
  refine ⟨f, hf, hf_aug, _⟩, 
  rw size_remove_insert he₁ hf₂, exact hB₁.2, 
end  

lemma extends_to_basis_of :
  I ⊆ X → M.is_indep I → ∃ B, I ⊆ B ∧ M.is_basis_of B X := 
let P := λ J, I ⊆ J ∧ M.is_indep J ∧ J ⊆ X in 
begin
  intros hIX hIi, 
  rcases maximal_example_aug P ⟨subset_refl I,⟨hIi,hIX⟩⟩ with ⟨B, ⟨_, ⟨hPB,hBmax⟩⟩⟩ , 
  simp_rw basis_of_iff_augment_i, 
  refine ⟨B, ⟨hPB.1,⟨hPB.2.2,⟨hPB.2.1,λ e he hecon,_⟩⟩ ⟩⟩, 
  rw elem_diff_iff at he, 
  have := hBmax _ he.2, 
  push_neg at this, 
  from this (subset.trans h_left (subset_union_left _ _)) hecon (union_of_subsets hPB.2.2 (singleton_subset_iff.mpr he.1)), 
end 

lemma exists_basis_of (M : matroid α)(X : set α) : 
  ∃ B, M.is_basis_of B X := 
by {cases extends_to_basis_of (empty_subset X) (empty_indep M) with B hB, from ⟨B,hB.2⟩}

lemma exists_basis (M : matroid α): 
  ∃ B, M.is_basis B := 
by apply exists_basis_of 

lemma extends_to_basis :
  M.is_indep I → ∃ B, I ⊆ B ∧ M.is_basis B := 
  λ h, extends_to_basis_of (subset_univ I) h 

lemma flat_eq_cl_basis {B F : set α}(hF : M.is_flat F)(hBF : M.is_basis_of B F):
  F = M.cl B :=
begin
  apply subset.antisymm, 
  rw [subset_cl_iff_r, subset_iff_union_eq_left.mp hBF.1, hBF.2.2], 
  rw [←flat_iff_own_cl.mp hF], 
  apply M.cl_monotone hBF.1,  
end

lemma flat_iff_cl_indep :
  M.is_flat F ↔ ∃ I, M.is_indep I ∧ F = M.cl I := 
begin
  refine ⟨λ h, _, λ h, _⟩,
    rcases M.exists_basis_of F with ⟨I,hI⟩,
    simp_rw [indep_iff_r, flat_eq_cl_basis h hI], 
    refine ⟨I, by rw hI.2.1, rfl⟩, 
  rcases h with ⟨I,-,rfl⟩, 
  apply cl_is_flat, 
end

lemma rank_k_flat_iff_cl_indep {k : ℤ}:
  M.is_rank_k_flat k F ↔ ∃ I, M.is_indep I ∧ size I = k ∧ F = M.cl I := 
begin
  simp_rw [is_rank_k_flat, flat_iff_cl_indep], 
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨⟨I,hI,rfl⟩,hF⟩, 
    refine ⟨I, hI, _, rfl⟩, 
    rw [←hF, rank_cl, ←(indep_iff_r.mp hI)],},
  rcases h with ⟨I, hI, hk, rfl⟩, 
  refine ⟨⟨I, hI, rfl⟩,_⟩, 
  rw [rank_cl, (indep_iff_r.mp hI), hk],
end

lemma point_iff_cl_nonloop :
  M.is_point P ↔ ∃ e, M.is_nonloop e ∧ P = M.cl {e} := 
begin
  simp_rw [is_point, rank_k_flat_iff_cl_indep, size_one_iff_eq_singleton],
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨I,hs,⟨e,rfl⟩,rfl⟩,
    exact ⟨e, by {rwa nonloop_iff_indep}, rfl⟩, },
  rcases h with ⟨e,he,rfl⟩, 
  exact ⟨{e}, by {rwa ←nonloop_iff_indep}, ⟨e,rfl⟩, rfl⟩, 
end


lemma indep_iff_contained_in_basis :
  M.is_indep X ↔ ∃ B, X ⊆ B ∧ M.is_basis B := 
begin
  refine ⟨λ h, extends_to_basis h,  λ h, _⟩, 
  cases h with B hB, 
  from indep_of_subset_indep hB.1 (basis_is_indep hB.2),  
end

lemma mem_cl_iff_i :
  e ∈ M.cl X 
  ↔ ∃ I ⊆ X, M.is_indep I ∧ ∀ J ⊆ X ∪ {e}, is_indep M J → size J ≤ size I :=
begin
  rw mem_cl_iff_r, 
  refine ⟨λ h, _, λ h, _⟩, 
  rcases M.exists_basis_of X with ⟨I, ⟨hI₁, hI₂, hI₃⟩⟩, 
  refine ⟨_, hI₁, hI₂, λ J hJx hJ, _⟩, 
  rw [←hI₂, hI₃, ←h, ←indep_iff_r.mp hJ], exact M.rank_mono hJx,
  rw eq_comm, 
  refine rank_eq_of_le_supset (subset_union_left _ _) _,
  rcases M.exists_basis_of (X ∪ {e}) with ⟨J, ⟨hJ₁, hJ₂, hJ₃⟩⟩, 
  rcases h with ⟨I,hI,⟨hIind,hIX⟩⟩,
  specialize hIX J hJ₁ hJ₂,   
  rw [←hJ₃,hJ₂], rw ←(r_indep hIind) at hIX,  
  from le_trans hIX (M.rank_mono hI), 
end

lemma rank_eq_iff_exists_basis_of (M : matroid α)(X : set α){n : ℤ}:
  M.r X = n ↔ ∃ B, M.is_basis_of B X ∧ size B = n := 
begin
  refine ⟨λ h, _, λ h, _⟩, 
  subst h, cases exists_basis_of M X with B hB,
  exact ⟨B, hB, size_basis_of hB⟩, 
  rcases h with ⟨B,⟨⟨h₁,h₂⟩,h₃⟩⟩, 
  rw [←h₂.2, h₂.1], exact h₃, 
end

lemma rank_as_indep (M : matroid α)(X : set α):
  M.r X = max_val (λ I: indep_subset_of M X, size I.val) := 
begin
  rcases max_spec (λ I: indep_subset_of M X, size I.val) with ⟨⟨B,h,h'⟩, h₁, h₂⟩, 
  dsimp only at *, rw [←h₁], clear h₁, 
  rw [←indep_iff_r.mp h'], 
  apply le_antisymm _ (M.rank_mono h), 
  by_contra hcon, push_neg at hcon, 
  rcases rank_augment hcon with ⟨z, hz, hB⟩, 
  specialize h₂ ⟨B ∪ {z}, _⟩, swap, dsimp at h₂, 
    have : B ⊂ (B ∪ {z}), from 
      ssubset_of_subset_ne (subset_union_left _ _) (λ h, by {rw ←h at hB, linarith,}), 
    linarith [size_strict_monotone this], 
  exact ⟨union_singleton_subset_of_subset_mem h hz, indep_of_indep_aug h' hB⟩,
end

lemma r_univ_eq_max_size_indep (M : matroid α):
  M.r univ = max_val (λ I : M.indep, size I.val) :=
begin
  rw rank_as_indep, 
  set φ : M.indep_subset_of univ → M.indep := λ X, ⟨X.val, X.property.2⟩ with hφ, 
  have : function.surjective φ, 
    from λ X, by {use ⟨X.val, ⟨subset_univ X.val, X.property⟩⟩, rw hφ, simp,}, 
  rw [max_reindex φ this (λ X, size X.val)], 
  refl, 
end


lemma not_indep_iff_exists_removal : 
  ¬M.is_indep X ↔ ∃ (e : α), e ∈ X ∧ M.r (X \ {e}) = M.r X := 
begin
  rw not_indep_iff_r, rcases exists_basis_of M X with ⟨B, ⟨h,h',h''⟩⟩, 
  refine ⟨λ h1, _, λ h1,_⟩, 
  { rw [←h'', h'] at h1,
    rcases elem_diff_of_size_lt h1 with ⟨e,he1,he2⟩, 
    refine ⟨e,he1,_⟩, 
    apply rank_eq_of_le_supset, intro x, simp, tauto,  
    rw [←h'',diff_eq], 
    apply M.rank_mono (subset_inter h _),  tidy, },
  rcases h1 with ⟨e, heX, he⟩, 
  rw ←he, refine lt_of_le_of_lt (M.rank_le_size _) _, 
  rw size_remove_mem heX, linarith,  
end


end basis 

section ext 

variables {M₁ M₂ : matroid α}

lemma rank_ext :
  M₁.r = M₂.r → M₁ = M₂ := 
λ h, by {ext, rw h}

lemma indep_ext :
  M₁.is_indep = M₂.is_indep → M₁ = M₂ := 
begin
  intro h, ext X,
  cases exists_basis_of M₁ X with B hB, 
  rw ←size_basis_of hB, 
  rw basis_of_iff_augment_i at hB, 
  simp_rw h at hB, 
  rw ←basis_of_iff_augment_i at hB, 
  rw ←size_basis_of hB, 
end

lemma circuit_ext : 
  M₁.is_circuit = M₂.is_circuit → M₁ = M₂ :=
begin
  intro h, apply indep_ext, ext X,
  simp_rw [indep_iff_contains_no_circuit, h], 
end

lemma cocircuit_ext :
  M₁.is_cocircuit = M₂.is_cocircuit → M₁ = M₂ := 
  λ h, dual_inj (circuit_ext h)

lemma hyperplane_ext :
  M₁.is_hyperplane = M₂.is_hyperplane → M₁ = M₂ := 
begin
  intro h, apply cocircuit_ext, ext X,
  simp_rw [cocircuit_iff_compl_hyperplane, h], 
end

lemma flat_ext : 
  M₁.is_flat = M₂.is_flat → M₁ = M₂ := 
begin
  intro h, apply hyperplane_ext, ext X, 
  simp_rw [hyperplane_iff_maximal_subflat, h], 
end

lemma basis_ext : 
  M₁.is_basis = M₂.is_basis → M₁ = M₂ := 
begin
  intro h, apply indep_ext, ext X, 
  simp_rw [indep_iff_contained_in_basis, h], 
end

lemma circuit_ind_of_distinct (hM₁M₂ : M₁ ≠ M₂):
  ∃ X, (M₁.is_circuit X ∧ M₂.is_indep X) ∨ (M₂.is_circuit X ∧ M₁.is_indep X) := 
begin
  by_contra h, push_neg at h, 
  refine hM₁M₂ (indep_ext _), ext Y,
  simp_rw [indep_iff_contains_no_circuit, not_iff_not],
  refine ⟨λ h₁, _, λ h₂, _⟩, 
  rcases h₁ with ⟨C, ⟨hC, hCY⟩⟩, 
  have := (h C).1 hC, 
  simp_rw [←dep_iff_not_indep, dep_iff_contains_circuit] at this, 
  rcases this with ⟨C₂, ⟨hC₂, hC₂C⟩⟩, 
  from ⟨C₂, ⟨hC₂, subset.trans hC₂C hCY⟩⟩, 
  rcases h₂ with ⟨C, ⟨hC, hCY⟩⟩, 
  have := (h C).2 hC, 
  simp_rw [←dep_iff_not_indep, dep_iff_contains_circuit] at this, 
  rcases this with ⟨C₂, ⟨hC₂, hC₂C⟩⟩, 
  from ⟨C₂, ⟨hC₂, subset.trans hC₂C hCY⟩⟩, 
end

end ext

end matroid 

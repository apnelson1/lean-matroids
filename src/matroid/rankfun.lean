/- A matroid is defined as a rank function, so this file is the biggest part of the
   matroid API. 
-/


import matroid.axioms  matroid.dual 
import prelim.collections prelim.minmax
open set 
--open ftype_induction 

open_locale classical 
noncomputable theory 
----------------------------------------------------------------
namespace matroid 
variables {U : Type}[fintype U]

section /- rank -/ rank


def rank (M : matroid U) := M.r univ 

/-- rank is nonnegative -/
lemma rank_nonneg (M : matroid U)(X : set U):
  0 ≤ M.r X := 
M.R0 X 

/-- rank is bounded above by size -/
lemma rank_le_size (M : matroid U)(X : set U):
  M.r X ≤ size X := 
M.R1 X 

/-- rank is monotone wrt set inclusion -/
lemma rank_mono (M : matroid U){X Y : set U}:
  X ⊆ Y → M.r X ≤ M.r Y := 
M.R2 X Y

/-- rank is submodular -/
lemma rank_submod (M : matroid U)(X Y : set U):
  M.r (X ∪ Y) + M.r (X ∩ Y) ≤ M.r X + M.r Y := 
M.R3 X Y 

lemma rank_mono_inter_left (M : matroid U)(X Y : set U): 
  M.r (X ∩ Y) ≤ M.r X := 
M.rank_mono (inter_subset_left X Y)

lemma rank_mono_union_left (M : matroid U)(X Y : set U) : 
  M.r X ≤ M.r (X ∪ Y) := 
M.rank_mono (subset_union_left X Y)

lemma rank_mono_inter_right (M : matroid U)(X Y : set U): 
  M.r (X ∩ Y) ≤ M.r Y := 
M.rank_mono (inter_subset_right X Y)

lemma rank_mono_union_right (M : matroid U)(X Y : set U) : 
  M.r Y ≤ M.r (X ∪ Y) := 
M.rank_mono (subset_union_right X Y)

lemma rank_mono_diff (M : matroid U)(X Y : set U):
  M.r (X \ Y) ≤ M.r X := 
by {rw diff_eq, apply rank_mono_inter_left}

lemma rank_eq_zero_of_le_zero {M : matroid U}{X : set U}:
  M.r X ≤ 0 → M.r X = 0 := 
λ h, le_antisymm h (M.rank_nonneg X)

lemma rank_subset_rank_zero {M : matroid U}{X Y : set U}: 
  X ⊆ Y → M.r Y = 0 → M.r X = 0 := 
λ hXY hY, by {apply rank_eq_zero_of_le_zero, rw ←hY, exact rank_mono M hXY}

lemma rank_inter_rank_zero {M : matroid U}(X : set U){Y : set U}:
  M.r Y = 0 → M.r (X ∩ Y) = 0 :=
λ hY, by {apply rank_subset_rank_zero _ hY, simp }

@[simp] lemma rank_empty (M : matroid U): 
  M.r ∅ = 0 := 
rank_eq_zero_of_le_zero (by {convert M.rank_le_size _, rw size_empty })

lemma rank_lt_size_ne_empty {M : matroid U}{X : set U}: 
  M.r X < size X → X ≠ ∅ := 
λ h hX, by {rw [hX, size_empty, rank_empty] at h, from lt_irrefl _ h,  }

lemma rank_single_ub (M : matroid U)(e : U):
  M.r {e} ≤ 1 := 
by {rw ←(size_singleton e), exact M.rank_le_size {e}}

lemma rank_le_univ (M : matroid U)(X : set U) : 
  M.r X ≤ M.r univ := 
M.rank_mono (subset_univ X)

lemma rank_compl_univ (M : matroid U): 
  M.r (univᶜ) = 0 := 
by rw [compl_univ, rank_empty]

lemma rank_gt_zero_of_ne {M : matroid U}{X : set U}:
  M.r X ≠ 0 → 0 < M.r X := 
λ h, lt_of_le_of_ne (M.rank_nonneg X) (ne.symm h)

lemma rank_eq_of_le_supset {M : matroid U}{X Y : set U}:
  X ⊆ Y → (M.r Y ≤ M.r X) → M.r X = M.r Y :=
λ h h', (le_antisymm (M.rank_mono h) h') 

lemma rank_eq_of_le_union {M : matroid U}{X Y : set U}:
  M.r (X ∪ Y) ≤ M.r X → M.r (X ∪ Y) = M.r X :=
λ h, ((rank_eq_of_le_supset ((subset_union_left X Y))) h).symm

lemma rank_eq_of_le_inter {M : matroid U}{X Y : set U}:
  M.r X ≤ M.r (X ∩ Y) →  M.r (X ∩ Y) = M.r X :=
λ h, (rank_eq_of_le_supset (inter_subset_left _ _) h)

lemma rank_eq_of_not_lt_supset {M : matroid U}{X Y : set U}:
  X ⊆ Y → ¬(M.r X < M.r Y) → M.r X = M.r Y :=
λ h h', rank_eq_of_le_supset h (int.le_of_not_gt' h')

lemma rank_eq_of_not_lt_union {M : matroid U}{X Y : set U}:
  ¬ (M.r X < M.r (X ∪ Y)) → M.r (X ∪ Y) = M.r X :=
λ h', rank_eq_of_le_union (int.le_of_not_gt' h')

@[simp] lemma rank_eq_rank_union_rank_zero {M : matroid U}(X : set U){Y :set U}:
  M.r Y = 0 → M.r (X ∪ Y) = M.r X := 
λ hY, by {apply rank_eq_of_le_union, linarith [M.rank_nonneg (X ∩ Y ), M.rank_submod X Y],} 

lemma rank_zero_of_union_rank_zero {M : matroid U}{X Y : set U}:
  M.r X = 0 → M.r Y = 0 → M.r (X ∪ Y) = 0 :=
λ hX hY, by {rw (rank_eq_rank_union_rank_zero _ hY), exact hX }

lemma rank_eq_of_le_union_supset {M : matroid U}{X Y : set U}(Z: set U):
  X ⊆ Y → M.r X = M.r Y → M.r (X ∪ Z) = M.r (Y ∪ Z) := 
begin
  intros hXY hr, apply rank_eq_of_le_supset (subset_union_subset_left X Y Z hXY), 
  have : M.r ((X ∪ Z) ∩ Y) = _ := by rw [inter_distrib_right, subset_def_inter_mp hXY] ,
  have : M.r ((X ∪ Z) ∪ Y) = _ := by rw [union_assoc, union_comm Z Y, ←union_assoc, subset_def_union_mp hXY ],
  linarith [M.rank_submod (X ∪ Z) Y , M.rank_mono_union_left X (Z ∩ Y) ], 
end 

lemma rank_eq_of_inter_union {M : matroid U}(X Y A : set U):
  M.r (X ∩ A) = M.r X → M.r ((X ∩ A) ∪ Y) = M.r (X ∪ Y) :=
λ h, rank_eq_of_le_union_supset _ (inter_subset_left _ _) h 
  
lemma rank_subadditive (M : matroid U)(X Y : set U) : 
  M.r (X ∪ Y) ≤ M.r X + M.r Y :=
by linarith [M.rank_submod X Y, M.rank_nonneg (X ∩ Y)]

lemma rank_augment_single_ub (M : matroid U)(X : set U)(e : U): 
  M.r (X ∪ {e}) ≤ M.r X + 1 := 
by linarith [rank_subadditive M X {e}, rank_single_ub M e]

lemma rank_eq_add_one_of_ne_aug {M : matroid U}{X : set U}{e : U}:
  M.r (X ∪ {e}) ≠ M.r X → M.r (X ∪ {e}) = M.r X + 1 := 
begin
  intro h, apply le_antisymm,
  from (rank_augment_single_ub M X e), 
  from (int.add_one_le_of_lt (lt_of_le_of_ne (rank_mono_union_left M _ _) (ne.symm h))),
end

lemma rank_eq_of_le_aug {M : matroid U}{X : set U}{e : U}:
  M.r (X ∪ {e}) ≤ M.r X → M.r (X ∪ {e}) = M.r X :=  
λ h, le_antisymm h (rank_mono_union_left _ _ _) 

lemma rank_diff_subadditive (M : matroid U)(X Y : set U) :
  M.r Y ≤ M.r X + M.r (Y \ X) := 
le_trans (M.rank_mono (by simp)) (rank_subadditive M X (Y \ X))

lemma rank_remove_single_lb (M : matroid U)(X : set U)(e : U):
  M.r X - 1 ≤ M.r (X \ {e}) :=
by linarith [rank_diff_subadditive M {e} X, rank_single_ub M e]

lemma rank_eq_sub_one_of_ne_remove (M : matroid U)(X : set U)(e : U):
  M.r X ≠ M.r (X \ {e}) → M.r (X \ {e}) = M.r X - 1 :=
begin
  intro h, apply le_antisymm  _ (rank_remove_single_lb M X e), 
  apply int.le_sub_one_of_le_of_ne _ (ne.symm h), 
  apply rank_mono_diff, 
end

lemma rank_diff_le_size_diff (M : matroid U){X Y : set U}(hXY : X ⊆ Y) :
  M.r Y - M.r X ≤ size Y - size X := 
by linarith [rank_diff_subadditive M X Y, diff_size hXY, M.rank_le_size (Y \ X )]
  

lemma submod_three_sets (M : matroid U)(X Y Y' : set U) :
  M.r (X ∪ (Y ∪ Y')) + M.r (X ∪ (Y ∩ Y')) ≤ M.r (X ∪ Y) + M.r (X ∪ Y') := 
by {have := M.rank_submod (X ∪ Y) (X ∪ Y'), rw [←union_distrib_left, ←union_distrib_union_right] at this, exact this}

lemma submod_three_sets_right (M : matroid U)(X Y Y' : set U) :
  M.r ((Y ∪ Y') ∪ X) + M.r ((Y ∩ Y') ∪ X) ≤ M.r (Y ∪ X) + M.r (Y' ∪ X) := 
by {simp_rw ←(union_comm X), apply submod_three_sets} 

lemma submod_three_sets_disj (M : matroid U)(X Y Y' : set U)(hYY' : Y ∩ Y' = ∅) :
  M.r (X ∪ (Y ∪ Y')) + M.r (X) ≤ M.r (X ∪ Y) + M.r (X ∪ Y') := 
by {have := submod_three_sets M X Y Y', rw [hYY', union_empty] at this, exact this}

/-lemma union_rank_diff_le_rank_diff (M : matroid U)(X Y Z : set U)(hXY : X ⊆ Y):
  M.r (Y ∪ Z) - M.r (X ∪ Z) ≤ M.r Y - M.r X :=
begin
  have := rank_submod M Y Z, 
  have := rank_submod M X Z, 
end -/


theorem rank_augment {M : matroid U} {X Z : set U} : (M.r X < M.r Z) → 
  ∃ (z : U), z ∈ Z ∧ M.r X < M.r (X ∪ {z}) := 
let P : set U → Prop := λ X', 
  (M.r X' = M.r X) ∧ (X' ⊆ X ∪ Z) ∧ (∀ (e:U), e ∈ X ∪ Z → M.r (X' ∪ {e}) = M.r X') in  
begin
  intro hXZ, 
  
  by_contra h_con, push_neg at h_con, 
  replace h_con : ∀ (z:U), z ∈ X ∪ Z → M.r (X ∪ {z}) = M.r X := 
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
  
  have hef : ({e} ∩ {f} : set U) = ∅ := inter_distinct_singles
    (λ h, by {rw [h, union_self] at h_aug_ef, linarith}),
  
  linarith [submod_three_sets_disj M Y {e} {f} hef],
end


lemma loopy_rank_zero {M : matroid U}{X : set U} (he : (∀ (e:U), e ∈ X → M.r {e} = 0)) : 
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
def is_indep (M : matroid U) : set U → Prop :=
  λ X, M.r X = size X

/-- independent set type -/ 
def indep (M : matroid U) := {I : set U // M.is_indep I}

instance coe_indep {M : matroid U} : has_coe (M.indep) (set U) := 
  coe_subtype   

instance fintype_indep {M : matroid U} : fintype (M.indep) := 
by {unfold indep, apply_instance }


def is_indep_subset_of (M : matroid U)(X : set U) : set U → Prop := 
  λ I, I ⊆ X ∧ M.is_indep I 

def indep_subset_of (M : matroid U)(X : set U) := {I : set U // M.is_indep_subset_of X I}


/-- is dependent in M; negation of independence -/
def is_dep (M : matroid U) : set U → Prop := 
   λ X, ¬(M.is_indep X)

lemma indep_iff_r {M : matroid U} {X : set U}: 
  M.is_indep X ↔ M.r X = size X := 
by refl 

lemma r_indep {M : matroid U}{X : set U}:
  M.is_indep X → M.r X = size X :=
indep_iff_r.mp 

lemma dep_iff_r {M : matroid U} {X : set U}:
  is_dep M X ↔ M.r X < size X := 
by {unfold is_dep, rw indep_iff_r, exact ⟨λ h, (ne.le_iff_lt h).mp (M.rank_le_size X), λ h, by linarith⟩}

--instance coe_coindep {M : matroid U} : has_coe (coindep M) U := ⟨λ I, I.val⟩  

lemma indep_or_dep (M : matroid U) (X : set U): 
  M.is_indep X ∨ M.is_dep X := 
by {rw [dep_iff_r, indep_iff_r], exact eq_or_lt_of_le (M.rank_le_size X)}

lemma dep_iff_not_indep {M : matroid U} {X : set U}: 
  M.is_dep X ↔ ¬M.is_indep X := 
by {rw [indep_iff_r, dep_iff_r], exact ⟨λ h, by linarith, λ h, (ne.le_iff_lt h).mp (M.rank_le_size X)⟩}

lemma not_indep_iff_r {M : matroid U}{X : set U}:
  ¬is_indep M X ↔ M.r X < size X := 
by {rw ←dep_iff_not_indep, apply dep_iff_r, }

lemma indep_iff_not_dep {M : matroid U} {X : set U}: 
  M.is_indep X ↔ ¬M.is_dep X := 
by {rw dep_iff_not_indep, simp}

lemma coindep_iff_r {M : matroid U} {X : set U} :
  (dual M).is_indep X ↔ (M.r Xᶜ = M.r univ) := 
by {unfold is_indep dual, dsimp only, split; {intros h, linarith}}

lemma codep_iff_r {M : matroid U} {X : set U} : 
  is_dep (dual M) X ↔ (M.r Xᶜ < M.r univ) := 
by {rw [dep_iff_not_indep, coindep_iff_r], exact ⟨λ h, (ne.le_iff_lt h).mp (rank_le_univ M Xᶜ), λ h, by linarith⟩}
    
lemma not_coindep_iff_r {M : matroid U} {X : set U}:
  ¬is_indep (dual M) X ↔ (M.r Xᶜ < M.r univ) := 
by rw [←dep_iff_not_indep, codep_iff_r] 

lemma empty_indep (M : matroid U) :
  M.is_indep ∅ :=  
by rw [indep_iff_r, size_empty, rank_empty]

lemma dep_nonempty {M : matroid U} {X : set U} (hdep : is_dep M X ):
  X ≠ ∅ := 
λ h, let h' := empty_indep M in by {rw ←h at h', exact hdep h'}

lemma subset_indep {M : matroid U} {X Y : set U}: 
  X ⊆ Y → M.is_indep Y → M.is_indep X := 
begin 
  intro hXY, simp_rw indep_iff_r, intro hY, 
  linarith [M.rank_le_size X, M.rank_le_size (Y \ X ), diff_size hXY, rank_diff_subadditive M X Y]
end 

lemma indep_aug {M : matroid U}{X Y : set U} : 
  size X < size Y → M.is_indep X → M.is_indep Y → (∃ (e:U), e ∈ Y ∧ e ∉ X ∧ M.is_indep (X ∪ {e})) := 
begin
  simp_rw indep_iff_r,
  intros hXY hIX hIY,
  rcases rank_augment (by linarith : M.r X < M.r Y) with ⟨e,⟨h₁, h₂⟩⟩, 
  have hx : ¬({e} ⊆ X),
  { exact (λ he, by {rw [union_comm, subset_def_union_mp he] at h₂, linarith})}, 
  rw singleton_subset_iff at hx,
  refine ⟨e,⟨h₁,hx,_⟩⟩, 
  have hs := (size_modular X {e}),
  rw [ eq.trans (inter_comm X {e}) (nonmem_disjoint hx), size_empty] at hs, 
  linarith [size_singleton e, M.rank_le_size (X ∪ {e}), int.add_one_le_iff.mpr h₂],  
end

lemma indep_aug_diff {M : matroid U}{X Y : set U} : 
  size X < size Y → M.is_indep X → M.is_indep Y  → (∃ (e:U), e ∈ Y \ X  ∧ M.is_indep (X ∪ {e})) := 
λ h₁ h₂ h₃, by {simp_rw elem_diff_iff, simp_rw and_assoc, exact indep_aug h₁ h₂ h₃}

lemma indep_of_indep_aug {M : matroid U}{I : set U}{e : U}:
  M.is_indep I → M.r I < M.r (I ∪ {e}) → M.is_indep (I ∪ {e}) :=
begin
  intros hI h, 
  rw indep_iff_r at *, 
  apply le_antisymm (M.rank_le_size _ ),
  apply le_trans (add_size_ub), 
  rw hI at h, convert h, 
end


lemma dep_subset {M : matroid U}{X Y : set U}: 
  X ⊆ Y → is_dep M X → is_dep M Y := 
by {intro hXY, repeat {rw dep_iff_not_indep}, contrapose!, exact subset_indep hXY}

lemma empty_indep_r (M : matroid U) :
   M.r ∅ = size (∅ : set U) :=
(empty_indep M)

lemma subset_indep_r {M : matroid U}{X Y : set U}: 
  X ⊆ Y → M.r Y = size Y → M.r X = size X := 
λ h, by {have := subset_indep h, rw [indep_iff_r, indep_iff_r] at this, assumption} 


lemma elem_indep_r {M : matroid U}{e : U}{I : set U}(he : e ∈ I)(hI : M.is_indep I):
  M.r {e} = 1 := 
begin 
  rw [←singleton_subset_iff] at he, 
  rw [←size_singleton e, ←indep_iff_r], 
  exact subset_indep_r he hI, 
end

lemma I1 (M : matroid U) : 
  M.is_indep ∅ := 
  empty_indep M 

instance nonempty_indep {M : matroid U} : nonempty (M.indep) := 
by {apply nonempty_subtype.mpr, from ⟨∅, M.I1⟩}

lemma I2 {M : matroid U} {X Y : set U}: 
  X ⊆ Y → M.is_indep Y → M.is_indep X := 
begin 
  intro hXY, simp_rw indep_iff_r, intro hY, 
  linarith [M.rank_le_size X, M.rank_le_size (Y \ X ), 
  diff_size hXY, rank_diff_subadditive M X Y]
end 

lemma I2_i_right {M : matroid U}(X Y : set U):
  M.is_indep Y → M.is_indep (X ∩ Y) :=
λ h, I2 (inter_subset_right _ _) h 

lemma I2_i_left {M : matroid U}(X Y : set U):
  M.is_indep X → M.is_indep (X ∩ Y) :=
λ h, I2 (inter_subset_left _ _) h 

lemma I2_u_right {M : matroid U}{X Y : set U}:
  M.is_indep (X ∪ Y) → M.is_indep Y :=
λ h, I2 (subset_union_right _ _) h

lemma I2_u_left {M : matroid U}{X Y : set U}:
  M.is_indep (X ∪ Y) → M.is_indep X :=
λ h, I2 (subset_union_left _ _) h 

lemma I3 {M : matroid U}{X Y : set U}: 
  size X < size Y → M.is_indep X → M.is_indep Y → (∃ (e:U), e ∈ Y \ X ∧ M.is_indep (X ∪ {e})) := 
  indep_aug_diff 

lemma indep_inter_rank_zero {M : matroid U}{I X : set U}(hI : M.is_indep I)(hX : M.r X = 0): 
   I ∩ X = ∅ :=
begin
  have h := I2_i_left I X hI, 
  rwa [indep_iff_r,rank_inter_rank_zero I hX, eq_comm, size_zero_iff_empty] at h, 
end

/-- converts a matroid to an independence family -/
def to_indep_family (M : matroid U) : indep_family U := 
  ⟨M.is_indep, I1 M, @I2 _ _ M, @I3 _ _ M⟩


instance nonempty_indep_subset_of (M : matroid U)(X : set U) : nonempty (indep_subset_of M X) :=
by {apply nonempty_subtype.mpr, exact ⟨∅,⟨empty_subset _, M.I1⟩ ⟩, }

instance fintype_indep_subset_of (M : matroid U)(X : set U) : fintype (indep_subset_of M X) :=
by {unfold indep_subset_of, apply_instance, } 



end indep 

section /-Circuits-/ circuit

/-- is a circuit of M : minimally dependent -/
def is_circuit (M : matroid U) : set U → Prop := 
  λ X, (¬is_indep M X ∧  ∀ Y: set U, Y ⊂ X → M.is_indep Y)

/-- circuit type -/
def circuit (M : matroid U) := { C : set U // M.is_circuit C }

instance coe_circuit {M : matroid U} : has_coe (M.circuit) (set U) := 
  coe_subtype    

instance fintype_circuit {M : matroid U} : fintype (M.circuit) := 
by {unfold circuit, apply_instance }

/-- is a cocircuit of M: circuit of the dual -/
def is_cocircuit (M : matroid U) : set U → Prop := 
  is_circuit (dual M)

/-- cocircuit type -/ 
def cocircuit (M : matroid U) := { C : set U // M.is_cocircuit C }

instance coe_cocircuit {M : matroid U} : has_coe (cocircuit M) (set U) := 
  coe_subtype    
instance fintype_cocircuit {M : matroid U} : fintype (cocircuit M) := 
by {unfold cocircuit, apply_instance}   

lemma circuit_iff_i {M : matroid U}{X : set U} : 
  M.is_circuit X ↔ ¬is_indep M X ∧  ∀ Y: set U, Y ⊂ X → M.is_indep Y :=
by rw is_circuit 


lemma circuit_iff_r {M : matroid U} (X : set U) :
  M.is_circuit X ↔ (M.r X = size X - 1) ∧ (∀ Y: set U, Y ⊂ X → M.r Y = size Y) := 
begin
  unfold is_circuit,
  rw not_indep_iff_r, simp_rw indep_iff_r, 
  split, rintros ⟨hr, hmin⟩,
  split, rcases nonempty_single_removal (rank_lt_size_ne_empty hr) with ⟨Y, ⟨hY₁, hY₂⟩⟩, specialize hmin Y hY₁,
  linarith [M.rank_mono hY₁.1],  
  intros Y hY, exact hmin _ hY, 
  rintros ⟨h₁, h₂⟩, refine ⟨by linarith, λ Y hY, _ ⟩,  
  from h₂ _ hY, 
end

lemma r_cct {M : matroid U} {C : set U} :
  M.is_circuit C → M.r C = size C - 1 := 
λ hC, ((circuit_iff_r C).mp hC).1
  
lemma r_cct_ssub {M : matroid U} {C Y : set U} : 
  M.is_circuit C → (Y ⊂ C) → M.r Y = size Y :=
λ hC hYC, (((circuit_iff_r C).mp hC).2 Y hYC)

lemma cocircuit_iff_r {M : matroid U} (X : set U):
  M.is_cocircuit X ↔ (M.r Xᶜ = M.r univ - 1) ∧ (∀ Y: set U, Y ⊂ X → M.r Yᶜ = M.r univ) := 
begin 
  simp_rw [is_cocircuit, is_circuit, not_coindep_iff_r, coindep_iff_r],
  split, rintros ⟨h₁, h₂⟩, split, 
  have h_nonempty : X ≠ ∅ := by {intros h, rw [h,compl_empty] at h₁, exact int.lt_irrefl _ h₁}, 
  rcases (nonempty_single_removal h_nonempty) with ⟨Y,⟨hY₁, hY₂⟩⟩ ,
  specialize h₂ _ hY₁,  
  rw [←compl_compl Y, ←compl_compl X, compl_size, compl_size Xᶜ] at hY₂, 
  linarith[M.rank_diff_le_size_diff (compl_subset_compl.mpr hY₁.1)], 
  exact h₂, rintros ⟨h₁, h₂⟩, exact ⟨by linarith, h₂⟩, 
end 

lemma dep_iff_contains_circuit {M : matroid U} {X : set U} :
  is_dep M X ↔ ∃ C, M.is_circuit C ∧ C ⊆ X := 
begin
  refine ⟨λ h, _, λ h, _ ⟩, 
  rcases (minimal_example _ h) with ⟨Z,⟨h₁Z,h₂Z, h₃Z⟩⟩, 
  refine ⟨Z, ⟨⟨h₂Z, (λ Y hY, _)⟩, h₁Z⟩⟩, 
  rw indep_iff_not_dep, exact h₃Z Y hY,  
  cases h with C hC, exact dep_subset hC.2 hC.1.1, 
end 

/-- circuits nonempty unless matroid is free -/
instance nonempty_circuit {M : matroid U}(hM : M.r univ < size univ) : nonempty (M.circuit) := 
begin 
  apply nonempty_subtype.mpr, 
  rw [←dep_iff_r, dep_iff_contains_circuit] at hM, 
  cases hM with C hC, 
  from ⟨C,hC.1⟩, 
end 

/-- cocircuits nonempty unless matroid is loopy -/
instance nonempty_cocircuit {M : matroid U}(hM : 0 < M.r univ) : nonempty (cocircuit M) := 
begin
  refine matroid.nonempty_circuit (_ : (dual M).r univ < size univ), 
  rw [dual_r, compl_univ, M.rank_empty], linarith, 
end

lemma circuit_dep {M : matroid U}{C : set U}:
  M.is_circuit C → M.is_dep C := 
λ h, dep_iff_contains_circuit.mpr ⟨C,h,subset_refl _⟩ 

lemma indep_iff_contains_no_circuit {M : matroid U}{X : set U} : 
  M.is_indep X ↔ ¬∃ C, M.is_circuit C ∧ C ⊆ X :=
by rw [←not_iff_not, ←dep_iff_not_indep, dep_iff_contains_circuit, not_not]


lemma empty_not_cct (M : matroid U): 
  ¬M.is_circuit ∅ := 
by {rw circuit_iff_r, intros h, have := h.1, linarith [rank_empty M, size_empty U]}

lemma nested_circuits_equal (M : matroid U) {C₁ C₂ : set U}: 
  C₁ ⊆ C₂ → M.is_circuit C₁ → M.is_circuit C₂ → C₁ = C₂ := 
begin 
  intros hC₁C₂ hC₁ hC₂, 
  rw circuit_iff_r at hC₁ hC₂, 
  by_contra a, 
  linarith [hC₂.2 _ (ssubset_of_subset_ne hC₁C₂ a)],
end 

lemma circuit_not_ssubset_circuit (M : matroid U){C₁ C₂ : set U}:
  M.is_circuit C₁ → M.is_circuit C₂ → ¬(C₁ ⊂ C₂) :=
  λ hC₁ hC₂ hC₁C₂, ne_of_ssubset hC₁C₂ (nested_circuits_equal M hC₁C₂.1 hC₁ hC₂)

lemma inter_circuits_ssubset {M : matroid U}{C₁ C₂ : set U}:
  M.is_circuit C₁ → M.is_circuit C₂ → C₁ ≠ C₂ → C₁ ∩ C₂ ⊂ C₁ := 
begin
  intros hC₁ hC₂ hC₁C₂, 
  refine ssubset_of_subset_ne (inter_subset_left _ _) (λ h, _), 
  rw ←subset_def_inter at h, exact hC₁C₂ (nested_circuits_equal M h hC₁ hC₂ ),
end

lemma circuit_elim {M : matroid U} {C₁ C₂ : set U} {e : U}: 
   C₁ ≠ C₂ → M.is_circuit C₁ → M.is_circuit C₂ → e ∈ C₁ ∩ C₂ → ∃ C, M.is_circuit C ∧ C ⊆ ((C₁ ∪ C₂) \ {e}) := 
begin
  intros hC₁C₂ hC₁ hC₂ he, 
  rw [←dep_iff_contains_circuit, dep_iff_r], 
  have hI : C₁ ∩ C₂ ⊂ C₁ := inter_circuits_ssubset hC₁ hC₂ hC₁C₂, 
  have heU := mem_of_mem_of_subset he (inter_subset_union C₁ C₂),
  have hcalc : M.r ((C₁ ∪ C₂) \ {e}) ≤ size ((C₁ ∪ C₂) \ {e}) -1 := 
  by linarith [M.rank_mono (diff_subset (C₁ ∪ C₂) {e} ), M.rank_submod C₁ C₂, 
        r_cct hC₁, r_cct hC₂, r_cct_ssub hC₁ hI, size_modular C₁ C₂, remove_single_size heU],
  from int.le_sub_one_iff.mp hcalc,
end 

/-lemma circuit_elemination_subtype {M : matroid U} {C₁ C₂ : circuit M} {e : U}: 
  C₁ ≠ C₂ → e ∈ (C₁ ∩ C₂ : set U) → ∃ (C : circuit M), (C : set U) ⊆ (C₁ ∪ C₂) \ {e} := 
  by{intros hne he, cases circuit_elemination _ C₁.2 C₂.2 he with C hC, use ⟨C, hC.1⟩, exact hC.2, exact λ h, hne (subtype.eq h)}-/

def matroid_to_cct_family (M : matroid U) : cct_family U := 
  ⟨λ X, M.is_circuit X, 
   empty_not_cct M, 
   λ C₁ C₂, circuit_not_ssubset_circuit M, 
   @circuit_elim _ _ M⟩


end circuit

section closure

/-- is spanning in M: closure is univ -/
@[simp] def is_spanning (M : matroid U) : set U → Prop := 
  λ X, M.r X = M.r univ 

/-- X spans Y if the rank of X is the rank of X ∪ Y -/
def spans (M : matroid U) : set U → set U → Prop := 
  λ X Y, M.r (X ∪ Y) = M.r X 

lemma spanning_iff_r {M : matroid U}{X : set U} :
  M.is_spanning X ↔ M.r X = M.r univ := 
by refl 

lemma spans_iff_r {M : matroid U} {X Y : set U} :
  M.spans X Y ↔ M.r (X ∪ Y) = M.r X :=
by refl 

lemma not_spans_iff_r {M : matroid U}{X Y : set U}: 
  ¬M.spans X Y ↔ M.r X < M.r (X ∪ Y) :=
by {rw [spans_iff_r, eq_comm], exact ⟨λ h, lt_of_le_of_ne (rank_mono_union_left M _ _) h, λ h, ne_of_lt h⟩}

lemma spanned_union (M : matroid U){X Y Y' : set U} :
  M.spans X Y → M.spans X Y' → M.spans X (Y ∪ Y') := 
begin
  unfold spans, intros h h', 
  linarith [submod_three_sets M X Y Y', M.rank_mono_union_left X (Y ∩ Y'), M.rank_mono_union_left X (Y ∪ Y')],
end

lemma spanned_union_closed (M : matroid U)(X : set U):
   union_closed (λ Y, spans M X Y) :=
begin
  refine ⟨_, λ Y Y' hY hY', spanned_union M hY hY'⟩, 
  have : M.r (X ∪ ∅) = M.r X := by rw union_empty, assumption, 
end

lemma spans_refl (M : matroid U) (X : set U): 
  M.spans X X :=
by {unfold spans, rw [union_self]} 

lemma spans_subset (M : matroid U){X Y Y' : set U} : 
  Y ⊆ Y' → M.spans X Y' → M.spans X Y :=
begin
  unfold spans, intros hYY' hXY, 
  linarith [M.rank_mono_union_left X Y,  M.rank_mono (subset_union_subset_right _ _ X hYY')], 
end

lemma spans_rank_zero {M : matroid U}(X : set U){L : set U}(hL : M.r L = 0):
  M.spans X L := 
by rw [spans_iff_r, rank_eq_rank_union_rank_zero X hL] 

/-- closure of X in M : union of all sets spanned by X -/
def cl (M : matroid U) : set U → set U :=
  λ X, max_of_union_closed (spanned_union_closed M X)

-- cl X is the (unique) maximal set that is spanned by X
lemma cl_iff_max {M : matroid U}{X F : set U} : 
  M.cl X = F ↔ M.spans X F ∧ ∀ Y, F ⊂ Y → ¬M.spans X Y :=
let huc := spanned_union_closed M X, h_eq := (union_closed_max_iff_in_and_ub huc F) in 
by {dsimp at h_eq, unfold is_maximal at h_eq, rw [h_eq], 
      unfold cl, rw [eq_comm, ←is_max_of_union_closed_iff huc]}
  
-- cl X is also the set spanned by X that contains all sets spanned by X
lemma cl_iff_spanned_ub {M : matroid U}{X F : set U}:
   M.cl X = F ↔ M.spans X F ∧ ∀ Y, M.spans X Y → Y ⊆ F := 
by {unfold cl, rw [eq_comm, is_max_of_union_closed_iff], refl}

lemma cl_iff_spanned_ub_r {M : matroid U}{X F : set U}:
   M.cl X = F ↔ M.r (X ∪ F) = M.r X ∧ ∀ Y, (M.r (X ∪ Y) = M.r X) → Y ⊆ F := 
by {unfold cl, rw [eq_comm, is_max_of_union_closed_iff], refl}

lemma cl_is_max {M : matroid U}{X : set U}:
  M.spans X (M.cl X) ∧ ∀ Y, (M.cl X) ⊂ Y → ¬M.spans X Y :=
cl_iff_max.mp rfl

lemma cl_is_ub {M : matroid U}{X : set U}:
  ∀ Y, M.spans X Y → Y ⊆ (M.cl X) := 
(cl_iff_spanned_ub.mp rfl).2 

lemma subset_cl (M : matroid U)(X : set U) : 
  X ⊆ M.cl X := 
(cl_iff_spanned_ub.mp rfl).2 _ (spans_refl M X)

lemma spans_cl (M : matroid U)(X : set U) :
  M.spans X (M.cl X) := 
(cl_iff_max.mp rfl).1 

lemma supset_cl {M : matroid U}(X : set U) :
  ∀ Y, (M.cl X ⊂ Y) → ¬M.spans X Y := 
(cl_iff_max.mp rfl).2

lemma spanned_subset_cl {M : matroid U}{X Y : set U}: 
  M.spans X Y → Y ⊆ M.cl X := 
λ h, cl_is_ub Y h 

lemma rank_zero_subset_cl {M : matroid U}(X : set U){L : set U}(hL : M.r L = 0):
  L ⊆ M.cl X := 
spanned_subset_cl (spans_rank_zero X hL)

lemma subset_cl_iff {M : matroid U}(X Y: set U) :
  Y ⊆ M.cl X ↔ M.spans X Y := 
⟨λ h, spans_subset M h (spans_cl _ _ ), λ h, spanned_subset_cl h⟩ 

lemma subset_cl_iff_r {M : matroid U}(X Y : set U) :
  Y ⊆ M.cl X ↔ M.r (X ∪ Y) = M.r X :=
by {rw subset_cl_iff, refl}

lemma spanning_iff_cl_univ {M : matroid U}(X : set U):
  M.is_spanning X ↔ M.cl X = univ :=
begin
  rw cl_iff_spanned_ub, unfold spans is_spanning, refine ⟨λ h, ⟨_,λ Y hY, _⟩, λ h, _⟩, 
  rw [h, union_univ], apply subset_univ, rw [←h.1, union_univ], 
end   
  
lemma cl_univ (M : matroid U):
  M.cl univ = univ := 
by {rw ←spanning_iff_cl_univ, obviously}

lemma rank_cl (M : matroid U)(X : set U) : 
  M.r (cl M X) = M.r X := 
begin
  have : M.r (X ∪ M.cl X) = M.r X := M.spans_cl X,
  linarith [M.rank_mono_union_right X (M.cl X), M.rank_mono (M.subset_cl X)], 
end 

lemma union_cl_rank_left (M : matroid U)(X Y : set U) :
  M.r ((M.cl X) ∪ Y) = M.r (X ∪ Y) := 
by {rw eq_comm, exact rank_eq_of_le_union_supset _ (subset_cl _ _) (rank_cl _ _).symm}
  
lemma union_cl_rank_right (M : matroid U)(X Y : set U) :
  M.r (X ∪ (M.cl Y)) = M.r (X ∪ Y) :=
by {rw [union_comm, union_comm _ Y], apply union_cl_rank_left} 

lemma cl_idem (M : matroid U)(X : set U) :
  cl M (cl M X) = cl M X := 
begin
  rw cl_iff_spanned_ub, refine ⟨by apply spans_refl, λ Y hY, _⟩,  
  rw subset_cl_iff, unfold spans, unfold spans at hY, 
  apply rank_eq_of_le_union, 
  linarith [M.rank_cl X, M.union_cl_rank_left X Y], 
end

lemma spans_iff_cl_spans {M : matroid U}{X Y : set U}:
  M.spans X Y ↔ M.spans (M.cl X) Y :=
begin   
  repeat {rw spans_iff_r}, 
  rw [rank_eq_of_le_union_supset, rank_cl],  
  apply subset_cl, exact (rank_cl _ _).symm,  
end

lemma cl_monotone (M : matroid U){X Y : set U}:
  X ⊆ Y → M.cl X ⊆ M.cl Y :=
λ h, by {rw subset_cl_iff_r, apply rank_eq_of_le_union, 
          rw [union_cl_rank_right, union_comm, subset_def_union_mp h]}
  
lemma nonmem_cl_iff_r {M : matroid U}{X : set U}{e : U} :
  e ∉ M.cl X ↔ M.r (X ∪ {e}) = M.r X + 1 :=
begin
  rw [←singleton_subset_iff, subset_cl_iff_r], refine ⟨λ h, _, λ _, λ _, by linarith⟩, 
  linarith [rank_augment_single_ub M X e, 
  int.add_one_le_iff.mpr ((ne.symm h).le_iff_lt.mp (rank_mono_union_left M X {e}))],
end

lemma mem_cl_iff_r {M : matroid U}{X : set U}{e : U} : 
  e ∈ M.cl X ↔ M.r (X ∪ {e}) = M.r X := 
by rw [←singleton_subset_iff, subset_cl_iff_r]

lemma mem_cl_iff_spans {M : matroid U}{X : set U}{e : U}:
  e ∈ M.cl X ↔ M.spans X {e} :=
by rw [spans_iff_r,mem_cl_iff_r]

lemma nonmem_cl_iff_nonspans {M : matroid U}{X : set U}{e : U}:
  e ∉ M.cl X ↔ ¬M.spans X {e} :=
⟨λ h, λ hn, h (mem_cl_iff_spans.mpr hn), λ h, λ hn, h (mem_cl_iff_spans.mp hn)⟩

lemma rank_removal_iff_closure {M : matroid U}(X : set U)(e : U)(h : e ∈ X):
  M.r (X \ {e}) = M.r X ↔ e ∈ M.cl (X \ {e}) :=
by rw [mem_cl_iff_r, remove_add_elem h, eq_comm]
  

lemma cl4 (M : matroid U)(X : set U)(e f : U) : 
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
def is_flat (M : matroid U) : set U → Prop := 
  λ F, ∀ (X : set U), F ⊂ X → M.r F < M.r X

/-- subtype of flats of M -/
def flat (M : matroid U) := { F : set U // M.is_flat F }  

instance coe_flat {M : matroid U} : has_coe (M.flat) (set U) := 
  coe_subtype   
  
instance fintype_flat {M : matroid U} : fintype (flat M) := 
by {unfold flat, apply_instance }


/-- flat of rank k -/
def is_rank_k_flat (M : matroid U) (k : ℤ) : set U → Prop := 
  λ F, M.is_flat F ∧ M.r F = k 

/-- the unique rank zero flat -/
def loops : matroid U → set U := 
  λ M, M.cl ∅ 

/-- is a rank -one flat -/
def is_point (M : matroid U) : set U → Prop := 
  λ F, M.is_rank_k_flat 1 F

/-- is a rank-two flat -/
def is_line (M : matroid U) : set U → Prop := 
  λ F, M.is_rank_k_flat 2 F

/-- is a rank-three flat -/
def is_plane (M : matroid U) : set U → Prop := 
  λ F, M.is_rank_k_flat 3 F

/-- flat of rank r M - 1 -/
def is_hyperplane (M : matroid U) : set U → Prop := 
  λ H, M.is_rank_k_flat (M.r univ - 1) H 

lemma rank_loops (M: matroid U): 
  M.r (M.loops) = 0 := 
by rw [loops, rank_cl, rank_empty]

lemma rank_zero_iff_subset_loops {M : matroid U}{X : set U}:
  M.r X = 0 ↔ X ⊆ M.loops  :=
begin
  refine ⟨λ h, _, λ h, rank_eq_zero_of_le_zero _ ⟩,  
  rw [loops, subset_cl_iff_r], 
  simp, from h, 
  convert M.rank_mono h, 
  from eq.symm (rank_loops M), 
end

lemma spans_loops (M : matroid U)(X : set U):
  M.spans X M.loops := 
spans_rank_zero X (rank_loops M)

lemma loops_subset_cl (M : matroid U)(X : set U):
  M.loops ⊆ M.cl X := 
rank_zero_subset_cl X (rank_loops M)

lemma flat_iff_r {M : matroid U} (X : set U) :
  M.is_flat X ↔ ∀ Y, X ⊂ Y → M.r X < M.r Y := 
by refl 

lemma cl_is_flat (M : matroid U) (X : set U): 
  M.is_flat (cl M X) := 
begin
  rw flat_iff_r, intros Y hY, have hne := cl_is_max.2 _ hY, 
  rw [spans_iff_cl_spans, spans_iff_r] at hne, 
  rw ←subset_def_union_mp hY.1, 
  from lt_of_le_of_ne (M.rank_mono_union_left (cl M X) Y) (ne.symm hne), 
end

lemma flat_iff_own_cl {M : matroid U}{F : set U}:
  M.is_flat F ↔ M.cl F = F :=
begin
  refine ⟨λ h, _, λ h, by {have := cl_is_flat M F, rw h at this, exact this}⟩,
  rw [cl_iff_max, spans_iff_r], simp_rw not_spans_iff_r,  
  from ⟨by rw union_self, λ Y hFY, lt_of_lt_of_le (h Y hFY) (by {rw union_comm, apply rank_mono_union_left})⟩,
end 

lemma loops_subset_flat (M : matroid U){F : set U}(hF : M.is_flat F):
  M.loops ⊆ F := 
by {rw ←flat_iff_own_cl.mp hF, apply loops_subset_cl}


lemma flat_iff_is_cl {M : matroid U}{F : set U}: 
  M.is_flat  F ↔ ∃ X : set U, cl M X = F := 
⟨λ h, ⟨F, flat_iff_own_cl.mp h⟩, λ h, 
    by {cases h with X hX, rw flat_iff_own_cl, rw ←hX, apply cl_idem}⟩

lemma subset_flat {M : matroid U}(X F : set U):
  X ⊆ F → M.is_flat F → M.cl X ⊆ F :=
begin
  rw flat_iff_own_cl, 
  intros hXF hF, 
  rw ←hF, apply cl_monotone _ hXF, 
end

lemma flat_iff_add_r {M : matroid U}{F : set U}:
  M.is_flat F ↔ ∀ (e:U), e ∉ F → M.r F < M.r (F ∪ {e}) :=
begin
  rw flat_iff_r, 
  refine ⟨λ h, λ e he, h _ (ssub_of_add_nonmem he), λ h, λ Y hY, _⟩,
  cases add_from_nonempty_diff.mp hY with e he, 
  exact lt_of_lt_of_le (h e he.1) (M.rank_mono he.2), 
end

lemma flat_iff_add {M : matroid U}{F : set U}:
  M.is_flat F ↔ ∀ (e : U), e ∉ F → ¬M.spans F {e} := 
by {rw [flat_iff_add_r], simp_rw not_spans_iff_r}

lemma fullrank_flat_is_univ {M : matroid U}{F : set U}:
  M.is_flat F → M.r F = M.r univ → F = univ := 
begin
  intros hF hFr, 
  rw [flat_iff_own_cl] at hF, 
  rw [←hF, ←spanning_iff_cl_univ], 
  from hFr, 
end

lemma hyperplane_iff_r {M : matroid U} (X : set U) :
  M.is_hyperplane X ↔ M.r X = M.r univ - 1 ∧ ∀ Y, X ⊂ Y → M.r Y = M.r univ := 
begin
  unfold is_hyperplane is_rank_k_flat, rw flat_iff_r, 
  refine ⟨λ h, ⟨h.2, λ Y hXY, _ ⟩, λ h, ⟨λ Y hXY, _, h.1⟩ ⟩,
  have := h.1 Y hXY, rw h.2 at this, linarith [rank_le_univ M Y],  
  rw [h.1,h.2 Y hXY], exact sub_one_lt _,   
end

lemma hyperplane_iff_maximal_nonspanning {M : matroid U} (X : set U): 
  M.is_hyperplane X ↔ ¬M.is_spanning X ∧ ∀ (Y: set U), X ⊂ Y → M.is_spanning Y :=
begin
  rw hyperplane_iff_r, split, 
  intro h, simp only [is_spanning], split, linarith [h.2],
  intros Y hXY, linarith [h.2 Y hXY, h.2, rank_le_univ M Y],
  simp only [is_spanning], 
  refine λ h, ⟨_,h.2⟩, cases h with h1 h2,  
  rcases ne_univ_single_addition (λ h', by {rw h' at h1, from h1 rfl} : X ≠ univ) with ⟨Y,hY₁, hY₂⟩,
  linarith [rank_diff_le_size_diff M hY₁.1, h2 _ hY₁, 
            int.le_sub_one_of_le_of_ne (rank_le_univ M X) h1],   
end 

lemma hyperplane_iff_maximal_subflat {M : matroid U} (H : set U):
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
  rcases ne_univ_single_addition_element h_univ with ⟨e, he₁, he₂⟩,
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

lemma cocircuit_iff_compl_hyperplane {M : matroid U} (X : set U): 
  M.is_cocircuit X ↔ M.is_hyperplane Xᶜ := 
begin
  rw [cocircuit_iff_r, hyperplane_iff_r], 
  refine ⟨λ h, ⟨h.1,λ Y hXY, _⟩ , λ h, ⟨h.1,λ Y hXY, h.2 _ (scompl_subset_compl.mpr hXY)⟩⟩, 
  rw [←(h.2 _ (scompl_subset_comm.mp hXY)), compl_compl], 
end

lemma inter_flats_is_flat (M : matroid U) (F₁ F₂ : set U) :
  M.is_flat F₁ → M.is_flat F₂ → M.is_flat (F₁ ∩ F₂) := 
begin 
  repeat {rw [flat_iff_add]}, simp_rw ←nonmem_cl_iff_nonspans, 
  intros h₁ h₂ e he, rw nonmem_inter_iff at he, cases he, 
  exact λ h, (h₁ e he) (mem_of_mem_of_subset h (cl_monotone M (inter_subset_left F₁ F₂))), 
  exact λ h, (h₂ e he) (mem_of_mem_of_subset h (cl_monotone M (inter_subset_right F₁ F₂))), 
end

/-- is both a circuit and a hyperplane -/
def is_circuit_hyperplane (M : matroid U)(C : set U) := 
  M.is_circuit C ∧ M.is_hyperplane C 

lemma circuit_hyperplane_rank {M : matroid U}{C : set U}(hC : is_circuit_hyperplane M C) :
  M.r C = M.r univ - 1 := 
by {simp_rw [is_circuit_hyperplane, hyperplane_iff_r] at hC, from hC.2.1}

lemma circuit_hyperplane_size {M : matroid U}{C : set U}(hC : is_circuit_hyperplane M C) :
  size C = M.r univ := 
by {have := circuit_hyperplane_rank hC, simp_rw [is_circuit_hyperplane, circuit_iff_r] at hC, linarith [hC.1.1]}

lemma circuit_hyperplane_rank_size {M : matroid U}{C : set U}(hC : is_circuit_hyperplane M C) :
  M.r C = size C - 1 := 
by linarith [circuit_hyperplane_size hC, circuit_hyperplane_rank hC]

lemma circuit_hyperplane_ssubset_rank {M : matroid U}{C X : set U}(hC : is_circuit_hyperplane M C):
  X ⊂ C → M.r X = size X := 
λ hXC, by {simp_rw [is_circuit_hyperplane, circuit_iff_r] at hC, from hC.1.2 _ hXC,}

lemma circuit_hyperplane_ssupset_rank {M : matroid U}{C X : set U}(hC : is_circuit_hyperplane M C) :
  C ⊂ X → M.r X = M.r univ := 
λ hXC, by {simp_rw [is_circuit_hyperplane, hyperplane_iff_r] at hC, from hC.2.2 _ hXC,}

lemma circuit_hyperplane_dual {M : matroid U}{C : set U}:
  M.is_circuit_hyperplane C ↔ (dual M).is_circuit_hyperplane Cᶜ := 
begin
  simp_rw [is_circuit_hyperplane, ←cocircuit_iff_compl_hyperplane, is_cocircuit],  
  rw [dual_dual, ←is_cocircuit, cocircuit_iff_compl_hyperplane, compl_compl, and_comm], 
end


--lemma closure_eq_iff_flat {M : matroid U} {X F : set U} : 
--  cl M X = F ↔ X ⊆ F ∧ is_flat M F ∧ ∀ F', is_flat 

end flat

section /- Series and Parallel -/ series_parallel 

/-- is a rank-zero element -/
def is_loop (M : matroid U) : U → Prop := 
  λ e, M.r {e} = 0 

/-- is a rank-one element -/
def is_nonloop (M : matroid U) : U → Prop := 
  λ e, M.r {e} = 1 

/-- is a loop of the dual -/
def is_coloop (M : matroid U) : U → Prop := 
  is_loop (dual M) 

/-- is not a coloop of the dual -/
def is_noncoloop (M : matroid U) : U → Prop := 
  is_coloop (dual M)

lemma nonloop_iff_indep {M : matroid U}{e : U}:
  M.is_nonloop e ↔ M.is_indep {e} := 
by rw [is_nonloop, indep_iff_r, size_singleton] 

lemma rank_nonloop {M : matroid U}{e : U}:
  M.is_nonloop e → M.r {(e : U)} = 1 :=
by {unfold is_nonloop, from λ h, h}

lemma rank_loop {M : matroid U}{e : U}:
  M.is_loop e → M.r {e} = 0 :=
by {unfold is_loop, from λ h, h}

lemma loop_iff_elem_loops {M : matroid U} {e : U} : 
  M.is_loop e ↔ e ∈ M.loops := 
by {simp_rw [is_loop, ←singleton_subset_iff], from rank_zero_iff_subset_loops}  

lemma nonloop_iff_not_elem_loops {M : matroid U}{e : U}: 
  M.is_nonloop e ↔ e ∉ M.loops := 
begin
  simp_rw [is_nonloop, ←singleton_subset_iff, ←rank_zero_iff_subset_loops], 
  refine ⟨λ h h', by linarith, λ h, _⟩, 
  linarith [rank_single_ub M e, rank_gt_zero_of_ne h], 
end

lemma nonloop_iff_not_loop {M : matroid U} (e : U) : 
  M.is_nonloop e ↔ ¬ M.is_loop e := 
begin 
  unfold is_loop is_nonloop, refine ⟨λ h, _ ,λ h, _⟩,rw h ,
  simp only [not_false_iff, one_ne_zero], 
  have := M.rank_le_size {e}, rw size_singleton at this,       
  linarith [(ne.le_iff_lt (ne.symm h)).mp (M.rank_nonneg {e})],  
end

lemma coloop_iff_r {M : matroid U} (e : U) :
  M.is_coloop e ↔ M.r {e}ᶜ = M.r univ - 1 := 
begin
  unfold is_coloop is_loop, rw [dual_r,size_singleton],
  exact ⟨λh, by linarith,λ h, by linarith⟩,   
end

lemma coloop_iff_r_less {M : matroid U} (e : U) :
  M.is_coloop e ↔ M.r {e}ᶜ < M.r univ := 
begin
  unfold is_coloop is_loop, rw [dual_r,size_singleton],
  refine ⟨λh,by linarith,λ h,_⟩, 
  have := rank_diff_le_size_diff M (subset_univ {e}ᶜ), 
  rw [←size_compl, size_singleton] at this, 
  linarith [int.le_sub_one_iff.mpr h],
end


/-- nonloop as subtype -/
def nonloop (M : matroid U) : Type := { e : U // is_nonloop M e}

instance coe_nonloop {M : matroid U} : has_coe (nonloop M) (U) := ⟨λ e, e.val⟩  
--def noncoloop (M : matroid U) : Type := { e : U // is_nonloop (dual M) e}

lemma rank_coe_nonloop {M : matroid U}(e : nonloop M) : 
  M.r {(e : U)} = 1 := 
rank_nonloop (e.2)

lemma coe_nonloop_indep {M : matroid U}(e : nonloop M) :
  M.is_indep {(e : U)} := 
by {rw [indep_iff_r], simp only [size_singleton, coe_coe], apply rank_coe_nonloop e,}

lemma rank_two_nonloops_lb {M : matroid U} (e f : nonloop M) :
  1 ≤ M.r ({e,f}) := 
begin
  rw ←union_singletons_eq_pair, 
  linarith [rank_coe_nonloop e, M.rank_mono_union_left {e} {f}],
end 

lemma rank_two_nonloops_ub {M : matroid U} (e f : nonloop M) : 
  M.r ({e,f}) ≤ 2 := 
begin
  rw ←union_singletons_eq_pair, 
  linarith [rank_coe_nonloop e, rank_coe_nonloop f, 
    M.rank_nonneg ({e} ∩ {f}), M.rank_submod {e} {f}], 
end 

/-- two nonloops have rank-one union -/
def parallel (M : matroid U) (e f : nonloop M) : Prop := 
  M.r ({e,f}) = 1 



--example (e f : U): ({e,f} : set U) = ({f,e} : set U) := pair_comm e f
--example (e : U): ({e,e} : set U) = {e} := by {exact pair_eq_singleton e,}

/-- parallel in dual -/
def series (M : matroid U) (e f : nonloop (dual M)): Prop := 
  (dual M).parallel e f 

lemma parallel_refl (M : matroid U): 
  reflexive M.parallel:= 
λ e, by {unfold parallel, rw pair_eq_singleton, exact e.property}

lemma parallel_symm (M : matroid U) : 
  symmetric M.parallel:= 
λ x y, by {simp_rw [parallel, pair_comm], tauto,}

lemma parallel_iff_dep {M: matroid U}{e f : nonloop M} : 
  M.parallel e f ↔ (e = f ∨ M.is_dep {e,f}) :=
begin
  unfold parallel, rw dep_iff_r,  refine ⟨λ h, ((or_iff_not_imp_left.mpr (λ hne, _))), λ h, _ ⟩,
  have := size_union_distinct_singles (λ h', hne (subtype.ext h')) , 
  rw h, unfold_coes at *, linarith,  
  cases h, rw [h, pair_eq_singleton], exact f.property, 
  have := rank_two_nonloops_lb e f, 
  have := size_union_singles_ub e.1 f.1,
  unfold_coes at *, rw ←int.le_sub_one_iff at h, linarith, 
end

lemma parallel_iff_cct {M: matroid U}{e f : nonloop M} : 
  M.parallel e f ↔ (e = f ∨ M.is_circuit {e,f}) :=
begin
  refine ⟨λ h, _, λ h, (parallel_iff_dep.mpr (or.imp_right _ h : (e = f) ∨ is_dep M ({e,f})))⟩, 
  replace h := parallel_iff_dep.mp h, cases h, exact or.inl h, apply or_iff_not_imp_left.mpr, intro h', 
  refine ⟨h,λ Y hY, _⟩, rcases ssubset_pair hY, 
  rw h_1, exact empty_indep M,  unfold_coes at h_1,  cases h_1; 
  {rw h_1, apply coe_nonloop_indep,},
  apply circuit_dep, 
end

lemma parallel_trans (M : matroid U) :
  transitive M.parallel :=
begin
  intros e f g hef hfg, unfold parallel at *, 
  have := M.rank_submod ({e,f}) ({f,g}), rw [hef, hfg] at this, 
  have h1 : 1 ≤ M.r (({e,f}) ∩ ({f,g})),  
  {rw ←rank_coe_nonloop f, refine M.rank_mono (subset_inter _ _ ); simp, },
  have h2 := M.rank_mono (_ : ({e,g} : set U)  ⊆ {e,f} ∪ {f,g}), swap, 
  {intro x, simp, tauto,  }, 
  linarith [(rank_two_nonloops_lb e g)],  
end

lemma parallel_equiv (M : matroid U) : 
  equivalence M.parallel := 
  ⟨M.parallel_refl, M.parallel_symm, M.parallel_trans⟩

lemma series_equiv (M : matroid U): 
  equivalence M.series :=
parallel_equiv M.dual 

def parallel_classes_setoid (M : matroid U) : setoid (nonloop M) := 
  ⟨M.parallel, M.parallel_equiv⟩ 


end series_parallel 


  
/-lemma point_iff_parallel_class_and_loops {M : matroid U} {P: set U} : 
  is_point M P ↔ ∃  :=
  begin
     
  end-/

section /-Bases-/ basis


/-- B is a basis of X : an independent subset of X spanning X -/
def is_basis_of (M : matroid U)( B X : set U) : Prop := 
  B ⊆ X ∧ M.r B = size B ∧ M.r B = M.r X 

/-- B is a basis of M: an independent set spanning M -/
def is_basis (M : matroid U)(B : set U) : Prop := 
  M.is_basis_of B univ 


/-- basis type -/
def basis (M : matroid U) := {B : set U // M.is_basis B}

instance coe_subtype_basis {M : matroid U} : has_coe (M.basis) (set U) :=
  coe_subtype

instance fintype_basis {M : matroid U} : fintype (M.basis) := 
by {unfold basis, apply_instance }

/-- basis of set X type -/
def basis_of (M : matroid U)(X : set U) := {B : set U // M.is_basis_of B X}

instance coe_subtype_basis_of {M : matroid U}(X : set U) : has_coe (M.basis_of X) (set U) :=
  coe_subtype

instance fintype_basis_of {M : matroid U}(X : set U) : fintype (M.basis_of X) := 
by {unfold basis_of, apply_instance }



lemma size_basis_of {M : matroid U} {B X : set U}:
  M.is_basis_of B X → size B = M.r X :=
  λ h, by {rw is_basis_of at h, linarith}

lemma size_basis {M : matroid U}{B : set U} :
  M.is_basis B → size B = M.r univ := 
size_basis_of 

lemma bases_of_equicardinal (M : matroid U){B₁ B₂ X: set U}:
  M.is_basis_of B₁ X → M.is_basis_of B₂ X → size B₁ = size B₂ := 
λ h₁ h₂, by rw[size_basis_of h₁, size_basis_of h₂]

lemma bases_equicardinal (M : matroid U){B₁ B₂ : set U}:
  M.is_basis B₁ → M.is_basis B₂ → size B₁ = size B₂ := 
bases_of_equicardinal M 

lemma basis_iff_r {M : matroid U} {B : set U} :
  M.is_basis B ↔ M.r B = size B ∧ M.r B = M.r univ :=
⟨λ h, h.2, λ h, ⟨subset_univ B,h⟩⟩

/-- is a basis of the dual -/
def is_cobasis (M : matroid U): set U → Prop := 
  λ B, (dual M).is_basis B 

def cobasis (M : matroid U) := {B : set U // M.is_cobasis B}

@[simp] lemma cobasis_iff {M : matroid U} {B : set U} :
  M.is_cobasis B ↔ (dual M).is_basis B :=
by rw is_cobasis

@[simp] lemma basis_of_iff_augment {M : matroid U} {B X : set U}: 
  M.is_basis_of B X ↔ B ⊆ X ∧ M.r B = size B ∧ ∀ (e:U), e ∈ X → M.r (B ∪ {e}) = M.r B := 
begin
  refine ⟨λ h, ⟨h.1,⟨h.2.1,λ e he, _⟩⟩, λ h, ⟨h.1,⟨h.2.1,_⟩⟩⟩, 
  { linarith [h.2.2, 
      M.rank_mono (union_of_subsets h.1 (singleton_subset_iff.mpr he)), 
      M.rank_mono (subset_union_left B {e})]}, 
  refine rank_eq_of_not_lt_supset h.1 (λ hBX, _), 
  cases rank_augment hBX with e he, 
  linarith [h.2.2 e he.1, he.2],   
end

lemma basis_iff_augment {M : matroid U}{B : set U}:
  M.is_basis B ↔ M.r B = size B ∧ ∀ (e:U), M.r (B ∪ {e}) = M.r B := 
begin
  unfold is_basis, rw basis_of_iff_augment, 
  refine ⟨λ h, ⟨h.2.1,λ e, h.2.2 e (mem_univ e)⟩, λ h, ⟨subset_univ B, ⟨h.1,λ e he,h.2 e⟩⟩ ⟩, 
end

lemma basis_of_iff_augment_i {M : matroid U}{B X : set U} : 
  M.is_basis_of B X ↔ B ⊆ X ∧ M.is_indep B ∧ ∀ (e:U), e ∈ X \ B → ¬M.is_indep (B ∪ {e}) :=
begin
  rw basis_of_iff_augment, 
  refine ⟨λ h, ⟨h.1,⟨h.2.1,λ e he hi, _⟩⟩, λ h, ⟨h.1,⟨h.2.1,λ e he, _⟩ ⟩⟩, 
  rw indep_iff_r at hi, 
  rw elem_diff_iff at he, 
  linarith [h.2.2 e he.1, add_nonmem_size he.2], 
  by_cases heB: e ∈ B, 
  rw (add_elem heB), 
  have : e ∈ X \ B := by {rw elem_diff_iff, from ⟨he,heB⟩},
  have := h.2.2 _ this, 
  rw not_indep_iff_r at this, 
  have hi := h.2.1, rw indep_iff_r at hi, 
  linarith [add_nonmem_size heB, M.rank_mono (subset_union_left B {e})], 
end 

lemma basis_iff_augment_i {M : matroid U}{B : set U} : 
  is_basis M B ↔ M.is_indep B ∧ ∀ (e:U), e ∉ B → ¬M.is_indep (B ∪ {e}) := 
begin
  simp_rw [is_basis, basis_of_iff_augment_i, ←mem_compl_iff, univ_diff], 
  from ⟨λ h, ⟨h.2.1,λ e he, h.2.2 _ he⟩, λ h, ⟨subset_univ B, h⟩⟩, 
end

lemma basis_of_iff_indep_full_rank {M : matroid U}{B X : set U} :
  M.is_basis_of B X ↔ B ⊆ X ∧ M.is_indep B ∧ size B = M.r X := 
begin
  simp_rw [is_basis_of, indep_iff_r], 
  refine ⟨λ h, ⟨h.1, ⟨_,_⟩⟩, λ h, ⟨h.1,⟨_,_⟩⟩⟩; 
  linarith, 
end

lemma basis_iff_indep_full_rank {M : matroid U}{B : set U} :
  M.is_basis B ↔ M.is_indep B ∧ size B = M.r univ :=
begin
  simp_rw [basis_iff_r, indep_iff_r], 
  refine ⟨λ h, ⟨h.1, _⟩, λ h, ⟨h.1,_⟩⟩;
  linarith, 
end

lemma basis_is_indep {M : matroid U}{B : set U}: 
  M.is_basis B → M.is_indep B := 
  λ h, (basis_iff_indep_full_rank.mp h).1 

lemma cobasis_iff_r {M : matroid U}{B : set U}:
  M.is_cobasis B ↔ M.r Bᶜ = size Bᶜ ∧ M.r Bᶜ = M.r univ := 
begin
  simp_rw [is_cobasis, basis_iff_r, dual],
  refine ⟨λ _, ⟨_,_⟩, λ _, ⟨_,_⟩⟩;
  linarith [size_compl B, rank_compl_univ M], 
end

lemma cobasis_iff_compl_basis {M : matroid U}{B : set U} :
  M.is_cobasis B ↔ M.is_basis Bᶜ := 
by rw [cobasis_iff_r, basis_iff_r] 

lemma compl_cobasis_iff_basis {M : matroid U} {B : set U}:
  M.is_cobasis Bᶜ ↔ M.is_basis B := 
by rw [cobasis_iff, ←cobasis_iff_compl_basis, cobasis_iff, dual_dual]


lemma basis_exchange (M : matroid U){B₁ B₂ : set U}{e : U}(hB₁ : M.is_basis B₁)
(hB₂ : M.is_basis B₂)(he : e ∈ B₁ \ B₂):
  ∃ (f : U), f ∈ (B₂ \ B₁) ∧ M.is_basis (B₁ \ {e} ∪ {f}) :=
begin
  rw basis_iff_indep_full_rank at hB₁ hB₂, 
  simp_rw basis_iff_indep_full_rank,   
  cases elem_diff_iff.mp he with he₁ he₂, 
  have h' : M.is_indep (B₁ \ {e}) := subset_indep (diff_subset _ _) hB₁.1, 
  rcases indep_aug_diff (by { rw remove_single_size he₁, linarith, }) h' hB₂.1 
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

lemma extends_to_basis_of {M : matroid U}{I X : set U}:
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

lemma exists_basis_of (M : matroid U)(X : set U) : 
  ∃ B, M.is_basis_of B X := 
by {cases extends_to_basis_of (empty_subset X) (empty_indep M) with B hB, from ⟨B,hB.2⟩}

lemma exists_basis (M : matroid U): 
  ∃ B, M.is_basis B := 
by apply exists_basis_of 

lemma extends_to_basis {M : matroid U}{I : set U}:
  M.is_indep I → ∃ B, I ⊆ B ∧ M.is_basis B := 
  λ h, extends_to_basis_of (subset_univ I) h 

lemma indep_iff_contained_in_basis {M : matroid U}{X : set U}:
  M.is_indep X ↔ ∃ B, X ⊆ B ∧ M.is_basis B := 
begin
  refine ⟨λ h, extends_to_basis h,  λ h, _⟩, 
  cases h with B hB, 
  from I2 hB.1 (basis_is_indep hB.2),  
end

lemma mem_cl_iff_i {M : matroid U}{X : set U}{e : U} :
  e ∈ M.cl X 
  ↔ ∃ I ⊆ X, M.is_indep I ∧ ∀ J ⊆ X ∪ {e}, is_indep M J → size J ≤ size I :=
begin
  rw mem_cl_iff_r, 
  refine ⟨λ h, _, λ h, _⟩, 
  rcases M.exists_basis_of X with ⟨I, ⟨hI₁, hI₂, hI₃⟩⟩, 
  refine ⟨_, hI₁, hI₂, λ J hJx hJ, _⟩, 
  rw [←hI₂, hI₃, ←h, ←indep_iff_r.mp hJ], from M.rank_mono hJx,
  rw eq_comm, apply rank_eq_of_le_supset (subset_union_left _ _),
  rcases M.exists_basis_of (X ∪ {e}) with ⟨J, ⟨hJ₁, hJ₂, hJ₃⟩⟩, 
  rcases h with ⟨I,hI,⟨hIind,hIX⟩⟩,
  specialize hIX J hJ₁ hJ₂,   
  rw [←hJ₃,hJ₂], rw ←(r_indep hIind) at hIX,  
  from le_trans hIX (M.rank_mono hI), 
end

lemma rank_eq_iff_exists_basis_of (M : matroid U) (X : set U){n : ℤ}:
  M.r X = n ↔ ∃ B, M.is_basis_of B X ∧ size B = n := 
begin
  refine ⟨λ h, _, λ h, _⟩, 
  subst h, cases exists_basis_of M X with B hB,
  exact ⟨B, hB, size_basis_of hB⟩, 
  rcases h with ⟨B,⟨⟨h₁,h₂⟩,h₃⟩⟩, 
  rw [←h₂.2, h₂.1], exact h₃, 
end

lemma rank_as_indep (M : matroid U)(X : set U):
  M.r X = max_val (λ I: indep_subset_of M X, size I.val) := 
begin
  rcases max_spec (λ I: indep_subset_of M X, size I.val) with ⟨⟨B,h,h'⟩, h₁, h₂⟩, 
  dsimp only at *, rw [←h₁], clear h₁, 
  rw [←indep_iff_r.mp h'], 
  apply le_antisymm _ (M.rank_mono h), 
  by_contra hcon, push_neg at hcon, 
  rcases rank_augment hcon with ⟨z, hz, hB⟩, 
  specialize h₂ ⟨B ∪ {z}, _⟩, dsimp at h₂, 
    have : B ⊂ (B ∪ {z}), from 
      ssubset_of_subset_ne (subset_union_left _ _) (λ h, by {rw ←h at hB, linarith,}), 
    linarith [size_strict_monotone this], 
  exact ⟨union_singleton_subset_of_subset_mem h hz, indep_of_indep_aug h' hB⟩,
end

lemma rank_matroid_as_indep (M : matroid U):
  M.r univ = max_val (λ I : M.indep, size I.val) :=
begin
  rw rank_as_indep, 
  set φ : M.indep_subset_of univ → M.indep := λ X, ⟨X.val, X.property.2⟩ with hφ, 
  have : function.surjective φ, 
    from λ X, by {use ⟨X.val, ⟨subset_univ X.val, X.property⟩⟩, rw hφ, simp,}, 
  rw [max_reindex φ this (λ X, size X.val)], trivial,  
end


lemma not_indep_iff_exists_removal {M : matroid U}{X : set U} : 
  ¬M.is_indep X ↔ ∃ (e : U), e ∈ X ∧ M.r (X \ {e}) = M.r X := 
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
  rw remove_single_size heX, linarith,  
end


end basis 

section characterizations 

lemma rank_determines_matroid {M₁ M₂ : matroid U}:
  M₁.r = M₂.r → M₁ = M₂ := 
λ h, by {ext, rw h}

lemma indep_determines_matroid {M₁ M₂ : matroid U}:
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

lemma circuit_determines_matroid {M₁ M₂ : matroid U}: 
  M₁.is_circuit = M₂.is_circuit → M₁ = M₂ :=
begin
  intro h, apply indep_determines_matroid, ext X,
  simp_rw [indep_iff_contains_no_circuit, h], 
end

lemma cocircuit_determines_matroid {M₁ M₂ : matroid U}:
  M₁.is_cocircuit = M₂.is_cocircuit → M₁ = M₂ := 
  λ h, dual_inj (circuit_determines_matroid h)

lemma hyperplane_determines_matroid {M₁ M₂ : matroid U}:
  M₁.is_hyperplane = M₂.is_hyperplane → M₁ = M₂ := 
begin
  intro h, apply cocircuit_determines_matroid, ext X,
  simp_rw [cocircuit_iff_compl_hyperplane, h], 
end

lemma flat_determines_matroid {M₁ M₂ : matroid U}: 
  M₁.is_flat = M₂.is_flat → M₁ = M₂ := 
begin
  intro h, apply hyperplane_determines_matroid, ext X, 
  simp_rw [hyperplane_iff_maximal_subflat, h], 
end

lemma basis_determines_matroid {M₁ M₂ : matroid U}: 
  M₁.is_basis = M₂.is_basis → M₁ = M₂ := 
begin
  intro h, apply indep_determines_matroid, ext X, 
  simp_rw [indep_iff_contained_in_basis, h], 
end

lemma circuit_ind_of_distinct {M₁ M₂ : matroid U}(hM₁M₂ : M₁ ≠ M₂):
  ∃ X, (M₁.is_circuit X ∧ M₂.is_indep X) ∨ (M₂.is_circuit X ∧ M₁.is_indep X) := 
begin
  by_contra h, push_neg at h, 
  refine hM₁M₂ (indep_determines_matroid _), ext Y,
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

end characterizations

end matroid 
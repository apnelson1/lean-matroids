
import tactic 
import .int_lemmas 
import data.set.basic 

open_locale classical 
noncomputable theory 

universes u v w

namespace set 

variables {α : Type u}  

/-- the symmetric difference of two sets -/
def symm_diff (X Y : set α) : set α := (X \ Y) ∪ (Y \ X)



-- univ/empty with unions and intersections 


-- Complements


@[simp] lemma union_compl_rev (X: set α) : Xᶜ ∪ X = univ := 
by rw [union_comm, union_compl_self]

@[simp] lemma inter_compl_rev (X: set α) : Xᶜ ∩ X = ∅ := 
by rw [inter_comm, inter_compl_self]

-- Building things up from a minimal axiom set for fun

lemma empty_unique (X : set α) : (∀ (Y: set α), Y ∪ X = Y) → X = ∅ := 
λ hX, by calc X = ∅ ∪ X : (empty_union X).symm ... = ∅ : hX ∅

lemma empty_of_has_no_mem {s : set α}(hs : ¬ ∃ x, x ∈ s) : s = ∅ := 
by {rw eq_empty_iff_forall_not_mem, push_neg at hs, exact hs, }

@[simp] lemma empty_of_ss_empty {P : α → Prop}:
  {x ∈ (∅ : set α) | P x} = ∅ :=
by {ext, simp, }

-- αbsorption

@[simp] lemma absorb_union_inter (X Y : set α) : X ∪ (X ∩ Y) = X := 
by calc X ∪ (X ∩ Y) = (X ∩ univ) ∪ (X ∩ Y) : by rw inter_univ  ... = X : by rw [←inter_distrib_left, union_comm, union_univ, inter_univ ]

@[simp] lemma absorb_inter_union (X Y : set α) : X ∩ (X ∪ Y) = X := 
by calc X ∩ (X ∪ Y) = (X ∪ ∅) ∩ (X ∪ Y) : by rw union_empty ... = X : by rw [←union_distrib_left, inter_comm, inter_empty, union_empty]


-- Unions/Inters of triples 


@[simp] lemma union_left_absorb (X Y : set α) : (X ∪ Y) ∪ X = X ∪ Y := 
by rw [union_right_comm, union_self]  

@[simp] lemma union_right_absorb (X Y : set α) : X ∪ (Y ∪ X) = X ∪ Y := 
by rw [union_left_comm, union_self, union_comm]  

@[simp] lemma inter_left_absorb (X Y : set α) : (X ∩ Y) ∩ X = X ∩ Y := 
by rw [inter_right_comm, inter_self]  

@[simp] lemma inter_right_absorb (X Y : set α) : X ∩ (Y ∩ X) = X ∩ Y := 
by rw [inter_left_comm, inter_self, inter_comm]

lemma inter_distrib_inter_left (X Y Z : set α) : (X ∩ Y) ∩ Z = (X ∩ Z) ∩ (Y ∩ Z) := 
by rw [inter_assoc X Z, inter_comm Z, inter_assoc Y, inter_self, inter_assoc] 

lemma inter_distrib_inter_right (X Y Z : set α) : X ∩ (Y ∩ Z) = (X ∩ Y) ∩ (X ∩ Z) := 
by rw [inter_comm _ (X ∩ Z), inter_assoc _ _ (X ∩ Y), inter_comm Z, ←inter_assoc X, ←inter_assoc X, ←inter_assoc X, inter_self]

lemma union_distrib_union_left (X Y Z : set α) : (X ∪ Y) ∪ Z = (X ∪ Z) ∪ (Y ∪ Z) := 
by rw [union_assoc X Z, union_comm Z, union_assoc Y, union_self, union_assoc]

lemma union_distrib_union_right (X Y Z : set α) : X ∪ (Y ∪ Z) = (X ∪ Y) ∪ (X ∪ Z) := 
by rw [union_comm X, union_distrib_union_left Y Z X, union_comm X, union_comm X]   

@[simp] lemma inter_right_self (X Y : set α) : X ∩ Y ∩ Y = X ∩ Y :=
by rw [inter_assoc, inter_self] 

@[simp] lemma union_right_self (X Y : set α) : X ∪ Y ∪ Y = X ∪ Y :=
by rw [union_assoc, union_self] 

-- Subsets 

lemma subset_iff_union_eq_left {X Y : set α} : (X ⊆ Y) ↔ (X ∪ Y = Y) := 
by rw [←compl_subset_compl, subset_iff_inter_eq_left, ←compl_union, compl_inj_iff, union_comm Y X]

lemma subset_iff_union_eq_right {X Y : set α} : (X ⊆ Y) ↔ (Y = X ∪ Y) := 
by rw [subset_iff_union_eq_left, eq_comm]

lemma subset_refl (X : set α) : X ⊆ X :=
by rw [subset_iff_inter_eq_left, inter_self]

lemma subset_ssubset_or_eq {X Y : set α} : (X ⊆ Y) → (X ⊂ Y) ∨ X = Y :=
λ hXY, by {rw or_comm, apply eq_or_ssubset_of_subset hXY}

lemma subset_iff_ssubset_or_eq {X Y : set α} : (X ⊆ Y) ↔ (X ⊂ Y) ∨ X = Y :=
⟨λ h, subset_ssubset_or_eq h, λ h, by {cases h, from h.1, rw h}⟩

lemma ssubset_iff_subset_not_supset {X Y : set α} : X ⊂ Y ↔ X ⊆ Y ∧ ¬(Y ⊆ X) :=
iff.rfl

lemma ssubset_of_subset_ne {X Y : set α} : X ⊆ Y → X ≠ Y → X ⊂ Y := 
@lt_of_le_of_ne _ _ X Y 

lemma ne_of_ssubset {X Y : set α} : X ⊂ Y → X ≠ Y := 
ne_of_irrefl

lemma ssubset_irrefl (X : set α) : ¬(X ⊂ X) :=
λ h, by {rw ssubset_iff_subset_ne at h, from h.2 rfl}

lemma univ_subset  {X : set α} (hX : univ ⊆ X) : X = univ := 
subset.antisymm (subset_univ X) hX
 
instance subset_subtype_nonempty {X : set α} : nonempty {Y : set α // Y ⊆ X} := 
by {apply nonempty_subtype.mpr, from ⟨_,empty_subset _⟩,  }

instance subtype_coe {X : set α} : has_coe {Y : set α // Y ⊆ X} (set α) := coe_subtype

lemma subset_empty  {X : set α} : X ⊆ ∅ → X = ∅ := 
λ hX, subset.antisymm hX (empty_subset X)  

lemma ssubset_empty (X : set α) : ¬ X ⊂ ∅ := 
λ h, by {rw ssubset_iff_subset_ne at h, from h.2 (subset_empty h.1)}

lemma empty_of_subset_compl {X : set α}(h : X ⊆ Xᶜ) : X = ∅ := 
by rwa [subset_iff_inter_eq_left, inter_compl_self, eq_comm] at h

lemma disjoint_compl_subset {X Y : set α}(h : X ∩ Y = ∅): X ⊆ Yᶜ := 
by rw [subset_iff_inter_eq_left, ← empty_union (X ∩ Yᶜ), ←h, ←inter_distrib_left, union_compl_self, inter_univ]

lemma subset_compl_disjoint {X Y : set α}(h : X ⊆ Yᶜ) : X ∩ Y = ∅ := 
by {rw subset_iff_inter_eq_left at h, rw [←h, inter_assoc], simp}

lemma disjoint_iff_subset_compl {X Y : set α} : X ∩ Y = ∅ ↔ X ⊆ Yᶜ := 
⟨λ h, disjoint_compl_subset h, λ h, subset_compl_disjoint h⟩   

lemma disjoint_iff_inter_compl_eq_left {X Y : set α} : X ∩ Y = ∅ ↔ X ∩ Yᶜ = X := 
by rw [disjoint_iff_subset_compl, subset_iff_inter_eq_left]

lemma disjoint_iff_inter_compl_eq_right {X Y : set α} : X ∩ Y = ∅ ↔ Xᶜ ∩ Y = Y := 
by rw [inter_comm, disjoint_iff_inter_compl_eq_left, inter_comm]

lemma disjoint_iff_diff_eq_left {X Y : set α} : X ∩ Y = ∅ ↔ X \ Y = X := 
disjoint_iff_inter_compl_eq_left

lemma subset_iff_diff_empty (X Y : set α) : X ⊆ Y ↔ X \ Y = ∅ :=
by {rw [←compl_compl Y, ←disjoint_iff_subset_compl], simp [diff_eq],}

lemma subset_iff_partition (X Y : set α) : X ⊆ Y ↔ Y = X ∪ (Y \ X):= 
begin
  refine ⟨λ h, _, λ h, _⟩, 
  { nth_rewrite 0 ←(subset_iff_union_eq_left.mp h),
    rw [diff_eq, union_distrib_left], simp,},
  rw h, simp,  
end 

lemma subset_iff_disjoint_compl {X Y : set α} : X ⊆ Y ↔ X ∩ Yᶜ = ∅ :=
by rw [subset_iff_diff_empty, diff_eq]

lemma disjoint_of_subset_left' {X Y Z : set α }(hXY : X ⊆ Y)(hYZ : Y ∩ Z = ∅): X ∩ Z = ∅ :=
by {rw ←disjoint_iff_inter_eq_empty at *, exact disjoint_of_subset_left hXY hYZ}

lemma disjoint_of_subset_right' {X Y Z : set α }(hXY : X ⊆ Y)(hZY : Z ∩ Y = ∅) : Z ∩ X = ∅ :=
by {rw ←disjoint_iff_inter_eq_empty at *, exact disjoint_of_subset_right hXY hZY, }

lemma disjoint_of_subsets {X X' Y Y' : set α}(hXX' : X ⊆ X')(hYY' : Y ⊆ Y')(hXY : X' ∩ Y' = ∅):
  X ∩ Y = ∅ :=
by {rw ←disjoint_iff_inter_eq_empty at *, exact disjoint_of_subset hXX' hYY' hXY, }

lemma cover_compl_subset {X Y : set α} :  X ∪ Y = univ → Xᶜ ⊆ Y  := 
λ h, by rw [subset_iff_union_eq_left, ←univ_inter (Xᶜ ∪ Y), ←h, ←union_distrib_right, inter_compl_self, empty_union]

lemma compl_inj {X Y : set α}(h : Xᶜ = Yᶜ): X = Y := 
by rw [←compl_compl X, ←compl_compl Y, h]

@[simp] lemma union_compl_union  (X Y : set α) : X ∪ (Xᶜ ∪ Y) = univ :=  
by rw [←univ_inter(X ∪ (Xᶜ ∪ Y)), ←union_compl_self, ←union_distrib_left, absorb_inter_union] 

@[simp] lemma inter_compl_inter (X Y : set α) : X ∩ (Xᶜ ∩ Y) = ∅ := 
by rw [←empty_union(X ∩ (Xᶜ ∩ Y)), ←inter_compl_self, ←inter_distrib_left, absorb_union_inter]

@[simp] lemma inter_compl_union (X Y : set α) : X ∩ (Xᶜ ∪ Y) = X ∩ Y :=
by rw [inter_distrib_left, inter_compl_self, empty_union]

@[simp] lemma union_compl_inter (X Y : set α) : X ∪ (Xᶜ ∩ Y) = X ∪ Y :=
by rw [union_distrib_left, union_compl_self, univ_inter]

lemma union_inter_compl_inter (X Y : set α) : (X ∪ Y) ∪ (Xᶜ ∩ Yᶜ)  = univ := 
by rw [union_distrib_left, union_comm _ Xᶜ, union_comm X Y, union_comm _ Yᶜ,
      ←(compl_compl Y),  compl_compl Yᶜ, union_compl_union Yᶜ, union_comm _ X, 
      ←(compl_compl X),    compl_compl Xᶜ, union_compl_union Xᶜ, inter_self]

@[simp] lemma inter_union_compl_union (X Y : set α) : (X ∩ Y) ∩ (Xᶜ ∪ Yᶜ)  = ∅ := 
by rw [inter_distrib_left, inter_comm _ Xᶜ, inter_comm X Y, inter_comm _ Yᶜ, 
        ←(compl_compl Y), compl_compl Yᶜ, inter_compl_inter Yᶜ, inter_comm _ X, 
        ←(compl_compl X), compl_compl Xᶜ, inter_compl_inter Xᶜ, union_self]
  
@[simp] lemma inter_union_compl_inter (X Y : set α) : (X ∪ Y) ∩ (Xᶜ ∩ Yᶜ) = ∅ := 
by rw [inter_distrib_right X Y, inter_compl_inter, inter_comm Xᶜ, inter_compl_inter, union_self]
  
@[simp] lemma union_inter_compl_union  (X Y : set α) : (X ∩ Y) ∪ (Xᶜ ∪ Yᶜ) = univ := 
by rw [union_distrib_right X Y, union_compl_union, union_comm Xᶜ, union_compl_union, inter_self]

lemma compl_compl_inter_left (X Y : set α) : (Xᶜ ∩ Y)ᶜ = X ∪ Yᶜ := 
by {nth_rewrite 0 ←(compl_compl Y), rw [compl_inter, compl_compl, compl_compl] }

lemma compl_compl_inter_right (X Y : set α) : (X ∩ Yᶜ)ᶜ = Xᶜ ∪ Y := 
by {nth_rewrite 0 ←(compl_compl X), rw [compl_inter, compl_compl, compl_compl] }

lemma compl_compl_union_left (X Y : set α) : (Xᶜ ∪ Y)ᶜ = X ∩ Yᶜ := 
by {nth_rewrite 0 ←(compl_compl Y), rw [compl_union, compl_compl, compl_compl] }

lemma compl_compl_union_right (X Y : set α) : (X ∪ Yᶜ)ᶜ = Xᶜ ∩ Y := 
by {nth_rewrite 0 ←(compl_compl X), rw [compl_union, compl_compl, compl_compl] }


lemma compl_partition (X Y : set α) : (X ∩ Y) ∪ (Xᶜ ∩ Y) = Y := 
by rw [←inter_distrib_right, union_compl_self, univ_inter]

lemma compl_partition_subset  {X Y : set α} (hXY : X ⊆ Y) : X ∪ (Xᶜ ∩ Y) = Y := 
by {nth_rewrite 0 ←(subset_iff_inter_eq_left.mp hXY), exact compl_partition X Y}

lemma compl_pair {X Y : set α}(h : Xᶜ = Y) : (X = Yᶜ) := 
by rw [←h, compl_compl]

lemma compl_pair_iff {X Y : set α} : (Xᶜ = Y) ↔ (X = Yᶜ) := 
⟨λ h, compl_pair h, λ h, by {rw eq_comm at h, from (compl_pair h).symm}⟩

lemma compl_diff (X Y : set α) : (X \ Y)ᶜ = Xᶜ ∪ Y := 
by rw [diff_eq, compl_inter, compl_compl]

@[simp] lemma union_union_compl_self (X Y : set α) : (X ∪ Y) ∪ Yᶜ = univ := 
by rw [union_assoc, union_compl_self, union_univ]

@[simp] lemma inter_inter_compl_self (X Y : set α) : (X ∩ Y) ∩ Yᶜ = ∅ := 
by rw [inter_assoc, inter_compl_self, inter_empty]

@[simp] lemma union_union_compl_right (X Y : set α) : X ∪ (Y ∪ Xᶜ) = univ := 
by rw [←union_assoc, union_comm X, union_union_compl_self]

@[simp] lemma inter_inter_compl_right (X Y : set α) : X ∩ (Y ∩ Xᶜ) = ∅ := 
by rw [←inter_assoc, inter_comm X, inter_inter_compl_self]

lemma union_inter_compl_self (X Y : set α) : X ∪ (Y ∩ Yᶜ) = X :=
by simp 

lemma inter_union_compl_self (X Y : set α) : X ∩ (Y ∪ Yᶜ) = X :=
by rw [union_compl_self, inter_univ]

lemma subset_own_compl {X : set α} : X ⊆ Xᶜ → X = ∅ := 
  λ h, by {rw [subset_iff_union_eq_left,union_compl_self, ←compl_empty, compl_inj_iff] at h, rw ←h }

lemma inter_subset_union (X Y : set α) : X ∩ Y ⊆ X ∪ Y := 
  subset.trans (inter_subset_left X Y) (subset_union_left X Y)

lemma subset_of_inter_mp {X Y Z : set α} : X ⊆ Y ∩ Z → X ⊆ Y ∧ X ⊆ Z := 
  λ h, ⟨subset.trans h (inter_subset_left _ _), subset.trans h (inter_subset_right _ _)⟩  

lemma union_of_subsets {X Y Z : set α} : (X ⊆ Z) → (Y ⊆ Z) → (X ∪ Y ⊆ Z) := 
  λ hXZ hYZ, by {rw subset_iff_inter_eq_left at *, rw [inter_distrib_right, hXZ, hYZ]}

lemma subset_of_inter_mpr  {X Y Z : set α} : (X ⊆ Y) → (X ⊆ Z) → (X ⊆ Y ∩ Z) := 
  λ hXY hXZ, by {rw subset_iff_inter_eq_left at *, rw [←inter_assoc, hXY, hXZ]}

lemma subset_of_inter_iff {X Y Z : set α} : X ⊆ (Y ∩ Z) ↔ (X ⊆ Y ∧ X ⊆ Z) := 
  ⟨λ h, subset_of_inter_mp h, λ h, subset_of_inter_mpr  h.1 h.2⟩

lemma inter_of_subsets (X Y Z : set α)(h : X ⊆ Z) : X ∩ Y ⊆ Z := 
subset.trans (inter_subset_left X Y) h

lemma union_of_supsets (X Y Z : set α)(h : X ⊆ Y) : (X ⊆ Y ∪ Z) := 
subset.trans h (subset_union_left Y Z)

lemma subset_inter_subset_left {X Y : set α}(Z : set α)(h : X ⊆ Y) : (X ∩ Z) ⊆ (Y ∩ Z) := 
by {rw subset_iff_inter_eq_left at *, rw [←inter_distrib_inter_left, h]}

lemma subset_inter_subset_right (X Y Z : set α) : (X ⊆ Y) → (Z ∩ X) ⊆ (Z ∩ Y) := 
by {rw [inter_comm _ X, inter_comm _ Y], apply subset_inter_subset_left }

lemma subset_union_subset_left (X Y Z : set α) : (X ⊆ Y) → (X ∪ Z) ⊆ (Y ∪ Z) := 
  λ hXY, by {rw subset_iff_union_eq_left at *, rw [←union_distrib_union_left, hXY]}

lemma subset_union_subset_right (X Y Z : set α) : (X ⊆ Y) → (Z ∪ X) ⊆ (Z ∪ Y) := 
by {rw [union_comm _ X, union_comm _ Y], apply subset_union_subset_left }

lemma subset_of_set_and_compl {X Y: set α} : X ⊆ Y → X ⊆ Yᶜ → X = ∅ :=
  λ h1 h2, by {have := subset_of_inter_mpr h1 h2, rw inter_compl_self at this, exact subset_empty this}

@[trans] lemma subset.lt_of_le_of_lt {X Y Z : set α}(_ : X ⊆ Y)(_ : Y ⊂ Z): X ⊂ Z := 
lt_of_le_of_lt ‹X ≤ Y› ‹Y < Z› 

@[trans] lemma subset.lt_of_lt_of_le {X Y Z : set α}(_ : X ⊂ Y)(_ : Y ⊆ Z): X ⊂ Z := 
lt_of_lt_of_le ‹X < Y› ‹Y ≤ Z›

lemma ssubset_not_supset {X Y : set α}(h : X ⊂ Y) : ¬(Y ⊆ X) :=
λ h', ssubset_irrefl _ (subset.lt_of_lt_of_le h h') 

lemma subset_not_ssupset {X Y : set α}(h: X ⊆ Y): ¬(Y ⊂ X) := 
λ h', ssubset_irrefl _ (subset.lt_of_le_of_lt h h')

lemma eq_of_subset_not_ssubset  {X Y: set α} : X ⊆ Y → ¬(X ⊂ Y) → X = Y := 
λ h h', by {simp only [not_and, not_not, ssubset_iff_subset_ne] at h', exact h' h}

lemma inter_of_ssubsets (X Y Z : set α) : (X ⊂ Z) → (X ∩ Y ⊂ Z) := 
λ h, ssubset_of_subset_ne (inter_of_subsets X Y Z h.1)
     (λ heq, by {rw ←heq at h, have := ssubset_not_supset h, from this (inter_subset_left _ _) })

@[trans] lemma ssubset.trans {X Y Z : set α}: X ⊂ Y → Y ⊂ Z → X ⊂ Z := 
λ hXY hYZ, subset.lt_of_le_of_lt hXY.1 hYZ

lemma ssubset_inter {X Y : set α} : X ≠ Y → X ∩ Y ⊂ X ∨ X ∩ Y ⊂ Y :=
begin
  intro h, 
  by_contra a, push_neg at a, simp_rw [ssubset_iff_subset_ne, not_and', not_imp_not] at a, 
  exact h (eq.trans (a.1 (inter_subset_left X Y)).symm (a.2 (inter_subset_right X Y)) ),
end 

-- Misc

lemma union_union_diff (X Y Z : set α) : (X ∪ Z) ∪ (Y \ Z) = X ∪ Y ∪ Z :=
by {rw [diff_eq, union_distrib_left, union_right_comm, union_assoc _ Z], simp,}

lemma union_diff_absorb (X Y : set α) : X ∪ (Y \ X) = X ∪ Y :=
by {nth_rewrite 0 ←union_self X, rw union_union_diff, simp}

@[simp] lemma union_union_inter_compl_self (X Y Z : set α) : (X ∪ Z) ∪ (Y ∩ Zᶜ) = X ∪ Y ∪ Z :=
by rw [←diff_eq, union_union_diff] 

lemma union_inter_diff (X Y Z : set α) : (X ∪ Z) ∩ (Y \ Z) = (X ∩ Y) \ Z :=
by {rw [diff_eq, diff_eq, inter_distrib_right], simp_rw [←inter_assoc, inter_right_comm Z Y Zᶜ], simp, }

lemma subset_of_subset_diff {X Y Z : set α}(h : X ⊆ Y \ Z): X ⊆ Y :=
λ x hx, by {have := h hx, rw mem_diff at this, exact this.1,  }

lemma eq_of_union_eq_inter {X Y : set α} : X ∪ Y = X ∩ Y → X = Y := 
begin
  intro h, apply subset.antisymm, 
  calc X ⊆ (X ∪ Y) : subset_union_left _ _ ... = X ∩ Y : h ... ⊆ Y : inter_subset_right _ _,  
  calc Y ⊆ (X ∪ Y) : subset_union_right _ _ ... = X ∩ Y : h ... ⊆ X : inter_subset_left _ _,  
end 

lemma union_of_disjoint {X Y Z : set α} : X ∩ Y = ∅ → X ∩ Z = ∅ → X ∩ (Y ∪ Z) = ∅ :=
  λ hY hZ, by {rw [inter_distrib_left, hY, hZ], simp }

@[simp] lemma diff_union (X Y : set α): (X ∩ Y) ∪ (X \ Y) = X  := 
by rw [diff_eq, ←inter_distrib_left, union_compl_self, inter_univ]

@[simp] lemma inter_diff (X Y : set α): X ∩ (Y \ X)  = ∅ := 
by rw [diff_eq, ←inter_assoc, inter_right_comm, inter_compl_self, empty_inter]

@[simp] lemma partition_inter (X Y : set α) : (X ∩ Y) ∩ (X \ Y) = ∅ := 
by rw [inter_assoc, inter_diff, inter_empty]

@[simp] lemma inter_diffs_eq_empty (X Y : set α) : (X \ Y) ∩ (Y \ X) = ∅ := 
by {simp only [diff_eq], rw [inter_assoc, ←inter_assoc Yᶜ], simp}

lemma pair_move {X Z: set α}(Y :set α)(hXY : Z ⊆ X): (X \ Z) ∪ (Y ∪ Z) = X ∪ Y := 
by {ext, simp, tauto, }

lemma diff_empty_subset (X Y : set α) : X \ Y = ∅ → X ⊆ Y := 
λ hXY, by {rw [←diff_union X Y, hXY, union_empty], apply inter_subset_right}

lemma subset_diff_empty (X Y : set α) : X ⊆ Y → X \ Y = ∅ := 
λ hXY, by {rw diff_eq, rw subset_iff_inter_eq_left at hXY, rw [←hXY, inter_assoc, inter_compl_self, inter_empty]}

lemma diff_empty_iff_subset (X Y : set α) : X \ Y = ∅ ↔ X ⊆ Y := 
by {split, apply diff_empty_subset, apply subset_diff_empty}

lemma subset_diff_disjoint (X Y Z: set α) : X ⊆ Y → X ∩ Z = ∅ → X ⊆ Y \ Z := 
λ hXY hXZ, by {rw [disjoint_iff_subset_compl, subset_iff_inter_eq_left] at hXZ, 
                rw [diff_eq, subset_iff_inter_eq_left, inter_comm Y, ←inter_assoc, hXZ, subset_iff_inter_eq_left.mp hXY], }

lemma ssubset_diff_nonempty {X Y : set α} : X ⊂ Y → (Y \ X).nonempty :=
λ hXY, set.nonempty_of_ssubset hXY

lemma union_diff_of_subset  {X Y : set α} : X ⊆ Y → X ∪ (Y \ X) = Y := 
λ h, by {rw [subset_iff_inter_eq_left, inter_comm] at h, have := diff_union Y X, rw h at this, exact this}

lemma diff_eq_self_of_subset_diff {X Y Z : set α}(h : X ⊆ Z \ Y): X \ Y = X :=
by {rw [←disjoint_iff_diff_eq_left, disjoint_iff_subset_compl], refine subset.trans h _, rw diff_eq, simp, }

@[simp] lemma diff_inter_right_eq_empty (X Y : set α) : (Y \ X) ∩ X = ∅ := 
by rw [inter_comm, inter_diff]

@[simp] lemma union_diff (X Y : set α) : X ∪ (Y \ X) = X ∪ Y := 
by {rw [diff_eq, union_distrib_left, union_compl_self, inter_univ]}

@[simp] lemma union_diff_diff (X Y : set α) : (X ∪ Y) \ (Y \ X) = X := 
by rw [diff_eq, diff_eq, compl_inter,compl_compl,union_comm, ←union_distrib_right, inter_compl_self, empty_union]

lemma diff_self_diff (X Y : set α) : X \ (X \ Y) = X ∩ Y := 
by rw [diff_eq, compl_diff, inter_distrib_left, inter_compl_self, empty_union]

lemma inter_distrib_diff (X Y Z : set α) : X ∩ (Y \ Z) = (X ∩ Y) \ (X ∩ Z) := 
by {rw [diff_eq, diff_eq, compl_inter, inter_distrib_left, inter_right_comm, inter_compl_self, empty_inter, empty_union, ←inter_assoc]}

lemma diff_right_comm (X Y Z : set α) : X \ Y \ Z = X \ Z \ Y := 
by simp [diff_eq, inter_right_comm]

@[simp] lemma univ_diff (X : set α) : univ \ X = Xᶜ := 
  (compl_eq_univ_diff X).symm

@[simp] lemma diff_univ (X : set α) : X \ univ = ∅ := 
by rw [diff_eq, compl_univ, inter_empty]


@[simp] lemma symm_diff_self (X : set α) : symm_diff X X = ∅ :=
by {unfold symm_diff, rw [diff_self, empty_union]}

lemma symm_diff_alt (X Y : set α) : symm_diff X Y = (X ∪ Y) \ (X ∩ Y) := 
begin
   unfold symm_diff, 
   repeat {rw [diff_eq]}, 
   rw [compl_inter, inter_distrib_right, inter_distrib_left, inter_distrib_left],
   simp,   
end  

lemma empty_ssubset_nonempty {X : set α} : X.nonempty → ∅ ⊂ X := 
λ h, by {rw ←set.ne_empty_iff_nonempty at h, from ssubset_of_subset_ne (empty_subset X) (ne.symm h)}

lemma nonempty_iff_empty_subset {X : set α}: X.nonempty ↔ ∅ ⊂ X := 
⟨λ h, empty_ssubset_nonempty h, λ h, by {rw ←set.ne_empty_iff_nonempty, from (ne_of_ssubset h).symm, }⟩

lemma scompl_subset_compl.mpr {X Y : set α} : X ⊂ Y → Yᶜ ⊂ Xᶜ := 
λ h, ssubset_of_subset_ne (compl_subset_compl.mpr h.1) 
      (λ h', by {rw (compl_inj h') at h, from ssubset_irrefl _ h}) 

lemma compl_to_ssubset {X Y : set α} : Xᶜ ⊂ Yᶜ → Y ⊂ X := 
λ h, by {have := scompl_subset_compl.mpr h, repeat {rw compl_compl at this}, exact this }

lemma scompl_subset_comm.mpr {X Y : set α} : X ⊂ Yᶜ → Y ⊂ Xᶜ := 
λ h, by {rw [←compl_compl X] at h, exact compl_to_ssubset h}

lemma scompl_subset_comm.mp {X Y : set α} : Xᶜ ⊂ Y → Yᶜ ⊂ X := 
λ h, by {rw [←compl_compl Y] at h, exact compl_to_ssubset h}

lemma ssubset_univ_of_ne_univ {X : set α}: X ≠ univ → X ⊂ univ := 
by {rw ssubset_iff_subset_ne, tauto} 

lemma pairwise_disjoint_inter_sUnion {S S₁ S₂: set (set α)} 
(hdj : pairwise_disjoint S)(h₁ : S₁ ⊆ S)(h₂ : S₂ ⊆ S):
  sUnion (S₁ ∩ S₂) = sUnion S₁ ∩ sUnion S₂ := 
begin
  ext, simp only [mem_inter_iff, mem_sUnion], split, 
  { rintros ⟨t,hT,hxt⟩, rw mem_inter_iff at hT, refine ⟨⟨t,hT.1,hxt⟩,⟨t,hT.2,hxt⟩⟩, },
  rintros ⟨⟨t,h,hxt⟩,⟨t',h',hxt'⟩⟩,
  have := (pairwise_disjoint.elim hdj (mem_of_mem_of_subset h h₁) ((mem_of_mem_of_subset h' h₂)) x hxt hxt'), 
  subst this, use t, tidy, 
end

end set 
import tactic.ext
--import tactic.ring 
import tactic.linarith
import tactic.tidy 
import tactic 
import boolring_tactic
 

import order.boolean_algebra

local attribute [instance] classical.prop_decidable


class boolalg α extends boolean_algebra α :=
(size : α → ℤ)
(size_bot_ax : size ⊥ = 0)
(size_nonneg_ax (X : α) : 0 ≤ size X)
(size_modular_ax (X Y : α) : size (X ⊔ Y) + size (X ⊓ Y) = size X + size Y)
(contains_single_ax (X : α) : X ≠ ⊥ → ∃ Y, Y ≤ X ∧ size Y = 1)

variables {α : Type}[boolalg α]


namespace boolalg 


infix ∪ := has_sup.sup 
infix ∩ := has_inf.inf 
infix ⊆ := has_le.le 


def sss (X Y: α) := (X ⊆ Y ∧ X ≠ Y) 
infix ⊂ := sss 

def symm_diff  (X Y : α) : α := (X \ Y) ∪ (Y \ X)

lemma diff_def (X Y : α) : X \ Y = X ∩ Yᶜ := sdiff_eq


-----------------------------------------------------------

lemma inter_comm (X Y : α) : (X ∩ Y = Y ∩ X) := inf_comm 
lemma union_comm (X Y : α) : (X ∪ Y = Y ∪ X) := sup_comm

lemma inter_assoc (X Y Z : α) : (X ∩ Y) ∩ Z = X ∩ (Y ∩ Z) := inf_assoc
lemma union_assoc (X Y Z : α) : (X ∪ Y) ∪ Z = X ∪ (Y ∪ Z) := sup_assoc 

@[simp] lemma inter_top (X : α)  : X ∩ ⊤ = X := inf_top_eq
@[simp] lemma top_inter (X : α)  : ⊤ ∩ X = X := top_inf_eq 
@[simp] lemma union_bot (X : α)  : X ∪ ⊥ = X := sup_bot_eq
@[simp] lemma bot_union (X : α)  : ⊥ ∪ X = X := bot_sup_eq 

@[simp] lemma union_compl (X: α) : X ∪ Xᶜ = ⊤ := sup_compl_eq_top
@[simp] lemma inter_compl (X: α) : X ∩ Xᶜ = ⊥ := inf_compl_eq_bot 
@[simp] lemma union_compl_rev (X: α) : Xᶜ ∪ X = ⊤ := compl_sup_eq_top
@[simp] lemma inter_compl_rev (X: α) : Xᶜ ∩ X = ⊥ := compl_inf_eq_bot 

lemma union_distrib_right (X Y Z : α) : (X ∩ Y) ∪ Z  = (X ∪ Z) ∩ (Y ∪ Z) := sup_inf_right 
lemma union_distrib_left  (X Y Z : α) :  X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z) := sup_inf_left 
lemma inter_distrib_right (X Y Z : α) : (X ∪ Y) ∩ Z  = (X ∩ Z) ∪ (Y ∩ Z) := inf_sup_right 
lemma inter_distrib_left  (X Y Z : α) :  X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) := inf_sup_left 

lemma bot_unique (X : α) : (∀ (Y: α), Y ∪ X = Y) → X = ⊥ :=  
  λ hX, by calc X = ⊥ ∪ X : (bot_union X).symm ... = ⊥ : hX ⊥

lemma top_unique (X : α) : (∀ (Y: α), Y ∩ X = Y) → X = ⊤ := 
  λ hX, by calc X = ⊤ ∩ X : (top_inter X).symm ... = ⊤ : hX ⊤ 

-- Idempotence

@[simp] lemma union_idem (X : α) : X ∪ X = X := sup_idem
@[simp] lemma inter_idem (X : α) : X ∩ X = X := inf_idem 
@[simp] lemma union_top  (X : α) : X ∪ ⊤ = ⊤ := sup_top_eq
@[simp] lemma top_union  (X : α) : ⊤ ∪ X = ⊤ := top_sup_eq 
@[simp] lemma inter_bot  (X : α) : X ∩ ⊥ = ⊥ := inf_bot_eq 
@[simp] lemma bot_inter  (X : α) : ⊥ ∩ X = ⊥ := bot_inf_eq 
  
-- Absorption
@[simp] lemma absorb_union_inter (X Y : α) : X ∪ (X ∩ Y) = X := sup_inf_self
@[simp] lemma absorb_inter_union (X Y : α) : X ∩ (X ∪ Y) = X := inf_sup_self
  

-- Size 

lemma size_modular (X Y : α) : size (X ∪ Y) + size (X ∩ Y) = size (X) + size Y := size_modular_ax X Y 

@[simp] lemma size_bot : size (⊥ : α) = 0 := size_bot_ax 

lemma compl_size (X : α) : size Xᶜ = size (⊤ : α) - size X :=
  calc size Xᶜ = size (X ∪ Xᶜ) + size (X ∩ Xᶜ) - size X : by linarith [size_modular X Xᶜ]
  ...          = size (⊤ : α)  + size (⊥ : α)  - size X : by rw [union_compl X, inter_compl X]
  ...          = size (⊤ : α) - size X                  : by simp only [add_zero, size_bot]

lemma size_compl (X : α) : size X = size (⊤ : α) - size(Xᶜ) := by linarith [compl_size X]

lemma size_nonneg (X : α) : 0 ≤ size X := size_nonneg_ax X 

lemma contains_single (X : α) : X ≠ ⊥ → (∃ Y, Y ⊆ X ∧ size Y = 1) := contains_single_ax X 
  
lemma union_left_comm (X Y Z : α) : X ∪ (Y ∪ Z) = Y ∪ (X ∪ Z) := sup_left_comm X Y Z
lemma inter_left_comm (X Y Z : α) : X ∩ (Y ∩ Z) = Y ∩ (X ∩ Z) := inf_left_comm X Y Z

lemma union_right_comm (X Y Z : α) : X ∪ Y ∪ Z = X ∪ Z ∪ Y := by simplify_sets [X,Y,Z] 
lemma inter_right_comm (X Y Z : α) : X ∩ Y ∩ Z = X ∩ Z ∩ Y := by simplify_sets [X,Y,Z]

lemma inter_distrib_inter_left (X Y Z : α) : (X ∩ Y) ∩ Z = (X ∩ Z) ∩ (Y ∩ Z) := 
  by simplify_sets [X,Y,Z]

lemma inter_distrib_inter_right (X Y Z : α) : X ∩ (Y ∩ Z) = (X ∩ Y) ∩ (X ∩ Z) := 
  by simplify_sets [X,Y,Z]

lemma union_distrib_union_left (X Y Z : α) : (X ∪ Y) ∪ Z = (X ∪ Z) ∪ (Y ∪ Z) := 
  by simplify_sets [X,Y,Z]

lemma union_distrib_union_right (X Y Z : α) : X ∪ (Y ∪ Z) = (X ∪ Y) ∪ (X ∪ Z) := 
  by simplify_sets [X,Y,Z]



-- sss 


lemma ss_def_union (X Y : α) : (X ⊆ Y) ↔ (X ∪ Y = Y) := sup_eq_right.symm
lemma ss_def_inter (X Y: α) : (X ⊆ Y) ↔ (X ∩ Y = X) := inf_eq_left.symm   

lemma ss_refl (X : α) : X ⊆ X := rfl.ge

lemma ss_def_inter_mp  {X Y : α} : X ⊆ Y → X ∩ Y = X := (le_iff_inf X Y).mp
lemma ss_def_inter_mpr  {X Y : α} : X ∩ Y = X → X ⊆ Y  := (le_iff_inf X Y).mpr
lemma ss_def_union_mp  {X Y : α} : X ⊆ Y → X ∪ Y = Y := sup_eq_right.mpr
lemma ss_def_union_mpr {X Y : α} : X ∪ Y = Y → X ⊆ Y := sup_eq_right.mp 
  
lemma ss_antisymm  {X Y : α} : X ⊆ Y → Y ⊆ X → X = Y := antisymm
lemma inter_ss_left (X Y : α) : (X ∩ Y) ⊆ X := inf_le_left
  

lemma inter_ss_right (X Y : α) : (X ∩ Y) ⊆ Y := inf_le_right 
lemma ss_union_left (X Y : α) : X ⊆ X ∪ Y := le_sup_left
lemma ss_union_right (X Y : α) : Y ⊆ X ∪ Y := le_sup_right
   
lemma ss_top (X : α) : X ⊆ ⊤ := le_top 
lemma top_ss  {X : α} : ⊤ ⊆ X → X = ⊤ := top_le_iff.mp 
lemma bot_ss  (X : α) : ⊥ ⊆ X := bot_le 
lemma ss_bot  {X : α} : X ⊆ ⊥ → X = ⊥ := eq_bot_iff.mpr


lemma disj_iff_ss_compl {X Y : α} : X ∩ Y = ⊥ ↔ X ⊆ Yᶜ := inf_eq_bot_iff_le_compl (union_compl Y) (inter_compl Y)

lemma cover_compl_ss {X Y : α} :  X ∪ Y = ⊤ → Xᶜ ⊆ Y  := 
  λ h, by rw [ss_def_union, ←top_inter (Xᶜ ∪ Y), ←h, ←union_distrib_right, inter_compl, bot_union]

lemma compl_unique {X Y : α} : X ∪ Y = ⊤ → X ∩ Y = ⊥ → Y = Xᶜ := 
  λ hU hI, by {apply ss_antisymm, rw inter_comm at hI, from disj_iff_ss_compl.mp hI, from cover_compl_ss hU}

@[simp] lemma compl_compl  (X : α) : Xᶜᶜ = X := 
  by {apply ss_antisymm, apply cover_compl_ss, from eq.trans (union_comm Xᶜ X) (union_compl X), from disj_iff_ss_compl.mp (inter_compl X)}

lemma compl_inj {X Y : α} : Xᶜ = Yᶜ → X = Y := 
  λ h, by rw [←compl_compl X, ←compl_compl Y, h]

lemma compl_inj_iff {X Y : α} : Xᶜ = Yᶜ ↔ X = Y := 
  ⟨λ h, compl_inj h, λ h, by rw h⟩ 

@[simp] lemma compl_top : (⊤ : α)ᶜ = ⊥ := 
  eq.symm (compl_unique (top_union ⊥) (inter_bot ⊤))

@[simp] lemma compl_bot : (⊥ : α)ᶜ = ⊤ := 
  eq.symm (compl_unique (union_top ⊥) (bot_inter ⊤)) 

lemma bot_of_compl_top {X : α} (hX : Xᶜ = ⊤) : X = ⊥  := 
  by rw [←compl_compl X, hX, compl_top]

lemma top_of_compl_bot {X : α} (hX : Xᶜ = ⊥) : X = ⊤  := 
  by rw [←compl_compl X, hX, compl_bot]

@[simp] lemma inter_compl_left {X : α} : Xᶜ ∩ X = ⊥ := 
  by rw [inter_comm, inter_compl]

@[simp] lemma union_compl_left {X : α} : Xᶜ ∪ X = ⊤ := 
  by rw [union_comm, union_compl]

@[simp] lemma union_compl_union  (X Y : α) : X ∪ (Xᶜ ∪ Y) = ⊤ :=  
  by rw [←top_inter(X ∪ (Xᶜ ∪ Y)), ←union_compl, ←union_distrib_left, absorb_inter_union] 

@[simp] lemma inter_compl_inter (X Y : α) : X ∩ (Xᶜ ∩ Y) = ⊥ := 
  by rw [←bot_union(X ∩ (Xᶜ ∩ Y)), ←inter_compl, ←inter_distrib_left, absorb_union_inter]

@[simp] lemma inter_compl_union (X Y : α) : X ∩ (Xᶜ ∪ Y) = X ∩ Y :=
  by rw [inter_distrib_left, inter_compl, bot_union]

@[simp] lemma union_compl_inter (X Y : α) : X ∪ (Xᶜ ∩ Y) = X ∪ Y :=
  by rw [union_distrib_left, union_compl, top_inter]

@[simp] lemma union_inter_compl_inter (X Y : α) : (X ∪ Y) ∪ (Xᶜ ∩ Yᶜ)  = ⊤ := 
  by simplify_sets [X,Y]

@[simp] lemma inter_union_compl_union (X Y : α) : (X ∩ Y) ∩ (Xᶜ ∪ Yᶜ)  = ⊥ := 
  by simplify_sets [X,Y]
  
@[simp] lemma inter_union_compl_inter (X Y : α) : (X ∪ Y) ∩ (Xᶜ ∩ Yᶜ) = ⊥ := 
  by simplify_sets [X,Y]
  
@[simp] lemma union_inter_compl_union  (X Y : α) : (X ∩ Y) ∪ (Xᶜ ∪ Yᶜ) = ⊤ := 
  by simplify_sets [X,Y]

lemma compl_inter (X Y : α) : (X ∩ Y)ᶜ = Xᶜ ∪ Yᶜ := 
  eq.symm (compl_unique (union_inter_compl_union X Y) (inter_union_compl_union X Y))

lemma compl_union (X Y : α) : (X ∪ Y)ᶜ = Xᶜ ∩ Yᶜ := 
  eq.symm (compl_unique (union_inter_compl_inter X Y) (inter_union_compl_inter X Y))

lemma compl_compl_inter_left (X Y : α) : (Xᶜ ∩ Y)ᶜ = X ∪ Yᶜ := 
  by {nth_rewrite 0 ←(compl_compl Y), rw [compl_inter, compl_compl, compl_compl] }

lemma compl_compl_inter_right (X Y : α) : (X ∩ Yᶜ)ᶜ = Xᶜ ∪ Y := 
  by {nth_rewrite 0 ←(compl_compl X), rw [compl_inter, compl_compl, compl_compl] }

lemma compl_compl_union_left (X Y : α) : (Xᶜ ∪ Y)ᶜ = X ∩ Yᶜ := 
  by {nth_rewrite 0 ←(compl_compl Y), rw [compl_union, compl_compl, compl_compl] }

lemma compl_compl_union_right (X Y : α) : (X ∪ Yᶜ)ᶜ = Xᶜ ∩ Y := 
  by {nth_rewrite 0 ←(compl_compl X), rw [compl_union, compl_compl, compl_compl] }

lemma compl_partition (X Y : α) : (X ∩ Y) ∪ (Xᶜ ∩ Y) = Y := 
  by rw [←inter_distrib_right, union_compl, top_inter]

lemma compl_partition_ss  {X Y : α}: X ⊆ Y → X ∪ (Xᶜ ∩ Y) = Y := 
  λ h, by {nth_rewrite 0 ←(ss_def_inter_mp h), from compl_partition X Y}

lemma compl_pair {X Y : α} : (Xᶜ = Y) → (X = Yᶜ) := 
  λ h, by rw [←h, compl_compl]

lemma compl_diff (X Y : α) : (X \ Y)ᶜ = Xᶜ ∪ Y := 
  by rw [diff_def, compl_inter, compl_compl]

@[simp] lemma union_union_compl (X Y : α) : X ∪ (Y ∪ Yᶜ) = ⊤ := 
  by rw[union_compl, union_top]

@[simp] lemma inter_inter_compl (X Y : α) : X ∩ (Y ∩ Yᶜ) = ⊥ := 
  by rw[inter_compl, inter_bot]

@[simp] lemma union_inter_compl (X Y : α) : X ∪ (Y ∩ Yᶜ) = X :=
  by rw [inter_compl, union_bot]

@[simp] lemma inter_union_compl (X Y : α) : X ∩ (Y ∪ Yᶜ) = X :=
  by rw [union_compl, inter_top]

lemma ss_to_compl {X Y : α} : X ⊆ Y → Yᶜ ⊆ Xᶜ := 
  λ hXY, by {rw ss_def_inter at hXY, rw [←hXY, compl_inter, union_comm], apply ss_union_left} 

lemma compl_to_ss {X Y : α}: Xᶜ ⊆ Yᶜ → Y ⊆ X := 
  λ hXY, by {have := ss_to_compl hXY, repeat {rw compl_compl at this}, from this }

lemma ss_compl_right {X Y : α}: X ⊆ Yᶜ → Y ⊆ Xᶜ := 
  λ hXY, by {rw [←compl_compl X] at hXY, from compl_to_ss hXY}

lemma ss_compl_left {X Y : α} : Xᶜ ⊆ Y → Yᶜ ⊆ X := 
  λ hXY, by {rw [←compl_compl Y] at hXY, from compl_to_ss hXY}

lemma ss_of_compl_iff_disjoint {X Y: α} : X ⊆ Yᶜ ↔ X ∩ Y = ⊥ := 
begin 
  rw ss_def_inter,  refine ⟨λ h, _, λ h, _⟩, 
  rw [←h, inter_assoc, inter_comm _ Y, inter_compl, inter_bot], 
  rw [←union_bot (X ∩ Yᶜ), ←h, ←inter_distrib_left, union_comm, union_compl, inter_top] 
end

lemma ss_own_compl {X : α} : X ⊆ Xᶜ → X = ⊥ := 
  λ h, by {rw [ss_def_union,union_compl, ←compl_bot, compl_inj_iff] at h, rw ←h }
----
lemma ss_sss_or_eq {X Y : α} : (X ⊆ Y) → (X ⊂ Y) ∨ X = Y :=    
  λ h, by {unfold sss, by_cases h' : X = Y; tauto} 

-- strict subset


lemma sss_iff (X Y : α) : X ⊂ Y ↔ X < Y := 
begin
  rw lt_iff_le_not_le, 
  refine ⟨λ h, ⟨h.1,λ h', h.2 (ss_antisymm h.1 h'), ⟩, λ h, ⟨h.1,λ h', _⟩⟩, 
  cases h with hl hr, 
  rw h' at hr, 
  from hr (ss_refl _),   
end

lemma sss_size {X Y : α} : (X ⊆ Y) → (size X < size Y) → (X ⊂ Y) := 
  λ hXY hS, ⟨hXY, by {intros heq, rw heq at hS, linarith}⟩

 
lemma sss_bot (X : α) : ¬ X ⊂ ⊥ := 
  λ h, h.2 (ss_bot h.1) 
 


-- more sss 


lemma disjoint_iff_ss_compl {X Y : α} : X ∩ Y = ⊥ ↔ X ⊆ Yᶜ := 
  by {refine ⟨λ h, _, λ h, _⟩, rw [ss_def_inter, ←union_bot (X ∩ Yᶜ), ←h, ←inter_distrib_left], simp, 
    rw [ss_def_inter] at h, rw [←h, inter_assoc], simp } 

lemma ss_trans {X Y Z : α} : X ⊆ Y → Y ⊆ Z →  X ⊆ Z :=
  λ hXY hYZ, by {rw ss_def_inter at *, rw [←hXY, inter_assoc, hYZ]}

lemma inter_ss_union (X Y : α) : X ∩ Y ⊆ X ∪ Y := 
  ss_trans (inter_ss_left X Y) (ss_union_left X Y)

lemma ss_of_inter_mp {X Y Z : α} : X ⊆ Y ∩ Z → X ⊆ Y ∧ X ⊆ Z := 
  λ h, ⟨ss_trans h (inter_ss_left _ _), ss_trans h (inter_ss_right _ _)⟩  

lemma union_of_sss {X Y Z : α} : (X ⊆ Z) → (Y ⊆ Z) → (X ∪ Y ⊆ Z) := 
  λ hXZ hYZ, by {rw ss_def_inter at *, rw [inter_distrib_right, hXZ, hYZ]}

lemma ss_of_inter_mpr  {X Y Z : α} : (X ⊆ Y) → (X ⊆ Z) → (X ⊆ Y ∩ Z) := 
  λ hXY hXZ, by {rw ss_def_inter at *, rw [←inter_assoc, hXY, hXZ]}

lemma ss_of_inter_iff {X Y Z : α} : X ⊆ (Y ∩ Z) ↔ (X ⊆ Y ∧ X ⊆ Z) := 
  ⟨λ h, ss_of_inter_mp h, λ h, ss_of_inter_mpr  h.1 h.2⟩

lemma inter_of_sss (X Y Z : α) : (X ⊆ Z) → (X ∩ Y ⊆ Z) := 
  λ h, ss_trans (inter_ss_left X Y) h

lemma union_of_supsets (X Y Z : α) : (X ⊆ Y) → (X ⊆ Y ∪ Z) := 
  λ h, ss_trans h (ss_union_left Y Z)

lemma ss_inter_ss_left (X Y Z : α) : (X ⊆ Y) → (X ∩ Z) ⊆ (Y ∩ Z) := 
  λ hXY, by {rw ss_def_inter at *, rw [←inter_distrib_inter_left, hXY]}

lemma ss_inter_ss_right (X Y Z : α) : (X ⊆ Y) → (Z ∩ X) ⊆ (Z ∩ Y) := 
  by {rw [inter_comm _ X, inter_comm _ Y], apply ss_inter_ss_left }

lemma ss_union_ss_left (X Y Z : α) : (X ⊆ Y) → (X ∪ Z) ⊆ (Y ∪ Z) := 
  λ hXY, by {rw ss_def_union at *, rw [←union_distrib_union_left, hXY]}

lemma ss_union_ss_right (X Y Z : α) : (X ⊆ Y) → (Z ∪ X) ⊆ (Z ∪ Y) := 
  by {rw [union_comm _ X, union_comm _ Y], apply ss_union_ss_left }

lemma union_ss_pairs {X₁ X₂ Y₁ Y₂ : α} : X₁ ⊆ Y₁ → X₂ ⊆ Y₂ → X₁ ∪ X₂ ⊆ Y₁ ∪ Y₂ :=
  λ h₁ h₂, ss_trans (ss_union_ss_left X₁ Y₁ X₂ h₁) (ss_union_ss_right X₂ Y₂ Y₁ h₂) 

lemma ss_of_set_and_compl {X Y: α} : X ⊆ Y → X ⊆ Yᶜ → X = ⊥ :=
  λ h1 h2, by {have := ss_of_inter_mpr h1 h2, rw inter_compl at this, from ss_bot this}

lemma ss_sss_trans {X Y Z : α} : X ⊆ Y → Y ⊂ Z → X ⊂ Z := 
  λ hXY hYZ, ⟨ss_trans hXY hYZ.1, λ h, by {rw ←h at hYZ, from hYZ.2 (ss_antisymm hYZ.1 hXY)}⟩ 

lemma sss_ss_trans {X Y Z : α} : X ⊂ Y → Y ⊆ Z → X ⊂ Z := 
  λ hXY hYZ, ⟨ss_trans hXY.1 hYZ, λ h, by {rw h at hXY, from hXY.2 (ss_antisymm hXY.1 hYZ)}⟩ 

lemma sss_irrefl (X : α) : ¬ (X ⊂ X) :=
  λ h, h.2 rfl

lemma sss_not_supset {X Y : α} : X ⊂ Y → ¬(Y ⊆ X) :=
  λ h h', sss_irrefl _ (sss_ss_trans h h') 

lemma ss_not_ssupset {X Y : α} : X ⊆ Y → ¬(Y ⊂ X) := 
  λ h h', sss_irrefl _ (ss_sss_trans h h')

lemma eq_of_sss {X Y: α} : X ⊆ Y → ¬(X ⊂ Y) → X = Y := 
  λ h h', by {simp only [not_and, not_not, sss] at h', from h' h}

lemma sss_trans {X Y Z : α}: X ⊂ Y → Y ⊂ Z → X ⊂ Z := 
  λ hXY hYZ, ss_sss_trans hXY.1 hYZ

lemma sss_inter {X Y : α} : X ≠ Y → X ∩ Y ⊂ X ∨ X ∩ Y ⊂ Y:=
  λ h, by {by_contra, push_neg at a, cases a, erw [not_and', not_imp_not] at a_left a_right, 
  from h (eq.trans (a_left (inter_ss_left X Y)).symm (a_right (inter_ss_right X Y)) )}

-- Misc

lemma inter_is_lb  {X Y Z : α} : Z ⊆ X → Z ⊆ Y → Z ⊆ (X ∩ Y) := 
  λ hZX hZY, by {rw ss_def_inter at *, rw [←inter_assoc, hZX, hZY]}

lemma union_is_ub  {X Y Z : α} : X ⊆ Z → Y ⊆ Z → X ∪ Y ⊆ Z := 
  λ hXZ hYZ, by {rw ss_def_union at *, rw [union_assoc, hYZ, hXZ]}

lemma union_of_disjoint {X Y Z : α} : X ∩ Y = ⊥ → X ∩ Z = ⊥ → X ∩ (Y ∪ Z) = ⊥ :=
  λ hY hZ, by {rw [inter_distrib_left, hY, hZ], simp }

lemma diff_ss  (X Y : α) : X \ Y ⊆ X := 
  by {rw diff_def, from inter_ss_left X Yᶜ} 

@[simp] lemma diff_union (X Y : α): (X ∩ Y) ∪ (X \ Y) = X  := 
  by rw [diff_def, ←inter_distrib_left, union_compl, inter_top]

@[simp] lemma inter_diff (X Y : α): X ∩ (Y \ X)  = ⊥ := 
  by rw [diff_def, ←inter_assoc, inter_right_comm, inter_compl, bot_inter]

@[simp] lemma partition_inter (X Y : α) : (X ∩ Y) ∩ (X \ Y) = ⊥ := 
  by rw [inter_assoc, inter_diff, inter_bot]

@[simp] lemma diffs_disj (X Y : α) : (X \ Y) ∩ (Y \ X) = ⊥ := 
  by {simp only [diff_def], rw [inter_assoc, ←inter_assoc Yᶜ], simp}

lemma diff_bot_ss (X Y : α) : X \ Y = ⊥ → X ⊆ Y := 
  λ hXY, by {rw [←diff_union X Y, hXY, union_bot], apply inter_ss_right}

lemma ss_diff_bot (X Y : α) : X ⊆ Y → X \ Y = ⊥ := 
  λ hXY, by {rw diff_def, rw ss_def_inter at hXY, rw [←hXY, inter_assoc, inter_compl, inter_bot]}

lemma diff_bot_iff_ss (X Y : α) : X \ Y = ⊥ ↔ X ⊆ Y := 
  by {split, apply diff_bot_ss, apply ss_diff_bot}

lemma ss_diff_disjoint (X Y Z: α) : X ⊆ Y → X ∩ Z = ⊥ → X ⊆ Y \ Z := 
  λ hXY hXZ, by {rw [disjoint_iff_ss_compl, ss_def_inter] at hXZ, 
                rw [diff_def, ss_def_inter, inter_comm Y, ←inter_assoc, hXZ, ss_def_inter_mp hXY], }

lemma sss_diff_nonempty {X Y : α} : X ⊂ Y → Y \ X ≠ ⊥ :=
  λ hXY, by {intros hYX, rw diff_bot_iff_ss at hYX, from hXY.2 (ss_antisymm hXY.1 hYX)}

lemma union_diff_of_ss  {X Y : α} : X ⊆ Y → X ∪ (Y \ X) = Y := 
  λ h, by {rw [ss_def_inter, inter_comm] at h, have := diff_union Y X, rw h at this, from this}

@[simp] lemma diff_inter (X Y : α) : (Y \ X) ∩ X = ⊥ := 
  by rw [inter_comm, inter_diff]

@[simp] lemma union_diff (X Y : α) : X ∪ (Y \ X) = X ∪ Y := 
  by {rw [diff_def, union_distrib_left, union_compl, inter_top]}

@[simp] lemma union_diff_diff (X Y : α) : (X ∪ Y) \ (Y \ X) = X := 
  by rw [diff_def, diff_def, compl_inter,compl_compl,union_comm, ←union_distrib_right, inter_compl, bot_union]

lemma inter_distrib_diff (X Y Z : α) : X ∩ (Y \ Z) = (X ∩ Y) \ (X ∩ Z) := 
  by {rw [diff_def, diff_def, compl_inter, inter_distrib_left, inter_right_comm, inter_compl, bot_inter, bot_union, ←inter_assoc]}

@[simp] lemma diff_bot (X : α) : X \ ⊥ = X := 
  by {rw [diff_def, compl_bot, inter_top]} 

@[simp] lemma bot_diff (X : α) : ⊥ \ X = ⊥ := 
  by rw [diff_def, bot_inter]

@[simp] lemma top_diff (X : α) : ⊤ \ X = Xᶜ := 
  by rw [diff_def, top_inter]

@[simp] lemma diff_top (X : α) : X \ ⊤ = ⊥ := 
  by rw [diff_def, compl_top, inter_bot]

@[simp] lemma diff_self (X : α) : X \ X = ⊥ := 
  by rw [diff_def, inter_compl X ]

@[simp] lemma symm_diff_self (X : α) : symm_diff X X = ⊥ :=
  by {unfold symm_diff, rw [diff_self, bot_union]}

lemma symm_diff_alt (X Y : α) : symm_diff X Y = (X ∪ Y) \ (X ∩ Y) := 
begin
   unfold symm_diff, 
   repeat {rw [diff_def]}, 
   rw [compl_inter, inter_distrib_right, inter_distrib_left, inter_distrib_left],
   simp,   
end  

lemma size_monotone {X Y: α} (hXY : X ⊆ Y) : size X ≤ size Y := 
  by {have := size_modular X (Y \ X), rw union_diff_of_ss  hXY at this      , 
        rw [inter_diff, size_bot] at this, linarith [size_nonneg(Y \ X)]}

lemma size_subadditive {X Y : α} : size (X ∪ Y) ≤ size X + size Y :=
  by {linarith [size_modular X Y, size_nonneg (X ∩ Y)] }

lemma compl_inter_size (X Y : α) : size (X ∩ Y) + size (Xᶜ ∩ Y) = size Y := 
  by rw [←size_modular, ←inter_distrib_right, union_compl, top_inter, ←inter_distrib_inter_left, inter_compl, bot_inter, size_bot]; ring

lemma compl_inter_size_ss {X Y : α} : X ⊆ Y → size (Xᶜ ∩ Y) = size Y - size X := 
  λ hXY, by {have := compl_inter_size X Y, rw ss_def_inter_mp hXY at this, linarith} 

lemma diff_size {X Y : α} : X ⊆ Y → size (Y \ X) = size Y - size X :=  
  λ hXY, by rw [diff_def, inter_comm, compl_inter_size_ss hXY]

lemma size_disjoint_sum {X Y : α}: X ∩ Y = ⊥ → size (X ∪ Y) = size X + size Y := 
  λ hXY, by {have := size_modular X Y, rw [hXY, size_bot] at this, linarith}

lemma size_modular_diff (X Y : α) : size (X ∪ Y) = size (X \ Y) + size (Y \ X) + size (X ∩ Y) :=
  by {rw [←size_disjoint_sum (diffs_disj X Y)], have := (symm_diff_alt X Y), 
        unfold symm_diff at this,rw this, linarith [diff_size (inter_ss_union X Y)]  }


lemma size_induced_partition (X Y : α) : size X = size (X ∩ Y) + size (X \ Y) := 
  by {nth_rewrite 0 ←diff_union X Y, refine size_disjoint_sum _, apply partition_inter}

lemma size_compl_sum (X : α) : size X + size Xᶜ = size (⊤ : α) := 
  by {have := size_disjoint_sum (inter_compl X), rw (union_compl X) at this, linarith}

lemma size_zero_bot {X : α} : (size X = 0) →  X = ⊥ := 
  λ h, by {by_contra h', cases contains_single X h' with Y hY, cases hY, linarith [size_monotone hY_left] }
    
lemma size_zero_iff_bot {X : α} : (size X = 0) ↔ (X = ⊥) := 
  by {split, apply size_zero_bot, intros h, rw h, from size_bot}

lemma size_nonempty {X : α} : X ≠ ⊥ → 0 < size X  := 
  λ hX, lt_of_le_of_ne (size_nonneg X) (λ h, hX (size_zero_bot h.symm))

lemma size_strict_monotone {X Y : α} : X ⊂ Y → size X < size Y := 
  λ hXY, by {rw [size_induced_partition Y X, inter_comm, ss_def_inter_mp hXY.1], 
                linarith [size_nonempty (sss_diff_nonempty hXY)]} 

lemma eq_of_eq_size_ss {X Y : α} : (X ⊆ Y) → (size X = size Y) → X = Y :=
  λ hXY, by {cases ss_sss_or_eq hXY, intros sXY, exfalso, replace h := size_strict_monotone h, linarith, from λ h', h}

lemma eq_of_ge_size_ss {X Y : α} : (X ⊆ Y) → (size Y ≤ size X) → X = Y :=
  λ hXY hXY', by {apply eq_of_eq_size_ss hXY, from le_antisymm (size_monotone hXY) hXY'}

lemma size_eq_of_supset {X Y : α} : (X ⊆ Y) → (size Y ≤ size X) → size X = size Y := 
  λ hss hs, by linarith[size_monotone hss]

lemma single_ss (X : α) : X ≠ ⊥ → (∃ (Y Z : α), Y ∩ Z = ⊥ ∧ Y ∪ Z = X ∧ size Y = 1) := 
  begin
    intro h, cases contains_single X h with Y hY, use Y, use X \ Y, 
    from ⟨inter_diff _ _,⟨union_diff_of_ss  hY.1,hY.2⟩⟩,
  end

lemma single_ss_nonempty {X : α}: X ≠ ⊥ → (∃ (Y Z : α), Y ∩ Z = ⊥ ∧ Y ∪ Z = X ∧ size Y = 1) := 
  λ hX, single_ss X hX 

lemma union_ssss (X : α) : 1 < size X  → ∃ Y Z : α, Y ⊂ X ∧ Z ⊂ X ∧ Y ∩ Z = ⊥ ∧ Y ∪ Z = X := 
  begin
    intros hX, 
    have h := (λ h', by {rw [h', size_bot] at hX, linarith }: X ≠ ⊥), 
    rcases single_ss X h with ⟨Y,⟨Z,⟨hI,hU,h1⟩⟩⟩, use Y, use Z, 
    refine ⟨⟨by {rw ←hU, apply ss_union_left},_⟩,⟨by {rw ←hU, apply ss_union_right},_⟩,hI,hU⟩, 
    intros hYX, rw hYX at h1, linarith, 
    intros hZX, 
    have := size_modular Y Z, 
    rw [hU, hI, size_bot, h1,hZX] at this, 
    linarith
  end

lemma sss_to_compl {X Y : α} : X ⊂ Y → Yᶜ ⊂ Xᶜ := 
  λ h, ⟨ss_to_compl h.1, λ h', h.2 (compl_inj h').symm⟩

lemma compl_to_sss {X Y : α} : Xᶜ ⊂ Yᶜ → Y ⊂ X := 
  λ h, by {have := sss_to_compl h, repeat {rw compl_compl at this}, from this }

lemma sss_compl_right {X Y : α} : X ⊂ Yᶜ → Y ⊂ Xᶜ := 
  λ h, by {rw [←compl_compl X] at h, from compl_to_sss h}

lemma sss_compl_left {X Y : α} : Xᶜ ⊂ Y → Yᶜ ⊂ X := 
  λ h, by {rw [←compl_compl Y] at h, from compl_to_sss h}


end boolalg



import boolalg
import init.meta.interactive_base

open boolalg 

variables {A : boolalg}

----------------------------------------------

lemma symm_diff_three (X Y Z : A) : symm_diff (symm_diff X Y) Z = X ∩ Yᶜ ∩ Zᶜ ∪ Y ∩ Xᶜ ∩ Zᶜ ∪ (Z ∩ (Xᶜ ∩ Yᶜ) ∪ Z ∩ (Y ∩ X)) :=
begin
  unfold symm_diff,
  repeat {rw diff_eq},
  repeat {rw inter_distrib_right},
  rw [compl_union, compl_inter, compl_inter, compl_compl, compl_compl], 
  repeat {rw inter_distrib_left},
  repeat {rw inter_distrib_right},
  rw [inter_compl_self Y, inter_comm Xᶜ X, inter_compl_self X, bot_union, union_bot]
end

lemma symm_diff_comm (X Y : A) : symm_diff X Y = symm_diff Y X := 
  by {unfold symm_diff, rw union_comm}


lemma symm_diff_assoc (X Y Z : A) : symm_diff (symm_diff X Y) Z = symm_diff X (symm_diff Y Z) := 
begin
  rw [symm_diff_three, symm_diff_comm, symm_diff_three],
  rw [inter_comm Y Xᶜ, inter_comm Z, inter_comm Z, inter_comm Y X, inter_right_comm Y, inter_assoc Z
      , inter_comm Y, inter_comm Z, inter_comm Yᶜ, inter_comm Z Y],
    nth_rewrite 1 ←union_assoc, 
    nth_rewrite 4 union_comm,  
    repeat {rw ←union_assoc},
    repeat {rw ←inter_assoc}
end

lemma symm_diff_distrib_inter_left (X Y Z : A) : X ∩ (symm_diff Y Z)  = symm_diff (X ∩ Y) (X ∩ Z) := 
  by {unfold symm_diff, rw [inter_distrib_left, inter_distrib_diff, ←inter_distrib_diff, ←inter_distrib_diff]}

lemma symm_diff_distrib_inter_right (X Y Z : A) : (symm_diff X Y) ∩ Z  = symm_diff (X ∩ Z) (Y ∩ Z) := 
  by {rw [inter_comm, inter_comm X, inter_comm Y], apply symm_diff_distrib_inter_left}

lemma symm_diff_inter (X Y : A) : 
  symm_diff X (X ∩ Y) = X \ Y := 
  by rw [symm_diff_alt, absorb_union_inter, diff_eq, compl_inter, inter_distrib_left,
     union_comm, union_inter_compl_self, compl_inter, inter_distrib_left, union_comm, union_inter_compl_self, ← diff_eq] -- inter_compl_self, bot_union, compl_inter, inter_distrib_left],  
  
lemma top_symm_diff (X : A) : 
  symm_diff ⊤ X = Xᶜ := 
  by {unfold symm_diff, simp only [top_diff, diff_top, union_bot]}
-----------------------------------------------



@[simp] instance to_comm_ring  : comm_ring A  := 
{ 
  add := λ X Y, symm_diff X Y, 
  add_assoc := λ X Y Z, symm_diff_assoc X Y Z,
  zero := ⊥,
  zero_add := λ X, by {simp only [has_add.add], unfold symm_diff, rw [bot_diff, diff_bot, bot_union]},--rw [bot_union, boolalg.compl_bot, top_union, inter_top]},
  add_zero := λ X, by {simp only [has_add.add], unfold symm_diff, rw [bot_diff, diff_bot, union_bot]},
  neg := λ X, X, 
  add_left_neg := λ X, symm_diff_self X, 
  add_comm := λ X Y, symm_diff_comm X Y, 
  mul := λ X Y, X ∩ Y,
  mul_assoc := λ X Y Z, inter_assoc X Y Z,
  one := ⊤,
  one_mul := λ X, top_inter X,
  mul_one := λ X, inter_top X,
  left_distrib := λ X Y Z, symm_diff_distrib_inter_left X Y Z,
  right_distrib := λ X Y Z, symm_diff_distrib_inter_right X Y Z, 
  mul_comm := λ X Y, inter_comm X Y, 
}


lemma one_plus (X : A) : 1 + X = Xᶜ := 
  top_symm_diff X 

lemma plus_one (X : A) : X + 1 = Xᶜ := 
  by {rw add_comm, from one_plus X} 

lemma top_to_boolalg : (⊤ : A) = (1 : A) := rfl

lemma bot_to_boolalg : (⊥ : A) = (0 : A) := rfl

lemma symm_diff_to_boolalg {X Y : A} :  (X \ Y) ∪ (Y \ X) = X + Y := rfl 

lemma inter_to_boolalg {X Y : A} : X ∩ Y = X * Y := rfl 

lemma union_to_boolalg {X Y : A} : X ∪ Y = (X + Y) + X*Y := 
  begin 
    rw [add_assoc], 
    nth_rewrite 1 ←one_mul Y, 
    rw [←right_distrib, one_plus, ←symm_diff_to_boolalg, ←inter_to_boolalg, diff_eq, diff_eq, inter_right_comm, compl_inter],
    simp,
  end 

lemma compl_to_boolalg {X : A} : Xᶜ = X + 1 := 
  (plus_one X).symm 

lemma subset_to_boolalg {X Y : A} : X ⊆ Y ↔ X*Y = X := 
  by {rw ←inter_to_boolalg, exact subset_iff_inter_eq_left X Y} 

lemma diff_to_boolalg {X Y : A} : X \ Y = X*(Y + 1) := 
  by rw [plus_one, ←inter_to_boolalg, diff_eq]




mk_simp_attribute ba_simp "ba_simplg"

@[simp, ba_simp] lemma times_idem (X : A) : X*X = X := inter_idem X 
@[simp, ba_simp] lemma plus_zero (X : A) : X+0 = X := add_zero X 
@[simp, ba_simp] lemma zero_plus (X : A) : 0+X = X := zero_add X   
@[simp, ba_simp] lemma times_zero (X : A) : X*0 = 0 := inter_bot X 
@[simp, ba_simp] lemma zero_times (X : A) : 0*X = 0 := bot_inter X
@[simp, ba_simp] lemma times_one (X : A) : X*1 = X := inter_top X 
@[simp, ba_simp] lemma one_times (X : A) : 1*X = X := top_inter X 
@[simp, ba_simp] lemma times_comm (X Y : A) : X*Y = Y*X := mul_comm X Y 
@[simp, ba_simp] lemma times_assoc (X Y Z : A) : X*Y*Z = X*(Y*Z) := mul_assoc X Y Z
@[simp, ba_simp] lemma plus_comm (X Y : A) : X+Y=Y+X := add_comm X Y
@[simp, ba_simp] lemma plus_assoc (X Y Z : A) : X+Y+Z = X+(Y+Z)  := add_assoc X Y Z

@[simp, ba_simp] lemma rmult_cancel (X Y : A) : X*(X*Y) = X*Y := 
  by rw [←mul_assoc, times_idem]


@[simp] lemma two_eq_zero : (2 : A) = (0 : A) := 
  begin
    have : (1:A) + (1:A) = (2:A) := rfl, rw ←this,
    rw [one_plus, ←top_to_boolalg, ←bot_to_boolalg],
    simp, 
  end


@[simp, ba_simp] lemma two_times (X : A) : 2*X = 0 := by simp

@[simp, ba_simp] lemma times_two (X : A) : X*2 = 0 := by simp


lemma neg_self (X : A) : X = -X := 
  by {have := calc X + X = X*2 : by ring ... = 0 : by simp, ring, }

@[simp, ba_simp] lemma plus_self (X : A) : X + X = 0 := 
  by {ring SOP, rw two_eq_zero, ring}

@[simp, ba_simp] lemma plus_self_left (X Y : A) : X + (X + Y )= Y := 
  by {ring, rw two_eq_zero, ring}

@[simp, ba_simp] lemma power_cancel (X : A) (n : nat) : X^(n.succ) = X := 
  by {induction n with n IH, ring, rw [pow_succ' X (nat.succ n), IH, times_idem] }

@[simp, ba_simp] lemma distrib_cancel (X Y : A) : X*Y + X*(Y+1) = X := 
  by {rw[←left_distrib], simp only [plus_self_left, times_one]} 


--@[simp, ba_simp] lemma one_sandwich (X : A) : 1 + (X+1) = X := sorry 


--@[simp, ba_simp] lemma mul_cancel_left (S X: A) : S*(S*X) = S*X := sorry 



lemma one_side {X Y : A} : X = Y ↔ X + Y = 0 := 
  by {refine ⟨λ h, by{rw h, simp}, λ h, _⟩, rw (eq_neg_of_add_eq_zero h), exact (neg_self Y).symm }

@[simp, ba_simp] lemma prod_comp_cancel (X : A) : X*(X+1) = 0 := 
  by {ring SOP, simp }
  
lemma expand_product {X₁ X₂ Y₁ Y₂ S : A} : (X₁ * S + X₂ * (S+1)) * (Y₁ * S + Y₂ * (S+1)) = X₁ * Y₁ * S + X₂ * Y₂ * (S+1) :=
  by {apply one_side.mpr, ring, ring SOP, simp only with ba_simp, ring, simp}


meta def set_to_ring_eqn : tactic unit := do
`[try {simp only
    [top_to_boolalg, bot_to_boolalg, symm_diff_to_boolalg, inter_to_boolalg, union_to_boolalg, 
      diff_to_boolalg, compl_to_boolalg, subset_to_boolalg] at *}]

/-
meta def normalize_boolalg_eqns : tactic unit := do
  `[set_to_ring_eqn,
    try {apply one_side.mpr},
    ring SOP]
meta def simp_only_ba_simp : tactic unit :=
  do `[simp only with ba_simp]
meta def simp_ba_simp : tactic unit :=
  do `[simp with ba_simp]
--meta def simp_ba_simp_hyp : tactic unit :=
-/
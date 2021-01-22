
import order.boolean_algebra 
import tactic 
open boolean_algebra 

variables {α : Type*}[boolean_algebra α]


@[simp] def symm_diff (X Y : α) : α := (X \ Y) ⊔ (Y \ X) 
@[simp] lemma sdiff_def {X Y : α} : X \ Y = X ⊓ Yᶜ := sdiff_eq 

-- commutativity/associativity with explicit params for easier rewriting 
lemma inf_comm' (X Y : α) : X ⊓ Y = Y ⊓ X := by apply inf_comm 
lemma inf_assoc' (X Y Z : α) : X ⊓ Y ⊓ Z = X ⊓ (Y ⊓ Z) := by apply inf_assoc  

lemma inf_right_comm (X Y Z : α) : X ⊓ Y ⊓ Z = X ⊓ Z ⊓ Y := by rw [inf_assoc, inf_comm' Y, ←inf_assoc]

local attribute [simp] symm_diff sdiff_eq 

lemma symm_diff_comm (X Y : α) : symm_diff X Y = symm_diff Y X := 
  by simp [sup_comm] 

-- 'Normal form' for associativity 
lemma symm_diff_three (X Y Z : α) : 
  symm_diff (symm_diff X Y) Z = X ⊓ Yᶜ ⊓ Zᶜ ⊔ Y ⊓ Xᶜ ⊓ Zᶜ ⊔ (Z ⊓ (Xᶜ ⊓ Yᶜ) ⊔ Z ⊓ (Y ⊓ X)) :=
begin
  simp only [symm_diff, sdiff_def, inf_sup_right, compl_sup,compl_inf,compl_compl'],
  repeat {rw inf_sup_left},
  repeat {rw inf_sup_right},
  rw [inf_compl_eq_bot, inf_comm' Xᶜ X, inf_compl_eq_bot], 
  simp, 
end

lemma symm_diff_assoc (X Y Z : α) : symm_diff (symm_diff X Y) Z = symm_diff X (symm_diff Y Z) := 
begin
  rw [symm_diff_three, symm_diff_comm, symm_diff_three],
  rw [inf_comm' Y Xᶜ, inf_comm' Z, inf_comm' Z, inf_comm' Y X, inf_right_comm Y, 
      inf_assoc' Z, inf_comm' Y, inf_comm' Z, inf_comm' Yᶜ, inf_comm' Z Y],
    nth_rewrite 1 ←sup_assoc, 
    nth_rewrite 4 sup_comm,  
    repeat {rw ←sup_assoc},
    repeat {rw ←inf_assoc},
end

lemma inf_distrib_diff (X Y Z : α) : X ⊓ (Y \ Z) = (X ⊓ Y) \ (X ⊓ Z) := 
  by {simp only [sdiff_def, compl_inf, inf_sup_left], rw [inf_right_comm _ Y, ←inf_assoc], simp,  }

lemma symm_diff_distrib_inf_left (X Y Z : α): X ⊓ (symm_diff Y Z)  = symm_diff (X ⊓ Y) (X ⊓ Z) := 
  by simp only [symm_diff, inf_sup_left, inf_sup_right, inf_distrib_diff] 
    
lemma symm_diff_distrib_inf_right (X Y Z : α): (symm_diff X Y) ⊓ Z  = symm_diff (X ⊓ Z) (Y ⊓ Z) := 
  by {rw [inf_comm', inf_comm' X, inf_comm' Y], apply symm_diff_distrib_inf_left}

lemma symm_diff_inter (X Y : α) : 
  symm_diff X (X ⊓ Y) = X \ Y := 
  by simp [inf_right_comm X Y, ←inf_assoc' _ Xᶜ, inf_sup_left]

lemma sup_sdiff (X Y : α) : 
  X ⊔ (X \ Y) = X :=
  by simp  

lemma top_symm_diff (X : α) : 
  symm_diff ⊤ X = Xᶜ := 
  by simp 

lemma symm_diff_self (X : α) : 
  symm_diff X X = ⊥ := 
  by simp 

@[simp] lemma bot_diff (X : α) :
  ⊥ \ X = ⊥ := 
  by simp

@[simp] lemma diff_bot (X : α) :
  X \ ⊥ = X := 
  by simp  

@[simp] lemma le_iff_inf (X Y : α) : 
  X ≤ Y ↔ X ⊓ Y = X := 
  inf_eq_left.symm

-----------------------------------------------

@[simp] instance to_comm_ring : comm_ring α := 
{ 
  add := λ X Y, symm_diff X Y, 
  add_assoc := λ X Y Z, symm_diff_assoc X Y Z,
  zero := ⊥,
  zero_add := λ X, by simp [has_add.add],
  add_zero := λ X, by simp [has_add.add],
  neg := λ X, X, 
  add_left_neg := λ X, symm_diff_self X, 
  add_comm := λ X Y, symm_diff_comm X Y, 
  mul := λ X Y, X ⊓ Y,
  mul_assoc := λ X Y Z, inf_assoc,
  one := ⊤,
  one_mul := λ X, top_inf_eq,
  mul_one := λ X, inf_top_eq,
  left_distrib := λ X Y Z, symm_diff_distrib_inf_left X Y Z,
  right_distrib := λ X Y Z, symm_diff_distrib_inf_right X Y Z, 
  mul_comm := λ X Y, inf_comm, 
}

lemma one_add (X : α) : 1 + X = Xᶜ := 
  top_symm_diff X 

lemma add_one (X : α) : X + 1 = Xᶜ := 
  by {rw add_comm, from top_symm_diff X} 

lemma top_to_ring: (⊤ : α) = (1 : α) := rfl

lemma bot_to_ring : (⊥ : α) = (0 : α):= rfl

lemma symm_diff_to_ring {X Y : α} : (X \ Y) ⊔ (Y \ X) = X + Y := rfl 

lemma inf_to_ring {X Y : α} : X ⊓ Y = X * Y := rfl 

lemma sup_to_ring {X Y : α} : X ⊔ Y = (X + Y) + X*Y := 
begin 
  rw [add_assoc], 
  nth_rewrite 1 ←one_mul Y, 
  rw [←right_distrib, one_add, ←symm_diff_to_ring, ←inf_to_ring],
  rw [sdiff_def, sdiff_def, inf_right_comm, compl_inf, inf_sup_left], 
  simp only [compl_compl', inf_idem],
  rw [←sdiff_def, inf_comm' Xᶜ, ←sdiff_def, sup_sdiff, sup_sdiff_same], 
end 

lemma compl_to_ring {X : α} : 
  Xᶜ = X + 1 := 
  (add_one X).symm 

lemma le_to_ring {X Y : α} : 
  X ≤ Y ↔ X*Y = X := 
  by {rw ←inf_to_ring, from inf_eq_left.symm} 

lemma diff_to_ring {X Y : α} : 
  X \ Y = X*(Y + 1) := 
  by rw [add_one, ←inf_to_ring, sdiff_def]
---------------------

@[simp] lemma mul_idem (X : α): 
  X*X = X := 
  inf_idem 

@[simp] lemma two_eq_zero : 
  (2 : α) = (0 : α) := 
  let h : (2:α) = (1:α) + (1:α) := rfl in
  by rw [h, one_add, ←top_to_ring, ←bot_to_ring, compl_top]

@[simp] lemma add_self (X : α): 
  X + X = 0 := 
  by {ring SOP, rw two_eq_zero, from mul_zero X}

lemma add_self_left (X Y : α):
   X + (X + Y) = Y :=  
   by rw [←add_assoc, add_self, zero_add]

@[simp] lemma prod_comp_cancel (X : α) : X*(X+1) = 0 := 
  by {ring SOP, simp}
  
lemma expand_product {X₁ X₂ Y₁ Y₂ S : α} : 
  (X₁ * S + X₂ * (S+1)) * (Y₁ * S + Y₂ * (S+1)) = X₁ * Y₁ * S + X₂ * Y₂ * (S+1):=
  begin
    simp only [←mul_assoc, mul_comm _ S, prod_comp_cancel, mul_idem, left_distrib, right_distrib, mul_one],
    ring SOP, 
    simp [mul_comm, two_eq_zero, (by ring : (3:α) = (2:α) + (1:α)), mul_left_comm],
  end


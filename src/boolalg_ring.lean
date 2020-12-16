import boolalg

open boolalg 

variables {A : boolalg}

----------------------------------------------

lemma symm_diff_alt (X Y : A) : symm_diff X Y = (X ∪ Y) - (X ∩ Y) := sorry  

lemma symm_diff_three (X Y Z : A) : symm_diff (symm_diff X Y) Z = X ∩ Yᶜ ∩ Zᶜ ∪ Y ∩ Xᶜ ∩ Zᶜ ∪ (Z ∩ (Xᶜ ∩ Yᶜ) ∪ Z ∩ (Y ∩ X)) :=
begin
  unfold symm_diff has_sub.sub, 
  repeat {rw inter_distrib_right},
  rw [compl_union, compl_inter, compl_inter, compl_compl, compl_compl], 
  repeat {rw inter_distrib_left},
  repeat {rw inter_distrib_right},
  rw [inter_compl Y, inter_comm Xᶜ X, inter_compl X, bot_union, union_bot]
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

lemma symm_diff_distrib_inter_left (X Y Z : A): X ∩ (symm_diff Y Z)  = symm_diff (X ∩ Y) (X ∩ Z) := 
  by {unfold symm_diff, rw [inter_distrib_left, inter_distrib_diff, ←inter_distrib_diff, ←inter_distrib_diff]}

lemma symm_diff_distrib_inter_right (X Y Z : A): (symm_diff X Y) ∩ Z  = symm_diff (X ∩ Z) (Y ∩ Z) := 
  by {rw [inter_comm, inter_comm X, inter_comm Y], apply symm_diff_distrib_inter_left}

lemma symm_diff_inter (X Y : A) : 
  symm_diff X (X ∩ Y) = X - Y := 
  by rw [symm_diff_alt, absorb_union_inter, diff_def, compl_inter, inter_distrib_left,
     union_comm, union_inter_compl, compl_inter, inter_distrib_left, union_comm, union_inter_compl, ← diff_def] -- inter_compl, bot_union, compl_inter, inter_distrib_left],  
  
lemma top_symm_diff (X : A) : 
  symm_diff ⊤ X = Xᶜ := 
  by {unfold symm_diff, simp only [top_diff, diff_top, union_bot]}
-----------------------------------------------



@[simp] instance to_ring  : comm_semiring A  := 
{ 
  add := λ X Y, symm_diff X Y, 
  add_assoc := λ X Y Z, symm_diff_assoc X Y Z, --by {simp only [has_add.add], exact } 
  zero := ⊥,
  zero_add := λ X, by {simp only [has_add.add], unfold symm_diff, rw [bot_diff, diff_bot, bot_union]},--rw [bot_union, boolalg.compl_bot, top_union, inter_top]},
  add_zero := λ X, by {simp only [has_add.add], unfold symm_diff, rw [bot_diff, diff_bot, union_bot]},
  add_comm := λ X Y, symm_diff_comm X Y, 
  mul := λ X Y, X ∩ Y,
  mul_assoc := λ X Y Z, inter_assoc X Y Z,
  one := ⊤,
  one_mul := λ X, top_inter X,
  mul_one := λ X, inter_top X,
  zero_mul := λ X, by {simp only [has_mul.mul], rw bot_inter},
  mul_zero := λ X, by {simp only [has_mul.mul], rw inter_bot},
  mul_comm := λ X Y, inter_comm X Y, 
  left_distrib := λ X Y Z, symm_diff_distrib_inter_left X Y Z,
  right_distrib := λ X Y Z, symm_diff_distrib_inter_right X Y Z, 
}



lemma one_plus (X : A) : 1 + X = Xᶜ := 
  top_symm_diff X 

lemma plus_one (X : A) : X + 1 = Xᶜ := 
  by {rw add_comm, from one_plus X} 

lemma top_to_boolalg : (⊤ : A) = (1 : A) 
  := rfl

lemma bot_to_boolalg : (⊥ : A) = (0 : A) 
  := rfl

lemma symm_diff_to_boolalg {X Y : A} :  (X - Y) ∪ (Y-X) = X + Y :=
  rfl 


lemma inter_to_boolalg {X Y : A} : X ∩ Y = X * Y := 
  rfl 



lemma union_to_boolalg {X Y : A} : X ∪ Y = (X + Y) + X*Y := 
  begin 
    rw [add_assoc], 
    nth_rewrite 1 ←one_mul Y, 
    rw [←right_distrib, one_plus, ←symm_diff_to_boolalg, ←inter_to_boolalg, diff_def, diff_def, inter_right_comm, compl_inter],
    simp
  end 

lemma compl_to_boolalg {X : A} : Xᶜ = X + 1 := 
  (plus_one X).symm 

lemma subset_to_boolalg {X Y : A} : X ⊆ Y ↔ X*Y = X := 
  by {rw ←inter_to_boolalg, exact inter_subset X Y} 

lemma diff_to_boolalg {X Y : A} : X - Y = X*(Y + 1) := 
  by rw [plus_one, ←inter_to_boolalg, diff_def]

lemma two_eq_zero_boolalg : (2 : A) = (0 : A) := 
  begin
    have : (1:A) + (1:A) = (2:A) := rfl, rw ←this,
    rw one_plus, unfold has_one.one,  
  end

lemma mult_idem_boolalg (X : A): X*X = X := sorry
-- X ⊆ Y ↔ (X ∩ Y = X)


lemma blah {X Y : A} : X ⊆ Y → X ∪ (Y - X) = Y  := 
  begin
     repeat {try {rw union_to_boolalg} , try {rw subset_to_boolalg}, rw diff_to_boolalg }, 
     intro h, 
     have := two_eq_zero_boolalg, 
     have := mult_idem_boolalg X, 
     --intro h, 
     ring SOP, 
     rw [h,this],
     ring SOP,  
     
     --repeat {rw this, rw h, ring_exp}, 
  end

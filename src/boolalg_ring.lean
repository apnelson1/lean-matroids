import boolalg

open boolalg 

variables {A : boolalg}

@[simp] instance to_ring  : comm_semiring A  := 
{ 
  add := λ X Y, (X ∪ Y) ∩ (Xᶜ ∪ Yᶜ),
  add_assoc := λ X Y Z, sorry,
  zero := ⊥,
  zero_add := λ X, by {simp only [has_add.add], rw [bot_union, boolalg.compl_bot, top_union, inter_top]},
  add_zero := λ X, by {simp only [has_add.add], rw [union_bot, boolalg.compl_bot, union_top, inter_top]},
  add_comm := λ X Y, by{simp only [has_add.add], rw [union_comm Y, union_comm Yᶜ]},
  mul := λ X Y, X ∩ Y,
  mul_assoc := λ X Y Z, inter_assoc X Y Z,
  one := ⊤,
  one_mul := λ X, top_inter X,
  mul_one := λ X, inter_top X,
  zero_mul := λ X, by {simp only [has_mul.mul], rw bot_inter},
  mul_zero := λ X, by {simp only [has_mul.mul], rw inter_bot},
  mul_comm := λ X Y, inter_comm X Y, 
  left_distrib := sorry,
  right_distrib := sorry  
}

lemma inter_to_boolalg {X Y : A} : X ∩ Y = X * Y := rfl 

lemma union_to_boolalg {X Y : A} : X ∪ Y = (X + Y) + X*Y := sorry 

lemma compl_to_boolalg {X : A} : Xᶜ = X + 1 := sorry 

lemma subset_to_boolalg {X Y : A} : X ⊆ Y ↔ X*Y = X := sorry 

lemma diff_to_boolalg {X Y : A} : X - Y = X*(Y + 1) := sorry 

lemma two_eq_zero_boolalg : (2 : A) = (0 : A) := sorry 

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

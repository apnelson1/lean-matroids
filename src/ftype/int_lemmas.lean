import tactic 

--some number stuff

lemma le_sub_one_of_le_of_ne {x y : ℤ} : 
  x ≤ y → x ≠ y → x ≤ y - 1 :=
  λ h h', int.le_sub_one_of_lt (lt_of_le_of_ne h h')

lemma le_of_not_gt' {x y : ℤ} : 
  ¬ (y < x) → x ≤ y := 
  not_lt.mp

lemma lt_iff_le_sub_one {x y : ℤ} :
  x < y ↔ x ≤ y - 1 := 
  int.le_sub_one_iff.symm

lemma nonneg_int_strong_induction (P : ℤ → Prop) : 
  P 0 → (∀ n, 0 < n → (∀ m, 0 ≤ m → m < n → P m) → P n) → (∀ n₀, 0 ≤ n₀ → P n₀) := 
begin
  intros h0 IH n₀ hn₀, 
  set Q : ℕ → Prop := λ s, (∀ t, t ≤ s → P t) with hQ,
  suffices : Q (n₀.to_nat), 
  
  have h' := this n₀.to_nat (le_of_eq _), 
  rw (int.to_nat_of_nonneg hn₀) at h', from h', refl,
  
  apply nat.case_strong_induction_on _, 
  refine λ t ht, _, 
  rw nat.eq_zero_of_le_zero ht, norm_cast, from h0, 

  intros n hn t ht, 
  cases (nat.eq_zero_or_pos t), 
  rw h, norm_cast, from h0, 
  
  apply IH t _, 
  intros m h0m hmt, 
  have := hn (m.to_nat) _ (m.to_nat) (le_refl _), 
  rw (int.to_nat_of_nonneg h0m) at this, from this,

  rw int.to_nat_le, 
  rw [←int.coe_nat_le_coe_nat_iff, ←int.coe_nat_add_one_out] at ht, linarith, 

  exact int.coe_nat_pos.mpr h, 
end
  
-------------------------------------------------------------------------------


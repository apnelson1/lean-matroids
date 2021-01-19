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
  P 0 → (∀ n, 0 < n → (∀ m, m < n → P m) → P n) → (∀ n₀, 0 ≤ n₀ → P n₀) := 
  sorry 
-------------------------------------------------------------------------------


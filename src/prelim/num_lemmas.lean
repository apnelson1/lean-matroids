import data.set.intervals 
import tactic 

universes u v w 
open_locale classical 

/-! Some simple additions to the api -/

open set 

namespace int 


lemma le_sub_one_of_le_of_ne {x y : ℤ} : 
  x ≤ y → x ≠ y → x ≤ y - 1 :=
  λ h h', int.le_sub_one_of_lt (lt_of_le_of_ne h h')

lemma le_of_not_gt' {x y : ℤ} : 
  ¬ (y < x) → x ≤ y := 
  not_lt.mp

lemma nonneg_le_one_iff {x : ℤ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
  x = 0 ∨ x = 1 :=
by {by_cases h : x ≤ 0, left, apply le_antisymm h h0, 
    push_neg at h, rw int.le_sub_one_iff.symm at h, 
    right, linarith, }

lemma nat_le_two_iff {x : ℕ} (h2 : x ≤ 2) : 
  x = 0 ∨ x = 1 ∨ x = 2 :=
by {cases x, tauto, cases x, tauto, cases x, tauto, repeat {rw nat.succ_eq_add_one at h2}, linarith} 

lemma nonneg_le_two_iff {x : ℤ} (h0 : 0 ≤ x) (h2 : x ≤ 2) :
  x = 0 ∨ x = 1 ∨ x = 2 :=
begin
  by_cases h2' : 2 ≤ x, right, right, apply le_antisymm h2 h2', 
  push_neg at h2', rw int.le_sub_one_iff.symm at h2', 
  cases nonneg_le_one_iff h0 h2', {left, exact h}, {right, left, exact h},
end 

lemma to_nat_zero_of_nonpos {x : ℤ} (hx : x ≤ 0): 
  x.to_nat = 0 := 
by {rcases em (x = 0) with (rfl | hx'), simp, apply to_nat_zero_of_neg (lt_of_le_of_ne hx hx'), }

end int



namespace nat

lemma lt_iff_succ_le {a b : ℕ} : 
  a < b ↔ a.succ ≤ b := 
⟨λ h, succ_le_of_lt h, λ h, lt_of_succ_le h⟩ 

end nat 



section order

variables {α : Type*} [partial_order α] {a b c : α}

lemma squeeze_le_trans_left (hab : a ≤ b) (hbc : b ≤ c) (hac : a = c):
  a = b := 
le_antisymm hab (hbc.trans hac.symm.le)

lemma squeeze_le_trans_right (hab : a ≤ b) (hbc : b ≤ c) (hac : a = c):
  b = c := 
le_antisymm hbc (hac.symm.le.trans hab)

lemma squeeze_le_trans (hab : a ≤ b) (hbc : b ≤ c) (hac : a = c):
  a = b ∧ b = c := 
⟨squeeze_le_trans_left hab hbc hac, squeeze_le_trans_right hab hbc hac⟩ 

end order 
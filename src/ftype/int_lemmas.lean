import tactic 

-- some very mild additions to the int API in mathlib  

namespace int 

lemma le_sub_one_of_le_of_ne {x y : ℤ} : 
  x ≤ y → x ≠ y → x ≤ y - 1 :=
  λ h h', int.le_sub_one_of_lt (lt_of_le_of_ne h h')

lemma le_of_not_gt' {x y : ℤ} : 
  ¬ (y < x) → x ≤ y := 
  not_lt.mp

lemma lt_iff_le_sub_one {x y : ℤ} :
  x < y ↔ x ≤ y - 1 := 
  int.le_sub_one_iff.symm
  
end int 
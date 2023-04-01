import .size .induction_size

noncomputable theory
open_locale classical big_operators

variables {α : Type*}

def neg_one_pow (n : ℤ) : ℤ := (-1)^(n.nat_abs)



theorem ie (s : set (set α)) :
  size (⋃₀ s) = ∑ᶠ t in s.powerset \ {∅}, neg_one_pow (size t) * size (⋂₀ t) :=
begin
  revert s,
  refine induction_set_size_insert _ (by simp) _,
  intros s a ha IH,




end
import tactic data.real.basic 
----------------------------------------------------------------\
open set 

structure foo (a b : ℤ) := 
(d : ℤ)
(hd : 0 < d ∧ a < d ∧ d < b)

def apart (a b : ℤ) := nonempty (foo a b)

lemma bar {a b : ℤ} : 
  apart a b ↔ (a + 1 < b) ∧ (b < 0) :=
by sorry 

lemma baz (a b : ℤ) (h : apart a b) : false := 
by {obtain ⟨h₁,h₂⟩ := bar.mp h, }

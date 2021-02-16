import prelim.collections prelim.size prelim.induction prelim.minmax
import .rankfun
import tactic 

noncomputable theory 
open_locale classical 

open matroid set 

variables {U : Type}[fintype U]

def is_simple (M : matroid U) :=
  ∀ X, size X ≤ 2 → M.is_indep X 


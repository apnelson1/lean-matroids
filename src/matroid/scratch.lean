import tactic 

variables {E : Type*} {P Q : set E} {e : E}

example (heQ : e ∉ Q) (hPQ : P ⊆ Q) : e ∉ P := by {library_search, }
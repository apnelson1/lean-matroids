import tactic 

variables {E : Type*} {P Q : Prop} {e : E}

example {hP : P ∨ Q} {hQ : ¬P} : Q := by {library_search, }
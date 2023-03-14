
axiom choice {α : Sort*} : nonempty α → α 

lemma em (P : Prop) : P ∨ ¬P :=
begin
  suffices : nonempty (P ∨ ¬P), 
  exact @choice (P ∨ ¬P) this,

  

end  

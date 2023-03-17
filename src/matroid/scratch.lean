import tactic 

open_locale classical 

variables {E : Type*} {P Q : Prop} {e : E}

example {hP : P ↔ Q} {hQ : ¬Q} : ¬P := 
begin
  have := mt, 
end 


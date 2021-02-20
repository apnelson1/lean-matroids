import .set 

open_locale classical 
noncomputable theory 


/-! This file was an attempt to create a propositional typeclass in place of fintype. It currently breaks everything it touches 
 because of infinite loops in instance searches (one would like to go back and forth between this new typeclass and fintype)
 but it would help with annoying mismatch issues if it could be made to work. -/


/-- Propositional finiteness instance. Classically equivalent to fintype, 
    but is propositional to hopefully avoid fintype mismatch issues -/
class is_finite (α : Type) := 
(fin : nonempty (fintype α))

instance of_fintype {α : Type}[fintype α] : is_finite α := { fin := nonempty.intro (infer_instance) }

instance of_is_finite {α : Type}[ft : is_finite α] : fintype α := classical.choice ft.fin
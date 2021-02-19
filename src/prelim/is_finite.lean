import .set 

open_locale classical 
noncomputable theory 

/-- Propositional finiteness instance. Classically equivalent to fintype, 
    but is propositional to hopefully avoid fintype mismatch issues -/
class is_finite (α : Type) := 
(fin : nonempty (fintype α))

instance of_fintype {α : Type}[fintype α] : is_finite α := { fin := nonempty.intro (infer_instance) }

instance of_is_finite {α : Type}[ft : is_finite α] : fintype α := classical.choice ft.fin
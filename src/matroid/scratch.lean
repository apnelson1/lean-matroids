/-import prelim.collections prelim.size prelim.induction prelim.minmax
import .rankfun
import tactic 
-/
import tactic data.setoid.partition 


example {α : Type} {r : setoid α} (a : α): ∃! (b : set α), b ∈ r.classes ∧ a ∈ b := 
begin
  have := @setoid.classes_eqv_classes _ r a, 
  --rw exists_unique_iff_exists at this, 
  rcases this with ⟨b, ⟨h, hb, -⟩, hu⟩, 
  refine ⟨b, ⟨h,hb⟩, _⟩, 
  convert hu, simp only [exists_prop, exists_unique_iff_exists], 
  --  this: ∃! (b : set α) (H : b ∈ r.classes), a ∈ b
  --convert this, simp only [eq_self_iff_true],
  
end



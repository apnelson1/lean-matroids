import order.minimal 

variables {α : Type*} {r : α → α → Prop} {s : set α} {x : α} {P : α → Prop}

lemma mem_maximals_iff' [is_antisymm α r] :
  x ∈ maximals r s ↔ x ∈ s ∧ ∀ ⦃y⦄, y ∈ s → r x y → x = y :=
begin
  simp only [maximals, set.mem_sep_iff, and.congr_right_iff],  
  refine λ hx, ⟨λ h y hys hxy, antisymm hxy (h hys hxy), λ h y hys hxy, _⟩, 
  convert hxy; rw h hys hxy, 
end 

lemma mem_minimals_iff' [is_antisymm α r] :
  x ∈ minimals r s ↔ x ∈ s ∧ ∀ ⦃y⦄, y ∈ s → r y x → x = y :=
by { convert mem_maximals_iff', apply is_antisymm.swap }

lemma mem_maximals_prop_iff [is_antisymm α r] : 
  x ∈ maximals r P ↔ P x ∧ ∀ ⦃y⦄, P y → r x y → x = y :=
mem_maximals_iff'

lemma mem_maximals_set_of_iff [is_antisymm α r] : 
  x ∈ maximals r (set_of P) ↔ P x ∧ ∀ ⦃y⦄, P y → r x y → x = y :=
mem_maximals_iff'

lemma mem_minimals_prop_iff [is_antisymm α r] : 
  x ∈ minimals r P ↔ P x ∧ ∀ ⦃y⦄, P y → r y x → x = y :=
mem_minimals_iff'

lemma mem_minimals_set_of_iff [is_antisymm α r] : 
  x ∈ minimals r (set_of P) ↔ P x ∧ ∀ ⦃y⦄, P y → r y x → x = y :=
mem_minimals_iff'
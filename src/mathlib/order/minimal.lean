import order.minimal 

variables {α : Type*} {r : α → α → Prop} {s : set α} {x y : α} {P : α → Prop}

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

lemma mem_minimals_set_of_iff' {P : set α → Prop} {x : set α} : 
  x ∈ minimals (⊆) (set_of P) ↔ P x ∧ ∀ ⦃y⦄, y ⊂ x → ¬ P y := 
by simp [mem_minimals_set_of_iff, and.congr_right_iff, 
    ssubset_iff_subset_ne, and_imp, ne.def, not_imp_not, imp.swap, eq_comm]

lemma mem_maximals_set_of_iff' {P : set α → Prop} {x : set α} : 
  x ∈ maximals (⊆) (set_of P) ↔ P x ∧ ∀ ⦃y⦄, x ⊂ y → ¬ P y := 
by simp [mem_maximals_set_of_iff, and.congr_right_iff, ssubset_iff_subset_ne, and_imp, 
  not_imp_not, imp.swap]

def maximal {α : Type*} (r : α → α → Prop) (P : α → Prop) (x : α) := 
  x ∈ maximals r (set_of P)

def minimal {α : Type*} (r : α → α → Prop) (P : α → Prop) (x : α) := 
  x ∈ minimals r (set_of P)

lemma maximal.eq_of_le [is_antisymm α r] (h : maximal r P x) (hr : r x y) (hy : P y) :
  x = y := antisymm hr (h.2 hy hr)

lemma minimal.eq_of_le [is_antisymm α r] (h : minimal r P x) (hr : r y x) (hy : P y) :
  x = y := antisymm (h.2 hy hr) hr

-- lemma maximal.not_prop_of_lt [is_partial_order α r] (h : maximal r P x) (h : x < y) : ¬ P y := 

 

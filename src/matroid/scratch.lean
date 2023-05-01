import tactic 

variables {α β : Type} {X Y Z : set α} (x y z a b : α)

open set 

lemma mem_of_mem_of_subset' (h : a ∈ X) (h' : X ⊆ Y) : a ∈ Y := h' h 

example (h : a ∈ X ∪ Y) (h' : ∀ a ∈ X, (1 < 2) → a ∈ Z) (hY : Y ⊆ Z) : a ∈ Z :=
begin
  refine or.elim h (λ h'', h' _ h'' _) (λ h'', hY h''), norm_num, 
  -- obtain (hx | hy) := h,  
  --  obtain ⟨hx, hy⟩ := h, 
  --  refine h' ((inter_subset_right _ _) h), 
  --  change ∀ {x}, x ∈ Y → x ∈ Z at h',     
  -- refine mem_of_mem_of_subset (mem_of_mem_of_subset h (inter_subset_right _ _)) h', 

end  

example (h : a ∈ insert b X) (hb : b ∈ Y) (hXY : X ⊆ Y) : a ∈ Y :=
begin
  --rw mem_insert_iff at h, 
  obtain (rfl | haX) := h, exact hb, exact hXY haX, 

  -- obtain (rfl | rfl) := subset_singleton_iff_eq.mp h, 
  -- rw subset_singleton_iff_eq at h,
  -- cases h with h_empty h_nonempty, 

end 

example (P : set α → Prop) (h : X ⊆ {a}) : P X :=
begin
  obtain (rfl | rfl) := subset_singleton_iff_eq.mp h, 
end 

example (f : α → β) (P : β → Prop) (X : set α) (b : β) (h : b ∈ f '' X) : P b :=
begin
  -- rw mem_image at h, 
  obtain ⟨a, haX, rfl⟩ := h,   
end 

lemma inter_subset_left' (X Y : set α) : X ∩ Y ⊆ X := λ a, and.left 
import data.set.function 

namespace set 

variables {α β : Type*} {s s₁ s₂  : set α} {t t₁ : set β} {f : α → β}

lemma surj_on.image_preimage_inter (h : surj_on f s t) (ht₁ : t₁ ⊆ t) : f '' (f ⁻¹' t₁ ∩ s) = t₁ :=
begin
  refine subset_antisymm (λ b hb, _) (λ b hb, _), 
  { obtain ⟨a, ⟨ha, has⟩, rfl⟩ := hb, exact ha },
  obtain ⟨a, ha, rfl⟩ := h (ht₁ hb),
  exact ⟨a, ⟨hb, ha⟩, rfl⟩, 
end 

lemma inj_on.image_subset_image_iff (h : inj_on f s) (hs₁ : s₁ ⊆ s) (hs₂ : s₂ ⊆ s) :
  f '' s₁ ⊆ f '' s₂ ↔ s₁ ⊆ s₂ :=
begin
  refine ⟨λ h' x hx, _, image_subset _⟩,
  obtain ⟨y, hy, hxy⟩ := h' (mem_image_of_mem f hx),  
  rwa ← h (hs₂ hy) (hs₁ hx) hxy, 
end

lemma inj_on.image_eq_image_iff (h : inj_on f s) (hs₁ : s₁ ⊆ s) (hs₂ : s₂ ⊆ s) :
  f '' s₁ = f '' s₂ ↔ s₁ = s₂ :=
by rw [subset_antisymm_iff, h.image_subset_image_iff hs₁ hs₂, h.image_subset_image_iff hs₂ hs₁,  
    subset_antisymm_iff]
  

end set 
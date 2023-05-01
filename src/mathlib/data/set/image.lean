import data.set.image

open set

variables {α β : Type*} {f : α → β}


lemma function.injective.image_compl_eq (hf : f.injective) {A : set α} : 
  f '' Aᶜ  = (range f) \ f '' A := 
by rw [←image_univ, ←image_diff hf, compl_eq_univ_diff]

lemma function.injective.preimage_subset_of_subset_image (hf : f.injective) {A : set α} {B : set β} 
(h : B ⊆ f '' A) : 
  f ⁻¹' B ⊆ A := 
by { convert preimage_mono h, rw preimage_image_eq _ hf }

lemma function.injective.image_eq_singleton_iff (hf : f.injective) {A : set α} {b : β} : 
  f '' A = {b} ↔ ∃ a, f a = b ∧ A = {a} :=
begin
  refine ⟨λ h, _,_⟩, 
  { obtain (rfl | ⟨a, rfl⟩) :=  (subsingleton_of_image hf A 
      (by { rw h, exact subsingleton_singleton })).eq_empty_or_singleton,
    { rw [image_empty] at h, exact (singleton_ne_empty _ h.symm).elim },
    exact ⟨_, by simpa using h, rfl⟩ },
  rintro ⟨a, rfl, rfl⟩, 
  rw image_singleton,  
end  

@[simp] lemma subtype.preimage_image_coe (s : set α) (t : set s) : 
  (coe ⁻¹' (coe '' t : set α) : set s) = t := preimage_image_eq t subtype.coe_injective
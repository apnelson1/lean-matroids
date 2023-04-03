import data.set.image

open set

variables {α β : Type*} {f : α → β}

lemma function.injective.compl_image (hf : f.injective) (s : set α) :
  (f '' s)ᶜ = f '' sᶜ ∪ (range f)ᶜ :=
begin
  apply compl_injective,
  simp_rw [compl_union, compl_compl],
  refine (subset_inter _ (image_subset_range _ _)).antisymm _,
  { rintro x ⟨y, hy, rfl⟩ ⟨z,hz, hzy⟩,
    rw [hf hzy] at hz,
    exact hz hy},
  { rintro x ⟨hx, ⟨y, rfl⟩⟩,
    exact ⟨y, by_contra (λ hy, hx $ mem_image_of_mem _ hy), rfl⟩ }
end
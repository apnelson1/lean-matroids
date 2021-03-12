
import data.set.finite
import algebra.big_operators
import data.support
import data.finsupp

variables {α : Type*}

open set 

lemma set.insert_inter_of_mem {α : Type} {s₁ s₂ : set α} {a : α} (h : a ∈ s₂) :
  insert a s₁ ∩ s₂ = insert a (s₁ ∩ s₂) :=
by simp [set.insert_inter, h]

lemma set.insert_inter_of_not_mem {s₁ s₂ : set α} {a : α} (h : a ∉ s₂) :
  insert a s₁ ∩ s₂ = s₁ ∩ s₂ :=
begin
  ext x,
  simp only [mem_inter_iff, mem_insert_iff, mem_inter_eq, and.congr_left_iff, or_iff_right_iff_imp],
  cc,
end

lemma set.image_inter_support_eq {α β M : Type*} {f : α → M} [has_zero M] {s : set β} {g : β → α} :
  (g '' s ∩ function.support f) = g '' (s ∩ function.support (f ∘ g)) :=
begin
  ext y, split; intro hy,
    { rcases hy with ⟨⟨x, hx₀, rfl⟩, hy⟩,
      exact ⟨x, ⟨hx₀, hy⟩, rfl⟩ },
    { rcases hy with ⟨y, ⟨hys, hyfg⟩, rfl⟩, exact ⟨⟨y, hys, rfl⟩, hyfg⟩ }
end

lemma set.image_inter_support_finite_iff {α β M : Type*} {f : α → M} [has_zero M]
  {s : set β} {g : β → α} (hg : set.inj_on g s) :
  (g '' s ∩ function.support f).finite ↔ (s ∩ function.support (f ∘ g)).finite :=
begin
  rw [set.image_inter_support_eq, set.finite_image_iff],
  exact set.inj_on.mono (set.inter_subset_left s _) hg
end
import data.set.basic

namespace cleanup 
lemma set_union_sup (T : Type) (A B : set T) : (A ∪ B) = (A ⊔ B) := by refl
lemma set_inter_inf (T : Type) (A B : set T) : (A ∩ B) = (A ⊓ B) := by refl
lemma set_subset_le (T : Type) (A B : set T) : (A ⊆ B) = (A ≤ B) := by refl

meta def set_cleanup : tactic unit :=
  `[simp only [cleanup.set_union_sup, cleanup.set_inter_inf, cleanup.set_subset_le] at *]
end cleanup
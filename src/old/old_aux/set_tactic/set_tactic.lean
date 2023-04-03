import data.set.basic
import .extensionality

universe u

namespace extensionality
instance set_ext_lemmas (T : Type*) :
  (boolalg_ext_lemmas (set T) T) :=
{
  simpl_eq := by tidy,
  simpl_lt := by tidy,
  ext_bot := by tidy,
  ext_sdiff := by tidy,
  ext_le := by tidy,
  ext_meet := by tidy,
  ext_join := by tidy,
}

instance set_ext_lemmas_compl (T : Type*) :
  (boolalg_ext_lemmas_compl (set T) T) :=
{
  ext_compl := by tidy,
}

instance set_ext_lemmas_top (T : Type*) :
  (boolalg_ext_lemmas_top (set T) T) :=
{
  ext_top := by tidy,
}
end extensionality

namespace cleanup
lemma set_union_sup (T : Type*) (A B : set T) : (A ∪ B) = (A ⊔ B) := by refl
lemma set_inter_inf (T : Type*) (A B : set T) : (A ∩ B) = (A ⊓ B) := by refl
lemma set_subset_le (T : Type*) (A B : set T) : (A ⊆ B) = (A ≤ B) := by refl
lemma set_subset_lt (T : Type*) (A B : set T) : (A ⊂ B) = (A < B) := by refl
lemma set_univ_top (T : Type*) : (set.univ : set T) = ⊤ := by refl
lemma set_empt_bot (T : Type*) : (∅ : set T) = ⊥ := by refl

meta def set_cleanup : tactic unit :=
  `[simp only [cleanup.set_union_sup, cleanup.set_inter_inf, cleanup.set_subset_le,
      cleanup.set_subset_lt, cleanup.set_univ_top, cleanup.set_empt_bot] at *]
end cleanup
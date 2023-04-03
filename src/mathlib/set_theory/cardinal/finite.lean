import set_theory.cardinal.finite

variables {α : Type*} [fintype α]

namespace nat

lemma card_eq_to_finset_card (s : set α) [decidable_pred (∈ s)] : nat.card s = s.to_finset.card :=
by simp [card_eq_fintype_card]

end nat
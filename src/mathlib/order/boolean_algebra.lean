import order.boolean_algebra

variables {α : Type*} [boolean_algebra α]

@[simp] lemma sdiff_sdiff_cancel_right (a b : α) : a \ (b \ a) = a :=
disjoint_sdiff_self_right.sdiff_eq_left
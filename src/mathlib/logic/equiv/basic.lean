import tactic

universe u

-- Is there a reason this obvious @[simp] lemma wasn't in mathlib ?
@[simp] lemma equiv.sum_equiv_sigma_bool_apply (α β : Type u) (x : α ⊕ β) : 
  equiv.sum_equiv_sigma_bool α β x = sum.elim (sigma.mk tt) (sigma.mk ff) x := rfl 

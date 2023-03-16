-- import tactic 

-- variables {E : Type*} {P Q : Prop} {e : E}

-- example {hP : P ∨ Q} {hQ : ¬P} : Q := by {library_search, }

import data.finite.card

variables {α : Type*} {s t : set α}

open set

/-- A tactic that finds a `t.finite` term for a set `t` in a `finite` type. -/
meta def to_finite_tac : tactic unit := `[apply set.to_finite]

/-- Cardinality -/
noncomputable def set.ncard (s : set α) := nat.card s


@[simp] lemma ncard_eq_zero (hs : s.finite . to_finite_tac) :
  s.ncard = 0 ↔ s = ∅ :=
sorry

example (ht : t.finite) (hst : s ⊆ t) (hs : s.ncard = 0) : s = ∅  :=
begin
  have := λ h, ncard_eq_zero h,
end
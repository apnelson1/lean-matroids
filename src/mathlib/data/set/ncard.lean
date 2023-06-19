import data.set.ncard

open set 

/-- A fixed version that asserts in the conclusion that the set is finite. -/
theorem set.infinite.exists_supset_ncard_eq' {α : Type*} {s t : set α} 
 (ht : t.infinite) (hst : s ⊆ t) (hs : s.finite) {k : ℕ} (hsk : s.ncard ≤ k) :
∃ (s' : set α), s ⊆ s' ∧ s' ⊆ t ∧ s'.finite ∧ s'.ncard = k := 
begin
  obtain ((rfl : k = 0) | (hpos : 0 < k)) := eq_zero_or_pos, 
  { rw [le_zero_iff, ncard_eq_zero hs] at hsk,
    subst hsk, 
    exact ⟨∅, subset.rfl, empty_subset _, to_finite _, ncard_empty _⟩ },
  obtain ⟨s', hss', hs't, rfl⟩ := ht.exists_supset_ncard_eq hst hs hsk, 
  exact ⟨s', hss', hs't, finite_of_ncard_pos hpos, rfl⟩, 
end 

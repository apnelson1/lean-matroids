import order.minimal 

open set 

variables {α : Type*} {X Y E : set α} 

instance union_subset_ground [fact (X ⊆ E)] [fact (Y ⊆ E)] : fact (X ∪ Y ⊆ E) := 
by { rw fact_iff at *, exact union_subset ‹_› ‹_› }

instance inter_right_subset_ground [fact (X ⊆ E)] (Y : set α) : fact (X ∩ Y ⊆ E) := 
by { rw fact_iff at *, exact (inter_subset_left _ _).trans ‹_› }

instance inter_left_subset_ground [fact (X ⊆ E)] (Y : set α) : fact (Y ∩ X ⊆ E) := 
by { rw fact_iff at *, exact (inter_subset_right _ _).trans ‹_› }

instance diff_subset_ground (X : set α) : fact (E \ X ⊆ E) := ⟨diff_subset _ _⟩ 

instance empty_subset_ground : fact (∅ ⊆ E) := ⟨empty_subset _⟩

instance ground_subset_ground : fact (E ⊆ E) := ⟨subset.rfl⟩

@[simp] lemma set.subset_ground (X E : set α) [fact (X ⊆ E)] : X ⊆ E := fact.elim ‹_›

@[simp] lemma set.inter_ground (X E : set α) [fact (X ⊆ E)] : X ∩ E = X :=
inter_eq_self_of_subset_left (X.subset_ground E)

@[simp] lemma set.ground_inter (X E : set α) [fact (X ⊆ E)] : E ∩ X = X :=
inter_eq_self_of_subset_right (X.subset_ground E)

lemma rcompl_rcompl [fact (X ⊆ E)] : (E \ (E \ X)) = X := by simp 

lemma rcompl_subset_rcompl (E : set α) [fact (X ⊆ E)] [fact (Y ⊆ E)] : (E \ X) ⊆ (E \ Y) ↔ Y ⊆ X :=
begin
  rw [←compl_subset_compl, diff_eq, compl_inter, diff_eq, compl_inter, compl_compl, compl_compl, 
    union_subset_iff, and_iff_right (subset_union_left _ _)], 
  refine ⟨λ h, _, λ h, h.trans (subset_union_right _ _)⟩,
  rw [←Y.ground_inter E], 
  refine (inter_subset_inter_right _ h).trans _, 
  rw [inter_distrib_left, inter_compl_self, empty_union], 
  exact inter_subset_right _ _, 
end   

-- lemma foo {E X : set α} {P : set α → Prop} (hP : ∀ Y, P Y → Y ⊆ E) : 
--   X ∈ maximals (⊆) {Y | P Y} ↔ E \ X ∈ maximals (⊆) {Y | Y ⊆ E ∧ P (E \ Y)}  
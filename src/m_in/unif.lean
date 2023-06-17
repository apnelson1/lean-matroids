import .minor

variables {α : Type*} {M : matroid_in α} {k a b : ℕ} {I X C B E : set α}

open set 

namespace matroid_in 

/-- The truncation of a matroid to finite rank `k`. The independent sets of the truncation
  are the independent sets of the matroid of size at most `k`. -/
def truncate (M : matroid_in α) (k : ℕ) : matroid_in α := 
matroid_of_indep_of_bdd' M.E (λ I, M.indep I ∧ I.finite ∧ I.ncard ≤ k) 
(by simp)
(λ I J h hIJ, ⟨h.1.subset hIJ, h.2.1.subset hIJ, (ncard_le_of_subset hIJ h.2.1).trans h.2.2⟩ )
(begin
  rintro I J ⟨hI, hIfin, hIc⟩ ⟨hJ, hJfin, hJc⟩ hIJ, 
  obtain ⟨e, heJ, heI, hi⟩ := hI.augment_of_finite hJ hIfin hIJ, 
  refine ⟨e, heJ, heI, hi, hIfin.insert e, (ncard_insert_le _ _).trans _⟩, 
  rw [nat.add_one_le_iff], 
  exact hIJ.trans_le hJc, 
end) 
(⟨k, λ I, and.right⟩)
(λ I hI, hI.1.subset_ground)

@[simp] lemma truncate_indep_iff : (M.truncate k).indep I ↔ (M.indep I ∧ I.finite ∧ I.ncard ≤ k) := 
by simp [truncate]

@[simp] lemma truncate_ground_eq : (M.truncate k).E = M.E := rfl 

def set.unif_on (E : set α) (k : ℕ) := (free_on E).truncate k 

@[simp] lemma set.unif_on_indep_iff : (E.unif_on k).indep I ↔ I.finite ∧ I.ncard ≤ k ∧ I ⊆ E :=
by simp [set.unif_on, and_comm (I ⊆ E), and_assoc]

def unif_on (α : Type*) (k : ℕ) := (univ : set α).unif_on k 

@[simp] lemma unif_on_ground_eq : (unif_on α k).E = (univ : set α) := rfl 

@[simp] lemma unif_on_indep_iff [_root_.finite α] : (unif_on α k).indep I ↔ I.ncard ≤ k := 
by simp only [unif_on, set.unif_on_indep_iff, subset_univ, and_true, and_iff_right_iff_imp, 
    iff_true_intro (to_finite I), imp_true_iff]
  
/-- A canonical uniform matroid, with rank `a` and ground type `(fin b)`. -/
def unif (a b : ℕ) := unif_on (fin b) a 




end matroid_in 
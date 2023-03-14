import .rank

noncomputable theory
open_locale classical

variables {E : Type*} [finite E] {M M₁ M₂ : matroid E} 
  {C C' C₁ C₂ X : set E} {e : E}

open set 

namespace matroid 

/-- A circuit is a minimal dependent set -/
def circuit {E : Type*} (M : matroid E) (C : set E) := 
  ¬M.indep C ∧ ∀ I ⊂ C, M.indep I 

lemma circuit_def : 
  M.circuit C ↔ ¬M.indep C ∧ ∀ I ⊂ C, M.indep I :=
iff.rfl 

lemma circuit.dep (hC : M.circuit C) : 
  ¬M.indep C := 
hC.1 

lemma circuit.indep_of_ssubset (hC : M.circuit C) (hXC : X ⊂ C) :
  M.indep X := 
hC.2 _ hXC

lemma circuit.eq_of_dep_subset (hC : M.circuit C) (hX : ¬M.indep X) (hXC : X ⊆ C) :
  X = C :=
by_contra (λ h_eq, hX (hC.indep_of_ssubset (ssubset_of_ne_of_subset h_eq hXC)))

lemma circuit.nonempty (hC : M.circuit C) : 
  C.nonempty := 
by {rw set.nonempty_iff_ne_empty, rintro rfl, exact hC.1 M.empty_indep}

lemma circuit.card_eq (hC : M.circuit C) : 
  C.ncard = M.r C + 1 :=
begin
  obtain ⟨e,he⟩ := hC.nonempty, 
  have hss : C \ {e} ⊂ C, by {refine ssubset_of_ne_of_subset _ (diff_subset _ _), 
    simpa only [ne.def, sdiff_eq_left, disjoint_singleton_right, not_not_mem]},   
  have hlb := M.r_mono hss.subset, 
  have hub := r_lt_card_of_dep hC.dep, 
  rw [←nat.add_one_le_iff] at hub, 
  rw [(hC.indep_of_ssubset hss).r] at hlb, 
  have := ncard_diff_singleton_add_one he, 
  linarith, 
end 

lemma circuit.eq_of_dep_subset_self (hC : M.circuit C) (hX : ¬M.indep X) (hXC : X ⊆ C) : 
  C = X :=
by_contra (λ h, hX (hC.indep_of_ssubset (ssubset_of_subset_of_ne hXC (ne.symm h))))

lemma circuit.eq_of_subset_circuit (hC₁ : M.circuit C₁) (hC₂ : M.circuit C₂) (h : C₁ ⊆ C₂) : 
  C₁ = C₂ :=
(hC₂.eq_of_dep_subset_self hC₁.dep h).symm

lemma exists_circuit_subset_of_dep (hX : ¬M.indep X) : 
  ∃ C, M.circuit C ∧ C ⊆ X :=
begin
  obtain ⟨C,⟨hCX,hCdep⟩,hmin⟩:=  finite.exists_minimal (λ Y, Y ⊆ X ∧ ¬M.indep Y) ⟨_,rfl.subset,hX⟩,
  exact ⟨C, ⟨hCdep,λ I hIC, 
    by_contra (λ hI, hIC.ne ((hmin I ⟨hIC.subset.trans hCX,hI⟩ hIC.subset).symm))⟩, hCX⟩,  
end   
  
lemma dep_iff_contains_circuit :
  ¬ M.indep X ↔ ∃ C, M.circuit C ∧ C ⊆ X  :=
begin
  refine ⟨exists_circuit_subset_of_dep, _⟩, 
  rintros ⟨C, hC, hCX⟩, 
  exact λhX, hC.dep (hX.subset hCX),  
end 

lemma circuit_elim (hC₁ : M.circuit C₁) (hC₂ : M.circuit C₂) (h : C₁ ≠ C₂) (e : E) : 
  ∃ C, M.circuit C ∧ C ⊆ (C₁ ∪ C₂) \ {e} :=
begin
  by_cases he : e ∈ (C₁ ∪ C₂), swap, 
  { have h' := subset_union_left C₁ C₂, 
    exact ⟨C₁, hC₁, subset_diff_singleton h' (λ he', he (h' he'))⟩},

  simp_rw [←dep_iff_contains_circuit, ←r_lt_card_iff_dep, nat.lt_iff_add_one_le], 
   -- have hsm := M.r_inter_add_r_union_le_r_add_r C₁ C₂, 
  have hss : C₁ ∩ C₂ ⊂ C₁ := ssubset_of_ne_of_subset 
    (by {simp only [ne.def, inter_eq_left_iff_subset], 
      exact λ h', h (hC₁.eq_of_subset_circuit hC₂ h')}) (inter_subset_left _ _),  
  -- rw [(hC₁.indep_of_ssubset hss).r] at hsm, 
  have : M.r (C₁ ∪ C₂) + 2 ≤ (C₁ ∪ C₂).ncard, 
    linarith [hC₁.card_eq, hC₂.card_eq, ncard_inter_add_ncard_union C₁ C₂, 
      (hC₁.indep_of_ssubset hss).r, M.r_inter_add_r_union_le_r_add_r C₁ C₂], 

  have := M.r_add_card_le_r_add_card_of_subset (diff_subset (C₁ ∪ C₂) {e}), 
  -- have hsm := M.r_inter_add_r_union_le_r_add_r ((C₁ ∪ C₂) \ {e}) {e}, 
  -- rw [inter_singleton_eq_empty.mpr, r_empty, diff_union_self, union_singleton, insert_eq_self.mpr he] at hsm, 
  end 

  end matroid
  
  


import .flat

noncomputable theory

open_locale classical 

variables {E : Type*} [finite E] {M M₁ M₂ : matroid E} {B B₁ B₂ X Y Z : set E} {e f x y z : E}

open set
namespace matroid 

lemma basis.rev_exchange (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hx₁ : x ∈ B₁) (hx₂ : x ∉ B₂) : 
  ∃ y, y ∉ B₁ ∧ y ∈ B₂ ∧ M.base (insert y (B₁ \ {x})) :=
begin
  by_contra' h, 
  have hr : M.r B₂ ≤ M.r (B₁ \ {x}), 
  { refine (M.r_mono (subset_union_right (B₁ \ {x}) B₂)).trans_eq 
      (r_union_eq_of_r_all_insert_le (λ y hy₂, _)),
    have hyx : y ≠ x, { rintro rfl, exact hx₂ hy₂}, 
    obtain hy₁ | hy₁ := em (y ∈ B₁), 
    { rw [insert_eq_of_mem], rw mem_diff_singleton, exact ⟨hy₁, hyx⟩},
    have hB := h _ hy₁ hy₂, 
    rw [base_iff_indep_card_eq_r, ncard_exchange hy₁ hx₁, hB₁.card, eq_self_iff_true, and_true, 
      ←r_lt_card_iff_dep, nat.lt_iff_add_one_le] at hB,
    apply @nat.le_of_add_le_add_right 1, 
    convert hB, 
    rw [(hB₁.indep.subset (diff_subset _ _)).r, eq_comm], 
    refine ncard_insert_of_not_mem (by simpa)},
  rw [(hB₁.indep.subset (diff_subset _ _)).r, hB₂.indep.r, hB₂.card_eq_card_of_base hB₁] at hr, 
  exact (ncard_diff_singleton_lt_of_mem hx₁).not_le hr, 
end     

end matroid 
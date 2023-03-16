import .flat

noncomputable theory

open_locale classical 

variables {E : Type*} [finite E] {M M₁ M₂ : matroid E} {B B₁ B₂ X Y Z : set E} {e f x y z : E}

open set
namespace matroid 

lemma base.strong_exchange (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hx : x ∈ B₁ \ B₂) :
  ∃ y ∈ B₂ \ B₁, M.base (insert x (B₂ \ {y})) ∧ M.base (insert y (B₁ \ {x})):=
begin
  by_contra, 
  simp_rw [not_exists] at h, 
  obtain ⟨C, ⟨hCB₂,hC⟩, hCunique⟩ :=   
    hB₂.indep.unique_circuit_of_insert x (hB₂.insert_dep hx.2), 
  
  simp only [exists_unique_iff_exists, exists_prop, and_imp] at hCunique, 
  have hC_exchange : ∀ y ∈ C, y ≠ x →  M.base (insert x (B₂ \ {y})), 
  { intros y hyC hyx, 
    have hy₂ : y ∈ B₂, 
      from mem_of_mem_insert_of_ne (hCB₂ hyC) hyx, 
    rw [base_iff_indep_card, ncard_exchange hx.2 hy₂, hB₂.card, eq_self_iff_true, and_true],
    by_contra hdep, 
    rw [dep_iff_supset_circuit] at hdep, 
    obtain ⟨C', hC'ss, hC'⟩ := hdep, 
    have  hC'x : x ∈ C', 
    { by_contra hx', 
      exact hC'.dep (hB₂.indep.subset (((subset_insert_iff_of_not_mem hx').mp hC'ss).trans 
          (diff_subset _ _)))},
    have := hCunique C' (hC'ss.trans (insert_subset_insert (diff_subset _ _))) hC' hC'x,  
    subst this, 
    simpa using hC'ss hyC},
  
  -- have hr : B₂ ⊆   

  -- have hr : M.r B₂ ≤ M.r (B₁ \ {x}), 
  -- { refine (M.r_mono (subset_union_right (B₁ \ {x}) B₂)).trans_eq 
  --     (r_union_eq_of_r_all_insert_le (λ y hy₂, _)),
  --   have hyx : y ≠ x, { rintro rfl, exact hx.2 hy₂}, 
  --   obtain hy₁ | hy₁ := em (y ∈ B₁), 
  --   { rw [insert_eq_of_mem], rw mem_diff_singleton, exact ⟨hy₁, hyx⟩},
  --   have hB := h _ ⟨hy₂,hy₁⟩, 
  --   rw [base_iff_indep_card_eq_r, ncard_exchange hy₁ hx.1, hB₁.card, eq_self_iff_true, and_true, 
  --     ←r_lt_card_iff_dep, nat.lt_iff_add_one_le] at hB,
  --   apply @nat.le_of_add_le_add_right 1, 
  --   convert hB, 
  --   rw [(hB₁.indep.subset (diff_subset _ _)).r, eq_comm], 
  --   refine ncard_insert_of_not_mem (by simpa)},
  -- rw [(hB₁.indep.subset (diff_subset _ _)).r, hB₂.indep.r, hB₂.card_eq_card_of_base hB₁] at hr, 
  -- exact (ncard_diff_singleton_lt_of_mem hx.1).not_le hr, 
  -- The above is just a proof of the regular exchange axiom. Embarrassing! 
end     


-- def dual (M : matroid E) : matroid E := 
-- { base := λ B, M.base Bᶜ,
--   exists_base' := exists.elim M.exists_base (λ B hb, ⟨Bᶜ, by rwa compl_compl⟩),
--   base_exchange' := 
--   begin
--     rintro B₁ B₂ hB₁ hB₂ x ⟨hx₁,hx₂⟩, 
--     rw [←mem_compl_iff] at hx₂, 
--     rw [←not_mem_compl_iff] at hx₁, 
--     -- rw mem_compl
--     obtain ⟨y,hy,hB⟩ := hB₂.rev_exchange hB₁ ⟨hx₂, hx₁⟩, 
--     -- obtain ⟨y,⟨hy₁,hy₂⟩,hB⟩ := hB₁.rev_exchange hB₂ ⟨hx₂, hx₁⟩,
--     -- rw [mem_compl_iff] at hy₁ hy₂, 
--     rw [diff_eq_compl_inter, compl_compl] at hy,
--     refine ⟨y,hy, _⟩, 
--   end }

end matroid 
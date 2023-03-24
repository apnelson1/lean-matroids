import ..submatroids.pseudominor

/- Here we prove Edmonds' matroid intersection theorem: given two matroids M₁ and M₂ on α, the size 
of the largest set that is independent in both matroids is equal to the minimum of M₁.r X + M₂.r Xᶜ,
taken over all X ⊆ α. The proof is really by induction on the size of the ground set, but to make 
things easier we instead do induction on the number of nonloops, applying the induction hypothesis 
to loopifications and projections of M₁ and M₂.  -/


open_locale classical 

open matroid set 

variables {E : Type*} [finite E] {M₁ M₂ : matroid E} {I A : set E}

section intersection 

/-- The cardinality of a largest common independent set of matroids `M₁,M₂` -/
noncomputable def max_common_ind (M₁ M₂ : matroid E) :=
nat.find_greatest (λ n, ∃ I, M₁.indep I ∧ M₂.indep I ∧ I.ncard = n) (nat.card E)

lemma max_common_ind_eq_iff (M₁ M₂ : matroid E) {n : ℕ} :
  max_common_ind M₁ M₁ = n ↔ (∃ I, M₁.indep I ∧ M₂.indep I ∧ I.ncard = n :=

/-- the easy direction of matroid intersection, stated for a specific pair of sets. -/
theorem common_ind_le_r_add_r_compl (hI₁ : M₁.indep I) (hI₂ : M₂.indep I) (A : set E) : 
  I.ncard ≤ M₁.r A + M₂.r Aᶜ := 
begin
  rw [←ncard_inter_add_ncard_diff_eq_ncard I A, ←(hI₁.inter_right A).r, ←(hI₂.diff A).r, 
    diff_eq_compl_inter],
  exact add_le_add (M₁.r_mono (inter_subset_right I A)) (M₂.r_mono (inter_subset_left _ _)), 
end

lemma exists_common_ind (M₁ M₂ : matroid E) : 
  ∃ I, M₁.indep I ∧ M₂.indep I ∧ I.ncard = infi (λ X, M₁.r X + M₂.r Xᶜ) :=
begin
  sorry
end 

theorem matroid_intersection (M₁ M₂ : matroid E) : 
  max_common_ind M₁ M₂ = infi (λ X, M₁.r X + M₂.r Xᶜ) :=
begin
  rw [max_common_ind, nat.find_greatest_eq_iff],   
  
  simp only [ne.def, not_exists, not_and],
  split, 
  { refine (cinfi_le (order_bot.bdd_below _) ∅).trans _, 
    simp only [r_empty, compl_empty, zero_add],
    exact M₂.rk_le_card}, 
  refine ⟨λ h, _,_⟩,  
end 


end intersection

-- /-- the parameter ν is nonnegative -/
-- lemma ν_nonneg (M₁ M₂ : matroid α) : 
--   0 ≤ ν M₁ M₂ := 
-- by {apply lb_le_max, intro X, apply size_nonneg}

-- /-- function that provides an upper bound on ν M₁ M₂ -/
-- def matroid_inter_ub_fn (M₁ M₂ : matroid α) (X : set α): ℤ := 
--   M₁.r X + M₂.r Xᶜ



-- /-- the easy direction of matroid intersection, stated as an upper bound on ν -/
-- lemma ν_ub (M₁ M₂ : matroid α) : 
--   ν M₁ M₂ ≤ min_val (matroid_inter_ub_fn M₁ M₂)  := 
-- begin
--   rcases max_spec (λ (X : common_ind M₁ M₂), size X.val) with ⟨X, hX1, hX2⟩,
--   rcases min_spec (matroid_inter_ub_fn M₁ M₂) with ⟨A, hA1, hA2⟩, 
--   rw [ν, ←hX1, ←hA1], 
--   apply matroid_intersection_pair_le, 
-- end

-- /-- Edmonds' matroid intersection theorem: the size of a largest common independent set 
--     is equal to the minimum value of a natural upper bound on the size of any such set. 
--     Implies many other minmax theorems in combinatorics.                             -/
-- theorem matroid_intersection (M₁ M₂ : matroid α) : 
--   ν M₁ M₂ = min_val (λ X, M₁.r X + M₂.r Xᶜ) := 
-- begin
--   -- the hard direction suffices
--   refine le_antisymm (ν_ub M₁ M₂) _, 

--   --induction boilerplate 
--   convert  nonneg_int_strong_induction_param 
--     (λ p : matroid α × matroid α, min_val (matroid_inter_ub_fn p.1 p.2) ≤ ν p.1 p.2)
--     (λ p : matroid α × matroid α, size (nonloops p.1 ∩ nonloops p.2))
--     (λ p, size_nonneg _)
--     _ _ ⟨M₁,M₂⟩,

--   -- base case, when everything is a loop. Here the LHS is obviously 0.
--   rintros ⟨N₁,N₂⟩ hN, dsimp only at ⊢ hN, 

--   have h' : (matroid_inter_ub_fn N₁ N₂) (loops N₁) = 0 :=  by 
--   { rw [size_zero_iff_empty, N₂.nonloops_eq_compl_loops, ← subset_iff_disjoint_compl] at hN, 
--     rw [matroid_inter_ub_fn, rank_loops, ← nonloops_eq_compl_loops, zero_add, 
--       rank_zero_of_subset_rank_zero hN N₂.rank_loops]},

--   linarith [ν_nonneg N₁ N₂, min_is_lb (matroid_inter_ub_fn N₁ N₂) (loops N₁)],  
  
--   -- we now assume that the result holds for any strictly loopier pair of matroids, 
--   -- and that there is at least one common nonloop; call it e. 
  
--   rintros ⟨N₁,N₂⟩ hsize IH, dsimp only at hsize IH ⊢, 
--   set k := ν N₁ N₂ with hk, 
--   --rw ←hsize at hn, 
--   obtain ⟨e, he_mem⟩  := exists_mem_of_size_pos hsize, 
--   have  h_e_nl := he_mem, 
--   rw [mem_inter_iff, ← nonloop_iff_mem_nonloops] at h_e_nl, 
  
--   -- contract and delete (loopify/project) e from both elements of the pairs, to get 
--   -- strictly loopier pairs to which we'll apply the IH, along with the associated maximizers 
--   set N₁d := N₁ ⟍ {e} with hN₁d, 
--   set N₂d := N₂ ⟍ {e} with hN₂d,  
--   set N₁c := N₁ ⟋ {e} with hN₁c, 
--   set N₂c := N₂ ⟋ {e} with hN₂c, 

--   obtain ⟨⟨Id,hId_ind⟩, ⟨hId_eq_max, hId_ub⟩⟩ := max_spec (λ (X : common_ind N₁d N₂d), size X.val),
--   obtain ⟨⟨Ic,hIc_ind⟩, ⟨hIc_eq_max, hIc_ub⟩⟩ := max_spec (λ (X : common_ind N₁c N₂c), size X.val),

--   -- e doesn't belong to Ic, because Ic is independent in M/e 
--   have heIc : e ∉ Ic := λ heIc, by 
--   { have := projected_set_rank_zero N₁ {e}, 
--     rw [←hN₁c, mem_indep_r heIc hIc_ind.1] at this, 
--     exact one_ne_zero this},
  
--   -- ν does not get larger upon deletion 
--   have h_nu_d : ν N₁d N₂d ≤ k :=  by 
--   { rw [ν, ←hId_eq_max, hk, ν],
--     convert max_is_ub (λ (X : common_ind N₁ N₂), size X.val) ⟨Id, _⟩, 
--     from ⟨indep_of_loopify_indep hId_ind.1, indep_of_loopify_indep hId_ind.2⟩},
  
--   -- ν goes down upon contraction 
--   have h_nu_c : ν N₁c N₂c ≤ k-1 := by 
--   { rw [hk, ν, ν, ←hIc_eq_max], 
--     have := max_is_ub (λ (X : common_ind N₁ N₂), size X.val) ⟨Ic ∪ {e}, _⟩, 
--     dsimp only at this ⊢,
--     linarith only [size_union_nonmem_singleton heIc, this], 
--     split, all_goals {apply indep_union_project_set_of_project_indep}, 
--     exact hIc_ind.1, exact (nonloop_iff_indep.mp h_e_nl.1), 
--     exact hIc_ind.2, exact (nonloop_iff_indep.mp h_e_nl.2)},                             
  
--   -- `(N₁ ⟍ e, N₂ ⟍ e)` is loopier than `(N₁, N₂)`.
--   have h_fewer_nonloops_d : size (N₁d.nonloops ∩ N₂d.nonloops) < size (N₁.nonloops ∩ N₂.nonloops),
--   { rw [hN₁d, hN₂d, loopify_nonloops_eq, loopify_nonloops_eq, diff_inter_diff_right, 
--         size_remove_mem he_mem],
--     apply sub_one_lt, },

--   -- so is `(N₁ ⟋ e , N₂ ⟋ e)`.  
--   have h_fewer_nonloops_c : size (N₁c.nonloops ∩ N₂c.nonloops) < size (N₁.nonloops ∩ N₂.nonloops),
--   { rw [hN₁c, hN₂c, project_nonloops_eq, project_nonloops_eq],
--     refine size_strict_monotone ((ssubset_iff_of_subset _).mpr ⟨e, he_mem, _⟩), 
--     { intros x hx, simp_rw [mem_inter_iff, mem_diff_iff] at hx, exact ⟨hx.1.1, hx.2.1⟩}, 
--     refine nonmem_of_nonmem_supset (nonmem_diff_of_mem _ _) (inter_subset_left _ _), 
--     apply mem_cl_single},

--   -- apply IH to deletion and then contraction, getting minimizers Ac and Ad
--   have hd := IH ⟨N₁d, N₂d⟩ h_fewer_nonloops_d, 
--   obtain ⟨Ad, ⟨hAd_eq_min, hAd_lb⟩⟩ := min_spec (matroid_inter_ub_fn N₁d N₂d), 
--   rw [←hAd_eq_min] at hd, 

--   have hc := IH ⟨N₁c, N₂c⟩ h_fewer_nonloops_c, 
--   obtain ⟨Ac, ⟨hAc_eq_min, hAc_lb⟩⟩ := min_spec (matroid_inter_ub_fn N₁c N₂c), 
--   rw [←hAc_eq_min] at hc, 

--   -- this gives upper bounds on certain rank expressions
--   have hAd_ub : N₁.r (Ad \ {e}) + N₂.r (Adᶜ \ {e}) ≤ k := le_trans hd h_nu_d,

--   have hAc_ub : N₁.r (Ac ∪ {e}) + N₂.r (Acᶜ ∪ {e}) ≤ k+1 := by 
--   { suffices : (N₁.r (Ac ∪ {e}) - N₁.r {e}) + (N₂.r (Acᶜ ∪ {e}) - N₂.r {e}) ≤ k-1, 
--       by linarith [rank_nonloop h_e_nl.1, rank_nonloop h_e_nl.2],
--     from le_trans hc h_nu_c},

--   -- use contradiction, and replace the IH with a bound applying to all sets 
--   by_contra h_contr, push_neg at h_contr, 
--   replace h_contr : ∀ X, k + 1 ≤ matroid_inter_ub_fn N₁ N₂ X := 
--     λ X, by linarith [min_is_lb (matroid_inter_ub_fn N₁ N₂) X],

--   -- apply the bound to sets for which we know a bound in the other direction; 
--   have hi := h_contr (Ac ∩ Ad \ {e}), 
--   have hu := h_contr (Ac ∪ Ad ∪ {e}), 
--   unfold matroid_inter_ub_fn at hi hu, 
--   rw [compl_union, compl_union, ←diff_eq] at hu, 
--   rw [compl_diff, compl_inter] at hi, 
  
--   -- contradict submodularity. 
--   have sm1 := N₁.rank_submod (Ac ∪ {e}) (Ad \ {e}), 
--   have sm2 := N₂.rank_submod (Acᶜ ∪ {e}) (Adᶜ \ {e}),
--   rw [union_union_diff, union_inter_diff] at sm1 sm2, 
--   linarith only [sm1, sm2, hi, hu, hAd_ub, hAc_ub], 
-- end

-- /-- restatement of matroid intersection theorem as the existence of a matching maximizer/minimizer-/
-- theorem matroid_intersection_exists_pair_eq (M₁ M₂ : matroid α) : 
--   ∃ I A, is_common_ind M₁ M₂ I ∧ size I =  M₁.r A + M₂.r Aᶜ  := 
-- begin
--   rcases max_spec (λ (I : common_ind M₁ M₂), size I.val) with ⟨⟨I,h_ind⟩,h_eq_max, hI_ub⟩, 
--   rcases min_spec (λ X, M₁.r X + M₂.r Xᶜ) with ⟨A, hA_eq_min, hA_lb⟩, 
--   refine ⟨I, A, ⟨h_ind,_⟩⟩,  
--   dsimp only at *, 
--   rw [h_eq_max, hA_eq_min], 
--   apply matroid_intersection, 
-- end 

-- end intersection 




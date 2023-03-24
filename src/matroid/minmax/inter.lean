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

/-- The cardinality of a largest common independent set of matroids `M₁,M₂`. 
  Is `find_greatest` really the right way to do this?  -/
noncomputable def max_common_ind (M₁ M₂ : matroid E) :=
nat.find_greatest (λ n, ∃ I, M₁.indep I ∧ M₂.indep I ∧ I.ncard = n) ((univ : set E).ncard)

lemma max_common_ind_eq_iff (M₁ M₂ : matroid E) {n : ℕ} :
  max_common_ind M₁ M₂ = n ↔ (∃ I, M₁.indep I ∧ M₂.indep I ∧ n ≤ I.ncard) ∧
    (∀ I, M₁.indep I → M₂.indep I → I.ncard ≤ n)  :=
begin
  rw [max_common_ind, nat.find_greatest_eq_iff],  
  obtain (rfl | n) := n, 
  { simp only [nat.nat_zero_eq_zero, zero_le', ne.def, eq_self_iff_true, not_true, ncard_eq_zero, 
    exists_eq_right_right, is_empty.forall_iff, not_exists, not_and, true_and, le_zero_iff, 
    and_true], 
    split, 
    { 
      refine λ h, ⟨⟨_, M₁.empty_indep, M₂.empty_indep⟩, λ I hI₁ hI₂, _⟩,
      suffices hcI : ¬(0 < I.ncard), by rwa [not_lt, le_zero_iff, ncard_eq_zero] at hcI,   
      exact λ hcI, h hcI (ncard_mono (subset_univ _)) I hI₁ hI₂ rfl},
    refine λ h n hpos hn I hI₁ hI₂ hcard, _, 
    rw [←hcard, h.2 I hI₁ hI₂] at hpos, 
    simpa using hpos},

  simp only [ne.def, nat.succ_ne_zero, not_false_iff, forall_true_left, not_exists, not_and, 
    nat.succ_eq_add_one], 
  split, 
  { rintro ⟨hn, ⟨I, hI₁, hI₂, hIcard⟩, h'⟩, 
    refine ⟨⟨I, hI₁, hI₂, hIcard.symm.le⟩, λ J hJ₁ hJ₂, _⟩,
    by_contra' hJcard, 
    exact h' hJcard (ncard_mono (subset_univ _)) J hJ₁ hJ₂ rfl},
  simp only [and_imp, forall_exists_index], 
  refine λ I hI₁ hI₂ hIcard h, ⟨_,⟨I, hI₁,hI₂,_⟩ ,λ n' hn' hn'' J hJ₁ hJ₂ hJcard, _⟩,
  { rw ←(h I hI₁ hI₂).antisymm hIcard, exact ncard_mono (subset_univ _)},
  { rw ←(h I hI₁ hI₂).antisymm hIcard},
  subst hJcard, 
  exact (h J hJ₁ hJ₂).not_lt hn', 
end 

/-- the easy direction of matroid intersection, stated for a specific pair of sets. -/
theorem common_ind_le_r_add_r_compl (hI₁ : M₁.indep I) (hI₂ : M₂.indep I) (A : set E) : 
  I.ncard ≤ M₁.r A + M₂.r Aᶜ := 
begin
  rw [←ncard_inter_add_ncard_diff_eq_ncard I A, ←(hI₁.inter_right A).r, ←(hI₂.diff A).r, 
    diff_eq_compl_inter],
  exact add_le_add (M₁.r_mono (inter_subset_right I A)) (M₂.r_mono (inter_subset_left _ _)), 
end

/-- The hard direction of matroid intersection : existence -/
lemma exists_common_ind (M₁ M₂ : matroid E) : 
  ∃ I, M₁.indep I ∧ M₂.indep I ∧ (⨅ X, M₁.r X + M₂.r Xᶜ) ≤ I.ncard  :=
begin
  by_contra' hcon, 
  have hcon' : ∀ I X, M₁.indep I → M₂.indep I → I.ncard < M₁.r X + M₂.r Xᶜ, 
    from λ I X hI₁ hI₂, (hcon I hI₁ hI₂).trans_le (cinfi_le' (λ (X : set E), r M₁ X + r M₂ Xᶜ) X), 
    
  set matroid_pairs := (matroid E) × (matroid E), 
  set param : matroid_pairs → ℕ := λ p, (p.1.nonloops ∩ p.2.nonloops).ncard with hparam, 
  set counterex : set (matroid_pairs) := 
    { p | ∀ I X, p.1.indep I → p.2.indep I → I.ncard < p.1.r X + p.2.r Xᶜ } with hce,
  
  haveI : finite (matroid_pairs) := finite.prod.finite, 
  have hfin : counterex.finite := set.to_finite _, 
  have hcne : counterex.nonempty := ⟨⟨M₁,M₂⟩, hcon'⟩, 
  
  obtain ⟨p,hp,hpmin⟩ := finite.exists_minimal_wrt param counterex hfin hcne, 
  clear hcon hcon' M₁ M₂ hfin hcne, 
  obtain ⟨⟨M₁,M₂⟩,hcon⟩ := ⟨p,hp⟩,  
  simp only [hce, mem_set_of_eq] at hcon, 

  have hne : (M₁.nonloops ∩ M₂.nonloops).nonempty, 
  { by_contra' hcon',
    rw [not_nonempty_iff_eq_empty, ←disjoint_iff_inter_eq_empty, ←subset_compl_iff_disjoint_right, 
      nonloops, nonloops, compl_compl] at hcon', 
    specialize hcon ∅ (M₁.cl ∅) (M₁.empty_indep) (M₂.empty_indep),
    rw [ncard_empty, r_cl, r_empty, zero_add] at hcon,  
    have h' := hcon.trans_le (M₂.r_mono hcon'), 
    rw [r_cl, r_empty] at h', exact h'.ne rfl},

  obtain ⟨e, he₁,he₂⟩ := hne, 

  set M₁d := M₁ ⟍ {e} with hM₁d, 
  set M₂d := M₂ ⟍ {e} with hM₂d,  
  set M₁c := M₁ ⟋ {e} with hM₁c, 
  set M₂c := M₂ ⟋ {e} with hM₂c, 

  have h1dl : (M₁d).loop e := loop_of_loopify (mem_singleton _),   
  have h2dl : (M₂d).loop e := loop_of_loopify (mem_singleton _),   
  have h1cl : (M₁c).loop e := loop_of_project_mem (mem_singleton _),   
  have h2cl : (M₂c).loop e := loop_of_project_mem (mem_singleton _),   

  have h_smaller_d : (M₁d.nonloops ∩ M₂d.nonloops).ncard < (M₁.nonloops ∩ M₂.nonloops).ncard, 
  { apply ncard_lt_ncard, 
    refine ssubset_of_subset_not_subset 
    (inter_subset_inter (loopify_pminor _ _).nonloops_subset_nonloops 
      (loopify_pminor _ _).nonloops_subset_nonloops) (λ h, _ ), 
    specialize h ⟨he₁,he₂⟩, 
    simp_rw [nonloops, mem_inter_iff, mem_compl_iff, ←loop_iff_mem_cl_empty] at h, 
    exact h.1 h1dl}, 

  have h_smaller_c : (M₁c.nonloops ∩ M₂c.nonloops).ncard < (M₁.nonloops ∩ M₂.nonloops).ncard, 
  { apply ncard_lt_ncard, 
    refine ssubset_of_subset_not_subset 
    (inter_subset_inter (project_pminor _ _).nonloops_subset_nonloops 
      (project_pminor _ _).nonloops_subset_nonloops) (λ h, _ ), 
    specialize h ⟨he₁,he₂⟩, 
    simp_rw [nonloops, mem_inter_iff, mem_compl_iff, ←loop_iff_mem_cl_empty] at h, 
    exact h.1 h1cl}, 

  have hd : ∃ Id Xd, M₁d.indep Id ∧ M₂d.indep Id ∧ M₁d.r Xd + M₂d.r Xdᶜ ≤ Id.ncard,        
  { by_contra' h', 
    exact h_smaller_d.ne.symm (hpmin ⟨M₁d,M₂d⟩ h' h_smaller_d.le)},

  have hc : ∃ Ic Xc, M₁c.indep Ic ∧ M₂c.indep Ic ∧ M₁c.r Xc + M₂c.r Xcᶜ ≤ Ic.ncard,        
  { by_contra' h', 
    exact h_smaller_c.ne.symm (hpmin ⟨M₁c,M₂c⟩ h' h_smaller_c.le)},

  rw mem_nonloops_iff_not_loop at he₁ he₂, 

  obtain ⟨Id,Xd, hId₁, hId₂, hId⟩ := hd, 
  obtain ⟨Ic,Xc, hIc₁, hIc₂, hIc⟩ := hc,

  zify at hIc hId hcon, 

  have heIc : e ∉ Ic, 
  { rw [hM₁c, indep.project_indep_iff] at hIc₁, 
    { rw [←disjoint_singleton_right], exact hIc₁.1,},
    { rwa [loop_iff_dep, not_not] at he₁},
    exact indep_of_project_indep hIc₁},    

  

  have ineq1 := λ (X : set E), 
    (hId.trans_lt (hcon _ X (indep_of_loopify_indep hId₁) (indep_of_loopify_indep hId₂))), 

  have ineq2 := λ (X : set E), hcon (insert e Ic) X 
    (by rwa ← indep_project_singleton_iff he₁ (heIc)) 
    (by rwa ← indep_project_singleton_iff he₂ (heIc)),


  simp_rw [ncard_insert_of_not_mem heIc, int.lt_iff_add_one_le] at ineq2, 
  rw [hM₁c, hM₂c, coe_r_project_singleton he₁, coe_r_project_singleton he₂] at hIc, 
  

  
  -- have := λ X, hIc 
  -- have : M₁.r (Xd \ {e}) + M₂.r (Xdᶜ \ {e}) ≤ _,


    -- have := hpmin ⟨M₁d,M₂d⟩ h',  


  


  -- have : ∃ e, ¬ M₁.loop e ∧ ¬M₁.loop e, 
  -- { by_contra' hloopy, 
  --   have h_all : M₁.cl ∅ = univ,  
  --   { simp_rw [eq_univ_iff_forall, ←loop_iff_mem_cl_empty], exact hloopy, },
  --   have h' := hcon ∅ univ M₁.empty_indep M₂.empty_indep, 
  --   simp_rw [compl_univ, ←h_all, r_cl] at h',  
  --   simpa using h'},
  


  -- have := @finite.exists_minimal_wrt matroid_pairs ℕ _ param counterex _,  
  
end 

theorem matroid_intersection (M₁ M₂ : matroid E) : 
  max_common_ind M₁ M₂ = ⨅ X, M₁.r X + M₂.r Xᶜ :=
begin
  rw [max_common_ind_eq_iff], 
  obtain ⟨I, hI₁, hI₂, hle⟩ := exists_common_ind M₁ M₂, 
  refine ⟨exists_common_ind M₁ M₂, λ I hI₁ hI₂, _ ⟩, 
  exact (le_cinfi_iff (order_bot.bdd_below _)).mpr (common_ind_le_r_add_r_compl hI₁ hI₂),    
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




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
  ∃ I X, M₁.indep I ∧ M₂.indep I ∧ I.ncard = M₁.r X + M₂.r Xᶜ :=
begin
  -- Suppose not. Construct a minimal counterexample (wrt the number of nonloops of `M₁`)
  by_contra' hcon, 
  have hcon' : ∀ I X, M₁.indep I → M₂.indep I → I.ncard < M₁.r X + M₂.r Xᶜ, 
  { refine λ I X hI₁ hI₂, lt_of_le_of_ne _ (hcon I X hI₁ hI₂), 
    exact common_ind_le_r_add_r_compl hI₁ hI₂ X, },
  
  set matroid_pairs := (matroid E) × (matroid E), 
  set param : matroid_pairs → ℕ := λ p, p.1.nonloops.ncard with hparam,
  set counterex : set (matroid_pairs) := 
    { p | ∀ I X, p.1.indep I → p.2.indep I → I.ncard < p.1.r X + p.2.r Xᶜ } with hce,
  
  haveI : finite (matroid_pairs) := finite.prod.finite, 
  have hfin : counterex.finite := set.to_finite _, 
  have hcne : counterex.nonempty := ⟨⟨M₁,M₂⟩, hcon'⟩, 
  
  obtain ⟨p,hp,hpmin⟩ := finite.exists_minimal_wrt param counterex hfin hcne, 
  clear hcon hcon' M₁ M₂ hfin hcne, 
  obtain ⟨⟨M₁,M₂⟩,hcon⟩ := ⟨p,hp⟩,  
  simp only [mem_set_of_eq] at hcon, 

  -- There is a common nonloop of `M₁` and `M₂`, otherwise the result is easy
  have hne : ∃ e, ¬M₁.loop e ∧ ¬M₂.loop e, 
  { by_contra' he,
    simp_rw [loop_iff_mem_cl_empty, ←mem_compl_iff, ←subset_def] at he,  
    specialize hcon ∅ (M₁.cl ∅) M₁.empty_indep M₂.empty_indep, 
    rw [ncard_empty, r_cl, r_empty, zero_add] at hcon, 
    exact (hcon.trans_le (M₂.r_mono he)).ne (by rw [r_cl, r_empty])}, 

  obtain ⟨e, he₁,he₂⟩ := hne, 

  -- Projecting/loopifying `e` gives non-counterexamples (by minimality) ... 
  set M₁d := M₁ ⟍ {e} with hM₁d, 
  set M₂d := M₂ ⟍ {e} with hM₂d,  
  set M₁c := M₁ ⟋ {e} with hM₁c, 
  set M₂c := M₂ ⟋ {e} with hM₂c, 

  have d_lt : M₁d.nonloops.ncard < M₁.nonloops.ncard, from 
    ncard_lt_ncard (strict_pminor_of_loopify_nonloop he₁).nonloops_ssubset_nonloops,

  have c_lt : M₁c.nonloops.ncard < M₁.nonloops.ncard, from 
    ncard_lt_ncard (strict_pminor_of_project_nonloop he₁).nonloops_ssubset_nonloops,

  have hd : ∃ Id Xd, M₁d.indep Id ∧ M₂d.indep Id ∧ M₁d.r Xd + M₂d.r Xdᶜ ≤ Id.ncard,        
  { by_contra' h', exact d_lt.ne.symm (hpmin ⟨M₁d,M₂d⟩ h' d_lt.le)},

  have hc : ∃ Ic Xc, M₁c.indep Ic ∧ M₂c.indep Ic ∧ M₁c.r Xc + M₂c.r Xcᶜ ≤ Ic.ncard,        
  { by_contra' h', exact c_lt.ne.symm (hpmin ⟨M₁c,M₂c⟩ h' c_lt.le)},

-- So there are corresponding minimizers in these minors. 
  obtain ⟨Id,Xd, hId₁, hId₂, hId⟩ := hd, 
  obtain ⟨Ic,Xc, hIc₁, hIc₂, hIc⟩ := hc,

  zify at hIc hId hcon, 

  have heIc : e ∉ Ic, 
  { rw [hM₁c, indep.project_indep_iff] at hIc₁, 
    { rw [←disjoint_singleton_right], exact hIc₁.1,},
    { rwa [loop_iff_dep, not_not] at he₁},
    exact indep_of_project_indep hIc₁},    

  -- Use these minimizers to get rank lower bounds. 
  have ineq1 := λ X, 
    (hId.trans_lt (hcon _ X (indep_of_loopify_indep hId₁) (indep_of_loopify_indep hId₂))), 
  simp_rw [hM₁d, hM₂d, r_loopify] at ineq1, 

  have ineq2 := λ (X : set E), hcon (insert e Ic) X 
    (by rwa ← indep_project_singleton_iff he₁ (heIc)) 
    (by rwa ← indep_project_singleton_iff he₂ (heIc)),

  simp_rw [ncard_insert_of_not_mem heIc,nat.cast_add, nat.cast_one] at ineq2, 
  rw [hM₁c, hM₂c, coe_r_project_singleton he₁, coe_r_project_singleton he₂] at hIc, 
  
  have hi := ineq1 ((Xc ∩ Xd) \ {e}), 
  have hu := ineq2 (insert e (Xc ∪ Xd)), 

  -- And contradict them with submodularity bounds. 
  have sm1 := M₁.r_submod (insert e Xc) (Xd \ {e}), 
  have sm2 := M₂.r_submod (insert e Xcᶜ) (Xdᶜ \ {e}),
  have htemp : ∀  S, e ∉ S \ {e}, 
  { intro S, rw [mem_diff_singleton, not_and, not_ne_iff], exact λ _, rfl},
  rw [insert_union, insert_union_distrib, insert_diff_singleton, ←insert_union_distrib, 
    insert_inter_of_not_mem (htemp _), ←inter_diff_assoc] at sm1 sm2, 
  
  have huc : (insert e (Xc ∪ Xd))ᶜ = Xcᶜ ∩ Xdᶜ \ {e}, 
  { apply compl_injective, 
    simp_rw [diff_eq_compl_inter, compl_inter, compl_compl, singleton_union]},
  have hic : (Xc ∩ Xd \ {e})ᶜ = (insert e (Xcᶜ ∪ Xdᶜ)), 
  { apply compl_injective, 
    simp_rw [←union_singleton, compl_union, compl_compl, diff_eq_compl_inter, inter_comm {e}ᶜ]}, 

  rw hic at hi, 
  rw huc at hu, 
  linarith, 
end 

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

theorem matroid_intersection (M₁ M₂ : matroid E) : 
  max_common_ind M₁ M₂ = ⨅ X, M₁.r X + M₂.r Xᶜ :=
begin
  rw [max_common_ind_eq_iff], 
  obtain ⟨I, X, hI₁, hI₂, heq⟩ := exists_common_ind M₁ M₂, 
  refine ⟨⟨I, hI₁, hI₂, (cinfi_le' _ _).trans_eq heq.symm⟩, λ J hJ₁ hJ₂, _ ⟩,
  exact (le_cinfi_iff (order_bot.bdd_below _)).mpr (common_ind_le_r_add_r_compl hJ₁ hJ₂),    
end 


end intersection


import .constructions .projection 

namespace ftype 

variables {U : ftype}

def is_common_ind (M₁ M₂ : rankfun U)(X : U) := 
  is_indep M₁ X ∧ is_indep M₂ X 

lemma bot_is_common_ind (M₁ M₂ : rankfun U): 
  is_common_ind M₁ M₂ ⊥ := 
  ⟨I1 M₁, I1 M₂⟩ 

lemma exists_common_ind {M₁ M₂ : rankfun U}: 
  ∃ X, is_common_ind M₁ M₂ X := 
  ⟨⊥, bot_is_common_ind M₁ M₂⟩

-- size of largest common independent set 
def ν (M₁ M₂ : rankfun U) : ℤ := 
  max_val_over size (is_common_ind M₁ M₂) exists_common_ind

def largest_common_ind (M₁ M₂ : rankfun U) : U := 
  arg_max_over size (is_common_ind M₁ M₂) exists_common_ind

lemma size_largest_common_ind_eq_nu (M₁ M₂ : rankfun U) : 
  size (largest_common_ind M₁ M₂) = ν M₁ M₂ := 
  (arg_max_over_attains _ _ _).2 

lemma largest_common_ind_is_common_ind (M₁ M₂ : rankfun U) : 
  is_common_ind M₁ M₂ (largest_common_ind M₁ M₂) := 
  (arg_max_over_attains _ _ _).1 

lemma size_common_ind_le_nu {M₁ M₂ : rankfun U}{X : U} :
  is_common_ind M₁ M₂ X → size X ≤ ν M₁ M₂ := 
  λ h, (max_over_is_ub _ _ _ X h)

lemma nu_nonneg (M₁ M₂ : rankfun U) :
  0 ≤ ν M₁ M₂ := 
  by {rw ←(size_bot U), from size_common_ind_le_nu (bot_is_common_ind _ _)} 

def matroid_intersection_ub_fn (M₁ M₂ : rankfun U) : U → ℤ := 
  (λ X, M₁.r X + M₂.r Xᶜ)

theorem matroid_intersection_pair_le {M₁ M₂ : rankfun U}{I : U}(A : U) : 
  is_common_ind M₁ M₂ I → size I ≤ M₁.r A + M₂.r Aᶜ := 
begin
  rintros ⟨h₁,h₂⟩, 
  rw ←(compl_inter_size A I), 
  have h₁i := I2 (inter_subset_right A I) h₁, 
  have h₂i := I2 (inter_subset_right Aᶜ I) h₂, 
  rw [←indep_iff_r.mp h₁i, ←indep_iff_r.mp h₂i], 
  linarith [R2 M₁ (inter_subset_left A I), R2 M₂ (inter_subset_left Aᶜ I)], 
end

lemma matroid_intersection_ub (M₁ M₂ : rankfun U): 
  ν M₁ M₂ ≤ min_val (λ X, M₁.r X + M₂.r Xᶜ) := 
begin
  set ub_fn := λ X, M₁.r X + M₂.r Xᶜ with h_ub_fn, 
  set A := arg_min ub_fn with hA , 
  set I := largest_common_ind M₁ M₂ with hI, 
  rw [←size_largest_common_ind_eq_nu, ←arg_min_attains ub_fn, ←hA], 
  from matroid_intersection_pair_le A (largest_common_ind_is_common_ind M₁ M₂)
end

theorem matroid_intersection (M₁ M₂ : rankfun U): 
  ν M₁ M₂ = min_val (λ X, M₁.r X + M₂.r Xᶜ) := 
begin
  set ub_fn := λ (N₁ N₂ : rankfun U) X, N₁.r X + N₂.r Xᶜ with h_ub_fn, 
  --induction boilerplate (and ≥ suffices)
  set Q : ℤ → Prop := 
    λ s, ∀ (M₁ M₂ : rankfun U), size (loops M₁ ∪ loops M₂)ᶜ = s → 
      min_val (ub_fn M₁ M₂) ≤ ν M₁ M₂,
  suffices : ∀ n₀, 0 ≤ n₀ → Q n₀, 
    from antisymm (matroid_intersection_ub M₁ M₂) (this _ (size_nonneg _) M₁ M₂ rfl) , 
  refine nonneg_int_strong_induction _ (λ N₁ N₂ hloops, _) (λ n hn IH N₁ N₂ hsize, _), 

  -- base case 
  rw [size_zero_iff_bot, top_iff_compl_bot] at hloops,
  have h' : (ub_fn N₁ N₂) (loops N₁) = 0 :=  by 
  {
      simp_rw h_ub_fn,  
      linarith [R0 N₂ (loops N₁)ᶜ, rank_loops N₁, rank_loops N₂,  
                                R2 N₂ (cover_compl_subset hloops)], 
  },
  linarith [nu_nonneg N₁ N₂, min_is_lb (ub_fn N₁ N₂) (loops N₁)], 
  
  --inductive step 
  set k := ν N₁ N₂ with hk, 
  rw ←hsize at hn, 
  cases size_pos_has_mem hn with e he, 
  
  have h_e_nl : (is_nonloop N₁ e) ∧ (is_nonloop N₂ e) := by split; 
  {
    rw [nonloop_iff_not_elem_loops, ←mem_compl_iff], 
    refine subset.trans he _, 
    simp only [compl_union, inter_subset_left, inter_subset_right],
  }, 

  set N₁d := loopify N₁ e with hN₁d, 
  set N₂d := loopify N₂ e with hN₂d, 
  set N₁c := project N₁ e with hN₁c, 
  set N₂c := project N₂ e with hN₂c, 

  set Id := largest_common_ind N₁d N₂d with hId, 
  set Ic := largest_common_ind N₁c N₂c with hIc, 
  let hId' : is_common_ind N₁d N₂d Id := by apply largest_common_ind_is_common_ind, 
  let hIc' : is_common_ind N₁c N₂c Ic := by apply largest_common_ind_is_common_ind,

  have heIc : e ∉ Ic := λ heIc, by 
  {
    have := projected_set_rank_zero N₁ e, 
    rw [←hN₁c, elem_indep_r heIc hIc'.1] at this, 
    from one_ne_zero this, 
  },
  
  have h_nu_d : ν N₁d N₂d ≤ k := by 
  { 
    rw [←size_largest_common_ind_eq_nu, ←hId, hk], 
    from size_common_ind_le_nu 
          ⟨indep_of_loopify_indep hId'.1,
           indep_of_loopify_indep hId'.2⟩,
  },

  have h_nu_c : ν N₁c N₂c ≤ k-1 := by 
  {
    rw [←size_largest_common_ind_eq_nu, ←hIc, hk], 
    linarith 
    [
      size_insert_nonmem heIc,
      size_common_ind_le_nu 
      ⟨
        indep_of_project_indep hIc'.1 (nonloop_iff_indep.mp h_e_nl.1), 
        indep_of_project_indep hIc'.2 (nonloop_iff_indep.mp h_e_nl.2)
      ⟩
    ],                                                          
  },                             

  -- these next two claims let us apply IH to deletion/contraction 
  have h_more_loops_d : size (loops N₁d ∪ loops N₂d)ᶜ < n := by 
  {
    have h_add_e := union_subset_union 
      (loopify_makes_loops N₁ e) 
      (loopify_makes_loops N₂ e), 
    rw ←union_distrib_union_left at h_add_e, 
    have := size_monotone h_add_e, 
    rw [size_insert_mem_compl he, ←hN₁d, ←hN₂d] at this, 
    rw [compl_size] at ⊢ hsize, linarith,  
  },

  have h_more_loops_c : size (loops N₁c ∪ loops N₂c)ᶜ < n := by 
  {
    have h_add_e := union_subset_union 
      (project_makes_loops N₁ e) 
      (project_makes_loops N₂ e), 
    rw ←union_distrib_union_left at h_add_e, 
    have := size_monotone h_add_e, 
    rw [size_insert_mem_compl he, ←hN₁c, ←hN₂c] at this, 
    rw [compl_size] at ⊢ hsize, linarith,  
  },  
  
  -- apply IH to deletion, get minimizer Ad
  rcases IH _ h_more_loops_d N₁d N₂d rfl with hd, 
  set Ad := arg_min (ub_fn N₁d N₂d) with hAd,
  rw [←arg_min_attains (ub_fn N₁d N₂d), ←hAd] at hd, 
  have hAd_ub : N₁.r (Ad \ {e}) + N₂.r (Adᶜ \ {e}) ≤ k := le_trans hd h_nu_d,


  --apply IH to contraction, get minimizer Ac 
  rcases IH _ h_more_loops_c N₁c N₂c rfl with hc,
  set Ac := arg_min (ub_fn N₁c N₂c) with hAc,
  rw [←arg_min_attains (ub_fn N₁c N₂c), ←hAc] at hc, 
  have hAc_ub : N₁.r (Ac ∪ {e}) + N₂.r (Acᶜ ∪ {e}) ≤ k+1 := by 
  {
    suffices : (N₁.r (Ac ∪ {e}) - N₁.r e) + (N₂.r (Acᶜ ∪ {e}) - N₂.r e) ≤ k-1, 
      by linarith [rank_nonloop h_e_nl.1, rank_nonloop h_e_nl.2],
    from le_trans hc h_nu_c, 
  },

  by_contra h_contr, push_neg at h_contr, 
  replace h_contr : ∀ X, k + 1 ≤ ub_fn N₁ N₂ X := 
    λ X, by linarith [min_is_lb (ub_fn N₁ N₂) X],

  have hi := h_contr (Ac ∩ Ad \ {e}), 
  have hu := h_contr (Ac ∪ Ad ∪ {e}), 
  simp_rw h_ub_fn at hi hu, 
  rw [compl_union, compl_union, ←diff_eq] at hu, 
  rw [compl_diff, compl_inter] at hi, 
  have sm1 := R3 N₁ (Ac ∪ {e}) (Ad \ {e}), 
  have sm2 := R3 N₂ (Acᶜ ∪ {e}) (Adᶜ \ {e}),
  rw [union_union_diff, union_inter_diff] at sm1 sm2, 
  linarith only [sm1, sm2, hi, hu, hAd_ub, hAc_ub], 
end

theorem matroid_intersection_exists_pair_eq (M₁ M₂ : rankfun U): 
  ∃ I A, is_common_ind M₁ M₂ I ∧ size I =  M₁.r A + M₂.r Aᶜ  := 
begin
  set I := largest_common_ind M₁ M₂ with hI, 
  let h_ind := largest_common_ind_is_common_ind M₁ M₂, 
  rw ←hI at h_ind, 
  set A := arg_min (λ X, M₁.r X + M₂.r Xᶜ) with hX, 
  refine ⟨I, ⟨A, ⟨h_ind,_⟩⟩⟩,  
  rw [hI, size_largest_common_ind_eq_nu, matroid_intersection M₁ M₂], 
  from (arg_min_attains _).symm, 
end 

end ftype 
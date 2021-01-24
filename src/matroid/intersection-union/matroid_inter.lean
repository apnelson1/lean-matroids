
import matroid.constructions matroid.projection ftype.minmax

open_locale classical 
noncomputable theory 
open ftype 
open matroid  

variables {U : ftype}

-- setting up the various types we are minimizing/maximizing over 
section prelim 

--instance set_fintype : fintype (set U) := set_fintype_of U
def is_indep_pair (M₁ M₂ : matroid U) := λ (p : set U × set U), M₁.is_indep p.1 ∧ M₂.is_indep p.2

def is_basis_pair (M₁ M₂ : matroid U) := λ (p : set U × set U), M₁.is_basis p.1 ∧ M₂.is_basis p.2

def is_disjoint (pair : (set U × set U)) := pair.1 ∩ pair.2 = ∅  

def indep_pair (M₁ M₂ : matroid U) := {p : set U × set U // is_indep_pair M₁ M₂ p }

def basis_pair (M₁ M₂ : matroid U) := {p : set U × set U // is_basis_pair M₁ M₂ p }

def indep_pair_of_subset (M₁ M₂ : matroid U)(X : set U) := {p : set U × set U // is_indep_pair M₁ M₂ p ∧ (p.1 ⊆ X ∧ p.2 ⊆ X) }

def inter_size (pair : (set U × set U)) : ℤ := size (pair.1 ∩ pair.2)

def union_size (pair : (set U × set U)) : ℤ := size (pair.1 ∪ pair.2) 

def disjoint_indep_pair (M₁ M₂ : matroid U) := {pair : indep_pair M₁ M₂ // is_disjoint pair.1}

def disjoint_basis_pair (M₁ M₂ : matroid U) := {pair : basis_pair M₁ M₂ // is_disjoint pair.1}

instance indep_pair_fintype {M₁ M₂ : matroid U} : fintype (indep_pair M₁ M₂) := 
  by {unfold indep_pair, apply_instance }

instance basis_pair_fintype {M₁ M₂ : matroid U} : fintype (basis_pair M₁ M₂) := 
  by {unfold basis_pair, apply_instance }

instance indep_pair_nonempty {M₁ M₂ : matroid U} : nonempty (indep_pair M₁ M₂) := 
begin
  simp only [indep_pair, nonempty_subtype, prod.exists], 
  from ⟨∅, ∅, ⟨M₁.I1, M₂.I1⟩ ⟩ , 
end 

instance indep_pair_of_subset_nonempty {M₁ M₂ : matroid U}{X : set U} : nonempty (indep_pair_of_subset M₁ M₂ X) := 
begin
  simp only [indep_pair_of_subset, nonempty_subtype, prod.exists], 
  from ⟨∅, ∅, ⟨M₁.I1, M₂.I1⟩, ⟨empty_subset _, empty_subset _⟩ ⟩ , 
end 

instance indep_pair_of_subset_fintype {M₁ M₂ : matroid U}{X : set U} : fintype (indep_pair_of_subset M₁ M₂ X) := 
begin
  unfold indep_pair_of_subset, apply_instance, 
end 

instance basis_pair_nonempty {M₁ M₂ : matroid U} : nonempty (basis_pair M₁ M₂) := 
begin
  simp only [basis_pair, exists_and_distrib_right, nonempty_subtype, exists_and_distrib_left, prod.exists], 
  cases exists_basis M₁ with B₁ hB₁,
  cases exists_basis M₂ with B₂ hB₂, 
  from ⟨B₁, B₂, hB₁, hB₂⟩,  
end 

instance disjoint_indep_pair_nonempty (M₁ M₂ : matroid U) : 
  nonempty (disjoint_indep_pair M₁ M₂) :=
by {unfold disjoint_indep_pair, refine nonempty_subtype.mpr _, use ⟨⟨∅,∅⟩, ⟨I1 M₁, I1 M₂⟩⟩, tidy,  } 

/--independence in both M₁ and M₂ -/
def is_common_ind (M₁ M₂ : matroid U) := 
  λ X, is_indep M₁ X ∧ is_indep M₂ X 

/-- subtype of common independent sets -/ 
def common_ind (M₁ M₂ : matroid U) := {X : set U // is_common_ind M₁ M₂ X}

instance nonempty_common_ind (M₁ M₂ : matroid U) : nonempty (common_ind M₁ M₂) := 
by {apply nonempty_subtype.mpr, from ⟨∅, ⟨I1 M₁, I1 M₂⟩⟩}

instance fintype_common_ind (M₁ M₂ : matroid U ): fintype (common_ind M₁ M₂) := 
  by {unfold common_ind, apply_instance}

instance coe_common_ind (M₁ M₂ : matroid U) : has_coe (common_ind M₁ M₂) (set U) :=
  ⟨λ X, X.val⟩

/-- has partition into an independent set of M₁ and an independent set of M₂-/
def is_two_partitionable (M₁ M₂ : matroid U) : set U → Prop := 
  λ X, ∃ I₁ I₂, is_indep M₁ I₁ ∧ is_indep M₂ I₂ ∧ X = I₁ ∪ I₂ ∧ I₁ ∩ I₂ = ∅

/-- has partition into a basis of M₁ and a basis set of M₂-/
def is_two_basis_partitionable (M₁ M₂ : matroid U) : set U → Prop := 
  λ X, ∃ B₁ B₂ , is_basis M₁ B₁ ∧ is_basis M₂ B₂ ∧ B₁ ∪ B₂ = X ∧ B₁ ∩ B₂ = ∅

/-- is the union of a basis of M₁ and a basis of M₂ -/
def is_union_two_bases (M₁ M₂ : matroid U) : set U → Prop := 
  λ X, ∃ B₁ B₂, is_basis M₁ B₁ ∧ is_basis M₂ B₂ ∧ B₁ ∪ B₂ = X 

end prelim   

section intersection 

/-- size of largest common independent set -/
def ν (M₁ M₂ : matroid U) : ℤ := 
  max_val (λ (X : common_ind M₁ M₂), size X.val)

lemma ν_nonneg (M₁ M₂ : matroid U) : 
  0 ≤ ν M₁ M₂ := 
begin
  rcases max_spec (λ (X : common_ind M₁ M₂), size X.val) with ⟨X, hX1, hX2⟩, 
  rw [ν, ←hX1],
  apply size_nonneg,  
end

/-- function that provides an upper bound on ν M₁ M₂ -/
def matroid_intersection_ub_fn (M₁ M₂ : matroid U) : set U → ℤ := 
  (λ X, M₁.r X + M₂.r Xᶜ)

local notation `ub_fn` := matroid_intersection_ub_fn 

theorem matroid_intersection_pair_le {M₁ M₂ : matroid U}{I : common_ind M₁ M₂}(A : set U) : 
  size (I : set U) ≤ M₁.r A + M₂.r Aᶜ := 
begin
  rcases I with ⟨I, ⟨h₁, h₂⟩⟩, 
  unfold_coes, dsimp only, 
  rw ←(compl_inter_size A I), 
  have h₁i := I2 (inter_subset_right A I) h₁, 
  have h₂i := I2 (inter_subset_right Aᶜ I) h₂, 
  rw [←indep_iff_r.mp h₁i, ←indep_iff_r.mp h₂i], 
  linarith [rank_mono_inter_left M₁ A I, rank_mono_inter_left M₂ Aᶜ I], 
end

lemma ν_ub (M₁ M₂ : matroid U): 
  ν M₁ M₂ ≤ min_val (matroid_intersection_ub_fn M₁ M₂)  := 
begin
  rcases max_spec (λ (X : common_ind M₁ M₂), size X.val) with ⟨X, hX1, hX2⟩,
  rcases min_spec (matroid_intersection_ub_fn M₁ M₂) with ⟨A, hA1, hA2⟩, 
  rw [ν, ←hX1, ←hA1], 
  apply matroid_intersection_pair_le, 
end

/-- Edmonds' matroid intersection theorem: the size of a largest common independent set 
    is equal to the minimum value of a natural upper bound on the size of any such set. 
    Implies many other minmax theorems in combinatorics.                             -/
theorem matroid_intersection (M₁ M₂ : matroid U): 
  ν M₁ M₂ = min_val (matroid_intersection_ub_fn M₁ M₂) := 
begin
  --induction boilerplate (and ≥ suffices)

  set lb_fn := λ (M₁ M₂ : matroid U), (λ (X : common_ind M₁ M₂), size X.val) with h_lb_fn, 

  set Q : ℤ → Prop := 
    λ s, ∀ (M₁ M₂ : matroid U), size (loops M₁ ∪ loops M₂)ᶜ = s → 
      min_val (ub_fn M₁ M₂) ≤ ν M₁ M₂,
  suffices : ∀ n₀, 0 ≤ n₀ → Q n₀, 
    from antisymm (ν_ub M₁ M₂) (this _ (size_nonneg _) M₁ M₂ rfl), 
  refine nonneg_int_strong_induction _ (λ N₁ N₂ hloops, _) (λ n hn IH N₁ N₂ hsize, _), 

  -- base case, when everything is a loop. Here the LHS is obviously 0.
  rw [size_zero_iff_empty, univ_iff_compl_empty] at hloops,
  have h' : (matroid_intersection_ub_fn N₁ N₂) (loops N₁) = 0 :=  by 
  {
    simp_rw matroid_intersection_ub_fn,  
    linarith [N₂.rank_nonneg (loops N₁)ᶜ, rank_loops N₁, rank_loops N₂,  
                              N₂.rank_mono (cover_compl_subset hloops)], 
  },
  linarith [ν_nonneg N₁ N₂, min_is_lb (ub_fn N₁ N₂) (loops N₁)],  

  -- we now assume that the result holds for any strictly loopier pair of matroids, 
  -- and that there is at least one common nonloop; call it e. 
  set k := ν N₁ N₂ with hk, 
  rw ←hsize at hn, 
  cases size_pos_has_elem hn with e he, 

  have h_e_nl : (is_nonloop N₁ e) ∧ (is_nonloop N₂ e) := by split; 
  {
    rw [nonloop_iff_not_elem_loops, ←elem_compl_iff], 
    refine elem_of_elem_of_subset he _, 
    simp only [compl_union, inter_subset_left, inter_subset_right],
  }, 

  -- contract and delete (loopify/project) e from both elements of the pairs, to get 
  -- strictly loopier pairs to which we'll apply the IH, along with the associated maximizers 
  set N₁d := loopify N₁ e with hN₁d, 
  set N₂d := loopify N₂ e with hN₂d, 
  set N₁c := project N₁ e with hN₁c, 
  set N₂c := project N₂ e with hN₂c, 

  rcases max_spec (λ (X : common_ind N₁d N₂d), size X.val) with ⟨⟨Id,hId_ind⟩, ⟨hId_eq_max, hId_ub⟩⟩, 
  rcases max_spec (λ (X : common_ind N₁c N₂c), size X.val) with ⟨⟨Ic,hIc_ind⟩, ⟨hIc_eq_max, hIc_ub⟩⟩,

  -- e doesn't belong to Ic, because Ic is independent in M/e 
  have heIc : e ∉ Ic := λ heIc, by 
  {
    have := projected_set_rank_zero N₁ e, 
    rw [←hN₁c, elem_indep_r heIc hIc_ind.1] at this, 
    from one_ne_zero this, 
  },

  -- ν does not get larger upon deletion 
  have h_nu_d : ν N₁d N₂d ≤ k := by 
  { 
    rw [ν, ←hId_eq_max, hk, ν],
    refine max_is_ub (λ (X : common_ind N₁ N₂), size X.val) ⟨Id,_⟩, 
    from ⟨indep_of_loopify_indep hId_ind.1, indep_of_loopify_indep hId_ind.2⟩,
  },

  -- ν goes down upon contraction 
  have h_nu_c : ν N₁c N₂c ≤ k-1 := by 
  {
    rw [hk, ν, ν, ←hIc_eq_max], 
    have := max_is_ub (λ (X : common_ind N₁ N₂), size X.val) ⟨Ic ∪ e, _⟩, 
    dsimp only at this ⊢,
    linarith only [add_nonelem_size heIc, this], 
    split, 
    from indep_of_project_indep hIc_ind.1 (nonloop_iff_indep.mp h_e_nl.1), 
    from indep_of_project_indep hIc_ind.2 (nonloop_iff_indep.mp h_e_nl.2),                                                               
  },                             

  -- (N₁\ e, N₂\e) is loopier 
  have h_more_loops_d : size (loops N₁d ∪ loops N₂d)ᶜ < n := by 
  {
    have h_add_e := union_subset_pairs 
      (loopify_makes_loops N₁ e) 
      (loopify_makes_loops N₂ e), 
    rw ←union_distrib_union_left at h_add_e, 
    have := size_monotone h_add_e, 
    rw [add_compl_single_size he, ←hN₁d, ←hN₂d] at this, 
    rw [compl_size] at ⊢ hsize, linarith,  
  },

  -- so is (N₁/e , N₂/e)
  have h_more_loops_c : size (loops N₁c ∪ loops N₂c)ᶜ < n := by 
  {
    have h_add_e := union_subset_pairs 
      (project_makes_loops N₁ e) 
      (project_makes_loops N₂ e), 
    rw ←union_distrib_union_left at h_add_e, 
    have := size_monotone h_add_e, 
    rw [add_compl_single_size he, ←hN₁c, ←hN₂c] at this, 
    rw [compl_size] at ⊢ hsize, linarith,  
  },  

  -- apply IH to deletion, get minimizer Ad
  rcases IH _ (size_nonneg _) h_more_loops_d N₁d N₂d rfl with hd, 
  rcases min_spec (ub_fn N₁d N₂d) with ⟨Ad, ⟨hAd_eq_min, hAd_lb⟩⟩, 
  rw [←hAd_eq_min] at hd, 
  have hAd_ub : N₁.r (Ad \ e) + N₂.r (Adᶜ \ e) ≤ k := le_trans hd h_nu_d,


  --apply IH to contraction, get minimizer Ac 
  rcases IH _ (size_nonneg _) h_more_loops_c N₁c N₂c rfl with hc,
  rcases min_spec (ub_fn N₁c N₂c) with ⟨Ac, ⟨hAc_eq_min, hAc_lb⟩⟩,
  rw [←hAc_eq_min] at hc, 
  have hAc_ub : N₁.r (Ac ∪ e) + N₂.r (Acᶜ ∪ e) ≤ k+1 := by 
  {
    suffices : (N₁.r (Ac ∪ e) - N₁.r e) + (N₂.r (Acᶜ ∪ e) - N₂.r e) ≤ k-1, 
      by linarith [rank_nonloop h_e_nl.1, rank_nonloop h_e_nl.2],
    from le_trans hc h_nu_c, 
  },

  -- use contradiction, and replace the IH with a bound applying to all sets 
  by_contra h_contr, push_neg at h_contr, 
  replace h_contr : ∀ X, k + 1 ≤ ub_fn N₁ N₂ X := 
    λ X, by linarith [min_is_lb (ub_fn N₁ N₂) X],

  -- apply the bound to sets for which we know a bound in the other direction; 
  have hi := h_contr (Ac ∩ Ad \ e), 
  have hu := h_contr (Ac ∪ Ad ∪ e), 
  unfold matroid_intersection_ub_fn at hi hu, 
  rw [compl_union, compl_union, ←diff_def] at hu, 
  rw [compl_diff, compl_inter] at hi, 
  
  -- contradict submodularity. 
  have sm1 := N₁.rank_submod (Ac ∪ e) (Ad \ e), 
  have sm2 := N₂.rank_submod (Acᶜ ∪ e) (Adᶜ \ e),
  rw [union_union_diff, union_inter_diff] at sm1 sm2, 
  linarith only [sm1, sm2, hi, hu, hAd_ub, hAc_ub], 
end

/-- restatement of matroid intersection as the existence of a matching maximizer/minimizer -/
theorem matroid_intersection_exists_pair_eq (M₁ M₂ : matroid U): 
  ∃ I A, is_common_ind M₁ M₂ I ∧ size I =  M₁.r A + M₂.r Aᶜ  := 
begin
  rcases max_spec (λ (I : common_ind M₁ M₂), size I.val) with ⟨⟨I,h_ind⟩,h_eq_max, hI_ub⟩, 
  rcases min_spec (λ X, M₁.r X + M₂.r Xᶜ) with ⟨A, hA_eq_min, hA_lb⟩, 
  refine ⟨I, A, ⟨h_ind,_⟩⟩,  
  dsimp only [ftype.ftype_coe, nonempty_of_inhabited] at *, 
  rw [h_eq_max, hA_eq_min], 
  apply matroid_intersection, 
end 

end intersection 




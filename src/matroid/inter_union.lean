
import .constructions .projection ftype.minmaxsum

open_locale classical 
noncomputable theory 
namespace ftype 

variables {U : ftype}

-- setting up the various types we are minimizing/maximizing over 
section prelim 

instance set_fintype : fintype (set U) := set_fintype_of U

def indep_pair (M₁ M₂ : rankfun U) := {p : set U × set U // is_indep M₁ p.1 ∧ is_indep M₂ p.2}

def basis_pair (M₁ M₂ : rankfun U) := {p : set U × set U // is_basis M₁ p.1 ∧ is_basis M₂ p.2}

def is_disjoint (pair : (set U × set U)) : Prop := pair.1 ∩ pair.2 = ∅  

def inter_size (pair : (set U × set U)) : ℤ := size (pair.1 ∩ pair.2)

def union_size (pair : (set U × set U)) : ℤ := size (pair.1 ∪ pair.2) 

def disjoint_indep_pair (M₁ M₂ : rankfun U) := {pair : indep_pair M₁ M₂ // is_disjoint pair.1}

def disjoint_basis_pair (M₁ M₂ : rankfun U) := {pair : basis_pair M₁ M₂ // is_disjoint pair.1}

instance nonempty_indep (M : rankfun U) : nonempty {X : set U // is_indep M X} := 
  nonempty_subtype.mpr ⟨∅, I1 M⟩

instance nonempty_basis (M : rankfun U) : nonempty {B : set U // is_basis M B} := 
  nonempty_subtype.mpr (exists_basis M)

instance indep_pair_fintype {M₁ M₂ : rankfun U} : fintype (indep_pair M₁ M₂) := 
  by {unfold indep_pair, apply_instance }

instance basis_pair_fintype {M₁ M₂ : rankfun U} : fintype (basis_pair M₁ M₂) := 
  by {unfold basis_pair, apply_instance }

instance indep_pair_nonempty {M₁ M₂ : rankfun U} : nonempty (indep_pair M₁ M₂) := 
begin
  simp only [indep_pair, exists_and_distrib_right, nonempty_subtype, exists_and_distrib_left, prod.exists], 
  from ⟨⟨∅, I1 M₁⟩, ⟨∅, I1 M₂⟩⟩,  
end 

instance basis_pair_nonempty {M₁ M₂ : rankfun U} : nonempty (basis_pair M₁ M₂) := 
begin
  simp only [basis_pair, exists_and_distrib_right, nonempty_subtype, exists_and_distrib_left, prod.exists], 
  from ⟨exists_basis M₁, exists_basis M₂⟩,  
end 

instance disjoint_indep_pair_nonempty (M₁ M₂ : rankfun U) : 
  nonempty (disjoint_indep_pair M₁ M₂) :=
by {unfold disjoint_indep_pair, refine nonempty_subtype.mpr _, use ⟨⟨∅,∅⟩, ⟨I1 M₁, I1 M₂⟩⟩, tidy,  } 

/--independence in both M₁ and M₂ -/
def is_common_ind (M₁ M₂ : rankfun U) := 
  λ X, is_indep M₁ X ∧ is_indep M₂ X 

/-- subtype of common independent sets -/ 
def common_ind (M₁ M₂ : rankfun U) := {X : set U // is_common_ind M₁ M₂ X}

instance nonempty_common_ind (M₁ M₂ : rankfun U) : nonempty (common_ind M₁ M₂) := 
by {apply nonempty_subtype.mpr, from ⟨∅, ⟨I1 M₁, I1 M₂⟩⟩}

instance fintype_common_ind (M₁ M₂ : rankfun U ): fintype (common_ind M₁ M₂) := 
  by {unfold common_ind, apply_instance}

instance coe_common_ind (M₁ M₂ : rankfun U) : has_coe (common_ind M₁ M₂) (set U) :=
  ⟨λ X, X.val⟩

/-- has partition into an independent set of M₁ and an independent set of M₂-/
def is_two_partitionable (M₁ M₂ : rankfun U) : set U → Prop := 
  λ X, ∃ I₁ I₂, is_indep M₁ I₁ ∧ is_indep M₂ I₂ ∧ X = I₁ ∪ I₂ ∧ I₁ ∩ I₂ = ∅

/-- has partition into a basis of M₁ and a basis set of M₂-/
def is_two_basis_partitionable (M₁ M₂ : rankfun U) : set U → Prop := 
  λ X, ∃ B₁ B₂ , is_basis M₁ B₁ ∧ is_basis M₂ B₂ ∧ B₁ ∪ B₂ = X ∧ B₁ ∩ B₂ = ∅

/-- is the union of a basis of M₁ and a basis of M₂ -/
def is_union_two_bases (M₁ M₂ : rankfun U) : set U → Prop := 
  λ X, ∃ B₁ B₂, is_basis M₁ B₁ ∧ is_basis M₂ B₂ ∧ B₁ ∪ B₂ = X 

end prelim   

section intersection 

/-- size of largest common independent set -/
def ν (M₁ M₂ : rankfun U) : ℤ := 
  max_val (λ (X : common_ind M₁ M₂), size X.val)

lemma ν_nonneg (M₁ M₂ : rankfun U) : 
  0 ≤ ν M₁ M₂ := 
begin
  rcases max_spec (λ (X : common_ind M₁ M₂), size X.val) with ⟨X, hX1, hX2⟩, 
  rw [ν, ←hX1],
  apply size_nonneg,  
end

/-- function that provides an upper bound on ν M₁ M₂ -/
def matroid_intersection_ub_fn (M₁ M₂ : rankfun U) : set U → ℤ := 
  (λ X, M₁.r X + M₂.r Xᶜ)

local notation `ub_fn` := matroid_intersection_ub_fn 

theorem matroid_intersection_pair_le {M₁ M₂ : rankfun U}{I : common_ind M₁ M₂}(A : set U) : 
  size (I : set U) ≤ M₁.r A + M₂.r Aᶜ := 
begin
  rcases I with ⟨I, ⟨h₁, h₂⟩⟩, 
  unfold_coes, dsimp only, 
  rw ←(compl_inter_size A I), 
  have h₁i := I2 (inter_subset_right A I) h₁, 
  have h₂i := I2 (inter_subset_right Aᶜ I) h₂, 
  rw [←indep_iff_r.mp h₁i, ←indep_iff_r.mp h₂i], 
  linarith [R2_i M₁ A I, R2_i M₂ Aᶜ I], 
end

lemma ν_ub (M₁ M₂ : rankfun U): 
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
theorem matroid_intersection (M₁ M₂ : rankfun U): 
  ν M₁ M₂ = min_val (matroid_intersection_ub_fn M₁ M₂) := 
begin
  --induction boilerplate (and ≥ suffices)

  set lb_fn := λ (M₁ M₂ : rankfun U), (λ (X : common_ind M₁ M₂), size X.val) with h_lb_fn, 

  set Q : ℤ → Prop := 
    λ s, ∀ (M₁ M₂ : rankfun U), size (loops M₁ ∪ loops M₂)ᶜ = s → 
      min_val (ub_fn M₁ M₂) ≤ ν M₁ M₂,
  suffices : ∀ n₀, 0 ≤ n₀ → Q n₀, 
    from antisymm (ν_ub M₁ M₂) (this _ (size_nonneg _) M₁ M₂ rfl), 
  refine nonneg_int_strong_induction _ (λ N₁ N₂ hloops, _) (λ n hn IH N₁ N₂ hsize, _), 

  -- base case, when everything is a loop. Here the certificate is obvious.
  rw [size_zero_iff_empty, univ_iff_compl_empty] at hloops,
  have h' : (matroid_intersection_ub_fn N₁ N₂) (loops N₁) = 0 :=  by 
  {
    simp_rw matroid_intersection_ub_fn,  
    linarith [R0 N₂ (loops N₁)ᶜ, rank_loops N₁, rank_loops N₂,  
                              R2 N₂ (cover_compl_subset hloops)], 
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
  -- strictly loopier pairs to which we'll apply the IH. 
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

  -- ν goes down upon contrction 
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

  -- same for (N₁/e , N₂/e)
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
  -- contradict submodularity. 
  have hi := h_contr (Ac ∩ Ad \ e), 
  have hu := h_contr (Ac ∪ Ad ∪ e), 
  unfold matroid_intersection_ub_fn at hi hu, 
  rw [compl_union, compl_union, ←diff_def] at hu, 
  rw [compl_diff, compl_inter] at hi, 
  have sm1 := R3 N₁ (Ac ∪ e) (Ad \ e), 
  have sm2 := R3 N₂ (Acᶜ ∪ e) (Adᶜ \ e),
  rw [union_union_diff, union_inter_diff] at sm1 sm2, 
  linarith only [sm1, sm2, hi, hu, hAd_ub, hAc_ub], 
end

/-- restatement of matroid intersection as the existence of a matching maximizer/minimizer -/
theorem matroid_intersection_exists_pair_eq (M₁ M₂ : rankfun U): 
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

section intersections_of_bases

/-- is the intersection of a basis of M₁ and a basis of M₂ -/
def is_inter_bases (M₁ M₂ : rankfun U) := 
  λ X, ∃ B₁ B₂, is_basis M₁ B₁ ∧ is_basis M₂ B₂ ∧ B₁ ∩ B₂ = X 

/-- is contained in the intersection of a basis of M₁ and a basis of M₂-/
def is_subset_inter_bases (M₁ M₂ : rankfun U) := 
  λ X, ∃ Y, is_inter_bases M₁ M₂ Y ∧ X ⊆ Y 

lemma exists_inter_bases (M₁ M₂ : rankfun U):
  ∃ I, (is_inter_bases M₁ M₂ I) := 
begin
  cases exists_basis M₁ with B₁ hB₁, 
  cases exists_basis M₂ with B₂ hB₂,
  from ⟨B₁ ∩ B₂, ⟨B₁,B₂,hB₁,hB₂,rfl⟩⟩, 
end

def inter_bases (M₁ M₂ : rankfun U) := {X : set U // is_inter_bases M₁ M₂ X}

instance inter_bases_nonempty (M₁ M₂ : rankfun U) : nonempty (inter_bases M₁ M₂) :=
by {apply nonempty_subtype.mpr, apply exists_inter_bases, } 

instance inter_bases_fintype (M₁ M₂ : rankfun U) : fintype (inter_bases M₁ M₂) := 
by {unfold inter_bases, apply_instance,}

lemma subset_inter_bases_is_common_ind {M₁ M₂ : rankfun U}{I : set U} :
  is_subset_inter_bases M₁ M₂ I → is_common_ind M₁ M₂ I :=
begin
  rintros ⟨Y, ⟨B₁,B₂,hB₁,hB₂, hIB₁B₂⟩,hY'⟩, 
  rw ←hIB₁B₂ at hY', split, 
  refine I2 (subset_trans hY' _) (basis_is_indep hB₁),
  apply inter_subset_left,    
  refine I2 (subset_trans hY' _) (basis_is_indep hB₂),
  apply inter_subset_right,
end

lemma is_common_ind_iff_is_subset_inter_bases {M₁ M₂ : rankfun U}:
  is_common_ind M₁ M₂ = is_subset_inter_bases M₁ M₂ :=
begin
  ext I, 
  refine ⟨λ h, _, subset_inter_bases_is_common_ind⟩, 
  rcases extends_to_basis h.1 with ⟨B₁,hIB₁,hB₁⟩,
  rcases extends_to_basis h.2 with ⟨B₂,hIB₂,hB₂⟩, 
  from ⟨B₁ ∩ B₂, ⟨B₁, B₂, hB₁, hB₂, rfl⟩, inter_is_lb hIB₁ hIB₂⟩, 
end

lemma inter_two_bases_is_subset_inter_bases {M₁ M₂ : rankfun U}{B₁ B₂ : set U}:
  is_basis M₁ B₁ → is_basis M₂ B₂ → is_subset_inter_bases M₁ M₂ (B₁ ∩ B₂) := 
λ h₁ h₂, by {refine ⟨B₁ ∩ B₂, ⟨B₁,B₂,h₁,h₂, rfl⟩ , subset_refl _⟩, }

lemma inter_bases_is_subset_inter_bases {M₁ M₂ : rankfun U}{I : set U}: 
  is_inter_bases M₁ M₂ I → is_subset_inter_bases M₁ M₂ I := 
λ h, by {rcases h with ⟨B₁,B₂,h⟩, refine ⟨I, ⟨B₁, B₂, h⟩, subset_refl _⟩,}

lemma inter_bases_is_common_ind {M₁ M₂ : rankfun U}{I : set U} :
  is_inter_bases M₁ M₂ I → is_common_ind M₁ M₂ I := 
by {rw is_common_ind_iff_is_subset_inter_bases, from inter_bases_is_subset_inter_bases}


lemma max_common_indep_inter_bases (M₁ M₂ : rankfun U):
  ν M₁ M₂ = max_val (λ (pair : basis_pair M₁ M₂), inter_size pair.val) :=
begin
  rcases max_spec (λ (X : common_ind M₁ M₂), size X.val) with ⟨⟨I,hI_ind⟩,hI_size,hI_ub⟩, 
  rcases max_spec (λ (pair : basis_pair M₁ M₂), inter_size pair.val) with ⟨⟨⟨B₁, B₂⟩,hB⟩,h_inter,h_size_ub⟩, 
  rw [ν], dsimp at *, rw [←hI_size, ←h_inter],
  apply le_antisymm, 
  rw is_common_ind_iff_is_subset_inter_bases at hI_ind, 
  rcases hI_ind with ⟨Y,⟨⟨B₁',B₂',⟨hB₁',hB₂',hY⟩⟩,h'⟩⟩, 
  have := h_size_ub ⟨⟨B₁',B₂'⟩, ⟨hB₁', hB₂'⟩⟩, rw inter_size at this, dsimp at this,  
  rw ←hY at h', 
  linarith [size_monotone h'],
  refine (hI_ub ⟨B₁ ∩ B₂, subset_inter_bases_is_common_ind (inter_two_bases_is_subset_inter_bases hB.1 hB.2) ⟩), 
end

end intersections_of_bases


section union

/-- size of the largest set that is the union of independent sets of M₁ and M₂-/
def π (M₁ M₂ : rankfun U) : ℤ :=  
  max_val (λ (Ip : indep_pair M₁ M₂), union_size Ip.val)

lemma π_eq_max_union_bases (M₁ M₂ : rankfun U) :
  π M₁ M₂ = max_val (λ (Bp : basis_pair M₁ M₂), union_size Bp.val) := 
begin
  rcases max_spec (λ (Bp : basis_pair M₁ M₂), union_size Bp.val) 
    with ⟨⟨⟨Bp₁, Bp₂⟩, hBp⟩, hBp_union, hBp_ub⟩, 
  rcases max_spec (λ (Ip : indep_pair M₁ M₂), union_size Ip.val) 
    with ⟨⟨⟨Ip₁, Ip₂⟩, hIp⟩, hIp_union, hIp_ub⟩, 
  rw [π], dsimp only at *, rw [←hBp_union, ←hIp_union], 
  apply le_antisymm,
  rcases extends_to_basis hIp.1 with ⟨B₁,hB₁⟩, 
  rcases extends_to_basis hIp.2 with ⟨B₂,hB₂⟩, 
  refine le_trans (size_monotone _) (hBp_ub ⟨⟨B₁, B₂⟩, ⟨hB₁.2, hB₂.2⟩⟩), 
  from union_subset_pairs hB₁.1 hB₂.1, 
  from hIp_ub ⟨⟨Bp₁,Bp₂⟩, ⟨basis_is_indep hBp.1,basis_is_indep hBp.2⟩⟩, 
end

/-- simple relationship between π M₁ M₂ and ν M₁ M₂* -/
theorem π_eq_ν_plus_r (M₁ M₂ : rankfun U) :
  π M₁ M₂ = ν M₁ (dual M₂) + M₂.r univ := 
begin
  rw [eq_comm,max_common_indep_inter_bases, π_eq_max_union_bases],
  
  -- bijection φ that we will use to reindex summation
  set φ : basis_pair M₁ M₂ → basis_pair M₁ (dual M₂) := λ p, ⟨⟨p.val.1, p.val.2ᶜ⟩,_⟩ with hφ, 
  swap,
  -- φ really maps to basis,cobasis pairs
  {
    dsimp only, refine ⟨p.property.1, _⟩, 
    rw [←cobasis_iff_compl_basis, cobasis_iff, dual_dual], 
    from p.property.2, 
  },
  -- ... and is bijective
  have hφ_bij : function.bijective φ := by  
  {
    refine ⟨λ Bp Bp' h,_, λ Bp,_⟩, 
    rcases Bp with ⟨⟨Bp₁,Bp₂⟩,hBp⟩ ; rcases Bp' with ⟨⟨Bp'₁,Bp'₂⟩,hBp'⟩,  
    rw hφ at h, dsimp at h, 
    rw subtype.mk_eq_mk at h ⊢, 
    simp only [prod.mk.inj_iff, compl_inj_iff] at h ⊢, 
    from h, 
    refine ⟨⟨⟨Bp.val.1,Bp.val.2ᶜ⟩,⟨Bp.property.1,_⟩⟩,_⟩, dsimp,  
    rw [←cobasis_iff_compl_basis, cobasis_iff], from Bp.property.2, 
    rw hφ,  simp,  
  },
  -- use φ to reindex so LHS/RHS are being summed over the same set 
  have := max_reindex φ hφ_bij (λ pair, inter_size pair.val), erw ←this,
  
  -- bring addition inside the max 
  rw max_add_commute, 
  
  -- it remains show the functions we're maximizing are the same 
  convert rfl, ext Bp, 
  rcases Bp with ⟨⟨B₁,B₂⟩,hB⟩,   
  dsimp [union_size,inter_size] at ⊢ hB,
  linarith [size_basis hB.1, size_basis hB.2, size_modular B₁ B₂, size_induced_partition_inter B₁ B₂], 
end 


/-- The matroid union theorem for two matroids : a minmax formula for the size of the
largest partitionable set. The heavy lifting in the proof is done by matroid intersection. -/
theorem two_matroid_union (M₁ M₂ : rankfun U) :
  π M₁ M₂ = min_val (λ A : set U, size (Aᶜ) + M₁.r A + M₂.r A ) :=
begin
  rw [π_eq_ν_plus_r, matroid_intersection],
  rw min_add_commute (matroid_intersection_ub_fn M₁ (dual M₂)) (M₂.r univ),
  congr', ext X, rw [matroid_intersection_ub_fn], dsimp,
  rw [dual_r, compl_compl], linarith,  
end

end union 




end ftype 
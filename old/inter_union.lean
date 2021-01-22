import .constructions .projection ftype.minmaxsum 

noncomputable theory 
namespace ftype 

variables {U : ftype}

section intersection 

/--independence in both M₁ and M₂ -/
def is_common_ind (M₁ M₂ : rankfun U)(X : set U) := 
  is_indep M₁ X ∧ is_indep M₂ X 

lemma empty_is_common_ind (M₁ M₂ : rankfun U): 
  is_common_ind M₁ M₂ (∅ : set U) := 
  ⟨I1 M₁, I1 M₂⟩ 

lemma exists_common_ind {M₁ M₂ : rankfun U}: 
  set.nonempty (is_common_ind M₁ M₂) := 
  ⟨∅, empty_is_common_ind M₁ M₂⟩

/-- size of max common independent set of M₁ M₂ -/
def ν (M₁ M₂ : rankfun U) : ℤ := 
  max_size_over (is_common_ind M₁ M₂) exists_common_ind

/-- A largest common independent set of M₁ M₂ -/
def max_common_ind (M₁ M₂ : rankfun U) : set U := 
  arg_max_size_over (is_common_ind M₁ M₂) exists_common_ind

lemma size_max_common_ind_eq_nu (M₁ M₂ : rankfun U) : 
  size (max_common_ind M₁ M₂) = ν M₁ M₂ := 
  (arg_max_over_attains _ _ _).2 

lemma max_common_ind_is_common_ind (M₁ M₂ : rankfun U) : 
  is_common_ind M₁ M₂ (max_common_ind M₁ M₂) := 
  (arg_max_over_attains _ _ _).1 

lemma size_common_ind_le_nu {M₁ M₂ : rankfun U}{X : set U} :
  is_common_ind M₁ M₂ X → size X ≤ ν M₁ M₂ := 
  λ h, (max_over_is_ub _ _ _ X h)

lemma exists_max_common_ind (M₁ M₂ : rankfun U) : 
  ∃ I, is_common_ind M₁ M₂ I ∧ size I = ν M₁ M₂ ∧ ∀ J, is_common_ind M₁ M₂ J → size J ≤ size I := 
max_size_over_spec (is_common_ind M₁ M₂) exists_common_ind
   
lemma nu_nonneg (M₁ M₂ : rankfun U) :
  0 ≤ ν M₁ M₂ := 
  by {rw ←(size_empty U), from size_common_ind_le_nu (empty_is_common_ind _ _)} 

/-- The function that provides an upper bound on ν for each X -/
def matroid_intersection_ub_fn (M₁ M₂ : rankfun U) : set U → ℤ := 
  (λ X, M₁.r X + M₂.r Xᶜ)

theorem matroid_intersection_pair_le {M₁ M₂ : rankfun U}{I : set U}(A : set U) : 
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
  set I := max_common_ind M₁ M₂ with hI, 
  rw [←size_max_common_ind_eq_nu, ←arg_min_attains ub_fn, ←hA], 
  from matroid_intersection_pair_le A (max_common_ind_is_common_ind M₁ M₂)
end

/-- Edmonds' matroid intersection theorem: the size of a largest common independent set 
    is equal to the minimum value of a natural upper bound on the size of any such set. 
    Implies many other minmax theorems in combinatorics.                             -/
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
rw [size_zero_iff_empty, univ_iff_compl_empty] at hloops,
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
cases size_pos_has_elem hn with e he, 

have h_e_nl : (is_nonloop N₁ e) ∧ (is_nonloop N₂ e) := by split; 
{
  rw [nonloop_iff_not_elem_loops, ←elem_compl_iff], 
  refine elem_of_elem_of_subset he _, 
  simp only [compl_union, inter_subset_left, inter_subset_right],
}, 

set N₁d := loopify N₁ e with hN₁d, 
set N₂d := loopify N₂ e with hN₂d, 
set N₁c := project N₁ e with hN₁c, 
set N₂c := project N₂ e with hN₂c, 

set Id := max_common_ind N₁d N₂d with hId, 
set Ic := max_common_ind N₁c N₂c with hIc, 
let hId' : is_common_ind N₁d N₂d Id := by apply max_common_ind_is_common_ind, 
let hIc' : is_common_ind N₁c N₂c Ic := by apply max_common_ind_is_common_ind,

have heIc : e ∉ Ic := λ heIc, by 
{
  have := projected_set_rank_zero N₁ e, 
  rw [←hN₁c, elem_indep_r heIc hIc'.1] at this, 
  from one_ne_zero this, 
},

have h_nu_d : ν N₁d N₂d ≤ k := by 
{ 
  rw [←size_max_common_ind_eq_nu, ←hId, hk], 
  from size_common_ind_le_nu 
        ⟨indep_of_loopify_indep hId'.1,
          indep_of_loopify_indep hId'.2⟩,
},

have h_nu_c : ν N₁c N₂c ≤ k-1 := by 
{
  rw [←size_max_common_ind_eq_nu, ←hIc, hk], 
  linarith 
  [
    add_nonelem_size heIc,
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
  have h_add_e := union_subset_pairs 
    (loopify_makes_loops N₁ e) 
    (loopify_makes_loops N₂ e), 
  rw ←union_distrib_union_left at h_add_e, 
  have := size_monotone h_add_e, 
  rw [add_compl_single_size he, ←hN₁d, ←hN₂d] at this, 
  rw [compl_size] at ⊢ hsize, linarith,  
},

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
set Ad := arg_min (ub_fn N₁d N₂d) with hAd,
rw [←arg_min_attains (ub_fn N₁d N₂d), ←hAd] at hd, 
have hAd_ub : N₁.r (Ad \ e) + N₂.r (Adᶜ \ e) ≤ k := le_trans hd h_nu_d,


--apply IH to contraction, get minimizer Ac 
rcases IH _ (size_nonneg _) h_more_loops_c N₁c N₂c rfl with hc,
set Ac := arg_min (ub_fn N₁c N₂c) with hAc,
rw [←arg_min_attains (ub_fn N₁c N₂c), ←hAc] at hc, 
have hAc_ub : N₁.r (Ac ∪ e) + N₂.r (Acᶜ ∪ e) ≤ k+1 := by 
{
  suffices : (N₁.r (Ac ∪ e) - N₁.r e) + (N₂.r (Acᶜ ∪ e) - N₂.r e) ≤ k-1, 
    by linarith [rank_nonloop h_e_nl.1, rank_nonloop h_e_nl.2],
  from le_trans hc h_nu_c, 
},

by_contra h_contr, push_neg at h_contr, 
replace h_contr : ∀ X, k + 1 ≤ ub_fn N₁ N₂ X := 
  λ X, by linarith [min_is_lb (ub_fn N₁ N₂) X],

have hi := h_contr (Ac ∩ Ad \ e), 
have hu := h_contr (Ac ∪ Ad ∪ e), 
simp_rw h_ub_fn at hi hu, 
rw [compl_union, compl_union, ←diff_def] at hu, 
rw [compl_diff, compl_inter] at hi, 
have sm1 := R3 N₁ (Ac ∪ e) (Ad \ e), 
have sm2 := R3 N₂ (Acᶜ ∪ e) (Adᶜ \ e),
rw [union_union_diff, union_inter_diff] at sm1 sm2, 
linarith only [sm1, sm2, hi, hu, hAd_ub, hAc_ub], 
end

theorem matroid_intersection_exists_pair_eq (M₁ M₂ : rankfun U): 
  ∃ I A, is_common_ind M₁ M₂ I ∧ size I =  M₁.r A + M₂.r Aᶜ  := 
begin
  set I := max_common_ind M₁ M₂ with hI, 
  let h_ind := max_common_ind_is_common_ind M₁ M₂, 
  rw ←hI at h_ind, 
  set A := arg_min (λ X, M₁.r X + M₂.r Xᶜ) with hX, 
  refine ⟨I, ⟨A, ⟨h_ind,_⟩⟩⟩,  
  rw [hI, size_max_common_ind_eq_nu, matroid_intersection M₁ M₂], 
  from (arg_min_attains _).symm, 
end 

end intersection 


section intersections_of_bases

/-- is the intersection of a basis of M₁ and a basis of M₂ -/
def is_inter_bases (M₁ M₂ : rankfun U) := 
  λ X, ∃ B₁ B₂, is_basis M₁ B₁ ∧ is_basis M₂ B₂ ∧ B₁ ∩ B₂ = X 

/-- is contained in the intersection of a basis of M₁ and a basis of M₂-/
def subset_inter_bases (M₁ M₂ : rankfun U) := 
  λ X, ∃ Y, is_inter_bases M₁ M₂ Y ∧ X ⊆ Y 

lemma subset_inter_bases_is_common_ind {M₁ M₂ : rankfun U}{I : set U} :
  subset_inter_bases M₁ M₂ I → is_common_ind M₁ M₂ I :=
begin
  rintros ⟨Y, ⟨B₁,B₂,hB₁,hB₂, hIB₁B₂⟩,hY'⟩, 
  rw ←hIB₁B₂ at hY', split, 
  refine I2 (subset_trans hY' _) (basis_is_indep hB₁),
  apply inter_subset_left,    
  refine I2 (subset_trans hY' _) (basis_is_indep hB₂),
  apply inter_subset_right,
end

lemma common_ind_iff_subset_inter_bases {M₁ M₂ : rankfun U}{I : set U}:
  is_common_ind M₁ M₂ I ↔ subset_inter_bases M₁ M₂ I :=
begin
  refine ⟨λ h, _, subset_inter_bases_is_common_ind⟩, 
  rcases extends_to_basis h.1 with ⟨B₁,hIB₁,hB₁⟩,
  rcases extends_to_basis h.2 with ⟨B₂,hIB₂,hB₂⟩, 
  from ⟨B₁ ∩ B₂, ⟨B₁, B₂, hB₁, hB₂, rfl⟩, inter_is_lb hIB₁ hIB₂⟩, 
end

lemma exists_inter_bases {M₁ M₂ : rankfun U}:
  set.nonempty (is_inter_bases M₁ M₂) := 
begin
  cases exists_basis M₁ with B₁ hB₁, 
  cases exists_basis M₂ with B₂ hB₂, 
  from ⟨B₁ ∩ B₂, ⟨B₁,B₂,hB₁,hB₂,rfl⟩⟩, 
end


lemma max_common_indep_inter_bases (M₁ M₂ : rankfun U):
  ν M₁ M₂ = max_val_over (is_inter_bases M₁ M₂) exists_inter_bases size :=
begin
  rcases exists_max_common_ind M₁ M₂ 
    with ⟨I, hI_ind, hIsize, hI'I⟩, 
  rcases max_over_spec (is_inter_bases M₁ M₂) exists_inter_bases size 
    with ⟨J,hJ_inter,hJsize, hYJ⟩,  
  rw [←hIsize, ←hJsize], 
  apply le_antisymm, 
  rw common_ind_iff_subset_inter_bases at hI_ind, 
  rcases hI_ind with ⟨Y,⟨h,h'⟩⟩, 
  linarith [hYJ _ h, size_monotone h'], 
  from hI'I J (common_ind_iff_subset_inter_bases.mpr ⟨J,⟨hJ_inter,subset_refl _⟩⟩), 
end


end intersections_of_bases
section union

/-- is the union of an independent set of M₁ and an independent set of M₂-/
def is_union_two_indep (M₁ M₂ : rankfun U) : set U → Prop := 
  λ X, ∃ I₁ I₂, is_indep M₁ I₁ ∧ is_indep M₂ I₂ ∧ X = I₁ ∪ I₂

/-- has partition into an independent set of M₁ and an independent set of M₂-/
def is_two_partitionable (M₁ M₂ : rankfun U) : set U → Prop := 
  λ X, ∃ I₁ I₂, is_indep M₁ I₁ ∧ is_indep M₂ I₂ ∧ X = I₁ ∪ I₂ ∧ I₁ ∩ I₂ = ∅

/-- has partition into a basis of M₁ and a basis set of M₂-/
def is_two_basis_partitionable (M₁ M₂ : rankfun U) : set U → Prop := 
  λ X, ∃ B₁ B₂ , is_basis M₁ B₁ ∧ is_basis M₂ B₂ ∧ B₁ ∪ B₂ = X ∧ B₁ ∩ B₂ = ∅

/-- is the union of a basis of M₁ and a basis of M₂ -/
def is_union_two_bases (M₁ M₂ : rankfun U) : set U → Prop := 
  λ X, ∃ B₁ B₂, is_basis M₁ B₁ ∧ is_basis M₂ B₂ ∧ B₁ ∪ B₂ = X 

/-- is the union of independent -/
--def is_partitionable (Mset : list (rankfun U)) : set U → Prop := 
  --λ X, ∃ f: Mset → set U, ∀ M : Mset, is_indep M.val (f M) ∧ set.sUnion (set.range f) = X  

lemma two_partitionable_iff_union_two_indep {M₁ M₂ : rankfun U} :
  is_two_partitionable M₁ M₂ = is_union_two_indep M₁ M₂ := 
begin
  ext X, rw [is_two_partitionable, is_union_two_indep], 
  refine ⟨λ ⟨I₁,I₂, h₁, h₂, hu, hi⟩, ⟨I₁, I₂, h₁, h₂, hu⟩, λ h, _⟩, 
  rcases h with ⟨I₁,I₂, h₁, h₂, hu⟩, 
  from ⟨I₁, I₂ \ I₁, h₁, I2 (diff_subset I₂ I₁) h₂ , by simp [hu], by simp⟩,
end


/-- is a subset of the union of a basis of X and a basis of Y-/
def is_subset_union_two_bases (M₁ M₂ : rankfun U) := 
  λ X, ∃ Y, is_union_two_bases M₁ M₂ Y ∧ X ⊆ Y 

lemma two_partitionable_iff_subset_union_two_bases {M₁ M₂ : rankfun U}:
  is_two_partitionable M₁ M₂ = is_subset_union_two_bases M₁ M₂ := 
begin
  rw [two_partitionable_iff_union_two_indep], ext X, 
  refine ⟨λ h,_,λ h,_⟩, 
  
  rcases h with ⟨I₁, I₂, hI₁, hI₂, hIX⟩,
  cases extends_to_basis hI₁ with B₁ hB₁,  
  cases extends_to_basis hI₂ with B₂ hB₂, 
  refine ⟨B₁ ∪ B₂, ⟨B₁, B₂, hB₁.2, hB₂.2, rfl ⟩, _⟩,
  rw hIX, apply union_subset_pairs hB₁.1 hB₂.1, 

  rcases h with ⟨Y, ⟨B₁, B₂, hB₁, hB₂, hBY⟩, hXY⟩, 
  refine ⟨X ∩ B₁, X ∩ B₂, I2_i_right (basis_is_indep hB₁), I2_i_right (basis_is_indep hB₂), _ ⟩,   
  rw [←inter_distrib_left, hBY, eq_comm, ←subset_def_inter],
  from hXY, 
end

lemma union_two_bases_is_subset_union_two_bases (M₁ M₂ : rankfun U): 
  ∀ X, is_union_two_bases M₁ M₂ X → ∃ Y, is_union_two_bases M₁ M₂ Y ∧ X ⊆ Y :=
λ X hX, ⟨X, ⟨hX, subset_refl _⟩⟩ 

lemma exists_two_partitionable (M₁ M₂ : rankfun U): 
  ∃ X, is_two_partitionable M₁ M₂ X := 
⟨∅, ∅, ∅, I1 M₁, I1 M₂, by rw union_self, by rw inter_idem⟩

lemma exists_union_two_indep (M₁ M₂ : rankfun U): 
  ∃ X, is_union_two_indep M₁ M₂ X := 
⟨∅, ∅, ∅, I1 M₁, I1 M₂, by rw union_self⟩

lemma exists_union_two_bases (M₁ M₂ : rankfun U): 
  ∃ X, is_union_two_bases M₁ M₂ X := 
by {cases exists_basis M₁ with B₁ h₁, cases exists_basis M₂ with B₂ h₂, from ⟨_, B₁, B₂, h₁, h₂, rfl⟩}

lemma exists_subset_union_two_bases (M₁ M₂ : rankfun U): 
  ∃ X, is_subset_union_two_bases M₁ M₂ X := 
by {cases exists_union_two_bases M₁ M₂ with Y hY, from ⟨Y,Y,hY, subset_refl Y⟩,  }

/-- prop that there exists a set that is a basis of both M₁ and M₂-/
def exists_common_basis (M₁ M₂ : rankfun U) :=
  ∃ B, is_basis M₁ B ∧ is_basis M₂ B 

lemma univ_partitionable_iff_dual_common_basis {M₁ M₂ : rankfun U}:
  is_two_basis_partitionable M₁ M₂ (univ : set U) ↔ exists_common_basis M₁ (dual M₂) :=
begin
  refine ⟨λ h, _, λ h,_⟩,
  rcases h with ⟨B₁, B₂, h₁, h₂, hu, hi⟩, 
  refine ⟨B₁,h₁,_⟩, 
  rw [←cobasis_iff, cobasis_iff_compl_basis, (compl_unique hu hi).symm],
  from h₂, 
  rcases h with ⟨B, hB₁, hB₂⟩, 
  rw [←cobasis_iff, cobasis_iff_compl_basis] at hB₂, 
  refine ⟨B, Bᶜ, hB₁, hB₂, by simp⟩, 
end



/-- size of largest set that partitions into independent sets of M₁, M₂ -/
def π (M₁ M₂ : rankfun U) : ℤ :=
  max_size_over (is_two_partitionable M₁ M₂) (exists_two_partitionable _ _)

lemma π_attained_by_bases (M₁ M₂ : rankfun U) : 
  π M₁ M₂ = max_size_over (is_union_two_bases M₁ M₂) (exists_union_two_bases M₁ M₂) :=
begin
  --rcases max_size_over_spec (is_union_two_bases M₁ M₂) (exists_union_two_bases M₁ M₂) 
  --  with ⟨X, hXu, hsX, hYX⟩, 
  unfold π, simp_rw [two_partitionable_iff_subset_union_two_bases], 
  refine le_antisymm _ _, 
  rcases max_size_over_spec (is_union_two_bases M₁ M₂) (exists_union_two_bases M₁ M₂) 
    with ⟨X, hXu, hsX, hYX⟩, 
  rcases max_size_over_spec (is_subset_union_two_bases M₁ M₂) (exists_subset_union_two_bases M₁ M₂) 
    with ⟨X', hX'u, hsX', hYX'⟩, 
  
  erw [←hsX, ←hsX'], 
  cases hX'u with Y hY, 
  linarith [hYX Y hY.1, size_monotone hY.2], 
  
  have hPQ := union_two_bases_is_subset_union_two_bases M₁ M₂, 
  refine max_over_subset_le_max 
    (is_union_two_bases M₁ M₂)
    (λ X, ∃ Y, is_union_two_bases M₁ M₂ Y ∧ X ⊆ Y)
    (exists_union_two_bases M₁ M₂)
    size 
    (union_two_bases_is_subset_union_two_bases M₁ M₂), 
end


----------------------------- Trying to make summation manipulations more versatile ----------------

def prop_pairs {α : Type} (P₁ P₂ : α → Prop) := {x : α // P₁ x} × {x : α // P₂ x}



instance pp_fin {α : Type} [fintype α] {P₁ P₂ : α → Prop} : fintype (prop_pairs P₁ P₂) := 
begin
  --letI i1: fintype {x : α // P₁ x} := infer_instance, 
  --letI i2: fintype {x : α // P₂ x} := infer_instance,  
  unfold prop_pairs, apply_instance,
  --from @prod.fintype _ _ (fintype.subtype_of_fintype (is_basis M₁)) (fintype.subtype_of_fintype (is_basis M₂)),
end 


def basis_pairs (M₁ M₂ : rankfun U) := {B : set U // is_basis M₁ B} × {B : set U // is_basis M₂ B}



def  bp_fin {M₁ M₂ : rankfun U}: fintype (basis_pairs M₁ M₂) := 
begin
  letI := U.fin, 
  unfold basis_pairs, apply_instance,
  --haveI : fintype (set U) := infer_instance, 
  --haveI i1 : fintype {B : set U // is_basis M₁ B} := by library_search,
  --haveI i2 : fintype {B : set U // is_basis M₂ B} := infer_instance, 
  --exact @prod.fintype _ _ (fintype.subtype_of_fintype (is_basis M₁)) (fintype.subtype_of_fintype (is_basis M₂)),
  
  --unfold basis_pairs, 
  
  -- assumption, 
end


----------------------------------------------------------------------------------------------------
/-
lemma ν_eq_π_minus_rank (M₁ M₂ : rankfun U) : 
  ν M₁ (dual M₂) = π M₁ M₂ - M₂.r univ := 
begin
  set sub_r : ℤ → ℤ := λ n, n - M₂.r univ with h_sub_r, 

  set cond2 := λ X, ∃ B₁ B₂, is_basis M₁ B₁ ∧ is_basis M₂ B₂ ∧ X = B₁ \ B₂ with hcond2, 

  have h_mono : monotone sub_r := λ n n' hnn', by {simp only [sub_r], linarith,}, 
  --have := calc ν M₁ (dual M₂) = _ : by rw max_common_indep_inter_bases, 
  rw max_common_indep_inter_bases, 

  have h2: is_inter_bases M₁ (dual M₂) = cond2 := by 
  {
      ext, refine ⟨λ h,_,λ h,_⟩, 
      rcases h with ⟨B₁, B₂, hB₁, hB₂, hX⟩, 
      refine ⟨B₁, B₂ᶜ, hB₁,_,by simp [hX]⟩, 
      rw [←cobasis_iff_compl_basis], from hB₂, 
      rcases h with ⟨B₁, B₂, hB₁, hB₂, hX⟩, 
      refine ⟨B₁, B₂ᶜ,hB₁,_,by simp [hX]⟩, 
      simp_rw [←cobasis_iff_compl_basis, ←is_cobasis, dual_dual, hB₂],
  },
  have h3 : max_val_over (is_inter_bases M₁ (dual M₂)) exists_inter_bases size 
          = max_val_over cond2 (by {rw ←h2, apply exists_inter_bases}) size := by congr', 
    
  rw h3, 
  sorry 

  
end
-/



--lemma max_two_partitionable_is_union_two_bases (M₁ M₂ : rankfun U) :
--  ∃ X : set U, size X = π M₁ M₂ ∧ is_union_two_indep M₁ M₂ X 




/-
lemma pi_nu (M₁ M₂ : rankfun U) : 
  π M₁ M₂ = ν M₁ (dual M₂) - M₂.r univ := 
begin
  sorry, 
end 
-/



 

/-
lemma intersection_max_inter_bases (M₁ M₂ : rankfun U): 
  ν M₁ M₂ = 
    max_val_over 
      (is_basis M₁)
      (exists_basis M₁) 
      (
        λ B₁, max_val_over (is_basis M₂)
                           (exists_basis M₂)
                           (λ B₂, size (B₁ ∩ B₂))
      ) := 
begin
  set I := max_common_ind M₁ M₂ with hI, 

  sorry, 
end



-/

end union 




end ftype 
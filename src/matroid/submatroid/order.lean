import prelim.embed prelim.minmax set_tactic.solver
import matroid.rankfun matroid.dual matroid.simple 

open_locale classical 
noncomputable theory

open matroid set list 

variables {U : Type}[fintype U]{N M : matroid U}

section weak_image 
/- M is a weak image N if the rank in N is upper-bounded by the rank in M -/
def is_weak_image (N M : matroid U):= 
  ∀ X, N.r X ≤ M.r X 

instance weak_image_le : has_le (matroid U) := 
⟨λ N M, is_weak_image N M⟩

lemma weak_image_r_set (h : N ≤ M)(X : set U):
  N.r X ≤ M.r X :=
h X

lemma weak_image_iff_indep:
  N ≤ M ↔ ∀ X, N.is_indep X → M.is_indep X := 
begin
  simp_rw indep_iff_r, 
  refine ⟨λ h, λ X hX, le_antisymm (M.rank_le_size _) _, λ h, λ Y, _⟩,  
  {  rw ←hX, apply h}, 
  rcases exists_basis_of N Y with ⟨BN,⟨hN1, ⟨hN2, hN3⟩⟩⟩, 
  exact le_trans (by rw [h _ hN2, ←hN3, hN2]) (M.rank_mono hN1),  
end

lemma indep_of_weak_image_indep (h : N ≤ M){I : set U}(hI : N.is_indep I):
  M.is_indep I := 
weak_image_iff_indep.mp h I hI


lemma weak_image_iff_dep:
  N ≤ M ↔ ∀ X, M.is_dep X → N.is_dep X := 
by simp_rw [weak_image_iff_indep, indep_iff_not_dep, not_imp_not]

lemma weak_image_iff_cct:
  N ≤ M ↔ ∀ C, M.is_circuit C → ∃ C', N.is_circuit C' ∧ C' ⊆ C := 
begin
  simp_rw [weak_image_iff_dep, dep_iff_contains_circuit],  
  refine ⟨λ h, λ C hC, _, λ h, λ X hX, _⟩, 
  {  apply h, exact ⟨C,hC,subset_refl _⟩,},
  rcases hX with ⟨C, ⟨h', h''⟩⟩, 
  rcases h C h' with ⟨C',h1,h2⟩, 
  exact ⟨C', h1, subset.trans h2 h''⟩, 
end

lemma weak_image_tfae: 
  tfae
[ N ≤ M, 
  ∀ X, N.r X ≤ M.r X, 
  ∀ X, N.is_indep X → M.is_indep X, 
  ∀ X, M.is_dep X → N.is_dep X,
  ∀ C, M.is_circuit C → ∃ C', N.is_circuit C' ∧ C' ⊆ C] :=
begin
  tfae_have : 1 ↔ 2, unfold has_le.le is_weak_image, 
  tfae_have : 1 ↔ 3, apply weak_image_iff_indep, 
  tfae_have : 1 ↔ 4, apply weak_image_iff_dep,  
  tfae_have : 1 ↔ 5, apply weak_image_iff_cct, 
  tfae_finish, 
end
/- that was fun! -/

lemma weak_image_rank_zero_of_rank_zero (h : N ≤ M){X : set U}(hX : M.r X = 0):
  N.r X = 0 :=
by {apply rank_eq_zero_of_le_zero, rw ←hX, apply h}

lemma weak_image_loop_of_loop (h : N ≤ M){e : U}(he : M.is_loop e):
  N.is_loop e :=
weak_image_rank_zero_of_rank_zero h he 

lemma nonloop_of_weak_image_nonloop (h : N ≤ M){e : U}(he : N.is_nonloop e):
  M.is_nonloop e :=
by {rw is_nonloop at *, linarith [rank_single_ub M e, h {e}], }

lemma loops_weak_image (h : N ≤ M): 
  loops M ⊆ loops N := 
by {intro e, simp only [←loop_iff_elem_loops], apply weak_image_loop_of_loop h }

end weak_image

section quotient 
/-- a quotient of M is a matroid N for which rank differences of nested pairs in N are at most
the corresponding rank differences in M. This is equivalent to the existence of a matroid P for 
which M is a deletion of P and N is a contraction of P, but we do not show this equivalence here.-/
def is_quotient (N M : matroid U) := 
  ∀ X Y, X ⊆ Y → N.r Y - N.r X ≤ M.r Y - M.r X

reserve infixl ` ≼ `:75
infix ` ≼ ` :=  is_quotient 

lemma quotient_iff_r : 
  N ≼ M ↔ ∀ X Y, X ⊆ Y → N.r Y - N.r X ≤ M.r Y - M.r X := 
by rw is_quotient

lemma rank_diff_of_quotient (hNM : N ≼ M) {X Y : set U}(h : X ⊆ Y):
  N.r Y - N.r X ≤ M.r Y - M.r X :=
hNM _ _ h 

lemma weak_image_of_quotient (h : N ≼ M) :
   N ≤ M :=
λ X, by {convert h ∅ X (empty_subset _); simp, }

lemma quotient_of_cl (h : ∀ X, M.cl X ⊆ N.cl X) : 
   N ≼ M := 
begin
  set P : set U × set U → Prop :=  
  (λ p, p.1 ⊆ p.2 → N.r p.2 - N.r p.1 ≤ M.r p.2 - M.r p.1 ) with hP, 
  suffices : ∀ p, P p, exact λ X Y, this ⟨X,Y⟩, 
  apply nonneg_int_strong_induction_param P (λ p, size (p.2 \ p.1)), 
  { rintros ⟨X,Y⟩, apply size_nonneg}, 
  { rintros ⟨X,Y⟩ hs hXY, dsimp only at *, 
    rw [size_zero_iff_empty, diff_empty_iff_subset] at hs, 
    rw [subset.antisymm hXY hs, sub_self, sub_self],  }, 
  rintros ⟨X,Y⟩ h_size h' hXY, dsimp only at *,   
  cases size_pos_has_mem h_size with e he,
  specialize h' ⟨X, Y \ {e}⟩ _ _, swap, 
  { dsimp only, rw [diff_right_comm, remove_single_size he], linarith}, swap,
  { dsimp only [diff_eq] at he ⊢, 
    apply subset_inter hXY, 
    rw subset_compl_singleton_iff, 
    rw [mem_inter_iff, mem_compl_iff] at he, 
    exact he.2,   },
  rw [diff_eq,mem_inter_iff, mem_compl_iff] at he, 
  dsimp only at h', 
  suffices : N.r Y - N.r (Y \ {e}) ≤ M.r Y - M.r (Y \ {e}), by linarith, 
  by_cases hY : M.r Y = M.r (Y \ {e}), swap, 
  { rw [rank_eq_sub_one_of_ne_remove _ _ _ hY], linarith [rank_remove_single_lb N Y e]  },
  rw [hY, sub_self], 
  rw [eq_comm, rank_removal_iff_closure _ _ he.1]  at hY, 
  have hN := elem_of_subset (h _) hY, rw [←rank_removal_iff_closure _ _ he.1] at hN, 
  linarith, 
end

lemma quotient_iff_dual_quotient : 
  N ≼ M ↔ M.dual ≼ N.dual :=
begin
  suffices h' : ∀ (N M : matroid U), N ≼ M → M.dual ≼ N.dual, 
  exact ⟨λ h, h' _ _ h, λ h, by {convert h' _ _ h; rw dual_dual, }⟩, 
  intros N M h X Y hXY, 
  simp_rw [dual_r], 
  rw compl_subset_compl.symm at hXY, 
  linarith [h _ _ hXY],
end

lemma quotient_tfae : 
  tfae 
[N ≼ M,
 ∀ F, N.is_flat F → M.is_flat F, 
 ∀ X Y, X ⊆ Y → N.r Y - N.r X ≤ M.r Y - M.r X,
 ∀ X, M.cl X ⊆ N.cl X,
 M.dual ≼ N.dual] :=
begin
  tfae_have : 1 ↔ 3, unfold is_quotient,
  tfae_have : 3 → 2, 
  {exact λ h, λ F hF Y hFY, by linarith [hF _ hFY, h _ _ hFY.1],}, 
  tfae_have : 2 → 4, 
  {exact λ h X, subset_flat X _ (subset_cl N X) (h _ (N.cl_is_flat X))}, 
  tfae_have: 4 → 1, apply quotient_of_cl, 
  tfae_have : 1 ↔ 5, apply quotient_iff_dual_quotient, 
  tfae_finish, 
end

lemma quotient_iff_flat :
  N ≼ M ↔ ∀ F, N.is_flat F → M.is_flat F :=
by apply @tfae.out _ quotient_tfae 0 1 

lemma flat_of_quotient_flat (h : N ≼ M){F : set U}(hF : N.is_flat F):
  M.is_flat F :=
(quotient_iff_flat.mp h) F hF 

lemma indep_of_quotient_indep (h : N ≼ M){I : set U}(hI : N.is_indep I):
  M.is_indep I := 
indep_of_weak_image_indep (weak_image_of_quotient h) hI 

lemma quotient_iff_cl :
  N ≼ M ↔ ∀ X, M.cl X ⊆ N.cl X :=
by apply @tfae.out _ quotient_tfae 0 3 

lemma quotient_rank_zero_of_rank_zero (h : N ≼ M){X : set U}(hX : M.r X = 0):
  N.r X = 0 :=
weak_image_rank_zero_of_rank_zero (weak_image_of_quotient h) hX 

lemma quotient_loop_of_loop (h : N ≼ M){e : U}(he : M.is_loop e):
  N.is_loop e :=
weak_image_loop_of_loop (weak_image_of_quotient h) he

lemma nonloop_of_quotient_nonloop (h : N ≼ M){e : U}(he : N.is_nonloop e):
  M.is_nonloop e :=
nonloop_of_weak_image_nonloop (weak_image_of_quotient h) he

lemma loops_quotient (h : N ≼ M): 
  loops M ⊆ loops N := 
loops_weak_image (weak_image_of_quotient h)

lemma eq_of_eq_rank_quotient (h : N ≼ M)(hr : N.r univ = M.r univ):
  N = M :=
begin
  ext X, by_contra hn,
  /- take a maximal set on which the ranks of N and M differ. -/
  rcases maximal_example_aug (λ X, ¬N.r X = M.r X) hn with ⟨Y, hXY, h',h''⟩, 
  dsimp only at h'', simp_rw [not_not] at h'', clear hXY hn X, 
  have hY : Y ≠ univ := λ hY, by {rw ←hY at hr, exact h' hr },
  cases ne_univ_iff_has_nonmem.mp hY with e heY,  
  specialize h'' e heY, 
  have hle := weak_image_of_quotient h, 
  rw quotient_iff_cl at h, 
  by_cases hM : e ∈ M.cl Y, 
  { rw [(mem_cl_iff_r.mp hM)] at h'',
    rw [←h'', eq_comm, ←mem_cl_iff_r] at h', 
    exact h' (mem_of_mem_of_subset hM (h _))}, 
  rw nonmem_cl_iff_r at hM,  
  linarith [int.le_sub_one_of_le_of_ne (hle _) h', rank_augment_single_ub N Y e], 
end

end quotient 

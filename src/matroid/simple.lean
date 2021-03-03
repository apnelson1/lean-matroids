import prelim.collections prelim.embed prelim.size prelim.induction prelim.minmax
import .parallel 

noncomputable theory 
open_locale classical 

open set 
namespace matroid 

variables {U V : Type}[fintype U][fintype V]

section simple 

def is_loopless (M : matroid U) := 
  ∀ X, size X ≤ 1 → M.is_indep X 

def is_simple (M : matroid U) :=
  ∀ X, size X ≤ 2 → M.is_indep X 

lemma loopless_iff_all_nonloops {M : matroid U} :
  M.is_loopless ↔ ∀ e, M.is_nonloop e :=
begin
  simp_rw [nonloop_iff_r, is_loopless, size_le_one_iff_empty_or_singleton, indep_iff_r],
  refine ⟨λ h, λ e, _, λ h, λ X hX, _⟩, 
  { rw ←size_singleton e, apply h, right, exact ⟨e,rfl⟩},
  rcases hX with (rfl | ⟨e,rfl⟩), simp, 
  rw [size_singleton, h e], 
end 

lemma nonloop_of_loopless {M : matroid U}(e : U)(h : M.is_loopless):
  M.is_nonloop e := 
by {rw loopless_iff_all_nonloops at h, tauto, }

lemma rank_single_of_loopless {M : matroid U}(h : M.is_loopless)(e : U): 
  M.r {e} = 1 := 
by {rw [←nonloop_iff_r], apply nonloop_of_loopless e h,  }


lemma simple_iff_no_loops_or_parallel_pairs {M : matroid U}:
  M.is_simple ↔ M.is_loopless ∧ ∀ (e f : U), M.parallel e f → e = f :=
begin
  refine ⟨λ h, ⟨λ X hX, h X (by linarith),λ e f hef, by_contra (λ hn, _)⟩, λ h, λ X hX, _⟩, 
  { rcases hef with ⟨he,hf,hef⟩, 
    have hef' := size_union_distinct_singles hn, 
    linarith [r_indep (h {e,f} (by linarith))],},
  rcases int.nonneg_le_two_iff (size_nonneg X) hX with (h0 | h1 | h2), 
  { rw size_zero_iff_empty at h0, rw h0, apply M.empty_indep, },
  { rcases size_one_iff_eq_singleton.mp h1 with ⟨e,rfl⟩, 
    exact nonloop_iff_indep.mp (nonloop_of_loopless _ h.1), },
  rcases size_eq_two_iff_pair.mp h2 with ⟨e,f,hef,rfl⟩, 
  by_contra hn, 
  suffices heq : e = f, rw [heq, pair_eq_singleton, size_singleton] at h2, norm_num at h2, 
  apply h.2 e f, rw parallel_iff_dep _ _, right, 
    rwa [←dep_iff_not_indep] at hn, 
  all_goals {apply nonloop_of_loopless, exact h.1},
end

/- The simple matroid associated with M (simplification of M). Its elements are the parallel classes of M, and 
the rank of a set of parallel classes is just the rank in M of their union. -/
def si (M : matroid U): matroid (M.parallel_class) := 
{ r := λ X, M.r (union_parallel_classes X),
  R0 := λ X, by {apply M.R0 },
  R1 := λ X, begin 
    let f := choose_transversal M, 
    simp only [rank_img_transversal f, ←size_img_transversal f],
    apply M.R1, 
  end,
  R2 := λ X Y hXY, begin
    dsimp only, 
    convert M.rank_mono (inter_subset_right _ _), 
    rw [←(subset_iff_inter_eq_left.mp hXY), inter_union_parallel_classes],
  end,
  R3 := λ X Y, begin
    dsimp only, 
    convert M.rank_submod _ _, apply union_union_parallel_classes,
    apply inter_union_parallel_classes, 
  end }

lemma si_r (M : matroid U) (S : set M.parallel_class): 
  M.si.r S = M.r (union_parallel_classes S) := 
rfl 

/- it is more convenient to think of the simplification rank in terms of a fixed transversal of the parallel classes-/
lemma si_r_transversal {M : matroid U}(f : M.transversal)(S : set M.parallel_class): 
  (si M).r S = M.r (f '' S) := 
by rw [←rank_img_transversal, si_r]

lemma si_is_loopless (M : matroid U): 
  (si M).is_loopless := 
let f := M.choose_transversal in 
  loopless_iff_all_nonloops.mpr (λ S, by 
  { rw [nonloop_iff_r, si_r_transversal f, image_singleton, ←nonloop_iff_r], apply nonloop_of_range_transversal,  }) 


lemma si_is_simple (M : matroid U): 
  (si M).is_simple :=
begin
  let f := M.choose_transversal, 
  refine simple_iff_no_loops_or_parallel_pairs.mpr ⟨(M.si_is_loopless), λ P Q hPQ, _⟩,  
  apply eq_of_parallel_range_transversal f, 
  obtain ⟨-,-,hr⟩ := hPQ, 
  refine ⟨_,_,_⟩, all_goals {try {apply nonloop_of_range_transversal}}, 
  rwa [si_r_transversal f, image_pair] at hr, 
end

lemma si_is_irestr (M : matroid U): 
  (si M).is_irestr_of M :=
begin
  rw irestr_of_iff_exists_map, 
  let f := choose_transversal M, 
  exact ⟨⟨f, transversal_inj f⟩, λ S, by {rw [si_r_transversal f], refl}⟩, 
end

end simple 

section simple_minor


/-- If N is loopless and is isomorphic to a minor of a pminor of M, then N is isomorphic 
to a minor of M.  -/
lemma iminor_of_iminor_of_pminor {N : matroid V}{M' M: matroid U}(hN : N.is_loopless)
(hNM' : N.is_iminor_of M')(hM'M : M'.is_pminor_of M):
N.is_iminor_of M :=
begin
  obtain ⟨φ,C, hrange, hr, hCi, hCr⟩ := iminor_of_iff_exists_good_C.mp hNM', 
  obtain ⟨C',D',hC'D', h⟩ := pminor_iff_exists_pr_lp_disjoint.mp hM'M, substI h, 
  clear hM'M hNM', 
  
  have hrange' : range φ ∩ (C' ∪ D') = ∅, 
  { by_contra hn, 
    obtain ⟨e,he⟩ := ne_empty_iff_has_mem.mp hn, clear hn,
    obtain ⟨heφ, heC⟩ := ((mem_inter_iff _ _ _).mp he), clear he, 
    obtain ⟨f,rfl⟩ := mem_range.mp heφ, clear heφ, 
    specialize hr {f}, 
    rw [rank_single_of_loopless hN, image_singleton] at hr,
    rw [union_comm, rank_eq_rank_union_rank_zero C _, sub_self] at hr, exact one_ne_zero hr, 
    apply rank_zero_of_subset_rank_zero (singleton_subset_iff.mpr heC),
    apply rank_zero_of_pr_lp, },
  have hCC'D' : C ∩ (C' ∪ D') = ∅, 
  { rw [←size_zero_iff_empty, 
        ←rank_zero_of_inter_rank_zero C (rank_zero_of_pr_lp M C' D'),
        ←r_indep (inter_indep_of_indep_left _ (C' ∪ D') hCi)], },
  
  refine iminor_of_iff_exists_embedding.mpr ⟨φ, C ∪ C', _, λ X, _⟩, 
  {rw disjoint_iff_subset_compl at *, 
   refine subset.trans (subset_inter hrange hrange') _, 
   intros x, simp only [and_imp, compl_union, mem_inter_eq, mem_compl_eq], tauto},
  
  have h' : ∀ Z: set U, Z ∩ (C' ∪ D') = ∅ → D' ∩ Z = ∅, 
  { intros Z hZ, rw inter_comm, apply disjoint_of_subset_right' (subset_union_right C' D') hZ, }, 

  rw [hr X, loopify_rank_of_disjoint (M ⟋ C') (h' _ hCC'D'), ←union_assoc,  
      loopify_rank_of_disjoint (M ⟋ C'), project_r, project_r], ring, 

  rw [inter_distrib_left, h' _ hCC'D', disjoint_of_subset_right' _ (h' _ hrange'), union_self], 
  apply image_subset_range,  
end

lemma iminor_iff_iminor_si {N : matroid V}{M : matroid U}(hN : N.is_simple):
  N.is_iminor_of M ↔ N.is_iminor_of (si M) :=
begin
  sorry, 
end

end simple_minor 
end matroid 


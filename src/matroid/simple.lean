import prelim.collections prelim.embed prelim.size prelim.induction prelim.minmax
import .parallel 

noncomputable theory 
open_locale classical 

open set 
namespace matroid 

variables {U V : Type}[nonempty (fintype U)][fintype V]

section simple 

def is_loopless_set (M : matroid U)(S : set U) :=
  ∀ X ⊆ S, size X ≤ 1 → M.is_indep X

def is_loopless (M : matroid U) := 
  is_loopless_set M univ 

lemma loopless_iff_univ_loopless {M : matroid U}: 
  is_loopless M ↔ is_loopless_set M univ := 
iff.rfl 

def is_simple_set (M : matroid U)(S : set U) :=
  ∀ X ⊆ S, size X ≤ 2 → M.is_indep X 

lemma simple_of_subset_simple {M : matroid U}{S T : set U}(hT : M.is_simple_set T)(hST : S ⊆ T):
  M.is_simple_set S := 
λ X hX, hT X (subset.trans hX hST)

def is_simple (M : matroid U) :=
  is_simple_set M univ 

lemma simple_iff_univ_simple {M : matroid U}: 
  is_simple M ↔ is_simple_set M univ := 
iff.rfl 

def simple_set (M : matroid U) := {X : set U // M.is_simple_set X} 

instance simple_set_nonempty {M : matroid U}: nonempty M.simple_set := 
  ⟨⟨∅, λ X hX _, by {rw eq_empty_of_subset_empty hX, apply empty_indep, }⟩⟩ 

instance simple_set_fintype {M : matroid U}: fintype M.simple_set := 
  by {unfold simple_set, apply_instance,}

def simple_subset_of (M : matroid U)(S : set U) := {X : set U // M.is_simple_set X ∧ X ⊆ S} 

instance simple_subset_nonempty {M : matroid U}{S : set U}: nonempty (M.simple_subset_of S) := 
  ⟨⟨∅, ⟨λ X hX _, by {rw eq_empty_of_subset_empty hX, apply empty_indep, }, empty_subset _⟩ ⟩⟩ 

instance simple_subset_fintype {M : matroid U}{S : set U}: fintype (M.simple_subset_of S) := 
  by {unfold simple_subset_of, apply_instance,}


lemma loopless_set_iff_all_nonloops {M : matroid U}{S : set U}: 
  M.is_loopless_set S ↔ ∀ e ∈ S, M.is_nonloop e :=
begin
  simp_rw [nonloop_iff_r, is_loopless_set, size_le_one_iff_empty_or_singleton, indep_iff_r],
  refine ⟨λ h, λ e he ,_  , λ h, λ X hX h', _⟩, 
  {rw ← size_singleton e, exact h _ (singleton_subset_iff.mpr he) (or.inr ⟨e, rfl⟩)},  
  rcases h' with (rfl | ⟨e,rfl⟩), simp, 
  rw [size_singleton, h e (singleton_subset_iff.mp hX)],  
end

lemma loopless_iff_all_nonloops {M : matroid U} :
  M.is_loopless ↔ ∀ e, M.is_nonloop e :=
by {rw [loopless_iff_univ_loopless, loopless_set_iff_all_nonloops], tauto}

lemma nonloop_of_mem_loopless_set {M : matroid U}{S : set U}{e : U}
(h : M.is_loopless_set S)(he : e ∈ S):
  M.is_nonloop e := 
by {rw loopless_set_iff_all_nonloops at h, tauto, }

lemma exists_loop_of_not_loopless_set {M : matroid U}{S : set U}(hS : ¬M.is_loopless_set S): 
  ∃ e ∈ S, M.is_loop e :=
begin
  by_contra hn, 
  simp_rw [loopless_set_iff_all_nonloops, nonloop_iff_not_loop] at hS, 
  push_neg at hS hn,
  obtain ⟨e,⟨he,he'⟩⟩ := hS, 
  exact hn e he he',    
end 

lemma exists_loop_of_not_loopless {M : matroid U}(h : ¬M.is_loopless): 
  ∃ e, M.is_loop e := 
let ⟨e,_,h'⟩ := exists_loop_of_not_loopless_set h in ⟨e,h'⟩ 

lemma nonloop_of_loopless {M : matroid U}(e : U)(h : M.is_loopless):
  M.is_nonloop e := 
by {rw loopless_iff_all_nonloops at h, tauto, }

lemma rank_single_of_loopless {M : matroid U}(h : M.is_loopless)(e : U): 
  M.r {e} = 1 := 
by {rw [←nonloop_iff_r], apply nonloop_of_loopless e h,  }

lemma simple_set_iff_no_loops_or_parallel_pairs {M : matroid U}{S : set U}:
  M.is_simple_set S ↔ M.is_loopless_set S ∧ ∀ (e f ∈ S), M.parallel e f → e = f := 
begin
  refine ⟨λ h, ⟨λ X hXS hX, h X hXS (by linarith [hX]),λ e f he hf hef, by_contra (λ hn, _)⟩, λ h, λ X hXS hX, _⟩, 
  { rcases hef with ⟨he,hf,hef⟩, 
    have hef' := size_union_distinct_singles hn, 
    linarith [r_indep (h {e,f} (λ x, by {simp, rintros (rfl | rfl); assumption, }) (by linarith))]},
  rcases int.nonneg_le_two_iff (size_nonneg X) hX with (h0 | h1 | h2), 
  { rw size_zero_iff_empty at h0, rw h0, apply M.empty_indep, },
  { obtain ⟨e,rfl⟩ := size_one_iff_eq_singleton.mp h1, 
    rw singleton_subset_iff at hXS, 
    exact nonloop_iff_indep.mp (nonloop_of_mem_loopless_set h.1 hXS), },
  rcases size_eq_two_iff_pair.mp h2 with ⟨e,f,hef,rfl⟩, 
  by_contra hn, 
  cases pair_subset_iff.mp hXS with he hf, 
  
  suffices heq : e = f, rw [heq, pair_eq_singleton, size_singleton] at h2, norm_num at h2, 
  apply h.2 e f he hf, rw parallel_iff_dep _ _, right, 
    rwa [←dep_iff_not_indep] at hn, 
  all_goals {apply nonloop_of_mem_loopless_set h.1, assumption,  },
end


lemma simple_iff_no_loops_or_parallel_pairs {M : matroid U}:
  M.is_simple ↔ M.is_loopless ∧ ∀ (e f : U), M.parallel e f → e = f :=
by {rw [simple_iff_univ_simple, simple_set_iff_no_loops_or_parallel_pairs], tidy, }  


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


/- TODO - a simple matroid is a minor of M iff if it is a minor of si M . 

lemma iminor_iff_iminor_si {N : matroid V}{M : matroid U}(hN : N.is_simple):
  N.is_iminor_of M ↔ N.is_iminor_of (si M) :=
begin
  sorry, 
end -/ 


end simple_minor 
end matroid 



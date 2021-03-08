import prelim.collections prelim.embed prelim.size prelim.induction prelim.minmax
import .parallel .simple matroid.constructions.partition 

noncomputable theory 
open_locale classical 

open set matroid 

variables {U V : Type}[fintype U][fintype V]

/-- the 'parallel class matroid' on U in which the rank of a set is the number of parallel classes of M 
that it intersects-/
def pc_matroid (M : matroid U) := 
  partition.M M.parallel_cl M.rank_nonneg 

lemma pc_matroid_def (M : matroid U):
  pc_matroid M = partition.M M.parallel_cl M.rank_nonneg :=
rfl 

/-- the number of parallel classes that intersect a set X-/
def matroid.ε (M : matroid U)(X : set U) := (pc_matroid M).r X 

lemma ε_eq_pc_matroid_r (M : matroid U)(X : set U): 
  M.ε X = (pc_matroid M).r X := 
rfl 

lemma pc_matroid_indep_iff (M : matroid U)(X : set U): 
  (pc_matroid M).is_indep X ↔ M.is_simple_set X  := 
begin
  rw [pc_matroid_def],
end
/-
lemma pc_matroid_indep_iff (M : matroid U)(X : set U): 
  (pc_matroid M).is_indep X ↔ M.is_simple_set X  := 
begin
  rw [pc_matroid, partition.indep_iff, simple_set_iff_no_loops_or_parallel_pairs],
  refine ⟨λ h, ⟨by_contra (λ hn, _), λ e f he hf hef, (by_contra (λ hn ,_))⟩, λ h P, _⟩,
  { obtain ⟨e,heX, he⟩ := exists_loop_of_not_loopless_set hn, 
    specialize h (M.parallel_cl e), 
    rw [parallel_cl_loop_empty he, rank_empty, size_le_zero_iff_has_no_mem] at h, 
    exact h ⟨e, by {simp [heX, parallel_cl_loop_empty he], }⟩,},
  { specialize h (M.parallel_cl e), 
    rw [rank_parallel_cl (hef.1), size_le_one_iff_mem_unique] at h,
    refine hn (h _ _ _ _), simpa using he,
    simp only [mem_sep_eq], 
    exact ⟨hf, (parallel_cl_eq_of_parallel hef).symm⟩},
  by_cases hP : ∃ x ∈ X, M.parallel_cl x = P, swap, 
  { refine le_trans _ (M.rank_nonneg P),
    rw [size_le_zero_iff_eq_empty, sep_in_eq_empty_iff],
    exact λ x hx hP', hP (⟨x,hx, hP'⟩)}, 
  obtain ⟨e, heX, rfl⟩ := hP, 
  rcases loop_or_nonloop M e with (h0 | h1), 
  { rw [parallel_cl_loop_empty h0, rank_empty, size_le_zero_iff_eq_empty, sep_in_eq_empty_iff], 
    refine λ x hx, ne_empty_iff_nonempty.mpr _, 
    exact parallel_cl_nonempty_of_nonloop (nonloop_of_mem_loopless_set h.1 hx)},
  simp_rw [rank_parallel_cl h1, size_le_one_iff_mem_unique, mem_sep_eq], 
  rintros f f' ⟨hfx, hf⟩ ⟨hf'x, hf'⟩,
  refine h.2 _ _ hfx hf'x (parallel_of_parallel_cl_eq_left _ (by rw [hf, hf'])), 
  exact nonloop_of_mem_loopless_set h.1 hfx, 
end


lemma ε_eq_largest_simple_subset (M : matroid U)(X : set U): 
  M.ε X = max_val (λ (S : M.simple_subset_of X), size S.val) :=
begin
  rw [ε_eq_pc_matroid_r, rank_as_indep], 
  let e : ((pc_matroid M).indep_subset_of X) ≃ (M.simple_subset_of X) := 
  equiv.subtype_equiv_right 
    (λ X, by {rw [← pc_matroid_indep_iff, and_comm], refl, }),
  exact (max_reindex e.to_fun e.surjective (λ X, size X.val)), 
end

lemma ε_eq_size_of_simple_matroid {M : matroid U}(hM : M.is_simple)(X : set U): 
  M.ε X = size X :=
begin
  rw [ε_eq_largest_simple_subset], 
  let X' : M.simple_subset_of X := 
    ⟨X, ⟨simple_of_subset_simple hM (subset_univ _), subset_refl _⟩⟩, 
  exact attained_ub_is_max' _ X' (size X) rfl (λ Y, size_monotone Y.2.2),  
end

lemma ε_eq_size_iff_simple_set {M : matroid U}{X : set U}:
  M.ε X = size X ↔ M.is_simple_set X :=
by rw [ε_eq_pc_matroid_r, ← indep_iff_r, pc_matroid_indep_iff]

lemma ε_eq_size_univ_iff_simple {M : matroid U}:
  M.ε univ = size (univ :set U) ↔ M.is_simple :=
ε_eq_size_iff_simple_set

lemma ε_eq_num_parallel_classes_inter (M : matroid U)(X : set U):
  M.ε X = size {P : M.parallel_class | (X ∩ P).nonempty } :=
begin

  /-rw [ε_eq_pc_matroid_r, pc_matroid, partition.r_eq, type_size_eq, ← fin_sum_one_eq_size], 
  rw ← finset.sum_filter_ne_zero, 
  let f : ↥(finset.filter 
    (λ (x : option M.parallel_class), min (parallel_ub_fn M x) 
    (size (X ∩ parallel_partition_fn M ⁻¹' {x})) ≠ 0) 
    finset.univ) 
    ≃ {P : M.parallel_class // (P.val ∩ X).nonempty} := sorry, -/
  
end

lemma ε_eq_num_points (M : matroid U)(X : set U): 
  M.ε X = type_size {P : M.point // ((P.val \ M.loops) ∩ X).nonempty } :=
begin

end

-/

--def point_partition_matroid (M : mat
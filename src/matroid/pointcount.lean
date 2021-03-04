import prelim.collections prelim.embed prelim.size prelim.induction prelim.minmax
import .parallel .simple .constructions 

noncomputable theory 
open_locale classical 

open set matroid 


variables {U V : Type}[fintype U][fintype V]

/-- sends each nonloop to its parallel class, and each loop to 'none' -/
def parallel_partition_fn (M : matroid U):  U → option (M.parallel_class) := 
  λ e, dite (M.is_nonloop e) (λ he, some (parallel_cl' ⟨e,he⟩)) (λ _, none) 

@[simp] lemma parallel_partition_fn_eq_none_iff {M : matroid U}{e : U}: 
  parallel_partition_fn M e = none ↔ M.is_loop e := 
by {rw [loop_iff_not_nonloop, parallel_partition_fn], dsimp only, split_ifs; tauto,   } 

@[simp] lemma parallel_partition_fn_eq_some_iff {M : matroid U}{e : U}{P : M.parallel_class}: 
  parallel_partition_fn M e = some P ↔ e ∈ (P : set U) := 
begin
  cases P, dsimp only [parallel_partition_fn, parallel_cl', subtype.coe_mk],
  split_ifs with he, 
  { rw [subtype.mk_eq_mk], 
    obtain ⟨f,hf,rfl⟩ := P_property,   
    simp_rw [mem_parallel_cl, parallel_cl, ext_iff, mem_set_of_eq],
    refine ⟨λ h, (h e).mp (parallel_refl_nonloop he), λ h, λ x, (have _ := parallel_symm' h, ⟨_,_⟩)⟩;
    {intro, transitivity; assumption }},
  simp only [false_iff],
  exact λ hn, he (nonloop_of_mem_parallel_class hn P_property), 
end 

/-- sends each parallel class to 1 and 'none' to 0 -/
def parallel_ub_fn (M : matroid U) : option (M.parallel_class) → ℤ  
  | none       := 0
  | (some val) := 1

@[simp] lemma parallel_ub_fn_at_zero (M : matroid U): 
  parallel_ub_fn M none = 0 := rfl 

@[simp] lemma parallel_ub_fn_at_val (M : matroid U)(P : M.parallel_class) : 
  parallel_ub_fn M (some P) = 1 := rfl 

lemma parallel_ub_fn_nonneg (M : matroid U): 
  ∀ x, 0 ≤ parallel_ub_fn M x :=
λ x, by {cases x; simp [parallel_ub_fn, zero_le_one]}

/-- the matroid on U in which the rank of a set is the number of parallel classes of M 
that it intersects-/
def parallel_partition_matroid (M : matroid U) := 
  partition.M (parallel_partition_fn M) (parallel_ub_fn_nonneg M)

/-- the number of parallel classes that intersect a set X-/
def matroid.ε (M : matroid U)(X : set U) := (parallel_partition_matroid M).r X 

lemma ε_eq_pp_matroid_r (M : matroid U)(X : set U): 
  M.ε X = (parallel_partition_matroid M).r X := rfl 

lemma parallel_partition_matroid_indep_iff (M : matroid U)(X : set U): 
  (parallel_partition_matroid M).is_indep X ↔ M.is_simple_set X  := 
begin
  rw [parallel_partition_matroid, partition.indep_iff, simple_set_iff_no_loops_or_parallel_pairs],
  refine ⟨λ h, ⟨by_contra (λ hn, _), λ e f he hf hef, (by_contra (λ hn ,_))⟩, λ h i, _⟩,
  { obtain ⟨e,heX, he⟩ := exists_loop_of_not_loopless_set hn, 
    specialize h none, 
    simp_rw [parallel_ub_fn, size_le_zero_iff_has_no_mem, mem_inter_iff, not_exists, 
    not_and, mem_preimage, mem_singleton_iff, parallel_partition_fn] at h,  
    rw loop_iff_not_nonloop at he, 
    specialize h e heX, split_ifs at h, tauto, },
  { obtain ⟨he',hf',-⟩ := id hef, 
    have hefs:= size_union_distinct_singles hn, 
    set P := (parallel_cl' ⟨e,he'⟩) with hP, 
    specialize h (some P), rw parallel_ub_fn_at_val at h,
    suffices h₀ : (e ∈ parallel_partition_fn M ⁻¹' {some P}) 
                ∧ (f ∈ parallel_partition_fn M ⁻¹' {some P}), 
    linarith [size_monotone (subset_inter (pair_subset_iff.mpr ⟨he,hf⟩) (pair_subset_iff.mpr h₀))],
    simp only [hP, mem_singleton_iff, mem_preimage, parallel_partition_fn_eq_some_iff, parallel_cl', 
    subtype.coe_mk, mem_parallel_cl],
    refine ⟨parallel_refl_nonloop he', parallel_symm' hef⟩},
  cases i with P, 
  { simp_rw [parallel_ub_fn_at_zero, size_le_zero_iff_has_no_mem],
    simp only [not_exists, mem_singleton_iff, mem_inter_eq, not_and, mem_preimage, parallel_partition_fn_eq_none_iff],
    simp_rw ← nonloop_iff_not_loop,   
    exact λ x hx, nonloop_of_mem_loopless_set h.1 hx},
  simp_rw [parallel_ub_fn_at_val, size_le_one_iff_mem_unique, mem_inter_iff, mem_preimage, mem_singleton_iff, 
  parallel_partition_fn_eq_some_iff],
  rintros e f ⟨heX, hei⟩ ⟨hfX, hfi⟩, 
  apply h.2 e f heX hfX, 
  apply parallel_of_mems_parallel_class hei hfi, 
end

lemma ε_eq_largest_simple_subset (M : matroid U)(X : set U): 
  M.ε X = max_val (λ (S : M.simple_subset_of X), size S.val) :=
begin
  rw [ε_eq_pp_matroid_r, rank_as_indep], 
  let e : ((parallel_partition_matroid M).indep_subset_of X) ≃ (M.simple_subset_of X) := 
  equiv.subtype_equiv_right 
    (λ X, by {rw [← parallel_partition_matroid_indep_iff, and_comm], refl, }),
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
by rw [ε_eq_pp_matroid_r, ← indep_iff_r, parallel_partition_matroid_indep_iff]

lemma ε_eq_size_univ_iff_simple {M : matroid U}:
  M.ε univ = size (univ :set U) ↔ M.is_simple :=
ε_eq_size_iff_simple_set



--def point_partition_matroid (M : matroid U) := 

#lint 
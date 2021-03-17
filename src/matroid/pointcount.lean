import prelim.collections prelim.embed prelim.size prelim.induction prelim.minmax
import .parallel .simple matroid.constructions.partition matroid.submatroid.projection

noncomputable theory 
open_locale classical 

open set matroid 

variables {α β : Type*} [fintype α] [fintype β]

/-- the 'parallel class matroid' on α in which the rank of a set is the number of parallel 
classes of M that it intersects-/
def pc_matroid (M : matroid α) := 
  presetoid_matroid.M M.ps 

lemma pc_matroid_def (M : matroid α) :
  pc_matroid M = presetoid_matroid.M M.ps := 
rfl 

/-- the number of parallel classes that intersect a set X. -/
def matroid.ε (M : matroid α) (X : set α) := (pc_matroid M).r X 

lemma ε_eq_pc_matroid_r (M : matroid α) (X : set α) : 
  M.ε X = (pc_matroid M).r X := 
rfl 

lemma pc_matroid_indep_iff (M : matroid α) (X : set α) : 
  (pc_matroid M).is_indep X ↔ M.is_simple_set X  := 
begin
  rw [pc_matroid_def, presetoid_matroid.indep_iff, simple_set_iff_no_loops_or_parallel_pairs,
  ps_kernel_eq_loops, loopless_set_iff_all_nonloops, disjoint_left],

  simp_rw [← nonloop_iff_not_mem_loops, ← parallel_refl_iff_nonloop, ← ps_rel_eq_parallel, 
  size_le_one_iff_mem_unique, mem_inter_iff, presetoid.mem_classes_iff], 

  convert iff.rfl, 
  refine iff_iff_eq.mp ⟨λ h P hP e f he hf, h _ _ he.1 hf.1 _, 
                        λ h e f he hf hef, h (M.ps.cl e) _ e f ⟨he, _⟩ ⟨hf,_⟩ ⟩,  
  { obtain ⟨a, ha, rfl⟩ := hP, exact presetoid.rel_of_mems_cl he.2 hf.2  }, 
  { exact ⟨e, presetoid.rel_self_of_rel hef, rfl⟩ },
  { rw presetoid.mem_cl_iff, exact  presetoid.rel_self_of_rel hef}, 
  rw presetoid.mem_cl_iff, symmetry, assumption, 
end

lemma ε_eq_largest_simple_subset (M : matroid α) (X : set α) : 
  M.ε X = max_val (λ (S : M.simple_subset_of X), size (S : set α)) :=
begin
  rw [ε_eq_pc_matroid_r, rank_as_indep], 
  let e : ((pc_matroid M).indep_subset_of X) ≃ (M.simple_subset_of X) := 
  equiv.subtype_equiv_right 
    (λ X, by {rw [← pc_matroid_indep_iff, and_comm], refl, }),
  exact (max_reindex e.to_fun e.surjective (λ X, size (X : set α))), 
end

lemma ε_univ_eq_largest_simple_set (M : matroid α): 
  M.ε univ = max_val (λ (S : M.simple_set), size (S : set α)) := 
begin
  rw ε_eq_largest_simple_subset, 
  exact max_reindex 
    (λ (S : M.simple_subset_of univ), (⟨S.1, S.2.1⟩ : M.simple_set))
    (λ S, ⟨⟨S.1, S.2, subset_univ _⟩, by simp⟩) 
    (λ S, size (S : set α)), 
end

lemma ε_eq_size_of_simple_matroid {M : matroid α} (hM : M.is_simple) (X : set α) : 
  M.ε X = size X :=
begin
  rw [ε_eq_largest_simple_subset], 
  let X' : M.simple_subset_of X := 
    ⟨X, ⟨simple_of_subset_simple hM (subset_univ _), subset_refl _⟩⟩, 
  exact attained_ub_is_max' _ X' (size X) rfl.le (λ Y, size_monotone Y.2.2),  
end

lemma ε_eq_size_iff_simple_set {M : matroid α} {X : set α} :
  M.ε X = size X ↔ M.is_simple_set X :=
by rw [ε_eq_pc_matroid_r, ← indep_iff_r, pc_matroid_indep_iff]

lemma ε_eq_size_univ_iff_simple {M : matroid α} :
  M.ε univ = size (univ : set α) ↔ M.is_simple :=
ε_eq_size_iff_simple_set


lemma ε_eq_num_parallel_classes_inter (M : matroid α) (X : set α) :
  M.ε X = size {P : M.parallel_class | (X ∩ P).nonempty } :=
begin
  simp_rw [ε_eq_pc_matroid_r, pc_matroid_def, presetoid_matroid.r_eq], 
  exact (size_set_subtype_eq_size_set _ _).symm, 
end

/-- Golfing needed-/
lemma ε_eq_rank_of_rank_le_one {M : matroid α} {X : set α} (h : M.r X ≤ 1):
  M.ε X = M.r X := 
begin
  rw [ε_eq_num_parallel_classes_inter], 
  by_cases hX : M.r X < 1,
  { have hX' : M.r X = 0, linarith [M.rank_nonneg X],
    rw [hX', size_zero_iff_has_no_mem],
    simp only [not_exists, mem_set_of_eq],
    rintros ⟨P,hP⟩, 
    by_contra hn, 
    obtain ⟨e,⟨he₁,he₂⟩⟩ := hn, 
    apply nonloop_iff_not_loop.mp (nonloop_of_mem_parallel_class he₂ hP), 
    apply loop_of_mem_rank_zero he₁ hX'}, 
  have hX' : M.r X = 1 := le_antisymm h (le_of_not_lt hX), 
  rw [hX', size_eq_one_iff_nonempty_unique_mem], 
  obtain ⟨x,hxX, hxl⟩ := contains_nonloop_of_one_le_rank (hX'.symm.le), 
  simp only [mem_set_of_eq],
  refine ⟨⟨⟨M.parallel_cl x, parallel_cl_is_parallel_class hxl⟩, ⟨x,hxX,_⟩⟩, λ P P' hP hP', _⟩,   
  { rw [subtype.coe_mk, mem_parallel_cl], exact parallel_refl_of_nonloop hxl }, 
  rcases P with ⟨P,hPp⟩, rcases P' with ⟨P', hPp'⟩,  
  obtain ⟨e, he, rfl⟩ := rep_parallel_class hPp, 
  obtain ⟨e', he', rfl⟩ := rep_parallel_class hPp', 
  obtain ⟨⟨x,⟨hx,hxp⟩⟩,⟨x',⟨hx',hxp'⟩⟩⟩ := ⟨hP,hP'⟩, 
  rw [subtype.mk_eq_mk], 
  apply parallel_cl_eq_of_parallel, 
  rw [subtype.coe_mk, mem_parallel_cl] at hxp hxp', 
  have := parallel_of_rank_le_one hxp.nonloop_left hxp'.nonloop_left _, 
  { exact (hxp.symm.trans this).trans hxp',  },
  rw ← hX', apply rank_mono, 
  intros a ha, 
  simp only [mem_singleton_iff, mem_insert_iff] at ha, 
  rcases ha with (rfl | rfl); tauto,   
end
  

lemma ε_eq_ε_inter_nonloops {M : matroid α} {X : set α}:
  M.ε X = M.ε (X ∩ M.nonloops) := 
begin
  rw [nonloops_eq_compl_loops, ← diff_eq], 
  convert (rank_eq_rank_diff_rank_zero X _).symm, 
  rw rank_zero_iff_subset_loops, 
  intros e he, 
  rw [← loop_iff_mem_loops, loop_iff_r, ← ε_eq_pc_matroid_r, ε_eq_rank_of_rank_le_one],
  { rwa [← loop_iff_r, loop_iff_mem_loops],}, 
  
  exact rank_single_ub M e, 
  -- What the hell? VVV 
  recover, apply_instance, 
end

lemma ε_eq_num_points_inter (M : matroid α) (X : set α) : 
  M.ε X = size {P : M.point | ((P.val \ M.loops) ∩ X).nonempty } :=
begin
  rw ε_eq_num_parallel_classes_inter, 
  convert (size_image_inj M.parallel_class_point_equiv.injective _).symm, 
  ext P, cases P with P hP, 
  simp only [mem_set_of_eq, subtype.val_eq_coe],  
  split,
  { rintros ⟨x,hx⟩, 
    rw [mem_inter_iff, mem_diff, ← nonloop_iff_not_mem_loops] at hx,
    refine ⟨parallel_class_of x hx.1.2, ⟨⟨x,mem_inter hx.2 _⟩,_⟩⟩, 
    { exact mem_parallel_class_of hx.1.2,},
    refine subtype.mk_eq_mk.mpr _, 
    simp only [coe_parallel_class_of, subtype.val_eq_coe, ← point_eq_cl_mem hP hx.1.2 hx.1.1], 
    rw cl_eq_parallel_cl_union_loops,},
  simp only [and_imp, exists_imp_distrib], 
  rintros ⟨Q,hQ⟩ ⟨x, hx⟩ hxQ,
  simp only [subtype.mk_eq_mk, parallel_class_point_equiv_apply] at hxQ,  
  subst hxQ, 
  refine ⟨x, _⟩,
  simp only [mem_union, mem_inter_iff, mem_diff, 
  subtype.coe_mk, ← nonloop_iff_not_mem_loops] at ⊢ hx, 
  have := nonloop_of_mem_parallel_class hx.2 hQ, tauto, 
end

lemma ε_univ_eq_num_points (M : matroid α):
  M.ε univ = type_size M.point :=
begin
  simp only [ε_eq_num_points_inter M univ, point, type_size_eq], 
  congr', ext, 
  simp only [inter_univ, iff_true, subtype.val_eq_coe], 
  
end

/- This should be changed to being stated in terms of M ⟍ {f} rather than M ⟍ {e}  to be consistent
with other lemmas -/
lemma ε_loopify_parallel (M : matroid α) {e f : α} (hef : e ≠ f) (hpara : M.parallel e f) : 
  (M ⟍ {e}).ε univ = M.ε univ :=
begin
  rw eq_comm, repeat {rw ε_univ_eq_largest_simple_set}, 
  obtain ⟨⟨S,hS⟩,  hS', hS''⟩ := max_spec (λ (S : M.simple_set), size (S : set α)), 
  rw [← hS', eq_comm], 
  dsimp only [subtype.coe_mk],
  by_cases he : e ∈ S,  
  { have hf : f ∉ S, from λ hf, 
    by {rw simple_set_iff_no_loops_or_parallel_pairs at hS, exact hef (hS.2 _ _ he hf hpara)}, 
    set S' := (S \ {e}) ∪ {f} with hS'_def, 
    have hS' : (M ⟍ {e}).is_simple_set S', 
    { rw [loopify_simple_iff_simple_disjoint, disjoint_singleton_right, hS'_def],
      refine ⟨simple_set_exchange hS he hpara, λ he, _⟩,  
      rw [mem_union, mem_diff_iff, mem_singleton_iff, mem_singleton_iff] at he, tauto},
    refine attained_ub_is_max' _ ⟨S', hS'⟩ _ _ _, 
    { rw [subtype.coe_mk, hS'_def, size_remove_union_singleton he hf]}, 
    rintros ⟨S₀, hS₀⟩, 
    rw loopify_simple_iff_simple_disjoint at hS₀, 
    exact hS'' ⟨S₀, hS₀.1⟩}, 
  refine attained_ub_is_max' _ ⟨S, _⟩ _ (le_of_eq rfl) _, 
  { exact loopify_simple_iff_simple_disjoint.mpr ⟨hS, by rwa disjoint_singleton_right⟩}, 
  rintros ⟨S₀, hS₀⟩, 
  rw loopify_simple_iff_simple_disjoint at hS₀, 
  exact hS'' ⟨S₀, hS₀.1⟩, 
end
 
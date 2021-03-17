import finsum.fin_api 
import prelim.collections prelim.embed prelim.size prelim.induction prelim.minmax
import .parallel .simple matroid.constructions.partition matroid.submatroid.projection

noncomputable theory 
open_locale classical big_operators 

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

lemma r_le_ε (M : matroid α) (X : set α) : 
  M.r X ≤ M.ε X := 
begin
  rw ε_eq_largest_simple_subset,  
  obtain ⟨⟨Y, hYX, hYs⟩, hY', hY''⟩ := max_spec (λ (S : M.simple_subset_of X), size (S : set α)), 
  obtain ⟨B, hB ⟩ := M.exists_basis_of X, 
  rw [← hY', ← hB.size_eq_r],  
  convert hY'' ⟨B, ⟨simple_of_indep hB.indep, hB.is_subset_of⟩⟩, 
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

lemma ε_eq_r_of_r_le_one {M : matroid α} {X : set α} (h : M.r X ≤ 1): 
  M.ε X = M.r X :=
begin
  refine le_antisymm _ (r_le_ε _ _), 
  rw [ε_eq_num_parallel_classes_inter],
  by_cases hX : M.r X < 1,
  { have hX' : M.r X = 0, linarith [M.rank_nonneg X],
    rw [hX', size_le_zero_iff_has_no_mem],
    simp only [not_exists, mem_set_of_eq],
    rintros ⟨P,hP⟩, 
    by_contra hn, 
    obtain ⟨e,⟨he₁,he₂⟩⟩ := hn, 
    apply nonloop_iff_not_loop.mp (nonloop_of_mem_parallel_class he₂ hP), 
    apply loop_of_mem_rank_zero he₁ hX'}, 

  have hX' : M.r X = 1 := le_antisymm h (le_of_not_lt hX), 
  rw [hX', size_le_one_iff_mem_unique], 
  refine λ P P' hP hP', _, 
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

lemma ε_eq_r_of_ε_le_one {M : matroid α} {X : set α} (h : M.ε X ≤ 1):
  M.ε X = M.r X := 
ε_eq_r_of_r_le_one (le_trans (r_le_ε _ _) h)

lemma ε_eq_ε_inter_nonloops {M : matroid α} {X : set α}:
  M.ε X = M.ε (X ∩ M.nonloops) := 
begin
  rw [nonloops_eq_compl_loops, ← diff_eq], 
  convert (rank_eq_rank_diff_rank_zero X _).symm, 
  rw rank_zero_iff_subset_loops, 
  intros e he, 
  rw [← loop_iff_mem_loops, loop_iff_r, ← ε_eq_pc_matroid_r, ε_eq_r_of_r_le_one],
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

lemma ε_flat_eq_num_points {M : matroid α} {F : set α} (hF : M.is_flat F): 
  M.ε F = size {P : set α | M.is_point P ∧ P ⊆ F} := 
begin
  simp only [ε_eq_num_points_inter M F, ← size_set_of_push] , 
  convert rfl, 
  ext P,
  cases P with P hP, 
  refine ⟨λ h, (nonempty_of_r_nonzero M _), _⟩, 
  { have hPF : P \ M.loops ⊆ F := subset.trans (diff_subset _ _) h,  
    rw [subset_iff_inter_eq_left.mp hPF, rank_eq_rank_diff_loops, hP.r], 
    norm_num },
  obtain ⟨e,he,rfl⟩ := point_iff_cl_nonloop.mp hP, 
  rintros ⟨x, ⟨ ⟨hxP, hxL⟩ , hxF⟩ ⟩, 
  apply (subset_flat _ _ _ hF), 
  rw singleton_subset_iff, 
  exact mem_flat_of_parallel hF (parallel_of_mem_cl hxP (nonloop_iff_not_mem_loops.mpr hxL)) hxF,
end

lemma ε_univ_eq_num_points (M : matroid α):
  M.ε univ = type_size M.point :=
begin
  rw [point, type_size_type_of_eq_size_set_of], 
  convert ε_flat_eq_num_points M.univ_is_flat, 
  ext P, 
  exact ⟨λ h, ⟨h, subset_univ _⟩, λ h, h.1⟩,  
end

lemma ε_univ_eq_size_set_of_points (M : matroid α):
  M.ε univ = size { P : set α | M.is_point P } :=
by {rw [ε_univ_eq_num_points, point, type_size_type_of_eq_size_set_of]}

lemma ε_proj_nonloop (M : matroid α) {e : α} (he : M.is_nonloop e): 
  (M ⟋ {e}).ε univ = size { L | M.is_line L ∧ e ∈ L} := 
begin
  rw [ε_univ_eq_num_points, point, type_size_type_of_eq_size_set_of], 
  convert rfl, ext, rwa [point_project_nonloop_iff], 
end

/-- this is the workhorse for Kung's Theorem - it gives a formula for the number of points of M 
in terms of the lengths of lines of M through e -/
lemma ε_as_ε_proj_nonloop {M : matroid α} {e : α} (he : M.is_nonloop e): 
  M.ε univ = 1 + ∑ᶠ L in { L | M.is_line L ∧ e ∈ L}, (M.ε L - 1) :=  
begin
  set lines := {L : set α | M.is_line L ∧ e ∈ L}, 
  have hcle : ∀ L ∈ lines, disjoint {P | M.is_point P ∧ P ⊆ L ∧ P ≠ M.cl {e}} {M.cl {e}}, 
  { intros L hL, simp, },
  have h₁ : ∀ L ∈ lines, M.ε L - 1 = size {P | M.is_point P ∧ P ⊆ L ∧ P ≠ M.cl {e}},
  { intros L hL, 
    rw [ε_flat_eq_num_points (hL.1.flat),  sub_eq_iff_eq_add, 
    ←size_singleton (M.cl {e}), ← size_union_of_disjoint (hcle L hL)], 
    congr', 
    ext X, 
    rw [mem_def, mem_union, mem_set_of_eq, mem_singleton_iff], 
    refine ⟨λ h, by {by_cases h' : X = M.cl {e}; tauto, } , λ h, _⟩, 
    rcases h with (h₁ | rfl), tauto, 
    exact ⟨point_of_cl_nonloop he, subset_flat _ _ (singleton_subset_iff.mpr hL.2) (hL.1.flat)⟩},
     
  rw [finsum_in_eq_of_eq h₁, ← size_bUnion, ← size_singleton (M.cl {e} : set α),
   ← size_union_of_disjoint, ε_univ_eq_size_set_of_points], rotate, 
  { rw [disjoint_iff_inter_eq_empty, inter_bUnion], 
    ext x, 
    rw [mem_bUnion_iff],
    conv in (_ ∩ _) {rw [inter_comm], rw (disjoint_iff_inter_eq_empty.mp (hcle _ h))}, 
    tauto},
  { rintros x y ⟨hx, hxL⟩ ⟨hy, hyL⟩ hxy, 
    simp only [disjoint_right, and_imp, not_and, not_not, mem_set_of_eq, ne.def], 
    rintros a ha hay - - hax, 
    obtain ⟨f, hf, rfl⟩ := point_iff_cl_nonloop.mp ha, 
    rw [cl_eq_cl_iff_parallel_cl_eq_parallel_cl, ← parallel_iff_parallel_cl_eq_left hf],
    apply parallel_of_rank_le_one hf he,  
    refine le_trans (M.rank_mono _) (rank_inter_lines_le_one hx hy hxy), 
    have := singleton_subset_iff.mp (subset.trans (M.subset_cl {f}) hay), 
    have := singleton_subset_iff.mp (subset.trans (M.subset_cl {f}) hax), 
    intro z, 
    simp only [mem_singleton_iff, mem_inter_eq, mem_insert_iff],
    rintro (rfl | rfl); tauto,},

  convert rfl, 
  ext P,
  simp only [exists_prop, mem_Union, singleton_union, mem_set_of_eq, mem_insert_iff, ne.def],  
  refine ⟨by { rintros (rfl | h), exact point_of_cl_nonloop he, tauto, }, λ h, _⟩, 

  obtain ⟨f, hf, rfl⟩ := point_iff_cl_nonloop.mp h, 
  simp only [cl_eq_cl_iff_parallel_cl_eq_parallel_cl, ← parallel_iff_parallel_cl_eq_left hf], 
  
  by_cases hef : M.parallel f e, left, assumption, right, 
  
  refine ⟨M.cl {e,f}, ⟨⟨cl_is_flat _ _,_⟩,_⟩ , _, _, hef⟩, 
  { rw [rank_cl, pair_comm, rank_two_of_not_parallel hf he hef] },
  { exact mem_of_mem_of_subset (mem_insert _ _) (subset_cl _ _) },
  { exact point_of_cl_nonloop hf},
  simp [cl_monotone], 
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
 
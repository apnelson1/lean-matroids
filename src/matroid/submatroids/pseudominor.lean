import .quotients

/-!
# Projections, Loopifications and Pseudominors

For a matroid `M` on Type `α` and sets `C,D` in `M`, this file defines matroids `M ⟋ C` and 
`M ⟍ D` which are obtained from `M` by contracting `C` and deleting `D` respectively, but then 
adding back in `C` (or `D`) as a set containing only loops. We call these operations 'projection'
and 'loopification'. 

The advantage of this over taking minors is that we stay in the Type `matroid E` rather than 
changing the ground set and having to deal with type equality . In practice it seems 
that many proofs that involve manipulating minors can be phrased only in terms of these modified 
minor-like-objects, which we call pseudominors. Kung's theorem and the matroid intersection theorem
are currently both proved in this way. 
-/
 
noncomputable theory 
open set 

variables {E : Type*} [finite E] {e f : E} {M : matroid E} {X Y D C F I I₀ R: set E}

namespace matroid 

section project 


/-- contract `C` and replace it with a set of loops to get a matroid on the same ground set.  
Often more convenient than just contracting `C` because the underlying type is preserved. -/
def project (M : matroid E) (C : set E) : matroid E :=
matroid_of_cl (λ X, M.cl (X ∪ C)) 
(λ X, (subset_union_left _ _).trans (M.subset_cl _)) 
(λ X Y hXY, M.cl_mono (union_subset_union_left _ hXY)) 
(λ X, by {simp only [cl_union_cl_left_eq_cl_union, union_assoc, union_self]} ) 
(λ X e f hf, by {rw [insert_union] at ⊢ hf, exact cl_exchange hf})

infix ` ⟋ ` :75 :=  matroid.project  

/-- Project every element outside `R` -/
def project_to (M : matroid E) (R : set E) : matroid E :=
  M ⟋ Rᶜ  

@[simp] lemma project_cl_eq (M : matroid E) (C X : set E) :
  (M ⟋ C).cl X = M.cl (X ∪ C) := 
by simp only [project, matroid_of_cl_apply]

@[simp] lemma project_empty (M : matroid E) : M ⟋ ∅ = M := 
eq_of_cl_eq_cl_forall (λ X, by simp_rw [project_cl_eq, union_empty])

@[simp] lemma project_project (M : matroid E) (C₁ C₂ : set E) : 
  M ⟋ C₁ ⟋ C₂ = M ⟋ (C₁ ∪ C₂) :=
begin
  refine eq_of_cl_eq_cl_forall (λ X, _), 
  simp_rw [project_cl_eq], 
  rw [union_right_comm, union_assoc],
end  

lemma project_is_quotient (M : matroid E) (C : set E) :
  M ⟋ C ≼ M :=
begin
  simp_rw [is_quotient, project_cl_eq], 
  exact λ X, M.cl_mono (subset_union_left _ _),   
end 

lemma project_is_weak_image (M : matroid E) (C : set E) :
  M ⟋ C ≤ M :=
(M.project_is_quotient C).weak_image  

lemma project_project_comm (M : matroid E) (C₁ C₂ : set E) :
  M ⟋ C₁ ⟋ C₂ = M ⟋ C₂ ⟋ C₁ :=
by rw [project_project, project_project, union_comm]

lemma project_contract_subset_loops (M : matroid E) (C : set E) :
  C ⊆ (M ⟋ C).cl ∅ :=
by {rw [project_cl_eq, empty_union], apply M.subset_cl}

lemma project_indep_disjoint_contract (hI : (M ⟋ C).indep I) : 
  disjoint I C := 
begin
  simp_rw [indep_iff_not_mem_cl_diff_forall, project_cl_eq] at hI, 
  rw [disjoint_iff_forall_ne], 
  rintro x hxI _ hxC rfl,
  exact hI x hxI (M.subset_cl _ (or.inr hxC)),  
end 

lemma project_indep_disjoint_cl_contract (hI : (M ⟋ C).indep I) : 
  disjoint I (M.cl C) := 
begin
  simp_rw [indep_iff_not_mem_cl_diff_forall, project_cl_eq] at hI, 
  rw [disjoint_iff_forall_ne], 
  rintro x hxI _ hxC rfl,
  exact hI x hxI (mem_of_mem_of_subset hxC (M.cl_mono (subset_union_right _ _))),  
end 

lemma union_indep_of_project_indep (hI : (M ⟋ C).indep I) (hI₀ : M.basis I₀ C) :
  M.indep (I ∪ I₀) :=
begin
  by_contra h', 
  simp_rw [indep_iff_not_mem_cl_diff_forall, project_cl_eq] at hI, 
  rw dep_iff_supset_circuit at h',
  obtain ⟨D,hDss,hD⟩ := h',  
  
  have heD : (D ∩ I).nonempty, 
  { rw [nonempty_iff_ne_empty, ne.def, ←disjoint_iff_inter_eq_empty],
    exact λ hDI, hD.dep (hI₀.indep.subset (hDI.subset_right_of_subset_union hDss))}, 

  obtain ⟨x,hx⟩ := heD, 
  apply hI x hx.2,   
  refine mem_of_mem_of_subset (hD.subset_cl_diff_singleton x hx.1) _, 
  rw [←cl_union_cl_right_eq_cl_union, ←hI₀.cl, cl_union_cl_right_eq_cl_union], 
  refine cl_subset_cl_of_subset _ (diff_subset_iff.mpr (hDss.trans _)), 
  rw [singleton_union, insert_union_distrib, insert_diff_singleton],
  exact union_subset_union (subset_insert _ _) (subset_insert _ _),
end 

lemma project_indep_of_union_basis_indep (hI₀ : M.basis I₀ C) (hdj : disjoint I I₀) 
(h_ind : M.indep (I ∪ I₀)) : 
  (M ⟋ C).indep I :=
begin
  simp_rw [indep_iff_not_mem_cl_diff_forall, project_cl_eq], 
  rw [indep_iff_not_mem_cl_diff_forall] at h_ind, 
  intros x hxI, 
  refine not_mem_subset _ (h_ind _ (or.inl hxI)), 
  rw [←cl_union_cl_right_eq_cl_union, ←hI₀.cl, cl_union_cl_right_eq_cl_union, union_diff_distrib, 
    diff_singleton_eq_self (disjoint_left.mp hdj hxI)],
  exact rfl.subset, 
end 
 
lemma project_indep_iff_exists (M : matroid E) (I : set E) : 
  (M ⟋ C).indep I ↔ ∃ I₀, disjoint I I₀ ∧ M.basis I₀ C ∧ M.indep (I ∪ I₀) :=
begin
  refine ⟨λ h, _,λ h, _⟩, 
  { obtain ⟨I₀, hI₀⟩ := M.exists_basis C, 
    refine ⟨I₀, disjoint_of_subset_right hI₀.subset (project_indep_disjoint_contract h), hI₀, _⟩, 
    exact union_indep_of_project_indep h hI₀},
  obtain ⟨I₀, hII₀, hI₀, hu⟩ := h,  
  exact project_indep_of_union_basis_indep hI₀ hII₀ hu,  
end    

lemma project_indep_iff_forall (M : matroid E) (I : set E) : 
  (M ⟋ C).indep I ↔ disjoint I C ∧ ∀ I₀, M.basis I₀ C → M.indep (I ∪ I₀) :=
begin
  refine ⟨λ hI, ⟨project_indep_disjoint_contract hI, λ I₀ hI₀, 
    union_indep_of_project_indep hI hI₀⟩, _⟩, 
  rw project_indep_iff_exists, 
  rintro ⟨hdj, hbas⟩,   
  obtain ⟨I₀, hI₀⟩ := M.exists_basis C, 
  exact ⟨I₀, disjoint_of_subset_right hI₀.subset hdj, hI₀, hbas _ hI₀⟩,  
end 

lemma project_basis_of_basis (hI : M.basis I (X ∪ C)) (hIC : M.basis (I ∩ C) C) :
  (M ⟋ C).basis (I \ C) X :=
begin
  simp_rw [basis_iff_indep_cl, project_cl_eq, diff_union_self, diff_subset_iff], 
  refine ⟨project_indep_of_union_basis_indep hIC _ _, _, _⟩, 
  { rw disjoint_iff_forall_ne, rintro x ⟨-,hxC⟩ y ⟨-,hyC⟩ rfl, exact hxC hyC},
  { rw diff_union_inter, exact hI.indep},
  { rw [←cl_union_cl_left_eq_cl_union, hI.cl, cl_union_cl_left_eq_cl_union, 
      union_assoc, union_self], 
    refine subset_trans (subset_union_left _ _) (M.subset_cl _)},
  rw [union_comm], 
  exact hI.subset,
end 

lemma union_basis_of_project_basis (hI : (M ⟋ C).basis I X) (hI₀ : M.basis I₀ C) :
  M.basis (I ∪ I₀) (X ∪ C) :=
begin
  simp_rw [basis_iff_indep_cl],  
  refine ⟨union_indep_of_project_indep hI.indep hI₀, _, 
    union_subset_union hI.subset hI₀.subset⟩, 
  simp_rw [basis_iff_indep_cl, project_cl_eq] at hI,
  rw [←cl_union_cl_right_eq_cl_union, hI₀.cl, cl_union_cl_right_eq_cl_union], 
  exact union_subset hI.2.1 ((subset_union_right _ _).trans (M.subset_cl _)),  
end 

lemma project_basis_iff_exists : 
  (M ⟋ C).basis I X ↔ ∃ I₀, disjoint I I₀ ∧ M.basis I₀ C ∧ M.basis (I ∪ I₀) (X ∪ C) :=
begin
  split, 
  { obtain ⟨I₀, hI₀⟩ := M.exists_basis C, 
    exact λ h, ⟨I₀, disjoint_of_subset_right hI₀.subset (project_indep_disjoint_contract h.indep), 
      hI₀, union_basis_of_project_basis h hI₀⟩},
  rintro ⟨I₀, hII₀, hI₀C, hb⟩,    
  have h'' := hI₀C.eq_of_subset_indep (hb.indep.inter_right C) 
      (subset_inter (subset_union_right _ _) hI₀C.subset) (inter_subset_right _ _),
  
  convert project_basis_of_basis hb (h'' ▸ hI₀C), 
  have h' := inter_union_diff (I ∪ I₀) C, 
  
  refine subset_antisymm (subset_diff.mpr ⟨subset_union_left _ _,_⟩) (diff_subset_iff.mpr _), 
  { rw disjoint_iff_forall_ne, 
    rintro x hxI hy hyC rfl, 
    exact hII₀.ne_of_mem hxI (((set.ext_iff.mp h'') x).mpr ⟨or.inl hxI, hyC⟩) rfl},
  exact (union_subset_union_right _ hI₀C.subset).trans_eq (union_comm _ _), 
end 

lemma project_basis_iff_forall : 
  (M ⟋ C).basis I X ↔ disjoint I (M.cl C) ∧ ∀ I₀, M.basis I₀ C → M.basis (I ∪ I₀) (X ∪ C) :=
begin
  split,
  { exact λ hI, ⟨project_indep_disjoint_cl_contract hI.indep, λ I₀ hI₀, 
      union_basis_of_project_basis hI hI₀⟩},
  rintro ⟨hIdj, h⟩, 
  rw project_basis_iff_exists, 
  obtain ⟨I₀, hI₀⟩ := M.exists_basis C, 
  exact ⟨I₀, disjoint_of_subset_right (hI₀.subset.trans (M.subset_cl _)) hIdj, hI₀, h _ hI₀⟩,   
end  

@[simp] lemma coe_r_project (M : matroid E) (C X : set E) : 
  ((M.project C).r X : ℤ) = M.r (X ∪ C) - M.r C :=
begin
  obtain ⟨I,hI⟩ := (M.project C).exists_basis X, 
  obtain ⟨I₀,hI₀⟩ := M.exists_basis C, 
  obtain ⟨h1,h2⟩  := project_basis_iff_forall.mp hI, 
  specialize h2 _ hI₀, 
  
  rw [←hI.r, hI.indep.r, ←h2.r, ←hI₀.r, hI₀.indep.r, h2.indep.r, ncard_union_eq],
  {rw [nat.cast_add], linarith},
  exact disjoint_of_subset_right (hI₀.subset.trans (M.subset_cl _)) h1, 
end 

end project 

section loopify 

/-- The loopification of `D` in a matroid `M` is obtained from `M` by turning all elements of `D` 
  into loops. Not very mathematically natural, but often more convenient than deletion because the 
  underlying type remains the same. -/
def loopify (M : matroid E) (D : set E) : 
  matroid E := 
matroid_of_circuit 
(λ C, (M.circuit C ∧ disjoint C D) ∨ ∃ e ∈ D, C = {e}) 
(begin
  by_contra' h, 
  obtain (h | ⟨e, -, h⟩) := h, 
  { simpa using h.1.nonempty},
  exact nonempty_iff_ne_empty.mp (singleton_nonempty _) h.symm, 
end) 
(begin
  rintros C₁ C₂ (⟨hC₁,hC₁D⟩ | ⟨e₁,he₁,rfl⟩) (⟨hC₂,hC₂D⟩ | ⟨e₂,he₂,rfl⟩) hC₁C₂,   
  { exact hC₁.eq_of_subset_circuit hC₂ hC₁C₂},
  { obtain (rfl | h) := subset_singleton_iff_eq.mp hC₁C₂,
    { exact (M.empty_not_circuit hC₁).elim},
    exact h},
  { exact (disjoint_iff_forall_ne.mp hC₂D e₁ (singleton_subset_iff.mp hC₁C₂) _ he₁ rfl).elim},
  simp only [subset_singleton_iff, mem_singleton_iff, forall_eq] at hC₁C₂, 
  rw hC₁C₂,
end)
(begin
  rintros C₁ C₂ e (⟨hC₁,hC₁D⟩ | ⟨e₁,he₁,rfl⟩) (⟨hC₂,hC₂D⟩ | ⟨e₂,he₂,rfl⟩) hne he,
  { obtain ⟨C,hCdiff,hC⟩ := hC₁.elimination hC₂ hne e, 
    refine ⟨C, hCdiff, or.inl ⟨hC,_⟩⟩,
    apply disjoint_of_subset_left hCdiff (disjoint.disjoint_sdiff_left (hC₁D.union_left hC₂D))},
  { rw [mem_inter_iff, mem_singleton_iff] at he, 
    obtain ⟨he,rfl⟩ := he, 
    exact (hC₁D.ne_of_mem he he₂ rfl).elim},
  { rw [mem_inter_iff, mem_singleton_iff] at he, 
    obtain ⟨rfl,he⟩ := he, 
    exact (hC₂D.ne_of_mem he he₁ rfl).elim},
  simp only [ne.def, singleton_eq_singleton_iff, mem_inter_iff, mem_singleton_iff] at he hne,
  exact (hne (he.1.symm.trans he.2)).elim, 
end)

infix ` ⟍ ` :75 :=  matroid.loopify  

@[simp] lemma circuit_loopify_iff :
  (M ⟍ D).circuit C ↔ (M.circuit C ∧ disjoint C D) ∨ ∃ e ∈ D, C = {e} := 
by simp [loopify]

@[simp] lemma indep_loopify_iff :
  (M ⟍ D).indep I ↔ disjoint I D ∧ M.indep I :=
begin
  simp_rw [indep_iff_forall_subset_not_circuit, circuit_loopify_iff, exists_prop, not_or_distrib, 
    not_and, not_exists, not_and, disjoint_iff_forall_ne, ne.def, not_forall, not_not, exists_prop, 
    exists_eq_right'],
  split, 
  { intros h, 
    refine ⟨_,λ C hCI hC, _⟩, 
    { rintro x hxI hy hyD rfl,
      exact (h {x} (singleton_subset_iff.mpr hxI)).2 x hyD rfl},
    obtain ⟨x, hxC,hxD⟩ := (h C hCI).1 hC, 
    exact (h {x} (singleton_subset_iff.mpr (hCI hxC))).2 x hxD rfl},
  simp only [and_imp],
  refine λ h h' C hCI, ⟨λ hC, (h' C hCI hC).elim, _⟩, 
  rintro x hCD rfl, 
  exact h x (singleton_subset_iff.mp hCI) x hCD rfl, 
end 

lemma basis_loopify_iff : 
  (M ⟍ D).basis I X ↔ disjoint I D ∧ M.basis I (X \ D) :=
begin
  simp_rw [basis_iff, indep_loopify_iff], 
  split, 
  { rintro ⟨⟨hdj, hI⟩, hIX, h⟩, 
    refine ⟨hdj, hI, (subset_diff.mpr ⟨hIX, hdj⟩), λ J hJ hIJ hJX, _⟩,
    
     },
end  

@[simp] lemma r_loopify : 
  (M ⟍ D).r X = M.r (X \ D) :=
begin
  simp_rw [eq_r_iff], 
end 


-- Is this maybe easier to define in terms of flats? Independent sets would be easiest, but I want 
-- to avoid cardinality in the axioms. TODO 
-- def loopify' (M : matroid E) (D : set E) : 
--   matroid E :=
-- matroid_of_flat
--   (λ F, ∃ F₀, M.flat F₀ ∧ F = F₀ ∪ D)
--   (⟨univ, M.univ_flat, univ_union.symm⟩)
--   (by {rintro _ _ ⟨F₁, hF₁, rfl⟩ ⟨F₂, hF₂, rfl⟩, 
--     exact ⟨F₁ ∩ F₂,hF₁.inter hF₂,by rw union_distrib_right⟩})
--   (begin
--     rintro _ e ⟨F, hF,rfl⟩ he,
--     obtain ⟨F', ⟨heF',hFF'⟩, hF'u⟩ := 
--       hF.exists_unique_flat_of_not_mem (not_mem_subset (subset_union_left _ _) he), 
    
--     refine ⟨F' ∪ D, ⟨⟨F',hFF'.flat_right,rfl⟩,
--       insert_subset.mpr ⟨(subset_union_left _ _) heF',union_subset_union_left _ hFF'.subset⟩,_⟩, _⟩,  
--     { rintro _ ⟨F₀,hF₀, rfl⟩ hss hssu, 
--       have := hFF'.eq_of_subset_of_ssubset hF₀, 
--       },
--   end )

end loopify 

end matroid 


-- lemma project_makes_loops (M : matroid α) (C : set α) : loops M ∪ C ⊆ loops (M ⟋ C)  := 
-- by rw [←rank_zero_iff_subset_loops, project_r, union_assoc, union_self, 
--         union_comm, rank_eq_rank_union_rank_zero C (rank_loops M), sub_self]

-- lemma loop_of_project (M : matroid α )(he : e ∈ C) : (M ⟋ C).is_loop e := 
-- loop_iff_mem_loops.mpr (mem_of_mem_of_subset (by {exact or.inr he}) (project_makes_loops M C)) 

-- lemma projected_set_rank_zero (M : matroid α) (C : set α) : (M ⟋ C).r C = 0 := 
-- by rw [project_r, union_self, sub_self] 

-- lemma projected_set_union_rank_zero (M : matroid α) (C : set α){X : set α} (hX : M.r X = 0) :
--   (M ⟋ C).r (X ∪ C) = 0 :=
-- by rwa [project_r, union_assoc, union_self, union_comm, rank_eq_rank_union_rank_zero, sub_self] 

-- lemma project_rank_zero_eq (h : M.r C = 0) : M ⟋ C = M := 
-- by {ext X, rw [project_r, rank_eq_rank_union_rank_zero X h, h, sub_zero]}

-- lemma project_rank_zero_of_rank_zero (C : set α) (hX : M.r X = 0) : (M ⟋ C).r X = 0 := 
-- by {apply rank_eq_zero_of_le_zero, rw ←hX, apply project_is_weak_image}

-- lemma project_nonloops_eq (C : set α): (M ⟋ C).nonloops = M.nonloops \ M.cl C :=
-- begin
--   ext x,
--   rw [mem_diff, ← nonloop_iff_mem_nonloops, ← nonloop_iff_mem_nonloops, nonloop_iff_r, project_r, 
--     nonmem_cl_iff_r, union_comm],  
--   refine ⟨λ h, ⟨by_contra (λ hn, _), by linarith⟩, λ h, by linarith [h.2]⟩,
--   rw [← loop_iff_not_nonloop, loop_iff_r] at hn, 
--   rw [rank_eq_rank_union_rank_zero _ hn, sub_self] at h, 
--   exact zero_ne_one h,   
-- end

-- lemma indep_union_project_set_of_project_indep 
-- (hX : is_indep (M ⟋ C) X) (hC : is_indep M C) :
-- is_indep M (X ∪ C) :=
-- by {simp_rw [indep_iff_r, project_r] at *, 
--     linarith [M.R1 (X ∪ C), size_modular X C, size_nonneg (X ∩ C)]}

-- lemma project_nonloop_fewer_nonloops (he : M.is_nonloop e): (M ⟋ {e}).nonloops ⊂ M.nonloops := 
-- begin
--   simp_rw [nonloops_eq_compl_loops],
--   apply ssubset_compl_commpl.mpr,  
--   rw ssubset_iff_subset_ne, 
--   refine ⟨subset.trans (subset_union_left _ _) (project_makes_loops M {e}), λ hn, _⟩, 
--   rw ext_iff at hn, 
--   have h' := (not_iff_not.mpr (hn e)).mp (nonloop_iff_not_mem_loops.mp he), 
--   exact h' (loop_iff_mem_loops.mp (loop_of_project M (mem_singleton e))),  
-- end 

-- lemma indep_of_project_indep (h: is_indep (M ⟋ C) X) : is_indep M X :=
-- indep_of_weak_image_indep (project_is_weak_image M C) h

-- lemma project_as_project_to (M : matroid α) (C : set α) : (M ⟋ C) = M.project_to Cᶜ := 
-- by rw [project_to, compl_compl]

-- lemma project_to_r (M : matroid α) (R X : set α) : (M.project_to R).r X = M.r (X ∪ Rᶜ) - M.r Rᶜ := 
-- by rw [project_to, project_r]

-- lemma indep_project_iff : (M ⟋ C).is_indep X ↔ M.is_indep X ∧ M.r (X ∪ C) = M.r X + M.r C := 
-- begin
--   rw [indep_iff_r,project_r, indep_iff_r], 
--   refine ⟨λ h, ⟨_,_⟩, λ h, _⟩, 
--   { refine le_antisymm (M.rank_le_size _) _, rw ←h, linarith [rank_subadditive M X C]},
--   { refine le_antisymm (M.rank_subadditive X C) _, 
--     rw (by linarith : M.r (X ∪ C) = M.r C + size X), 
--     linarith [M.rank_le_size X], },
--   rw [←h.1, h.2], simp, 
-- end

-- lemma flat_of_flat_project (h : (M ⟋ C).is_flat F) : M.is_flat F := 
-- flat_of_quotient_flat (project_is_quotient _ _) h 

-- lemma flat_project_iff : (M ⟋ C).is_flat F ↔ M.is_flat F ∧ C ⊆ F :=
-- begin
--   refine ⟨λ h, ⟨flat_of_flat_project h,_⟩, λ h, _⟩, 
--   { refine subset.trans _ (loops_subset_flat _ h),  
--     rw ←rank_zero_iff_subset_loops,
--     apply projected_set_rank_zero, },
--   simp_rw [flat_iff_r, project_r, union_comm F C, subset_iff_union_eq_left.mp h.2], 
--   intros Y hFY, 
--   suffices : M.r F < M.r Y, linarith [rank_mono_union_left M Y C], 
--   exact h.1 _ hFY, 
-- end

-- lemma point_project_nonloop_iff { e : α } (he : M.is_nonloop e){X : set α}:
--   (M ⟋ {e}).is_point X ↔ M.is_line X ∧ e ∈ X := 
-- begin
--   dsimp only  [is_point, is_line, is_rank_k_flat, project_r], 
--   rw [flat_project_iff, rank_nonloop he, singleton_subset_iff], 
--   split, 
--   { rintros ⟨⟨hF,he⟩,hX⟩, 
--     rw [union_mem_singleton he] at hX, 
--     exact ⟨⟨hF, eq_add_of_sub_eq hX⟩, he⟩ },
--   rintros ⟨⟨hF, hX⟩, he⟩, 
--   rw [union_mem_singleton he, hX], 
--   tidy, 
-- end

-- end project 

-- section loopify

-- variables {α : Type*} [fintype α] {e f : α} {M : matroid α} {X Y D C I R S : set α}

-- /-- Replace D with loops to get a matroid on the same ground set. Often more 
-- convenient than deleting D -/
-- def loopify (M : matroid α) (D : set α) : matroid α := 
-- { r := λ X, M.r (X \ D), 
--   R0 := λ X, M.R0 _, 
--   R1 := λ X, by linarith [M.R1 (X \ D), size_diff_le_size X D], 
--   R2 := λ X Y hXY, M.rank_mono (diff_subset_diff_left hXY), 
--   R3 := λ X Y, by {simp only [diff_eq], rw [inter_distrib_right, inter_distrib_inter_left], 
--                     linarith [M.rank_submod (X ∩ Dᶜ) (Y ∩ Dᶜ)], }} 

-- infix ` ⟍ ` :75 :=  matroid.loopify 

-- /-- loopify all elements of M outside R -/
-- def loopify_to (M : matroid α) (R : set α) : matroid α := M ⟍ (Rᶜ)

-- infix ` ‖ `  :75 :=  matroid.loopify_to
   
-- @[simp] lemma loopify_r (M : matroid α) (D X : set α) : (M ⟍ D).r X = M.r (X \ D) := rfl  
-- @[simp] lemma loopify_empty (M : matroid α) : M ⟍ ∅ = M := 
-- by { ext X, rw [loopify_r, diff_empty]}

-- lemma loopify_is_weak_image (M : matroid α) (D : set α) :  
--   M ⟍ D ≤ M :=
-- λ X, rank_mono_diff _ _ _ 

-- lemma loopify_loopify (M : matroid α) (D D' : set α) :
--    M ⟍ D ⟍ D' = M ⟍ (D ∪ D') :=
-- by {ext X, simp [diff_eq, ←inter_assoc, inter_right_comm]}

-- lemma loopify_loops_eq (M : matroid α) (D : set α) : 
--   M.loops ∪ D = (M ⟍ D).loops := 
-- begin
--   refine subset.antisymm _ (λ x hx, _), 
--   { rw [←rank_zero_iff_subset_loops, loopify_r, rank_zero_iff_subset_loops], tidy,},
  
--   rw [← loop_iff_mem_loops, loop_iff_r, loopify_r] at hx, 
--   by_contra hn, 
--   rw [mem_union_eq, not_or_distrib, ← nonloop_iff_not_mem_loops, nonloop_iff_r] at hn, 
--   have hxD : {x} \ D = {x},
--   { ext, 
--     simp only [mem_singleton_iff, and_iff_left_iff_imp, mem_diff], 
--     rintro rfl,  
--     exact hn.2},
--   rw [hxD,hn.1] at hx, 
--   exact one_ne_zero hx, 
-- end

-- lemma loops_subset_loopify_loops_eq (M : matroid α)(D : set α):
--   M.loops ⊆ (M ⟍ D).loops :=
-- by {rw ← loopify_loops_eq, apply subset_union_left}

-- lemma loop_of_loopify (M : matroid α) (he : e ∈ D) :
--   (M ⟍ D).is_loop e := 
-- by {rw [loop_iff_mem_loops, ← loopify_loops_eq], exact or.inr he}

-- lemma loopify_nonloops_eq (M : matroid α) (D : set α): 
--   (M ⟍ D).nonloops = M.nonloops \ D := 
-- by rw [nonloops_eq_compl_loops, nonloops_eq_compl_loops, ← loopify_loops_eq, compl_union, diff_eq]

-- lemma loopify_nonloop_fewer_nonloops (he : M.is_nonloop e): 
--   (M ⟍ {e}).nonloops ⊂ M.nonloops := 
-- begin
--   simp_rw [nonloops_eq_compl_loops],
--   apply ssubset_compl_commpl.mpr,  
--   rw ← loopify_loops_eq, 
--   exact ssubset_of_add_nonmem_iff.mp (nonloop_iff_not_mem_loops.mp he),
-- end

-- lemma loopify_rank_zero_eq (h : M.r D = 0) :
--   M ⟍ D = M := 
-- by {ext X, rw [loopify_r, rank_eq_rank_diff_rank_zero X h]}

-- lemma loopified_set_rank_zero (M : matroid α) (D : set α) :
--   (M ⟍ D).r D = 0 :=
-- by rw [loopify_r, set.diff_self, rank_empty] 

-- lemma loopified_set_union_rank_zero (M : matroid α) (D : set α){X : set α} (h: M.r X = 0) :
--   (M ⟍ D).r (X ∪ D) = 0 :=
-- by {rw [loopify_r, union_diff_right], exact rank_zero_of_subset_rank_zero (diff_subset _ _) h}

-- lemma loopify_rank_zero_of_rank_zero (D : set α)(hX : M.r X = 0) :
--   (M ⟍ D).r X = 0 := 
-- by {apply rank_eq_zero_of_le_zero, rw ←hX, apply loopify_is_weak_image}

-- lemma loopify_rank_of_disjoint (M : matroid α) (h : D ∩ X = ∅) :
--   (M ⟍ D).r X = M.r X := 
-- by {rw loopify_r, congr, rwa [inter_comm, disjoint_iff_diff_eq_left] at h}

-- lemma indep_of_loopify_indep (hX : is_indep (M ⟍ D) X) : 
--   is_indep M X := 
-- indep_of_weak_image_indep (loopify_is_weak_image M D) hX

-- lemma loopify_to_r (M : matroid α) (R X : set α) : 
--   (M ‖ R).r X = M.r (X ∩ R) := 
-- by simp [diff_eq, loopify_to, loopify_r]

-- lemma loopify_as_loopify_to (M : matroid α) (D : set α) : 
--   (M ⟍ D) = (M ‖ Dᶜ) := 
-- by rw [loopify_to, compl_compl]

-- lemma loopify_to.nonloops (M : matroid α) (R : set α):
--   (M ‖ R).nonloops = M.nonloops ∩ R := 
-- by rw [loopify_to, loopify_nonloops_eq, diff_eq, compl_compl]

-- lemma indep_loopify_to_iff : 
--   (M ‖ R).is_indep I ↔ M.is_indep I ∧ I ⊆ R := 
-- begin
--   rw [indep_iff_r, loopify_to_r, indep_iff_r],
--   refine ⟨λ h, _, λ h, by {cases h with h h', rwa subset_iff_inter_eq_left.mp h'}⟩,
--   have h' : I ∩ R = I, 
--   { refine eq_of_eq_size_subset (inter_subset_left _ _) _, 
--     refine le_antisymm (size_mono_inter_left _ _) _,
--     rw ←h, apply rank_le_size,},
--   rw [←h, h', subset_iff_inter_eq_left],
--   simpa, 
-- end

-- lemma indep_loopify_iff : 
--   (M ⟍ D).is_indep X ↔ M.is_indep X ∧ X ∩ D = ∅ := 
-- by rw [loopify_as_loopify_to, indep_loopify_to_iff, subset_compl_iff_disjoint]

-- lemma indep_of_indep_loopify_to (hI : (M ‖ R).is_indep I) :
--   M.is_indep I := 
-- (indep_loopify_to_iff.mp hI).1

-- lemma indep_loopify_to_subset_is_indep 
-- (hSR: S ⊆ R) (hI: (M ‖ S).is_indep I ) :
--   (M ‖ R).is_indep I := 
-- by {simp_rw [indep_loopify_to_iff] at *, exact ⟨hI.1, subset.trans hI.2 hSR⟩} 

-- lemma loopify_to_eq_loopify_to_iff {M N : matroid α}:
--   M ‖ S = N ‖ S ↔ (∀ X ⊆ S, M.r X = N.r X) := 
-- begin
--   refine ⟨λ h, λ X hX, _, λ h, _⟩,
--   { rw [← (subset_iff_inter_eq_left.mp hX), ← loopify_to_r, ← loopify_to_r, h]},
--   ext Y : 2 , 
--   rw [loopify_to_r, loopify_to_r, h _ (inter_subset_right _ _)], 
-- end

-- end loopify 

-- section pminor

-- variables {α : Type*} [fintype α] { M N : matroid α } {C D : set α}

-- /-- a pminor (pseudominor) of a matroid M is a matroid on the same ground set arising 
-- from loopifications and/or projections of M  -/
-- def is_pminor_of (N M : matroid α) := 
--   ∃ C D, N = M ⟋ C ⟍ D 

-- lemma pr_is_pminor (M : matroid α) (C : set α): 
--   (M ⟋ C).is_pminor_of M := 
-- ⟨C, ∅, by simp⟩ 

-- lemma lp_is_pminor (M : matroid α) (D : set α): 
--   (M ⟍ D).is_pminor_of M := 
-- ⟨∅, D, by simp⟩ 

-- lemma pr_lp_eq_lp_pr (M : matroid α) (C D : set α) :
--   M ⟋ C ⟍ D = M ⟍ (D \ C) ⟋ C :=
-- by {ext X, simp only [loopify_r, project_r], convert rfl; {ext, simp, tauto! }}
  
-- lemma lp_pr_eq_pr_lp (M : matroid α) (C D : set α) :
--   M ⟍ D ⟋ C = M ⟋ (C \ D) ⟍ D :=
-- by {ext X, simp only [loopify_r, project_r], convert rfl; {ext, simp, tauto! }}

-- lemma rank_zero_of_lp_pr (M : matroid α) (C D : set α) :
--   (M ⟍ D ⟋ C).r (C ∪ D) = 0 := 
-- begin
--   apply rank_zero_of_union_rank_zero, apply projected_set_rank_zero, 
--   apply project_rank_zero_of_rank_zero, apply loopified_set_rank_zero, 
-- end

-- lemma rank_zero_of_pr_lp (M : matroid α) (C D : set α) :
--   (M ⟋ C ⟍ D).r (C ∪ D) = 0 := 
-- begin
--   apply rank_zero_of_union_rank_zero, 
--   apply loopify_rank_zero_of_rank_zero, apply projected_set_rank_zero, 
--   apply loopified_set_rank_zero,
-- end

-- lemma pminor_iff_exists_lp_pr_disjoint {N M : matroid α} :
--   N.is_pminor_of M ↔ ∃ C D, C ∩ D = ∅ ∧ N = M ⟍ D ⟋ C :=
-- begin
--   split, rintros ⟨C,D,h⟩, refine ⟨C,D \ C, ⟨by simp ,_⟩ ⟩, rwa ←pr_lp_eq_lp_pr, 
--   rintros ⟨C,D,hCD,h⟩, refine ⟨C \ D, D, _⟩, rwa ←lp_pr_eq_pr_lp, 
-- end

-- lemma pminor_iff_exists_pr_lp_disjoint {N M : matroid α} :
--   N.is_pminor_of M ↔ ∃ C D, C ∩ D = ∅ ∧ N = M ⟋ C ⟍ D :=
-- begin
--   split, swap, rintros ⟨C,D,hCD,h⟩, exact ⟨C, D, h⟩,
--   rintros ⟨C,D,h⟩, refine ⟨C,D \ C, ⟨by simp ,_⟩ ⟩, 
--   rw [h, ←loopify_rank_zero_eq (_ : (M ⟋ C ⟍ (D \ C)).r (C ∩ D) = 0), loopify_loopify],
--   { congr, ext, simp, tauto!, }, 
--   refine rank_zero_of_subset_rank_zero _ (rank_zero_of_pr_lp _ _ _), 
--   intro x, simp, tauto,
-- end

-- end pminor 

-- end matroid 

import mathlib.data.set.basic
import mathlib.order.boolean_algebra
import .quotients
--import .connectivity

/-!
# Projections, Loopifications and Pseudominors

For a matroid `M` on Type `E` and sets `C,D` in `M`, this file defines matroids `M ⟋ C` and
`M ⟍ D` which are obtained from `M` by contracting `C` and deleting `D` respectively, but then
adding back in `C` (or `D`) as a set containing only loops. We call these operations 'projection'
and 'loopification'.

The advantage of this over taking minors is that we stay in the Type `matroid E` rather than
changing the ground set and having to deal with type equality . In practice it seems
that many proofs that involve manipulating minors can be phrased only in terms of these modified
minor-like-objects, which we call pseudominors.

Kung's theorem and the matroid intersection theorem are currently both proved in this way.
(or at least will be once I fix them again)
-/

noncomputable theory
open set

variables {E : Type*}  {e f : E} {M N : matroid E} {X Y D C F H B I I₀ R : set E}

namespace matroid

section restrict

@[class] structure has_restr (α β : Type*) := (restr : α → β → α)

infix ` ‖ ` :75 :=  has_restr.restr 

instance {E : Type*} : has_restr (matroid E) (set E) := ⟨λ M E, M.lrestrict E⟩  

@[simp] lemma lrestr_indep_iff : (M ‖ R).indep I ↔ M.indep I ∧ I ⊆ R := lrestrict_indep_iff

lemma indep.lrestr_indep_of_subset (hI : M.indep I) (hIR : I ⊆ R) : (M ‖ R).indep I := 
lrestr_indep_iff.mpr ⟨hI, hIR⟩ 

lemma indep.lrestr_to_indep (h : (M ‖ R).indep I) : M.indep I := (lrestr_indep_iff.mp h).1 

lemma indep.lrestr_to_subset (h : (M ‖ R).indep I) : I ⊆ R := (lrestr_indep_iff.mp h).2 

lemma lrestr_lrestr (M : matroid E) (R₁ R₂ : set E) : (M ‖ R₁) ‖ R₂ = M ‖ (R₁ ∩ R₂) :=
eq_of_indep_iff_indep_forall (λ I, by simp [and_assoc])

lemma lrestr_lrestr_eq_lrestr_of_subset (M : matroid E) {R₁ R₂ : set E} (h : R₂ ⊆ R₁) :
  (M ‖ R₁) ‖ R₂ = M ‖ R₂ := 
by rw [lrestr_lrestr, inter_eq_right_iff_subset.mpr h]

@[simp] lemma lrestr_basis_iff : (M ‖ R).basis I X ↔ M.basis I (X ∩ R) :=
begin
  refine ⟨λ h, indep.basis_of_maximal_subset _ _ _, λ h, indep.basis_of_maximal_subset _ _ _⟩,
  { exact (lrestr_indep_iff.mp h.indep).1 },
  { exact subset_inter h.subset (lrestr_indep_iff.mp h.indep).2 },
  { intros J hJ hIJ hJXR,
     rw h.eq_of_subset_indep (hJ.lrestr_indep_of_subset (hJXR.trans (inter_subset_right _ _))) 
      hIJ (hJXR.trans (inter_subset_left _ _)) },
  { exact h.indep.lrestr_indep_of_subset (h.subset.trans (inter_subset_right _ _)) },
  { exact h.subset.trans (inter_subset_left _ _) },
  intros J hJ hIJ hJX, 
  rw h.eq_of_subset_indep (lrestr_indep_iff.mp hJ).1 hIJ (subset_inter hJX _), 
  exact (lrestr_indep_iff.mp hJ).2, 
end 

@[simp] lemma lrestr_base_iff : (M ‖ R).base B ↔ M.basis B R := iff.rfl 

@[simp] lemma lrestr_r (M : matroid E) (R X : set E) : (M ‖ R).r X = M.r (X ∩ R) :=
by { obtain ⟨I, hI⟩ := (M ‖ R).exists_basis X, rw [←hI.card, ←(lrestr_basis_iff.mp hI).card] }

@[simp] lemma lrestr_nonloop_iff : (M ‖ R).nonloop e ↔ M.nonloop e ∧ e ∈ R :=
by rw [←indep_singleton, ←indep_singleton, lrestr_indep_iff, singleton_subset_iff]

@[simp] lemma lrestr_loop_iff : (M ‖ R).loop e ↔ M.loop e ∨ e ∉ R :=
by rw [←not_iff_not, not_loop_iff, lrestr_nonloop_iff, not_or_distrib, not_loop_iff, not_not]

@[simp] lemma lrestr_cl (M : matroid E) (R X : set E) : (M ‖ R).cl X = M.cl (X ∩ R) ∪ Rᶜ :=
begin
  obtain ⟨I, hI⟩ := (M ‖ R).exists_basis X, 
  simp_rw [←hI.cl, ←(lrestr_basis_iff.mp hI).cl] ,
  ext e, 
  rw [hI.indep.mem_cl_iff, lrestr_indep_iff, mem_union, (lrestr_basis_iff.mp hI).indep.mem_cl_iff, 
    insert_subset, mem_compl_iff, and_imp, and_imp, ←imp_iff_or_not], 
  exact ⟨λ h he hi, h hi he (hI.indep.lrestr_to_subset), λ h hi heR hIR, h heR hi⟩,
end 

@[simp] lemma lrestr.loops (M : matroid E) (R : set E) : ((M ‖ R).cl ∅)ᶜ = (M.cl ∅)ᶜ ∩ R :=
by rw [lrestr_cl, empty_inter, compl_union, compl_compl]

@[simp] lemma lrestr.nonloops (M : matroid E) (R : set E) : ((M ‖ R).cl ∅)ᶜ = (M.cl ∅)ᶜ ∩ R :=
by rw [lrestr_cl, empty_inter, compl_union, compl_compl]

lemma lrestr.weak_image (M : matroid E) (R : set E) : M ‖ R ≤w M := λ I, indep.lrestr_to_indep 

-- lemma lrestr.circuit_iff : (M ‖ R).circuit C ↔ M.circuit C ∧ C ⊆ R := sorry  

-- lemma lrestr.hyperplane_iff : (M ‖ R).hyperplane H ↔ 
--   H ∈ maximals (⊆) {X : set E | ¬∃ I ⊆ X, M.basis I R } := sorry 

-- lemma lrestr.cocircuit_iff : (M ‖ R).cocircuit X ↔ 
--   X ∈ minimals (⊆) {X : set E | ∀ I, M.basis I R → (I ∩ X).nonempty  } := sorry 

-- lemma lrestr_eq_lrestr_iff' {M N : matroid E} : M ‖ X = N ‖ X ↔ ∀ I ⊆ X, M.indep I ↔ N.indep I := sorry 

-- lemma lrestr_eq_lrestr_iff {M N : matroid E} : M ‖ X = N ‖ Y ↔ 
--   (∀ e ∈ (X ∪ Y)ᶜ, M.loop e ∧ M.loop e) ∧ ∀ I ⊆ X ∩ Y, M.indep I ↔ N.indep I :=
-- begin
--   sorry, 
-- end

end restrict

section loopify

@[class] structure has_del (α β : Type*) := (del : α → β → α)

infix ` ⟍ ` :75 :=  has_del.del 

/-- Matroid deletion is restriction to the complement -/
instance matroid_del_loopify {E : Type*} : has_del (matroid E) (set E) := ⟨λ M X, M ‖ Xᶜ⟩    

/-- Matroid deletion of an element is deletion of the corresponding singleton set -/
instance del_singleton {E : Type*} : has_del (matroid E) E := ⟨λ M e, M ⟍ ({e} : set E)⟩  

lemma loopify_eq_lrestr_compl (M : matroid E) (D : set E) : M ⟍ D = M ‖ Dᶜ := rfl 

@[simp] lemma loopify.elem (M : matroid E) (e : E) : M ⟍ e = M ⟍ ({e} : set E) := rfl 

@[simp] lemma loopify.base_iff : (M ⟍ D).base B ↔ M.basis B Dᶜ := iff.rfl

@[simp] lemma loopify.indep_iff :
  (M ⟍ D).indep I ↔ disjoint I D ∧ M.indep I :=
by rw [loopify_eq_lrestr_compl, lrestr_indep_iff, subset_compl_iff_disjoint_right, and_comm]

lemma indep.loopify_to_indep (h : (M ⟍ D).indep I) : M.indep I := (loopify.indep_iff.mp h).2

lemma loopify.weak_image (M : matroid E) (D : set E) : M ⟍ D ≤w M := lrestr.weak_image _ _ 

@[simp] lemma loopify.empty (M : matroid E): M ⟍ (∅ : set E) = M :=
eq_of_indep_iff_indep_forall (λ I, by simp)

lemma loopify.circuit_iff : (M ⟍ D).circuit C ↔ (M.circuit C ∧ disjoint C D) ∨ ∃ e ∈ D, C = {e} :=
begin
  simp_rw [circuit_iff, loopify.indep_iff, not_and, exists_prop],
  split,
  { rintro ⟨h₁, h₂⟩,
    obtain (h | ⟨e,heC,heD⟩) := (C ∩ D).eq_empty_or_nonempty,
    { left,
      rw ←disjoint_iff_inter_eq_empty at h,
      exact ⟨⟨h₁ h, λ I hIC, (h₂ I hIC).2⟩,h⟩},
      refine or.inr ⟨e,heD, _⟩,
      obtain (hss | rfl) := (singleton_subset_iff.mpr heC).ssubset_or_eq, swap, refl,
      have hcon := (h₂ _ hss).1,
      rw [disjoint_singleton_left] at hcon,
      exact (hcon heD).elim},
  rintro (⟨⟨hdep, h⟩,hdj⟩  | ⟨e,heD,rfl⟩),
  { exact ⟨λ _, hdep, λ I hIC, ⟨disjoint_of_subset_left hIC.subset hdj, h I hIC⟩⟩},
  refine ⟨λ h, (disjoint_singleton_left.mp h heD).elim, λ I hI, _⟩,
  rw ssubset_singleton_iff at hI,
  subst hI,
  exact ⟨empty_disjoint _, M.empty_indep⟩,
end

lemma loopify.circuit_iff_of_disjoint (hC : disjoint C D) : (M ⟍ D).circuit C ↔ M.circuit C :=
begin
  rw [loopify.circuit_iff],
  refine ⟨λ h, h.elim (and.left) _,λ h, (or.inl ⟨h,hC⟩)⟩,
  rintro ⟨e,heD,rfl⟩,
  refine h.elim (and.left) (false.elim ∘ _),
  rintro ⟨f,hfD,hef⟩,
  rw [hef, disjoint_singleton_left] at hC,
  exact hC hfD,
end

@[simp] lemma loopify.cl_eq (D X : set E) : (M ⟍ D).cl X = M.cl (X \ D) ∪ D :=
begin
  ext e,
  simp_rw [mem_cl_iff_exists_circuit, loopify.circuit_iff],
  split,
  { rintro (heX | ⟨C, ⟨⟨hC,hCD⟩ | ⟨f,hfD,rfl⟩,hC'⟩⟩),
    { exact (em (e ∈ D)).elim or.inr (λ heD,
        or.inl (mem_of_mem_of_subset (⟨heX, heD⟩ : e ∈ X \ D) (M.subset_cl _) ))},
    { refine or.inl (mem_of_mem_of_subset (hC.subset_cl_diff_singleton e hC'.1)
        (M.cl_subset_cl_of_subset _)),
      rw [subset_diff],
      exact ⟨hC'.2, disjoint_of_subset_left (diff_subset _ _) hCD⟩},
    rw ←mem_singleton_iff.mp hC'.1 at hfD,
    exact or.inr hfD},

  by_cases heD : e ∈ D,
  { exact λ _, or.inr ⟨{e}, or.inr ⟨_,heD,rfl⟩, mem_singleton_of_eq rfl, by simp⟩},
  rintro (heX | heD'), swap, exact (heD heD').elim,

  rw mem_cl_iff_exists_circuit at heX,
  obtain ( heXD | ⟨C, hC, heC, hCX⟩) := heX,
  { exact or.inl ((diff_subset _ _) heXD)},
  refine (em (e ∈ X)).elim or.inl (λ heX, or.inr _),
  refine ⟨C, or.inl ⟨hC, _⟩, heC, hCX.trans (diff_subset _ _)⟩,

  rw [←inter_union_diff C {e}, disjoint_union_left, inter_singleton_eq_of_mem heC,
    disjoint_singleton_left],
  rw subset_diff at hCX,
  exact ⟨heD, hCX.2⟩,
end

@[simp] lemma loopify.loop_iff : (M ⟍ D).loop e ↔ M.loop e ∨ e ∈ D :=
by { simp_rw [loop_iff_mem_cl_empty, loopify.cl_eq, empty_diff], refl }

@[simp] lemma loopify.nonloop_iff : (M ⟍ D).nonloop e ↔ M.nonloop e ∧ e ∉ D :=
by simp_rw [←not_loop_iff, loopify.loop_iff, not_or_distrib] 

lemma subset_loops_of_loopify (M : matroid E) (D : set E) : D ⊆ (M ⟍ D).cl ∅ :=
by {rw [loopify.cl_eq], exact subset_union_right _ _}

lemma loop_of_loopify (h : e ∈ D) : (M ⟍ D).loop e :=
by {rw loop_iff_mem_cl_empty, exact M.subset_loops_of_loopify D h}

@[simp] lemma loopify.nonloops (M : matroid E) (D : set E) : ((M ⟍ D).cl ∅)ᶜ  = (M.cl ∅)ᶜ \ D :=
by { ext, simp_rw [mem_diff, mem_compl_iff, ←loop_iff_mem_cl_empty, ←not_or_distrib, not_iff_not, 
  loopify.loop_iff] }

lemma loopify.basis_iff : (M ⟍ D).basis I X ↔ disjoint I D ∧ M.basis I (X \ D) :=
begin
  simp_rw [basis_iff, loopify.indep_iff],
  split,
  { rintro ⟨⟨hdj, hI⟩, hIX, h⟩,
    exact ⟨hdj, hI, (subset_diff.mpr ⟨hIX, hdj⟩), λ J hJ hIJ hJX,
     h J ⟨(disjoint_of_subset_left hJX (disjoint_sdiff_left)),hJ⟩
      hIJ (hJX.trans (diff_subset _ _))⟩},
  rintro ⟨hdj,hI,hIXD,h⟩,
  exact ⟨⟨hdj,hI⟩, hIXD.trans (diff_subset _ _), λ J h' hIJ hJX, h _ h'.2 hIJ
    (subset_diff.mpr ⟨hJX, h'.1⟩)⟩,
end

lemma loopify.basis_iff_of_disjoint (h : disjoint X D) : (M ⟍ D).basis I X ↔ M.basis I X :=
begin
  rw [loopify.basis_iff],
  exact ⟨λ hI,
    hI.2.basis_subset (hI.2.subset.trans (diff_subset _ _)) (subset_diff.mpr ⟨subset.rfl, h⟩),
  λ hI, ⟨disjoint_of_subset_left hI.subset h, hI.basis_subset
    (subset_diff.mpr ⟨hI.subset,disjoint_of_subset_left hI.subset h⟩) (diff_subset _ _)⟩⟩,
end

@[simp] lemma loopify.r_eq : (M ⟍ D).r X = M.r (X \ D) :=
begin
  obtain ⟨I, hI⟩ := (M ⟍ D).exists_basis X,
  rw [←hI.r, hI.indep.r],
  rw [loopify.basis_iff] at hI,
  rw [←hI.2.r, hI.2.indep.r],
end

lemma loopify.eq_of_subset_loops (h : D ⊆ M.cl ∅) : M ⟍ D = M :=
begin
  refine eq_of_indep_iff_indep_forall (λ I, _),
  rw [loopify.indep_iff],
  refine ⟨and.right, λ hI, ⟨disjoint_of_subset_right h hI.disjoint_loops,hI⟩⟩,
end

lemma loopify_eq_self_iff_subset_loops : M ⟍ D = M ↔ D ⊆ M.cl ∅ :=
begin
  refine ⟨λ h e heD, _, loopify.eq_of_subset_loops⟩,
  rw [←h, loopify.cl_eq],
  exact or.inr heD,
end

lemma loopify.r_eq_of_disjoint (h : disjoint X D) : (M ⟍ D).r X = M.r X :=
by rw [loopify.r_eq, sdiff_eq_left.mpr h]

@[simp] lemma loopify_loopify (M : matroid E) (D D' : set E) : M ⟍ D ⟍ D' = M ⟍ (D ∪ D') :=
begin
  refine eq_of_indep_iff_indep_forall (λ I, _),
  simp_rw [loopify.indep_iff, ←and_assoc],
  convert iff.rfl,
  rw [and_comm, disjoint_union_right],
end

lemma loopify_loopify_comm (M : matroid E) (D D' : set E) : M ⟍ D ⟍ D' = M ⟍ D' ⟍ D :=
by rw [loopify_loopify, union_comm, loopify_loopify]

lemma not_mem_of_indep_loopify_singleton (h : (M ⟍ ({e} : set E)).indep I) : e ∉ I :=
(loop_of_loopify (mem_singleton e)).not_mem_indep h

end loopify

section project

@[class] structure has_con (α β : Type*) := (con : α → β → α)

infix ` ⟋ ` :75 :=  has_con.con

private lemma project_aux {M : matroid E} (I : set E) {C J : set E} (hJ : M.basis J C): 
  cl_indep (λ X, M.cl (X ∪ C)) I ↔ disjoint I J ∧ M.indep (I ∪ J) :=
begin
  simp_rw [cl_indep, ←cl_union_cl_right_eq_cl_union _ _ C, ←hJ.cl, cl_union_cl_right_eq_cl_union, 
    disjoint_iff_forall_ne], 
  refine ⟨λ h, ⟨_,_⟩,λ h e heI hecl, _⟩, 
  { rintro e heI f heJ rfl, exact h e heI (M.subset_cl _ (or.inr heJ)) },
  { rw [indep_iff_forall_subset_not_circuit], 
    refine λ C' hCIJ hC, hC.dep (hJ.indep.subset (λ e heC, _)), 
    refine or.elim (hCIJ heC) (λ heI, (h e heI _).elim) id, 
    refine (M.cl_subset_cl_of_subset _) (hC.subset_cl_diff_singleton e heC), 
    rw [diff_subset_iff, ←union_assoc, union_diff_self, union_assoc], 
    exact hCIJ.trans (subset_union_right _ _) },
  rw indep_iff_not_mem_cl_diff_forall at h, 
  refine h.2 e (or.inl heI) (M.cl_subset_cl_of_subset _ hecl), 
  
  rw [union_diff_distrib],
  have heJ : e ∉ J, from λ heJ, h.1 e heI e heJ rfl, 
  nth_rewrite 0 [←diff_singleton_eq_self heJ],
end  

/-- The matroid obtained from `M` by contracting all elements in `C` and replacing them with loops-/
def project (M : matroid E) (C : set E) :
  matroid E :=
matroid_of_cl (λ X, M.cl (X ∪ C)) (λ X, (subset_union_left _ _).trans (M.subset_cl _))
(λ X Y hXY, M.cl_mono (union_subset_union_left _ hXY))
(λ X, by {simp only [cl_union_cl_left_eq_cl_union, union_assoc, union_self]} )
(λ X e f hf, by {simp_rw [insert_union] at ⊢ hf, exact cl_exchange hf})
(begin
  intros I X hI hIX,
  obtain ⟨J, hJ⟩ := M.exists_basis C, 
  simp only [project_aux _ hJ] at ⊢ hI, 
  obtain ⟨K, hIJK, hK⟩ := hI.2.subset_basis_of_subset (union_subset_union_left J hIX),  
  refine ⟨K \ J, ⟨⟨disjoint_sdiff_left,_⟩,_,_⟩, _⟩, 
  { rw [diff_union_self, union_eq_left_iff_subset.mpr ((subset_union_right _ _).trans hIJK)], 
    exact hK.indep },
  { rw [subset_diff], exact ⟨(subset_union_left _ _).trans hIJK, hI.1⟩ },
  { rw [diff_subset_iff, union_comm], exact hK.subset },
  simp only [mem_set_of_eq, and_imp], 
  refine λ I' hdj hi hII' hI'X hKJI', subset_diff.mpr ⟨_, hdj⟩, 
  rw hK.eq_of_subset_indep hi (by rwa [diff_subset_iff, union_comm] at hKJI')
    (union_subset_union_left _ hI'X),  
  exact subset_union_left _ _,
end)

instance proj {E : Type*} : has_con (matroid E) (set E) := ⟨λ M C, M.project C⟩ 

instance proj_elem {E : Type*} : has_con (matroid E) E := ⟨λ M e, M ⟋ ({e} : set E)⟩  

/-- Project every element outside `R` -/
def project_to (M : matroid E) (R : set E) : matroid E := M ⟋ Rᶜ

@[simp] lemma project_cl_eq (M : matroid E) (C X : set E) : (M ⟋ C).cl X = M.cl (X ∪ C) :=
by simp only [has_con.con, matroid.project, matroid_of_cl_apply]

@[simp] lemma project_empty (M : matroid E) : M ⟋ (∅ : set E) = M :=
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

lemma project_weak_image (M : matroid E) (C : set E) :
  M ⟋ C ≤w M :=
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

lemma project_indep_iff_exists :
  (M ⟋ C).indep I ↔ ∃ I₀, disjoint I I₀ ∧ M.basis I₀ C ∧ M.indep (I ∪ I₀) :=
begin
  refine ⟨λ h, _,λ h, _⟩,
  { obtain ⟨I₀, hI₀⟩ := M.exists_basis C,
    refine ⟨I₀, disjoint_of_subset_right hI₀.subset (project_indep_disjoint_contract h), hI₀, _⟩,
    exact union_indep_of_project_indep h hI₀},
  obtain ⟨I₀, hII₀, hI₀, hu⟩ := h,
  exact project_indep_of_union_basis_indep hI₀ hII₀ hu,
end

lemma project_indep_iff_forall :
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
  ((M ⟋ C).r X : ℤ) = M.r (X ∪ C) - M.r C :=
begin
  obtain ⟨I,hI⟩ := (M ⟋ C).exists_basis X,
  obtain ⟨I₀,hI₀⟩ := M.exists_basis C,
  obtain ⟨h1,h2⟩  := project_basis_iff_forall.mp hI,
  specialize h2 _ hI₀,

  rw [←hI.r, hI.indep.r, ←h2.r, ←hI₀.r, hI₀.indep.r, h2.indep.r, ncard_union_eq],
  {rw [nat.cast_add], linarith},
  exact disjoint_of_subset_right (hI₀.subset.trans (M.subset_cl _)) h1,
end

lemma indep.project_indep_iff (hI₀ : M.indep I₀) : 
  (M ⟋ I₀).indep I ↔ disjoint I I₀ ∧ M.indep (I ∪ I₀) :=
begin
  simp_rw [project_indep_iff_exists],
  split,
  { rintro ⟨J, hdj, hJ, hIJ⟩,
    have := hI₀.eq_of_basis hJ, subst this,
    exact ⟨hdj, hIJ⟩},
  rintro ⟨hdj, hI⟩,
  exact ⟨I₀, hdj, hI₀.basis_self, hI⟩,
end

lemma indep_of_project_indep (h : (M ⟋ C).indep I) :
  M.indep I :=
h.weak_image (project_weak_image _ _)

lemma project_cl_eq_project (M : matroid E) (C : set E) :
  M ⟋ (M.cl C) = M ⟋ C  :=
eq_of_cl_eq_cl_forall (λ X, by simp_rw [project_cl_eq, cl_union_cl_right_eq_cl_union])

lemma basis.project_eq_project (hI : M.basis I X) :
  M ⟋ I = M ⟋ X :=
by rw [←project_cl_eq_project, ←M.project_cl_eq_project X, hI.cl]

@[simp] lemma project_loops_eq :
  (M ⟋ C).cl ∅ = M.cl C :=
by rw [project_cl_eq, empty_union]

lemma loop_of_project_iff :
  (M ⟋ C).loop e ↔ e ∈ M.cl C :=
by rw [loop_iff_mem_cl_empty, project_cl_eq, empty_union]

lemma loop_of_project_mem_cl (he : e ∈ M.cl C) :
  (M ⟋ C).loop e :=
loop_of_project_iff.mpr he

lemma loop_of_project_mem (he : e ∈ C) :
  (M ⟋ C).loop e :=
loop_of_project_iff.mpr (mem_of_mem_of_subset he (M.subset_cl _))

lemma project_eq_of_loops (h : C ⊆ M.cl ∅) :
  (M ⟋ C) = M :=
by rw [←project_cl_eq_project, cl_eq_loops_of_subset h, project_cl_eq_project, project_empty]

lemma project_eq_self_iff_subset_loops :
  M ⟋ C = M ↔ C ⊆ M.cl ∅ :=
begin
  refine ⟨λ h e heC, _, project_eq_of_loops⟩, 
  rw [←h, project_loops_eq],
  exact (M.subset_cl C) heC, 
end    

@[simp] lemma project_elem (M : matroid E) (e : E) : M ⟋ e = M ⟋ ({e} : set E) := rfl 

lemma indep_project_singleton_iff (he : M.nonloop e) (heI : e ∉ I) :
  (M ⟋ e).indep I ↔ M.indep (insert e I) :=
begin
  rw [project_elem], 
  rw [←indep_singleton] at he, 
  split, 
  { intro h, 
    have := he.project_indep_iff, 
    rw [this, union_singleton] at h, 
    exact h.2},
  intro h, 
  rw [he.project_indep_iff, union_singleton, disjoint_singleton_right], 
  exact ⟨heI, h⟩,    
end 

lemma r_project_singleton_add_one (he : ¬M.loop e) (X : set E) :
  (M ⟋ e).r X  + 1 = M.r (insert e X) :=
by {zify, rw [project_elem, coe_r_project, nonloop_iff_r.mp he], simp}

lemma coe_r_project_singleton (he : ¬M.loop e) (X : set E) :
  ((M ⟋ e).r X : ℤ) = M.r (insert e X) - 1 :=
by {rw ←r_project_singleton_add_one he X, simp}

lemma not_mem_of_indep_project_singleton (h : (M ⟋ e).indep I) :
  e ∉ I :=
(loop_of_project_mem (mem_singleton e)).not_mem_indep h

end project

section loopify




section pseudominor

lemma project_loopify_swap (M : matroid E) (C D : set E) :
  M ⟋ C ⟍ D = M ⟍ (D \ C) ⟋ C :=
begin
  refine eq_of_cl_eq_cl_forall (λ X, _),
  simp only [project_cl_eq, loopify_cl_eq],
  rw [union_diff_distrib, sdiff_sdiff_cancel_right, @diff_eq_compl_inter _ D C,
    @diff_eq_compl_inter _ X (Cᶜ ∩ D), compl_inter, compl_compl, inter_distrib_right,
    union_right_comm, union_eq_right_iff_subset.mpr (inter_subset_left _ _), ←diff_eq_compl_inter,
    union_comm C, union_eq_union_iff_left],
  refine ⟨_,(inter_subset_right _ _).trans (subset_union_right _ _)⟩,
  rw [←diff_eq_compl_inter],
  nth_rewrite 0 [←inter_union_diff D C],
  refine union_subset
    ((inter_subset_right _ _).trans (subset_union_of_subset_left _ _)) (subset_union_right _ _),
  exact (subset_union_right _ _).trans (M.subset_cl _),
end

lemma loopify_project_swap (M : matroid E) (C D : set E) :
  M ⟍ D ⟋ C = M ⟋ (C \ D) ⟍ D :=
begin
  rw [project_loopify_swap, sdiff_sdiff_cancel_right],
  nth_rewrite 0 ←inter_union_diff C D,
  rw [union_comm, ←project_project],
  apply project_eq_of_loops,
  simp only [project_cl_eq, empty_union, loopify_cl_eq, sdiff_idem],
  exact (inter_subset_right _ _).trans (subset_union_right _ _),
end

lemma project_loopify_comm (M : matroid E) {C D : set E} (hCD : disjoint C D) :
  M ⟋ C ⟍ D = M ⟍ D ⟋ C :=
by {convert project_loopify_swap _ _ _, rwa [eq_comm, sdiff_eq_left, disjoint.comm]}

lemma project_loopify_eq_self_iff_subset_loops :
  M ⟋ C ⟍ D = M ↔ C ∪ D ⊆ M.cl ∅ :=
begin
  refine ⟨λ h, _,λ h, _⟩,
  { rw ←h,
    simp only [loopify_cl_eq, empty_diff, project_cl_eq, empty_union, union_subset_iff,
      subset_union_right, and_true],
    exact subset_union_of_subset_left (M.subset_cl _) _},
  rw [loopify_eq_self_iff_subset_loops.mpr, project_eq_self_iff_subset_loops.mpr],
  { exact (subset_union_left _ _).trans h},
  simp only [project_cl_eq, empty_union],
  exact (subset_union_right _ _).trans (h.trans (M.cl_mono (empty_subset C))),
end

/-- a pminor (pseudominor) of a matroid M is a matroid on the same ground set arising
-- from loopifications and/or projections of M  -/
def pminor (N M : matroid E) :=
  ∃ (C D : set E), N = M ⟋ C ⟍ D

def strict_pminor (N M : matroid E) :=
  pminor N M ∧ N ≠ M

infix ` ≤p ` :75 :=  matroid.pminor

infix ` <p ` :75 :=  matroid.strict_pminor

lemma strict_pminor.pminor (h : N <p M) :
  N ≤p M :=
h.1

lemma strict_pminor.ne (h : N <p M) :
  N ≠ M :=
h.2

lemma pminor.strict_pminor_of_ne (h : N ≤p M) (hne : N ≠ M) :
  N <p M :=
⟨h,hne⟩

lemma pminor.weak_image (h : N ≤p M) :
  N ≤w M :=
by {obtain ⟨C,D,rfl⟩ := h, exact (loopify_weak_image _ _).trans (project_weak_image _ _)}

lemma project_pminor (M : matroid E) (C : set E) :
  M ⟋ C ≤p M :=
⟨C, ∅, by simp⟩

lemma loopify_pminor (M : matroid E) (D : set E) :
  M ⟍ D ≤p M :=
⟨∅, D, by simp⟩

lemma project_loopify_pminor (M : matroid E) (C D : set E) :
  M ⟋ C ⟍ D ≤p M :=
⟨C,D,rfl⟩

lemma loopify_project_pminor (M : matroid E) (C D : set E) :
  M ⟍ D ⟋ C ≤p M :=
⟨C \D,D, by {rw loopify_project_swap}⟩

/-- This doesn't include co-independence of `D`. TODO -/
lemma exists_canonical_pminor_of_pminor (h : N ≤p M) :
  ∃ C D, N = M ⟋ C ⟍ D ∧ M.indep C ∧ disjoint D (M.cl C) :=
begin
  obtain ⟨C', D', rfl⟩ := h,
  obtain ⟨C, hC⟩ := M.exists_basis C',
  refine ⟨C, D' \ M.cl C, _, hC.indep, disjoint_sdiff_left⟩ ,
  nth_rewrite 0 ←inter_union_diff D' (M.cl C),
  rw [hC.project_eq_project, union_comm, ←loopify_loopify, loopify_eq_self_iff_subset_loops,
    loopify_cl_eq, empty_diff, project_cl_eq, empty_union, hC.cl],
  exact (inter_subset_right _ _).trans (subset_union_left _ _),
end

lemma pminor_trans {M₀ M₁ M₂ : matroid E} (h₀ : M₀ ≤p M₁) (h₁ : M₁ ≤p M₂) :
  M₀ ≤p M₂ :=
begin
  obtain ⟨C₁,D₁,rfl, hC₁,hD₁⟩ := exists_canonical_pminor_of_pminor h₁,
  obtain ⟨C₀,D₀,rfl, hC₀,hD₀⟩ := exists_canonical_pminor_of_pminor h₀,

  have hdj : disjoint (C₀ ∪ C₁) (D₀ ∪ D₁),
  { rw [disjoint_union_right, disjoint.comm],
    split,
    { refine disjoint_of_subset_right _ hD₀,
      rw [loopify_cl_eq, project_cl_eq, union_subset_iff],
      split,
      { nth_rewrite 0 ←inter_union_diff C₀ D₁,
        rw [union_comm],
        exact union_subset_union ((subset_union_left _ _).trans (M₂.subset_cl _))
            (inter_subset_right _ _)},
      exact subset_union_of_subset_left ((subset_union_right _ _).trans (M₂.subset_cl _)) _},
    rw [disjoint_union_left],
    refine ⟨_, (disjoint_of_subset_left (M₂.subset_cl _) hD₁.symm)⟩,
    simp only [indep_loopify_iff] at hC₀,
    exact hC₀.1},

  rw [project_loopify_comm, project_loopify_comm, project_loopify_comm, project_project,
     loopify_loopify, ←project_loopify_comm],
  { exact ⟨_,_,rfl⟩},
  { rwa [union_comm, union_comm D₁]},
  { exact disjoint_of_subset (subset_union_right _ _) (subset_union_left _ _) hdj},
  { exact disjoint_of_subset (subset_union_right _ _) (subset_union_right _ _) hdj},
  exact disjoint_of_subset (subset_union_left _ _) (subset_union_left _ _) hdj,
end

lemma pminor_antisymm (h : N ≤p M) (h' : M ≤p N) :
  M = N :=
h'.weak_image.antisymm h.weak_image

lemma pminor.eq_of_loops_subset_loops (h : N ≤p M) (h_loops : N.cl ∅ ⊆ M.cl ∅) :
  N = M :=
begin
  obtain ⟨C, D, rfl⟩:= h,
  rw project_loopify_eq_self_iff_subset_loops,
  simp only [loopify_cl_eq, project_cl_eq, empty_diff, empty_union] at *,
  exact (union_subset_union_left D (M.subset_cl C)).trans h_loops,
end

lemma strict_pminor_of_project_nonloop (he : ¬M.loop e) :
  M ⟋ e <p M :=
begin
  refine (project_pminor M {e}).strict_pminor_of_ne (λ h, he _),
  rwa [project_eq_self_iff_subset_loops, singleton_subset_iff, ←loop_iff_mem_cl_empty] at h,
end

lemma strict_pminor_of_loopify_nonloop (he : ¬M.loop e) :
  M ⟍ e <p M :=
begin
  refine (loopify_pminor M {e}).strict_pminor_of_ne (λ h, he _),
  rwa [loopify_eq_self_iff_subset_loops, singleton_subset_iff, ←loop_iff_mem_cl_empty] at h,
end

lemma strict_pminor_of_project_loopify_r_ne_zero (h : M.r (C ∪ D) ≠ 0) :
  M ⟋ C ⟍ D <p M :=
begin
  refine (project_loopify_pminor _ _ _).strict_pminor_of_ne
    (λ hC, h (r_eq_zero_iff_subset_loops.mpr _)),
  rwa [project_loopify_eq_self_iff_subset_loops] at hC,
end

lemma strict_pminor_of_project_r_ne_zero (h : M.r (C) ≠ 0) :
  M ⟋ C <p M :=
begin
  refine (project_pminor _ _).strict_pminor_of_ne (λ hC, h (r_eq_zero_iff_subset_loops.mpr _)),
  rwa [project_eq_self_iff_subset_loops] at hC,
end

lemma pminor.loops_supset_loops (h : N ≤p M) :
  M.cl ∅ ⊆ N.cl ∅ :=
begin
  obtain ⟨C,D,rfl⟩ := h,
  simp only [loopify_cl_eq, empty_diff, project_cl_eq, empty_union],
  exact subset_union_of_subset_left (M.cl_mono (empty_subset C)) _,
end

lemma pminor.nonloops_subset_nonloops (h : N ≤p M) :
  N.nonloops ⊆ M.nonloops :=
by { simp_rw [nonloops_eq_compl_cl_empty, compl_subset_compl], exact h.loops_supset_loops } 

lemma strict_pminor.nonloops_ssubset_nonloops (h : N <p M) :
  N.nonloops ⊂ M.nonloops :=
begin
  refine (h.pminor.nonloops_subset_nonloops).ssubset_of_ne (λ he, h.ne _),
  rw [nonloops_eq_compl_cl_empty, nonloops_eq_compl_cl_empty, compl_inj_iff] at he,
  exact h.pminor.eq_of_loops_subset_loops he.subset,
end

end pseudominor

end matroid


-- lemma project_makes_loops (M : matroid E) (C : set E) : loops M ∪ C ⊆ loops (M ⟋ C)  :=
-- by rw [←rank_zero_iff_subset_loops, project_r, union_assoc, union_self,
--         union_comm, rank_eq_rank_union_rank_zero C (rank_loops M), sub_self]

-- lemma loop_of_project (M : matroid E )(he : e ∈ C) : (M ⟋ C).is_loop e :=
-- loop_iff_mem_loops.mpr (mem_of_mem_of_subset (by {exact or.inr he}) (project_makes_loops M C))

-- lemma projected_set_rank_zero (M : matroid E) (C : set E) : (M ⟋ C).r C = 0 :=
-- by rw [project_r, union_self, sub_self]

-- lemma projected_set_union_rank_zero (M : matroid E) (C : set E){X : set E} (hX : M.r X = 0) :
--   (M ⟋ C).r (X ∪ C) = 0 :=
-- by rwa [project_r, union_assoc, union_self, union_comm, rank_eq_rank_union_rank_zero, sub_self]

-- lemma project_rank_zero_eq (h : M.r C = 0) : M ⟋ C = M :=
-- by {ext X, rw [project_r, rank_eq_rank_union_rank_zero X h, h, sub_zero]}

-- lemma project_rank_zero_of_rank_zero (C : set E) (hX : M.r X = 0) : (M ⟋ C).r X = 0 :=
-- by {apply rank_eq_zero_of_le_zero, rw ←hX, apply project_is_weak_image}

-- lemma project_nonloops_eq (C : set E): (M ⟋ C).nonloops = M.nonloops \ M.cl C :=
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

-- lemma project_as_project_to (M : matroid E) (C : set E) : (M ⟋ C) = M.project_to Cᶜ :=
-- by rw [project_to, compl_compl]

-- lemma project_to_r (M : matroid E) (R X : set E) : (M.project_to R).r X = M.r (X ∪ Rᶜ) - M.r Rᶜ :=
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

-- lemma point_project_nonloop_iff { e : E } (he : M.is_nonloop e){X : set E}:
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

-- variables {E : Type*} [fintype E] {e f : E} {M : matroid E} {X Y D C I R S : set E}

-- /-- Replace D with loops to get a matroid on the same ground set. Often more
-- convenient than deleting D -/
-- def loopify (M : matroid E) (D : set E) : matroid E :=
-- { r := λ X, M.r (X \ D),
--   R0 := λ X, M.R0 _,
--   R1 := λ X, by linarith [M.R1 (X \ D), size_diff_le_size X D],
--   R2 := λ X Y hXY, M.rank_mono (diff_subset_diff_left hXY),
--   R3 := λ X Y, by {simp only [diff_eq], rw [inter_distrib_right, inter_distrib_inter_left],
--                     linarith [M.rank_submod (X ∩ Dᶜ) (Y ∩ Dᶜ)], }}

-- infix ` ⟍ ` :75 :=  matroid.loopify

-- /-- loopify all elements of M outside R -/
-- def lrestrict (M : matroid E) (R : set E) : matroid E := M ⟍ (Rᶜ)

-- infix ` ‖ `  :75 :=  matroid.lrestrict

-- @[simp] lemma loopify_r (M : matroid E) (D X : set E) : (M ⟍ D).r X = M.r (X \ D) := rfl
-- @[simp] lemma loopify_empty (M : matroid E) : M ⟍ ∅ = M :=
-- by { ext X, rw [loopify_r, diff_empty]}

-- lemma loopify_is_weak_image (M : matroid E) (D : set E) :
--   M ⟍ D ≤ M :=
-- λ X, rank_mono_diff _ _ _

-- lemma loopify_loopify (M : matroid E) (D D' : set E) :
--    M ⟍ D ⟍ D' = M ⟍ (D ∪ D') :=
-- by {ext X, simp [diff_eq, ←inter_assoc, inter_right_comm]}

-- lemma loopify_loops_eq (M : matroid E) (D : set E) :
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

-- lemma loops_subset_loopify_loops_eq (M : matroid E)(D : set E):
--   M.loops ⊆ (M ⟍ D).loops :=
-- by {rw ← loopify_loops_eq, apply subset_union_left}

-- lemma loop_of_loopify (M : matroid E) (he : e ∈ D) :
--   (M ⟍ D).is_loop e :=
-- by {rw [loop_iff_mem_loops, ← loopify_loops_eq], exact or.inr he}

-- lemma loopify_nonloops_eq (M : matroid E) (D : set E):
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

-- lemma loopified_set_rank_zero (M : matroid E) (D : set E) :
--   (M ⟍ D).r D = 0 :=
-- by rw [loopify_r, set.diff_self, rank_empty]

-- lemma loopified_set_union_rank_zero (M : matroid E) (D : set E){X : set E} (h: M.r X = 0) :
--   (M ⟍ D).r (X ∪ D) = 0 :=
-- by {rw [loopify_r, union_diff_right], exact rank_zero_of_subset_rank_zero (diff_subset _ _) h}

-- lemma loopify_rank_zero_of_rank_zero (D : set E)(hX : M.r X = 0) :
--   (M ⟍ D).r X = 0 :=
-- by {apply rank_eq_zero_of_le_zero, rw ←hX, apply loopify_is_weak_image}

-- lemma loopify_rank_of_disjoint (M : matroid E) (h : D ∩ X = ∅) :
--   (M ⟍ D).r X = M.r X :=
-- by {rw loopify_r, congr, rwa [inter_comm, disjoint_iff_diff_eq_left] at h}

-- lemma indep_of_loopify_indep (hX : is_indep (M ⟍ D) X) :
--   is_indep M X :=
-- indep_of_weak_image_indep (loopify_is_weak_image M D) hX


-- lemma indep_loopify_iff :
--   (M ⟍ D).is_indep X ↔ M.is_indep X ∧ X ∩ D = ∅ :=
-- by rw [loopify_as_lrestrict, indep_lrestrict_iff, subset_compl_iff_disjoint]

-- lemma indep_of_indep_lrestrict (hI : (M ‖ R).is_indep I) :
--   M.is_indep I :=
-- (indep_lrestrict_iff.mp hI).1

-- lemma indep_lrestrict_subset_is_indep
-- (hSR: S ⊆ R) (hI: (M ‖ S).is_indep I ) :
--   (M ‖ R).is_indep I :=
-- by {simp_rw [indep_lrestrict_iff] at *, exact ⟨hI.1, subset.trans hI.2 hSR⟩}

-- lemma lrestrict_eq_lrestrict_iff {M N : matroid E}:
--   M ‖ S = N ‖ S ↔ (∀ X ⊆ S, M.r X = N.r X) :=
-- begin
--   refine ⟨λ h, λ X hX, _, λ h, _⟩,
--   { rw [← (subset_iff_inter_eq_left.mp hX), ← lrestrict_r, ← lrestrict_r, h]},
--   ext Y : 2 ,
--   rw [lrestrict_r, lrestrict_r, h _ (inter_subset_right _ _)],
-- end

-- end loopify

-- section pminor

-- variables {E : Type*} [fintype E] { M N : matroid E } {C D : set E}

-- /-- a pminor (pseudominor) of a matroid M is a matroid on the same ground set arising
-- from loopifications and/or projections of M  -/
-- def is_pminor_of (N M : matroid E) :=
--   ∃ C D, N = M ⟋ C ⟍ D

-- lemma pr_is_pminor (M : matroid E) (C : set E):
--   (M ⟋ C).is_pminor_of M :=
-- ⟨C, ∅, by simp⟩

-- lemma lp_is_pminor (M : matroid E) (D : set E):
--   (M ⟍ D).is_pminor_of M :=
-- ⟨∅, D, by simp⟩

-- lemma pr_lp_eq_lp_pr (M : matroid E) (C D : set E) :
--   M ⟋ C ⟍ D = M ⟍ (D \ C) ⟋ C :=
-- by {ext X, simp only [loopify_r, project_r], convert rfl; {ext, simp, tauto! }}

-- lemma lp_pr_eq_pr_lp (M : matroid E) (C D : set E) :
--   M ⟍ D ⟋ C = M ⟋ (C \ D) ⟍ D :=
-- by {ext X, simp only [loopify_r, project_r], convert rfl; {ext, simp, tauto! }}

-- lemma rank_zero_of_lp_pr (M : matroid E) (C D : set E) :
--   (M ⟍ D ⟋ C).r (C ∪ D) = 0 :=
-- begin
--   apply rank_zero_of_union_rank_zero, apply projected_set_rank_zero,
--   apply project_rank_zero_of_rank_zero, apply loopified_set_rank_zero,
-- end

-- lemma rank_zero_of_pr_lp (M : matroid E) (C D : set E) :
--   (M ⟋ C ⟍ D).r (C ∪ D) = 0 :=
-- begin
--   apply rank_zero_of_union_rank_zero,
--   apply loopify_rank_zero_of_rank_zero, apply projected_set_rank_zero,
--   apply loopified_set_rank_zero,
-- end

-- lemma pminor_iff_exists_lp_pr_disjoint {N M : matroid E} :
--   N.is_pminor_of M ↔ ∃ C D, C ∩ D = ∅ ∧ N = M ⟍ D ⟋ C :=
-- begin
--   split, rintros ⟨C,D,h⟩, refine ⟨C,D \ C, ⟨by simp ,_⟩ ⟩, rwa ←pr_lp_eq_lp_pr,
--   rintros ⟨C,D,hCD,h⟩, refine ⟨C \ D, D, _⟩, rwa ←lp_pr_eq_pr_lp,
-- end

-- lemma pminor_iff_exists_pr_lp_disjoint {N M : matroid E} :
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

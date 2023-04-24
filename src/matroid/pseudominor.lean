import mathlib.data.set.basic
import mathlib.order.boolean_algebra
import .quotients


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

variables {E : Type*}  {e f : E} {M N : matroid E} {X Y D C F H B I J I₀ R : set E}

namespace matroid

section restrict

@[class] structure has_restr (α β : Type*) := (restr : α → β → α)

infix ` ‖ ` :75 :=  has_restr.restr 

instance {E : Type*} : has_restr (matroid E) (set E) := ⟨λ M E, M.lrestrict E⟩  

@[simp] lemma lrestr.indep_iff : (M ‖ R).indep I ↔ M.indep I ∧ I ⊆ R := lrestrict_indep_iff 

lemma indep.lrestr_indep_of_subset (hI : M.indep I) (hIR : I ⊆ R) : (M ‖ R).indep I := 
lrestr.indep_iff.mpr ⟨hI, hIR⟩ 

lemma indep.lrestr_to_indep (h : (M ‖ R).indep I) : M.indep I := (lrestr.indep_iff.mp h).1 

lemma indep.lrestr_to_subset (h : (M ‖ R).indep I) : I ⊆ R := (lrestr.indep_iff.mp h).2 

lemma lrestr_lrestr (M : matroid E) (R₁ R₂ : set E) : (M ‖ R₁) ‖ R₂ = M ‖ (R₁ ∩ R₂) :=
eq_of_indep_iff_indep_forall (λ I, by simp [and_assoc])

lemma lrestr_lrestr_eq_lrestr_of_subset (M : matroid E) {R₁ R₂ : set E} (h : R₂ ⊆ R₁) :
  (M ‖ R₁) ‖ R₂ = M ‖ R₂ := 
by rw [lrestr_lrestr, inter_eq_right_iff_subset.mpr h]

@[simp] lemma lrestr_basis_iff : (M ‖ R).basis I X ↔ M.basis I (X ∩ R) :=
begin
  refine ⟨λ h, indep.basis_of_maximal_subset _ _ _, λ h, indep.basis_of_maximal_subset _ _ _⟩,
  { exact (lrestr.indep_iff.mp h.indep).1 },
  { exact subset_inter h.subset (lrestr.indep_iff.mp h.indep).2 },
  { intros J hJ hIJ hJXR,
     rw h.eq_of_subset_indep (hJ.lrestr_indep_of_subset (hJXR.trans (inter_subset_right _ _))) 
      hIJ (hJXR.trans (inter_subset_left _ _)) },
  { exact h.indep.lrestr_indep_of_subset (h.subset.trans (inter_subset_right _ _)) },
  { exact h.subset.trans (inter_subset_left _ _) },
  intros J hJ hIJ hJX, 
  rw h.eq_of_subset_indep (lrestr.indep_iff.mp hJ).1 hIJ (subset_inter hJX _), 
  exact (lrestr.indep_iff.mp hJ).2, 
end 

@[simp] lemma lrestr.base_iff : (M ‖ R).base B ↔ M.basis B R := iff.rfl 

@[simp] lemma lrestr.r_eq (M : matroid E) (R X : set E) : (M ‖ R).r X = M.r (X ∩ R) :=
by { obtain ⟨I, hI⟩ := (M ‖ R).exists_basis X, rw [←hI.card, ←(lrestr_basis_iff.mp hI).card] }

lemma lrestr.r_eq_of_subset (M : matroid E) {hXR : X ⊆ R} : (M ‖ R).r X = M.r X := 
by rw [lrestr.r_eq, inter_eq_left_iff_subset.mpr hXR]

@[simp] lemma lrestr.rk_eq (M : matroid E) (R : set E) : (M ‖ R).rk = M.r R := 
by rw [rk_def, lrestr.r_eq, univ_inter]

@[simp] lemma lrestr.nonloop_iff : (M ‖ R).nonloop e ↔ M.nonloop e ∧ e ∈ R :=
by rw [←indep_singleton, ←indep_singleton, lrestr.indep_iff, singleton_subset_iff]

@[simp] lemma lrestr.loop_iff : (M ‖ R).loop e ↔ M.loop e ∨ e ∉ R :=
by rw [←not_iff_not, not_loop_iff, lrestr.nonloop_iff, not_or_distrib, not_loop_iff, not_not]

@[simp] lemma lrestr.cl_eq (M : matroid E) (R X : set E) : (M ‖ R).cl X = M.cl (X ∩ R) ∪ Rᶜ :=
begin
  obtain ⟨I, hI⟩ := (M ‖ R).exists_basis X, 
  simp_rw [←hI.cl, ←(lrestr_basis_iff.mp hI).cl] ,
  ext e, 
  rw [hI.indep.mem_cl_iff, lrestr.indep_iff, mem_union, (lrestr_basis_iff.mp hI).indep.mem_cl_iff, 
    insert_subset, mem_compl_iff, and_imp, and_imp, ←imp_iff_or_not], 
  exact ⟨λ h he hi, h hi he (hI.indep.lrestr_to_subset), λ h hi heR hIR, h heR hi⟩,
end 

@[simp] lemma lrestr.loops_eq (M : matroid E) (R : set E) : ((M ‖ R).cl ∅)ᶜ = (M.cl ∅)ᶜ ∩ R :=
by rw [lrestr.cl_eq, empty_inter, compl_union, compl_compl]

@[simp] lemma lrestr.nonloops_eq (M : matroid E) (R : set E) : ((M ‖ R).cl ∅)ᶜ = (M.cl ∅)ᶜ ∩ R :=
by rw [lrestr.cl_eq, empty_inter, compl_union, compl_compl]

lemma lrestr.weak_image (M : matroid E) (R : set E) : M ‖ R ≤w M := λ I, indep.lrestr_to_indep 

instance lrestr.finite_rk {M : matroid E} [finite_rk M] {R : set E} : finite_rk (M ‖ R) := 
(lrestr.weak_image M R).finite_rk 

lemma lrestr_eq_lrestr_iff {M₁ M₂ : matroid E} : 
  M₁ ‖ X = M₂ ‖ X ↔ ∀ I ⊆ X, M₁.indep I ↔ M₂.indep I :=
begin
  refine ⟨λ h I hIX, _,λ h, eq_of_indep_iff_indep_forall (λ I, _)⟩, 
  { apply_fun (λ (M : matroid E), M.indep I) at h, 
    rwa [eq_iff_iff, lrestr.indep_iff, lrestr.indep_iff, ←(true_iff _).mpr hIX, 
      and_true, and_true] at h },
  simp_rw [lrestr.indep_iff, and.congr_left_iff], 
  exact h I, 
end   

end restrict

section loopify

@[class] structure has_del (α β : Type*) := (del : α → β → α)

infix ` ⟍ ` :75 :=  has_del.del 

/-- Matroid deletion is restriction to the complement -/
instance matroid_del_loopify {E : Type*} : has_del (matroid E) (set E) := ⟨λ M X, M ‖ Xᶜ⟩    

/-- Matroid deletion of an element is deletion of the corresponding singleton set -/
instance del_singleton {E : Type*} : has_del (matroid E) E := ⟨λ M e, M ⟍ ({e} : set E)⟩  

lemma loopify_eq_lrestr_compl (M : matroid E) (D : set E) : M ⟍ D = M ‖ Dᶜ := rfl 

@[simp] lemma loopify_elem (M : matroid E) (e : E) : M ⟍ e = M ⟍ ({e} : set E) := rfl 

@[simp] lemma loopify.base_iff : (M ⟍ D).base B ↔ M.basis B Dᶜ := iff.rfl

@[simp] lemma loopify.indep_iff :
  (M ⟍ D).indep I ↔ disjoint I D ∧ M.indep I :=
by rw [loopify_eq_lrestr_compl, lrestr.indep_iff, subset_compl_iff_disjoint_right, and_comm]

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
      exact ⟨⟨h₁ h, λ I hIC, (h₂ _ (λ _, hIC))⟩,h⟩},
      refine or.inr ⟨e,heD, _⟩,
      obtain (hss | rfl) := (singleton_subset_iff.mpr heC).ssubset_or_eq, swap, refl,
      rw h₂ {e} (λ hdj, false.elim _) hss.subset, 
      rw [disjoint_singleton_left] at hdj,
      exact hdj heD },
  rintro (⟨⟨hdep, h⟩,hdj⟩  | ⟨e,heD,rfl⟩),
  { exact ⟨λ _, hdep, λ I hdj' hIC, h _ (hdj' (disjoint_of_subset_left hIC hdj)) hIC⟩, },
  refine ⟨λ h, (disjoint_singleton_left.mp h heD).elim, λ I hI hIe, 
    (subset_singleton_iff_eq.mp hIe).elim _ id⟩,
  rintro rfl, 
  exact (hI (empty_disjoint _) M.empty_indep).elim, 
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

@[simp] lemma project_elem (M : matroid E) (e : E) : M ⟋ e = M ⟋ ({e} : set E) := rfl 

lemma project.indep_iff_cl_indep : (M ⟋ C).indep I ↔ cl_indep (λ X, M.cl (X ∪ C)) I :=
matroid_of_cl_indep_iff _ _ _ _ _

@[simp] lemma project.cl_eq (M : matroid E) (C X : set E) : (M ⟋ C).cl X = M.cl (X ∪ C) :=
by simp only [has_con.con, matroid.project, matroid_of_cl_apply]

@[simp] lemma project_empty (M : matroid E) : M ⟋ (∅ : set E) = M :=
eq_of_cl_eq_cl_forall (λ X, by simp_rw [project.cl_eq, union_empty])

@[simp] lemma project_project (M : matroid E) (C₁ C₂ : set E) :
  M ⟋ C₁ ⟋ C₂ = M ⟋ (C₁ ∪ C₂) :=
eq_of_cl_eq_cl_forall 
  (λ X, by rw [project.cl_eq, project.cl_eq, project.cl_eq, union_right_comm, union_assoc])

lemma project_is_quotient (M : matroid E) (C : set E) : M ⟋ C ≼ M :=
by { simp_rw [is_quotient, project.cl_eq], exact λ X, M.cl_mono (subset_union_left _ _) }

lemma project_weak_image (M : matroid E) (C : set E) : M ⟋ C ≤w M :=
(M.project_is_quotient C).weak_image

lemma project_project_comm (M : matroid E) (C₁ C₂ : set E) : M ⟋ C₁ ⟋ C₂ = M ⟋ C₂ ⟋ C₁ :=
by rw [project_project, project_project, union_comm]

lemma project.contract_subset_loops (M : matroid E) (C : set E) : C ⊆ (M ⟋ C).cl ∅ :=
by { rw [project.cl_eq, empty_union], apply M.subset_cl }

lemma basis.project_indep_iff {J : set E} (hJC : M.basis J C) : 
  (M ⟋ C).indep I ↔ disjoint I J ∧ M.indep (I ∪ J) :=
by rwa [project.indep_iff_cl_indep, project_aux]

lemma indep.project_indep_iff (hJ : M.indep J) : (M ⟋ J).indep I ↔ disjoint I J ∧ M.indep (I ∪ J) :=
hJ.basis_self.project_indep_iff

lemma indep.indep_project (h : (M ⟋ C).indep I) : M.indep I :=
h.weak_image (project_weak_image _ _)

instance {M : matroid E} [finite_rk M] {C : set E} : finite_rk (M ⟋ C) := 
let ⟨B, hB⟩ := (M ⟋ C).exists_base in hB.finite_rk_of_finite (hB.indep.indep_project.finite)

lemma project_cl_eq_project (M : matroid E) (C : set E) : M ⟋ (M.cl C) = M ⟋ C  :=
eq_of_cl_eq_cl_forall (λ X, by simp_rw [project.cl_eq, cl_union_cl_right_eq_cl_union])

lemma basis.project_eq_project (hI : M.basis I X) : M ⟋ I = M ⟋ X :=
by rw [←project_cl_eq_project, ←M.project_cl_eq_project X, hI.cl]

@[simp] lemma project_loops_eq : (M ⟋ C).cl ∅ = M.cl C := by rw [project.cl_eq, empty_union]

lemma project.loop_iff : (M ⟋ C).loop e ↔ e ∈ M.cl C :=
by rw [loop_iff_mem_cl_empty, project.cl_eq, empty_union]

lemma project.loop_of_mem_cl (he : e ∈ M.cl C) : (M ⟋ C).loop e := project.loop_iff.mpr he

lemma project.loop_of_mem (he : e ∈ C) : (M ⟋ C).loop e :=
project.loop_iff.mpr (mem_of_mem_of_subset he (M.subset_cl _))

lemma project.eq_of_subset_loops (h : C ⊆ M.cl ∅) : (M ⟋ C) = M :=
by rw [←project_cl_eq_project, cl_eq_loops_of_subset h, project_cl_eq_project, project_empty]

lemma project_eq_self_iff_subset_loops : M ⟋ C = M ↔ C ⊆ M.cl ∅ :=
begin
  refine ⟨λ h e heC, _, project.eq_of_subset_loops⟩, 
  rw [←h, project_loops_eq],
  exact (M.subset_cl C) heC, 
end    

lemma indep.disjoint_project (hI : (M ⟋ C).indep I) : disjoint I C :=
begin
  simp_rw [indep_iff_not_mem_cl_diff_forall, project.cl_eq] at hI,
  rw [disjoint_iff_forall_ne],
  rintro x hxI _ hxC rfl,
  exact hI x hxI (M.subset_cl _ (or.inr hxC)),
end

lemma union_indep.indep_project (hI : (M ⟋ C).indep I) (hJC : M.basis J C) : M.indep (I ∪ J) :=
(hJC.project_indep_iff.mp hI).2 

lemma basis.project_indep_of_disjoint_indep (hJ : M.basis J C) (hdj : disjoint I J)
(h_ind : M.indep (I ∪ J)) :
  (M ⟋ C).indep I :=
hJ.project_indep_iff.mpr ⟨hdj, h_ind⟩
 
lemma project_indep_iff_forall :
  (M ⟋ C).indep I ↔ disjoint I C ∧ ∀ I₀, M.basis I₀ C → M.indep (I ∪ I₀) :=
begin
  refine ⟨λ hI, ⟨hI.disjoint_project, λ I₀ hI₀,
    union_indep.indep_project hI hI₀⟩, λ h, _⟩,
  obtain ⟨J, hJ⟩ := M.exists_basis C, 
  exact hJ.project_indep_iff.mpr ⟨disjoint_of_subset_right hJ.subset h.1, h.2 _ hJ⟩,
end

lemma project_basis_of_basis (hI : M.basis I (X ∪ C)) (hIC : M.basis (I ∩ C) C) :
  (M ⟋ C).basis (I \ C) X :=
begin
  rw [←hIC.project_eq_project, basis_iff_indep_cl, project.cl_eq,  diff_union_inter,
    diff_subset_iff, union_comm, hI.cl, hIC.indep.project_indep_iff, diff_union_inter],  
  exact ⟨⟨disjoint_of_subset_right (inter_subset_right _ _) disjoint_sdiff_left, hI.indep⟩, 
    (subset_union_left _ _).trans (M.subset_cl _), hI.subset⟩
end

lemma basis.union_basis_of_project_basis (hJ : M.basis J C) (hI : (M ⟋ C).basis I X) :
  M.basis (I ∪ J) (X ∪ C) :=
begin
  simp_rw [basis_iff_indep_cl],
  refine ⟨union_indep.indep_project hI.indep hJ, _,
    union_subset_union hI.subset hJ.subset⟩,
  simp_rw [basis_iff_indep_cl, project.cl_eq] at hI,
  rw [←cl_union_cl_right_eq_cl_union, hJ.cl, cl_union_cl_right_eq_cl_union],
  exact union_subset hI.2.1 ((subset_union_right _ _).trans (M.subset_cl _)),
end

lemma indep.project_basis_of_disjoint_of_basis_union (hJ : M.indep J) (hdj : disjoint I J) 
(hIJ : M.basis (I ∪ J) (X ∪ J)) : 
  (M ⟋ J).basis I X :=
begin
  rw [basis_iff_indep_cl, hJ.project_indep_iff, project.cl_eq, hIJ.cl], 
  refine ⟨⟨hdj, hIJ.indep⟩, (subset_union_left _ _).trans (subset_cl _ _), _⟩,  
  refine (subset_inter (subset_compl_iff_disjoint_right.mpr hdj) 
    ((subset_union_left _ _).trans hIJ.subset)).trans _, 
  rw [←diff_eq_compl_inter, diff_subset_iff, union_comm], 
end 

lemma basis.project_basis_of_disjoint_of_basis_union (hJ : M.basis J C) (hdj : disjoint I J) 
(hIJ : M.basis (I ∪ J) (X ∪ J)) :
  (M ⟋ C).basis I X :=
by { rw [←hJ.project_eq_project], exact hJ.indep.project_basis_of_disjoint_of_basis_union hdj hIJ }

lemma project_basis_iff_forall :
  (M ⟋ C).basis I X ↔ disjoint I (M.cl C) ∧ ∀ J, M.basis J C → M.basis (I ∪ J) (X ∪ C) :=
begin
  refine ⟨λ h, _,λ h, _⟩, 
  { rw [←project_cl_eq_project] at h, 
    refine ⟨h.indep.disjoint_project, λ J hJ, _⟩, 
    rw [project_cl_eq_project] at h, 
    exact hJ.union_basis_of_project_basis h },
  
  obtain ⟨J, hJ⟩ := M.exists_basis C, 
  have h' := h.2 J hJ, 
  refine hJ.project_basis_of_disjoint_of_basis_union 
    (disjoint_of_subset_right (hJ.subset.trans (subset_cl _ _)) h.1) 
    (indep.basis_of_subset_cl h'.indep (union_subset_union_left _ (λ e heI, _ )) _), 
  { refine ((subset_union_left I J).trans h'.subset heI).elim id (λ heC, _), 
    exact (h.1.ne_of_mem heI ((M.subset_cl C) heC) rfl).elim },
  rw [h'.cl, ←cl_union_cl_right_eq_cl_union, ←hJ.cl, cl_union_cl_right_eq_cl_union], 
  exact M.subset_cl _, 
end

@[simp] lemma project.cast_r (M : matroid E) [finite_rk M] (C X : set E) :
  ((M ⟋ C).r X : ℤ) = M.r (X ∪ C) - M.r C :=
begin
  obtain ⟨I,hI⟩ := (M ⟋ C).exists_basis X,
  obtain ⟨I₀,hI₀⟩ := M.exists_basis C,
  obtain ⟨h1,h2⟩  := project_basis_iff_forall.mp hI,
  specialize h2 _ hI₀,

  rw [←hI.r, hI.indep.r, ←h2.r, ←hI₀.r, hI₀.indep.r, h2.indep.r, 
    ncard_union_eq _ hI.finite hI₀.finite],
  {rw [nat.cast_add], linarith},
  exact disjoint_of_subset_right (hI₀.subset.trans (M.subset_cl _)) h1,
end

lemma project.r_add_r_eq_r_union (M : matroid E) [finite_rk M] (C X : set E) : 
  (M ⟋ C).r X + M.r C = M.r (X ∪ C) := by { zify, simp }

lemma nonloop.indep_project_iff (he : M.nonloop e) (heI : e ∉ I) :
  (M ⟋ e).indep I ↔ M.indep (insert e I) :=
by rw [project_elem, he.indep.project_indep_iff, union_singleton, disjoint_singleton_right, 
    iff_true_intro heI, true_and]

lemma nonloop.r_project_add_one_eq [finite_rk M] (he : M.nonloop e) (X : set E) :
  (M ⟋ e).r X  + 1 = M.r (insert e X) :=
by { zify, rw [project_elem, project.cast_r, nonloop_iff_r.mp he], simp }

lemma nonloop.cast_r_project_eq [finite_rk M] (he : M.nonloop e) (X : set E) :
  ((M ⟋ e).r X : ℤ) = M.r (insert e X) - 1 :=
by { rw ←nonloop.r_project_add_one_eq he X, simp }

lemma not_mem_of_indep_project_singleton (h : (M ⟋ e).indep I) : e ∉ I :=
(project.loop_of_mem (mem_singleton e)).not_mem_indep h

lemma project_eq_loopify_of_subset_coloops (hX : X ⊆ M﹡.cl ∅) : M ⟋ X = M ⟍ X :=
eq_of_cl_eq_cl_forall (λ S, by rw [project.cl_eq, loopify.cl_eq, cl_union_eq_of_subset_coloops _ hX, 
    cl_diff_eq_of_subset_coloops _ hX, diff_union_self])

lemma project_eq_loopify_of_subset_loops (hX : X ⊆ M.cl ∅) : M ⟋ X = M ⟍ X :=
by rw [project_eq_self_iff_subset_loops.mpr hX, loopify_eq_self_iff_subset_loops.mpr hX]

lemma loop.project_eq_loopify (he : M.loop e) : M ⟋ e = M ⟍ e := 
project_eq_loopify_of_subset_loops (singleton_subset_iff.mpr he)

lemma coloop.project_eq_loopify (he : M.coloop e) : M ⟋ e = M ⟍ e := 
project_eq_loopify_of_subset_coloops (singleton_subset_iff.mpr he)

end project

section pseudominor

lemma project_loopify_swap (M : matroid E) (C D : set E) :
  M ⟋ C ⟍ D = M ⟍ (D \ C) ⟋ C :=
begin
  refine eq_of_cl_eq_cl_forall (λ X, _),
  simp only [project.cl_eq, loopify.cl_eq],
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
  apply project.eq_of_subset_loops,
  simp only [project.cl_eq, empty_union, loopify.cl_eq, sdiff_idem],
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
    simp only [loopify.cl_eq, empty_diff, project.cl_eq, empty_union, union_subset_iff,
      subset_union_right, and_true],
    exact subset_union_of_subset_left (M.subset_cl _) _},
  rw [loopify_eq_self_iff_subset_loops.mpr, project_eq_self_iff_subset_loops.mpr],
  { exact (subset_union_left _ _).trans h},
  simp only [project.cl_eq, empty_union],
  exact (subset_union_right _ _).trans (h.trans (M.cl_mono (empty_subset C))),
end

/-- a pminor (pseudominor) of a matroid M is a matroid on the same ground set arising
-- from loopifications and/or projections of M  -/
def pminor (N M : matroid E) : Prop := ∃ (C D : set E), N = M ⟋ C ⟍ D

def strict_pminor (N M : matroid E) : Prop := pminor N M ∧ N ≠ M

infix ` ≤p ` :75 :=  matroid.pminor

infix ` <p ` :75 :=  matroid.strict_pminor

lemma strict_pminor.pminor (h : N <p M) : N ≤p M := h.1

lemma strict_pminor.ne (h : N <p M) : N ≠ M := h.2

lemma pminor.strict_pminor_of_ne (h : N ≤p M) (hne : N ≠ M) : N <p M := ⟨h,hne⟩

lemma pminor.weak_image (h : N ≤p M) : N ≤w M :=
by {obtain ⟨C,D,rfl⟩ := h, exact (loopify.weak_image _ _).trans (project_weak_image _ _)}

lemma pminor.finite_rk [finite_rk M] (h : N ≤p M) : finite_rk N := h.weak_image.finite_rk

lemma project_pminor (M : matroid E) (C : set E) : M ⟋ C ≤p M := ⟨C, ∅, by simp⟩

lemma loopify_pminor (M : matroid E) (D : set E) : M ⟍ D ≤p M := ⟨∅, D, by simp⟩

lemma project_loopify_pminor (M : matroid E) (C D : set E) : M ⟋ C ⟍ D ≤p M := ⟨C,D,rfl⟩

lemma loopify_project_pminor (M : matroid E) (C D : set E) : M ⟍ D ⟋ C ≤p M :=
⟨C \D,D, by {rw loopify_project_swap}⟩

lemma exists_canonical_pminor_of_pminor (h : N ≤p M) :
  ∃ C D, N = M ⟋ C ⟍ D ∧ M.indep C ∧ disjoint D (M.cl C) :=
begin
  obtain ⟨C', D', rfl⟩ := h,
  obtain ⟨C, hC⟩ := M.exists_basis C',
  refine ⟨C, D' \ M.cl C, _, hC.indep, disjoint_sdiff_left⟩ ,
  nth_rewrite 0 ←inter_union_diff D' (M.cl C),
  rw [hC.project_eq_project, union_comm, ←loopify_loopify, loopify_eq_self_iff_subset_loops,
    loopify.cl_eq, empty_diff, project.cl_eq, empty_union, hC.cl],
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
      rw [loopify.cl_eq, project.cl_eq, union_subset_iff],
      split,
      { nth_rewrite 0 ←inter_union_diff C₀ D₁,
        rw [union_comm],
        exact union_subset_union ((subset_union_left _ _).trans (M₂.subset_cl _))
            (inter_subset_right _ _)},
      exact subset_union_of_subset_left ((subset_union_right _ _).trans (M₂.subset_cl _)) _},
    rw [disjoint_union_left],
    refine ⟨_, (disjoint_of_subset_left (M₂.subset_cl _) hD₁.symm)⟩,
    simp only [loopify.indep_iff] at hC₀,
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
  simp only [loopify.cl_eq, project.cl_eq, empty_diff, empty_union] at *,
  exact (union_subset_union_left D (M.subset_cl C)).trans h_loops,
end

lemma strict_pminor_of_project_nonloop (he : ¬M.loop e) : M ⟋ e <p M :=
begin
  refine (project_pminor M {e}).strict_pminor_of_ne (λ h, he _),
  rwa [project_eq_self_iff_subset_loops, singleton_subset_iff, ←loop_iff_mem_cl_empty] at h,
end

lemma strict_pminor_of_loopify_nonloop (he : ¬M.loop e) : M ⟍ e <p M :=
begin
  refine (loopify_pminor M {e}).strict_pminor_of_ne (λ h, he _),
  rwa [loopify_eq_self_iff_subset_loops, singleton_subset_iff, ←loop_iff_mem_cl_empty] at h,
end

lemma strict_pminor_of_project_loopify_r_ne_zero [finite_rk M] (h : M.r (C ∪ D) ≠ 0) :
  M ⟋ C ⟍ D <p M :=
begin
  refine (project_loopify_pminor _ _ _).strict_pminor_of_ne
    (λ hC, h (r_eq_zero_iff_subset_loops.mpr _)),
  rwa [project_loopify_eq_self_iff_subset_loops] at hC,
end

lemma strict_pminor_of_project_r_ne_zero [finite_rk M] (h : M.r (C) ≠ 0) : M ⟋ C <p M :=
begin
  refine (project_pminor _ _).strict_pminor_of_ne (λ hC, h (r_eq_zero_iff_subset_loops.mpr _)),
  rwa [project_eq_self_iff_subset_loops] at hC,
end

lemma pminor.loops_supset_loops (h : N ≤p M) : M.cl ∅ ⊆ N.cl ∅ :=
begin
  obtain ⟨C,D,rfl⟩ := h,
  simp only [loopify.cl_eq, empty_diff, project.cl_eq, empty_union],
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


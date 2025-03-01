import .pseudominor

open_locale classical 
open_locale big_operators
open set 

namespace matroid

variables {E : Type*} {X Y X' Y' Z  I J C : set E} {e f : E} {M : matroid E}

/-! Skewness -/
/-- Two sets `X,Y` are `skew` if restricting to `Y` is the same as projecting `X` and restricting 
  to `Y`. For finite rank, this is the same as `r X + r Y = r (X ∪ Y)`.-/
def skew (M : matroid E) (X Y : set E) : Prop := (M ⟋ X) ‖ Y = M ‖ Y 

lemma skew_iff_project_lrestr_eq_lrestr : M.skew X Y ↔ (M ⟋ X) ‖ Y = M ‖ Y := iff.rfl 

lemma skew.project_lrestr_eq (h : M.skew X Y) : (M ⟋ X) ‖ Y = M ‖ Y := h 

lemma skew.symm (h : M.skew X Y) : M.skew Y X :=
begin
  rw [skew, lrestr_eq_lrestr_iff] at *, 
  refine λ I hIX, ⟨λ hI, hI.of_project, λ hI, _⟩,  
  obtain ⟨J, hJ⟩ := M.exists_basis Y, 
  rw [hJ.project_indep_iff], 
  have hi := (h J hJ.subset).mpr hJ.indep, 
  obtain ⟨I', hI', hIJ⟩ := hI.subset_basis_of_subset hIX, 
  rw [hI'.project_indep_iff, disjoint.comm, union_comm] at hi,  
  exact ⟨disjoint_of_subset_left hIJ hi.1, hi.2.subset (union_subset_union_left _ hIJ)⟩,   
end 

lemma skew.comm : M.skew X Y ↔ M.skew Y X := ⟨skew.symm, skew.symm⟩ 

lemma empty_skew (M : matroid E) (X : set E) : M.skew ∅ X := by rw [skew, project_empty] 

lemma skew_empty (M : matroid E) (X : set E) : M.skew X ∅ := by rw [skew.comm, skew, project_empty] 

lemma skew.subset_right (h : M.skew X Y) (hY'Y : Y' ⊆ Y) : M.skew X Y' :=
begin
  rw [skew_iff_project_lrestr_eq_lrestr, lrestr_eq_lrestr_iff] at h ⊢, 
  exact λ I hI, h I (hI.trans hY'Y),  
end 

lemma skew.subset_left (h : M.skew X Y) (hX'X : X' ⊆ X) : M.skew X' Y :=
(h.symm.subset_right hX'X).symm

lemma skew.loop_of_mem_inter (h : M.skew X Y) (he : e ∈ X ∩ Y) : M.loop e :=
begin
  rw [skew_iff_project_lrestr_eq_lrestr] at h, 
  have heY : (M ‖ Y).loop e,
  { rw [←h, lrestr.loop_iff], exact or.inl (project.loop_of_mem he.1) },
  rw [lrestr.loop_iff, ←imp_iff_or_not] at heY, 
  exact heY he.2, 
end 

lemma skew.inter_subset_loops (h : M.skew X Y) : X ∩ Y ⊆ M.cl ∅ := λ e, h.loop_of_mem_inter

lemma skew_of_subset_loops (h : X ⊆ M.cl ∅) (Y : set E) : M.skew X Y := 
by rw [skew_iff_project_lrestr_eq_lrestr, project_eq_self_iff_subset_loops.mpr h]

lemma subset_loops_skew (X : set E) (h : Y ⊆ M.cl ∅) : M.skew X Y := (skew_of_subset_loops h X).symm 

lemma skew.diff_loops_disjoint_left (h : M.skew X Y) : disjoint (X \ M.cl ∅) Y := 
begin
  refine disjoint_of_subset_left _ (@disjoint_sdiff_left _ Y X),
  rw [←@diff_inter_self_eq_diff _ X Y, inter_comm], 
  exact diff_subset_diff_right h.inter_subset_loops, 
end 

lemma skew.diff_loops_disjoint_right (h : M.skew X Y) : disjoint X (Y \ M.cl ∅) := 
h.symm.diff_loops_disjoint_left.symm 

lemma loop.singleton_skew (he : M.loop e) (X : set E) : M.skew {e} X := 
skew_of_subset_loops (singleton_subset_iff.mpr he) X 

lemma loop.skew_singleton (he : M.loop e) (X : set E) : M.skew X {e} := 
subset_loops_skew X (singleton_subset_iff.mpr he)

lemma basis.skew (hI : M.basis I X) (hJ : M.basis J Y) (hdj : disjoint I J) (hi : M.indep (I ∪ J)) :
  M.skew X Y :=
begin
  rw [skew_iff_project_lrestr_eq_lrestr, lrestr_eq_lrestr_iff], 
  intros K hKY, 
  rw [hI.project_indep_iff], 
  have hK' := (hKY.trans (M.subset_cl Y)).trans_eq hJ.cl.symm, 
  
  refine ⟨λ h, h.2.subset (subset_union_left _ _),λ h, ⟨_,_⟩⟩, 
  { rw disjoint_iff_forall_ne, 
    rintro e heK f heI rfl, 
    have heJ : e ∈ J := hJ.indep.mem_cl_iff.mp (hK' heK) 
      (hi.subset (insert_subset.mpr ⟨or.inl heI,subset_union_right _ _⟩)), 
    exact hdj.ne_of_mem heI heJ rfl },

  obtain ⟨K₁, hK₁⟩ := h.subset_basis_of_subset hKY,   
  obtain ⟨K₂, hK₂⟩ := hK₁.1.indep.subset_basis_of_subset (subset_union_left K₁ I), 
  have hi : K₁ ∪ I = K₂, 
  { refine hK₂.1.subset.antisymm' (union_subset hK₂.2 (λ e heI, (by_contra (λ heK₂, _)))),
    have heK₂' : e ∈ M.cl K₂, by { rw hK₂.1.cl, exact (M.subset_cl _) (or.inr heI) }, 
    rw [←union_diff_cancel hK₂.2, ←cl_union_cl_left_eq, hK₁.1.cl, ←hJ.cl, 
      cl_union_cl_left_eq] at heK₂', 
    have he : e ∈ M.cl ((I ∪ J) \ {e}), 
    { rw [union_comm, union_diff_distrib, diff_singleton_eq_self], 
      { refine M.cl_subset (union_subset_union_right _ _) heK₂',
        refine subset_diff_singleton _ (not_mem_subset (diff_subset _ _) heK₂),
        exact diff_subset_iff.mpr hK₂.1.subset }, 
      exact λ heJ, hdj.ne_of_mem heI heJ rfl }, 
    rw indep_iff_not_mem_cl_diff_forall at hi, 
    exact hi e (or.inl heI) he },
  subst hi, 
  exact hK₂.1.indep.subset (union_subset_union_left _ hK₁.2), 
end 

lemma skew.disjoint_of_indep_left (h : M.skew I X) (hI : M.indep I) : disjoint I X := 
begin
  rw disjoint_iff_forall_ne, 
  rintro e heI _ heY rfl, 
  exact hI.nonloop_of_mem heI (h.loop_of_mem_inter ⟨heI, heY⟩), 
end 

lemma skew.disjoint_of_indep_right (h : M.skew X I) (hI : M.indep I) : disjoint X I :=
(h.symm.disjoint_of_indep_left hI).symm

lemma skew.union_indep (h : M.skew I J) (hI : M.indep I) (hJ : M.indep J) : M.indep (I ∪ J) :=
begin
  rw [skew_iff_project_lrestr_eq_lrestr, lrestr_eq_lrestr_iff] at h, 
  specialize h J subset.rfl, 
  rw [hI.project_indep_iff, iff_true_right hJ, union_comm] at h, 
  exact h.2,
end 

lemma indep.skew_diff_of_subset (hI : M.indep I) (hJ : J ⊆ I) : M.skew J (I \ J) :=
begin
  rw [skew.comm, skew_iff_project_lrestr_eq_lrestr, lrestr_eq_lrestr_iff], 
  intros K hKJ,
  rw [(hI.diff J).project_indep_iff, 
    and_iff_right (disjoint_of_subset_left hKJ disjoint_sdiff_right), 
    iff_true_intro (hI.subset (hKJ.trans hJ)), iff_true], 
  exact hI.subset (union_subset (hKJ.trans hJ) (diff_subset _ _)), 
end 

lemma skew_iff_disjoint_of_union_indep (h : M.indep (I ∪ J)) : M.skew I J ↔ disjoint I J :=
begin
  refine ⟨λ h', disjoint_iff_inter_eq_empty.mpr ((h.subset _).eq_empty_of_subset_loops _),λ h', _⟩, 
  { exact inter_subset_union _ _ }, 
  { exact h'.inter_subset_loops },
  convert h.skew_diff_of_subset (subset_union_left _ _), 
  rwa [union_diff_left, eq_comm, sdiff_eq_left, disjoint.comm], 
end 

lemma skew.union_indep_of_subset_of_subset (h : M.skew X Y) (hI : M.indep I) (hIX : I ⊆ X)
(hJ : M.indep J) (hJY : J ⊆ Y) : M.indep (I ∪ J) :=
((h.subset_left hIX).subset_right hJY).union_indep hI hJ

lemma skew.inter_basis_left_of_basis_union (h : M.skew X Y) (hI : M.basis I (X ∪ Y)) : 
  M.basis (I ∩ X) X :=
begin
  refine (hI.indep.inter_right X).basis_of_forall_insert (inter_subset_right _ _) 
    (λ e he hi, _), 
  have heY : e ∉ Y, 
    from λ heY,  hi.nonloop_of_mem (mem_insert e _) (h.loop_of_mem_inter ⟨he.1,heY⟩), 
  rw [diff_inter, diff_self, union_empty] at he, 
  refine he.2 (hI.mem_of_insert_indep (or.inl he.1) _), 
  rw [←diff_union_inter I X, union_comm, ←insert_union], 
  exact h.union_indep_of_subset_of_subset hi (insert_subset.mpr ⟨he.1,inter_subset_right _ _⟩ ) 
    (hI.indep.diff _) (diff_subset_iff.mpr hI.subset), 
end 

lemma skew.inter_basis_right_of_basis_union (h : M.skew X Y) (hI : M.basis I (X ∪ Y)) : 
  M.basis (I ∩ Y) Y :=
by { rw union_comm at hI, exact h.symm.inter_basis_left_of_basis_union hI }

lemma skew_iff_r [finite_rk M] : M.skew X Y ↔ M.r X + M.r Y = M.r (X ∪ Y) :=
begin
  refine ⟨λ h, _,λ h, _⟩, 
  { rw [skew_iff_project_lrestr_eq_lrestr] at h, 
    rw [←lrestr.rk_eq M Y, rk_def, ←h, lrestr.r_eq, univ_inter, add_comm, 
      project.r_add_r_eq_r_union, union_comm] },
  
  obtain ⟨I, hI⟩ := M.exists_basis X, 
  obtain ⟨J, hJ⟩ := M.exists_basis Y, 
  rw [←hI.card, ←hJ.card, ←r_union_cl_left_eq_r_union, ←hI.cl, r_union_cl_left_eq_r_union, 
    ←r_union_cl_right_eq_r_union, ←hJ.cl, r_union_cl_right_eq_r_union, 
    ←ncard_inter_add_ncard_union _ _ hI.finite hJ.finite] at h,  
  
  refine hI.skew hJ _ _, 
  { have h' := h.trans_le (M.r_le_card_of_finite (hI.finite.union hJ.finite)), 
    rwa [add_le_iff_nonpos_left, le_zero_iff, ncard_eq_zero 
      (hI.finite.subset (inter_subset_left _ _)), ←disjoint_iff_inter_eq_empty] at h' },
  rw indep_iff_r_eq_card_of_finite (hI.finite.union hJ.finite),  
  refine (M.r_le_card_of_finite (hI.finite.union hJ.finite)).antisymm _, 
  linarith, 
end 

lemma skew.r_add [finite_rk M] (h : M.skew X Y) : M.r X + M.r Y = M.r (X ∪ Y) := skew_iff_r.mp h 

lemma skew.cl_left (h : M.skew X Y) : M.skew (M.cl X) Y := 
by rwa [skew_iff_project_lrestr_eq_lrestr, project_cl_eq_project, 
  ←skew_iff_project_lrestr_eq_lrestr]

lemma skew.cl_left_iff : M.skew X Y ↔ M.skew (M.cl X) Y := 
⟨skew.cl_left, λ h, h.subset_left (M.subset_cl X)⟩ 

lemma skew.cl_right (h : M.skew X Y) : M.skew X (M.cl Y) := (h.symm.cl_left).symm 

lemma skew.cl_right_iff : M.skew X Y ↔ M.skew X (M.cl Y) := 
⟨skew.cl_right, λ h, h.subset_right (M.subset_cl Y)⟩ 

lemma nonloop.singleton_skew_iff (he : M.nonloop e) : M.skew {e} X ↔ e ∉ M.cl X := 
begin
  rw skew.cl_right_iff, 
  refine ⟨λ h hecl, he (h.loop_of_mem_inter ⟨mem_singleton e,hecl⟩), λ h, _⟩, 
  obtain ⟨J, hJ⟩ := M.exists_basis X,  
  rw ←skew.cl_right_iff,  
  have heJ : e ∉ J, from (not_mem_subset (hJ.subset.trans (subset_cl _ _)) h), 
  refine he.indep.basis_self.skew hJ (disjoint_singleton_left.mpr heJ) _,  
  rwa [singleton_union, hJ.indep.insert_indep_iff_of_not_mem heJ, hJ.cl], 
end 

lemma nonloop.skew_singleton_iff (he : M.nonloop e) : M.skew X {e} ↔ e ∉ M.cl X :=
by rw [skew.comm, he.singleton_skew_iff]
 
/-- Useful for adding a disjointness assumption when proving skewness -/
lemma skew_iff_diff_loops_skew_left : M.skew X Y ↔ M.skew (X \ M.cl ∅) Y := 
by rw [iff.comm, skew.cl_left_iff, cl_diff_loops_eq_cl, ←skew.cl_left_iff]

lemma skew_iff_diff_loops_skew_right : M.skew X Y ↔ M.skew X (Y \ M.cl ∅) := 
by rw [iff.comm, skew.cl_right_iff, cl_diff_loops_eq_cl, ←skew.cl_right_iff]

lemma project_skew_of_union_skew (h : M.skew (C ∪ X) Y) : (M ⟋ C).skew X Y :=
begin
  rw [skew, project_project, skew_iff_project_lrestr_eq_lrestr.mp h, eq_comm, ←skew],
  exact h.subset_left (subset_union_left _ _), 
end  

section Skew

variables {ι : Type*} {Xs : ι → set E} 

/-- A collection of sets is `Skew` if each of its partitions gives a skew pair  -/
def Skew (M : matroid E) (Xs : ι → set E) := ∀ (I : set ι), M.skew (⋃ i ∈ I, Xs i) (⋃ i ∈ Iᶜ, Xs i)

-- lemma Skew_iff_forall : M.Skew Xs ↔ ∀ i, M.skew (Xs i) (⋃ j ∈ ({i} : set ι)ᶜ, Xs j)  :=
-- begin
--   refine ⟨λ h i, by { convert h {i}, simp, }, λ h I, _⟩,
--   rw skew_iff_project_lrestr_eq_lrestr, 

  
-- end 

end Skew

section separation 

/-- A set is a `separator` in `M` if it is skew to its complement -/
def is_separator (M : matroid E) (X : set E) := M.skew X Xᶜ  

end separation

/-- The notion of 2-connectedness for graphs can
    be extended to matroids. For each element `e`
    of a matroid `M`, let
    `gamma_set(e) = { e } ∪ { f : M has a circuit containing both e and f }`.  -/
def gamma_set (M : matroid E) (e : E) := { e } ∪ { f | ∃ C, M.circuit C ∧ e ∈ C ∧ f ∈ C }

/-- Define the relation `gamma` on `E` by `e gamma f` if and only if
    `e ∈ gamma f` -/
def gamma (M : matroid E) (e : E) (f : E) := e ∈ M.gamma_set f

/-- `gamma` is an equivalence relation on `E(M)` -/
theorem gamma_refl (M : matroid E) (e : E) : M.gamma e e :=
by { left, exact mem_singleton e }

theorem gamma_symm (M : matroid E) (e : E) (f : E) (h : M.gamma e f) : M.gamma f e :=
begin
  cases h with h,
  { rw mem_singleton_iff.mp h,
    exact M.gamma_refl f },
  { rcases h with ⟨C, hC, fC, eC⟩,
    right,
    use [C, hC, eC, fC] }
end

theorem gamma_trans (M : matroid E) (e : E) (f : E) (g : E)
  (hef : M.gamma e f) (hfg : M.gamma f g) : M.gamma e g :=
begin
  have hgf := M.gamma_symm f g hfg,

  -- trivial cases where not all `e, f, g` necessarily distinct
  cases hgf with hgf,
  { rw mem_singleton_iff.mp hgf, exact hef },
  cases hef with hef,
  { rw mem_singleton_iff.mp hef; assumption },
  cases hfg with hfg,
  { rw ←mem_singleton_iff.mp hfg,
    right, exact hef },

  -- main argument
  rcases hef with ⟨C₁, hC₁, fC₁, eC₁⟩,
  rcases hgf with ⟨C₂, hC₂, fC₂, gC₂⟩,

  have ne : C₁ ∩ C₂ ≠ ∅,
    { by_contra,
    have g : f ∈ C₁ ∩ C₂,
      use [fC₁, fC₂],
    rw h at g,
    exact g },

  sorry
end

end matroid

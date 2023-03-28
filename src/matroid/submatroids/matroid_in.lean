import .pseudominor

open_locale classical 
noncomputable theory

open matroid set 

variables {E α : Type*} [finite E] [finite α]

/- a `matroid_in α` is a matroid defined on some subset `E` of `α`. Implemented as a matroid on 
  which the nonelements of `E` are all loops. 
  
  The main motivation for this is to have a way of talking about minors that avoids type equality.
  Pseudominors give one way of doing this, while staying in `matroid E`, but they are a bit ugly 
  with duality. The advantage of `matroid_in` is that, if `M : matroid_in α`, then `M.dual` and 
  `M / C \ D` are both `matroid_in α`, and we can say things like `M / C \ D = M \ D / C` 
  meaningfully and without type equality.  

  The disadvantage is that one has to constantly keep track of a ground set, and API duplication 
  will happen. 
  -/

/-- A matroid on some subset `ground` of `α`. Implemented as a `matroid` in which the elements 
outside `ground` are all loops. The matroid `carrier` is a detail of this implentation, and not 
intended to be accessed directly.  -/
@[ext] structure matroid_in (α : Type*) [finite α] :=
(ground : set α)
(carrier : matroid α)
(support : groundᶜ ⊆ carrier.cl ∅)

namespace matroid_in 

section defs
/- Definitions -/

variables (M : matroid_in α)

def base (B : set α) : Prop := 
  M.carrier.base B

def indep (I : set α) : Prop := 
  ∃ B, M.base B ∧ I ⊆ B 

def basis (I X : set α) : Prop := 
  M.indep I ∧ I ⊆ X ∧ ∀ J, M.indep J → I ⊆ J → J ⊆ X → I = J 

def circuit (C : set α) : Prop := 
  ¬M.indep C ∧ ∀ I ⊂ C, M.indep I

def r (X : set α) : ℕ := 
  M.carrier.r X 

def flat (F : set α) : Prop := 
  F ⊆ M.ground ∧ ∀ I X, M.basis I F → M.basis I X → X ⊆ F 

def cl (X : set α) : set α := 
  ⋂₀ {F | M.flat F ∧ X ⊆ F}

def hyperplane (H : set α) : Prop :=
  M.flat H ∧ H ⊂ M.ground ∧ (∀ F, H ⊂ F → M.flat F → F = M.ground)

def loop (e : α) : Prop :=
  M.circuit {e} 

def coloop (e : α) : Prop :=
  ∀ B, M.base B → e ∈ B    

def cocircuit (K : set α) : Prop :=
  M.hyperplane (M.ground \ K)

end defs 

variables {M₁ M₂ M : matroid_in α} {X Y I B C : set α} {e f x y : α}

section carrier

/- The lemmas in this section break the abstraction between `M` and its `carrier`, and are only 
  used for basic API setup. -/

lemma subset_ground_of_disjoint_loops (hX : disjoint X (M.carrier.cl ∅)) : 
  X ⊆ M.ground :=
(subset_compl_iff_disjoint_right.mpr hX).trans (compl_subset_comm.mp M.support) 

lemma mem_ground_of_nonloop (he : ¬M.carrier.loop e) : 
  e ∈ M.ground :=
begin
  rw [loop_iff_mem_cl_empty] at he, 
  by_contra h', 
  rw ←mem_compl_iff at h', 
  exact he (M.support h')
end 

lemma subset_ground_of_base_carrier (hB : M.carrier.base B) : 
  B ⊆ M.ground := 
λ e he, mem_ground_of_nonloop (hB.indep.nonloop_of_mem he)  

lemma indep_iff_carrier_indep :
  M.indep I ↔ M.carrier.indep I := 
by simp_rw [matroid_in.indep, matroid_in.base, matroid.indep_iff_subset_base]

lemma r_ground_compl (M : matroid_in α) :
  M.r (M.groundᶜ) = 0 :=
begin
  refine r_eq_zero_of_loopy (λ e he, by_contra (λ he', he (mem_ground_of_nonloop _))), 
  rwa loop_iff_r, 
end 

end carrier 

lemma base.indep (hB : M.base B) : 
  M.indep B := 
⟨B, hB, subset.rfl⟩ 

lemma indep.subset_ground (hI : M.indep I) : 
  I ⊆ M.ground := 
let ⟨B,hB,hIB⟩ := hI in hIB.trans (subset_ground_of_base_carrier hB)

lemma r_le_r_of_subset (M : matroid_in α) (hXY : X ⊆ Y) : 
  M.r X ≤ M.r Y :=
M.carrier.r_mono hXY 

lemma indep.r (hI : M.indep I) : 
  M.r I = I.ncard :=
by rw [matroid_in.r, (indep_iff_carrier_indep.mp hI).r]

lemma empty_indep (M : matroid_in α) : 
  M.indep ∅ := 
M.carrier.empty_indep 

lemma indep.subset_basis_of_subset (hI : M.indep I) (hX : I ⊆ X) :
  ∃ J, M.basis J X ∧ I ⊆ J :=
begin
  obtain ⟨J,hIJ,hJ⟩ := (indep_iff_carrier_indep.mp hI).subset_basis_of_subset hX, 
  refine ⟨J,⟨hJ.indep,hJ.subset,λ J' hJ' hJJ' hJ'X, _⟩,hIJ⟩, 
  exact hJ.eq_of_subset_indep hJ' hJJ' hJ'X, 
end 

lemma exists_basis (M : matroid_in α) (X : set α) :
  ∃ I, M.basis I X := 
let ⟨I, hIX, h⟩ := M.empty_indep.subset_basis_of_subset (empty_subset X) in ⟨I,hIX⟩  

lemma basis.r (hI : M.basis I X) : 
  M.r I = M.r X :=
@matroid.basis.r _ _ M.carrier _ _ hI 

lemma basis.indep (hI : M.basis I X) :
  M.indep I := 
@matroid.basis.indep _ _ M.carrier _ _ hI 

lemma r_eq_r_inter_ground (X : set α): 
  M.r X = M.r (X ∩ M.ground) := 
begin
  rw [matroid_in.r, ←compl_compl M.ground, inter_comm, ←diff_eq_compl_inter, 
    ←r_eq_r_diff_r_zero X M.r_ground_compl], 
  refl, 
end 

lemma eq_of_base_iff_base {M₁ M₂ : matroid_in E} (h : M₁.ground = M₂.ground) 
(h' : ∀ B, M₁.base B ↔ M₂.base B) : 
  M₁ = M₂ :=
begin
  apply matroid_in.ext, 
    assumption,
  ext B, 
  exact h' B, 
end 
  

section equivalence 

/-- A `matroid_in` gives a matroid on a subtype -/
def to_matroid (M : matroid_in α) (hX : M.ground = X) : 
  matroid X :=
{ base := M.carrier.base ∘ (set.image coe),
  exists_base' := begin
    obtain ⟨B,hB⟩ := M.carrier.exists_base',   
    refine ⟨coe ⁻¹' B, _⟩, simp only [function.comp_app, subtype.image_preimage_coe], 
    convert hB, 
    rw [inter_eq_left_iff_subset, ←hX], 
    apply matroid_in.subset_ground_of_disjoint_loops, 
    exact hB.indep.disjoint_loops,  
  end,
  base_exchange' := begin
    subst hX, 
    rintro B₁ B₂ hB₁ hB₂ a ha, 
    simp only [function.comp_app] at hB₁ hB₂, 
    have ha' : (a : α) ∈ (coe '' B₁) \ (coe '' B₂), 
    { rw [←image_diff (subtype.coe_injective), mem_image], exact ⟨a,ha,rfl⟩},
    obtain ⟨y,hy,hy'⟩ :=  hB₁.exchange hB₂ ha', 
    refine ⟨⟨y, _⟩, _, _⟩,   
    { exact mem_ground_of_nonloop (hB₂.indep.nonloop_of_mem hy.1), },
    { simp only [←image_diff (subtype.coe_injective), mem_image, 
        subtype.exists, subtype.coe_mk, exists_and_distrib_right, exists_eq_right] at hy,  
      obtain ⟨hy'',h_eq⟩ := hy,   
      exact h_eq},
    rwa [function.comp_app, image_insert_eq, image_diff subtype.coe_injective, image_singleton], 
  end }

/-- A `matroid` on a subtype gives a `matroid_in` -/
def of_matroid_in {ground : set α} (M : matroid ground) :
  matroid_in α :=
{ ground := ground,
  carrier := 
  { base := λ B, M.base (coe ⁻¹' B) ∧ B ⊆ ground ,
    exists_base' := 
    (begin
      obtain ⟨B,hB⟩ := M.exists_base, 
      refine ⟨coe '' B, by rwa [preimage_image_eq _ subtype.coe_injective], _⟩, 
      simp only [image_subset_iff, subtype.coe_preimage_self, subset_univ], 
    end),
    base_exchange' := 
    begin
      rintro B₁ B₂ ⟨hB₁,hB₁ss⟩ ⟨hB₂,hB₂ss⟩ x hx, 
      set x' : ground := ⟨x, hB₁ss hx.1⟩ with hx'_def, 
      have hxx' : x = coe x', rw [hx'_def, subtype.coe_mk],  
      rw [hxx', ←mem_preimage, preimage_diff] at hx, 
      obtain ⟨y, hy, hBy⟩ := hB₁.exchange hB₂ hx, 
      rw [←preimage_diff, mem_preimage] at hy, 
      refine ⟨y,hy,_,_⟩,   
      { rw [←singleton_union, preimage_union, preimage_diff], rw [←singleton_union] at hBy, 
        convert hBy using 2,  
        { ext, simp [subtype.coe_inj]}, 
        convert rfl using 2, 
        { ext, rw [hx'_def], simp only [mem_singleton_iff, subtype.coe_mk, mem_preimage], 
          simp_rw [hxx'], rw [subtype.coe_inj], refl}},
      rw insert_subset, 
      exact ⟨y.2, (diff_subset _ _).trans hB₁ss⟩,   
    end },
  support := 
  (begin
    rintro e (he : e ∉ ground), 
    rw [←loop_iff_mem_cl_empty, loop_iff_not_mem_base_forall],  
    rintro B ⟨-,hB⟩ heB, 
    exact he (hB heB), 
  end) }

/-- A `matroid_in α` with ground set `X` is the same thing as a `matroid X`-/
def matroid_in_equiv_subtype {E : set α} : 
  {M : matroid_in α // M.ground = E} ≃ matroid E := 
{ to_fun := λ M, to_matroid M.1 M.2,
  inv_fun := λ M, ⟨of_matroid_in M, rfl⟩, 
  left_inv := begin
    rintro ⟨M, hM⟩, 
    subst hM, 
    ext, refl, 
    simp only [function.comp_app, subtype.image_preimage_coe, of_matroid_in, to_matroid, 
      subtype.coe_mk], 
    split, 
    { rintro ⟨hB, hBG⟩, convert hB, rwa [eq_comm, inter_eq_left_iff_subset]},
    intro hB, 
    rw [inter_eq_left_iff_subset.mpr (subset_ground_of_base_carrier hB)], 
    exact ⟨hB, subset_ground_of_base_carrier hB⟩, 
  end,
  right_inv := begin
    rintro M, 
    ext B, 
    simp only [of_matroid_in, function.comp_app, image_subset_iff, to_matroid, 
      subtype.coe_preimage_self, subset_univ, and_true], 
    rw preimage_image_eq _ (subtype.coe_injective), 
  end }


@[simp] lemma matroid_in_equiv_subtype_apply_base {E : set α} {B : set E} 
(M : {M : matroid_in α // M.ground = E}) :
  (matroid_in_equiv_subtype M).base B ↔ (M : matroid_in α).base (coe '' B) := 
by simp only [matroid_in_equiv_subtype, to_matroid, matroid_in.base, subtype.val_eq_coe, 
  equiv.coe_fn_mk]

@[simp] lemma matroid_in_equiv_subtype_apply_symm_base {B E : set α} (M : matroid E) :
  (matroid_in_equiv_subtype.symm M : matroid_in α).base B ↔ M.base (coe ⁻¹' B) ∧ B ⊆ E := 
by simp only [matroid_in_equiv_subtype, of_matroid_in, matroid_in.base, 
    equiv.coe_fn_symm_mk, subtype.coe_mk]
 
@[simp] lemma matroid_in_equiv_subtype_apply_indep {E : set α} {I : set E} 
(M : {M : matroid_in α // M.ground = E}) :
  (matroid_in_equiv_subtype M).indep I ↔ (M : matroid_in α).indep (coe '' I) := 
begin
  simp_rw [indep_iff_subset_base, matroid_in.indep, matroid_in_equiv_subtype_apply_base,  
    image_subset_iff],  
  split, 
  { rintro ⟨B, hB, hIB⟩, 
    exact ⟨_, hB, by rwa preimage_image_eq _ (subtype.coe_injective )⟩}, 
  rintro ⟨B, hB, hIB⟩, 
  refine ⟨_, _, hIB⟩, 
  convert hB, 
  simp_rw [subtype.image_preimage_coe, ← M.2],
  exact inter_eq_left_iff_subset.mpr (hB.indep.subset_ground), 
end 

@[simp] lemma matroid_in_equiv_subtype_apply_symm_indep {I E : set α} (M : matroid E) :
  (matroid_in_equiv_subtype.symm M : matroid_in α).indep I ↔ M.indep (coe ⁻¹' I) ∧ I ⊆ E := 
begin
  simp_rw [indep_iff_subset_base, matroid_in.indep, matroid_in_equiv_subtype_apply_symm_base], 
  split, 
  { rintro ⟨B, ⟨hB,hBE⟩, hIB⟩,  
    refine ⟨⟨_,hB,_⟩,hIB.trans hBE⟩, 
    rwa preimage_subset_preimage_iff, 
    simp only [subtype.range_coe_subtype, set_of_mem_eq], 
    exact hIB.trans hBE},
  rintro ⟨⟨B, hB, hIB⟩, hIE⟩,
  
  refine ⟨coe '' B,_,_⟩, 
  { simp only [image_subset_iff, subtype.coe_preimage_self, subset_univ, and_true],
    rwa [preimage_image_eq _ (subtype.coe_injective)]},
  rwa [←preimage_image_eq B (subtype.coe_injective), preimage_subset_preimage_iff] at hIB, 
  simpa only [subtype.range_coe_subtype, set_of_mem_eq], 
end 

@[simp] lemma matroid_in_equiv_subtype_apply_r {E : set α} 
(M : {M : matroid_in α // M.ground = E}) (X : set E) : 
  (matroid_in_equiv_subtype M).r X = (M : matroid_in α).r (coe '' X) := 
begin
  obtain ⟨I, hIX⟩ := (matroid_in_equiv_subtype M).exists_basis X, 
  rw [←hIX.r, hIX.indep.r], 
  simp_rw [basis_iff, matroid_in_equiv_subtype_apply_indep] at hIX, 
  obtain ⟨M, rfl⟩ := M, 
  simp_rw subtype.coe_mk at *, 
  have hI' : M.basis (coe '' I) (coe '' X), 
  { refine ⟨hIX.1, (image_subset _ hIX.2.1), λ J hJ hIJ hJX, _⟩,
    rw hIX.2.2 (coe ⁻¹' J) _ _ _, 
    { simpa using hJ.subset_ground},
    { convert hJ, simpa using hJ.subset_ground},
    { simpa using hIJ },
    rw [←preimage_image_eq X subtype.coe_injective, preimage_subset_preimage_iff],   
    { exact hJX},
    simp only [subtype.range_coe_subtype, set_of_mem_eq, hJ.subset_ground]},
  rw [←hI'.r, hI'.indep.r, ncard_image_of_injective _ subtype.coe_injective], 
end 

@[simp] lemma matroid_in_equiv_subtype_apply_symm_r {X E : set α} (M : matroid E) :
  (matroid_in_equiv_subtype.symm M : matroid_in α).r X = M.r (coe ⁻¹' X) :=
begin
  set M' := (matroid_in_equiv_subtype.symm M) with hM', 
  rw [r_eq_r_inter_ground, ←preimage_inter_range, subtype.range_coe], 
  set X' := X ∩ (M' : matroid_in α).ground with hX'_def, 
  have hX' : coe '' (coe ⁻¹' X' : set E) = X', 
  { rw image_preimage_eq_iff, simp [hX'_def], convert inter_subset_right _ _},
  rw [←hX', ←matroid_in_equiv_subtype_apply_r, hM', equiv.apply_symm_apply], 
  refl, 
end 

end equivalence 

section dual

/-- The dual of a `matroid_in` -/
def dual (M : matroid_in α) : matroid_in α := 
  matroid_in_equiv_subtype.symm (matroid_in_equiv_subtype ⟨M, rfl⟩).dual 

lemma dual_base_iff : 
  M.dual.base B ↔ M.base (M.ground \ B) ∧ B ⊆ M.ground :=
by simp [dual, image_compl_preimage]

@[simp] lemma dual_ground (M : matroid_in α): 
  M.dual.ground = M.ground := 
rfl 

@[simp] lemma dual_dual (M : matroid_in α) :
  M.dual.dual = M :=
begin
  apply eq_of_base_iff_base _ (λ B, _),
    simp, 
  simp only [dual_base_iff, dual_ground, sdiff_sdiff_right_self, inf_eq_inter], 
  split, 
  { rintro ⟨⟨h, -⟩, hB⟩, rwa [inter_eq_right_iff_subset.mpr hB] at h},
  intro hB, 
  have h := hB.indep.subset_ground, 
  exact ⟨⟨by rwa inter_eq_right_iff_subset.mpr h, diff_subset _ _⟩, h⟩, 
end 

end dual

section minor

def contract (M : matroid_in α) (C : set α) : matroid_in α := 
{ ground := M.ground \ C,
  carrier := M.carrier ⟋ C,
  support := 
  begin
    simp only [project_cl_eq, empty_union, diff_eq_compl_inter, compl_inter, compl_compl], 
    exact union_subset (M.carrier.subset_cl C) 
      (M.support.trans (M.carrier.cl_mono (empty_subset _))),
  end  }

-- def delete (M : matroid_in α) (D : set α) : matroid_in α := 
-- { ground := M.ground \ D,
--   carrier := M.carrier ⟍ D,
--   support := 
--   begin
--     simp, 
--   end  }


-- instance {α : Type*} : has_sdiff (M : matroid_in α) (set α)

end minor



end matroid_in 

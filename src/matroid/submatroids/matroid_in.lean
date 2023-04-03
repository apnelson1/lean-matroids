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

/-- A matroid on some subset `E` of `α`. Implemented as a `matroid` in which the elements 
outside `E` are all loops. -/
@[ext] structure matroid_in (α : Type*) [finite α] :=
(E : set α)
(carrier : matroid α)
(support : Eᶜ ⊆ carrier.cl ∅)

namespace matroid_in

instance {α : Type*} [finite α] : has_coe (matroid_in α) (matroid α) := ⟨λ M, M.carrier⟩ 

@[simp] lemma carrier_eq_coe {M : matroid_in α} : M.carrier = (M : matroid α) := rfl  

section defs
/- Definitions -/

variables (M : matroid_in α)

def base (B : set α) : Prop := (M : matroid α).base B

def indep (I : set α) : Prop := (M : matroid α).indep I 
  -- ∃ B, M.base B ∧ I ⊆ B

def basis (I X : set α) : Prop := (M : matroid α).basis I X 
  -- M.indep I ∧ I ⊆ X ∧ ∀ J, M.indep J → I ⊆ J → J ⊆ X → I = J

def circuit (C : set α) : Prop := (M : matroid α).circuit C ∧ C ⊆ M.E  
  -- ¬M.indep C ∧ ∀ I ⊂ C, M.indep I

def r (X : set α) : ℕ := (M : matroid α).r X 
  -- M.carrier.r X

def flat (F : set α) : Prop := (M : matroid α).flat (F ∪ M.Eᶜ) ∧ F ⊆ M.E  
  -- F ⊆ M.E ∧ ∀ I X, M.basis I F → M.basis I X → X ⊆ F 

def cl (X : set α) : set α := (M : matroid α).cl X ∩ M.E 
  -- ⋂₀ {F | M.flat F ∧ X ⊆ F}

def hyperplane (H : set α) : Prop := (M : matroid α).hyperplane (H ∪ M.Eᶜ) ∧ H ⊆ M.E  
  -- M.flat H ∧ H ⊂ M.E ∧ (∀ F, H ⊂ F → M.flat F → F = M.E)

def loop (e : α) : Prop := (M : matroid α).loop e ∧ e ∈ M.E  
  -- M.circuit {e}

def nonloop (e : α) : Prop := (M : matroid α).nonloop e 

def coloop (e : α) : Prop := (M : matroid α).coloop e 
  -- ∀ B, M.base B → e ∈ B

def cocircuit (K : set α) : Prop := (M : matroid α).cocircuit K 
  -- M.hyperplane (M.E \ K)

end defs

section basic 

variables {M : matroid_in α} {X Y I C B F H K : set α} {e f : α}

lemma loop_coe_of_not_mem_ground (h : e ∉ M.E) : (M : matroid α).loop e := M.support (mem_compl h)

lemma mem_ground_of_nonloop_coe (h : (M : matroid α).nonloop e) : e ∈ M.E := 
by_contra (λ he, h (M.support he))

lemma compl_ground_subset_loops_coe (M : matroid_in α) : M.Eᶜ ⊆ (M : matroid α).cl ∅ := M.support

lemma subset_ground_of_disjoint_loops_coe (hX : disjoint X ((M : matroid α).cl ∅)) : X ⊆ M.E :=
(subset_compl_iff_disjoint_right.mpr hX).trans (compl_subset_comm.mp M.support) 

lemma indep.subset_ground (hI : M.indep I) : I ⊆ M.E := 
  subset_ground_of_disjoint_loops_coe (matroid.indep.disjoint_loops hI)

lemma base_iff_coe : M.base B ↔ (M : matroid α).base B := iff.rfl 

lemma exists_base (M : matroid_in α) : ∃ B, M.base B := matroid.exists_base M  

lemma base.indep (hB : M.base B) : M.indep B := matroid.base.indep hB

lemma base.subset_ground (hB : M.base B) : B ⊆ M.E := hB.indep.subset_ground 

lemma indep_iff_coe : M.indep I ↔ (M : matroid α).indep I := iff.rfl 

lemma indep_iff_subset_base : M.indep I ↔ ∃ B, M.base B ∧ I ⊆ B := iff.rfl   

lemma indep.subset (hI : M.indep I) (hX : X ⊆ I) : M.indep X := matroid.indep.subset hI hX 

lemma indep.r (hI : M.indep I) : M.r I = I.ncard := matroid.indep.r hI

lemma indep.subset_basis_of_subset (hI : M.indep I) (hIX : I ⊆ X) : ∃ J, I ⊆ J ∧ M.basis J X :=
matroid.indep.subset_basis_of_subset hI hIX   

lemma circuit.subset_ground (hC : M.circuit C) : C ⊆ M.E := hC.2 

lemma circuit_iff : M.circuit C ↔ (¬ M.indep C ∧ (∀ I ⊂ C, M.indep I)) ∧ C ⊆ M.E := 
⟨λ h, ⟨h.1, h.subset_ground⟩, id⟩

lemma basis_iff_coe : M.basis I X ↔ (M : matroid α).basis I X := iff.rfl 

lemma basis.indep (hIX : M.basis I X) : M.indep I := matroid.basis.indep hIX 

lemma basis.subset (hIX : M.basis I X) : I ⊆ X := matroid.basis.subset hIX 

lemma exists_basis (M : matroid_in α) (X : set α) : ∃ I, M.basis I X := matroid.exists_basis M X

lemma basis.r (hIX : M.basis I X) : M.r I = M.r X := matroid.basis.r hIX

lemma cl_subset_ground (M : matroid_in α) (X : set α) : M.cl X ⊆ M.E := inter_subset_right _ _

lemma subset_cl (hX : X ⊆ M.E) : X ⊆ M.cl X := subset_inter (matroid.subset_cl M X) hX

lemma cl_subset_coe_cl (M : matroid_in α) (X : set α) : M.cl X ⊆ (M : matroid α).cl X := 
inter_subset_left _ _ 

lemma cl_mono (hXY : X ⊆ Y) (hY : Y ⊆ M.E) : M.cl X ⊆ M.cl Y := 
subset_inter ((M.cl_subset_coe_cl _).trans (matroid.cl_mono M hXY)) (cl_subset_ground _ _)

@[simp] lemma cl_cl (M : matroid_in α) (X : set α) : M.cl (M.cl X) = M.cl X := 
begin
  refine (subset_cl (M.cl_subset_ground X)).antisymm' (subset_inter _ (M.cl_subset_ground _)), 
  refine ((inter_subset_left _ _).trans _), 
  rw ←matroid.cl_cl (M : matroid α) X, 
  exact matroid.cl_mono _ (M.cl_subset_coe_cl X), 
end 

lemma subset_cl_iff_cl_subset_cl (hX : X ⊆ M.E) : X ⊆ M.cl Y ↔ M.cl X ⊆ M.cl Y :=
⟨λ h, inter_subset_inter (matroid.cl_subset_cl_of_subset_cl (h.trans (M.cl_subset_coe_cl _))) 
  subset.rfl, λ h, subset_trans (subset_cl hX) h⟩

lemma flat.subset_ground (hF : M.flat F) : F ⊆ M.E := hF.2 

lemma flat.cl (hF : M.flat F) : M.cl F = F := 
begin
  refine (subset_cl hF.subset_ground).antisymm' _,
  convert inter_subset_inter_left M.E hF.1.cl.subset using 1, 
  { convert rfl using 2,
    rw [←cl_union_cl_right_eq_cl_union, cl_eq_loops_of_subset (compl_ground_subset_loops_coe _), 
      cl_union_cl_right_eq_cl_union, union_empty], 
    apply_instance },
  rw [inter_distrib_right, inter_eq_left_iff_subset.mpr hF.subset_ground, compl_inter_self, 
    union_empty], 
end 

lemma loop.mem_ground (he : M.loop e) : e ∈ M.E := he.2 

lemma loop.dep (he : M.loop e) : ¬ M.indep {e} := matroid.loop.dep he.1 

lemma loop_iff_dep (he : e ∈ M.E) : M.loop e ↔ ¬ M.indep {e} := 
⟨loop.dep, λ h, ⟨matroid.loop_iff_dep.mpr h, he⟩⟩ 

lemma loop_iff_mem_cl_empty : M.loop e ↔ e ∈ M.cl ∅ := iff.rfl 

lemma nonloop_iff_coe (e : α) : M.nonloop e ↔ (M : matroid α).nonloop e := iff.rfl 

lemma nonloop.indep (he : M.nonloop e) : M.indep {e} := matroid.nonloop.indep he 

lemma nonloop_iff_indep : M.nonloop e ↔ M.indep {e} := matroid.nonloop_iff_indep 

lemma nonloop.mem_ground (he : M.nonloop e) : e ∈ M.E := 
singleton_subset_iff.mp he.indep.subset_ground 

lemma r_eq_coe_r (X : set α) : M.r X = (M : matroid α).r X := rfl 

lemma r_compl_ground : M.r M.Eᶜ = 0 := 
r_eq_zero_iff_subset_loops.mpr (compl_ground_subset_loops_coe _)

lemma coe_r_compl_ground (M : matroid_in α) : (M : matroid α).r M.Eᶜ = 0 := r_compl_ground
  
lemma r_eq_r_inter_ground (X : set α): 
  M.r X = M.r (X ∩ M.E) := 
by rw [←compl_compl M.E, inter_comm, ←diff_eq_compl_inter, r_eq_coe_r, r_eq_coe_r, 
    ←matroid.r_eq_r_diff_r_zero _ M.coe_r_compl_ground] 

lemma cocircuit_iff_coe (K : set α) : M.cocircuit K ↔ (M : matroid α).cocircuit K := iff.rfl 

lemma cocircuit.subset_ground (hK : M.cocircuit K) : K ⊆ M.E := 
λ x hx, matroid_in.nonloop.mem_ground (hK.nonloop_of_mem hx)

lemma hyperplane.subset_ground (hF : M.hyperplane F) : F ⊆ M.E := hF.2

-- TODO : hyperplanes, flats, cl definitions are equivalent to the usual ones. 

lemma eq_of_coe_eq_coe {M₁ M₂ : matroid_in α} (h : M₁.E = M₂.E) (h' : (M₁ : matroid α) = M₂) :
  M₁ = M₂ := 
by { ext, rw h, simp_rw [carrier_eq_coe, h'] }

lemma eq_of_base_iff_base {M₁ M₂ : matroid_in α} (h : M₁.E = M₂.E) 
(h' : ∀ B, M₁.base B ↔ M₂.base B) : M₁ = M₂ :=
by {apply matroid_in.ext, assumption, ext B, exact h' B}

end basic



variables {M₁ M₂ M : matroid_in α} {X Y I B C : set α} {e f x y : α}

-- section carrier

-- /- The lemmas in this section break the abstraction between `M` and its `carrier`, and are only
--   used for basic API setup. -/

-- lemma subset_ground_of_disjoint_loops (hX : disjoint X (M.carrier.cl ∅)) : 
--   X ⊆ M.E :=
-- (subset_compl_iff_disjoint_right.mpr hX).trans (compl_subset_comm.mp M.support) 

-- lemma mem_ground_of_nonloop (he : ¬M.carrier.loop e) : 
--   e ∈ M.E :=
-- begin
--   rw [loop_iff_mem_cl_empty] at he,
--   by_contra h',
--   rw ←mem_compl_iff at h',
--   exact he (M.support h')
-- end

-- lemma subset_ground_of_base_carrier (hB : M.carrier.base B) : 
--   B ⊆ M.E := 
-- λ e he, mem_ground_of_nonloop (hB.indep.nonloop_of_mem he)  

-- lemma subset_ground_of_indep_carrier (hI : M.carrier.indep I) : 
--   I ⊆ M.E :=
-- by {obtain ⟨B, hB, hIB⟩ := hI, exact hIB.trans (subset_ground_of_base_carrier hB)}

-- lemma indep_iff_carrier_indep :
--   M.indep I ↔ M.carrier.indep I :=
-- by simp_rw [matroid_in.indep, matroid_in.base, matroid.indep_iff_subset_base]

-- lemma r_ground_compl (M : matroid_in α) :
--   M.r (M.Eᶜ) = 0 :=
-- begin
--   refine r_eq_zero_of_loopy (λ e he, by_contra (λ he', he (mem_ground_of_nonloop _))), 
--   rwa loop_iff_r, 
-- end 

-- lemma flat_iff_carrier {F : set α} : 
--   M.flat F ↔ M.carrier.flat (F ∪ M.Eᶜ) ∧ F ⊆ M.E :=
-- begin
  
-- end 

-- -- lemma cl_eq_carrier_cl_inter_ground (M : matroid_in α) (X : set α) : 
-- --   M.cl X = M.carrier.cl X ∩ M.E :=
-- -- begin
-- --   rw [cl, flat], 
-- -- end 


-- end carrier

-- lemma base.indep (hB : M.base B) :
--   M.indep B :=
-- ⟨B, hB, subset.rfl⟩

-- lemma indep.subset_E (hI : M.indep I) : 
--   I ⊆ M.E := 
-- let ⟨B,hB,hIB⟩ := hI in hIB.trans (subset_ground_of_base_carrier hB)

-- lemma r_le_r_of_subset (M : matroid_in α) (hXY : X ⊆ Y) :
--   M.r X ≤ M.r Y :=
-- M.carrier.r_mono hXY

-- lemma indep.r (hI : M.indep I) :
--   M.r I = I.ncard :=
-- by rw [matroid_in.r, (indep_iff_carrier_indep.mp hI).r]

-- lemma empty_indep (M : matroid_in α) :
--   M.indep ∅ :=
-- M.carrier.empty_indep

-- lemma indep.subset_basis_of_subset (hI : M.indep I) (hX : I ⊆ X) :
--   ∃ J, M.basis J X ∧ I ⊆ J :=
-- begin
--   obtain ⟨J,hIJ,hJ⟩ := (indep_iff_carrier_indep.mp hI).subset_basis_of_subset hX,
--   refine ⟨J,⟨hJ.indep,hJ.subset,λ J' hJ' hJJ' hJ'X, _⟩,hIJ⟩,
--   exact hJ.eq_of_subset_indep hJ' hJJ' hJ'X,
-- -- end

-- lemma exists_basis (M : matroid_in α) (X : set α) :
--   ∃ I, M.basis I X :=
-- let ⟨I, hIX, h⟩ := M.empty_indep.subset_basis_of_subset (empty_subset X) in ⟨I,hIX⟩



section equivalence 

/-- A `matroid_in` gives a matroid on a subtype -/
def to_matroid_of_ground_eq (M : matroid_in α) (hX : M.E = X) : 
  matroid X :=
{ base := (M : matroid α).base ∘ (set.image coe),
  exists_base' := begin
    obtain ⟨B,hB⟩ := M.exists_base,
    refine ⟨coe ⁻¹' B, _⟩, 
    rwa [function.comp_app, subtype.image_preimage_coe, ←matroid_in.base, ←hX, 
      inter_eq_left_iff_subset.mpr hB.subset_ground],
  end,
  base_exchange' := begin
    subst hX,
    rintro B₁ B₂ hB₁ hB₂ a ha,
    simp only [function.comp_app] at hB₁ hB₂ ⊢,

    have ha' : (a : α) ∈ (coe '' B₁) \ (coe '' B₂),
    { rw [←image_diff (subtype.coe_injective), mem_image], exact ⟨a,ha,rfl⟩},
    obtain ⟨y,hy,hy'⟩ :=  hB₁.exchange hB₂ ha',
    refine ⟨⟨y, mem_ground_of_nonloop_coe (hB₂.indep.nonloop_of_mem hy.1)⟩, _, _⟩,
    { simp only [←image_diff (subtype.coe_injective), mem_image,
        subtype.exists, subtype.coe_mk, exists_and_distrib_right, exists_eq_right] at hy,
      obtain ⟨hy'',h_eq⟩ := hy,
      exact h_eq},
    rwa [image_insert_eq, image_diff subtype.coe_injective, image_singleton],
  end }

def to_matroid (M : matroid_in α) : matroid (M.E) := M.to_matroid_of_ground_eq rfl 

/-- A `matroid` on a subtype gives a `matroid_in` -/
def of_matroid_in {E : set α} (M : matroid E) :
  matroid_in α :=
{ E := E,
  carrier := 
  { base := λ B, M.base (coe ⁻¹' B) ∧ B ⊆ E ,
    exists_base' := 
    (begin
      obtain ⟨B,hB⟩ := M.exists_base,
      refine ⟨coe '' B, by rwa [preimage_image_eq _ subtype.coe_injective], _⟩,
      simp only [image_subset_iff, subtype.coe_preimage_self, subset_univ],
    end),
    base_exchange' :=
    begin
      rintro B₁ B₂ ⟨hB₁,hB₁ss⟩ ⟨hB₂,hB₂ss⟩ x hx, 
      set x' : E := ⟨x, hB₁ss hx.1⟩ with hx'_def, 
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
    rintro e he,  
    rw [←matroid.loop_iff_mem_cl_empty, matroid.loop_iff_not_mem_base_forall],
    rintro B ⟨-,hB⟩ heB, 
    exact he (hB heB), 
  end) }

/-- A `matroid_in α` with E set `X` is the same thing as a `matroid X`-/
def matroid_in_equiv_subtype {E : set α} : 
  {M : matroid_in α // M.E = E} ≃ matroid E := 
{ to_fun := λ M, to_matroid_of_ground_eq M.1 M.2,
  inv_fun := λ M, ⟨of_matroid_in M, rfl⟩, 
  left_inv := begin
    rintro ⟨M, hM⟩, 
    subst hM, 
    ext, refl, 
    simp only [function.comp_app, subtype.image_preimage_coe, of_matroid_in, 
      to_matroid_of_ground_eq, subtype.coe_mk, carrier_eq_coe, ←base_iff_coe ], 
    split, 
    { rintro ⟨hB, hBG⟩, convert hB, rwa [eq_comm, inter_eq_left_iff_subset]},
    intro hB,
    rw [inter_eq_left_iff_subset.mpr hB.subset_ground],
    exact ⟨hB, hB.subset_ground⟩,
  end,
  right_inv := begin
    rintro M, 
    ext B, 
    simp only [of_matroid_in, to_matroid_of_ground_eq, ←carrier_eq_coe, function.comp_app, 
      image_subset_iff, subtype.coe_preimage_self, subset_univ, and_true, 
      preimage_image_eq _ (subtype.coe_injective)], 
  end }




@[simp] lemma matroid_in_equiv_subtype_apply_base {E : set α} {B : set E} 
(M : {M : matroid_in α // M.E = E}) :
  (matroid_in_equiv_subtype M).base B ↔ (M : matroid_in α).base (coe '' B) := 
by simp only [matroid_in_equiv_subtype, to_matroid_of_ground_eq, matroid_in.base, 
  subtype.val_eq_coe, equiv.coe_fn_mk]

@[simp] lemma matroid_in_equiv_subtype_apply_symm_base {B E : set α} (M : matroid E) :
  (matroid_in_equiv_subtype.symm M : matroid_in α).base B ↔ M.base (coe ⁻¹' B) ∧ B ⊆ E :=
by { rw [matroid_in_equiv_subtype, equiv.coe_fn_symm_mk, subtype.coe_mk, of_matroid_in ], refl } 

end equivalence

/-
@[simp] lemma matroid_in_equiv_subtype_apply_indep {E : set α} {I : set E} 
(M : {M : matroid_in α // M.E = E}) :
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
  exact inter_eq_left_iff_subset.mpr (hB.indep.subset_E), 
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
(M : {M : matroid_in α // M.E = E}) (X : set E) : 
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
    { simpa using hJ.subset_E},
    { convert hJ, simpa using hJ.subset_E},
    { simpa using hIJ },
    rw [←preimage_image_eq X subtype.coe_injective, preimage_subset_preimage_iff],
    { exact hJX},
    simp only [subtype.range_coe_subtype, set_of_mem_eq, hJ.subset_E]},
  rw [←hI'.r, hI'.indep.r, ncard_image_of_injective _ subtype.coe_injective], 
end 

@[simp] lemma matroid_in_equiv_subtype_apply_symm_r {X E : set α} (M : matroid E) :
  (matroid_in_equiv_subtype.symm M : matroid_in α).r X = M.r (coe ⁻¹' X) :=
begin
  set M' := (matroid_in_equiv_subtype.symm M) with hM', 
  rw [r_eq_r_inter_E, ←preimage_inter_range, subtype.range_coe], 
  set X' := X ∩ (M' : matroid_in α).E with hX'_def, 
  have hX' : coe '' (coe ⁻¹' X' : set E) = X', 
  { rw image_preimage_eq_iff, simp [hX'_def], convert inter_subset_right _ _},
  rw [←hX', ←matroid_in_equiv_subtype_apply_r, hM', equiv.apply_symm_apply], 
  refl, 
end 

lemma eq_coe_image_preimage {E : set α} (M : matroid_in α) (h : M.E = E): 
  M = matroid_in_equiv_subtype.symm (matroid_in_equiv_subtype ⟨M, h⟩) := 
by simp only [equiv.symm_apply_apply, subtype.coe_mk]

-/

/-
end equivalence 

section ext

lemma eq_of_indep_iff_indep {M₁ M₂ : matroid_in E} (h : M₁.E = M₂.E) 
(h' : ∀ I, M₁.indep I ↔ M₂.indep I) : 
  M₁ = M₂ :=
begin
  rw [eq_coe_image_preimage M₁ h], 
  convert (eq_coe_image_preimage M₂ (rfl : M₂.E = M₂.E)).symm using 3, 
  refine eq_of_indep_iff_indep_forall (λ I, _), 
  simp_rw [matroid_in_equiv_subtype_apply_indep, subtype.coe_mk, h'], 
end 

lemma eq_of_r_eq_r {M₁ M₂ : matroid_in E} (h : M₁.E = M₂.E) 
(h' : ∀ X, M₁.r X = M₂.r X) : 
  M₁ = M₂ :=
begin
  rw [eq_coe_image_preimage M₁ h], 
  convert (eq_coe_image_preimage M₂ (rfl : M₂.E = M₂.E)).symm using 3, 
  refine eq_of_r_eq_r_forall (λ I, _), 
  simp_rw [matroid_in_equiv_subtype_apply_r, subtype.coe_mk, h'], 
end 




end ext 

-/

section dual

/-- The dual of a `matroid_in` -/
def dual (M : matroid_in α) : matroid_in α :=
  matroid_in_equiv_subtype.symm (matroid_in_equiv_subtype ⟨M, rfl⟩).dual

-- def dual (M : matroid_in α)

reserve postfix `*` :90 

notation (name := matroid_in_dual) M* := matroid_in.dual M 

lemma dual_base_iff : 
  M*.base B ↔ M.base (M.E \ B) ∧ B ⊆ M.E :=
by { simp [dual, image_compl_preimage], }

@[simp] lemma dual_E (M : matroid_in α): 
  M*.E = M.E := 
rfl 

@[simp] lemma dual_dual (M : matroid_in α) :
  M** = M :=
begin
  apply eq_of_base_iff_base _ (λ B, _),
    simp, 
  simp only [dual_base_iff, dual_E, sdiff_sdiff_right_self, inf_eq_inter], 
  split, 
  { rintro ⟨⟨h, -⟩, hB⟩, rwa [inter_eq_right_iff_subset.mpr hB] at h},
  intro hB, 
  have h := hB.indep.subset_ground, 
  exact ⟨⟨by rwa inter_eq_right_iff_subset.mpr h, diff_subset _ _⟩, h⟩, 
end 

end dual



end matroid_in

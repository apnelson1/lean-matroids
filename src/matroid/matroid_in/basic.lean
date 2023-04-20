import ..pseudominor
import ..connectivity
import ..maps.equiv

open_locale classical
noncomputable theory

open matroid set subtype

variables {E α : Type*}

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
@[ext] structure matroid_in (α : Type*) :=
(ground : set α)
(carrier : matroid α)
(support : groundᶜ ⊆ carrier.cl ∅)

namespace matroid_in

instance {α : Type*} : has_coe (matroid_in α) (matroid α) := ⟨λ M, M.carrier⟩

@[simp] lemma carrier_eq_coe {M : matroid_in α} : M.carrier = (M : matroid α) := rfl

def E (M : matroid_in α) := M.ground

@[simp] lemma ground_eq_E (M : matroid_in α) : M.ground = M.E := rfl

section defs
/- Definitions -/

variables (M : matroid_in α)

def base (B : set α) : Prop := (M : matroid α).base B

def indep (I : set α) : Prop := (M : matroid α).indep I
  -- ∃ B, M.base B ∧ I ⊆ B

def basis (I X : set α) : Prop := (M : matroid α).basis I X ∧ X ⊆ M.E
  -- M.indep I ∧ I ⊆ X ∧ ∀ J, M.indep J → I ⊆ J → J ⊆ X → I = J

def circuit (C : set α) : Prop := (M : matroid α).circuit C ∧ C ⊆ M.E
  -- ¬M.indep C ∧ ∀ I ⊂ C, M.indep I

def r (X : set α) : ℕ := (M : matroid α).r X
  -- M.carrier.r X

def rk (M : matroid_in α) : ℕ := (M : matroid α).rk

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

def coindep (X : set α) : Prop := (M : matroid α).coindep X ∧ X ⊆ M.E

def skew (X Y : set α) : Prop := (M : matroid α).skew X Y ∧ X ⊆ M.E ∧ Y ⊆ M.E

class finite_rk (M : matroid_in α) : Prop := (fin : finite_rk (M : matroid α)) 

instance finite_rk.to_coe (M : matroid_in α) [finite_rk M] : 
  (M : matroid α).finite_rk := ‹finite_rk M›.fin  

end defs

section basic

variables {M : matroid_in α} {X Y I C B F H K : set α} {e f : α}

lemma loop_coe_of_not_mem_ground (h : e ∉ M.E) : (M : matroid α).loop e := M.support (mem_compl h)

lemma mem_ground_of_nonloop_coe (h : (M : matroid α).nonloop e) : e ∈ M.E :=
by_contra (λ he, h (M.support he))

lemma compl_ground_subset_loops_coe (M : matroid_in α) : M.Eᶜ ⊆ (M : matroid α).cl ∅ := M.support

lemma subset_ground_of_disjoint_loops_coe (hX : disjoint X ((M : matroid α).cl ∅)) : X ⊆ M.E :=
hX.subset_compl_right.trans (compl_subset_comm.mp M.support)

lemma subset_loops_coe_of_disjoint_ground (hX : disjoint X M.E) : X ⊆ (M : matroid α).cl ∅ :=
hX.subset_compl_right.trans (compl_ground_subset_loops_coe _)

-- ### Independence

lemma indep.subset_ground (hI : M.indep I) : I ⊆ M.E :=
  subset_ground_of_disjoint_loops_coe (matroid.indep.disjoint_loops hI)

lemma base_iff_coe : M.base B ↔ (M : matroid α).base B := iff.rfl

lemma base.to_coe (hB : M.base B) : (M : matroid α).base B := hB

lemma exists_base (M : matroid_in α) : ∃ B, M.base B := matroid.exists_base M

lemma base.indep (hB : M.base B) : M.indep B := matroid.base.indep hB

lemma base.subset_ground (hB : M.base B) : B ⊆ M.E := hB.indep.subset_ground

lemma base.finite [finite_rk M] (hB : M.base B) : B.finite := hB.to_coe.finite 

lemma indep_iff_coe : M.indep I ↔ (M : matroid α).indep I := iff.rfl

lemma indep.to_coe (hI : M.indep I) : (M : matroid α).indep I := hI

lemma indep_iff_subset_base : M.indep I ↔ ∃ B, M.base B ∧ I ⊆ B := iff.rfl

lemma indep.subset (hI : M.indep I) (hX : X ⊆ I) : M.indep X := matroid.indep.subset hI hX

lemma indep.r (hI : M.indep I) : M.r I = I.ncard := matroid.indep.r hI

lemma indep_iff_r_eq_card [finite α] : M.indep I ↔ M.r I = I.ncard := matroid.indep_iff_r_eq_card

lemma indep.subset_basis_of_subset (hI : M.indep I) (hIX : I ⊆ X) (hX : X ⊆ M.E) :
  ∃ J, I ⊆ J ∧ M.basis J X :=
begin
  obtain ⟨J, hIJ, hJ⟩ := matroid.indep.subset_basis_of_subset hI hIX,
  exact ⟨J, hIJ, ⟨hJ, hX⟩⟩,
end
-- matroid.indep.subset_basis_of_subset hI hIX

lemma circuit.subset_ground (hC : M.circuit C) : C ⊆ M.E := hC.2

lemma circuit_iff : M.circuit C ↔ (¬ M.indep C ∧ (∀ I ⊂ C, M.indep I)) ∧ C ⊆ M.E :=
by { rw [circuit, matroid.circuit_iff], refl }

lemma basis.to_coe (h : M.basis I X) : (M : matroid α).basis I X := h.1

lemma basis.indep (hIX : M.basis I X) : M.indep I := matroid.basis.indep hIX.1

lemma basis.subset (hIX : M.basis I X) : I ⊆ X := matroid.basis.subset hIX.1

lemma basis.subset_ground (hIX : M.basis I X) : X ⊆ M.E := hIX.2

lemma exists_basis (M : matroid_in α) (hX : X ⊆ M.E) : ∃ I, M.basis I X :=
by { obtain ⟨I, hI⟩ := matroid.exists_basis (M : matroid α) X,   exact ⟨I, hI, hX⟩ }

lemma basis.r (hIX : M.basis I X) : M.r I = M.r X := matroid.basis.r hIX.1

-- ### Closure and flats

lemma cl_eq_coe_cl_inter (M : matroid_in α) (X : set α) : M.cl X = (M : matroid α).cl X ∩ M.E := rfl

lemma cl_coe_eq (M : matroid_in α) (X : set α) : (M : matroid α).cl X = M.cl X ∪ M.Eᶜ :=
begin
  rw [cl, union_distrib_right, union_compl_self, inter_univ, eq_comm, union_eq_left_iff_subset],
  refine subset_trans _ ((M : matroid α).cl_mono (empty_subset X)),
  exact compl_ground_subset_loops_coe _,
end

lemma cl_subset_ground (M : matroid_in α) (X : set α) : M.cl X ⊆ M.E := inter_subset_right _ _

lemma subset_cl (hX : X ⊆ M.E) : X ⊆ M.cl X := subset_inter (matroid.subset_cl M X) hX

lemma cl_subset_coe_cl (M : matroid_in α) (X : set α) : M.cl X ⊆ (M : matroid α).cl X :=
inter_subset_left _ _

lemma cl_mono (M : matroid_in α) (hXY : X ⊆ Y) : M.cl X ⊆ M.cl Y :=
subset_inter ((M.cl_subset_coe_cl _).trans (matroid.cl_mono M hXY)) (cl_subset_ground _ _)

lemma cl_eq_cl_inter_ground (M : matroid_in α) (X : set α) : M.cl X = M.cl (X ∩ M.E) :=
begin
  refine (M.cl_mono (inter_subset_left _ _)).antisymm' _,
  rw [cl, cl, ←union_empty (X ∩ M.E), ←cl_union_cl_right_eq_cl_union],
  refine inter_subset_inter_left _ ((M : matroid α).cl_mono _),
  rw [union_distrib_right],
  refine subset_inter (subset_union_left _ _) ((subset_univ X).trans _),
  refine (union_compl_self M.E).symm.trans_subset (union_subset_union_right _ _),
  exact compl_ground_subset_loops_coe _,
end

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

lemma basis.subset_cl (hIX : M.basis I X) : X ⊆ M.cl I :=
subset_inter (matroid.basis.subset_cl hIX.1) hIX.subset_ground

lemma flat.subset_ground (hF : M.flat F) : F ⊆ M.E := hF.2

lemma flat.cl (hF : M.flat F) : M.cl F = F :=
begin
  refine (subset_cl hF.subset_ground).antisymm' _,
  convert inter_subset_inter_left M.E hF.1.cl.subset using 1,
  { convert rfl using 2,
    rw [←cl_union_cl_right_eq_cl_union, cl_eq_loops_of_subset (compl_ground_subset_loops_coe _),
      cl_union_cl_right_eq_cl_union, union_empty] },
  rw [inter_distrib_right, inter_eq_left_iff_subset.mpr hF.subset_ground, compl_inter_self,
    union_empty],
end

-- ### loops and nonloops

lemma loop.mem_ground (he : M.loop e) : e ∈ M.E := he.2

lemma loop.dep (he : M.loop e) : ¬ M.indep {e} := matroid.loop.dep he.1

lemma loop.to_coe (he : M.loop e) : (M : matroid α).loop e := he.1

lemma loop_iff_dep (he : e ∈ M.E) : M.loop e ↔ ¬ M.indep {e} :=
⟨loop.dep, λ h, ⟨matroid.loop_iff_dep.mpr h, he⟩⟩

lemma loop_iff_mem_cl_empty : M.loop e ↔ e ∈ M.cl ∅ := iff.rfl

lemma nonloop_iff_coe (e : α) : M.nonloop e ↔ (M : matroid α).nonloop e := iff.rfl

lemma nonloop.to_coe (he : M.nonloop e) : (M : matroid α).nonloop e := he

@[simp] lemma indep_singleton : M.indep {e} ↔ M.nonloop e := matroid.indep_singleton

alias indep_singleton ↔ indep.nonloop nonloop.indep

attribute [protected] indep.nonloop nonloop.indep

lemma nonloop.mem_ground (he : M.nonloop e) : e ∈ M.E :=
singleton_subset_iff.mp he.indep.subset_ground

lemma nonloop_of_not_mem_cl (he : e ∈ M.E) (h : e ∉ M.cl X) : M.nonloop e :=
nonloop_of_not_mem_cl (λ h', h ⟨h',he⟩)

-- ### rank

lemma le_r_iff {n : ℕ} [finite α] : n ≤ M.r X ↔ ∃ I ⊆ X, M.indep I ∧ I.ncard = n := matroid.le_r_iff

lemma r_le_iff {n : ℕ} [finite α] : M.r X ≤ n ↔ ∀ I ⊆ X, M.indep I → I.ncard ≤ n := matroid.r_le_iff

lemma r_eq_coe_r (X : set α) : M.r X = (M : matroid α).r X := rfl

lemma r_compl_ground : M.r M.Eᶜ = 0 :=
r_eq_zero_of_subset_loops (compl_ground_subset_loops_coe _)

lemma coe_r_compl_ground (M : matroid_in α) : (M : matroid α).r M.Eᶜ = 0 := r_compl_ground

lemma r_eq_r_inter_ground (X : set α):
  M.r X = M.r (X ∩ M.E) :=
by rw [r_eq_coe_r, ←matroid.r_cl, 
    ←matroid.cl_diff_eq_cl_of_subset_loops (M.compl_ground_subset_loops_coe) X, 
    diff_eq, compl_compl, matroid.r_cl, ←r_eq_coe_r ]

lemma rk_eq_rk_coe (M : matroid_in α) : M.rk = (M : matroid α).rk := rfl

lemma rk_eq_r_ground (M : matroid_in α) : M.rk = M.r M.E :=
by rw [rk, matroid.rk_def, ←r_eq_coe_r, r_eq_r_inter_ground, univ_inter]


-- ### Cocircuits etc

lemma cocircuit_iff_coe (K : set α) : M.cocircuit K ↔ (M : matroid α).cocircuit K := iff.rfl

lemma cocircuit.subset_ground (hK : M.cocircuit K) : K ⊆ M.E :=
λ x hx, matroid_in.nonloop.mem_ground (hK.nonloop_of_mem hx)

lemma hyperplane.subset_ground (hF : M.hyperplane F) : F ⊆ M.E := hF.2

lemma coindep.subset_ground (hX : M.coindep X) : X ⊆ M.E := hX.2

lemma coindep_iff_disjoint_base : M.coindep X ↔ ∃ B, M.base B ∧ X ⊆ M.E \ B :=
by { simp_rw [coindep, matroid.coindep_iff_disjoint_base, ←base_iff_coe, subset_diff], tauto }

lemma coindep.to_coe (h : M.coindep X) : (M : matroid α).coindep X := h.1

lemma coindep_forall_subset_not_cocircuit (hX : X ⊆ M.E) :
  M.coindep X ↔ ∀ ⦃K⦄, K ⊆ X → ¬ M.cocircuit K :=
by simp_rw [coindep, matroid.coindep_iff_forall_subset_not_cocircuit, iff_true_intro hX, and_true, 
    cocircuit]

lemma coindep_iff_cl_compl_eq_ground (hX : X ⊆ M.E) : M.coindep X ↔ M.cl (M.E \ X) = M.E :=
begin
  rw [coindep, matroid.coindep_iff_cl_compl_eq_univ, cl_coe_eq, cl_eq_cl_inter_ground,
    ←diff_eq_compl_inter, ← (true_iff _).mpr hX, and_true],
  refine ⟨λ hu, (cl_subset_ground _ _).antisymm _, λ h, _⟩,
  { rwa [←compl_compl (M.cl _), ←compl_inter, ←compl_inj_iff, compl_univ, compl_compl,
      ←disjoint_iff_inter_eq_empty, disjoint_compl_left_iff_subset] at hu },
  rw [h, union_compl_self],
end

-- ### Skewness

lemma skew.to_coe (h : M.skew X Y) : (M : matroid α).skew X Y := h.1

lemma skew.left_subset_ground (h : M.skew X Y) : X ⊆ M.E := h.2.1

lemma skew.right_subset_ground (h : M.skew X Y) : Y ⊆ M.E := h.2.2

lemma skew.symm (h : M.skew X Y) : M.skew Y X := ⟨h.to_coe.symm, h.2.2, h.2.1⟩

lemma skew.comm : M.skew X Y ↔ M.skew Y X := ⟨skew.symm, skew.symm⟩

lemma skew.subset_left (h : M.skew X Y) {X' : set α} (hX'X : X' ⊆ X) : M.skew X' Y :=
⟨h.to_coe.subset_left hX'X, hX'X.trans h.2.1, h.2.2⟩

lemma skew.subset_right (h : M.skew X Y) {Y' : set α} (hY'Y : Y' ⊆ Y) : M.skew X Y' :=
⟨h.to_coe.subset_right hY'Y, h.2.1, hY'Y.trans h.2.2⟩

lemma skew.r_add [finite_rk M] (h : M.skew X Y) : M.r X + M.r Y = M.r (X ∪ Y) := h.to_coe.r_add

lemma skew_iff_r [finite_rk M] (hX : X ⊆ M.E) (hY : Y ⊆ M.E) : 
  M.skew X Y ↔ M.r X + M.r Y = M.r (X ∪ Y) :=
⟨skew.r_add, λ h, ⟨matroid.skew_iff_r.mpr h, hX,hY⟩⟩

lemma skew.cl_left (h : M.skew X Y) : M.skew (M.cl X) Y :=
⟨h.to_coe.cl_left.subset_left (M.cl_subset_coe_cl _), M.cl_subset_ground X, h.2.2⟩

lemma skew.cl_right (h : M.skew X Y) : M.skew X (M.cl Y) := (h.symm.cl_left).symm

lemma nonloop.singleton_skew_iff (he : M.nonloop e) (hX : X ⊆ M.E) : M.skew {e} X ↔ e ∉ M.cl X :=
by rw [skew, he.to_coe.singleton_skew_iff, singleton_subset_iff, cl_eq_coe_cl_inter, mem_inter_iff,
    ←(true_iff _).mpr hX, and_true, ←(true_iff _).mpr he.mem_ground, and_true, and_true]

lemma nonloop.skew_singleton_iff (he : M.nonloop e) (hX : X ⊆ M.E) : M.skew X {e} ↔ e ∉ M.cl X :=
by rw [skew.comm, he.singleton_skew_iff hX]


-- TODO : hyperplanes, flats, cl definitions are equivalent to the usual ones.

lemma eq_of_coe_eq_coe {M₁ M₂ : matroid_in α} (h : M₁.E = M₂.E) (h' : (M₁ : matroid α) = M₂) :
  M₁ = M₂ :=
by { ext, rw [ground_eq_E,h,ground_eq_E], simp_rw [carrier_eq_coe, h'] }

-- lemma eq_iff_coe_eq_coe {M₁ M₂ : matroid_in α} :
--   M₁ = M₂ ↔ M₁.E = M₂.E ∧ (M₁ : matroid α) = M₂ :=


end basic

variables {M₁ M₂ M : matroid_in α} {X Y I B C : set α} {e f x y : α}

section equivalence



/-- A `matroid_in` gives a matroid on a subtype -/
def to_matroid (M : matroid_in α) : matroid M.E := 
  (M : matroid α).preimage (function.embedding.subtype M.E)

def to_matroid_of_ground_eq (M : matroid_in α) (hX : M.E = X) : matroid X := 
M.to_matroid.congr_equiv (equiv.set_congr hX)

/-- A `matroid` on a subtype gives a `matroid_in` -/
def to_matroid_in {E : set α} (M : matroid E) : matroid_in α := 
⟨E, M.image (function.embedding.subtype E), 
begin
  intros e he, 
  rw [←matroid.loop_iff_mem_cl_empty, matroid.loop_iff_dep, image_indep_iff], 
  push_neg, 
  simp only [function.embedding.coe_subtype, ne.def], 
  refine λ I hI hi, he _,  
  rw [←@subtype.range_coe _ E, ←singleton_subset_iff, hi],
  exact image_subset_range _ _,  
end⟩ 
  
/-- A `matroid_in α` with ground set `E` is the same thing as a `matroid `-/
def matroid_in_equiv_subtype {E : set α} :
  {M : matroid_in α // M.E = E} ≃ matroid E :=
{ to_fun := λ M, to_matroid_of_ground_eq (M : matroid_in α) M.2,
  inv_fun := λ M, ⟨to_matroid_in M, rfl⟩,
  left_inv := begin 
    rintro ⟨M, rfl⟩, simp [to_matroid_of_ground_eq, to_matroid_in], 
    apply matroid_in.ext, refl, 
    apply eq_of_indep_iff_indep_forall (λ I, _),
    simp only [image_indep_iff, congr_equiv_apply_indep, function.embedding.coe_subtype, 
      carrier_eq_coe, to_matroid],  
    simp only [preimage_indep_iff, function.embedding.coe_subtype] at *, 
    split, 
    { rintro ⟨I, hI, rfl⟩, convert hI, ext, simp },
    refine λ h, ⟨coe ⁻¹' I, _, _⟩,  
    { convert h, ext,
      simp only [mem_image, mem_preimage, equiv.set_congr_apply, set_coe.exists, coe_mk, 
        exists_prop, exists_eq_right_right, and_iff_right_iff_imp],  
      exact λ h', indep.subset_ground h h' },
    rw [image_preimage_coe, ground_eq_E, eq_comm, inter_eq_left_iff_subset], 
    exact indep.subset_ground h, 
  end,
  right_inv := begin
    rintro M,
    ext B, 
    simp [to_matroid, to_matroid_of_ground_eq, to_matroid_in], 
    convert iff.rfl, 
    simp only [of_matroid_in, to_matroid_of_ground_eq, ←carrier_eq_coe, function.comp_app,
      image_subset_iff, subtype.coe_preimage_self, subset_univ, and_true,
      preimage_image_eq _ subtype.coe_injective],
  end }




-- matroid_of_base 
-- (λ B, (M : matroid α).base (coe '' B))
-- (exists.elim M.exists_base (λ B hB, ⟨coe ⁻¹' B, 
--   by rwa [subtype.image_preimage_coe, ←matroid_in.base, ←hX, 
--     inter_eq_left_iff_subset.mpr hB.subset_ground]⟩))
-- (begin
--     subst hX,
--     rintro B₁ B₂ hB₁ hB₂ a ha,
--     simp only [function.comp_app] at hB₁ hB₂ ⊢,

--     have ha' : (a : α) ∈ (coe '' B₁) \ (coe '' B₂),
--     { rw [←image_diff (subtype.coe_injective), mem_image], exact ⟨a,ha,rfl⟩},
--     obtain ⟨y,hy,hy'⟩ :=  hB₁.exchange hB₂ ha',
--     refine ⟨⟨y, mem_ground_of_nonloop_coe (hB₂.indep.nonloop_of_mem hy.1)⟩, _, _⟩,
--     { simp only [←image_diff (subtype.coe_injective), mem_image,
--         subtype.exists, subtype.coe_mk, exists_and_distrib_right, exists_eq_right] at hy,
--       obtain ⟨hy'',h_eq⟩ := hy,
--       exact h_eq},
--     rwa [image_insert_eq, image_diff subtype.coe_injective, image_singleton],
--   end)
--   (begin
--     subst hX, 
--     rintro I Y ⟨B, hB, hIB⟩ hIY, 
--     obtain ⟨J, hIJ, hJ⟩ :=
--       (hB.indep.subset (image_subset _ hIB)).subset_basis_of_subset (image_subset _ hIY), 
--     obtain ⟨BJ, hBJ, hJBJ⟩ := hJ.indep.exists_base_supset, 
--     refine ⟨coe ⁻¹' J, ⟨⟨coe ⁻¹' BJ,_,preimage_mono hJBJ⟩,_,_⟩, _⟩,  
--     { convert hBJ, rw [image_preimage_coe, inter_eq_left_iff_subset],
--       exact base.subset_ground hBJ },
--     { convert preimage_mono hIJ, rw [preimage_image_eq _ coe_injective] },
--     { convert preimage_mono hJ.subset, rw [preimage_image_eq _ coe_injective] },
--     rintro K ⟨⟨BK, hBK, hKBK⟩, hIK, hKY⟩  hJK,
--     rw @basis.eq_of_subset_indep _ _ _ (coe '' K) _ hJ,  
--     { rw [preimage_image_eq _ coe_injective] },
--     { exact hBK.indep.subset (image_subset _ hKBK) },
--     { convert image_subset _ hJK, rw [image_preimage_coe, eq_comm, inter_eq_left_iff_subset],
--       exact indep.subset_ground (hBJ.indep.subset hJBJ) },
--     exact image_subset _ hKY, 
--   end)

-- def to_matroid (M : matroid_in α) : matroid (M.E) := M.to_matroid_of_ground_eq rfl

-- /-- A `matroid` on a subtype gives a `matroid_in` -/
-- def of_matroid_in {E : set α} (M : matroid E) :
--   matroid_in α :=
-- { ground := E,
--   carrier :=
--   matroid_of_base (λ B, M.base (coe ⁻¹' B) ∧ B ⊆ E)
--     (begin
--       obtain ⟨B,hB⟩ := M.exists_base,
--       refine ⟨coe '' B, by rwa [preimage_image_eq _ subtype.coe_injective], _⟩,
--       simp only [image_subset_iff, subtype.coe_preimage_self, subset_univ],
--     end)

--   (begin
--       rintro B₁ B₂ ⟨hB₁, hB₁ss⟩ ⟨hB₂, hB₂ss⟩ x hx,
--       set x' : E := ⟨x, hB₁ss hx.1⟩ with hx'_def,
--       have hxx' : x = coe x', rw [hx'_def, subtype.coe_mk],
--       rw [hxx', ←mem_preimage, preimage_diff] at hx,
--       obtain ⟨y, hy, hBy⟩ := hB₁.exchange hB₂ hx,
--       rw [←preimage_diff, mem_preimage] at hy,
--       refine ⟨y, hy, _, _⟩,
--       { rw [←singleton_union, preimage_union, preimage_diff], rw [←singleton_union] at hBy,
--         convert hBy using 2,
--         { ext, simp [subtype.coe_inj]},
--         convert rfl using 2,
--         { ext, rw [hx'_def], simp only [mem_singleton_iff, subtype.coe_mk, mem_preimage],
--           simp_rw [hxx'], rw [subtype.coe_inj], refl}},
--       rw insert_subset,
--       exact ⟨y.2, (diff_subset _ _).trans hB₁ss⟩,
--     end)
--     (sorry ),
--   support := λ e he, begin
--     rw [←matroid.loop_iff_mem_cl_empty, matroid.loop_iff_not_mem_base_forall],
--     rintro B ⟨-,hB⟩ heB,
--     exact he (hB heB),
--   end }

-- /-- A `matroid_in α` with ground set `X` is the same thing as a `matroid X`-/
-- def matroid_in_equiv_subtype {E : set α} :
--   {M : matroid_in α // M.E = E} ≃ matroid E :=
-- { to_fun := λ M, to_matroid_of_ground_eq M.1 M.2,
--   inv_fun := λ M, ⟨of_matroid_in M, rfl⟩,
--   left_inv := begin
--     rintro ⟨M, hM⟩,
--     subst hM,
--     ext, refl,
--     simp only [function.comp_app, subtype.image_preimage_coe, of_matroid_in,
--       to_matroid_of_ground_eq, subtype.coe_mk, carrier_eq_coe, ←base_iff_coe],
--     refine ⟨_, λ hB, _⟩,
--     { rintro ⟨hB, hBG⟩, convert hB, rwa [eq_comm, inter_eq_left_iff_subset] },
--     rw [inter_eq_left_iff_subset.mpr hB.subset_ground],
--     exact ⟨hB, hB.subset_ground⟩,
--   end,
--   right_inv := begin
--     rintro M,
--     ext B,
--     simp only [of_matroid_in, to_matroid_of_ground_eq, ←carrier_eq_coe, function.comp_app,
--       image_subset_iff, subtype.coe_preimage_self, subset_univ, and_true,
--       preimage_image_eq _ subtype.coe_injective],
--   end }

@[simp] lemma matroid_in_equiv_subtype_apply_base {E : set α} {B : set E}
  (M : {M : matroid_in α // M.E = E}) :
  (matroid_in_equiv_subtype M).base B ↔ (M : matroid_in α).base (coe '' B) :=
by simp only [matroid_in_equiv_subtype, to_matroid_of_ground_eq, matroid_in.base,
  subtype.val_eq_coe, equiv.coe_fn_mk]

@[simp] lemma matroid_in_equiv_subtype_apply_symm_base {B E : set α} (M : matroid E) :
  (matroid_in_equiv_subtype.symm M : matroid_in α).base B ↔ M.base (coe ⁻¹' B) ∧ B ⊆ E :=
by { rw [matroid_in_equiv_subtype, equiv.coe_fn_symm_mk, subtype.coe_mk, of_matroid_in ], refl }

@[simp] lemma matroid_in_equiv_subtype_apply_indep {E : set α} {I : set E}
  (M : {M : matroid_in α // M.E = E}) :
  (matroid_in_equiv_subtype M).indep I ↔ (M : matroid_in α).indep (coe '' I) :=
begin
  simp_rw [indep_iff_subset_base, matroid.indep_iff_subset_base,
    matroid_in_equiv_subtype_apply_base, image_subset_iff],
  refine ⟨λ ⟨B, hB, hIB⟩, ⟨_, hB, by rwa preimage_image_eq _ coe_injective⟩, _⟩,
  rintro ⟨B, hB, hIB⟩,
  refine ⟨_,_,hIB⟩,
  simp_rw [image_preimage_coe, ←M.2, val_eq_coe,
    inter_eq_left_iff_subset.mpr (matroid_in.base.subset_ground hB)],
  assumption,
end

@[simp] lemma matroid_in_equiv_subtype_apply_symm_indep {I E : set α} (M : matroid E) :
  (matroid_in_equiv_subtype.symm M : matroid_in α).indep I ↔ M.indep (coe ⁻¹' I) ∧ I ⊆ E :=
begin
  simp_rw [matroid.indep_iff_subset_base, indep_iff_subset_base,
    matroid_in_equiv_subtype_apply_symm_base],
  refine ⟨λ ⟨B, ⟨hB, hBE⟩, hIB⟩, ⟨⟨_,hB,preimage_mono hIB⟩, hIB.trans hBE⟩, _⟩,
  rintro ⟨⟨B, hB, hIB⟩, hIE⟩,
  refine ⟨coe '' B, ⟨by rwa preimage_image_eq _ coe_injective,by simp⟩, _⟩,
  convert (image_subset_image_iff coe_injective).mpr hIB,
  rwa [eq_comm,image_preimage_eq_iff, range_coe_subtype],
end

@[simp] lemma matroid_in_equiv_subtype_apply_r {E : set α}
  (M : {M : matroid_in α // M.E = E}) (X : set E) :
  (matroid_in_equiv_subtype M).r X = (M : matroid_in α).r (coe '' X) :=
begin
  apply eq_of_forall_ge_iff,
  simp_rw [r_le_iff, matroid.r_le_iff, matroid_in_equiv_subtype_apply_indep],
  refine λ c, ⟨λ h I hIX hI, _,λ h I hIX hI, _⟩,
  { convert h (coe ⁻¹' I) _ _ using 1,
    { rw ncard_preimage_of_injective_subset_range coe_injective,
      rw [range_coe_subtype, ←M.2],
      exact indep.subset_ground hI },
    { convert preimage_mono hIX,
      rw preimage_image_eq _ coe_injective },
    rwa [image_preimage_coe, inter_eq_left_iff_subset.mpr],
    rw ←M.2, exact indep.subset_ground hI },
  convert h _ (image_subset _ hIX) hI using 1,
  rw ncard_image_of_injective _ coe_injective,
end

@[simp] lemma matroid_in_equiv_subtype_apply_symm_r {X E : set α} (M : matroid E) :
  (matroid_in_equiv_subtype.symm M : matroid_in α).r X = M.r (coe ⁻¹' X) :=
begin
  set M' := (matroid_in_equiv_subtype.symm M) with hM',
  rw [r_eq_r_inter_ground, ←preimage_inter_range, subtype.range_coe],
  set X' := X ∩ (M' : matroid_in α).E with hX'_def,
  have hX' : coe '' (coe ⁻¹' X' : set E) = X',
  { rw image_preimage_eq_iff, simp [hX'_def], convert inter_subset_right _ _},
  rw [←hX', ←matroid_in_equiv_subtype_apply_r, hM', equiv.apply_symm_apply],
  refl,
end

end equivalence

section ext

lemma eq_of_base_iff_base {M₁ M₂ : matroid_in α} (hE : M₁.E = M₂.E)
(h' : ∀ B ⊆ M₁.E, M₁.base B ↔ M₂.base B) : M₁ = M₂ :=
begin
  ext, rw [ground_eq_E, hE, ←ground_eq_E],
  exact ⟨λ h, (h' _ (base.subset_ground h)).mp h,
    λ h, (h' _ ((base.subset_ground h).trans_eq hE.symm)).mpr h⟩,
end

lemma eq_of_indep_iff_indep {M₁ M₂ : matroid_in E} (hE : M₁.E = M₂.E)
(h' : ∀ I ⊆ M₁.E, M₁.indep I ↔ M₂.indep I) :
  M₁ = M₂ :=
begin
  refine eq_of_base_iff_base hE (λ B hB, _),
  simp_rw [base_iff_coe, base_iff_maximal_indep, ←indep_iff_coe],
  exact ⟨λ h, ⟨by { rw ←h' _ h.1.subset_ground, exact h.1 },
    λ I hI hBI, h.2 _ (by rwa h' _ (hI.subset_ground.trans_eq hE.symm)) hBI⟩,
    λ h, ⟨by { rw h' _ (h.1.subset_ground.trans_eq hE.symm), exact h.1 },
    λ I hI hBI, h.2 _ (by { rwa ←h' _ hI.subset_ground}) hBI ⟩⟩,
end

lemma eq_of_r_eq_r {M₁ M₂ : matroid_in E} (hE : M₁.E = M₂.E)
(h' : ∀ X ⊆ M₁.E, M₁.r X = M₂.r X) :
  M₁ = M₂ :=
eq_of_indep_iff_indep hE (λ I hI, by
  rw [indep_iff_coe,  matroid.indep_iff_r_eq_card, ←r_eq_coe_r, h' _ hI, indep_iff_r_eq_card])

end ext



section dual

/-- The dual of a `matroid_in` -/
def dual (M : matroid_in α) : matroid_in α :=
  matroid_in_equiv_subtype.symm (matroid_in_equiv_subtype ⟨M, rfl⟩).dual

-- def dual (M : matroid_in α)

reserve postfix `*` :90

notation (name := matroid_in_dual) M* := matroid_in.dual M

lemma dual_base_iff : M*.base B ↔ M.base (M.E \ B) ∧ B ⊆ M.E :=
by { simp [dual, image_compl_preimage], }

@[simp] lemma dual_ground (M : matroid_in α) : M*.E = M.E := rfl

@[simp] lemma dual_dual (M : matroid_in α) : M** = M :=
begin
  apply eq_of_base_iff_base _ (λ B hB, _),
    simp,
  simp only [dual_base_iff, dual_ground, sdiff_sdiff_right_self, inf_eq_inter],
  split,
  { rintro ⟨⟨h, -⟩, hB⟩, rwa [inter_eq_right_iff_subset.mpr hB] at h},
  intro hB,
  have h := hB.indep.subset_ground,
  exact ⟨⟨by rwa inter_eq_right_iff_subset.mpr h, diff_subset _ _⟩, h⟩,
end

lemma dual_r_cast_eq (M : matroid_in α) {X : set α} (hX : X ⊆ M.E) :
  (M*.r X : ℤ) = X.ncard + M.r (M.E \ X) - M.rk :=
begin
  rw [dual, matroid_in_equiv_subtype_apply_symm_r, dual_rank_cast_eq,
    matroid_in_equiv_subtype_apply_r, rk_def, matroid_in_equiv_subtype_apply_r,
    ncard_preimage_of_injective_subset_range coe_injective
      (by rwa range_coe : X ⊆ range (coe : M.E → α)), image_univ,
    ←preimage_compl, image_preimage_coe, diff_eq_compl_inter, rk_eq_r_ground, range_coe],
  refl,
end

lemma dual_r_add_rk_eq (M : matroid_in α) {X : set α} (hX : X ⊆ M.E) :
  M*.r X + M.rk = X.ncard + M.r (M.E \ X) :=
by linarith [M.dual_r_cast_eq hX]

lemma dual_inj_iff {M₁ M₂ : matroid_in α} : M₁* = M₂* ↔ M₁ = M₂ :=
⟨λ h, by rw [←dual_dual M₁, h, dual_dual], congr_arg _⟩

@[simp] lemma dual_indep_iff_coindep : M*.indep X ↔ M.coindep X :=
begin
  simp_rw [indep_iff_subset_base, dual_base_iff, base_iff_coe, coindep,
    matroid.coindep_iff_disjoint_base],
  split,
  { rintro ⟨B, ⟨hBc, hBE⟩, hXB⟩,
    exact ⟨⟨_, hBc, disjoint_of_subset_right hXB disjoint_sdiff_left⟩, hXB.trans hBE⟩ },
  rintro ⟨⟨B, (hB : M.base B), hdj⟩, hX⟩,
  refine ⟨M.E \ B, ⟨_,diff_subset _ _⟩, subset_diff.mpr ⟨hX,hdj.symm⟩ ⟩,
  rwa [sdiff_sdiff_right_self, inf_eq_inter, inter_eq_right_iff_subset.mpr hB.subset_ground],
end

@[simp] lemma dual_coindep_iff_indep : M*.coindep X ↔ M.indep X :=
by rw [←dual_dual M, dual_indep_iff_coindep, dual_dual]

end dual

end matroid_in

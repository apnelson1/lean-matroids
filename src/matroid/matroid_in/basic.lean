import ..pseudominor
import ..connectivity
import ..maps.equiv

open_locale classical
noncomputable theory

open matroid set subtype

variables {α : Type*}

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
by { rw [circuit, matroid.circuit_iff_forall_ssubset], refl }

lemma basis.to_coe (h : M.basis I X) : (M : matroid α).basis I X := h.1

lemma basis.indep (hIX : M.basis I X) : M.indep I := matroid.basis.indep hIX.1

lemma basis.subset (hIX : M.basis I X) : I ⊆ X := matroid.basis.subset hIX.1

lemma basis.subset_ground (hIX : M.basis I X) : X ⊆ M.E := hIX.2

lemma exists_basis (M : matroid_in α) (hX : X ⊆ M.E) : ∃ I, M.basis I X :=
by { obtain ⟨I, hI⟩ := matroid.exists_basis (M : matroid α) X,   exact ⟨I, hI, hX⟩ }

lemma basis.r (hIX : M.basis I X) : M.r I = M.r X := matroid.basis.r hIX.1

lemma base_iff_basis_ground : M.base B ↔ M.basis B M.E :=
begin
  rw [base, basis, iff_true_intro subset.rfl, and_true, matroid.basis_iff, 
    matroid.base_iff_maximal_indep, and.congr_right_iff], 
  exact λ hi, ⟨λ h, ⟨indep.subset_ground hi, λ J hJ hBJ _, h _ hJ hBJ⟩,
    λ h I hI hBI, h.2 _ hI hBI (indep.subset_ground hI)⟩,  
end  

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

variables {M₁ M₂ M : matroid_in α} {E : set α}  {X Y I B C : set α} {e f x y : α}

section equivalence

/-- A `matroid_in` gives a matroid on a subtype -/
def to_matroid (M : matroid_in α) : matroid M.E := 
  (M : matroid α).preimage (function.embedding.subtype M.E)

def to_matroid_of_ground_eq (M : matroid_in α) (hX : M.E = X) : matroid X := 
M.to_matroid.congr (equiv.set_congr hX)

/-- A `matroid` on a subtype gives a `matroid_in` -/
def to_matroid_in {E : set α} (M : matroid E) : matroid_in α := 
⟨E, M.image (function.embedding.subtype E), 
begin
  intros e he, 
  simp_rw [←matroid.loop_iff_mem_cl_empty, matroid.loop_iff_dep, image.indep_iff, 
    function.embedding.coe_subtype, not_exists, not_and, coe_injective.image_eq_singleton_iff], 
  rintro I hI ⟨⟨x,hx⟩,rfl,rfl⟩, 
  exact he hx, 
end⟩ 
  
/-- A `matroid_in α` with ground set `E` is the same thing as a `matroid E`-/
def equiv_subtype : {M : matroid_in α // M.E = E} ≃ matroid E :=
{ to_fun := λ M, to_matroid_of_ground_eq (M : matroid_in α) M.2,
  inv_fun := λ M, ⟨to_matroid_in M, rfl⟩,
  left_inv := begin 
    rintro ⟨M, rfl⟩, 
    simp only [to_matroid_of_ground_eq, to_matroid_in, to_matroid, coe_mk, congr_eq_preimage, 
      preimage.trans], 
    refine matroid_in.ext _ _ rfl _, 
    convert (M : matroid α).image_preimage_eq_of_forall_subset_range 
      (function.embedding.subtype M.E) (λ I hI, _),  
    simp only [function.embedding.coe_subtype, range_coe_subtype, set_of], 
    exact indep.subset_ground hI, 
  end,
  right_inv := begin
    rintro M, 
    simp only [coe_mk, to_matroid_of_ground_eq, to_matroid_in, congr_eq_preimage, to_matroid, 
      ←carrier_eq_coe, preimage.trans],  
    convert M.preimage_image _, 
  end }

lemma equiv_subtype_apply {E : set α} {M : {M : matroid_in α // M.E = E} } : 
  equiv_subtype M = (M : matroid α).preimage (function.embedding.subtype E) := 
by { simp [equiv_subtype, to_matroid_of_ground_eq, to_matroid], congr' }

lemma equiv_subtype_apply_symm_coe_coe {E : set α} (M : matroid E) : 
  ((equiv_subtype.symm M : matroid_in α) : matroid α) = M.image (function.embedding.subtype E) := 
by simp [equiv_subtype, to_matroid_in, ←carrier_eq_coe]

@[simp] lemma equiv_subtype.symm_ground_eq (M : matroid E) : 
  (equiv_subtype.symm M : matroid_in α).E = E := rfl 

@[simp] lemma equiv_subtype.indep_iff {I : set E} (M : {M : matroid_in α // M.E = E}) :
  (equiv_subtype M).indep I ↔ (M : matroid_in α).indep (coe '' I) :=
by simp [equiv_subtype_apply, indep_iff_coe]
  
@[simp] lemma equiv_subtype.symm_indep_iff {I : set α} (M : matroid E) : 
  (equiv_subtype.symm M : matroid_in α).indep I ↔ ∃ I₀, M.indep I₀ ∧ coe '' I₀ = I :=
by { rw [indep_iff_coe, equiv_subtype_apply_symm_coe_coe], simp }

@[simp] lemma equiv_subtype.basis_iff {I X : set E} (M : {M : matroid_in α // M.E = E}) :
  (equiv_subtype M).basis I X ↔ (M : matroid_in α).basis (coe '' I) (coe '' X) :=
by { obtain ⟨M, rfl⟩:= M, simp [equiv_subtype_apply, basis] }
  
@[simp] lemma equiv_subtype.symm_basis_iff {I X : set α} (M : matroid E) : 
  (equiv_subtype.symm M : matroid_in α).basis I X ↔ 
    ∃ I₀ X₀, M.basis I₀ X₀ ∧ I = coe '' I₀ ∧ X = coe '' X₀ := 
begin
  rw [basis, equiv_subtype_apply_symm_coe_coe, equiv_subtype.symm_ground_eq, image.basis_iff, 
    function.embedding.coe_subtype], 
  split, 
  { rintro ⟨⟨I₀,hI₀,rfl⟩, hX⟩,
    exact ⟨I₀, coe ⁻¹' X, hI₀, rfl, by rwa [eq_comm, image_preimage_eq_iff, range_coe]⟩ }, 
  rintro ⟨I₀, X₀, hb, rfl, rfl⟩, 
  refine ⟨⟨I₀,_,rfl⟩, (image_subset_range _ _).trans_eq range_coe⟩,    
  rwa preimage_image_eq _ coe_injective,
end 

@[simp] lemma equiv_subtype.base_iff {B : set E} (M : {M : matroid_in α // M.E = E}) :
  (equiv_subtype M).base B ↔ (M : matroid_in α).base (coe '' B) :=
begin
  obtain ⟨M,rfl⟩ := M,  
  simp only [equiv_subtype_apply, base_iff_coe, coe_coe, coe_mk, preimage.base_iff, 
    function.embedding.coe_subtype, range_coe_subtype, set_of, base_iff_basis_ground, basis, 
    iff_true_intro subset.rfl, and_true], 
end

@[simp] lemma equiv_subtype.symm_base_iff {B : set α} (M : matroid E) : 
  (equiv_subtype.symm M : matroid_in α).base B ↔ ∃ B₀, M.base B₀ ∧ B = coe '' B₀ :=
begin
  simp_rw [base_iff_coe, equiv_subtype_apply_symm_coe_coe, image.base_iff], 
  convert iff.rfl, 
end 


@[simp] lemma equiv_subtype.r_eq (M : {M : matroid_in α // M.E = E}) (X : set E) :
  (equiv_subtype M).r X = (M : matroid_in α).r (coe '' X) :=
by simp [equiv_subtype_apply, r]

@[simp] lemma equiv_subtype.symm_r_eq (M : matroid E) (X : set α) :
  (equiv_subtype.symm M : matroid_in α).r X = M.r (coe ⁻¹' X) :=
by simp [r, equiv_subtype_apply_symm_coe_coe]

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

lemma eq_of_r_eq_r [finite E] {M₁ M₂ : matroid_in E} (hE : M₁.E = M₂.E)
(h' : ∀ X ⊆ M₁.E, M₁.r X = M₂.r X) :
  M₁ = M₂ :=
eq_of_indep_iff_indep hE (λ I hI, by
  rw [indep_iff_coe,  matroid.indep_iff_r_eq_card, ←r_eq_coe_r, h' _ hI, indep_iff_r_eq_card])

end ext

section dual

/-- The dual of a `matroid_in` -/
def dual (M : matroid_in α) : matroid_in α := equiv_subtype.symm (equiv_subtype ⟨M, rfl⟩)﹡

instance {α : Type*} : has_matroid_dual (matroid_in α) := ⟨dual⟩ 

lemma dual_eq (M : matroid_in α) : M﹡ = equiv_subtype.symm (equiv_subtype ⟨M, rfl⟩)﹡ := rfl  

lemma dual_base_iff : M﹡.base B ↔ M.base (M.E \ B) ∧ B ⊆ M.E :=
begin
  simp_rw [dual_eq, equiv_subtype.symm_base_iff, matroid.dual_base_iff, equiv_subtype.base_iff, 
    subtype.coe_mk], 
  have lem : ∀ (B₀ : set M.E),  M.E \ coe '' B₀ = coe '' B₀ᶜ, 
  from λ B₀, 
    by simp_rw [←@range_coe _ M.E, ←image_univ, ←image_diff coe_injective, compl_eq_univ_diff],
  split, 
  { rintro ⟨B₀, hB₀, rfl⟩, exact ⟨by rwa lem, (image_subset_range _ _).trans_eq range_coe⟩ },
  rintro ⟨hB, hBE⟩, 
  rw [←@range_coe _ M.E, subset_range_iff_exists_image_eq] at hBE,
  exact hBE.imp (λ B₀ h, ⟨by rwa [←lem, h], h.symm⟩), 
end 

@[simp] lemma dual_ground (M : matroid_in α) : M﹡.E = M.E := rfl

@[simp] lemma dual_dual (M : matroid_in α) : M﹡﹡ = M := by simp [dual_eq]

lemma dual_r_cast_eq [finite α] (M : matroid_in α) {X : set α} (hX : X ⊆ M.E) :
  (M﹡.r X : ℤ) = X.ncard + M.r (M.E \ X) - M.rk :=
begin
  rw [dual_eq, matroid_in_equiv_subtype_apply_symm_r, dual_rank_cast_eq,
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

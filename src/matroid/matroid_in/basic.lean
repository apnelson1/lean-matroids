import ..connectivity
import ..simple 
import ..maps.equiv

open_locale classical
open_locale big_operators
-- noncomputable theory

open matroid set subtype

variables {α : Type*}

/- a `matroid_in α` is a matroid defined on some subset `E` of `α`. Implemented as a matroid on
  which the nonelements of `E` are all loops.

  The main motivation for this is to have a way of talking about minors that avoids type equality.
  Pseudominors give one way of doing this, while staying in `matroid E`, but they are a bit ugly
  with duality. The advantage of `matroid_in` is that, if `M : matroid_in α`, then `M﹡` and
  `M ⟋ C ⟍ D` are both `matroid_in α`, and we can say things like `(M / C \ D)﹡ = M﹡ ⟍ C ⟋ D`
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

/-- The coercion of a `matroid_in α` to a `matroid α`. The coerced matroid has only loops 
  outside the ground set; most `matroid_in` properties are defined using this coercion, because
  the definitional properties are convenient for going between `matroid_in` and `matroid` APIs. -/
instance {α : Type*} : has_coe (matroid_in α) (matroid α) := ⟨λ M, M.carrier⟩

@[simp] lemma carrier_eq_coe {M : matroid_in α} : M.carrier = (M : matroid α) := rfl

/-- The ground set of a `matroid_in`. This is some `set` of the ambient type. -/
def E (M : matroid_in α) := M.ground

@[simp] lemma ground_eq_E (M : matroid_in α) : M.ground = M.E := rfl

/-- A `matroid_in` is `finite_rk` if its ground set has a finite base -/
class finite_rk (M : matroid_in α) : Prop := (fin : finite_rk (M : matroid α)) 

instance finite_rk.to_coe {M : matroid_in α} [finite_rk M] : 
  (M : matroid α).finite_rk := ‹finite_rk M›.fin  

section equivalence

variables {X X₁ X₂ E : set α}

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
    rw ←compl_compl M.E,  
    exact λ e he heM,  matroid.indep.nonloop_of_mem hI he (M.support heM),
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

def equiv.set_subtype {α : Type*} (X : set α) : { S : set α // S ⊆ X } ≃ set X  := 
{ to_fun := λ S, coe ⁻¹' (S : set α),
  inv_fun := λ Y, ⟨coe '' Y, by simp⟩,
  right_inv := λ S, by simp [preimage_image_eq _ coe_injective],
  left_inv := λ S, by {obtain ⟨S, h⟩ := S, simpa } }

@[simp] lemma equiv.set_subtype_apply (S) : equiv.set_subtype X S = coe ⁻¹' (S : set α) := rfl 

@[simp] lemma equiv.set_subtype_apply_symm_coe (S) : 
  ((equiv.set_subtype X).symm S : set α) = coe '' S := rfl 

lemma eq_image_symm_image_equiv_subtype (M : matroid_in α) : 
  (equiv_subtype.symm (equiv_subtype ⟨M,rfl⟩) : matroid_in α) = M :=
by simp_rw [equiv.symm_apply_apply, coe_mk] 

section transfer

/-- Transfer a `matroid` property of sets to a `matroid_in` property. -/
def transfer_set_prop (P : ∀ ⦃γ : Type*⦄ (M : matroid γ), set γ → Prop) : 
  ∀ (M : matroid_in α), set α → Prop := 
λ M X, ∃ (h : X ⊆ M.E), P (M.to_matroid) (equiv.set_subtype M.E ⟨X,h⟩) 

/-- Transfer a `matroid` property of pairs of sets to a `matroid_in` property. -/
def transfer_set_prop₂ (P : ∀ ⦃γ : Type*⦄ (M : matroid γ), set γ → set γ → Prop) : 
  ∀ (M : matroid_in α), set α → set α → Prop := 
λ M X₁ X₂, ∃ (h₁ : X₁ ⊆ M.E) (h₂ : X₂ ⊆ M.E), 
  P M.to_matroid (equiv.set_subtype M.E ⟨X₁,h₁⟩) (equiv.set_subtype M.E ⟨X₂,h₂⟩)

lemma transfer_set_prop_iff {P} {M : matroid_in α} : 
  transfer_set_prop P M X ↔ P (equiv_subtype ⟨M,rfl⟩) (coe ⁻¹' X) ∧ X ⊆ M.E  :=
by simp [transfer_set_prop, equiv_subtype_apply, to_matroid, and_comm] 
 
lemma transfer_set_prop₂_iff {P} {M : matroid_in α} : 
  transfer_set_prop₂ P M X₁ X₂ ↔ P (equiv_subtype ⟨M,rfl⟩) (coe ⁻¹' X₁) (coe ⁻¹' X₂) 
    ∧ X₁ ⊆ M.E ∧ X₂ ⊆ M.E:=
by simp [transfer_set_prop₂, equiv_subtype_apply, to_matroid, and_comm, ←and_assoc] 

@[simp] lemma transfer_set_prop_iff_symm {P} {M : matroid E} {X : set E} : 
  (transfer_set_prop P) (equiv_subtype.symm M : matroid_in α) (coe '' X) ↔ P M X  :=
by { rw ←equiv_subtype.apply_symm_apply M, simpa [transfer_set_prop_iff] }

@[simp] lemma transfer_set_prop_coe_iff {P} {M : matroid_in α} {X : set M.E} : 
  (transfer_set_prop P) M (coe '' X) ↔ P (equiv_subtype ⟨M, rfl⟩) X := 
by simp [transfer_set_prop_iff]

@[simp] lemma transfer_set_prop₂_iff_symm {P} {E : set α} {M : matroid E} {X₁ X₂ : set E} : 
  (transfer_set_prop₂ P) (equiv_subtype.symm M : matroid_in α) (coe '' X₁) (coe '' X₂) 
    ↔ P M X₁ X₂ :=
by { rw ←equiv_subtype.apply_symm_apply M, simpa [transfer_set_prop₂_iff] }

@[simp] lemma transfer_set_prop₂_coe_iff {P} {M : matroid_in α} {X₁ X₂ : set M.E} : 
  (transfer_set_prop₂ P) M (coe '' X₁) (coe '' X₂) ↔ P (equiv_subtype ⟨M, rfl⟩) X₁ X₂ := 
  by simp [transfer_set_prop₂_iff]

lemma transfer_set_prop.subset_ground {P} {M : matroid_in α}
(hX : transfer_set_prop P M X) : X ⊆ M.E := exists.elim hX (λ h _, h)

lemma transfer_set_prop.inter_ground {P} {M : matroid_in α}
(hX : transfer_set_prop P M X) : X ∩ M.E = X := inter_eq_self_of_subset_left hX.subset_ground

lemma transfer_set_prop.exists_eq_coe {P} {M : matroid_in α}
(hX : transfer_set_prop P M X) : ∃ (X₀ : set M.E), P (equiv_subtype ⟨M,rfl⟩) X₀ ∧ X = coe '' X₀ := 
begin
  simp_rw [transfer_set_prop_iff, ←@range_coe _ M.E, subset_range_iff_exists_image_eq] at hX, 
  obtain ⟨hX₀, X₀, rfl⟩ := hX, 
  exact ⟨_, by simpa using hX₀, rfl⟩, 
end 

lemma transfer_set_prop₂.exists_eq_coe {P} {M : matroid_in α} {X₁ X₂ : set α} 
(hX : transfer_set_prop₂ P M X₁ X₂) : 
  ∃ (X₁' X₂' : set M.E), P (equiv_subtype ⟨M,rfl⟩) X₁' X₂' ∧ X₁ = coe '' X₁' ∧ X₂ = coe '' X₂' :=
begin
  simp_rw [transfer_set_prop₂_iff, ←@range_coe _ M.E, subset_range_iff_exists_image_eq] at hX, 
  obtain ⟨hX', ⟨X₁', rfl⟩, ⟨X₁',rfl⟩ ⟩  := hX, 
  exact ⟨_, _, by simpa using hX', rfl, rfl⟩, 
end 

@[simp] lemma transfer_set_prop_forall_iff {P} {M : matroid_in α} {Q : set α → Prop} : 
  (∀ X, transfer_set_prop P M X → Q X) ↔ 
    ∀ (Y : set M.E), P (equiv_subtype ⟨M,rfl⟩) Y → Q (coe '' Y) := 
begin
  refine ⟨λ h Y hPY, h _ (transfer_set_prop_coe_iff.mpr hPY), λ h X hPX, _⟩,
  obtain ⟨Y, hY, rfl⟩ := hPX.exists_eq_coe, 
  exact h _ hY, 
end 

@[simp] lemma transfer_set_prop₂_forall_iff {P} {M : matroid_in α} {Q : set α → set α → Prop} : 
  (∀ X₁ X₂, transfer_set_prop₂ P M X₁ X₂ → Q X₁ X₂) ↔ 
    ∀ (Y₁ Y₂ : set M.E), P (equiv_subtype ⟨M,rfl⟩) Y₁ Y₂ → Q (coe '' Y₁) (coe '' Y₂) := 
begin
  refine ⟨λ h Y₁ Y₂ hP, h _ _ (transfer_set_prop₂_coe_iff.mpr hP), 
    λ h X₁ X₂ hP, _⟩,
  obtain ⟨Y₁, Y₂, hY, rfl, rfl⟩ := hP.exists_eq_coe, 
  exact h _ _ hY,  
end 

@[simp] lemma transfer_set_prop_exists_iff {P} {M : matroid_in α} {Q : set α → Prop} : 
  (∃ X, transfer_set_prop P M X ∧ Q X) ↔ 
    ∃ (Y : set M.E), P (equiv_subtype ⟨M,rfl⟩) Y ∧ Q (coe '' Y) := 
begin
  split, 
  { rintro ⟨X, hPX, hQX⟩, 
    obtain ⟨Y, hY, rfl⟩ := hPX.exists_eq_coe, 
    refine ⟨Y, hY, hQX⟩ },
  rintro ⟨Y, hY⟩, 
  exact ⟨coe '' Y, by rwa [transfer_set_prop_coe_iff]⟩, 
end 

lemma transfer_set_prop₂.subset_ground_left {P} {M : matroid_in α} {X₁ X₂ : set α} 
(hX : transfer_set_prop₂ P M X₁ X₂) : X₁ ⊆ M.E := let ⟨h, _, _⟩ := hX in h

lemma transfer_set_prop₂.subset_ground_right {P} {M : matroid_in α} {X₁ X₂ : set α} 
(hX : transfer_set_prop₂ P M X₁ X₂) : X₂ ⊆ M.E := let ⟨_, h, _⟩ := hX in h

lemma transfer_set_prop₂.inter_ground_left {P} {M : matroid_in α} {X₁ X₂ : set α}
(hX : transfer_set_prop₂ P M X₁ X₂) : X₁ ∩ M.E = X₁ := 
  inter_eq_self_of_subset_left hX.subset_ground_left

lemma transfer_set_prop₂.inter_ground_right {P} {M : matroid_in α} {X₁ X₂ : set α}
(hX : transfer_set_prop₂ P M X₁ X₂) : X₂ ∩ M.E = X₂ := 
  inter_eq_self_of_subset_left hX.subset_ground_right

/-- The type of sets in `α` satisfying `transfer_set_prop P` corresponds to the type of sets in 
  `M.E` satisfying `P` -/
def transfer_set_prop_equiv (P) (M : matroid_in α) : 
{ X : set α // transfer_set_prop P M X } ≃ { Y : set M.E // P (equiv_subtype ⟨M,rfl⟩) Y } :=
{ to_fun := λ X, ⟨coe ⁻¹' (X : set α),  (transfer_set_prop_iff.mp X.2).1⟩,
  inv_fun := λ Y, ⟨coe '' (Y : set M.E), by simpa using Y.2⟩,
  left_inv := by { rintro ⟨X, hX⟩, simp [hX.subset_ground], },
  right_inv := by { rintro ⟨Y, hY⟩, simp } }

@[simp] lemma transfer_set_prop_equiv_apply {P} (M : matroid_in α) {X : set α} 
(hX : transfer_set_prop P M X) : (transfer_set_prop_equiv P M ⟨X,hX⟩ : set M.E) = coe ⁻¹' X := rfl 

@[simp] lemma transfer_set_prop_equiv_apply_symm {P : ∀ ⦃γ : Type*⦄ (M : matroid γ), set γ → Prop} 
(M : matroid_in α) {Y : set M.E} (hY : P (equiv_subtype ⟨M,rfl⟩) Y) : 
  ((transfer_set_prop_equiv P M).symm ⟨Y,hY⟩ : set α) = coe '' Y := rfl 

end transfer

end equivalence 

variables {M : matroid_in α} {X Y I J C B F H K : set α} {e f : α} {k : ℕ}

section basic

lemma loop_coe_of_not_mem_ground (h : e ∉ M.E) : (M : matroid α).loop e := M.support (mem_compl h)

lemma mem_ground_of_nonloop_coe (h : (M : matroid α).nonloop e) : e ∈ M.E :=
by_contra (λ he, h (M.support he))

lemma compl_ground_subset_loops_coe (M : matroid_in α) : M.Eᶜ ⊆ (M : matroid α).cl ∅ := M.support

lemma subset_ground_of_disjoint_loops_coe (hX : disjoint X ((M : matroid α).cl ∅)) : X ⊆ M.E :=
hX.subset_compl_right.trans (compl_subset_comm.mp M.support)

lemma subset_loops_coe_of_disjoint_ground (hX : disjoint X M.E) : X ⊆ (M : matroid α).cl ∅ :=
hX.subset_compl_right.trans (compl_ground_subset_loops_coe _)

instance coe_finite_rk_of_finite {M : matroid_in α} [finite M.E] : 
  (M : matroid α).finite_rk := 
⟨by { obtain ⟨B, hB⟩ := (M : matroid α).exists_base, 
  exact ⟨B, hB, (to_finite M.E).subset 
    (subset_ground_of_disjoint_loops_coe (hB.indep.disjoint_loops))⟩}⟩

/-! Independence -/

/-- A `base` is a maximal independent set -/
def base (M : matroid_in α) (B : set α) : Prop := (M : matroid α).base B

/-- An `indep`endent set is a subset of a base -/
def indep (M : matroid_in α) (I : set α) : Prop := (M : matroid α).indep I

/-- A `basis` for `X` is a maximal independent subset of `X` -/
def basis (M : matroid_in α) (I X : set α) : Prop := (M : matroid α).basis I X ∧ X ⊆ M.E

lemma indep.subset_ground (hI : M.indep I) : I ⊆ M.E :=
  subset_ground_of_disjoint_loops_coe (matroid.indep.disjoint_loops hI)

lemma base_iff_coe : M.base B ↔ (M : matroid α).base B := iff.rfl

lemma base.to_coe (hB : M.base B) : (M : matroid α).base B := hB

lemma exists_base (M : matroid_in α) : ∃ B, M.base B := matroid.exists_base M

lemma base.indep (hB : M.base B) : M.indep B := matroid.base.indep hB

lemma base.subset_ground (hB : M.base B) : B ⊆ M.E := hB.indep.subset_ground

lemma base.finite [finite_rk M] (hB : M.base B) : B.finite := hB.to_coe.finite 

lemma base.insert_dep (hB : M.base B) (he : e ∉ B) : ¬M.indep (insert e B) := 
matroid.base.insert_dep hB he 

lemma indep_iff_coe : M.indep I ↔ (M : matroid α).indep I := iff.rfl

lemma indep.to_coe (hI : M.indep I) : (M : matroid α).indep I := hI



lemma indep_iff_subset_base : M.indep I ↔ ∃ B, M.base B ∧ I ⊆ B := iff.rfl

lemma indep.exists_base_supset (hI : M.indep I) : ∃ B, M.base B ∧ I ⊆ B := hI    

lemma indep.finite [finite_rk M] (hI : M.indep I) : I.finite := 
exists.elim (indep_iff_subset_base.mp hI) (λ B hB, hB.1.finite.subset hB.2)

lemma indep.subset (hI : M.indep I) (hX : X ⊆ I) : M.indep X := matroid.indep.subset hI hX

lemma indep.subset_basis_of_subset (hI : M.indep I) (hIX : I ⊆ X) (hX : X ⊆ M.E) :
  ∃ J, I ⊆ J ∧ M.basis J X :=
begin
  obtain ⟨J, hJ, hIJ⟩ := matroid.indep.subset_basis_of_subset hI hIX,
  exact ⟨J, hIJ, ⟨hJ, hX⟩⟩,
end

lemma indep.basis_self (hI : M.indep I) : M.basis I I := ⟨hI.to_coe.basis_self, hI.subset_ground⟩ 

lemma basis.to_coe (h : M.basis I X) : (M : matroid α).basis I X := h.1

lemma basis.indep (hIX : M.basis I X) : M.indep I := matroid.basis.indep hIX.1

lemma basis.subset (hIX : M.basis I X) : I ⊆ X := matroid.basis.subset hIX.1

lemma basis.subset_ground (hIX : M.basis I X) : X ⊆ M.E := hIX.2

lemma exists_basis (M : matroid_in α) (hX : X ⊆ M.E) : ∃ I, M.basis I X :=
by { obtain ⟨I, hI⟩ := matroid.exists_basis (M : matroid α) X,   exact ⟨I, hI, hX⟩ }

lemma base_iff_basis_ground : M.base B ↔ M.basis B M.E :=
begin
  rw [base, basis, iff_true_intro subset.rfl, and_true, matroid.basis_iff, 
    matroid.base_iff_maximal_indep, and.congr_right_iff], 
  exact λ hi, ⟨λ h, ⟨indep.subset_ground hi, λ J hJ hBJ _, h _ hJ hBJ⟩,
    λ h I hI hBI, h.2 _ hI hBI (indep.subset_ground hI)⟩,  
end  

/-- A set is `r_fin` in `M` if it has a finite basis -/
def r_fin (M : matroid_in α) (X : set α) := (M : matroid α).r_fin X ∧ X ⊆ M.E 

lemma r_fin.to_coe (h : M.r_fin X) : (M : matroid α).r_fin X := h.1 

lemma r_fin.subset_ground (h : M.r_fin X) : X ⊆ M.E := h.2 

lemma to_r_fin [finite_rk M] (h : X ⊆ M.E) : M.r_fin X := ⟨matroid.to_r_fin (M : matroid α) X, h⟩  

lemma basis.r_fin_iff_finite (hI : M.basis I X) : M.r_fin X ↔ I.finite :=
by rw [r_fin, hI.to_coe.r_fin_iff_finite, and_iff_left hI.subset_ground]

lemma indep.r_fin_iff_finite (hI : M.indep I) : M.r_fin I ↔ I.finite :=
hI.basis_self.r_fin_iff_finite 

lemma r_fin.subset (h : M.r_fin X) (hY : Y ⊆ X) : M.r_fin Y := 
⟨h.to_coe.subset hY, hY.trans h.subset_ground⟩ 

lemma r_fin_of_finite (hX : X ⊆ M.E) (hfin : X.finite) : M.r_fin X := 
⟨matroid.r_fin_of_finite M hfin, hX⟩

/-- Needs a `matroid` version-/
lemma r_fin_singleton (he : e ∈ M.E) : M.r_fin {e} := 
r_fin_of_finite (singleton_subset_iff.mpr he) (finite_singleton e)

@[simp] lemma r_fin_empty (M : matroid_in α) : M.r_fin ∅ := 
r_fin_of_finite (empty_subset _) finite_empty 

lemma r_fin.union (hX : M.r_fin X) (hY : M.r_fin Y) : M.r_fin (X ∪ Y) :=
⟨hX.to_coe.union hY.to_coe, union_subset hX.subset_ground hY.subset_ground⟩

/-- Needs a `matroid` version-/
lemma r_fin_union_iff : M.r_fin (X ∪ Y) ↔ M.r_fin X ∧ M.r_fin Y := 
⟨λ h, ⟨h.subset (subset_union_left X Y),h.subset (subset_union_right X Y)⟩, λ h, h.1.union h.2⟩ 

@[simp] lemma equiv_subtype.indep_iff {E : set α} {I : set E} (M : {M : matroid_in α // M.E = E}) :
  (equiv_subtype M).indep I ↔ (M : matroid_in α).indep (coe '' I) :=
by simp [equiv_subtype_apply, indep_iff_coe]
  
lemma equiv_subtype.symm_indep_iff_exists {E I : set α} (M : matroid E) : 
  (equiv_subtype.symm M : matroid_in α).indep I ↔ ∃ I₀, M.indep I₀ ∧ coe '' I₀ = I :=
by { rw [indep_iff_coe, equiv_subtype_apply_symm_coe_coe], simp }

@[simp] lemma equiv_subtype.symm_indep_iff {E I : set α} (M : matroid E) : 
  (equiv_subtype.symm M : matroid_in α).indep I ↔ M.indep (coe ⁻¹' I) ∧ I ⊆ E :=
begin
  rw [←equiv.apply_symm_apply equiv_subtype M, equiv_subtype.indep_iff, 
    equiv.apply_symm_apply, image_preimage_eq_inter_range, range_coe], 
  refine ⟨λ h, ⟨h.subset (inter_subset_left _ _),h.subset_ground⟩, _⟩,
  rintro ⟨hi,hIE⟩, 
  rwa [inter_eq_self_of_subset_left hIE] at hi, 
end

lemma indep_eq_transfer_set_prop (M : matroid_in α) : M.indep = transfer_set_prop (λ _, matroid.indep) M := 
begin
  ext X, 
  simp only [transfer_set_prop_iff, equiv_subtype.indep_iff, coe_mk, image_preimage_coe], 
  refine ⟨λ h, ⟨by rwa (inter_eq_self_of_subset_left h.subset_ground), h.subset_ground⟩, λ h, _⟩,
  rw [←inter_eq_self_of_subset_left h.2], 
  exact h.1, 
end 

@[simp] lemma equiv_subtype.basis_iff {E : set α} {I X : set E} 
(M : {M : matroid_in α // M.E = E}) :
  (equiv_subtype M).basis I X ↔ (M : matroid_in α).basis (coe '' I) (coe '' X) :=
by { obtain ⟨M, rfl⟩:= M, simp [equiv_subtype_apply, basis] }

@[simp] lemma equiv_subtype.symm_basis_iff {E I X : set α} (M : matroid E) : 
  (equiv_subtype.symm M : matroid_in α).basis I X ↔ 
    M.basis (coe ⁻¹' I) (coe ⁻¹' X) ∧ I ⊆ E ∧ X ⊆ E :=  
begin
  rw [←equiv.apply_symm_apply (equiv_subtype) M],
  simp_rw [equiv_subtype.basis_iff, equiv.apply_symm_apply, image_preimage_coe],  
  refine ⟨λ h, _,_⟩,
  { have hXE : X ⊆ E := h.subset_ground, 
    rw [inter_eq_self_of_subset_left hXE, inter_eq_self_of_subset_left (h.subset.trans hXE)], 
    exact ⟨h, h.subset.trans hXE, hXE⟩ }, 
  rintro ⟨h,hIE, hXE⟩, 
  rwa [inter_eq_self_of_subset_left hIE, inter_eq_self_of_subset_left hXE] at h,  
end 

lemma equiv_subtype.symm_basis_iff_exists {E I X : set α} (M : matroid E) : 
  (equiv_subtype.symm M : matroid_in α).basis I X ↔ 
    ∃ I₀ X₀, M.basis I₀ X₀ ∧ I = coe '' I₀ ∧ X = coe '' X₀ := 
begin
  rw equiv_subtype.symm_basis_iff, 
  refine ⟨λ h, ⟨_,_,h.1,_,_⟩, _⟩, 
  { rw [eq_comm, image_preimage_eq_iff, range_coe], exact h.2.1 },
  { rw [eq_comm, image_preimage_eq_iff, range_coe], exact h.2.2 },
  rintro ⟨I, X, h, rfl, rfl⟩, 
  simp_rw [←@range_coe _ E, preimage_image_eq _ coe_injective, 
    and_iff_left (image_subset_range _ _), iff_true_intro h], 
end 

@[simp] lemma equiv_subtype.base_iff {E : set α} {B : set E} (M : {M : matroid_in α // M.E = E}) :
  (equiv_subtype M).base B ↔ (M : matroid_in α).base (coe '' B) :=
begin
  obtain ⟨M,rfl⟩ := M,  
  simp only [equiv_subtype_apply, base_iff_coe, coe_coe, coe_mk, preimage.base_iff, 
    function.embedding.coe_subtype, range_coe_subtype, set_of, base_iff_basis_ground, basis, 
    iff_true_intro subset.rfl, and_true], 
end

lemma base_eq_transfer_set_prop (M : matroid_in α) : M.base = transfer_set_prop (λ _, matroid.base) M := 
begin
  ext X, 
  simp only [transfer_set_prop_iff, equiv_subtype.base_iff, coe_mk, image_preimage_coe], 
  refine ⟨λ h, ⟨by rwa (inter_eq_self_of_subset_left h.subset_ground), h.subset_ground⟩, λ h, _⟩,
  rw [←inter_eq_self_of_subset_left h.2], 
  exact h.1, 
end 

lemma equiv_subtype.symm_base_iff_exists {E B : set α} (M : matroid E) : 
  (equiv_subtype.symm M : matroid_in α).base B ↔ ∃ B₀, M.base B₀ ∧ B = coe '' B₀ :=
begin
  simp_rw [base_iff_coe, equiv_subtype_apply_symm_coe_coe, image.base_iff], 
  convert iff.rfl, 
end 

@[simp] lemma equiv_subtype.symm_base_iff {E B : set α} (M : matroid E) : 
  (equiv_subtype.symm M : matroid_in α).base B ↔ M.base (coe ⁻¹' B) ∧ B ⊆ E :=
begin
  rw [equiv_subtype.symm_base_iff_exists], 
  refine ⟨_, λ h, ⟨_, h.1, _⟩⟩,  
  { rintro ⟨B, hB, rfl⟩, 
    simp_rw [preimage_image_eq _ coe_injective, ←@range_coe _ E, 
      and_iff_left (image_subset_range _ _), iff_true_intro hB] },
  rw [image_preimage_eq_inter_range, range_coe, inter_eq_self_of_subset_left h.2], 
end 

@[simp] lemma equiv_subtype.r_fin_iff {E : set α} {X : set E} (M : {M : matroid_in α // M.E = E}) :
  (equiv_subtype M).r_fin X ↔ (M : matroid_in α).r_fin (coe '' X) := 
begin
  obtain ⟨I, hI⟩ := (equiv_subtype M).exists_basis X, 
  rw [hI.r_fin_iff_finite, ((equiv_subtype.basis_iff _).mp hI).r_fin_iff_finite, 
    finite_image_iff (coe_injective.inj_on _)], 
end 

@[simp] lemma equiv_subtype.symm_r_fin_iff {E X : set α} (M : matroid E) : 
  (equiv_subtype.symm M : matroid_in α).r_fin X ↔ M.r_fin (coe ⁻¹' X) ∧ X ⊆ E  :=
begin
  rw [←equiv.apply_symm_apply (equiv_subtype) M],
  simp_rw [equiv_subtype.r_fin_iff, equiv.apply_symm_apply, image_preimage_coe],  
  refine ⟨λ h, _,_⟩,
  { have hXE : X ⊆ E := h.subset_ground, 
    exact ⟨by rwa inter_eq_self_of_subset_left hXE, hXE⟩ }, 
  rintro ⟨h₁,h₂⟩, 
  rwa inter_eq_self_of_subset_left h₂ at h₁,  
end 

lemma equiv_subtype.symm_r_fin_iff_exists {E X : set α} (M : matroid E) : 
  (equiv_subtype.symm M : matroid_in α).r_fin X ↔ ∃ X₀, M.r_fin X₀ ∧ X = coe '' X₀ :=
begin
  rw [equiv_subtype.symm_r_fin_iff],  
  refine ⟨λ h, ⟨_,h.1, by { rw [eq_comm, image_preimage_eq_iff, range_coe], exact h.2 }⟩, _⟩, 
  rintro ⟨F₀, hF₀, rfl⟩, 
  simp_rw [preimage_image_eq _ coe_injective, ←@range_coe _ E],   
  exact ⟨hF₀, image_subset_range _ _⟩, 
end

lemma r_fin_eq_transfer_set_prop (M : matroid_in α) : M.r_fin = transfer_set_prop (λ _, matroid.r_fin) M :=
begin
  ext X, 
  simp_rw [transfer_set_prop_iff, equiv_subtype.r_fin_iff, coe_mk, image_preimage_coe, r_fin, 
    and_iff_left (inter_subset_right _ _), and.congr_left_iff], 
  intro h, 
  rw [inter_eq_self_of_subset_left h],  
end 

/-! Circuits -/

/-- A `circuit` is a minimal dependent set. -/
def circuit (M : matroid_in α) (C : set α) := (M : matroid α).circuit C ∧ C ⊆ M.E

lemma circuit.subset_ground (hC : M.circuit C) : C ⊆ M.E := hC.2

lemma circuit.to_coe (hC : M.circuit C) : (M : matroid α).circuit C := hC.1 

lemma circuit_iff : M.circuit C ↔ (¬ M.indep C ∧ (∀ I ⊂ C, M.indep I)) ∧ C ⊆ M.E :=
by { rw [circuit, matroid.circuit_iff_forall_ssubset], refl }

lemma circuit_iff_coe : M.circuit C ↔ (M : matroid α).circuit C ∧ C ⊆ M.E := iff.rfl 

lemma circuit_coe_iff : (M : matroid α).circuit C ↔ M.circuit C ∨ ∃ e ∈ M.Eᶜ, C = {e} := 
begin
  rw [circuit], 
  refine (em (C ⊆ M.E)).elim (λ hC, _) (λ hC, _), 
  { rw [or_iff_left, iff_true_intro hC, and_true],
    rintro ⟨e, hec, rfl⟩, 
    exact hec (hC (mem_singleton e)) },
  rw [or_iff_right (hC ∘ and.right)], 
  obtain ⟨e, heC, heM⟩ := not_subset_iff_exists_mem_not_mem.mp hC,  
  have hl := (loop_coe_of_not_mem_ground heM).circuit,
  refine ⟨λ h, ⟨e, heM, (hl.eq_of_subset_circuit h (singleton_subset_iff.mpr heC)).symm⟩ ,λ h, _⟩,  
  obtain ⟨f, hf, rfl⟩ := h, 
  rwa [←mem_singleton_iff.mp heC],
end 

lemma circuit_iff_mem_minimals : M.circuit C ↔ C ∈ minimals (⊆) {X | ¬M.indep X ∧ X ⊆ M.E} :=
⟨λ h, ⟨⟨h.1.1,h.2⟩,λ D hD hDC, h.1.2 hD.1 hDC⟩,
  λ h, ⟨⟨h.1.1,λ D hD hDC, h.2 ⟨hD, hDC.trans h.1.2⟩ hDC⟩,h.1.2⟩⟩

lemma indep_iff_forall_subset_not_circuit : M.indep I ↔ (∀ C ⊆ I, ¬M.circuit C) ∧ I ⊆ M.E :=
begin
  simp_rw [indep_iff_coe, matroid.indep_iff_forall_subset_not_circuit, matroid_in.circuit, 
    not_and], 
  refine ⟨λ h, ⟨λ C hCI hC, (h C hCI hC).elim, λ e heI, by_contra (λ heE, _)⟩,λ h C hCI hC, _⟩, 
  { have hl := matroid.loop.circuit (loop_coe_of_not_mem_ground heE),
    exact h {e} (singleton_subset_iff.mpr heI) hl },
  exact h.1 C hCI hC (hCI.trans h.2),
end    

@[simp] lemma equiv_subtype.circuit_iff {E : set α} {C : set E} 
(M : {M : matroid_in α // M.E = E}) :
  (equiv_subtype M).circuit C ↔ (M : matroid_in α).circuit (coe '' C) :=
begin
  obtain ⟨M,rfl⟩ := M,   
  simp_rw [circuit, equiv_subtype_apply, preimage.circuit_iff, coe_coe, 
    function.embedding.coe_subtype, iff_self_and, coe_mk, ←@range_coe _ M.E, 
    iff_true_intro (image_subset_range _ _), imp_true_iff], 
end 

@[simp] lemma equiv_subtype.symm_circuit_iff {E C : set α} (M : matroid E) : 
  (equiv_subtype.symm M : matroid_in α).circuit C ↔ M.circuit (coe ⁻¹' C) ∧ C ⊆ E  :=
begin
  rw [←equiv.apply_symm_apply (equiv_subtype) M, equiv_subtype.circuit_iff, 
    equiv.apply_symm_apply, image_preimage_coe],  
  refine ⟨λ h, _,_⟩,
  { have hCE : C ⊆ E := h.subset_ground, 
    exact ⟨by rwa inter_eq_self_of_subset_left hCE, hCE⟩ }, 
  rintro ⟨h₁,h₂⟩, 
  rwa inter_eq_self_of_subset_left h₂ at h₁,  
end   

lemma equiv_subtype.symm_circuit_iff_exists {E C : set α} (M : matroid E) : 
  (equiv_subtype.symm M : matroid_in α).circuit C ↔ ∃ C₀, M.circuit C₀ ∧ C = coe '' C₀ :=
begin
  rw [equiv_subtype.symm_circuit_iff],  
  refine ⟨λ h, ⟨_,h.1, by { rw [eq_comm, image_preimage_eq_iff, range_coe], exact h.2 }⟩, _⟩, 
  rintro ⟨F₀, hF₀, rfl⟩, 
  simp_rw [preimage_image_eq _ coe_injective, ←@range_coe _ E],   
  exact ⟨hF₀, image_subset_range _ _⟩, 
end   

lemma circuit_eq_transfer_set_prop (M : matroid_in α) : 
  M.circuit = transfer_set_prop (λ _, matroid.circuit) M :=
begin
  ext C, 
  simp only [transfer_set_prop_iff, equiv_subtype.circuit_iff, coe_mk, image_preimage_coe], 
  refine ⟨λ h, ⟨_,h.subset_ground⟩, _⟩,
  { rwa [inter_eq_self_of_subset_left h.subset_ground] },
  rintro ⟨hC, hE⟩, 
  rwa inter_eq_self_of_subset_left hE at hC, 
end 

/-- The `girth` of `M` is the length of its smallest finite circuit, or zero if none exists -/
noncomputable def girth (M : matroid_in α) := (equiv_subtype ⟨M,rfl⟩).girth 

lemma girth_eq_zero_iff : M.girth = 0 ↔ ∀ C, M.circuit C → C.infinite :=
begin
  simp_rw [girth, matroid.girth_eq_zero_iff, equiv_subtype.circuit_iff, coe_mk], 
  refine ⟨λ h C hC hCfin, h (coe ⁻¹' C) _ _, λ h C hC hCfin, h _ hC (hCfin.image _)⟩,
  { convert hC, rw [image_preimage_eq_iff, range_coe], exact hC.subset_ground },
  exact hCfin.preimage (coe_injective.inj_on _),
end 

lemma girth_le_iff {k : ℕ} (h : M.girth ≠ 0) : 
  M.girth ≤ k ↔ ∃ C, M.circuit C ∧ C.finite ∧ C.ncard ≤ k :=
begin
  simp_rw [girth, matroid.girth_le_iff h, equiv_subtype.circuit_iff, coe_mk], 
  split, 
  { rintro ⟨C, hC, hCfin, hCcard⟩, 
    refine ⟨_, hC, hCfin.image coe, _⟩,
    rwa ncard_image_of_injective _ coe_injective },
  rintro ⟨C, hC, hCfin, hCcard⟩, 
  refine ⟨coe ⁻¹' C, _, hCfin.preimage (coe_injective.inj_on _), _⟩, 
  { convert hC, rw [image_preimage_eq_iff, range_coe], exact hC.subset_ground },
  rwa ncard_preimage_of_injective_subset_range coe_injective, 
  rw [range_coe], 
  exact hC.subset_ground, 
end 

lemma le_girth_iff {k : ℕ} (h : M.girth ≠ 0) :
  k ≤ M.girth ↔ ∀ C, M.circuit C → C.finite → k ≤ C.ncard :=
begin
  simp_rw [girth, matroid.le_girth_iff h, equiv_subtype.circuit_iff, coe_mk], 
  refine ⟨λ h' C hC hCfin, _, λ h' C hC hCfin, _⟩,
  { convert h' (coe ⁻¹' C) _ _ using 1,
    { rw ncard_preimage_of_injective_subset_range coe_injective, 
      rw [range_coe], exact hC.subset_ground },
    { convert hC, rw [image_preimage_eq_iff, range_coe], exact hC.subset_ground },
    exact hCfin.preimage (coe_injective.inj_on _) },
  convert h' _ hC (hCfin.image coe) using 1, 
  rw [ncard_image_of_injective _ coe_injective], 
end    



-- ### Closure and flats

variables {F₁ F₂ : set α}

/-- A flat is a maximal set having a given basis -/
def flat (M : matroid_in α) (F : set α) := (M : matroid α).flat (F ∪ M.Eᶜ) ∧ F ⊆ M.E

/-- The closure of a set is the intersection of the flats containing it -/
def cl (M : matroid_in α) (X : set α) := (M : matroid α).cl X ∩ M.E

def hyperplane (M : matroid_in α) (H : set α) := (M : matroid α).hyperplane (H ∪ M.Eᶜ) ∧ H ⊆ M.E

lemma cl_eq_coe_cl_inter (M : matroid_in α) (X : set α) : M.cl X = (M : matroid α).cl X ∩ M.E := rfl

lemma cl_coe_eq (M : matroid_in α) (X : set α) : (M : matroid α).cl X = M.cl X ∪ M.Eᶜ :=
begin
  rw [cl, union_distrib_right, union_compl_self, inter_univ, eq_comm, union_eq_left_iff_subset],
  refine subset_trans _ ((M : matroid α).cl_mono (empty_subset X)),
  exact compl_ground_subset_loops_coe _,
end

lemma cl_subset_ground (M : matroid_in α) (X : set α) : M.cl X ⊆ M.E := inter_subset_right _ _

lemma subset_cl (hX : X ⊆ M.E) : X ⊆ M.cl X := subset_inter (matroid.subset_cl M X) hX

lemma r_fin.cl (h : M.r_fin X) : M.r_fin (M.cl X) := 
⟨h.to_coe.to_cl.subset (inter_subset_left _ _), inter_subset_right _ _⟩

lemma r_fin_cl_iff (hX : X ⊆ M.E) : M.r_fin (M.cl X) ↔ M.r_fin X :=
⟨λ h, h.subset (subset_cl hX), r_fin.cl⟩ 

lemma cl_subset_coe_cl (M : matroid_in α) (X : set α) : M.cl X ⊆ (M : matroid α).cl X :=
inter_subset_left _ _

lemma cl_subset (M : matroid_in α) (hXY : X ⊆ Y) : M.cl X ⊆ M.cl Y :=
subset_inter ((M.cl_subset_coe_cl _).trans (matroid.cl_mono M hXY)) (cl_subset_ground _ _)

lemma cl_subset_inter_ground (M : matroid_in α) (hXY : X ⊆ Y) : M.cl X ⊆ M.cl Y ∩ M.E :=
subset_inter (M.cl_subset hXY) (M.cl_subset_ground _) 

lemma cl_eq_cl_inter_ground (M : matroid_in α) (X : set α) : M.cl X = M.cl (X ∩ M.E) :=
begin
  refine (M.cl_subset (inter_subset_left _ _)).antisymm' _,
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

lemma subset_cl_of_subset (hX : X ⊆ M.E) (h : X ⊆ Y) : X ⊆ M.cl Y :=
(subset_cl hX).trans (M.cl_subset h)

lemma subset_cl_iff_cl_subset_cl (hX : X ⊆ M.E) : X ⊆ M.cl Y ↔ M.cl X ⊆ M.cl Y :=
⟨λ h, inter_subset_inter (matroid.cl_subset_cl (h.trans (M.cl_subset_coe_cl _)))
  subset.rfl, λ h, subset_trans (subset_cl hX) h⟩

lemma cl_union_cl_right_eq_cl (M : matroid_in α) (X Y : set α) : M.cl (X ∪ M.cl Y) = M.cl (X ∪ Y) :=
by rw [eq_comm, cl, ←cl_union_cl_right_eq_cl_union, ←cl, eq_comm, cl_eq_cl_inter_ground, 
    eq_comm, cl_eq_cl_inter_ground, inter_distrib_right, ←cl, inter_distrib_right, 
    inter_eq_self_of_subset_left (M.cl_subset_ground Y)]

lemma cl_union_cl_left_eq_cl (M : matroid_in α) (X Y : set α) : M.cl (M.cl X ∪ Y) = M.cl (X ∪ Y) :=
by rw [union_comm, cl_union_cl_right_eq_cl, union_comm]

@[simp] lemma cl_diff_loops_eq_cl (M : matroid_in α) (X : set α) : M.cl (X \ M.cl ∅) = M.cl X := 
by rw [←union_empty (X \ M.cl ∅), ←cl_union_cl_right_eq_cl, diff_union_self, 
  cl_union_cl_right_eq_cl, union_empty]

lemma indep.mem_cl_iff_of_not_mem (hI : M.indep I) (he : e ∈ M.E \ I) : 
  e ∈ M.cl I ↔ ¬M.indep (insert e I) := 
by rw [cl_eq_coe_cl_inter, mem_inter_iff, iff_true_intro he.1, and_true,   
    matroid.indep.mem_cl_iff_of_not_mem hI he.2, indep_iff_coe]
    
lemma indep.not_mem_cl_iff_of_not_mem (hI : M.indep I) (he : e ∈ M.E \ I) : 
  e ∉ M.cl I ↔ M.indep (insert e I) := 
by rw [hI.mem_cl_iff_of_not_mem he, not_not] 
  
lemma mem_cl_iff_exists_circuit_of_not_mem (he : e ∈ M.E \ X) : 
  e ∈ M.cl X ↔ ∃ C, M.circuit C ∧ e ∈ C ∧ C ⊆ insert e X :=
begin
  simp_rw [cl_eq_coe_cl_inter, mem_inter_iff, iff_true_intro he.1, and_true, 
    matroid.mem_cl_iff_exists_circuit_of_not_mem he.2, circuit_coe_iff], 
  apply exists_congr (λ C, _), 
  simp only [mem_compl_iff, exists_prop, and.congr_left_iff, or_iff_left_iff_imp, 
    forall_exists_index, and_imp], 
  rintro h' - x hx rfl, 
  rw [←mem_singleton_iff.mp h'] at hx, 
  exact (hx he.1).elim, 
end      

lemma hyperplane.subset_ground (hH : M.hyperplane H) : H ⊆ M.E := hH.2 

lemma hyperplane.coe_union_hyperplane (hH : M.hyperplane H) : 
  (M : matroid α).hyperplane (H ∪ M.Eᶜ) := hH.1

lemma hyperplane_iff_coe : M.hyperplane H ↔ (M : matroid α).hyperplane (H ∪ M.Eᶜ) ∧ H ⊆ M.E := 
iff.rfl    

lemma mem_cl_iff_forall_hyperplane (he : e ∈ M.E) (hX : X ⊆ M.E) : 
  e ∈ M.cl X ↔ ∀ H, M.hyperplane H → X ⊆ H → e ∈ H :=
begin
  simp_rw [cl_eq_coe_cl_inter, mem_inter_iff, and_iff_left he, matroid.mem_cl_iff_forall_hyperplane, 
    hyperplane_iff_coe], 
  refine ⟨λ h H hH hXH, (h _ hH.1 (hXH.trans (subset_union_left _ _))).elim id (λ h', (h' he).elim),
    λ h H hH hXH, _⟩, 
  refine (h (H ∩ M.E) ⟨_, inter_subset_right _ _⟩ (subset_inter hXH hX)).1, 
  rw [union_distrib_right, union_compl_self, inter_univ], 
  convert hH, 
  rw [union_eq_left_iff_subset, ←hH.flat.cl], 
  exact M.compl_ground_subset_loops_coe.trans (matroid.cl_mono M (empty_subset _)), 
end    

lemma basis.subset_cl (hIX : M.basis I X) : X ⊆ M.cl I :=
subset_inter (matroid.basis.subset_cl hIX.1) hIX.subset_ground

lemma base.cl (hB : M.base B) : M.cl B = M.E := by rw [cl, matroid.base.cl hB, univ_inter]

lemma basis.cl (hIX : M.basis I X) : M.cl I = M.cl X := by rw [cl, cl, hIX.to_coe.cl]

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

lemma flat_iff_cl_self : M.flat F ↔ M.cl F = F :=
begin
  refine ⟨flat.cl,λ h, _⟩, 
  rw [cl] at h, 
  rw [flat, flat_iff_cl_self, cl_union_eq_cl_of_subset_loops (M.compl_ground_subset_loops_coe)], 
  nth_rewrite 2 ←h, 
  nth_rewrite 0 ←inter_union_compl ((M : matroid α).cl F) M.E,  
  rw [and_iff_left (inter_subset_right _ _), h], 
  convert rfl, 
  rw [eq_comm, inter_eq_right_iff_subset], 
  exact M.compl_ground_subset_loops_coe.trans (cl_mono _ (empty_subset _)), 
end 

lemma flat_of_cl (M : matroid_in α) (X : set α) : M.flat (M.cl X) := by rw [flat_iff_cl_self, cl_cl]

/-- Flats of `M : matroid_in α` correspond to those in `(↑M : matroid α)` -/
def flat_coe_equiv (M : matroid_in α) : {F // M.flat F} ≃ {F // (M : matroid α).flat F} :=
{ to_fun := λ F, ⟨F ∪ M.Eᶜ, F.2.1⟩,
  inv_fun := λ F, ⟨F ∩ M.E, 
  begin
    rw [flat, and_iff_left (inter_subset_right _ _), union_distrib_right, union_compl_self, 
      inter_univ, union_eq_self_of_subset_right], 
    { exact F.2 }, 
    exact M.compl_ground_subset_loops_coe.trans F.2.loops_subset, 
  end⟩,
  left_inv := 
  begin
    rintro ⟨F,hF⟩, 
    simp only [coe_mk, inter_distrib_right, compl_inter_self, union_empty, 
      inter_eq_self_of_subset_left hF.subset_ground]
  end,
  right_inv := 
  begin
    rintro ⟨F,hF⟩, 
    simp only [coe_mk, union_distrib_right, union_compl_self, inter_univ, union_eq_left_iff_subset], 
    exact M.compl_ground_subset_loops_coe.trans hF.loops_subset,      
  end }

@[simp] lemma flat_coe_equiv_apply (M : matroid_in α) (F : {F // M.flat F}) : 
  (M.flat_coe_equiv F : set α) = F ∪ M.Eᶜ := rfl  

@[simp] lemma flat_coe_equiv_apply_symm (M : matroid_in α) (F : {F // (M : matroid α).flat F}) : 
  (M.flat_coe_equiv.symm F : set α) = F ∩ M.E := rfl 

@[simp] lemma equiv_subtype.cl_eq {E : set α} (X : set E) (M : {M : matroid_in α // M.E = E}) :
  (equiv_subtype M).cl X = coe ⁻¹' (M : matroid_in α).cl (coe '' X) :=
begin
  obtain ⟨M, rfl⟩ := M, 
  rw [coe_mk], 
  refine set.ext (λ e, (em (e ∈ X)).elim (λ he, _) (λ he, _)), 
  { refine iff_of_true (matroid.mem_cl_of_mem _ he) (matroid_in.subset_cl _ ⟨e, he, rfl⟩),
    convert image_subset_range _ _, 
    rw range_coe },
  rw [matroid.mem_cl_iff_exists_circuit_of_not_mem he, mem_preimage, cl, mem_inter_iff,   
    matroid.mem_cl_iff_exists_circuit_of_not_mem], 
  { simp only [equiv_subtype.circuit_iff, coe_mk, coe_prop, and_true, ← image_insert_eq],
    split, 
    { rintro ⟨C, hC, heC, hC'⟩, exact ⟨coe '' C, hC.to_coe, ⟨e,heC,rfl⟩, image_subset _ hC'⟩ },
    rintro ⟨C, hC, heC, hC'⟩, 
    obtain ⟨C₀,rfl⟩ := subset_range_iff_exists_image_eq.mp (hC'.trans (image_subset_range _ _)),     
    rw image_subset_image_iff coe_injective at hC', 
    rw coe_injective.mem_set_image at heC, 
    exact ⟨C₀, ⟨hC, (image_subset_range _ _).trans_eq range_coe⟩, heC, hC'⟩ },
  rwa [coe_injective.mem_set_image], 
end 

@[simp] lemma equiv_subtype.symm_cl_eq {E X : set α} (M : matroid E) : 
  (equiv_subtype.symm M : matroid_in α).cl X = coe '' (M.cl (coe ⁻¹' X)) :=
begin
  set N := equiv_subtype.symm M with hN, 
  have hM : M = equiv_subtype N, rw [hN, equiv.apply_symm_apply], 
  rw [hM, equiv_subtype.cl_eq, image_preimage_eq_inter_range, image_preimage_eq_inter_range, 
    inter_eq_self_of_subset_left, cl_eq_cl_inter_ground, range_coe],
  { convert rfl },
  rw range_coe, 
  convert cl_subset_ground _ _,
end 

@[simp] lemma equiv_subtype.flat_iff {E : set α} {F : set E} (M : {M : matroid_in α // M.E = E}) :
  (equiv_subtype M).flat F ↔ (M : matroid_in α).flat (coe '' F) := 
begin
  rw [flat_iff_cl_self, matroid.flat_iff_cl_self, equiv_subtype.cl_eq, 
    ←image_eq_image coe_injective, image_preimage_eq_iff.mpr], 
  convert cl_subset_ground _ _,
  rw [range_coe], 
  exact M.2.symm, 
end 

@[simp] lemma equiv_subtype.symm_flat_iff {E F : set α} (M : matroid E) : 
  (equiv_subtype.symm M : matroid_in α).flat F ↔ M.flat (coe ⁻¹' F) ∧ F ⊆ E  :=
begin
  rw [←equiv.apply_symm_apply (equiv_subtype) M, equiv_subtype.flat_iff, 
    equiv.apply_symm_apply, image_preimage_coe],  
  refine ⟨λ h, _,_⟩,
  { have hFE : F ⊆ E := h.subset_ground, 
    exact ⟨by rwa inter_eq_self_of_subset_left hFE, hFE⟩ }, 
  rintro ⟨h₁,h₂⟩, 
  rwa inter_eq_self_of_subset_left h₂ at h₁,  
end   

lemma equiv_subtype.symm_flat_iff_exists {E F : set α} (M : matroid E) : 
  (equiv_subtype.symm M : matroid_in α).flat F ↔ ∃ F₀, M.flat F₀ ∧ F = coe '' F₀ :=
begin
  rw [equiv_subtype.symm_flat_iff],  
  refine ⟨λ h, ⟨_,h.1, by { rw [eq_comm, image_preimage_eq_iff, range_coe], exact h.2 }⟩, _⟩, 
  rintro ⟨F₀, hF₀, rfl⟩, 
  simp_rw [preimage_image_eq _ coe_injective, ←@range_coe _ E],   
  exact ⟨hF₀, image_subset_range _ _⟩, 
end   

lemma flat_eq_transfer_set_prop (M : matroid_in α) : M.flat = transfer_set_prop (λ _, matroid.flat) M := 
begin
  ext F, 
  simp only [transfer_set_prop_iff, equiv_subtype.flat_iff, coe_mk, image_preimage_coe], 
  exact ⟨λ h, ⟨by rwa inter_eq_self_of_subset_left h.subset_ground,h.subset_ground⟩, 
    λ h, by { rw ←inter_eq_self_of_subset_left h.2, exact h.1 }⟩,
end 

lemma flat.exists_eq_coe (h : M.flat F) : 
  ∃ F₀ : set M.E, (equiv_subtype ⟨M,rfl⟩).flat F₀ ∧ F = coe '' F₀  :=
by { rw [flat_eq_transfer_set_prop] at h, exact h.exists_eq_coe,  }

def covby (M : matroid_in α) := transfer_set_prop₂ (λ _, matroid.covby) M

lemma covby_iff : M.covby F₁ F₂ ↔ M.flat F₁ ∧ M.flat F₂ ∧ F₁ ⊂ F₂ ∧ 
  ∀ F, M.flat F → F₁ ⊆ F → F ⊆ F₂ → F = F₁ ∨ F = F₂ :=
begin
  
  
  
  
  
  split, 
  
  { revert F₁ F₂,
    simp_rw [covby, transfer_set_prop₂_forall_iff, matroid.covby_iff, 
      equiv_subtype.flat_iff, coe_mk, flat_eq_transfer_set_prop, transfer_set_prop_forall_iff, 
      ssubset_iff_subset_not_subset, image_coe_subset_image_coe_iff, image_coe_eq_image_coe_iff, 
      ←flat_eq_transfer_set_prop, equiv_subtype.flat_iff, coe_mk],
    exact λ _ _, id }, 

  simp_rw [and_imp, flat_eq_transfer_set_prop], 
  revert F₁,
  simp,  
  -- simp only [transfer_set_prop_forall_iff, equiv_subtype.flat_iff, coe_mk, image_subset_iff, 
  --   image_coe_subset_image_coe_iff, image_coe_eq_image_coe_iff], 
  
  -- rw [and_imp, and_imp, flat_eq_transfer_set_prop], 
  -- revert F₁ F₂, 
  revert F₁, 
  
  
  simp only [transfer_set_prop_forall_iff, equiv_subtype.flat_iff, coe_mk, image_subset_iff, and_imp], 
   
   
  

  
  simp only [flat_eq_transfer_set_prop], simp, 
  
--     },
  -- rw [covby, iff_def], 


  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨F₁,F₂,hc,rfl,rfl⟩ := h.exists_eq_coe,
    simp_rw [matroid.covby_iff, equiv_subtype.flat_iff, coe_mk, ssubset_iff_subset_not_subset] 
      at hc, 
    simp_rw [ssubset_iff_subset_not_subset, image_subset_image_iff coe_injective], 
    refine ⟨hc.1, hc.2.1, hc.2.2.1, λ F hF hF₁F hFF₂, _ ⟩,  
    obtain ⟨F, hF', rfl⟩ := hF.exists_eq_coe,     
    rw [image_subset_image_iff coe_injective] at hF₁F hFF₂, 
    simp_rw [image_eq_image coe_injective], 
    exact hc.2.2.2 F hF hF₁F hFF₂ },

  
  obtain ⟨F₁, hF₁, rfl⟩ := h.1.exists_eq_coe,  
  obtain ⟨F₂, hF₂, rfl⟩ := h.2.1.exists_eq_coe,  
  
  simp only [covby, transfer_set_prop₂_iff, matroid.covby_iff, preimage_image_coe, 
    equiv_subtype.flat_iff, coe_mk, image_subset_iff, coe_preimage_self, subset_univ, and_true, 
    ssubset_iff_subset_not_subset],

  simp_rw [ssubset_iff_subset_not_subset, image_coe_subset_image_coe_iff] at h, 
  -- refine (em (F₁ ⊆ M.E)).symm.elim (λ hnss, iff_of_false _ _) (λ hF₁E, _), 
  -- { rw [covby, transfer_set_prop₂_iff], tauto },
  -- { exact λ h, hnss h.1.subset_ground },
  -- refine (em (F₂ ⊆ M.E)).symm.elim (λ hnss, iff_of_false _ _) (λ hF₂E, _), 
  -- { rw [covby, transfer_set_prop₂_iff], tauto },
  -- { exact λ h, hnss h.2.1.subset_ground },
  -- rw [←@range_coe _ M.E] at hF₁E hF₂E, 
  -- obtain ⟨F₁, rfl⟩ := subset_range_iff_exists_image_eq.mp hF₁E, 
  -- obtain ⟨F₂, rfl⟩ := subset_range_iff_exists_image_eq.mp hF₂E, 

  simp only [covby, matroid.covby_iff, transfer_set_prop₂_iff, preimage_image_coe, 
    equiv_subtype.flat_iff, coe_mk, image_subset_iff, coe_preimage_self, subset_univ, and_true, 
    and.congr_right_iff, ssubset_iff_subset_not_subset, image_subset_image_iff coe_injective], 
     
  
  
  refine λ hF₁ hF₂ hss, ⟨λ h F hF hF₁F hFF₂, _, λ h, _⟩,
  
  -- have := h (coe ⁻¹' F), 
  

  -- simp_rw [covby, transfer_set_prop₂_iff, matroid.covby_iff, equiv_subtype.flat_iff, coe_mk, 
  --   image_preimage_coe, inter_eq_self_of_subset_left hF₁E, inter_eq_self_of_subset_left hF₂E, 
  --   and_iff_right hF₁E, and_iff_left hF₂E, and.congr_right_iff], 

  -- refine (em (F₁ ⊆ M.E)).symm.elim (λ hnss, iff_of_false _ _) (λ hF₁E, _), 
  -- { rw [covby, transfer_set_prop₂_iff], tauto },
  -- { exact λ h, hnss h.1.subset_ground },
  -- refine (em (F₂ ⊆ M.E)).symm.elim (λ hnss, iff_of_false _ _) (λ hF₂E, _), 
  -- { rw [covby, transfer_set_prop₂_iff], tauto },
  -- { exact λ h, hnss h.2.1.subset_ground },
  -- rw [←@range_coe _ M.E] at hF₁E hF₂E, 
  -- obtain ⟨F₁, rfl⟩ := subset_range_iff_exists_image_eq.mp hF₁E, 
  -- obtain ⟨F₂, rfl⟩ := subset_range_iff_exists_image_eq.mp hF₂E, 

  -- simp_rw [covby, flat_eq_transfer_set_prop, transfer_set_prop₂_coe_iff, 
  --   transfer_set_prop_coe_iff, matroid.covby_iff, equiv_subtype.flat_iff, coe_mk],
  --   simp, 
  

  -- -- squeeze_simp [covby, matroid.covby_iff], 

  -- simp_rw [covby, transfer_set_prop₂_iff, matroid.covby_iff, equiv_subtype.flat_iff, coe_mk, 
  --   image_preimage_coe, inter_eq_self_of_subset_left hF₁E, inter_eq_self_of_subset_left hF₂E, 
  --   and_iff_right hF₁E, and_iff_left hF₂E, and.congr_right_iff], 
    
  -- -- have := matroid.covby_iff, 

end 

lemma covby.flat_left (h : M.covby F₁ F₂) : M.flat F₁ := 
begin
  rw [←h.inter_ground_left], 
  simp only [covby, transfer_set_prop₂_iff] at h, 
  simpa using h.1.flat_left, 
end 

lemma covby.flat_right (h : M.covby F₁ F₂) : M.flat F₂ := 
begin
  rw [←h.inter_ground_right], 
  simp only [covby, transfer_set_prop₂_iff] at h, 
  simpa using h.1.flat_right, 
end 

lemma covby.ssubset (h : M.covby F₁ F₂) : F₁ ⊂ F₂ :=
begin
  
end  

-- ### loops and nonloops

/-- A `loop` is a dependent singleton (that is contained in the ground set )-/
def loop (M : matroid_in α) (e : α) : Prop := (M : matroid α).loop e ∧ e ∈ M.E

/-- A `nonloop` is an independent singleton -/
def nonloop (M : matroid_in α) (e : α) : Prop := (M : matroid α).nonloop e

/-- A `coloop` is a loop of the dual matroid -/
def coloop (M : matroid_in α) (e : α) : Prop := (M : matroid α).coloop e
  
lemma loop.mem_ground (he : M.loop e) : e ∈ M.E := he.2

lemma loop.dep (he : M.loop e) : ¬ M.indep {e} := matroid.loop.dep he.1

lemma loop.to_coe (he : M.loop e) : (M : matroid α).loop e := he.1

lemma loop_iff_dep (he : e ∈ M.E) : M.loop e ↔ ¬ M.indep {e} :=
⟨loop.dep, λ h, ⟨matroid.loop_iff_dep.mpr h, he⟩⟩

lemma loop_iff_circuit : M.loop e ↔ M.circuit {e} := 
begin
  refine (em (e ∈ M.E)).symm.elim (λ he, iff_of_false (λ hl, he hl.mem_ground) 
    (λ hC, he (hC.subset_ground (mem_singleton e)))) (λ he, _), 
  rw [loop_iff_dep he, circuit, indep_iff_coe, circuit_iff_dep_forall_diff_singleton_indep, 
    and_assoc], 
  simp only [indep_singleton, not_nonloop_iff, mem_singleton_iff, forall_eq, diff_self, empty_indep, 
    singleton_subset_iff, true_and, iff_self_and, iff_true_intro he, imp_true_iff], 
end

lemma loop_iff_mem_cl_empty : M.loop e ↔ e ∈ M.cl ∅ := iff.rfl

lemma nonloop_iff_coe (e : α) : M.nonloop e ↔ (M : matroid α).nonloop e := iff.rfl

lemma nonloop.to_coe (he : M.nonloop e) : (M : matroid α).nonloop e := he

@[simp] lemma indep_singleton : M.indep {e} ↔ M.nonloop e := matroid.indep_singleton

alias indep_singleton ↔ indep.nonloop nonloop.indep

@[simp] lemma equiv_subtype.nonloop_iff {E : set α} {M : {M : matroid_in α // M.E = E}} {e : E} : 
  (equiv_subtype M).nonloop e ↔ (M : matroid_in α).nonloop (e : α) :=
by simp [←matroid.indep_singleton]

@[simp] lemma equiv_subtype.symm_nonloop_iff {E : set α} {M : matroid E} {e : α} : 
  (equiv_subtype.symm M : matroid_in α).nonloop e ↔ ∃ f, M.nonloop f ∧ e = f :=
begin
  simp_rw [←indep_singleton, equiv_subtype.symm_indep_iff, singleton_subset_iff, 
    ←matroid.indep_singleton, ←@range_coe _ E, mem_range], 
  split, 
  { rintro ⟨hi, ⟨y,rfl⟩⟩, 
    rw [←image_singleton, preimage_image_coe] at hi,
    exact ⟨_, hi, rfl⟩ },
  rintro ⟨f, hf, rfl⟩, 
  rw [←image_singleton, preimage_image_coe ], 
  exact ⟨hf, _, rfl⟩, 
end 

-- by simp_rw [←indep_singleton, equiv_subtype.symm_indep_iff, ←image_singleton, preimage_image_coe, 
--     ←@range_coe _ E, and_iff_left (image_subset_range _ _), matroid.indep_singleton]

attribute [protected] indep.nonloop nonloop.indep

lemma nonloop.mem_ground (he : M.nonloop e) : e ∈ M.E :=
singleton_subset_iff.mp he.indep.subset_ground

lemma nonloop_of_not_mem_cl (he : e ∈ M.E) (h : e ∉ M.cl X) : M.nonloop e :=
nonloop_of_not_mem_cl (λ h', h ⟨h',he⟩)

/-- A `loopless` matroid is one with no loop-/
def loopless (M : matroid_in α) := ∀ e ∈ M.E, M.nonloop e 

@[simp] lemma equiv_subtype.loopless_iff {E : set α} {M : {M : matroid_in α // M.E = E}} : 
  (equiv_subtype M).loopless ↔ (M : matroid_in α).loopless :=
by { obtain ⟨M, rfl⟩ := M, simp [loopless, matroid.loopless] }

lemma loopless_iff_girth_ne_one : M.loopless ↔ M.girth ≠ 1 :=
begin
  convert (@equiv_subtype.loopless_iff _ _ ⟨M,rfl⟩).symm, 
  rw [loopless_iff_girth_ne_one, girth], 
end 

lemma loopless_iff_forall_circuit : M.loopless ↔ ∀ C, M.circuit C → C.finite → 1 < C.ncard :=
begin
  convert (@equiv_subtype.loopless_iff _ _ ⟨M,rfl⟩).symm, 
  simp_rw [loopless_iff_forall_circuit, equiv_subtype.circuit_iff, coe_mk, eq_iff_iff], 
  
  refine ⟨λ h C hC hCfin, _, λ h C hC hCfin, _⟩,
  { rw ←ncard_image_of_injective C coe_injective, 
    exact h _ hC (hCfin.image coe) },
  have hcoe : (coe : M.E → α) '' (coe ⁻¹' C) = C, 
  { rw [image_preimage_eq_iff, range_coe], exact hC.subset_ground },
  convert h (coe ⁻¹' C) _ (hCfin.preimage (coe_injective.inj_on _)) using 1,
  { rw [←ncard_image_of_injective _ coe_injective, hcoe] },
  rwa hcoe, 
end 

@[simp] lemma equiv_subtype.symm_loopless_iff {E : set α} (M : matroid E) : 
  (equiv_subtype.symm M : matroid_in α).loopless ↔ M.loopless :=
by { rw [loopless_iff_girth_ne_one, matroid.loopless_iff_girth_ne_one, girth], simp }

/-- A `simple` matroid is one with no parallel pair -/
def simple (M : matroid_in α) := ∀ e f ∈ M.E, M.indep {e,f} 

@[simp] lemma equiv_subtype.simple_iff {E : set α} {M : {M : matroid_in α // M.E = E}} : 
  (equiv_subtype M).simple ↔ (M : matroid_in α).simple :=
by { obtain ⟨M, rfl⟩ := M, simp [simple, matroid.simple, image_pair] }

lemma simple_iff_girth : M.simple ↔ M.girth = 0 ∨ 2 < M.girth :=
begin
  convert (@equiv_subtype.simple_iff _ _ ⟨M,rfl⟩).symm, 
  rw [eq_iff_iff, matroid.simple_iff_girth, girth], 
end 

@[simp] lemma equiv_subtype.symm_simple_iff {E : set α} (M : matroid E) : 
  (equiv_subtype.symm M : matroid_in α).simple ↔ M.simple :=
by rw [simple_iff_girth, matroid.simple_iff_girth, girth, coe_eta, equiv.apply_symm_apply]

/-! Rank -/

/-- The rank of a set `X`. This is equal to the rank of `X ∩ M.E` in the coercion. -/
noncomputable def r (M : matroid_in α) (X : set α) := (M : matroid α).r X

/-- The rank of the ground set `M.E` -/
noncomputable def rk (M : matroid_in α) : ℕ := (M : matroid α).rk

lemma le_r_iff {n : ℕ} [finite α] : n ≤ M.r X ↔ ∃ I ⊆ X, M.indep I ∧ I.ncard = n := matroid.le_r_iff

lemma r_le_iff {n : ℕ} [finite α] : M.r X ≤ n ↔ ∀ I ⊆ X, M.indep I → I.ncard ≤ n := matroid.r_le_iff

lemma r_eq_coe_r (X : set α) : M.r X = (M : matroid α).r X := rfl

@[simp] lemma r_compl_ground : M.r M.Eᶜ = 0 := 
  r_eq_zero_of_subset_loops (compl_ground_subset_loops_coe _)

lemma coe_r_compl_ground (M : matroid_in α) : (M : matroid α).r M.Eᶜ = 0 := r_compl_ground

lemma r_eq_r_inter_ground (X : set α):
  M.r X = M.r (X ∩ M.E) :=
by rw [r_eq_coe_r, ←matroid.r_cl, 
    ←matroid.cl_diff_eq_cl_of_subset_loops (M.compl_ground_subset_loops_coe) X, 
    diff_eq, compl_compl, matroid.r_cl, ←r_eq_coe_r ]

@[simp] lemma coe_r_union_compl_ground (M : matroid_in α) (X : set α) : 
  (M : matroid α).r (X ∪ M.Eᶜ) = M.r X :=
by rw [←r, r_eq_r_inter_ground, inter_distrib_right, compl_inter_self, union_empty,
  ←r_eq_r_inter_ground]

@[simp] lemma r_union_compl_ground (M : matroid_in α) (X : set α) : M.r (X ∪ M.Eᶜ) = M.r X :=
M.coe_r_union_compl_ground X 

lemma rk_eq_rk_coe (M : matroid_in α) : M.rk = (M : matroid α).rk := rfl

lemma rk_eq_r_ground (M : matroid_in α) : M.rk = M.r M.E :=
by rw [rk, matroid.rk_def, ←r_eq_coe_r, r_eq_r_inter_ground, univ_inter]

@[simp] lemma r_cl (M : matroid_in α) (X : set α) : M.r (M.cl X) = M.r X := 
by rw [r, r, ←(M : matroid α).r_cl X, cl, ←r, ←r, ←r_eq_r_inter_ground]

@[simp] lemma r_empty (M : matroid_in α) : M.r ∅ = 0 := matroid.r_empty M  

lemma indep.r (hI : M.indep I) : M.r I = I.ncard := matroid.indep.r hI

lemma indep_iff_r_eq_card [finite α] : M.indep I ↔ M.r I = I.ncard := matroid.indep_iff_r_eq_card

lemma indep_iff_r_eq_card_of_finite (hI : I.finite) : 
  M.indep I ↔ M.r I = I.ncard := matroid.indep_iff_r_eq_card_of_finite hI 

lemma basis.r (hIX : M.basis I X) : M.r I = M.r X := matroid.basis.r hIX.to_coe

lemma basis.card (hIX : M.basis I X) : I.ncard = M.r X := matroid.basis.card hIX.to_coe 

lemma nonloop.r (he : M.nonloop e) : M.r {e} = 1 := he.r 

@[simp] lemma equiv_subtype.r_eq {E : set α} (M : {M : matroid_in α // M.E = E}) (X : set E) :
  (equiv_subtype M).r X = (M : matroid_in α).r (coe '' X) :=
by simp [equiv_subtype_apply, r]

@[simp] lemma equiv_subtype.symm_r_eq {E : set α} (M : matroid E) (X : set α) :
  (equiv_subtype.symm M : matroid_in α).r X = M.r (coe ⁻¹' X) :=
by simp [r, equiv_subtype_apply_symm_coe_coe]

-- ### Cocircuits etc

/-- A `cocircuit` is a minimal transversal of bases. -/
def cocircuit (M : matroid_in α) (K : set α) := (M : matroid α).cocircuit K
  
/-- A `coindep`endent set is one whose complement (relative to the ground set) contains a base -/
def coindep (M : matroid_in α) (X : set α) := (M : matroid α).coindep X ∧ X ⊆ M.E

lemma cocircuit_iff_coe (K : set α) : M.cocircuit K ↔ (M : matroid α).cocircuit K := iff.rfl

lemma cocircuit.subset_ground (hK : M.cocircuit K) : K ⊆ M.E :=
λ x hx, matroid_in.nonloop.mem_ground (hK.nonloop_of_mem hx)

lemma cocircuit_iff_mem_minimals : 
  M.cocircuit K ↔ K ∈ minimals (⊆) {X | ∀ B, M.base B → (B ∩ X).nonempty } :=
by simp_rw [cocircuit, matroid.cocircuit_iff_mem_minimals, base_iff_coe]

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

lemma compl_hyperplane_iff_cocircuit (hK : K ⊆ M.E) : M.hyperplane (M.E \ K) ↔ M.cocircuit K :=
by rw [cocircuit, ←matroid.compl_hyperplane_iff_cocircuit, hyperplane, 
    and_iff_left (diff_subset _ _), diff_eq, union_distrib_right, union_compl_self, univ_inter, 
    ←compl_inter, inter_eq_self_of_subset_left hK]

lemma compl_cocircuit_iff_hyperplane (hH : H ⊆ M.E) : M.cocircuit (M.E \ H) ↔ M.hyperplane H :=
by rw [←compl_hyperplane_iff_cocircuit (diff_subset _ _), diff_diff_cancel_left hH] 

lemma cocircuit.compl_hyperplane (hK : M.cocircuit K) : M.hyperplane (M.E \ K) := 
(compl_hyperplane_iff_cocircuit hK.subset_ground).mpr hK

lemma hyperplane.compl_cocircuit (hH : M.hyperplane H) : M.cocircuit (M.E \ H) :=
(compl_cocircuit_iff_hyperplane hH.subset_ground).mpr hH 

/-! ### Skewness -/

/-- Two sets are `skew` if contracting one does not affect the restriction to the other. -/
def skew (M : matroid_in α) (X Y : set α) := (M : matroid α).skew X Y ∧ X ⊆ M.E ∧ Y ⊆ M.E

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

lemma skew_iff_cl_left (hX : X ⊆ M.E) : M.skew X Y ↔ M.skew (M.cl X) Y := 
⟨skew.cl_left, λ h, h.subset_left (subset_cl hX)⟩   

lemma skew_iff_cl_right (hY : Y ⊆ M.E) : M.skew X Y ↔ M.skew X (M.cl Y) := 
⟨skew.cl_right, λ h, h.subset_right (subset_cl hY)⟩

lemma skew.inter_subset_loops (h : M.skew X Y) : X ∩ Y ⊆ M.cl ∅ := 
subset_inter (matroid.skew.inter_subset_loops h.1) 
  ((inter_subset_right _ _).trans h.right_subset_ground) 

lemma skew.disjoint_of_indep_left (h : M.skew I X) (hI : M.indep I) : disjoint I X := 
h.to_coe.disjoint_of_indep_left hI

lemma skew.disjoint_of_indep_right (h : M.skew X I) (hI : M.indep I) : disjoint X I :=
(h.symm.disjoint_of_indep_left hI).symm

lemma skew_iff_disjoint_of_union_indep (h : M.indep (I ∪ J)) : M.skew I J ↔ disjoint I J :=
by rw [←matroid.skew_iff_disjoint_of_union_indep h, skew, ←union_subset_iff, 
  and_iff_left h.subset_ground]

lemma indep.skew_diff_of_subset (hI : M.indep I) (hJ : J ⊆ I) : M.skew J (I \ J) :=
⟨matroid.indep.skew_diff_of_subset hI hJ, (hJ.trans hI.subset_ground), 
  (diff_subset _ _).trans hI.subset_ground⟩ 

lemma skew.diff_loops_disjoint_left (h : M.skew X Y) : disjoint (X \ M.cl ∅) Y :=
begin
  convert matroid.skew.diff_loops_disjoint_left h.1 using 1,
  rw [cl_coe_eq, ←diff_diff, diff_eq, diff_eq, compl_compl, eq_comm, inter_eq_left_iff_subset],
  exact (inter_subset_left _ _).trans h.left_subset_ground,  
end 

lemma skew.diff_loops_disjoint_right (h : M.skew X Y) : disjoint X (Y \ M.cl ∅) :=
(h.symm.diff_loops_disjoint_left).symm

lemma skew_iff_diff_loops_skew_left : M.skew X Y ↔ M.skew (X \ M.cl ∅) Y := 
begin
  refine (em (X ⊆ M.E)).symm.elim (λ hX, iff_of_false (λ h', hX h'.left_subset_ground) (λ h', hX _)) 
    (λ hX, _), 
  { have h'' := h'.left_subset_ground, 
    rwa [diff_subset_iff, union_eq_self_of_subset_left (M.cl_subset_ground _)] at h'' },
  rw [iff.comm, skew_iff_cl_left ((diff_subset _ _).trans hX), cl_diff_loops_eq_cl,   
    ←skew_iff_cl_left hX], 
end 

lemma skew.union_indep (h : M.skew I J) (hI : M.indep I) (hJ : M.indep J) : M.indep (I ∪ J) :=
h.to_coe.union_indep hI hJ

lemma nonloop.singleton_skew_iff (he : M.nonloop e) (hX : X ⊆ M.E) : M.skew {e} X ↔ e ∉ M.cl X :=
by rw [skew, he.to_coe.singleton_skew_iff, singleton_subset_iff, cl_eq_coe_cl_inter, mem_inter_iff,
    ←(true_iff _).mpr hX, and_true, ←(true_iff _).mpr he.mem_ground, and_true, and_true]

lemma nonloop.skew_singleton_iff (he : M.nonloop e) (hX : X ⊆ M.E) : M.skew X {e} ↔ e ∉ M.cl X :=
by rw [skew.comm, he.singleton_skew_iff hX]

-- TODO : hyperplanes, flats, cl definitions are equivalent to the usual ones.

lemma eq_of_coe_eq_coe {M₁ M₂ : matroid_in α} (h : M₁.E = M₂.E) (h' : (M₁ : matroid α) = M₂) :
  M₁ = M₂ :=
by { ext, rw [ground_eq_E,h,ground_eq_E], simp_rw [carrier_eq_coe, h'] }

lemma eq_iff_coe_eq_coe {M₁ M₂ : matroid_in α} : (M₁.E = M₂.E ∧ (M₁ : matroid α) = M₂ ) ↔ M₁ = M₂ := 
⟨λ h, eq_of_coe_eq_coe h.1 h.2, by { rintro rfl, simp  }⟩   

end basic

section ext

lemma eq_of_base_iff_base_forall {M₁ M₂ : matroid_in α} (hE : M₁.E = M₂.E)
(h' : ∀ B ⊆ M₁.E, M₁.base B ↔ M₂.base B) : M₁ = M₂ :=
begin
  ext, rw [ground_eq_E, hE, ←ground_eq_E],
  exact ⟨λ h, (h' _ (base.subset_ground h)).mp h,
    λ h, (h' _ ((base.subset_ground h).trans_eq hE.symm)).mpr h⟩,
end

lemma eq_of_indep_iff_indep_forall {M₁ M₂ : matroid_in α} (hE : M₁.E = M₂.E)
(h' : ∀ I ⊆ M₁.E, M₁.indep I ↔ M₂.indep I) :
  M₁ = M₂ :=
begin
  refine eq_of_base_iff_base_forall hE (λ B hB, _),
  simp_rw [base_iff_coe, base_iff_maximal_indep, ←indep_iff_coe],
  exact ⟨λ h, ⟨by { rw ←h' _ h.1.subset_ground, exact h.1 },
    λ I hI hBI, h.2 _ (by rwa h' _ (hI.subset_ground.trans_eq hE.symm)) hBI⟩,
    λ h, ⟨by { rw h' _ (h.1.subset_ground.trans_eq hE.symm), exact h.1 },
    λ I hI hBI, h.2 _ (by { rwa ←h' _ hI.subset_ground}) hBI ⟩⟩,
end

lemma eq_of_cl_eq_cl_forall {M₁ M₂ : matroid_in α} (hE : M₁.E = M₂.E) 
  (h : ∀ X ⊆ M₁.E, M₁.cl X = M₂.cl X) : M₁ = M₂ := 
begin
  refine eq_of_indep_iff_indep_forall hE (λ I hI, _), 
  simp_rw [indep_iff_coe, indep_iff_not_mem_cl_diff_forall, cl_coe_eq, hE], 
  refine ⟨λ h' e heI, _,λ h' e heI, _⟩,
  { rw [←h _ ((diff_subset I {e}).trans hI)], exact h' _ heI },
  rw [h _ ((diff_subset I {e}).trans hI)], exact h' _ heI, 
end 

lemma eq_of_mem_cl_iff_mem_cl_forall {M₁ M₂ : matroid_in α} (hE : M₁.E = M₂.E) 
  (h : ∀ (X ⊆ M₁.E) (e ∈ M₁.E), e ∈ M₁.cl X ↔ e ∈ M₂.cl X ) : M₁ = M₂ :=
begin
  refine eq_of_cl_eq_cl_forall hE (λ X hX, _), 
  rw [←inter_eq_self_of_subset_left (M₁.cl_subset_ground X), 
    ←inter_eq_self_of_subset_left (M₂.cl_subset_ground X)], 
  simp_rw [set.ext_iff, mem_inter_iff, hE, and.congr_left_iff, ←hE], 
  exact h X hX, 
end 

lemma eq_of_r_eq_r_forall {M₁ M₂ : matroid_in α} [finite_rk M₁] (hE : M₁.E = M₂.E)
(h : ∀ X ⊆ M₁.E, M₁.r X = M₂.r X) :
  M₁ = M₂ :=
eq_of_coe_eq_coe hE (eq_of_r_eq_r_forall (λ X, by rw [←r_eq_coe_r, r_eq_r_inter_ground, ←r_eq_coe_r,  
  r_eq_r_inter_ground X, h _ (inter_subset_right _ _), hE] )) 
  
end ext

section dual

/-- The dual of a `matroid_in`. -/
def dual (M : matroid_in α) : matroid_in α := equiv_subtype.symm (equiv_subtype ⟨M, rfl⟩)﹡

instance {α : Type*} : has_matroid_dual (matroid_in α) := ⟨dual⟩ 

lemma dual_eq (M : matroid_in α) : M﹡ = equiv_subtype.symm (equiv_subtype ⟨M, rfl⟩)﹡ := rfl  

@[simp] lemma dual_base_iff : M﹡.base B ↔ M.base (M.E \ B) ∧ B ⊆ M.E :=
begin
  simp_rw [dual_eq, equiv_subtype.symm_base_iff, matroid.dual.base_iff, equiv_subtype.base_iff, 
    coe_mk, and.congr_left_iff, coe_injective.image_compl_eq, 
    image_preimage_eq_inter_range, range_coe], 
  simp only [diff_inter_self_eq_diff, iff_self, implies_true_iff],
end 

@[simp] lemma dual_ground (M : matroid_in α) : M﹡.E = M.E := rfl

@[simp] lemma dual_dual (M : matroid_in α) : M﹡﹡ = M := by simp [dual_eq] 

lemma dual_inj {M₁ M₂ : matroid_in α} (h : M₁﹡ = M₂﹡) : M₁ = M₂ := 
by rw [←dual_dual M₁, ←dual_dual M₂, h]

lemma dual_inj_iff {M₁ M₂ : matroid_in α} : M₁﹡ = M₂﹡ ↔ M₁ = M₂ := ⟨dual_inj, congr_arg _⟩ 

lemma dual_r_cast_eq (M : matroid_in α) [finite M.E] {X : set α} (hX : X ⊆ M.E) :
  (M﹡.r X : ℤ) = X.ncard + M.r (M.E \ X) - M.rk :=
begin
  rw [←@range_coe _ M.E, subset_range_iff_exists_image_eq] at hX, 
  obtain ⟨X₀, rfl⟩ := hX, 
  simp_rw [dual_eq, equiv_subtype.symm_r_eq, dual_r_cast_eq, preimage_image_eq _ coe_injective, 
    ncard_image_of_injective _ coe_injective, rk_eq_r_ground, rk_def, equiv_subtype.r_eq, coe_mk, 
    image_univ, range_coe_subtype, set_of_mem_eq, sub_left_inj, add_right_inj, nat.cast_inj, 
    coe_injective.image_compl_eq, range_coe], 
end

lemma dual_r_add_rk_eq (M : matroid_in α) [finite M.E] {X : set α} (hX : X ⊆ M.E) :
  M﹡.r X + M.rk = X.ncard + M.r (M.E \ X) :=
by linarith [M.dual_r_cast_eq hX]

@[simp] lemma dual_indep_iff_coindep : M﹡.indep X ↔ M.coindep X :=
begin
  simp_rw [indep_iff_subset_base, dual_base_iff, base_iff_coe, coindep,
    matroid.coindep_iff_disjoint_base],
  split,
  { rintro ⟨B, ⟨hBc, hBE⟩, hXB⟩,
    exact ⟨⟨_, hBc, disjoint_of_subset_left hXB disjoint_sdiff_right⟩, hXB.trans hBE⟩ },
  rintro ⟨⟨B, (hB : M.base B), hdj⟩, hX⟩,
  refine ⟨M.E \ B, ⟨_,diff_subset _ _⟩, subset_diff.mpr ⟨hX,hdj⟩ ⟩,
  rwa [sdiff_sdiff_right_self, inf_eq_inter, inter_eq_right_iff_subset.mpr hB.subset_ground],
end

@[simp] lemma dual_coindep_iff_indep : M﹡.coindep X ↔ M.indep X :=
by rw [←dual_dual M, dual_indep_iff_coindep, dual_dual]

@[simp] lemma dual_circuit_iff_cocircuit : M﹡.circuit C ↔ M.cocircuit C :=
begin
  refine (em (C ⊆ M.E)).symm.elim 
    (λ hn, iff_of_false (λ hC, hn (hC.subset_ground)) ((λ hC, hn (hC.subset_ground)))) (λ hCE, _), 
  simp_rw [circuit_iff_mem_minimals, dual_indep_iff_coindep, cocircuit_iff_coe, 
    matroid.cocircuit_iff_mem_minimals, coindep_iff_disjoint_base, not_exists, not_and, 
    ←base_iff_coe, dual_ground, subset_diff, not_and, not_disjoint_iff_nonempty_inter, inter_comm],
  exact ⟨λ h, ⟨λ B hB, h.1.1 B hB h.1.2, λ D hD h', h.2 ⟨λ B hB hDE, hD B hB, h'.trans hCE⟩ h'⟩,
    λ h, ⟨⟨λ B hB hCE', h.1 B hB, hCE⟩, λ D hD hDC, h.2 (λ B hB, hD.1 B hB (hDC.trans hCE)) hDC⟩⟩, 
end  

@[simp] lemma dual_cocircuit_iff_circuit : M﹡.cocircuit C ↔ M.circuit C :=
by rw [←dual_dual M, dual_circuit_iff_cocircuit, dual_dual]

@[simp] lemma dual_loop_iff_coloop : M﹡.loop e ↔ M.coloop e := 
by rw [coloop, matroid.coloop_iff_cocircuit, ←cocircuit_iff_coe, ←dual_circuit_iff_cocircuit, 
    loop_iff_circuit]

@[simp] lemma dual_coloop_iff_loop : M﹡.coloop e ↔ M.loop e := 
by rw [←dual_dual M, dual_loop_iff_coloop, dual_dual]
    
lemma coloop_iff_mem_dual_cl_empty : M.coloop e ↔ e ∈ M﹡.cl ∅ :=
by rw [←dual_dual M, ←dual_loop_iff_coloop, dual_dual, loop_iff_mem_cl_empty]

lemma dual_cl_empty_eq_coloops (M : matroid_in α) : M﹡.cl ∅ = {e | M.coloop e} := 
by { ext, rw ←coloop_iff_mem_dual_cl_empty, refl } 

lemma mem_dual_cl_iff_forall_circuit (he : e ∈ M.E) (hX : X ⊆ M.E) : 
  e ∈ M﹡.cl X ↔ ∀ C, M.circuit C → e ∈ C → (X ∩ C).nonempty :=
begin
  refine (em (e ∈ X)).elim (λ h, iff_of_true (subset_cl hX h) (λ C hC heC, ⟨e,h,heC⟩)) (λ heX, _), 

  rw [mem_cl_iff_forall_hyperplane], swap, assumption, swap, assumption, 
  refine ⟨λ h C hC heC, _,λ h H hH hXH, by_contra (λ heH, _)⟩, 
  { have con := h (M.E \ C) (cocircuit.compl_hyperplane _), 
    { rw [imp_iff_not (λ h, h.2 heC : e ∉ M.E \ C), not_subset_iff_exists_mem_not_mem] at con, 
      obtain ⟨f, hfX, hfn⟩ := con, 
      exact ⟨f, hfX, by_contra (λ hf, hfn ⟨hX hfX,hf⟩)⟩ },
    rwa [←dual_circuit_iff_cocircuit, dual_dual] },

  have hHC := hH.compl_cocircuit, 
  rw [dual_cocircuit_iff_circuit, dual_ground] at hHC, 
  obtain ⟨f, hfX, hf⟩ :=  h _ hHC ⟨he, heH⟩, 
  exact hf.2 (hXH hfX), 
end 

lemma dual_cl_to_coe (M : matroid_in α) {X : set α} (hX : X ⊆ M.E) : 
  M﹡.cl X = (M : matroid α)﹡.cl X := 
begin
  refine set.ext (λ e, (em (e ∈ M.E)).symm.elim (λ he, iff_of_false 
    (not_mem_subset (cl_subset_ground _ _) he) _) (λ he, _)), 
  { rw matroid.mem_dual_cl_iff_forall_circuit, 
    refine λ h, he _, 
    have con := h _ (loop_coe_of_not_mem_ground he).circuit (mem_singleton e), 
    simp only [inter_singleton_nonempty] at con,
    exact hX con },
  
  simp_rw [mem_dual_cl_iff_forall_circuit he hX, matroid.mem_dual_cl_iff_forall_circuit, 
    circuit, and_imp],  
  refine ⟨λ h C hC heC, h C hC _ heC,λ h C hC _ heC, h C hC heC⟩, 
  obtain (⟨-,hCE⟩ | ⟨f,hf,rfl⟩) := circuit_coe_iff.mp hC, 
    exact hCE,
  rwa [←mem_singleton_iff.mp heC, singleton_subset_iff],
end 

end dual

section flat_of_r

/-- A `flat` of rank `k` in `M`. When `k = 0`, the definition excludes infinite-rank flats
  with junk rank `0`.  -/
def flat_of_r (M : matroid_in α) (k : ℕ) := transfer_set_prop (λ γ M', M'.flat_of_r k) M

lemma flat_of_r_zero_iff_loops : M.flat_of_r 0 F ↔ F = M.cl ∅ :=
begin
  simp only [flat_of_r, transfer_set_prop_iff, flat_of_r_zero_iff_loops, equiv_subtype.cl_eq, coe_mk, 
    image_empty, preimage_coe_eq_preimage_coe_iff], 
  split, 
  { rintro ⟨he, h⟩, 
    rwa [inter_eq_self_of_subset_left h, inter_eq_self_of_subset_left $ cl_subset_ground _ _] 
      at he },
  rintro rfl, 
  refine ⟨rfl, cl_subset_ground _ _⟩, 
end 

-- def flat_of_r (M : matroid_in α) (k : ℕ) (F : set α) :=

lemma flat_of_r_iff : M.flat_of_r k F ↔ M.flat F ∧ M.r F = k ∧ M.r_fin F :=
begin
  simp_rw [flat_of_r, transfer_set_prop_iff, matroid.flat_of_r, flat_eq_transfer_set_prop, 
    r_fin_eq_transfer_set_prop], 
  simp only [equiv_subtype.flat_iff, coe_mk, image_preimage_coe, equiv_subtype.r_eq, 
    equiv_subtype.r_fin_iff, transfer_set_prop_iff, ←r_eq_r_inter_ground], 
  tauto, 
end 

lemma flat_of_r.flat (h : M.flat_of_r k F) : M.flat F := (flat_of_r_iff.mp h).1 
lemma flat_of_r.r (h : M.flat_of_r k F) : M.r F = k := (flat_of_r_iff.mp h).2.1
lemma flat_of_r.r_fin (h : M.flat_of_r k F) : M.r_fin F := (flat_of_r_iff.mp h).2.2

lemma flat_of_r_iff_coe : M.flat_of_r k F ↔ (M : matroid α).flat_of_r k (F ∪ M.Eᶜ) ∧ F ⊆ M.E :=
begin
  rw [flat_of_r_iff, matroid.flat_of_r, flat, ←r, r_union_compl_ground, r_fin, iff.comm,
    ←matroid.r_fin_cl_iff, cl_union_eq_cl_of_subset_loops M.compl_ground_subset_loops_coe, 
    matroid.r_fin_cl_iff],  
  tauto, 
end 

@[simp] lemma equiv_subtype.flat_of_r_iff {E : set α} {F : set E} 
(M : {M : matroid_in α // M.E = E}) :
  (equiv_subtype M).flat_of_r k F ↔ (M : matroid_in α).flat_of_r k (coe '' F) := 
by { obtain ⟨M,rfl⟩ := M, simp [flat_of_r] }
  
@[simp] lemma equiv_subtype.symm_flat_of_r_iff {E F : set α} (M : matroid E) : 
  (equiv_subtype.symm M : matroid_in α).flat_of_r k F ↔ M.flat_of_r k (coe ⁻¹' F) ∧ F ⊆ E  :=
by { simp [flat_of_r] }

/-- Flats of rank `k` in `M : matroid_in α` correspond to those in `↑M : matroid α`.-/
def flat_of_r_coe_equiv (M : matroid_in α) (k : ℕ) : 
  {F // M.flat_of_r k F} ≃ {F // (M : matroid α).flat_of_r k F} := 
{ to_fun := λ F, ⟨F ∪ M.Eᶜ, (flat_of_r_iff_coe.mp F.2).1⟩,
  inv_fun := λ F, ⟨F ∩ M.E, 
  begin
    rw [flat_of_r_iff_coe, and_iff_left (inter_subset_right _ _), union_distrib_right, 
      union_compl_self, inter_univ, union_eq_left_iff_subset.mpr],
      { exact F.2 }, 
    exact M.compl_ground_subset_loops_coe.trans F.2.flat.loops_subset,  
  end⟩,
  left_inv := 
  begin
    rintro ⟨F,hF⟩, 
    simp only [coe_mk, inter_distrib_right, compl_inter_self, union_empty, 
      inter_eq_self_of_subset_left hF.subset_ground]
  end,
  right_inv := 
  begin
    rintro ⟨F,hF⟩, 
    simp only [coe_mk, union_distrib_right, union_compl_self, inter_univ, union_eq_left_iff_subset], 
    exact M.compl_ground_subset_loops_coe.trans hF.flat.loops_subset,      
  end }

@[simp] lemma flat_of_r_coe_equiv_apply (F : {F // M.flat_of_r k F}) : 
  (M.flat_of_r_coe_equiv k F : set α) = F ∪ M.Eᶜ := rfl  

@[simp] lemma flat_of_r_coe_equiv_apply_symm (F : {F // (M : matroid α).flat_of_r k F}) : 
  ((M.flat_of_r_coe_equiv k).symm F : set α) = F ∩ M.E := rfl 

/-- A `point` is a rank-one flat -/
def point (M : matroid_in α) (P : set α) := M.flat_of_r 1 P 

/-- A `line` is a rank-two flat -/
def line (M : matroid_in α) (L : set α) := M.flat_of_r 2 L 

lemma point_eq_transfer_set_prop (M : matroid_in α) : M.point = transfer_set_prop (λ _, matroid.point) M := 
rfl

lemma line_eq_transfer_set_prop (M : matroid_in α) : M.line = transfer_set_prop (λ _, matroid.line) M := rfl

lemma sum_ncard_point_diff_loops (M : matroid_in α) [finite M.E] : 
  ∑ᶠ P : {P // M.point P}, ((P : set α) \ M.cl ∅).ncard = (M.E \ M.cl ∅).ncard :=
begin
  set e := transfer_set_prop_equiv (λ _, matroid.point) M, 
  convert (@finsum_comp_equiv _ _ _ _ e.symm _).symm, 
  convert (equiv_subtype ⟨M,rfl⟩).sum_ncard_point_diff_loops.symm using 1, 
  { simp only [equiv_subtype.cl_eq, coe_mk, image_empty],
    rw [←ncard_image_of_injective _ coe_injective, image_compl_preimage, range_coe] },
  apply finsum_congr, 
  rintro ⟨P, hP⟩, 
  simp only [transfer_set_prop_equiv_apply_symm, coe_mk, equiv_subtype.cl_eq, image_empty], 
  rw [←ncard_image_of_injective _ coe_injective, image_diff coe_injective, image_preimage_coe, 
    inter_eq_self_of_subset_left (cl_subset_ground _ _)], 
end 

noncomputable def num_points (M : matroid_in α) : ℕ := nat.card { P // M.point P }

lemma num_points_eq_equiv_subtype (M : matroid_in α) : 
  M.num_points = (equiv_subtype ⟨M,rfl⟩).num_points :=   
nat.card_eq_of_bijective _ ((transfer_set_prop_equiv (λ _, matroid.point) M).bijective)

lemma num_points_eq_coe (M : matroid_in α) : 
  M.num_points = (M : matroid α).num_points :=
nat.card_eq_of_bijective (M.flat_of_r_coe_equiv 1) (equiv.bijective _)

lemma simple_iff_num_points_eq_card [finite M.E] (hnl : ¬M.base ∅) : 
  M.simple ↔ M.num_points = M.E.ncard := 
begin
  nth_rewrite 0 ← eq_image_symm_image_equiv_subtype M, 
  rw [equiv_subtype.symm_simple_iff, matroid.simple_iff_num_points_eq_card, 
    ←num_points_eq_equiv_subtype, ncard_univ, nat.card_coe_set_eq], 
  simpa, 
end 

end flat_of_r 



end matroid_in

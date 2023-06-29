import Oneshot.Basic
import Oneshot.Mathlib.Data.Set.Image
import Oneshot.Mathlib.Data.Set.Function

noncomputable section

open Set

universe u

variable {α β α₁ α₂ α₃ : Type _} {M : MatroidIn α} {N : MatroidIn β}

namespace MatroidIn

section Iso

structure Iso (M₁ : MatroidIn α₁) (M₂ : MatroidIn α₂) extends Equiv M₁.e M₂.e where
  on_base' : ∀ B : Set M₁.e, M₁.base (coe '' B) ↔ M₂.base (coe '' (to_fun '' B))
#align matroid_in.iso MatroidIn.Iso

infixl:75 " ≃i " => MatroidIn.Iso

instance Iso.equivLike {α β : Type _} {M₁ : MatroidIn α} {M₂ : MatroidIn β} :
    EquivLike (M₁ ≃i M₂) M₁.e M₂.e
    where
  coe e := e.toEquiv.toFun
  inv e := e.toEquiv.invFun
  left_inv e := e.toEquiv.left_inv
  right_inv e := e.toEquiv.right_inv
  coe_injective' e e' h h' := by cases e; cases e'; simpa using h
#align matroid_in.iso.equiv_like MatroidIn.Iso.equivLike

def Iso.symm (e : M ≃i N) : N ≃i M where
  toEquiv := e.symm
  on_base' := by
    intro B
    rw [e.on_base']
    congr
    exact (e.to_equiv.image_symm_image B).symm
#align matroid_in.iso.symm MatroidIn.Iso.symm

@[simp]
theorem coe_symm (e : M ≃i N) : (e.symm : N.e → M.e) = e.toEquiv.symm :=
  rfl
#align matroid_in.coe_symm MatroidIn.coe_symm

def Iso.cast {M N : MatroidIn α} (h : M = N) : M ≃i N
    where
  toEquiv := Equiv.cast (by rw [h])
  on_base' := by subst h; simp
#align matroid_in.iso.cast MatroidIn.Iso.cast

def Iso.refl (M : MatroidIn α₁) : M ≃i M :=
  ⟨Equiv.refl M.e, by simp⟩
#align matroid_in.iso.refl MatroidIn.Iso.refl

def Iso.trans {M₁ : MatroidIn α₁} {M₂ : MatroidIn α₂} {M₃ : MatroidIn α₃} (e₁ : M₁ ≃i M₂)
    (e₂ : M₂ ≃i M₃) : M₁ ≃i M₃
    where
  toEquiv := e₁.toEquiv.trans e₂.toEquiv
  on_base' B := by
    rw [e₁.on_base', e₂.on_base']
    convert Iff.rfl
    rw [← image_comp]
    rfl
#align matroid_in.iso.trans MatroidIn.Iso.trans

def isoOfIndep (e : M.e ≃ N.e)
    (hi : ∀ I : Set M.e, M.indep (coe '' I) ↔ N.indep (coe '' (e '' I))) : M ≃i N
    where
  toEquiv := e
  on_base' := by
    intro B
    simp_rw [base_iff_maximal_indep, Equiv.toFun_as_coe]
    simp only [image_subset_iff]
    simp_rw [← hi, and_congr_right_iff]
    refine' fun hI => ⟨fun h I hIN hBI => _, fun h I hI hBI => _⟩
    · have hIE := hIN.subset_ground
      rw [← @Subtype.range_coe _ N.E] at hIE 
      obtain ⟨I, rfl⟩ := subset_range_iff_exists_image_eq.mp hIE
      rw [← e.image_preimage I, ← hi] at hIN 
      have := h _ hIN
      simp only [Subtype.preimage_image_coe, Subtype.image_coe_eq_image_coe_iff] at this hBI 
      simp [this hBI]
    specialize h (coe '' (e '' (coe ⁻¹' I)))
    simp only [Subtype.preimage_image_coe, Equiv.preimage_image, Subtype.image_coe_eq_image_coe_iff,
      Equiv.image_eq_iff_eq, ← hi, Subtype.image_preimage_coe,
      inter_eq_self_of_subset_left hI.subset_ground] at h 
    simp only [h hI hBI, Subtype.image_preimage_coe, inter_eq_left_iff_subset]
    exact hI.subset_ground
#align matroid_in.iso_of_indep MatroidIn.isoOfIndep

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (X «expr ⊆ » M.E) -/
noncomputable def isoOfBijOn (M : MatroidIn α) (N : MatroidIn β) (f : α → β)
    (hbij : BijOn f M.e N.e) (hf : ∀ (X) (_ : X ⊆ M.e), M.base X ↔ N.base (f '' X)) : M ≃i N
    where
  toEquiv := Set.BijOn.equiv f hbij
  on_base' := by
    intro B
    rw [Equiv.toFun_as_coe, hf _ (Subtype.coe_image_subset (E M) B)]
    convert Iff.rfl
    ext y
    simp only [mem_image, SetCoe.exists, Subtype.coe_mk, exists_and_right, exists_eq_right]
    constructor
    · rintro ⟨hy, x, hx, hxB, hb⟩
      refine' ⟨x, ⟨hx, hxB⟩, _⟩
      rw [← Subtype.coe_inj, Subtype.coe_mk] at hb 
      rw [← hb]
      rfl
    rintro ⟨x, ⟨hx, hB⟩, rfl⟩
    exact ⟨hbij.maps_to hx, x, hx, hB, rfl⟩
#align matroid_in.iso_of_bij_on MatroidIn.isoOfBijOn

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (B «expr ⊆ » M.E) -/
theorem Iso.exists_bijOn [Nonempty β] (e : M ≃i N) :
    ∃ f : α → β, BijOn f M.e N.e ∧ ∀ (B) (_ : B ⊆ M.e), M.base B ↔ N.base (f '' B) := by
  classical
  let b := Classical.arbitrary β
  refine' ⟨fun a => if h : a ∈ M.E then e ⟨a, h⟩ else b, ⟨fun x hx => _, _, _⟩, _⟩
  · simp_rw [dif_pos hx]; exact (e ⟨x, hx⟩).2
  · intro x hx x' hx' h
    simp_rw [dif_pos hx, dif_pos hx', Subtype.coe_inj] at h 
    simpa using e.to_equiv.apply_eq_iff_eq.mp h
  · refine' fun y hy => ⟨e.symm ⟨y, hy⟩, Subtype.mem _, _⟩
    simp_rw [Subtype.coe_prop, Subtype.coe_eta, dite_eq_ite, if_true, Subtype.coe_eq_iff]
    exact ⟨hy, e.to_equiv.apply_symm_apply _⟩
  refine' fun B hB => _
  rw [← @Subtype.range_coe _ M.E] at hB 
  obtain ⟨B, rfl⟩ := subset_range_iff_exists_image_eq.mp hB
  rw [e.on_base']
  convert Iff.rfl
  ext b
  simp only [mem_image, SetCoe.exists, Subtype.coe_mk, exists_and_right, exists_eq_right,
    Equiv.toFun_as_coe]
  constructor
  · rintro ⟨a, ⟨ha, haB⟩, h⟩
    rw [dif_pos ha] at h ; subst h
    simp only [Subtype.coe_prop, Subtype.coe_eta, exists_true_left]
    exact ⟨a, ha, haB, rfl⟩
  rintro ⟨hb, a, ha, haB, he⟩
  refine' ⟨a, ⟨ha, haB⟩, _⟩
  rw [dif_pos ha]
  apply_fun (coe : N.E → β) at he 
  exact he
#align matroid_in.iso.exists_bij_on MatroidIn.Iso.exists_bijOn

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (X «expr ⊆ » M.E) -/
noncomputable def isoOfBijOnIndep (f : α → β) (hbij : BijOn f M.e N.e)
    (hf : ∀ (X) (_ : X ⊆ M.e), M.indep X ↔ N.indep (f '' X)) : M ≃i N :=
  isoOfBijOn M N f hbij
    (by
      intro I hIE
      simp_rw [base_iff_maximal_indep, ← hf I hIE, and_congr_right_iff]
      refine' fun hI => ⟨fun h J hJ hIJ => _, fun h J hJ hIJ => _⟩
      · have hJ_e := hbij.surj_on.image_preimage_inter hJ.subset_ground
        rw [← hJ_e, h]
        · rwa [hf (f ⁻¹' J ∩ M.E) (inter_subset_right _ _), hJ_e]
        rwa [subset_inter_iff, and_iff_left hIE, ← image_subset_iff]
      have hIJ' := h (f '' J) _ (image_subset _ hIJ)
      · rwa [hbij.inj_on.image_eq_image_iff (hIJ.trans hJ.subset_ground) hJ.subset_ground] at hIJ' 
      rwa [← hf _ hJ.subset_ground])
#align matroid_in.iso_of_bij_on_indep MatroidIn.isoOfBijOnIndep

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (I «expr ⊆ » M.E) -/
theorem Iso.exists_bijOn_indep [Nonempty β] (e : M ≃i N) :
    ∃ f : α → β, BijOn f M.e N.e ∧ ∀ (I) (_ : I ⊆ M.e), M.indep I ↔ N.indep (f '' I) :=
  by
  refine' e.exists_bij_on.imp fun f hf => ⟨hf.1, fun I hIE => _⟩
  simp_rw [indep_iff_subset_base]
  constructor
  · rintro ⟨B, hB, hIB⟩; exact ⟨f '' B, (hf.2 B hB.subset_ground).mp hB, image_subset _ hIB⟩
  rintro ⟨B, hB, hIB⟩
  have hB' := hf.1.SurjOn.image_preimage_inter hB.subset_ground
  refine' ⟨f ⁻¹' B ∩ M.E, _, _⟩
  · rwa [hf.2 _ (inter_subset_right _ _), hB']
  rwa [subset_inter_iff, ← image_subset_iff, and_iff_left hIE]
#align matroid_in.iso.exists_bij_on_indep MatroidIn.Iso.exists_bijOn_indep

def Iso.image (e : M ≃i N) (B : Set α) : Set β :=
  coe '' (e '' (coe ⁻¹' B))
#align matroid_in.iso.image MatroidIn.Iso.image

def Iso.preimage (e : M ≃i N) (B : Set β) : Set α :=
  coe '' (e ⁻¹' (coe ⁻¹' B))
#align matroid_in.iso.preimage MatroidIn.Iso.preimage

@[ssE_finish_rules]
theorem Iso.image_subset_ground (e : M ≃i N) (X : Set α) : e.image X ⊆ N.e :=
  Subtype.coe_image_subset _ _
#align matroid_in.iso.image_subset_ground MatroidIn.Iso.image_subset_ground

@[ssE_finish_rules]
theorem Iso.preimage_subset_ground (e : M ≃i N) (X : Set β) : e.Preimage X ⊆ M.e :=
  Subtype.coe_image_subset _ _
#align matroid_in.iso.preimage_subset_ground MatroidIn.Iso.preimage_subset_ground

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
@[simp]
theorem Iso.preimage_image (e : M ≃i N) {X : Set α}
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    e.Preimage (e.image X) = X :=
  by
  rw [← @Subtype.range_coe _ M.E] at hX 
  obtain ⟨X, rfl⟩ := subset_range_iff_exists_image_eq.mp hX
  rw [iso.image, iso.preimage]
  simp only [Subtype.preimage_image_coe, Subtype.image_coe_eq_image_coe_iff]
  exact e.to_equiv.preimage_image X
#align matroid_in.iso.preimage_image MatroidIn.Iso.preimage_image

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
@[simp]
theorem Iso.image_preimage (e : M ≃i N) {X : Set β}
    (hX : X ⊆ N.e := by
      run_tac
        ssE) :
    e.image (e.Preimage X) = X :=
  by
  rw [autoParam_eq, ← @Subtype.range_coe _ N.E] at hX 
  obtain ⟨X, rfl⟩ := subset_range_iff_exists_image_eq.mp hX
  rw [iso.image, iso.preimage]
  simp_rw [Subtype.preimage_image_coe, Subtype.image_coe_eq_image_coe_iff]
  exact e.to_equiv.image_preimage X
#align matroid_in.iso.image_preimage MatroidIn.Iso.image_preimage

theorem Iso.image_inj (e : M ≃i N) {X X' : Set α} (hB : X ⊆ M.e) (hB' : X' ⊆ M.e)
    (h : e.image X = e.image X') : X = X' := by
  rwa [iso.image, iso.image, image_eq_image Subtype.coe_injective,
      image_eq_image (EquivLike.injective e), preimage_eq_preimage'] at h  <;>
    rwa [Subtype.range_coe]
#align matroid_in.iso.image_inj MatroidIn.Iso.image_inj

theorem Iso.preimage_inj (e : M ≃i N) {X X' : Set β} (hB : X ⊆ N.e) (hB' : X' ⊆ N.e)
    (h : e.Preimage X = e.Preimage X') : X = X' := by
  rwa [iso.preimage, iso.preimage, image_eq_image Subtype.coe_injective,
      preimage_eq_preimage (EquivLike.surjective e), preimage_eq_preimage'] at h  <;>
    rwa [Subtype.range_coe]
#align matroid_in.iso.preimage_inj MatroidIn.Iso.preimage_inj

theorem Iso.image_eq_preimage_symm (e : M ≃i N) {X : Set α} : e.image X = e.symm.Preimage X :=
  by
  rw [iso.preimage, coe_symm, iso.image, image_eq_image Subtype.coe_injective, ←
    image_equiv_eq_preimage_symm]
  rfl
#align matroid_in.iso.image_eq_preimage_symm MatroidIn.Iso.image_eq_preimage_symm

theorem Iso.preimage_eq_image_symm (e : M ≃i N) {X : Set β} : e.Preimage X = e.symm.image X :=
  by
  rw [iso.image, coe_symm, iso.preimage, image_eq_image Subtype.coe_injective, ←
    preimage_equiv_eq_image_symm]
  rfl
#align matroid_in.iso.preimage_eq_image_symm MatroidIn.Iso.preimage_eq_image_symm

theorem Iso.image_eq_image_inter_ground (e : M ≃i N) (X : Set α) : e.image X = e.image (X ∩ M.e) :=
  by rw [iso.image, iso.image, ← preimage_inter_range, Subtype.range_coe]
#align matroid_in.iso.image_eq_image_inter_ground MatroidIn.Iso.image_eq_image_inter_ground

theorem Iso.preimage_eq_preimage_inter_ground (e : M ≃i N) (X : Set β) :
    e.Preimage X = e.Preimage (X ∩ N.e) := by
  rw [e.preimage_eq_image_symm, iso.image_eq_image_inter_ground, ← e.preimage_eq_image_symm]
#align matroid_in.iso.preimage_eq_preimage_inter_ground MatroidIn.Iso.preimage_eq_preimage_inter_ground

@[simp]
theorem Iso.image_ground (e : M ≃i N) : e.image M.e = N.e :=
  by
  rw [← @Subtype.range_coe _ M.E, ← @Subtype.range_coe _ N.E, iso.image]
  simp only [Subtype.range_coe_subtype, set_of_mem_eq, Subtype.coe_preimage_self, image_univ]
  convert image_univ
  · exact e.to_equiv.range_eq_univ
  simp
#align matroid_in.iso.image_ground MatroidIn.Iso.image_ground

@[simp]
theorem Iso.preimage_ground (e : M ≃i N) : e.Preimage N.e = M.e := by
  rw [iso.preimage_eq_image_symm, iso.image_ground]
#align matroid_in.iso.preimage_ground MatroidIn.Iso.preimage_ground

theorem Iso.image_inter (e : M ≃i N) (X Y : Set α) : e.image (X ∩ Y) = e.image X ∩ e.image Y := by
  rw [e.image_eq_image_inter_ground, inter_inter_distrib_right, iso.image, preimage_inter,
    image_inter (EquivLike.injective e), image_inter Subtype.coe_injective, ← iso.image, ←
    iso.image, ← e.image_eq_image_inter_ground, ← e.image_eq_image_inter_ground]
#align matroid_in.iso.image_inter MatroidIn.Iso.image_inter

theorem Iso.preimage_compl (e : M ≃i N) (X : Set β) : e.Preimage (Xᶜ) = M.e \ e.Preimage X := by
  rw [iso.preimage, preimage_compl, preimage_compl, compl_eq_univ_diff,
    image_diff Subtype.coe_injective, image_univ, Subtype.range_coe, iso.preimage]
#align matroid_in.iso.preimage_compl MatroidIn.Iso.preimage_compl

theorem Iso.image_compl (e : M ≃i N) (X : Set α) : e.image (Xᶜ) = N.e \ e.image X := by
  rw [iso.image_eq_preimage_symm, iso.preimage_compl, ← iso.image_eq_preimage_symm]
#align matroid_in.iso.image_compl MatroidIn.Iso.image_compl

theorem Iso.image_diff (e : M ≃i N) (X Y : Set α) : e.image (X \ Y) = e.image X \ e.image Y := by
  rw [diff_eq, e.image_inter, e.image_compl, diff_eq, ← inter_assoc, diff_eq,
    inter_eq_self_of_subset_left (e.image_subset_ground _)]
#align matroid_in.iso.image_diff MatroidIn.Iso.image_diff

@[simp]
theorem Iso.image_empty (e : M ≃i N) : e.image ∅ = ∅ := by simp [iso.image]
#align matroid_in.iso.image_empty MatroidIn.Iso.image_empty

theorem Iso.image_subset_image (e : M ≃i N) {X Y : Set α} (hXY : X ⊆ Y) : e.image X ⊆ e.image Y :=
  by rw [← diff_eq_empty, ← e.image_diff, diff_eq_empty.mpr hXY, e.image_empty]
#align matroid_in.iso.image_subset_image MatroidIn.Iso.image_subset_image

theorem Iso.image_ground_diff (e : M ≃i N) (X : Set α) : e.image (M.e \ X) = N.e \ e.image X := by
  rw [iso.image_diff, iso.image_ground]
#align matroid_in.iso.image_ground_diff MatroidIn.Iso.image_ground_diff

def Iso.dual (e : M ≃i N) : M﹡ ≃i N﹡
    where
  toEquiv := e.toEquiv
  on_base' := by
    intro B
    rw [dual_base_iff', dual_base_iff', ← @Subtype.range_coe _ M.E, ← @Subtype.range_coe _ N.E,
      and_iff_left (image_subset_range _ _), and_iff_left (image_subset_range _ _), ← image_univ, ←
      image_diff Subtype.coe_injective, e.on_base', ← image_univ, ←
      image_diff Subtype.coe_injective, Equiv.toFun_as_coe, image_diff (Equiv.injective _),
      image_univ, Equiv.range_eq_univ]
#align matroid_in.iso.dual MatroidIn.Iso.dual

@[simp]
theorem Iso.dual_coe (e : M ≃i N) : (e.dual : M﹡.e → N﹡.e) = e :=
  rfl
#align matroid_in.iso.dual_coe MatroidIn.Iso.dual_coe

@[simp]
theorem Iso.dual_image (e : M ≃i N) : e.dual.image = e.image :=
  rfl
#align matroid_in.iso.dual_image MatroidIn.Iso.dual_image

@[simp]
theorem Iso.dual_preimage (e : M ≃i N) : e.dual.Preimage = e.Preimage :=
  rfl
#align matroid_in.iso.dual_preimage MatroidIn.Iso.dual_preimage

theorem Iso.on_base (e : M ≃i N) {B : Set α} (hI : B ⊆ M.e) : M.base B ↔ N.base (e.image B) :=
  by
  rw [← @Subtype.range_coe _ M.E] at hI 
  obtain ⟨B, rfl⟩ := subset_range_iff_exists_image_eq.mp hI
  rw [iso.image, e.on_base', Equiv.toFun_as_coe]
  convert Iff.rfl using 1
  simp only [Subtype.preimage_image_coe, eq_iff_iff]
  rfl
#align matroid_in.iso.on_base MatroidIn.Iso.on_base

theorem Iso.on_indep (e : M ≃i N) {I : Set α} (hI : I ⊆ M.e) : M.indep I ↔ N.indep (e.image I) :=
  by
  rw [indep_iff_subset_base, indep_iff_subset_base]
  constructor
  · rintro ⟨B, hB, hIB⟩
    exact ⟨e.image B, (e.on_base hB.subset_ground).mp hB, e.image_subset_image hIB⟩
  rintro ⟨B, hB, hIB⟩
  refine' ⟨e.preimage B, _, _⟩
  · rwa [iso.preimage_eq_image_symm, ← e.symm.on_base hB.subset_ground]
  rw [← e.preimage_image hI, e.preimage_eq_image_symm, e.preimage_eq_image_symm]
  apply e.symm.image_subset_image hIB
#align matroid_in.iso.on_indep MatroidIn.Iso.on_indep

-- lemma iso.preimage_image (e : M ≃i N) {X : set β} (hX : X ⊆ N.E) : 
--   e.preimage 
-- instance : has_coe_to_fun (M₁ ≃i M₂) (λ _, M₁.E → M₂.E) := ⟨λ e, e.to_fun⟩ 
-- def iso.refl (M : matroid_in α₁) : M ≃i M := 
-- ⟨equiv.refl M.E, by simp⟩ 
-- def iso.symm (e : M₁ ≃i M₂) : M₂ ≃i M₁ := 
-- ⟨e.to_fun.symm, λ B, by { rw e.on_base, simp }⟩ 
-- def iso.trans (e₁ : M₁ ≃i M₂) (e₂ : M₂ ≃i M₃) : M₁ ≃i M₃ :=
-- { to_fun := e₁.to_fun.trans e₂.to_fun,
--   on_base := λ B, by { rw [e₂.on_base, e₁.on_base], convert iff.rfl } }
-- lemma on_base {B : set α₁} (i : M₁ ≃i M₂) (hB : M₁.base B) : M₂.base (i '' B)
-- lemma on_indep (h : M₁ ≃i M₂) (I : set M₁.E) : M₁.indep I ↔ 
-- def iso.image (e : M₁ ≃i M₂) (B : set α₁) : set α₂ := coe '' (e '' (coe ⁻¹' B))
-- def iso.preimage (e : M₁ ≃i M₂) (B : set α₂) : set α₁ := coe '' (e ⁻¹' (coe ⁻¹' B))
-- lemma iso.image_preimage (e : M₁ ≃i M₂) {X : set α₁} (hX : X ⊆ M₁.E) : 
--   e.preimage (e.image X) = X :=
-- begin
--   rw ←@subtype.range_coe _ M₁.E at hX, 
--   obtain ⟨X, rfl⟩ := subset_range_iff_exists_image_eq.mp hX, 
--   rw [iso.image, iso.preimage], 
--   simp only [subtype.preimage_image_coe, subtype.image_coe_eq_image_coe_iff], 
--   exact e.to_equiv.preimage_image X, 
-- end 
-- lemma iso.base_iff_base (e : M₁ ≃i M₂) {B : set α₁} (hB : B ⊆ M₁.E) : 
--   M₁.base B ↔ M₂.base (e.image B) :=
-- begin
--   rw ←@subtype.range_coe _ M₁.E at hB, 
--   obtain ⟨B, rfl⟩ := subset_range_iff_exists_image_eq.mp hB, 
--   rw [iso.image, e.symm.on_base, iso.symm],  
--   convert iff.rfl, 
--   convert equiv.image_eq_preimage _ _, 
--   simp, 
-- end
end Iso

section Image

end Image

-- variables {E E₀ E₁ E₂ : Type u} {M₀ : matroid E₀} {M₁ : matroid E₁} {M₂ : matroid E₂}
-- /-- Two matroids are isomorphic if there is a map between ground sets that preserves bases -/
-- def is_iso (M₁ : matroid E₁) (M₂ : matroid E₂) (e : E₁ ≃ E₂) :=
--   ∀ B, M₁.base B ↔ M₂.base (e '' B)
-- /-- A bundled isomorphism between two matroids -/
-- structure iso (M₁ : matroid E₁) (M₂ : matroid E₂) :=
-- (to_fun : E₁ ≃ E₂)
-- (on_base : ∀ B, M₁.base B ↔ M₂.base (to_fun '' B))
-- infix ` ≃i ` :75 :=  matroid.iso
-- instance : has_coe_to_fun (M₁ ≃i M₂) (λ _, E₁ → E₂) :=
--   ⟨λ e, e.to_fun⟩
-- def iso.refl (M : matroid E) : M ≃i M := ⟨equiv.refl E, λ B, by simp⟩
-- def iso.symm (e : M₁ ≃i M₂) : M₂ ≃i M₁ := ⟨e.to_fun.symm, λ B, by {rw e.on_base, simp, }⟩
-- end iso 
-- section embed
-- variables {E E' : Type u} {M : matroid E} {M' : matroid E'} {f : E ↪ E'} 
-- /-- Embed a matroid as a restriction in a larger type. All elements outside the image are loops. -/
-- def image (M : matroid E) (f : E ↪ E') : matroid E' :=
-- matroid_of_indep (λ I', ∃ I, M.indep I ∧ f '' I = I') ⟨_, M.empty_indep, by simp⟩
-- ( begin 
--   rintro _ _ ⟨J, hJ, rfl⟩ hIJ, refine ⟨J ∩ f ⁻¹' I, hJ.subset (inter_subset_left _ _), _⟩,
--   rw [image_inter f.injective, image_preimage_eq_inter_range, ←inter_assoc, 
--     inter_eq_right_iff_subset.mpr hIJ, eq_comm, 
--     inter_eq_left_iff_subset.mpr (hIJ.trans (image_subset_range _ _))], 
--   end)
-- ( begin
--     rintro _ _ ⟨I, hI, rfl⟩ hIn ⟨⟨B,hB,rfl⟩,hBmax⟩, 
--     obtain ⟨e, he, heI⟩ := hI.exists_insert_of_not_base _ (hB.base_of_maximal (λ J hJ hBJ, _)), 
--     { exact ⟨f e, by rwa [←image_diff f.injective, f.injective.mem_set_image], 
--       ⟨_, heI, image_insert_eq⟩⟩ },
--     { refine λ hI', hIn ⟨⟨_,hI,rfl⟩,_⟩, 
--       rintro _ ⟨J, hJ, rfl⟩ hIJ,  
--       rw hI'.eq_of_subset_indep hJ, 
--       rwa image_subset_image_iff f.injective at hIJ },
--     exact hBJ.antisymm 
--       ((image_subset_image_iff f.injective).mp (hBmax ⟨_,hJ,rfl⟩ (image_subset _ hBJ))),   
--   end)
-- ( begin
--   rintro _ X ⟨I,hI,rfl⟩ hIX, 
--   obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset (image_subset_iff.mp hIX), 
--   refine ⟨f '' J, ⟨⟨_,hJ.indep,rfl⟩,image_subset _ hIJ, image_subset_iff.mpr hJ.subset⟩, _⟩,
--   rintro _ ⟨⟨K,hK,rfl⟩,hIK,hKX⟩ hJK,   
--   rw hJ.eq_of_subset_indep hK ((image_subset_image_iff f.injective).mp hJK) 
--     (image_subset_iff.mp hKX), 
--   end)
-- lemma image.set_of_indep_eq (M : matroid E) : 
--   {I | (M.image f).indep I} = (set.image f) '' {I | M.indep I} :=
-- by { ext, simp_rw [image, matroid_of_indep_apply], refl }
-- @[simp] lemma image.indep_iff {I' : set E'} : (M.image f).indep I' ↔ ∃ I, M.indep I ∧ f '' I = I' := 
-- by simp [image]
-- lemma image.compl_range_subset_loops (M : matroid E) (f : E ↪ E') : (range f)ᶜ ⊆ (M.image f).cl ∅ :=   
-- begin
--   refine λ e he, (loop_iff_mem_cl_empty.mp _),   
--   simp_rw [loop_iff_dep, image.indep_iff, not_exists, not_and, 
--     f.injective.image_eq_singleton_iff, not_exists, not_and], 
--   rintro I hI e rfl rfl, 
--   simpa using he, 
-- end 
-- @[simp] lemma image.base_iff {B' : set E'} : (M.image f).base B' ↔ ∃ B, M.base B ∧ B' = f '' B :=
-- begin
--   simp_rw [base_iff_maximal_indep, image.indep_iff], 
--   split, 
--   { rintro ⟨⟨B, hB, rfl⟩,h⟩,
--     exact ⟨B, ⟨hB, λ I hI hBI, 
--       (image_eq_image f.injective).mp (h _ ⟨I,hI,rfl⟩ (image_subset f hBI))⟩, rfl⟩ },
--   rintro ⟨B, ⟨hBi, hB⟩, rfl⟩,  
--   refine ⟨⟨_,hBi,rfl⟩, _⟩, 
--   rintro _ ⟨I, hI, rfl⟩ hBI, 
--   rw [hB _ hI $ (image_subset_image_iff f.injective).mp hBI], 
-- end 
-- @[simp] lemma image.basis_iff {I' X' : set E'} :
--   (M.image f).basis I' X' ↔ ∃ I, M.basis I (f ⁻¹' X') ∧ I' = f '' I :=
-- begin
--   simp_rw [basis_iff, image.indep_iff], 
--   split, 
--   { rintro ⟨⟨I, hI, rfl⟩, hIX', hmax⟩,
--     refine ⟨I, ⟨hI, image_subset_iff.mp hIX', λ J hJ hIJ hJX, 
--       (image_eq_image f.injective).mp _⟩, rfl⟩,
--     rw hmax _ ⟨_, hJ, rfl⟩ (image_subset _ hIJ) (image_subset_iff.mpr hJX) },
--   rintro ⟨I, ⟨hI, hIX, hmax⟩, rfl⟩, 
--   refine ⟨⟨_, hI, rfl⟩, image_subset_iff.mpr hIX, _⟩, 
--   rintro _ ⟨J, hJ, rfl⟩ hIJ hJX, 
--   rw hmax _ hJ ((image_subset_image_iff f.injective).mp hIJ) (image_subset_iff.mp hJX), 
-- end 
-- @[simp] lemma image.circuit_iff {C' : set E'} :
--   (M.image f).circuit C' ↔ (∃ C, M.circuit C ∧ C' = f '' C) ∨ (∃ e ∈ (range f)ᶜ, C' = {e}) :=
-- begin
--   simp_rw [circuit_iff, image.indep_iff, not_exists, not_and],  
--   split,
--   { rintro ⟨h,h'⟩, 
--     obtain (hC' | hC') := em (C' ⊆ range f), 
--     { obtain ⟨C,rfl⟩ := subset_range_iff_exists_image_eq.mp hC', 
--       refine or.inl ⟨C, ⟨λ hi, h _ hi rfl, λ I hd hIC, (image_eq_image f.injective).mp _⟩, rfl⟩,
--       refine h' _ (λ I' hI' hf, hd _) (image_subset _ hIC), 
--       rwa ←(image_eq_image f.injective).mp hf },
--     obtain ⟨e, heC, her⟩ := not_subset.mp hC',  
--     refine or.inr ⟨e, her, (h' {e} (λ I hI heI, her _) (singleton_subset_iff.mpr heC)).symm⟩,
--     exact (image_subset_range _ _) (heI.symm.subset (mem_singleton e)) },
--   rintro (⟨C, ⟨hC,hmin⟩, rfl⟩ | ⟨e, he, rfl⟩),    
--   { refine ⟨λ I hI h_eq, hC (by rwa [←(image_eq_image f.injective).mp h_eq]), λ C' hC' hC'C, _⟩,
--     obtain ⟨C₀, rfl⟩ := subset_range_iff_exists_image_eq.mp (hC'C.trans (image_subset_range _ _)), 
--     refine hC'C.antisymm (image_subset_iff.mpr _), 
--     rw [preimage_image_eq _ f.injective, ←hmin _ (λ hi, (hC' _ hi rfl))
--       ((image_subset_image_iff f.injective).mp hC'C)] },
--   exact ⟨λ I hI h', he (singleton_subset_iff.mp (h'.symm.subset.trans (image_subset_range _ _))), 
--     λ I h h', (subset_singleton_iff_eq.mp h').elim 
--       (λ h', (h ∅ M.empty_indep (by rwa [eq_comm, image_empty])).elim ) id⟩, 
-- end
-- @[simp] lemma image.cl_eq (M : matroid E) (f : E ↪ E') (X' : set E') : 
--   (M.image f).cl X' = f '' (M.cl (f ⁻¹' X')) ∪ (range f)ᶜ :=
-- begin
--   obtain ⟨I', hI'⟩ := (M.image f).exists_basis X', 
--   obtain ⟨I, hI, rfl⟩ := image.basis_iff.mp hI', 
--   ext e, 
--   simp only [mem_union, mem_image, mem_compl_iff, mem_range, not_exists], 
--   obtain (⟨e,rfl⟩ | he) := em (e ∈ range f), 
--   { have hfalse : ¬ ∀ x, ¬ f x = f e, from λ h, (h e rfl),
--     rw [iff_false_intro hfalse, or_false], 
--     simp only [embedding_like.apply_eq_iff_eq, exists_eq_right],
--     obtain (he | he) := em (f e ∈ X'),
--     { exact iff_of_true (mem_cl_of_mem _ he) (mem_cl_of_mem _ he) },
--     simp_rw [hI.mem_cl_iff_of_not_mem he, hI'.mem_cl_iff_of_not_mem he, image.indep_iff, 
--       ←image_insert_eq, image_eq_image f.injective, exists_eq_right], },
--   refine iff_of_true (loop.mem_cl _ _) (or.inr _), 
--   { simp_rw [loop_iff_dep, image.indep_iff, not_exists, not_and], 
--     exact λ x hx hex, he ((image_subset_range f x) (hex.symm.subset (mem_singleton e))) },
--   rintro x rfl, 
--   exact he (mem_range_self _), 
-- end  
-- @[simp] lemma image.flat_iff {F' : set E'} :
--   (M.image f).flat F' ↔ ∃ F, M.flat F ∧ F' = (f '' F) ∪ (range f)ᶜ :=
-- begin
--   rw [flat_iff_cl_self, image.cl_eq], 
--   refine ⟨λ h, _, _⟩, 
--   { refine ⟨f ⁻¹' F', _⟩,
--     suffices hflat : M.flat (f ⁻¹' F'), by { convert and.intro hflat h.symm, rw [hflat.cl] },
--     rw [←h, preimage_union, preimage_compl, preimage_range, compl_univ, union_empty, 
--         preimage_image_eq _ f.injective],
--     exact M.flat_of_cl _ },
--   rintro ⟨F, hF, rfl⟩, 
--   rw [preimage_union, preimage_compl, preimage_range, compl_univ, union_empty, 
--     preimage_image_eq _ f.injective, hF.cl], 
-- end   
-- lemma image.hyperplane_iff {H' : set E'} : 
--   (M.image f).hyperplane H' ↔ ∃ H, M.hyperplane H ∧ H' = (f '' H) ∪ (range f)ᶜ :=
-- begin
--   simp_rw [hyperplane_iff_maximal_proper_flat, image.flat_iff], 
--   split, 
--   { rintro ⟨⟨H, hfH, rfl⟩,hss, h⟩, 
--     refine ⟨_,⟨hfH,ssubset_univ_iff.mpr _,λ F hHF hF, eq_univ_of_forall (λ e, _),⟩,rfl⟩, 
--     { rintro rfl, 
--       rw [image_univ, union_compl_self] at hss,
--       exact hss.ne rfl },
--     simpa using (h (f '' F ∪ (range f)ᶜ) _ ⟨F, hF, rfl⟩).symm.subset (mem_univ (f e)), 
--     rw ssubset_iff_of_subset (union_subset_union_left _ (image_subset _ hHF.subset)), 
--     obtain ⟨x, hxH, hxF⟩ := exists_of_ssubset hHF, 
--     refine ⟨f x, or.inl (mem_image_of_mem _ hxH), _⟩, 
--     rwa [mem_union, f.injective.mem_set_image, not_or_distrib, not_mem_compl_iff, 
--       iff_true_intro (mem_range_self _), and_true] },
--   rintro ⟨H,⟨⟨hfH,hHss,hH⟩ ,rfl⟩⟩, 
--   refine ⟨⟨H,hfH,rfl⟩,ssubset_univ_iff.mpr (λ hu, hHss.ne (eq_univ_of_forall (λ e, _))), _⟩,  
--   { simpa using hu.symm.subset (mem_univ (f e)) },
--   rintro X hHX ⟨F, hF, rfl⟩, 
--   rw [hH F _ hF, image_univ, union_compl_self],  
--   refine ssubset_of_ne_of_subset (by { rintro rfl, exact hHX.ne rfl }) (λ e heH, _), 
--   have hss := hHX.subset, 
--   simpa using hss (or.inl (mem_image_of_mem f heH)), 
-- end 
-- lemma image.cocircuit_iff {K' : set E'} :   
--   (M.image f).cocircuit K' ↔ ∃ K, M.cocircuit K ∧ K' = f '' K :=
-- begin
--   simp_rw [←compl_hyperplane_iff_cocircuit, image.hyperplane_iff],
--   refine ⟨exists_imp_exists' compl _, exists_imp_exists' compl _⟩,
--   { simp_rw [@compl_eq_comm _ K', compl_union, compl_compl, f.injective.compl_image_eq, 
--       inter_distrib_right, compl_inter_self, union_empty, 
--       inter_eq_self_of_subset_left (image_subset_range _ _), eq_comm, 
--       iff_true_intro id, imp_true_iff]  },
--   simp_rw [@compl_eq_comm _ K', compl_union, f.injective.compl_image_eq, compl_compl, 
--     inter_distrib_right, compl_inter_self, union_empty, 
--     inter_eq_self_of_subset_left (image_subset_range _ _), eq_comm, 
--     iff_true_intro id, imp_true_iff], 
-- end   
-- @[simp] lemma image.r_eq (M : matroid E) (X' : set E') : (M.image f).r X' = M.r (f ⁻¹' X') :=
-- begin
--   obtain ⟨I, hI⟩ := (M.image f).exists_basis (X'),   
--   obtain ⟨I₀, hI₀, rfl⟩ := image.basis_iff.mp hI, 
--   rw [←hI.card, ncard_image_of_injective _ f.injective, ←hI₀.card], 
-- end 
-- @[simp] lemma image.loop_iff {e' : E'} : 
--   (M.image f).loop e' ↔ (∃ e, M.loop e ∧ e' = f e) ∨ e' ∈ (range f)ᶜ :=
-- begin
--   simp_rw [loop_iff_circuit, image.circuit_iff, @eq_comm _ {e'}, 
--     f.injective.image_eq_singleton_iff, mem_compl_iff, mem_range, not_exists, 
--     singleton_eq_singleton_iff, exists_prop, exists_eq_right], 
--   split, 
--   { rintro (⟨C, hC, a, rfl, rfl⟩ | h), exact or.inl ⟨_, hC, rfl⟩, exact or.inr h },
--   rintro (⟨e, he, rfl⟩ | h), exact or.inl ⟨_, he, ⟨_,rfl,rfl⟩⟩, exact or.inr h, 
-- end 
-- @[simp] lemma image.nonloop_iff {e' : E'} : (M.image f).nonloop e' ↔ ∃ e, M.nonloop e ∧ e' = f e :=
-- begin
--   simp_rw [←not_loop_iff, image.loop_iff, not_or_distrib, not_exists, not_and, not_mem_compl_iff],
--   split, 
--   { rintro ⟨h, ⟨e, rfl⟩⟩, exact ⟨_,λ h',h _ h' rfl,rfl⟩ }, 
--   rintro ⟨e, he, rfl⟩, exact ⟨λ h h' h_eq, he (by rwa f.injective h_eq), mem_range_self _⟩,     
-- end 
-- @[simp] lemma image.trans {E₀ E₁ E₂ : Type*} {M₀ : matroid E₀} {f₀ : E₀ ↪ E₁} {f₁ : E₁ ↪ E₂} : 
--   (M₀.image f₀).image f₁ = M₀.image (f₀.trans f₁) :=
-- begin
--   refine eq_of_indep_iff_indep_forall (λ I₂, _), 
--   simp only [image.indep_iff, function.embedding.trans_apply], 
--   split, 
--   { rintro ⟨I₁, ⟨⟨I₀, hI₀,rfl⟩, rfl⟩⟩, exact ⟨I₀, hI₀, by { ext, simp }⟩ },
--   rintro ⟨I₀, hI₀, rfl⟩, exact ⟨f₀ '' I₀, ⟨I₀, hI₀, rfl⟩, by { ext, simp }⟩,   
-- end 
-- /-- A matroid on `E'` and an injection from `E` into `E'` gives rise to a matroid on `E` -/
-- def preimage {E E' : Type u} (M' : matroid E') (f : E ↪ E') : matroid E := 
-- matroid_of_indep (λ I, M'.indep (f '' I)) (by simp) (λ I J hJ hIJ, hJ.subset (image_subset _ hIJ))
-- (begin
--   intros I B hI hIn hB,
--   obtain ⟨e, ⟨⟨e,he,rfl⟩,he'⟩ , hi⟩ := 
--     @indep.exists_insert_of_not_basis _ _ (f '' B) (range f) _ hI (image_subset_range _ _) _ _, 
--   { rw [f.injective.mem_set_image] at he', 
--     rw [←image_insert_eq] at hi, 
--     exact ⟨e, ⟨he,he'⟩, hi⟩ },
--   { refine λ hI', hIn ⟨hI,λ J hJ hIJ, ((image_eq_image f.injective).mp _).subset⟩,
--     exact (hI'.eq_of_subset_indep hJ (image_subset _ hIJ) (image_subset_range _ _)).symm },
--   refine hB.1.basis_of_maximal_subset (image_subset_range _ _) (λ J hJ hBJ hJr, _), 
--   obtain ⟨J, rfl⟩ := subset_range_iff_exists_image_eq.mp hJr, 
--   exact image_subset _ (hB.2 hJ ((image_subset_image_iff f.injective).mp hBJ))
-- end)
-- (begin
--   intros I X hI hIX, 
--   obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset (image_subset _ hIX), 
--   obtain ⟨J, rfl⟩ := subset_range_iff_exists_image_eq.mp (hJ.subset.trans (image_subset_range _ _)), 
--   refine ⟨J, ⟨hJ.indep, (image_subset_image_iff f.injective).mp hIJ, 
--     (image_subset_image_iff f.injective).mp hJ.subset⟩, λ K hK hJK, 
--     (image_subset_image_iff f.injective).mp 
--       (hJ.2 ⟨hK.1,image_subset _ hK.2.2⟩ (image_subset _ hJK))⟩,
-- end)
-- @[simp] lemma preimage.indep_iff {I : set E} : (M'.preimage f).indep I ↔ M'.indep (f '' I) := 
-- by simp [preimage]
-- @[simp] lemma preimage.set_of_indep_eq (M' : matroid E') : 
--   {I | (M'.preimage f).indep I} = {I | M'.indep (set.image f I)} := 
-- by { ext, simp }
-- @[simp] lemma preimage.basis_iff {I X : set E} : 
--   (M'.preimage f).basis I X ↔ M'.basis (f '' I) (f '' X) := 
-- begin
--   simp_rw [basis_iff, preimage.indep_iff, and.congr_right_iff, image_subset_image_iff f.injective, 
--     and.congr_right_iff], 
--   refine λ hI hIX, ⟨λ h J hJ hIJ hJX, _,λ h J hJ hIJ hJX, _⟩, 
--   { obtain ⟨J,rfl⟩ := subset_range_iff_exists_image_eq.mp (hJX.trans (image_subset_range _ _)), 
--     rw h _ hJ ((image_subset_image_iff f.injective).mp hIJ) 
--       ((image_subset_image_iff f.injective).mp hJX) },
--   rw [←(image_eq_image f.injective), h _ hJ (image_subset _ hIJ) (image_subset _ hJX)], 
-- end 
-- @[simp] lemma preimage.base_iff {B : set E} : 
--   (M'.preimage f).base B ↔ M'.basis (f '' B) (range f) :=
-- by rw [base_iff_basis_univ, preimage.basis_iff, image_univ]
-- @[simp] lemma preimage.cl_eq (M' : matroid E') (f : E ↪ E') (X : set E) : 
--   (M'.preimage f).cl X = f ⁻¹' (M'.cl (f '' X)) :=
-- begin
--   rw set.ext_iff, 
--   refine λ e, (em (e ∈ X)).elim 
--     (λ heX, iff_of_true (mem_cl_of_mem _ heX) (M'.mem_cl_of_mem ⟨_, heX, rfl⟩)) 
--     (λ heX, _),  
--   obtain ⟨I, hI⟩ := (M'.preimage f).exists_basis X, 
--   have hb := preimage.basis_iff.mp hI, 
--   rw [←hI.cl, hI.indep.mem_cl_iff_of_not_mem (not_mem_subset hI.subset heX), 
--     preimage.indep_iff, ←hb.cl, mem_preimage, 
--     hb.indep.mem_cl_iff_of_not_mem _, image_insert_eq],
--   rw f.injective.mem_set_image, 
--   exact not_mem_subset hI.subset heX,  
-- end 
-- @[simp] lemma preimage.flat_iff {F : set E} : 
--   (M'.preimage f).flat F ↔ M'.cl (f '' F) ∩ range f = f '' F :=
-- by rw [flat_iff_cl_self, preimage.cl_eq, ←image_eq_image f.injective, image_preimage_eq_inter_range]
-- @[simp] lemma preimage.circuit_iff {C : set E} : (M'.preimage f).circuit C ↔ M'.circuit (f '' C) :=
-- begin
--   simp_rw [circuit_iff, preimage.indep_iff, and.congr_right_iff], 
--   refine λ hd, ⟨λ h I hI hIC, _,λ h I hI hIC, _⟩, 
--   { obtain ⟨I, rfl⟩ := subset_range_iff_exists_image_eq.mp (hIC.trans (image_subset_range _ _)), 
--     rw h _ hI ((image_subset_image_iff f.injective).mp hIC) },
--   exact (image_eq_image f.injective).mp (h _ hI ((image_subset_image_iff f.injective).mpr hIC)), 
-- end 
-- @[simp] lemma preimage.r_eq (M' : matroid E') (X : set E) : (M'.preimage f).r X = M'.r (f '' X) :=
-- begin
--   obtain ⟨I, hI⟩ := (M'.preimage f).exists_basis X,   
--   rw [←hI.card, ←(preimage.basis_iff.mp hI).card, ncard_image_of_injective _ f.injective], 
-- end 
-- @[simp] lemma preimage.nonloop_iff {e : E} : (M'.preimage f).nonloop e ↔ M'.nonloop (f e) :=
-- by rw [←indep_singleton, ←indep_singleton, preimage.indep_iff, image_singleton]
-- @[simp] lemma preimage.loop_iff {e : E} : (M'.preimage f).loop e ↔ M'.loop (f e) :=
-- by rw [←not_iff_not, not_loop_iff, not_loop_iff, preimage.nonloop_iff] 
-- @[simp] lemma preimage_image (M : matroid E) (f : E ↪ E') : (M.image f).preimage f = M :=
-- begin
--   simp_rw [eq_iff_indep_iff_indep_forall, preimage.indep_iff, image.indep_iff], 
--   refine λ I, ⟨_,λ h, ⟨_,h,rfl⟩⟩, 
--   rintro ⟨I₀,hI₀, hf⟩, rwa ←(image_eq_image f.injective).mp hf,
-- end 
-- lemma image_preimage_eq_of_forall_subset_range (M' : matroid E') (f : E ↪ E') 
-- (h : ∀ I', M'.indep I' → I' ⊆ range f) : 
--   (M'.preimage f).image f = M' := 
-- begin
--   simp_rw [eq_iff_indep_iff_indep_forall, image.indep_iff, preimage.indep_iff], 
--   refine λ I', ⟨_,λ h', _⟩, 
--   { rintro ⟨I, hI, rfl⟩, exact hI },
--   obtain ⟨I,rfl⟩ := subset_range_iff_exists_image_eq.mp (h I' h'),  
--   exact ⟨_, h', rfl⟩, 
-- end 
-- @[simp] lemma preimage.trans {E₀ E₁ E₂ : Type*} {M₂ : matroid E₂} {f₀ : E₀ ↪ E₁} {f₁ : E₁ ↪ E₂} : 
--   (M₂.preimage f₁).preimage f₀ = M₂.preimage (f₀.trans f₁) :=
-- by simp_rw [eq_iff_indep_iff_indep_forall, preimage.indep_iff, image_image, 
--     function.embedding.trans_apply, iff_self, forall_const]
-- end embed
-- section congr 
-- variables {E E₀ E₁ E₂ : Type u} {e : E₁ ≃ E₂} {M₀ : matroid E₀} {M₁ : matroid E₁} {M₂ : matroid E₂}
-- /-- An equivalence between types induces a map from a matroid on one type to one on another -/
-- def congr (M₁ : matroid E₁) (e : E₁ ≃ E₂) : matroid E₂ := M₁.preimage (e.symm.to_embedding)
-- @[simp] lemma congr_eq_preimage (M₁ : matroid E₁) (e : E₁ ≃ E₂) : 
--   M₁.congr e = M₁.preimage e.symm.to_embedding := rfl 
-- lemma congr_eq_image (M₁ : matroid E₁) (e : E₁ ≃ E₂) : M₁.congr e = M₁.image e.to_embedding :=
-- begin
--   simp_rw [eq_iff_indep_iff_indep_forall, congr_eq_preimage, image.indep_iff, preimage.indep_iff], 
--   exact λ I, ⟨λ h, ⟨e.symm '' I,h,by { ext, simp, } ⟩, 
--     by { rintro ⟨I,hI,rfl⟩, convert hI, ext, simp }⟩, 
-- end 
-- lemma congr.indep_iff {I : set E₂} : (M₁.congr e).indep I ↔ M₁.indep (e.symm '' I) := by simp 
-- lemma congr.symm_indep_iff {I : set E₁} : (M₂.congr e.symm).indep I ↔ M₂.indep (e '' I) := by simp 
-- @[simp] lemma congr.base_iff {B : set E₂} : (M₁.congr e).base B ↔ M₁.base (e.symm '' B) :=
-- by simp [←base_iff_basis_univ]
-- @[simp] lemma congr.symm_base_iff {B : set E₁} : (M₂.congr e.symm).base B ↔ M₂.base (e '' B) :=
-- by simp [base_iff_basis_univ]
-- lemma congr.basis_iff {I X : set E₂} : 
--   (M₁.congr e).basis I X ↔ M₁.basis (e.symm '' I) (e.symm '' X) := by simp 
-- lemma congr.symm_basis_iff {e : E₁ ≃ E₂} {M₂ : matroid E₂} {I X : set E₁} :
--   (M₂.congr e.symm).basis I X ↔ M₂.basis (e '' I) (e '' X) := by simp 
-- lemma congr.r_eq (e : E₁ ≃ E₂) (M₁ : matroid E₁) (X : set E₂) :
--   (M₁.congr e).r X = M₁.r (e.symm '' X) := by simp
-- lemma congr.symm_r_eq (e : E₁ ≃ E₂) (M₂ : matroid E₂) (X : set E₁) :
--   (M₂.congr e.symm).r X = M₂.r (e '' X) := by simp 
-- lemma congr.circuit_iff {C : set E₂} : (M₁.congr e).circuit C ↔ M₁.circuit (e.symm '' C) := by simp 
-- lemma congr.symm_circuit_iff {C : set E₁} : (M₂.congr e.symm).circuit C = M₂.circuit (e '' C) :=
-- by simp
-- @[simp] lemma congr.flat_iff {F : set E₂} : (M₁.congr e).flat F ↔ M₁.flat (e.symm '' F) :=
-- by rw [congr_eq_preimage, preimage.flat_iff, equiv.coe_to_embedding, equiv.range_eq_univ, 
--     inter_univ, ←flat_iff_cl_self]
-- @[simp] lemma congr.symm_flat_iff {F : set E₁} : (M₂.congr e.symm).flat F = M₂.flat (e '' F) :=
-- by simp [←flat_iff_cl_self]
-- lemma congr.loop_iff {x : E₂} : (M₁.congr e).loop x ↔ M₁.loop (e.symm x) := by simp 
-- lemma congr.symm_loop_iff {x : E₁} : (M₂.congr e.symm).loop x ↔ M₂.loop (e x) := by simp 
-- lemma congr.nonloop_iff {x : E₂} : (M₁.congr e).nonloop x ↔ M₁.nonloop (e.symm x) := by simp 
-- lemma congr.symm_nonloop_iff {x : E₁} : (M₂.congr e.symm).nonloop x ↔ M₂.nonloop (e x) := by simp 
-- end congr
end MatroidIn


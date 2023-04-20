import ..dual

noncomputable theory
open_locale classical

open set

namespace matroid

universe u

section iso

variables {E E₀ E₁ E₂ : Type u} {M₀ : matroid E₀} {M₁ : matroid E₁} {M₂ : matroid E₂}

/-- Two matroids are isomorphic if there is a map between ground sets that preserves bases -/
def is_iso (M₁ : matroid E₁) (M₂ : matroid E₂) (e : E₁ ≃ E₂) :=
  ∀ B, M₁.base B ↔ M₂.base (e '' B)

/-- A bundled isomorphism between two matroids -/
structure iso (M₁ : matroid E₁) (M₂ : matroid E₂) :=
(to_fun : E₁ ≃ E₂)
(on_base : ∀ B, M₁.base B ↔ M₂.base (to_fun '' B))

infix ` ≃i ` :75 :=  matroid.iso

instance : has_coe_to_fun (M₁ ≃i M₂) (λ _, E₁ → E₂) :=
  ⟨λ e, e.to_fun⟩

def iso.refl (M : matroid E) : M ≃i M := ⟨equiv.refl E, λ B, by simp⟩
def iso.symm (e : M₁ ≃i M₂) : M₂ ≃i M₁ := ⟨e.to_fun.symm, λ B, by {rw e.on_base, simp, }⟩

/-- An equivalence between types induces a map from a matroid on one type to one on another -/
def congr_equiv (M₁ : matroid E₁) (e : E₁ ≃ E₂) : matroid E₂ :=
{ base := λ B, M₁.base (e ⁻¹' B),
  exists_base' := by
    {obtain ⟨B₁,hB₁⟩ := M₁.exists_base, exact ⟨e '' B₁, by simpa using hB₁⟩} ,
  base_exchange' :=
  begin
    rintro B₁ B₂ hB₁ hB₂ x hx,
    have hx' : e.symm x ∈ e ⁻¹' B₁ \ e⁻¹' B₂, by simpa,
    obtain ⟨y, hy, hBy⟩ := hB₁.exchange hB₂ hx',
    refine ⟨e y, by simpa, _⟩,
    dsimp only,
    simp_rw [←union_singleton, preimage_union, preimage_diff] at ⊢ hBy,
    convert hBy;
    simp [preimage_equiv_eq_image_symm],
  end,
  maximality := 
  begin
    rintro I X ⟨B, hB, hIB⟩ hIX, 
    obtain ⟨J, ⟨⟨BJ,hBJ,hBJB⟩,⟨hIJ, hJX⟩⟩, hJmax⟩
      := M₁.maximality (e ⁻¹' I) (e ⁻¹' X) ⟨e ⁻¹' B, _⟩ (preimage_mono hIX), 
    { refine ⟨e '' J, ⟨⟨e '' BJ, by simpa, image_subset _ hBJB⟩,_,_⟩, _⟩,  
      { convert image_subset e hIJ, rw e.image_preimage },
      { convert image_subset e hJX, rw e.image_preimage },
      rintro K ⟨⟨BK, hBK, hKBK⟩, hIK, hKX⟩ hJK, 
      rw [←e.preimage_subset, e.preimage_image], 
      refine hJmax ⟨⟨_,hBK,preimage_mono hKBK⟩,preimage_mono hIK,preimage_mono hKX⟩ _, 
      convert preimage_mono hJK, 
      rw e.preimage_image },
    exact ⟨hB, preimage_mono hIB⟩,  
  end }

@[simp] lemma congr_equiv_apply_base {e : E₁ ≃ E₂} {M₁ : matroid E₁} {B : set E₂} :
  (M₁.congr_equiv e).base B ↔ M₁.base (e ⁻¹' B) :=
iff.rfl

@[simp] lemma congr_equiv_apply_indep {e : E₁ ≃ E₂} {M₁ : matroid E₁} {I : set E₂} :
  (M₁.congr_equiv e).indep I ↔ M₁.indep (e ⁻¹' I) :=
begin
  simp_rw [indep, congr_equiv_apply_base],
  split,
  { rintro ⟨B₂, hB₂, hIB₂⟩, exact ⟨_, hB₂, preimage_mono hIB₂⟩},
  rintro ⟨B₁, hB₁, hIB₁⟩,
  refine ⟨e '' B₁, by rwa e.preimage_image, _⟩,
  rwa [←equiv.subset_image, ←preimage_equiv_eq_image_symm],
end

@[simp] lemma congr_equiv_apply_symm_base {e : E₁ ≃ E₂} {M₂ : matroid E₂} {B : set E₁} :
  (M₂.congr_equiv e.symm).base B ↔ M₂.base (e '' B) :=
by simp [←image_equiv_eq_preimage_symm]

@[simp] lemma congr_equiv_apply_symm_indep {e : E₁ ≃ E₂} {M₂ : matroid E₂} {I : set E₁} :
  (M₂.congr_equiv e.symm).indep I ↔ M₂.indep (e '' I) :=
by simp [←image_equiv_eq_preimage_symm]

@[simp] lemma congr_equiv_apply_basis {e : E₁ ≃ E₂} {M₁ : matroid E₁} {I X : set E₂} :
  (M₁.congr_equiv e).basis I X ↔ M₁.basis (e ⁻¹' I) (e ⁻¹' X) :=
begin
  suffices : ∀ {F₁ F₂ : Type*} {f : F₁ ≃ F₂} {N₁ : matroid F₁} {J Y : set F₂}, 
    (N₁.congr_equiv f).basis J Y → N₁.basis (f ⁻¹' J) (f ⁻¹' Y), 
  { refine ⟨this, λ hb', _⟩,
    convert @this E₂ E₁ e.symm (M₁.congr_equiv e) (e ⁻¹' I) (e ⁻¹' X) _,
    { rw [equiv.symm_preimage_preimage] }, 
    { rw [equiv.symm_preimage_preimage] },
    convert hb', ext B, simp  },

  simp only [basis, congr_equiv_apply_indep, equiv.preimage_subset, and.congr_right_iff], 
  
  rintro F₁ F₂ f N₁ J Y ⟨⟨hA, hAX⟩,h'⟩,
  refine ⟨⟨hA, preimage_mono hAX⟩, _⟩, 
  rintro K ⟨hK, hKX⟩ hIK, 
  rw [←f.image_subset, f.image_preimage], 
  refine h' ⟨by rwa f.preimage_image, _⟩ _; 
  rwa [←f.preimage_subset, f.preimage_image], 
end

@[simp] lemma congr_equiv_apply_symm_basis {e : E₁ ≃ E₂} {M₂ : matroid E₂} {I X : set E₁} :
  (M₂.congr_equiv e.symm).basis I X ↔ M₂.basis (e '' I) (e '' X) :=
by simp [←image_equiv_eq_preimage_symm]

@[simp] lemma congr_equiv_apply_r {e : E₁ ≃ E₂} {M₁ : matroid E₁} (X : set E₂) :
  (M₁.congr_equiv e).r X = M₁.r (e ⁻¹' X) :=
begin
  obtain ⟨I, hI⟩ := (M₁.congr_equiv e).exists_basis X,
  rw [←hI.r, hI.indep.r],
  rw [congr_equiv_apply_basis] at hI,
  rw [←hI.r, hI.indep.r, preimage_equiv_eq_image_symm, ncard_image_of_injective _ e.symm.injective],
end

@[simp] lemma congr_equiv_apply_symm_r {e : E₁ ≃ E₂} {M₂ : matroid E₂} (X : set E₁) :
  (M₂.congr_equiv e.symm).r X = M₂.r (e '' X) :=
by simp [←image_equiv_eq_preimage_symm]

@[simp] lemma congr_equiv_apply_circuit {e : E₁ ≃ E₂} {M₁ : matroid E₁} {C : set E₂} :
  (M₁.congr_equiv e).circuit C ↔ M₁.circuit (e ⁻¹' C) :=
begin
  simp_rw [circuit_iff_dep_forall_diff_singleton_indep, congr_equiv_apply_indep, preimage_diff],
  convert iff.rfl,
  rw eq_iff_iff,
  refine ⟨λ h x hxC, _,λ h x (hx : e x ∈ C), _⟩,
  { convert h (e.symm x) (by simpa),
    rw [←image_singleton, preimage_equiv_eq_image_symm]},
  convert h _ hx,
  rw [←image_singleton, preimage_image_eq _ e.injective],
end

@[simp] lemma congr_equiv_apply_symm_circuit {e : E₁ ≃ E₂} {M₂ : matroid E₂} {C : set E₁} :
  (M₂.congr_equiv e.symm).circuit C = M₂.circuit (e '' C) :=
by simp [←image_equiv_eq_preimage_symm]

@[simp] lemma congr_equiv_apply_flat {e : E₁ ≃ E₂} {M₁ : matroid E₁} {F : set E₂} :
  (M₁.congr_equiv e).flat F ↔ M₁.flat (e ⁻¹' F) :=
begin
  simp_rw [flat_def, congr_equiv_apply_basis],
  refine ⟨λ h I X hIF hFX, _,λ h I X hIF hFX, _⟩,
  { rw [←image_subset_iff],
    exact h (e '' I) (e '' X) (by simpa) (by simpa)},
  exact (equiv.preimage_subset e X F).mp (h (⇑e ⁻¹' I) (⇑e ⁻¹' X) hIF hFX),
end

@[simp] lemma congr_equiv_apply_symm_flat {e : E₁ ≃ E₂} {M₂ : matroid E₂} {F : set E₁} :
  (M₂.congr_equiv e.symm).flat F = M₂.flat (e '' F) :=
by simp [←image_equiv_eq_preimage_symm]

end iso

section embed

variables {E E' : Type*} {f : E ↪ E'} 

/-- Embed a matroid as a restriction in a larger type. All elements outside the image are loops. -/
def image (M : matroid E) (f : E ↪ E') : matroid E' :=
matroid_of_indep (λ I', ∃ I, M.indep I ∧ I' = f '' I) ⟨_, M.empty_indep, by simp⟩
( begin 
  rintro _ _ ⟨J, hJ, rfl⟩ hIJ, refine ⟨J ∩ f ⁻¹' I, hJ.subset (inter_subset_left _ _), _⟩,
  rw [image_inter f.injective, image_preimage_eq_inter_range, ←inter_assoc, 
    inter_eq_right_iff_subset.mpr hIJ, eq_comm, 
    inter_eq_left_iff_subset.mpr (hIJ.trans (image_subset_range _ _))], 
  end)
( begin
    rintro _ _ ⟨I, hI, rfl⟩ hIn ⟨⟨B,hB,rfl⟩,hBmax⟩, 
    obtain ⟨e, he, heI⟩ := hI.exists_insert_of_not_base _ (hB.base_of_maximal (λ J hJ hBJ, _)), 
    { exact ⟨f e, by rwa [←image_diff f.injective, f.injective.mem_set_image], 
      ⟨_, heI, image_insert_eq.symm⟩⟩ },
    { refine λ hI', hIn ⟨⟨_,hI,rfl⟩,_⟩, 
      rintro _ ⟨J, hJ, rfl⟩ hIJ,  
      rw hI'.eq_of_subset_indep hJ, 
      rwa image_subset_image_iff f.injective at hIJ },
    exact hBJ.antisymm 
      ((image_subset_image_iff f.injective).mp (hBmax ⟨_,hJ,rfl⟩ (image_subset _ hBJ))),   
  end)
(begin
  rintro _ X ⟨I,hI,rfl⟩ hIX, 
  obtain ⟨J, hIJ, hJ⟩ := hI.subset_basis_of_subset (image_subset_iff.mp hIX), 
  refine ⟨f '' J, ⟨⟨_,hJ.indep,rfl⟩,image_subset _ hIJ, image_subset_iff.mpr hJ.subset⟩, _⟩,
  rintro _ ⟨⟨K,hK,rfl⟩,hIK,hKX⟩ hJK,   
  rw hJ.eq_of_subset_indep hK ((image_subset_image_iff f.injective).mp hJK) 
    (image_subset_iff.mp hKX), 
end)

@[simp] lemma image_indep_iff {I' : set E'} {M : matroid E} : 
  (M.image f).indep I' ↔ ∃ I, M.indep I ∧ I' = f '' I := 
by simp [image]

/-- A matroid on `E'` and an injection from `E` into `E'` gives rise to a matroid on `E` -/
def preimage {E E' : Type*} (M' : matroid E') (f : E ↪ E') : matroid E := 
matroid_of_indep (λ I, M'.indep (f '' I)) (by simp) (λ I J hJ hIJ, hJ.subset (image_subset _ hIJ))
(begin
  intros I B hI hIn hB,
  obtain ⟨e, ⟨⟨e,he,rfl⟩,he'⟩ , hi⟩ := 
    @indep.exists_insert_of_not_basis _ _ _ (f '' B) (range f) hI (image_subset_range _ _) _ _, 
  { rw [f.injective.mem_set_image] at he', 
    rw [←image_insert_eq] at hi, 
    exact ⟨e, ⟨he,he'⟩, hi⟩ },
  { refine λ hI', hIn ⟨hI,λ J hJ hIJ, ((image_eq_image f.injective).mp _).subset⟩,
    exact (hI'.eq_of_subset_indep hJ (image_subset _ hIJ) (image_subset_range _ _)).symm },
  refine hB.1.basis_of_maximal_subset (image_subset_range _ _) (λ J hJ hBJ hJr, _), 
  obtain ⟨J, rfl⟩ := subset_range_iff_exists_image_eq.mp hJr, 
  exact image_subset _ (hB.2 hJ ((image_subset_image_iff f.injective).mp hBJ))
end)
(begin
  intros I X hI hIX, 
  obtain ⟨J, hIJ, hJ⟩ := hI.subset_basis_of_subset (image_subset _ hIX), 
  obtain ⟨J, rfl⟩ := subset_range_iff_exists_image_eq.mp (hJ.subset.trans (image_subset_range _ _)), 
  
  refine ⟨J, ⟨hJ.indep, (image_subset_image_iff f.injective).mp hIJ, 
    (image_subset_image_iff f.injective).mp hJ.subset⟩, λ K hK hJK, 
    (image_subset_image_iff f.injective).mp 
      (hJ.2 ⟨hK.1,image_subset _ hK.2.2⟩ (image_subset _ hJK))⟩,
end)

end embed

end matroid 
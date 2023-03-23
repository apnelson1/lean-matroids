import .pseudominor

noncomputable theory 
open set 
open function 

variables {E E₀ E₁ E₂ : Type*} [finite E] [finite E₀] [finite E₁] [finite E₂] 
  {e f : E} {M : matroid E} {M₀ : matroid E₀} {M₁ : matroid E₁} {M₂ : matroid E₂} 
  {X Y D C F B I I₀ R: set E}

namespace matroid 

/-- A structure encoding the fact that `M₀` is isomorphic to a minor of `M` -/
structure minor_embedding (M₀ : matroid E₀) (M : matroid E) := 
(contr : set E)
(to_embedding : E₀ ↪ E)
(disj : disjoint (range to_embedding) contr)
(indep_iff' : ∀ X, M₀.indep X ↔ (M ⟋ contr).indep (to_embedding '' X))

namespace minor_embedding

infix ` →m ` :25 :=  minor_embedding

instance : has_coe_to_fun (minor_embedding M₀ M) (λ a, E₀ → E) := ⟨λ φ, φ.to_embedding⟩ 

/-- Two `minor_embedding`s are equivalent if they differ only in choice of their contract and 
  delete-sets-/
def equiv (φ₁ φ₂ : M₀ →m M) := 
  (φ₁ : E₀ → E) = (φ₂ : E₀ → E)    

@[simp] lemma coe_to_embedding (φ : M₀ →m M) : 
  (φ.to_embedding : E₀ → E) = (φ : E₀ → E) := 
rfl 

@[simp] lemma inj (φ : M₀ →m M) {x y : E₀} :
  φ x = φ y ↔ x = y :=
φ.to_embedding.injective.eq_iff 

lemma injective (φ : M₀ →m M) :
  function.injective φ :=   
φ.to_embedding.injective

/-- The contract-set of a `minor_embedding` -/
def C (φ : M₀ →m M) : set E := 
  φ.contr 

/-- The ground set in `M` of a `minor_embedding` -/
def ground (φ : M₀ →m M) : set E := 
  set.range φ

/-- The delete-set of a `minor_embedding` --/
def D (φ : M₀ →m M) : set E := 
  (φ.C ∪ φ.ground)ᶜ 

lemma mem_ground (φ : M₀ →m M) (x : E₀) :
  φ x ∈ φ.ground := 
mem_range_self _

lemma image_subset_ground (φ : M₀ →m M) (I : set E₀) : 
  φ '' I ⊆ φ.ground :=
image_subset_range _ _

lemma not_mem_C (φ : M₀ →m M) (x : E₀) :
  φ x ∉ φ.C := 
λ h, φ.disj.ne_of_mem ⟨x,rfl⟩ h rfl

lemma not_mem_D (φ : M₀ →m M) (x : E₀) :
  φ x ∉ φ.D := 
not_mem_compl_iff.mpr (or.inr (φ.mem_ground _))

lemma C_disjoint_ground (φ : M₀ →m M) : 
  disjoint φ.C φ.ground := 
disjoint_iff_forall_ne.mpr (by {rintro x hx _ ⟨y,rfl⟩ rfl, exact φ.not_mem_C _ hx}) 

lemma D_disjoint_ground (φ : M₀ →m M) : 
  disjoint φ.D φ.ground := 
disjoint_iff_forall_ne.mpr (by {rintro x hx _ ⟨y,rfl⟩ rfl, exact φ.not_mem_D _ hx}) 

lemma indep_iff (φ : M₀ →m M) {I₀ : set E₀} : 
  M₀.indep I₀ ↔ (M ⟋ φ.C).indep (φ '' I₀) := 
φ.indep_iff' I₀  

lemma basis_iff (φ : M₀ →m M) {I₀ X₀ : set E₀} :
  M₀.basis I₀ X₀ ↔ (M ⟋ φ.C).basis (φ '' I₀) (φ '' X₀) :=
begin
  simp_rw [basis_iff, ←φ.indep_iff, image_subset_image_iff φ.injective], 
  split, 
  { rintro ⟨hi,hss,h⟩,
    refine ⟨hi,hss,λ J hJ hssJ hJss, _⟩,
    have h'J : ∃ J₀, φ '' J₀ = J,   
    { rw [←subset_range_iff_exists_image_eq], 
      exact hJss.trans (φ.image_subset_ground X₀)} ,
    obtain ⟨J₀,rfl⟩ := h'J,   
    rw [image_subset_image_iff φ.injective] at hssJ hJss, 
    rw [←φ.indep_iff] at hJ, 
    rw [h _ hJ hssJ hJss]},
  rintro ⟨hi, hss, h⟩,
  refine ⟨hi, hss, λ J₀ hJ₀ hssJ₀ hJ₀ss, hssJ₀.antisymm _⟩, 
  specialize h (φ '' J₀) (φ.indep_iff.mp hJ₀) ((image_subset_image_iff φ.injective).mpr hssJ₀)
    ((image_subset_image_iff φ.injective).mpr hJ₀ss), 
  rw ←(image_subset_image_iff φ.injective),  
  exact h.symm.subset, 
end  

lemma indep_project_iff (φ : M₀ →m M) (I₀ C₀ : set E₀) : 
  (M₀ ⟋ C₀).indep I₀ ↔ (M ⟋ φ.C ⟋ (φ '' C₀)).indep (φ '' I₀) :=
begin
  obtain ⟨IC₀,hIC₀⟩ := M₀.exists_basis C₀, 
  have h''  := φ.basis_iff.mp hIC₀, 
  obtain (hI₀ | hI₀) := em (M₀.indep I₀),  
  { rw [←hIC₀.project_eq_project,  ←h''.project_eq_project, 
      indep.project_indep_iff h''.indep (φ.indep_iff.mp hI₀), ←image_union, 
      ←φ.indep_iff, disjoint_image_iff φ.injective, indep.project_indep_iff hIC₀.indep hI₀]},

  apply iff_of_false (λ hI₀', hI₀ (indep_of_project_indep hI₀')) (λ hI₀', hI₀ _), 
  have h' := indep_of_project_indep hI₀', 
  rwa [←φ.indep_iff] at h', 
end  

/-- If `M₀` is a minor of `M₁` and `M₁` is a minor of `M₂`, then `M₀` is a minor of `M₂` -/
def trans (φ₀₁ : M₀ →m M₁) (φ₁₂ : M₁ →m M₂) : 
  M₀ →m M₂ := 
{ contr := (φ₁₂ '' φ₀₁.C) ∪ φ₁₂.C ,
  to_embedding := φ₀₁.to_embedding.trans φ₁₂.to_embedding, 
  disj := begin
    refine disjoint_iff_forall_ne.mpr _,
    simp_rw [mem_range, embedding.trans_apply, coe_to_embedding], 
    rintro x ⟨x₀,rfl⟩ y (⟨x₁,hx₁,rfl⟩ | hy) he,
    { simp_rw [minor_embedding.inj] at he,
      subst he, 
      exact φ₀₁.not_mem_C _ hx₁}, 
    subst he,  
    exact φ₁₂.not_mem_C _ hy, 
  end,
  indep_iff' := 
  begin
    intro X,  
    simp only [embedding.trans_apply, coe_to_embedding ], 
    nth_rewrite 1 ←image_image,  
    dsimp only, 
    rw [←project_project, project_project_comm, ←φ₁₂.indep_project_iff, φ₀₁.indep_iff],
  end }

@[simp] lemma trans_apply (φ₀₁ : M₀ →m M₁) (φ₁₂ : M₁ →m M₂) (x : E₀) : 
  (φ₀₁.trans φ₁₂) x = φ₁₂ (φ₀₁ x) := 
rfl   

@[simp] lemma trans_apply_image (φ₀₁ : M₀ →m M₁) (φ₁₂ : M₁ →m M₂) (X : set E₀) : 
  (φ₀₁.trans φ₁₂) '' X = φ₁₂ '' (φ₀₁ '' X) := 
by {ext, simp only [trans_apply, mem_image, exists_exists_and_eq_and]}

@[simp] lemma trans_apply_C (φ₀₁ : M₀ →m M₁) (φ₁₂ : M₁ →m M₂) : 
  (φ₀₁.trans φ₁₂).C = (φ₁₂ '' φ₀₁.C) ∪ φ₁₂.C := 
rfl 

@[simp] lemma trans_apply_ground (φ₀₁ : M₀ →m M₁) (φ₁₂ : M₁ →m M₂) : 
  (φ₀₁.trans φ₁₂).ground = φ₁₂ '' (φ₀₁.ground) := 
by {ext, simp [ground]}

/- What a mess! Should be trivial -/
@[simp] lemma trans_apply_D (φ₀₁ : M₀ →m M₁) (φ₁₂ : M₁ →m M₂) : 
  (φ₀₁.trans φ₁₂).D = (φ₁₂ '' φ₀₁.D) ∪ φ₁₂.D := 
begin
  apply compl_injective, 
  simp only [D, trans_apply_C, trans_apply_ground, ground, compl_compl, 
    compl_union, φ₁₂.injective.compl_image, compl_inter, image_union], 
  rw [inter_distrib_right, inter_eq_left_iff_subset.mpr (image_subset_range φ₁₂ _), 
    compl_inter_self, union_empty, ←range_comp, inter_distrib_left, inter_distrib_right, 
    inter_eq_right_iff_subset.mpr 
      (subset_compl_iff_disjoint_right.mpr φ₁₂.C_disjoint_ground : φ₁₂.C ⊆ (range φ₁₂)ᶜ), 
    union_eq_right_iff_subset.mpr (inter_subset_right _ _), inter_distrib_right, 
    compl_inter_self, union_empty, inter_distrib_right, 
    inter_eq_left_iff_subset.mpr (range_comp_subset_range _ _), 
    union_distrib_right, union_distrib_left,
    union_eq_left_iff_subset.mpr (range_comp_subset_range _ _), ←union_assoc, 
    union_comm φ₁₂.C, eq_comm],
  
  convert inter_eq_left_iff_subset.mpr (union_subset (union_subset _ (subset_union_left _ _)) _), 
  { exact (image_subset_range _ _).trans (subset_union_right _ _)},
  exact (range_comp_subset_range _ _).trans (subset_union_right _ _), 
end 

/-- A `minor_embedding` gives rise to a dual embedding -/
def dual (φ : M₀ →m M) : 
  M₀.dual →m M.dual := 
{ contr := φ.D,
  to_embedding := φ.to_embedding,
  disj := φ.D_disjoint_ground.symm,
  indep_iff' := begin
    intro X, 
    
    -- rw [dual_indep_iff_coindep], 
  end  }

/-- The scum theorem; every `minor_embedding`, has an equivalent embedding whose contract-set is 
  independent and whose delete-set is coindependent -/
theorem exists_indep_coindep_embedding (φ : M₀ →m M) : 
  ∃ (ψ : M₀ →m M), ψ.equiv φ ∧ M.indep ψ.C ∧ M.coindep φ.D := 
sorry         



end minor_embedding


/-- `M₀` is isomorphic to a minor of `M` if there is a `minor_embedding` from `M₀` to `M` -/
def is_iso_minor (M₀ : matroid E₀) (M : matroid E) : Prop := 
  nonempty (M₀ →m M)

/-- A matroid `M₀` on a subtype is a minor of `M` if there is a `minor_embedding` whose associated
  embedding function is the inclusion map. -/
def is_minor {X : set E} (M₀ : matroid X) (M : matroid E) : Prop :=
  ∃ (φ : M₀ →m M), (φ : X → E) = coe   

infix ` ≤m ` : 25 := is_iso_minor 








end matroid 
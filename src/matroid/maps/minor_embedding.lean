import ..pseudominor

noncomputable theory 
open set 
open function 

variables {E E₀ E₁ E₂ : Type*} [finite E] [finite E₀] [finite E₁] [finite E₂] 
  {e f : E} {M : matroid E} {M₀ : matroid E₀} {M₁ : matroid E₁} {M₂ : matroid E₂} 
  {X Y D C F B I I₀ R: set E}

namespace matroid 

/-- A structure encoding the fact that `M₀` is isomorphic to a minor of `M` -/
@[ext] structure minor_embedding (M₀ : matroid E₀) (M : matroid E) := 
(contr : set E)
(del : set E)
(disj : disjoint contr del)
(to_embedding : E₀ ↪ E)
(range_eq : range to_embedding = (contr ∪ del)ᶜ)
(indep_iff' : ∀ X, M₀.indep X ↔ (M ⟋ contr).indep (to_embedding '' X))

namespace minor_embedding

infix ` →m ` :25 :=  minor_embedding

instance : has_coe_to_fun (minor_embedding M₀ M) (λ a, E₀ → E) := ⟨λ φ, φ.to_embedding⟩ 

instance [finite E₀] [finite E] {M₀ : matroid E₀} {M : matroid E} : finite (M₀ →m M) :=
begin
  set f : (M₀ →m M) → (set E) × (set E) × (E₀ ↪ E)  := (λ φ, ⟨φ.contr, φ.del, φ.to_embedding⟩), 
  apply finite.of_injective f,
  intros φ₁ φ₂ h, 
  simp only [prod.mk.inj_iff] at h, obtain ⟨h₁,h₂,h₃⟩ := h, 
  apply matroid.minor_embedding.ext; assumption, 
end 

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

/-- The delete-set of a `minor_embedding` --/
def D (φ : M₀ →m M) : set E := 
  φ.del  

/-- The ground set in `M` of a `minor_embedding` -/
def ground (φ : M₀ →m M) : set E := 
  set.range φ

lemma ground_eq_range (φ : M₀ →m M) : 
  φ.ground = range φ := 
rfl 

lemma ground_eq_compl (φ : M₀ →m M) : 
  φ.ground = (φ.C ∪ φ.D)ᶜ := 
φ.range_eq  

lemma mem_ground (φ : M₀ →m M) (x : E₀) :
  φ x ∈ φ.ground := 
mem_range_self _

lemma image_subset_ground (φ : M₀ →m M) (I : set E₀) : 
  φ '' I ⊆ φ.ground :=
image_subset_range _ _

lemma C_disjoint_D (φ : M₀ →m M) : 
  disjoint φ.C φ.D := 
φ.disj   

lemma C_disjoint_ground (φ : M₀ →m M) : 
  disjoint φ.C φ.ground := 
by {rw ground_eq_compl, 
  exact disjoint_of_subset_left (subset_union_left _ _) disjoint_compl_right}

lemma D_disjoint_ground (φ : M₀ →m M) : 
  disjoint φ.D φ.ground := 
by {rw ground_eq_compl, 
  exact disjoint_of_subset_left (subset_union_right _ _) disjoint_compl_right}

@[simp] lemma compl_C_eq (φ : M₀ →m M) : 
  φ.Cᶜ = φ.ground ∪ φ.D :=
by {rw [ground_eq_compl, compl_union, union_distrib_right, compl_union_self, inter_univ, eq_comm, 
  union_eq_left_iff_subset, subset_compl_iff_disjoint_left], exact C_disjoint_D _}   

@[simp] lemma compl_D_eq (φ : M₀ →m M) : 
  φ.Dᶜ = φ.ground ∪ φ.C :=
by {rw [ground_eq_compl, compl_union, union_distrib_right, compl_union_self, univ_inter, eq_comm, 
  union_eq_left_iff_subset, subset_compl_iff_disjoint_left], exact (C_disjoint_D _).symm}

@[simp] lemma compl_ground_eq (φ : M₀ →m M) : 
  φ.groundᶜ = φ.C ∪ φ.D :=
by rw [ground_eq_compl, compl_compl] 

lemma not_mem_C (φ : M₀ →m M) (x : E₀) :
  φ x ∉ φ.C := 
λ h, φ.C_disjoint_ground.ne_of_mem h (φ.mem_ground x) rfl

lemma not_mem_D (φ : M₀ →m M) (x : E₀) :
  φ x ∉ φ.D := 
λ h, φ.D_disjoint_ground.ne_of_mem h (φ.mem_ground x) rfl

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
{ contr := (φ₁₂ '' φ₀₁.C) ∪ φ₁₂.C,
  del := (φ₁₂ '' φ₀₁.D) ∪ φ₁₂.D,
  disj :=
  begin
    rw [disjoint_union_left, disjoint_union_right, disjoint_union_right, 
      disjoint_image_iff φ₁₂.injective], 
    exact ⟨⟨C_disjoint_D _, 
      disjoint_of_subset_left (image_subset_ground _ _) (D_disjoint_ground _).symm⟩,  
      disjoint_of_subset_right (image_subset_ground _ _) (C_disjoint_ground _),
      C_disjoint_D _⟩,  
  end,
  to_embedding := φ₀₁.to_embedding.trans φ₁₂.to_embedding,
  range_eq := 
  begin
    simp_rw [embedding.trans, coe_to_embedding, embedding.coe_fn_mk, compl_union, range_comp, 
      range_id', image_univ, ←ground_eq_range],
    rw [ground_eq_compl, compl_eq_univ_diff, image_diff φ₁₂.injective, image_univ, 
      ←ground_eq_range, ground_eq_compl, image_union, compl_union, diff_eq_compl_inter, 
      compl_union, inter_right_comm, inter_assoc, inter_assoc, inter_assoc, inter_comm φ₁₂.Dᶜ ]
  end,
  indep_iff' := 
  begin
    intro X,  
    simp only [embedding.trans_apply, coe_to_embedding ], 
    nth_rewrite 1 ←image_image,  
    dsimp only, 
    rw [←project_project, project_project_comm, ←φ₁₂.indep_project_iff, φ₀₁.indep_iff],
  end  }
-- { contr := (φ₁₂ '' φ₀₁.C) ∪ φ₁₂.C ,
--   to_embedding := φ₀₁.to_embedding.trans φ₁₂.to_embedding, 
--   disj := begin
--     refine disjoint_iff_forall_ne.mpr _,
--     simp_rw [mem_range, embedding.trans_apply, coe_to_embedding], 
--     rintro x ⟨x₀,rfl⟩ y (⟨x₁,hx₁,rfl⟩ | hy) he,
--     { simp_rw [minor_embedding.inj] at he,
--       subst he, 
--       exact φ₀₁.not_mem_C _ hx₁}, 
--     subst he,  
--     exact φ₁₂.not_mem_C _ hy, 
--   end,
--   indep_iff' := 
--   begin
--     intro X,  
--     simp only [embedding.trans_apply, coe_to_embedding ], 
--     nth_rewrite 1 ←image_image,  
--     dsimp only, 
--     rw [←project_project, project_project_comm, ←φ₁₂.indep_project_iff, φ₀₁.indep_iff],
--   end }

@[simp] lemma trans_apply (φ₀₁ : M₀ →m M₁) (φ₁₂ : M₁ →m M₂) (x : E₀) : 
  (φ₀₁.trans φ₁₂) x = φ₁₂ (φ₀₁ x) := 
rfl   

@[simp] lemma trans_apply_image (φ₀₁ : M₀ →m M₁) (φ₁₂ : M₁ →m M₂) (X : set E₀) : 
  (φ₀₁.trans φ₁₂) '' X = φ₁₂ '' (φ₀₁ '' X) := 
by {ext, simp only [trans_apply, mem_image, exists_exists_and_eq_and]}

@[simp] lemma trans_apply_C (φ₀₁ : M₀ →m M₁) (φ₁₂ : M₁ →m M₂) : 
  (φ₀₁.trans φ₁₂).C = (φ₁₂ '' φ₀₁.C) ∪ φ₁₂.C := 
rfl 

@[simp] lemma trans_apply_D (φ₀₁ : M₀ →m M₁) (φ₁₂ : M₁ →m M₂) : 
  (φ₀₁.trans φ₁₂).D = (φ₁₂ '' φ₀₁.D) ∪ φ₁₂.D := 
rfl

@[simp] lemma trans_apply_ground (φ₀₁ : M₀ →m M₁) (φ₁₂ : M₁ →m M₂) : 
  (φ₀₁.trans φ₁₂).ground = φ₁₂ '' (φ₀₁.ground) := 
by {ext, simp [ground]}

/- A `minor_embedding` gives rise to a dual embedding -/
-- def dual (φ : M₀ →m M) : 
--   M₀.dual →m M.dual := 
-- { contr := φ.D,
--   del := φ.C,
--   disj := φ.disj.symm,
--   to_embedding := φ.to_embedding,
--   range_eq := by {rw [φ.range_eq, union_comm], refl},
--   indep_iff' := 
--   (begin
--     intro X, 
--     -- rw [dual_indep_iff], 
--     split, 
--     { --rintro ⟨B, hB, hBX⟩, 
--       -- obtain ⟨I,hI⟩ := M.dual.exists_basis φ.D, 
--       simp_rw [dual_indep_iff_coindep, coindep_iff_cl_compl_eq_univ], 
--       obtain ⟨I,hI⟩ := M.dual.exists_basis φ.D, 
--       rw [←hI.project_eq_project, hI.indep.project_indep_iff, dual_indep_iff_coindep, 
--         coindep_iff_cl_compl_eq_univ],  
--       refine λ hX, ⟨disjoint_of_subset (φ.image_subset_ground X) hI.subset φ.D_disjoint_ground.symm, 
--         _⟩,   
--       rw [←base_subset_iff_cl_eq_univ] at hX, 
--       have hIi := hI.indep, 
--       rw [dual_indep_iff_coindep, coindep_iff_cl_compl_eq_univ] at hIi, 
      
      
      
      
      
--       obtain ⟨Bd, hBd, hIBd⟩ := hI.indep, 
--       rw [dual_base_iff] at hBd, 
--       have hBi : M.indep (φ '' B), from indep_of_project_indep (φ.indep_iff.mp hB.indep),
      
--       have hss := (subset_union_right Bdᶜ (φ '' B)), 
--       -- have := subset_diff_of_
--       obtain ⟨B', hB', hBb'⟩ := hBi.subset_basis_of_subset (subset_union_right Bdᶜ _),  
--       refine ⟨B', _, disjoint_of_subset_left hBb'.subset _⟩, 
--       { rw [base_iff_basis_univ, ←hBd.cl],
--         convert hBb'.basis_cl using 1,
--         exact (M.cl_mono (subset_union_left _ _)).antisymm ((subset_univ _).trans_eq hBd.cl.symm)},
--       rw disjoint_union_right, 
      
--       -- obtain ⟨B', hB', hBB'⟩ :=   
--        }



/-- The scum theorem; every `minor_embedding`, has an equivalent embedding whose contract-set is 
  independent and whose delete-set is coindependent -/
theorem exists_indep_coindep_embedding (φ : M₀ →m M) : 
  ∃ (ψ : M₀ →m M), ψ.equiv φ ∧ M.indep ψ.C ∧ M.coindep φ.D := 
begin
  obtain ⟨C₀, ⟨ψ, hψφ, rfl⟩, hC₀min⟩ :=  
    finite.exists_minimal (λ (C : set E), ∃ e : M₀ →m M, e.equiv φ ∧ e.C = C) ⟨φ.C,φ,rfl,rfl⟩,  
  dsimp only at hC₀min, 

  -- TODO 

end 



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
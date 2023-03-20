import ..matroid 
import linear_algebra.finite_dimensional
import data.matrix.basic data.zmod.basic
import ..uniform
import .field_stuff

noncomputable theory 
open_locale classical 

open set 
open finite_dimensional
variables {α ρ R : Type*} [fintype α] [fintype ρ] {𝔽 : Type*} [field 𝔽] 

/- Linear map from vector in `𝔽^α` to a vector in `𝔽^X` given by forgetting all co-ordinates outside
`X`, where `(X : set α)` -/ 
def proj_to_set (𝔽 : Type*) [field 𝔽] (X : set α) := linear_map.fun_left 𝔽 𝔽 (coe : X → α)

@[simp] lemma proj_to_set_apply {X : set α} (v : α → 𝔽) (a : X):
  (proj_to_set 𝔽 X v) a = v (coe a) := 
rfl 

lemma proj_to_set_range_eq_top (𝔽 : Type*) [field 𝔽] (X : set α): 
  (proj_to_set 𝔽 X).range = ⊤ :=
begin
  ext, 
  simp only [submodule.mem_top, iff_true, linear_map.mem_range], 
  use λ a, dite (a ∈ X) (λ h, x ⟨a,h⟩) (λ _, 0), 
  ext a, 
  simp, 
end

/- Given a subspace of `𝔽^α`, projects it to a subspace of `𝔽^X` where `(X : set α)` by forgetting
all co-ordinates outside `X`-/
def submodule.proj_to_set (V : submodule 𝔽 (α → 𝔽)) (X : set α) := submodule.map (proj_to_set 𝔽 X) V 

/-def proj_to_univ_equiv (V : submodule 𝔽 (α → 𝔽)) :
  V.proj_to_set univ ≃ₗ[𝔽] V :=
{ to_fun := λ x, -- ⟨λ a, x.val ⟨a, mem_univ a⟩, by tidy⟩, 
    begin
      rw submodule.proj_to_set at x,
      have h2 := submodule.mem_map.1 x.2,
      cases h2 with y hy,
      apply x.2,
      sorry,
    end, 
  map_add' := by sorry,
  map_smul' := by sorry,
  inv_fun := λ x, --⟨λ u, x.1 u.1, by tidy⟩,
    begin
      -- have h2 := proj_to_set_apply V.2 x,
      sorry,
    end,
  left_inv := by sorry,
  right_inv := by sorry }-/

/- A subspace `R` of `𝔽^α` represents a matroid `M` on `α` if, for every `(X : set α)`, the rank of
`X` in `M` agrees with the dimension of the projection of `R` to the co-ordinates in `X`. -/
def is_subspace_rep {𝔽 : Type*} (h𝔽 : field 𝔽) (V : subspace 𝔽 ( α → 𝔽 )) (M : matroid α) := 
  ∀ X : set α, ( finrank 𝔽 (V.proj_to_set X) : ℕ) = M.r X 

/- A matroid is representable over `𝔽` if it has a (subspace) representation over `𝔽`. -/
def matroid.is_representable (M : matroid α) (𝔽 : Type*) [h𝔽 : field 𝔽] := 
  ∃ V, is_subspace_rep h𝔽 V M 

/- The set of rows of a `ρ × α` matrix. -/
def matrix.row_set (P : matrix ρ α R) : set (α → R) := 
  set.range (λ i, (λ a, P i a))

/- The row space of a `ρ × α` matrix over `𝔽`. -/
def matrix.row_space (P : matrix ρ α 𝔽) : submodule 𝔽 (α → 𝔽) :=   
  submodule.span 𝔽 P.row_set

/- A matrix represents `M` if its row space is a subspace representation of `M` -/
def is_matrix_rep (P : matrix ρ α 𝔽) (M : matroid α) := 
  is_subspace_rep _ P.row_space M 

/- A matroid is binary if it has a `GF(2)`-representation -/
def matroid.is_binary (M : matroid α) := 
  matroid.is_representable M (zmod 2)


/-lemma representable_iff_has_matrix_rep (M : matroid α) (𝔽 : Type*) [field 𝔽]:
  (M.is_representable 𝔽) ↔ ∃ (P : matrix (fin (M.r univ)) α 𝔽), is_matrix_rep P M :=
begin
  refine ⟨λ h, _, by {rintros ⟨P,hP⟩, exact ⟨P.row_space, hP⟩}⟩, 
  obtain ⟨R, hR⟩ := h, 
  obtain ⟨B, hB⟩ := finite_dimensional.fin_basis 𝔽 R, 
  have h_univ := hR univ, 
  suffices h_same : finrank 𝔽 ↥(submodule.proj_to_set R univ) = finrank 𝔽 R, 
  { exact ⟨λ i a, (B ⟨i.val, sorry⟩).val a, λ X, sorry⟩, },

  apply linear_equiv.findim_eq, 
  exact proj_to_univ_equiv _, 
end -/


lemma U23_binary : (canonical_unif 2 3).is_binary :=
begin
  unfold matroid.is_binary matroid.is_representable, 
  sorry,
end

lemma U24_nonbinary : ¬ (canonical_unif 2 4).is_binary :=
begin
  by_contra h2,
  cases h2 with V hV,
  have h1 := @num_subspaces_dim_one (zmod 2) V _ _ _ _ _ sorry _ sorry,
  simp at h1,
  have h3 := hV univ,
  rw canonical_unif_r at h3,
  rw ncard_univ at h3,
  simp at h3,
  
  sorry,
end

/-lemma U23_binary : (canonical_unif 2 3).is_binary :=
begin
  unfold matroid.is_binary matroid.is_representable, 
end-/



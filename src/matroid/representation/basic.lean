import ..dual
import linear_algebra.finite_dimensional
import data.matrix.basic data.zmod.basic
import ..uniform
import .field_stuff

noncomputable theory 
open_locale classical 

universes u v w z

open set 
open finite_dimensional
open submodule
variables {E ρ R : Type*} [finite E] [finite ρ] {𝔽 : Type*} [field 𝔽] 

section submodule_stuff 

variables {M : Type*} [semiring R] [add_comm_monoid M] 

/- Linear map from vector in `𝔽^E` to a vector in `𝔽^X` given by forgetting all co-ordinates outside
`X`, where `(X : set E)` -/ 
def proj_to_set (𝔽 : Type*) [field 𝔽] (X : set E) := linear_map.fun_left 𝔽 𝔽 (coe : X → E)

@[simp] lemma proj_to_set_apply {X : set E} (v : E → 𝔽) (a : X):
  (proj_to_set 𝔽 X v) a = v (coe a) := 
rfl 

lemma proj_to_set_range_eq_top (𝔽 : Type*) [field 𝔽] (X : set E): 
  (proj_to_set 𝔽 X).range = ⊤ :=
begin
  ext, 
  simp only [submodule.mem_top, iff_true, linear_map.mem_range], 
  use λ a, dite (a ∈ X) (λ h, x ⟨a,h⟩) (λ _, 0), 
  ext a, 
  simp, 
end

/- Given a subspace of `𝔽^E`, projects it to a subspace of `𝔽^X` where `(X : set E)` by forgetting
all co-ordinates outside `X`-/
def submodule.proj_to_set (V : submodule 𝔽 (E → 𝔽)) (X : set E) : submodule 𝔽 (X → 𝔽)
  := submodule.map (proj_to_set 𝔽 X) V 

/-- An equivalence  -/
def proj_to_univ_equiv (V : submodule 𝔽 (E → 𝔽)) :
   V ≃ₗ[𝔽] V.proj_to_set univ :=
(linear_equiv.fun_congr_left 𝔽 𝔽 (equiv.subtype_univ_equiv mem_univ)).submodule_map V

/- A subspace `R` of `𝔽^E` represents a matroid `M` on `α` if, for every `(X : set α)`, the rank of
`X` in `M` agrees with the dimension of the projection of `R` to the co-ordinates in `X`. -/
def is_subspace_rep (V : submodule 𝔽 ( E → 𝔽 )) (M : matroid E) := 
  ∀ X : set E, finrank 𝔽 (V.proj_to_set X) = M.r X 

/- A matroid is representable over `𝔽` if it has a (subspace) representation over `𝔽`. -/
def matroid.is_representable (M : matroid E) (𝔽 : Type*) [h𝔽 : field 𝔽] := 
  ∃ (V : submodule 𝔽 (E → 𝔽)), is_subspace_rep V M 

/- The set of rows of a `ρ × E` matrix. -/
def matrix.row_set (P : matrix ρ E R) : set (E → R) := 
  set.range (λ i, (λ a, P i a))

-- def matrix.row_set' (P : matroid ρ E R) : set ()

/- The row space of a `ρ × E` matrix over `𝔽`. -/
@[reducible] def matrix.row_space (P : matrix ρ E 𝔽) : submodule 𝔽 (E → 𝔽) :=   
  submodule.span 𝔽 P.row_set

/- A matrix represents `M` if its row space is a subspace representation of `M` -/
def is_matrix_rep (P : matrix ρ E 𝔽) (M : matroid E) := 
  is_subspace_rep P.row_space M 

/- A matroid is binary if it has a `GF(2)`-representation -/
def matroid.is_binary (M : matroid E) := 
  matroid.is_representable M (zmod 2)

lemma rank_of_rep {V : submodule 𝔽 (E → 𝔽)} {M : matroid E} (h : is_subspace_rep V M) :
  finrank 𝔽 V = M.rk :=
by rw [M.rk_def, ←h univ, (proj_to_univ_equiv V).finrank_eq]


lemma representable_iff_has_matrix_rep (M : matroid E) (𝔽 : Type*) [field 𝔽] {n : ℕ} 
(hn : n = M.rk) :
  (M.is_representable 𝔽) ↔ ∃ (P : matrix (fin n) E 𝔽), is_matrix_rep P M :=
begin
  refine ⟨λ h, _, by {rintros ⟨P,hP⟩, exact ⟨P.row_space, hP⟩}⟩, 
  obtain ⟨V,hV⟩ := h,  
  rw [←rank_of_rep hV] at hn, 
  set B := finite_dimensional.fin_basis_of_finrank_eq 𝔽 V hn.symm with hB,
  have h' := congr_arg (submodule.map V.subtype) B.span_eq,
  simp only [submodule.map_span, submodule.coe_subtype, map_subtype_top] at h', 
  use @matrix.of (fin n) E 𝔽 (λ i, (B i : E → 𝔽)), 
  rw [is_matrix_rep, matrix.row_space, matrix.row_set],  
  simp only [matrix.of_apply, ←h'], 
  convert hV, 
  convert h', 
  ext, 
  simp, 
end

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


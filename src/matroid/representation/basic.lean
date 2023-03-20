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
variables {E ρ R : Type*} [finite E] [finite ρ] {𝔽 : Type*} [field 𝔽] 



-- linear_map.fun_left : Π (R : Type u_1) (M : Type u_9) [_inst_1 : semiring R] [_inst_2 : add_comm_monoid M] [_inst_3 : module R M] {m : Type u_20} {n : Type u_21}, (m → n) → ((n → M) →ₗ[R] m → M)

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

/- A subspace `R` of `𝔽^α` represents a matroid `M` on `α` if, for every `(X : set α)`, the rank of
`X` in `M` agrees with the dimension of the projection of `R` to the co-ordinates in `X`. -/
def is_subspace_rep {𝔽 : Type*} (h𝔽 : field 𝔽) (V : subspace 𝔽 ( E → 𝔽 )) (M : matroid E) := 
  ∀ X : set E, ( finrank 𝔽 (V.proj_to_set X) : ℤ) = M.r X 

/- A matroid is representable over `𝔽` if it has a (subspace) representation over `𝔽`. -/
def matroid.is_representable (M : matroid E) (𝔽 : Type*) [h𝔽 : field 𝔽] := 
  ∃ V, is_subspace_rep h𝔽 V M 

/- The set of rows of a `ρ × E` matrix. -/
def matrix.row_set (P : matrix ρ E R) : set (E → R) := 
  set.range (λ i, (λ a, P i a))

/- The row space of a `ρ × E` matrix over `𝔽`. -/
def matrix.row_space (P : matrix ρ E 𝔽) : submodule 𝔽 (E → 𝔽) :=   
  submodule.span 𝔽 P.row_set

/- A matrix represents `M` if its row space is a subspace representation of `M` -/
def is_matrix_rep (P : matrix ρ E 𝔽) (M : matroid E) := 
  is_subspace_rep _ P.row_space M 

/- A matroid is binary if it has a `GF(2)`-representation -/
def matroid.is_binary (M : matroid E) := 
  matroid.is_representable M (zmod 2)


lemma representable_iff_has_matrix_rep (M : matroid E) (𝔽 : Type*) [field 𝔽]:
  (M.is_representable 𝔽) ↔ ∃ (P : matrix (fin (M.r univ)) E 𝔽), is_matrix_rep P M :=
begin
  refine ⟨λ h, _, by {rintros ⟨P,hP⟩, exact ⟨P.row_space, hP⟩}⟩, 
  obtain ⟨R, hR⟩ := h, 
  obtain ⟨B, hB⟩ := finite_dimensional.fin_basis 𝔽 R, 
  have h_univ := hR univ, 
  suffices h_same : finrank 𝔽 ↥(submodule.proj_to_set R univ) = finrank 𝔽 R, 
  { sorry }, --exact ⟨λ i a, (B ⟨i.val, sorry⟩).val a, λ X, sorry⟩, },

  /-apply linear_equiv.findim_eq, 
  exact proj_to_univ_equiv _, -/
  sorry,

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


import ..dual
import linear_algebra.finite_dimensional
import data.matrix.rank 
import data.matrix.basic
import data.zmod.basic
import ..constructions.basic
import .field_stuff

noncomputable theory 
open_locale classical
open_locale matrix  

universes u v w z

open set 
open finite_dimensional
open submodule
variables {E ρ R : Type*} [fintype E] [finite ρ] {𝔽 : Type*} [field 𝔽] 

section submodule_stuff 

variables {M : Type*} [semiring R] [add_comm_monoid M] 

/- Linear map from vector in `𝔽^E` to a vector in `𝔽^X` given by forgetting all co-ordinates outside
`X`, where `(X : set E)` -/ 
def proj_to_set (𝔽 : Type*) [field 𝔽] (X : set E) := linear_map.fun_left 𝔽 𝔽 (coe : X → E)

@[simp] lemma proj_to_set_apply {X : set E} (v : E → 𝔽) (a : X):
  (proj_to_set 𝔽 X v) a = v (coe a) := 
rfl 

#check proj_to_set

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

def submodule.proj_to_singleton (V : submodule 𝔽 (E → 𝔽)) (a : E) : submodule 𝔽 (({a} : set E) → 𝔽) 
  := V.proj_to_set {a}
-- want linear_map.apply

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

def matrix.column_set (P : matrix ρ E R) : set (ρ → R) := 
  matrix.row_set Pᵀ

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
  obtain ⟨R, hR⟩ := h, 
  obtain ⟨B, hB⟩ := finite_dimensional.fin_basis 𝔽 R, 
  have h_univ := hR univ, 
  suffices h_same : finrank 𝔽 ↥(submodule.proj_to_set R univ) = finrank 𝔽 R, 
  { sorry }, --exact ⟨λ i a, (B ⟨i.val, sorry⟩).val a, λ X, sorry⟩, },

  /-apply linear_equiv.findim_eq, 
  exact proj_to_univ_equiv _, -/
  sorry,

end

def matrix.col_submatrix (P : matrix ρ E 𝔽) (X : set E) : matrix ρ X 𝔽 := 
  matrix.submatrix P id coe 

lemma matrix_rep.apply {M : matroid E} {P : matrix ρ E 𝔽} (h : is_matrix_rep P M) (X : set E) : 
  M.r X = (P.col_submatrix X).rank := sorry 

-- show that if the submatrices for `{e}`, `{f}` have the same column space, then the 
-- submatrix for `{e,f}` has rank `1`, contradicting simplicity. 
--lemma col_space {M : matroid E} {P : matrix ρ E 𝔽} (h : is_matrix_rep P M) (e f : E) : 
-- span 𝔽 (range Mᵀ) is column space
variables [fintype ρ] [fintype E]
lemma submatrix_rank_one_of_span_eq_span {M : matroid E} {P : matrix ρ E 𝔽} (h : is_matrix_rep P M) 
(e f : E) (h_span : span 𝔽 (range (matrix.col_submatrix P {e})ᵀ) 
                    = span 𝔽 (range (matrix.col_submatrix P {f})ᵀ)) :
  (matrix.col_submatrix P {e, f}).rank = 1 :=
begin
  rw [matrix.rank], 
  -- have := matrix.transpose, 
  sorry,
end


variables (h𝔽 : field 𝔽) (V : submodule 𝔽 ( E → 𝔽 ))[fintype V]
variables [fintype {S : subspace 𝔽 V | finrank 𝔽 S = 1}]

--lemma simple_rep_inj 
-- define simple to mean every pair has rank 2
def simple (M : matroid E) : Prop := ∀ (e f : E), e ≠ f → M.r {e, f} = 2 

#check (λ x : E, submodule.proj_to_set V ({x} : set E))
#check submodule.proj_to_set V

def submodule.proj_to_set2 (x : E) := submodule.proj_to_set V ({x} : set E)

/-lemma inj_of_simple : simple M → is_subspace_rep h𝔽 V M → 
  function.injective (submodule.proj_to_set2) :=
begin
  sorry,
end

-- this is true for simple matroids
lemma card_subspaces_eq_ncard_univ :
  simple M → is_subspace_rep h𝔽 V M  → 
    (univ : set E).ncard ≤ fintype.card {S : subspace 𝔽 V | finrank 𝔽 S = 1} :=
begin
  intros hs hr,
  
  sorry,
end
--[_inst_3 : field K] [_inst_4 : add_comm_group V] [_inst_5 : module K V] [_inst_6 : fintype K] [_inst_7 : finite_dimensional K V] [_inst_8 : fintype ↥{S : submodule K V | finrank K ↥S = 1}] [_inst_9 : nontrivial K] [_inst_11 : nontrivial V], fintype.card ↥{S : subspace K V | finrank K ↥S = 1}

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
  have h4 : finrank (zmod 2) ↥V = 2,
  sorry,
  rw h4 at h1,
  have h5 := ncard_univ (fin 4),
  have h6 : univ.ncard ≤ fintype.card ↥{S : subspace (zmod 2) ↥V | finrank (zmod 2) ↥S = 1},
  
  sorry,
end-/

end submodule_stuff
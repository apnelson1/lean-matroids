import linear_algebra.linear_independent linear_algebra.basis
import data.zmod.basic
import ..constructions.basic
import ..dual
import .field_stuff
import ...mathlib.ncard

noncomputable theory
open_locale classical

variables {E 𝔽 ι : Type*} [field 𝔽] [fintype E] {M : matroid E}
-- why did we have finite E and not fintype E?

namespace matroid

/-- A matroid representation -/
structure rep (𝔽 : Type*) [field 𝔽] (M : matroid E) (ι : Type*):=
(to_fun : E → (ι → 𝔽))
(valid : ∀ (I : set E), linear_independent 𝔽 (λ (e : I), to_fun (e : E)) ↔ M.indep I)

instance : has_coe_to_fun (rep 𝔽 M ι) (λ _, E → (ι → 𝔽)) := ⟨λ φ, φ.to_fun⟩

/-- `M` is `𝔽`-representable if it has an `𝔽`-representation. -/
def is_representable (M : matroid E) (𝔽 : Type*) [field 𝔽] : Prop :=
  ∃ ι, nonempty (rep 𝔽 M ι)

lemma linear_independent_iff_coe (φ : rep 𝔽 M ι) {X : set E} :
  linear_independent 𝔽 (coe : (φ '' X) → (ι → 𝔽)) ↔ linear_independent 𝔽 (λ (e : X), φ (e : E)) :=
begin
  split,
  intros h,
  
  sorry,
  intros h,
  have h2 := linear_independent.image_of_comp X φ coe h,
  apply h2, 
end

lemma indep_of_local_inj (φ : rep 𝔽 M ι) {I : set E} (hI : M.indep I) : set.inj_on φ I := 
begin
  rw ← φ.valid at hI,
  intros x hx y hy hxy,
  by_contra hne,
  have hl : ¬ linear_independent 𝔽 (coe : (φ '' {x, y}) → (ι → 𝔽)),
  sorry,
  sorry,
end

lemma of_base (φ : rep 𝔽 M ι) {B : set E} (hB : M.base B) (e : E) : 
  φ e ∈ submodule.span 𝔽 (φ '' B) := 
begin
  by_cases e ∈ B,
  { have h2 := @submodule.subset_span 𝔽 _ _ _ _ (φ '' B),
    have h3 : φ e ∈ (φ '' B),
    apply (set.mem_image φ B (φ e)).2,
    use e,
    use h,
    have h4 := set.mem_of_subset_of_mem h2 h3,
    simp at h4,
    exact h4 },
  have h2 : ¬ linear_independent 𝔽 (λ (x : insert e B), φ.to_fun (x : E)),
  { rw rep.valid φ (insert e B),
    apply base.dep_of_insert hB h },
  by_contra h3,
  apply h2,
  rw linear_independent_insert' h,
  refine ⟨_, h3⟩,
  rw rep.valid,
  apply base.indep hB,
end 

/-lemma base_iff_basis (φ : rep 𝔽 M ι) {B : set E} :
  M.base B ↔ basis _ 𝔽 (submodule.span 𝔽 (φ '' set.univ)) :=
begin
  sorry,
end-/

lemma span_base (φ : rep 𝔽 M ι) (B : set E) (hB : M.base B) : (submodule.span 𝔽 (φ '' set.univ)) = submodule.span 𝔽 (φ '' B) :=
begin
  apply submodule.span_eq_span (λ x h, _) (λ x h, _),
  { rcases h with ⟨y, ⟨hy1, hy2⟩⟩,
    rw ← hy2,
    apply (of_base φ hB) },
  { rcases h with ⟨y, ⟨hy1, hy2⟩⟩,
    apply submodule.subset_span,
    simp only [set.mem_image, set.mem_univ, true_and],
    use ⟨y, hy2⟩ },
end

lemma of_rank (φ : rep 𝔽 M ι) [fintype 𝔽] [fintype (submodule.span 𝔽 (set.range φ))] : finite_dimensional.finrank 𝔽 (submodule.span 𝔽 (φ '' set.univ)) = M.rk :=
begin
  cases M.exists_base with B hB,
  -- need basis for this to work
  have h3 := finite_dimensional.fin_basis 𝔽 (submodule.span 𝔽 (set.range φ)),
  rw [span_base φ B hB, finrank_span_set_eq_card (φ '' B)],
  have h6 : (⇑φ '' B).to_finset.card = B.to_finset.card,
  { simp_rw set.to_finset_card,
    rw ← set.card_image_of_inj_on (indep_of_local_inj φ (base.indep hB)) }, 
  rw h6,
  simp only [← base.card hB, set.ncard_def, set.to_finset_card, nat.card_eq_fintype_card],
  have h8 : linear_independent 𝔽 (λ (x : B), φ.to_fun (x : E)),
  rw rep.valid,
  apply base.indep hB,
  apply linear_independent.image_of_comp B φ coe h8,
end


lemma foo (h : M.is_representable 𝔽) : 
  nonempty (rep 𝔽 M (fin M.rk))  := 
begin
  obtain ⟨ι, ⟨φ⟩⟩ := h,
  obtain ⟨B, hB⟩ := M.exists_base,
  have := of_base φ hB,
  sorry,
end

/- A matroid is binary if it has a `GF(2)`-representation -/
def matroid.is_binary (M : matroid E) :=
  matroid.is_representable M (zmod 2)

lemma U24_nonbinary : ¬ (canonical_unif 2 4).is_binary :=
begin
  by_contra h2,
  cases foo h2 with φ,
  rw [canonical_unif, unif_rk] at φ,
  { -- the two sorry's are for fintype instance on set of submodules & nontrivial submodule
    have h1 := @num_subspaces_dim_one (zmod 2) (submodule.span (zmod 2) (φ '' set.univ)) _ _ _ _ _ sorry _ sorry,
    simp at h1,
    
    have h4 : finite_dimensional.finrank (zmod 2) ↥(submodule.span (zmod 2) (⇑φ '' set.univ)) = 2,
    { rw finrank_span_set_eq_card,
      sorry },
    rw h4 at h1,
    have h5 := ncard_univ (fin 4),
    have h6 : univ.ncard ≤ fintype.card ↥{S : subspace (zmod 2) ↥V | finrank (zmod 2) ↥S = 1},
    sorry, },
  simp,
end


-- lemma foo (e f : E) (hne : e ≠ f) (h : M.r {e,f} = 1) :


end matroid



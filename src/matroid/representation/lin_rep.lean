import linear_algebra.linear_independent linear_algebra.basis
import data.zmod.basic
import ..constructions.basic
import ..dual ..simple
import .field_stuff
import ...mathlib.ncard

noncomputable theory
open_locale classical

variables {E 𝔽 ι : Type*} [field 𝔽] [fintype E] {M : matroid E} [nontrivial 𝔽]
-- we should have semiring 𝔽 by default, idk why it doesn't see it
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

-- want lemma that says if it's a simple matroid the cardinality of E
-- is leq that of the submodule

lemma non_zero_of_loopless (φ : rep 𝔽 M ι) (hl : loopless M) (x : E) : φ x ≠ 0 :=
begin
  have h2 := loopless_set.indep_of_mem hl (set.mem_univ x),
  rw ← φ.valid at h2,
  have h3 := linear_independent.image_of_comp {x} φ coe h2,
  --apply @linear_independent.ne_zero _ 𝔽 _,
  sorry,
end

lemma inj_of_simple (φ : rep 𝔽 M ι) (hs : simple M) : function.injective φ :=
begin
  intros x y hxy,
  have h := simple_set.pair_indep_of_mem hs (set.mem_univ x) (set.mem_univ y), 
  rw ← φ.valid at h,
  by_contra hxy2,
  rw ← set.mem_singleton_iff at hxy2,
  have h3 := (linear_independent_insert' hxy2).1 h,
  apply h3.2,
  simp,
  rw submodule.mem_span_singleton,
  use 1,
  simp only [one_smul],
  apply eq.symm hxy,
end

lemma simple_rep_subset_nonzero (φ : rep 𝔽 M ι) (hs : simple M) : φ '' set.univ ⊆ submodule.span 𝔽 (φ '' set.univ) \ {0} :=
begin
  intros x hx,
  rw set.mem_diff,
  split,
  have h2 := @submodule.subset_span 𝔽 _ _ _ _ (φ '' set.univ),
  apply set.mem_of_subset_of_mem h2 hx,
  simp,
  rcases hx with ⟨y, ⟨hy1, hy2⟩⟩,
  rw ← hy2, 
  apply non_zero_of_loopless φ (simple_set.loopless_set hs),
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

lemma of_rank_set (φ : rep 𝔽 M ι) [fintype 𝔽] (X : set E) [fintype (submodule.span 𝔽 (φ '' X))] : 
  finite_dimensional.finrank 𝔽 (submodule.span 𝔽 (φ '' X)) = M.r X :=
begin
  cases M.exists_basis X with I hI,
  have h3 := finite_dimensional.fin_basis 𝔽 (submodule.span 𝔽 (φ '' X)),
  
  sorry,
end

lemma non_zero_of_nonloop (φ : rep 𝔽 M ι) (x : E) (hx : M.nonloop x) : φ x ≠ (0 : ι → 𝔽) :=
begin
  have h2 := nonloop.r hx,
  by_contra h3,
  have h4 : finite_dimensional.finrank 𝔽 (submodule.span 𝔽 {φ x}) = 0,
  --rw finrank_eq_zero,
  --rw h3,
  sorry,
end

lemma rep_cl_eq_span_rep (φ : rep 𝔽 M ι) (X : set E): (φ '' M.cl X) = submodule.span 𝔽 (φ '' X) :=
begin
  ext;
  split,
  intros h,
  rcases h with ⟨y, ⟨hy1, hy2⟩⟩,
  by_cases y ∈ X, 
  rw ← hy2, 
  apply set.mem_of_subset_of_mem (submodule.subset_span),
  apply (set.mem_image φ X (φ y)).2,
  use y,
  refine ⟨h, rfl⟩,
  rw cl_def at hy1,
  --rw submodule.mem_span,
  sorry,
  sorry,
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

lemma U24_simple : (canonical_unif 2 4).simple :=
begin
  sorry,
end

-- this doesn't have sorry's but it relies on foo and U24_simple which do
lemma U24_nonbinary : ¬ (canonical_unif 2 4).is_binary :=
begin
  by_contra h2,
  cases foo h2 with φ,
  rw [canonical_unif, unif_rk] at φ,
  { have h8 := set.card_le_of_subset (simple_rep_subset_nonzero φ U24_simple),
    -- need basis
    have h9 := module.card_fintype (finite_dimensional.fin_basis (zmod 2) (submodule.span (zmod 2) (⇑φ '' set.univ))),
    rw [of_rank, unif_rk] at h9,
    { simp_rw [← set.to_finset_card, set.to_finset_diff] at h8,
      rw finset.card_sdiff at h8,
      { simp_rw set.to_finset_card at h8,
        simp only [fintype.card_of_finset, zmod.card, fintype.card_fin] at h9,
        simp only [set_like.coe_sort_coe, set.card_singleton] at h8,
        rw h9 at h8,
        have h11 : fintype.card ↥(⇑φ '' set.univ) = fintype.card (fin 4),
        rw set.card_image_of_injective set.univ (inj_of_simple φ U24_simple),
        tauto,
        -- linarith doesn't see the contradiction unless i simplify the inequality
        simp only [h11, fintype.card_fin, pow_two, two_mul, nat.succ_add_sub_one] at h8,
        linarith },
      -- this comes from finset.card_sdiff, will make nicer later
      simp only [set.to_finset_subset, set.coe_to_finset, set.singleton_subset_iff, 
        set_like.mem_coe, submodule.zero_mem] },
    -- this part comes from unif_rk needing 2 ≤ 4, will make nicer later
    simp only [nat.card_eq_fintype_card, fintype.card_fin, bit0_le_bit0, 
      nat.one_le_bit0_iff, nat.lt_one_iff]},
  simp,
end


-- lemma foo (e f : E) (hne : e ≠ f) (h : M.r {e,f} = 1) :


end matroid



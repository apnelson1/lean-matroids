import linear_algebra.finrank
import order.minimal 
import linear_algebra.linear_independent
import linear_algebra.span

universe u
variables {E 𝔽 ι : Type*}

def exchange_property (P : set E → Prop) : Prop :=
  ∀ X Y, P X → P Y → ∀ a ∈ X \ Y, ∃ b ∈ Y \ X, P (insert b (X \ {a}))

def exists_maximal_subset_property (P : set E → Prop) : Prop := 
  ∀ I X, P I → I ⊆ X → (maximals (⊆) {Y | P Y ∧ I ⊆ Y ∧ Y ⊆ X}).nonempty 

@[ext] structure matroid (E : Type*) :=
  (base : set E → Prop)
  (exists_base' : ∃ B, base B)
  (base_exchange' : exchange_property base)
  (maximality : exists_maximal_subset_property (λ I, ∃ B, base B ∧ I ⊆ B))

variables [field 𝔽] [fintype E] {M : matroid E} {I B : set E} {x : E}

namespace matroid

def indep (M : matroid E) (I : set E) : Prop :=
  ∃ B, M.base B ∧ I ⊆ B

/-- A `𝔽`-matroid representation is a map from the base of the matroid to `ι → 𝔽` such that a set -/
structure rep (𝔽 : Type*) [field 𝔽] (M : matroid E) (ι : Type*) :=
(to_fun : E → ι → 𝔽)
(valid' : ∀ I : set E, linear_independent 𝔽 (λ e : I, to_fun e) ↔ M.indep I)

namespace rep

-- take this as a sorry'd lemma, i don't want to import a bunch of stuff
lemma of_rank (φ : rep 𝔽 M ι) [fintype 𝔽] [fintype (span 𝔽 (set.range φ))] :
  finite_dimensional.finrank 𝔽 (span 𝔽 (range φ)) = M.rk :=
begin
  sorry,
end

end rep

lemma foo (φ : rep 𝔽 M ι) [fintype 𝔽] [fintype (span 𝔽 (set.range φ))] :
  nonempty (rep 𝔽 M (fin M.rk))  :=
begin
  have h1 := φ.of_rank,
  have h2 : finite_dimensional.finrank 𝔽 (fin M.rk → 𝔽) = M.rk, 
  simp,
  rw ← h2 at h1,
  rw ← finite_dimensional.nonempty_linear_equiv_iff_finrank_eq at h1,
  cases h1 with l,
  have h3 := λ (x : E), mem_of_subset_of_mem (@subset_span 𝔽 _ _ _ _ (range ⇑φ)) (mem_range_self x),
  use λ x, (l ⟨φ x, h3 x⟩),
  intros I,
  rw ← φ.valid,
  --refine ⟨λ h, _, λ h, _⟩,
  have h4 : linear_independent 𝔽 (λ (x : ↥I), φ x) ↔ linear_independent 𝔽 (λ (x : ↥I), (⟨φ x, h3 x⟩ : span 𝔽 (range ⇑φ))),
  refine ⟨λ h, _, λ h, _⟩,
  -- apply linear_independent_span,  
  -- i think this is what i want but it gives me a deterministic timeout...
 -- have h5 := (linear_map.linear_independent_iff ((span 𝔽 (range φ)).subtype) _).2 h,
  simp,
  --have h2 := linear_map.mem_submodule_image,
  --rw linear_map.linear_independent_iff l.to_linear_map,
  --convert linear_map.linear_independent_iff l.to_linear_map sorry using 1,
  --have h2 := gram_schmidt_linear_independent,
  sorry,
  sorry,
  --have h2 := @mem_range_self (ι → 𝔽) E φ x,
end
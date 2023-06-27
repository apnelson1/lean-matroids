import .restriction
import mathlib.data.set.basic 

noncomputable theory
open_locale classical
open_locale big_operators

open set

namespace matroid_in

variables {α : Type*} {M : matroid_in α} {I J B C X Y : set α} {e f x y : α}

/-- The notion of 2-connectedness for graphs can
    be extended to matroids. For each element `e`
    of a matroid `M`, let
    `gamma_set(e) = { e } ∪ { f : M has a circuit containing both e and f }`.  -/
def gamma_set (M : matroid_in α) (e : α) := { e } ∪ { f | ∃ C, M.circuit C ∧ e ∈ C ∧ f ∈ C }

/-- Define the relation `gamma` on `E` by `e gamma f` if and only if
    `e ∈ gamma f` -/
def gamma (M : matroid_in α) (e f : α) := e ∈ M.gamma_set f

/-- `gamma` is an equivalence relation on `E(M)` -/
theorem gamma_refl (M : matroid_in α) (e : α) : M.gamma e e :=
by { left, exact mem_singleton e }

theorem gamma_symm (h : M.gamma e f) : M.gamma f e :=
begin
  cases h with h,
  { rw mem_singleton_iff.mp h,
    exact M.gamma_refl f },
  { rcases h with ⟨C, hC, fC, eC⟩,
    right,
    use [C, hC, eC, fC] }
end

lemma gamma_exists_circuit_of_neq (h : M.gamma e f) (h' : e ≠ f) :
  ∃ C, M.circuit C ∧ e ∈ C ∧ f ∈ C  :=
begin
  cases h with h,
  { have := eq_of_mem_singleton h,
    contradiction, },
  { obtain ⟨C, hC, hfC, heC⟩ := h,
    use [C, hC, heC, hfC], }
end

theorem gamma_trans (e f g : α)
  (hef : M.gamma e f) (hfg : M.gamma f g) : M.gamma e g :=
begin
  have hfg := gamma_symm hfg,

  have nef : e ≠ f := sorry,
  have neg : e ≠ g := sorry,
  have nfg : g ≠ f := sorry,
  
  obtain ⟨C₁, hC₁⟩ := gamma_exists_circuit_of_neq hef nef,
  obtain ⟨C₂, hC₂⟩ := gamma_exists_circuit_of_neq hfg nfg,

  have h : (C₁ ∩ C₂).nonempty,
  {
    rw inter_nonempty,
    use f, use hC₁.2.2, use hC₂.2.2,
  },

  sorry
end

-- def direct_sum (M₁ : matroid_in α) (M₂ : matroid_in α) (hE : M₁.ground ∩ M₂.ground = ∅) :
--   matroid_in α :=
--    matroid_of_indep
--     (M₁.ground ∪ M₂.ground)
--     (λ I, ∃ I₁ I₂, M₁.indep I₁ ∧ M₂.indep I₂ ∧ I = I₁ ∪ I₂)
--     (by { use [∅, ∅, empty_indep _, empty_indep _], simp, })
--     (by {
--       sorry
--     })
--     (by {
--       rintro I X hI hI_not_max hX_max,
      
--     })
--     (sorry)
--     (by { sorry })



end matroid_in

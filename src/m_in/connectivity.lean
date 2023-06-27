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

def direct_sum' (M₁ : matroid_in α) (M₂ : matroid_in α)
  (hE : M₁.ground ∩ M₂.ground = ∅) :
  matroid_in α :=
   matroid_of_indep
    (M₁.ground ∪ M₂.ground)
    (λ I, ∃ I₁ I₂, M₁.indep I₁ ∧ M₂.indep I₂ ∧ I = I₁ ∪ I₂)
    (by { use [∅, ∅, empty_indep _, empty_indep _], simp, })
    (by {
      rintro I J ⟨J₁, J₂, ⟨hJ₁, hJ₂, Jeq⟩⟩ hIJ,
      use [I ∩ J₁, I ∩ J₂, hJ₁.subset (inter_subset_right I J₁),
        hJ₂.subset (inter_subset_right I J₂)],
      rw [←inter_distrib_left, ←Jeq],
      symmetry,
      exact inter_eq_self_of_subset_left hIJ,
    })
    (by {
      rintro I X ⟨I₁, I₂, hI₁, hI₂, Ieq⟩ hI_not_max ⟨⟨X₁, X₂, hX₁, hX₂, Xeq⟩, hX_max⟩,

      -- at least one of I₁, I₂ not maximal
      have hI : ¬ M₁.base I₁ ∨ ¬ M₂.base I₂,
      { sorry, },

      -- both X₁, X₂ maximal
      have hX₁base : M₁.base X₁,
      { sorry, },
      have hX₂base : M₂.base X₂,
      { sorry, },

      cases hI with hI,
      { obtain ⟨e, he, heI₁⟩ := hI₁.exists_insert_of_not_base hI hX₁base,
        use e,
        split,
        { split,
          { rw [Xeq, mem_union],
            left, use he.1 },
          { have : e ∉ I₁ := he.2,
            have : e ∉ I₂,
            { intro h,
              have : e ∈ M₁.E ∩ M₂.E := ⟨heI₁.subset_ground (mem_insert e I₁), hI₂.subset_ground h⟩,
              dsimp at hE,
              rw hE at this,
              exact not_mem_empty e this, },
            
            rw [Ieq, mem_union],
            intro g, cases g with g;
            contradiction } },
        { use [(insert e I₁), I₂, heI₁, hI₂],
          rw [Ieq, ←insert_union] } },
        { obtain ⟨e, he, heI₂⟩ := hI₂.exists_insert_of_not_base hI hX₂base,
          use e,
          split,
          { split,
            { rw [Xeq, mem_union],
              right, use he.1 },
            { have : e ∉ I₂ := he.2,
              have : e ∉ I₁,
              { intro h,
                have : e ∈ M₁.E ∩ M₂.E := ⟨hI₁.subset_ground h, heI₂.subset_ground (mem_insert e I₂)⟩,
                dsimp at hE,
                rw hE at this,
                exact not_mem_empty e this, },
              
              rw [Ieq, mem_union],
              intro g, cases g with g;
              contradiction } },
          { use [I₁, (insert e I₂), hI₁, heI₂],
            rw [Ieq, union_comm _ (insert _ _), insert_union, union_comm],
          } },
    })
    (by {
      rintro X,
    })
    (by {
      rintro I ⟨I₁, I₂, ⟨hI₁, hI₂, Ieq⟩⟩,
      dsimp,
      rw [Ieq, union_subset_iff],
      exact ⟨(hI₁.subset_ground).trans ((M₁.E).subset_union_left (M₂.E)),
             (hI₂.subset_ground).trans ((M₁.E).subset_union_right (M₂.E))⟩,
    })

end matroid_in

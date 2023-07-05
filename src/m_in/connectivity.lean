import .restriction
import mathlib.data.set.basic 
import function

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
sorry

def component (M : matroid_in α) (T : set α) :=
  ∀ t ∈ T, M.gamma_set t = T

/- this property is usually called 2-connected -/
def connected (M : matroid_in α) :=
  M.component M.ground

lemma connected_iff_exists_circuit (M : matroid_in α) :
  M.connected ↔ ∀ e f, ∃ C, M.circuit C ∧ e ∈ C ∧ f ∈ C :=
sorry

-- def direct_sum (M₁ : matroid_in α) (M₂ : matroid_in α) : matroid_in α :=
--   direct_sum' M₁ (M₂ ‖ (M₂.ground \ M₁.ground))
--   (by { simp only [ground_eq_E, restrict_ground_eq, inter_diff_self] })

lemma subset_eq_Union_inter_ground {ι : Type*} (I : set α) (Ms : ι → matroid_in α) (hI : I ⊆ (⋃ i, (Ms i).E)) :
  I = Union (λ i, I ∩ (Ms i).E) :=
sorry

lemma aux0 {ι : Type*}
  (Ms : ι → matroid_in α)
  (Is : ι → set α)
  (hIs : ∀ (i : ι), (Ms i).indep (Is i)) :
  ∀ i, Is i ⊆ (Ms i).E :=
sorry

lemma aux1 {ι : Type*}
  (Is : ι → set α) (Js : ι → set α) (hIsJs : Union Is ⊆ Union Js)
  (Ms : ι → matroid_in α) (hIs : ∀ i, Is i ⊆ (Ms i).E) (hJs : ∀ i, Js i ⊆ (Ms i).E)
  (hMs : univ.pairwise_disjoint (λ (i : ι), (Ms i).E)) : ∀ i, Is i ⊆ Js i :=
sorry


def direct_Sum' {ι : Type*} (Ms : ι → matroid_in α)
  (h : (univ : set ι).pairwise_disjoint (λ i , (Ms i).E)) : matroid_in α :=
  matroid_of_indep
  (⋃ i, (Ms i).E)
  (λ I, I ⊆ (⋃ i, (Ms i).E) ∧ ∀ i, (Ms i).indep (I ∩ (Ms i).E))
  ⟨empty_subset _, λ _, (by { rw empty_inter, exact empty_indep _ })⟩
  (λ I J ⟨h₁J, h₂J⟩ hIJ, ⟨hIJ.trans h₁J,
    λ i, (h₂J i).subset (((Ms i).E).inter_subset_inter_left hIJ)⟩)
  (begin -- augmentation
    rintro I B ⟨h₁I, h₂I⟩ hI hB,

    have hI' : ∃ i, ¬ (Ms i).base (I ∩ (Ms i).E) := sorry,
    have hB' : ∀ i,   (Ms i).base (B ∩ (Ms i).E) := sorry,

    obtain ⟨i, hi⟩ := hI',
    obtain ⟨e, ⟨he, he'⟩⟩ := (h₂I i).exists_insert_of_not_base hi (hB' i),

    refine ⟨e, ⟨⟨he.1.1, _⟩, ⟨_, λ j, _⟩⟩⟩,
    { have := he.2, dsimp at this, push_neg at this,
      exact λ g, (this g) (he'.subset_ground (mem_insert e (I ∩ (Ms i).E))), },
    { rw insert_subset, exact ⟨ (subset_Union (λ j, (Ms j).E) i)
              (he'.subset_ground (mem_insert e (I ∩ (Ms i).E))), h₁I⟩ },
    { by_cases hij : i = j,
      { subst hij, rw [insert_inter_distrib, insert_eq_of_mem he.1.2] at he',
        exact he' },
      { have h' : insert e I ∩ (Ms j).E = I ∩ (Ms j).E,
          { refine subset_antisymm _ _,
            { rintro f hf,
              refine ⟨_, hf.2⟩,
              cases eq_or_mem_of_mem_insert hf.1 with g g,
              { exfalso, subst g,
                exact hij (h.elim_set (mem_univ i) (mem_univ j) f (he.1.2) (hf.2)),
              },
              exact g, },
            { rintro f hf,
              refine ⟨_, hf.2⟩,
              rw mem_insert_iff,
              right, exact hf.1, } },
        rw h', exact h₂I j, } },
  end)
  (begin -- a maximal indep. set exists
    rintro X hX I ⟨h₁I, h₂I⟩ hIX,
    let Xs := λ i, X ∩ (Ms i).E,
    let Is := λ i, I ∩ (Ms i).E,
    have h' : ∀ i, ∃ B, (Ms i).basis B (Xs i) ∧ (Is i) ⊆ B :=
      sorry,
    choose! Bs hBs using h',

    refine ⟨Union Bs, ⟨⟨⟨λ e he, _, λ i, _⟩, ⟨_, _⟩⟩, _⟩⟩,
    { rw mem_Union at he |-,
      obtain ⟨i, hi⟩ := he,
      exact ⟨i, (hBs i).1.subset_ground_left hi⟩ },
    { have h' : ∀ i, Union Bs ∩ (Ms i).E = (Bs i) := sorry,
      simp_rw h', exact (hBs i).1.indep },
    { -- same arg as below
      have hI : I = Union Is := 
        subset_eq_Union_inter_ground I Ms h₁I,
      rw [hI, Union_subset_iff],
      rintro i,
      exact (hBs i).2.trans (subset_Union Bs i) },
    { rw Union_subset_iff,
      rintro i,
      exact (hBs i).1.subset.trans (inter_subset_left X (Ms i).E) },
    { rintro J ⟨⟨h₁J, h₂J⟩, ⟨hIJ, hJX⟩⟩ hBsJ,
      let Js := λ i, J ∩ (Ms i).E,
      have hJ : J = Union Js := 
        subset_eq_Union_inter_ground J Ms h₁J,
      rw [hJ, Union_subset_iff],
      rintro i,
      have hBs' : (Bs i) ⊆ (Js i),
        {
          rw Union_subset_iff at hBsJ,
          have := hBsJ i,
        },
      
      -- have hi : J ∩ (Ms i).E ⊆ (Bs i) := sorry,
      -- exact hi.trans (subset_Union Bs i)
    }
  end)
  (begin -- indep sets contained in ground set
    rintro I ⟨h₁I, h₂I⟩,
    let Is := λ i, I ∩ (Ms i).E, -- repeated again
    have hI : I = Union Is := sorry,
    rw [hI, Union_subset_iff],
    rintro i,
    have hi : I ∩ (Ms i).E ⊆ (Ms i).E :=
      inter_subset_right I (Ms i).E,
    exact hi.trans (subset_Union_of_subset i (by refl)),
  end)

end matroid_in

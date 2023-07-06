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

-- lemma pairwise_disjoint_of_subset_pairwise_disjoint {ι : Type*}
--   (Is Es : ι → set α) (hIs : ∀ i, Is i ⊆ Es i)
--   (hEs : univ.pairwise_disjoint Es) :
--   univ.pairwise_disjoint Is :=
-- sorry

lemma subsets_of_subsets_of_pairwise_disjoint {ι : Type*}
  (Is Js Es : ι → set α)
  (h : Union Is ⊆ Union Js)
  (hIs : ∀ i, Is i ⊆ Es i)
  (hJs : ∀ i, Js i ⊆ Es i)
  (hEs : univ.pairwise_disjoint Es) :
  ∀ i, Is i ⊆ Js i :=
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
      -- {
      --   by_contra' g,
      --   obtain ⟨i, h₁⟩ := g,
      --   obtain ⟨Q, hQ⟩ := (Ms i).exists_base,
      --   obtain ⟨e, he, he'⟩ := (hB.1.2 i).exists_insert_of_not_base h₁ hQ,
      --   let C := ( insert e (B ∩ (Ms i).E) ) ∪ (⋃ j ≠ i, B ∩ (Ms j).E),
      
      --   have : C ⊆ B,
      --     {
      --       refine hB.2 _ _,
      --       { refine ⟨_, λ k, _⟩,
      --         { rw union_subset_iff,
      --           refine ⟨_, λ e he, _⟩,
      --           { rw insert_eq,
      --             rw union_subset_iff,
      --             refine ⟨by { rw [singleton_subset_iff, mem_Union],
      --               exact ⟨i, hQ.subset_ground he.1⟩ },
      --               (inter_subset_right B (Ms i).E).trans (subset_Union _ i)⟩ },
      --           { rw mem_Union at he |-,
      --             simp only [ne.def, mem_Union, mem_inter_iff, exists_prop] at he,
      --             obtain ⟨j, ⟨_, _, ans⟩⟩ := he,
      --             exact ⟨j, ans⟩ } },
      --         { by_cases g : k = i,
      --           { subst g,
      --             have : C ∩ (Ms k).E = insert e (B ∩ (Ms k).E),
      --               { refine subset_antisymm _ _,
      --                 { rintro f hf,
      --                   cases hf.1 with q q,
      --                   { rw mem_insert_iff at q,
      --                     cases q with q q,
      --                     { subst q, exact mem_insert _ _ },
      --                     { rw mem_insert_iff, right, exact q } },
      --                   { rw mem_Union at q,
      --                     simp only [ne.def, mem_Union, mem_inter_iff, exists_prop] at q,
      --                     obtain ⟨_, ⟨_, hf', _⟩⟩ := q,
      --                     rw mem_insert_iff, right,
      --                     exact ⟨hf', hf.2⟩ } },
      --                 { rw [insert_eq, union_subset_iff],
      --                   refine ⟨_, subset_inter ((subset_insert _ _).trans (subset_union_left _ _))
      --                       (inter_subset_right B (Ms k).E)⟩,
      --                   { rw singleton_subset_iff,
      --                     refine ⟨(subset_union_left _ _) (mem_insert _ _),
      --                       hQ.subset_ground he.1⟩ } } },
      --             rw this, exact he' },
      --           {
      --             have : C ∩ (Ms k).E = B ∩ (Ms k).E,
      --             {
      --               refine subset_antisymm _ _,
      --               { rintro f hf,
      --                 refine ⟨_, hf.2⟩,
      --                 cases hf.1 with q q,
      --                 { rw mem_insert_iff at q,
      --                   cases q with t t,
      --                   { exfalso,
      --                     subst t,
      --                     have t : f ∈ (Ms k).E := hf.2,
      --                     have t' : f ∈ (Ms i).E := hQ.subset_ground he.1,
      --                     rw [pairwise_disjoint, set.pairwise] at h,
      --                     rw ←singleton_subset_iff at t t',
      --                     have := h (mem_univ k) (mem_univ i) g t t',
      --                     simp only [bot_eq_empty, le_eq_subset, singleton_subset_iff,
      --                       mem_empty_iff_false] at this,
      --                     exact this },
      --                   { exact t.1 } },
      --                 { simp only [mem_Union, ne.def, mem_Union, mem_inter_iff, exists_prop] at q,
      --                   obtain ⟨_, ⟨_, ans, _⟩⟩ := q,
      --                   exact ans } },
      --               {
                      
      --               }
      --             }
      --           }
      --         }
      --       }
      --     }

      -- },

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
          { -- question: likely possible to shorten / factor out
            refine subset_antisymm _ _,
            { rintro f hf,
              refine ⟨_, hf.2⟩,
              cases eq_or_mem_of_mem_insert hf.1 with g g,
              { exfalso, subst g,
                exact hij (h.elim_set (mem_univ i) (mem_univ j) f (he.1.2) (hf.2)), },
              exact g, },
            { rintro f hf,
              refine ⟨_, hf.2⟩,
              rw mem_insert_iff,
              right, exact hf.1, }
          }, -- end question
        rw h', exact h₂I j, } },
  end)
  (begin -- a maximal indep. set exists
    rintro X hX I ⟨h₁I, h₂I⟩ hIX,
    let Xs := λ i, X ∩ (Ms i).E,
    let Is := λ i, I ∩ (Ms i).E,

    have Xs_eq : Union Xs = X :=
      by { symmetry, exact subset_eq_Union_inter_ground _ _ hX },
    have Is_eq : Union Is = I :=
      by { symmetry, exact subset_eq_Union_inter_ground I Ms h₁I },

    have h' : ∀ i, ∃ B, (Ms i).basis B (Xs i) ∧ (Is i) ⊆ B,
      { rintro i,
        have : (Is i) ⊆ (Xs i),
          { have q : ∀ i, I ∩ (Ms i).E ⊆ (Ms i).E :=
              λ i, inter_subset_right I (Ms i).E,
            have q': ∀ i, X ∩ (Ms i).E ⊆ (Ms i).E :=
              λ i, inter_subset_right X (Ms i).E,
            rw [←Is_eq, ←Xs_eq] at hIX,
            exact aux1 Is Xs hIX Ms q q' h i, },
        exact (h₂I i).subset_basis_of_subset this (by simp), },
    choose! Bs hBs using h',

    refine ⟨Union Bs, ⟨⟨⟨λ e he, _, λ i, _⟩, ⟨_, _⟩⟩, _⟩⟩,
    { rw mem_Union at he |-,
      obtain ⟨i, hi⟩ := he,
      exact ⟨i, (hBs i).1.subset_ground_left hi⟩ },
    { have h' : ∀ i, Union Bs ∩ (Ms i).E = (Bs i),
        { -- question: likely possible to shorten and factor out
          rintro j,
          refine subset_antisymm _
            (subset_inter (subset_Union Bs j) ((hBs j).1.subset_ground_left)),
          { rintro e ⟨he₁, he₂⟩,
            rw [pairwise_disjoint, set.pairwise] at h,
            rw mem_Union at he₁,
            obtain ⟨k, hk⟩ := he₁,
            by_cases g : j = k,
            { subst g, exact hk },
            { exfalso,
              have g' := h (mem_univ j) (mem_univ k) g,
              have q := (hBs k).1.subset_ground_left hk,
              rw ←singleton_subset_iff at he₂ q,
              have := g' he₂ q,
              simp only [bot_eq_empty, le_eq_subset, singleton_subset_iff,
                mem_empty_iff_false] at this,
              exact this } }, }, -- end question
      simp_rw h', exact (hBs i).1.indep },
    { have hI : I = Union Is := 
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
      have hBs' : (Bs i) ⊆ (Js i) :=
        (subsets_of_subsets_of_pairwise_disjoint 
                      Bs Js (λ i, (Ms i).E)
                      hBsJ (λ i, (hBs i).1.subset_ground_left)
                      (λ i, inter_subset_right _ _) h) i,
      have hJs' : (Js i) ⊆ (Xs i),
        { -- question: likely possible to shorten and factor out
          rintro e he,
          rw hJ at hJX,
          have he' := (subset_Union Js i).trans hJX he,
          rw [←Xs_eq, mem_Union] at he',
          obtain ⟨k, hk⟩ := he',
          by_cases g : i = k,
          { subst g, exact hk },
          { exfalso,
            have q : { e } ⊆ (Ms k).E :=
              singleton_subset_iff.mpr hk.2,
            have q' : { e } ⊆ (Ms i).E :=
              singleton_subset_iff.mpr ((h₂J i).subset_ground he),
            rw [pairwise_disjoint, set.pairwise] at h,
            have := (h (mem_univ i) (mem_univ k) g) q' q,
            simp only [bot_eq_empty, le_eq_subset,
                singleton_subset_iff, mem_empty_iff_false] at this,
            exact this } }, -- end question
      exact (subset_antisymm_iff.mp ((hBs i).1.eq_of_subset_indep (h₂J i) hBs' hJs')).2.trans
          (subset_Union Bs i),
    }
  end)
  (begin -- indep sets contained in ground set
    rintro I ⟨h₁I, h₂I⟩,
    let Is := λ i, I ∩ (Ms i).E,
    have hI : I = Union Is :=
      subset_eq_Union_inter_ground I Ms h₁I,
    rw [hI, Union_subset_iff],
    rintro i,
    have hi : I ∩ (Ms i).E ⊆ (Ms i).E :=
      inter_subset_right I (Ms i).E,
    exact hi.trans (subset_Union_of_subset i (by refl)),
  end)

end matroid_in

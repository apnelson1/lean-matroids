import .restriction
import mathlib.data.set.basic 
-- import function

noncomputable theory
open_locale classical
open_locale big_operators

open set

namespace matroid_in

variables {α : Type*} {M : matroid_in α} {I J B C X Y : set α} {e f x y : α}

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

lemma subsets_of_subsets_of_pairwise_disjoint
  {ι : Type*}
  (Is Js Es : ι → set α)
  (h : Union Is ⊆ Union Js)
  (hIs : ∀ i, Is i ⊆ Es i)
  (hJs : ∀ i, Js i ⊆ Es i)
  (hEs : univ.pairwise_disjoint Es) :
  ∀ i, Is i ⊆ Js i :=
sorry

lemma not_mem_of_pairwise_disjoint
  {ι : Type*}
  {i j : ι}
  (e : α)
  (Es : ι → set α)
  (hEs : univ.pairwise_disjoint Es)
  (he : e ∈ Es i)
  (hij : i ≠ j)
  :
  e ∉ Es j :=
sorry

lemma empty_inter_of_nonmem_singleton
  (e : α)
  (S : set α)
  (he : e ∉ S) :
  { e } ∩ S = ∅ :=
sorry

def direct_Sum' {ι : Type*} (Ms : ι → matroid_in α)
  (hEs : (univ : set ι).pairwise_disjoint (λ i , (Ms i).E)) : matroid_in α :=
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
      { subst hij, rw [insert_inter_distrib, insert_eq_of_mem he.1.2] at he', exact he' },
      { have h' : insert e I ∩ (Ms j).E = I ∩ (Ms j).E,
        { refine subset_antisymm _ (inter_subset_inter_left (Ms j).E (subset_insert e I)),
          { simp only [singleton_union, subset_inter_iff, inter_subset_right, and_true],
            simp_rw [insert_eq, inter_distrib_right, union_subset_iff, inter_subset_left, and_true],
            rw empty_inter_of_nonmem_singleton _ _
                (not_mem_of_pairwise_disjoint e (λ k, (Ms k).E) hEs he.1.2 hij),
            exact empty_subset _ } },
        rw h', exact h₂I j, } },
  end)
  (begin -- a maximal indep. set exists
    rintro X hX I ⟨h₁I, h₂I⟩ hIX,

    let Xs := λ i, X ∩ (Ms i).E,
    let Is := λ i, I ∩ (Ms i).E,

-- lemma subsets_of_subsets_of_pairwise_disjoint
--   {ι : Type*}
--   (Is Js Es : ι → set α)
--   (h : Union Is ⊆ Union Js)
--   (hIs : ∀ i, Is i ⊆ Es i)
--   (hJs : ∀ i, Js i ⊆ Es i)
--   (hEs : univ.pairwise_disjoint Es) :
--   ∀ i, Is i ⊆ Js i :=
-- sorry

    have Xs_eq : Union Xs = X :=
      by { symmetry, exact subset_eq_Union_inter_ground _ _ hX },
    have Is_eq : Union Is = I :=
      by { symmetry, exact subset_eq_Union_inter_ground I Ms h₁I },
    rw [←Xs_eq, ←Is_eq] at hIX,

    have h' : ∀ i, ∃ B, (Ms i).basis B (Xs i) ∧ (Is i) ⊆ B,
      { have := subsets_of_subsets_of_pairwise_disjoint Is Xs (λ i, (Ms i).E) hIX
            (by simp only [inter_subset_right, implies_true_iff])
            (by simp only [inter_subset_right, implies_true_iff]) hEs,
        exact λ i, (h₂I i).subset_basis_of_subset (this i) (by simp only [inter_subset_right]) },
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

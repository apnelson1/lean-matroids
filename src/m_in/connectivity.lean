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

lemma inter_Union_of_subsets_of_pairwise_disjoint
  {ι : Type*}
  (Is Es : ι → set α)
  (hEs : univ.pairwise_disjoint Es)
  (hIs : ∀ i, Is i ⊆ Es i) :
  ∀ i, Union Is ∩ Es i = Is i :=
sorry

lemma not_subset_of_proper_subset (A B : set α) (h : A ⊂ B) :
  ¬ B ⊆ A :=
begin
  sorry
end

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
    have hB' : ∀ i,   (Ms i).base (B ∩ (Ms i).E),
      { by_contra' h, obtain ⟨i, hi⟩ := h,
        obtain ⟨Ti, hTi⟩ := (Ms i).exists_base,
        obtain ⟨e, he, heTi⟩ := (hB.1.2 i).exists_insert_of_not_base hi hTi,

        let T := insert e (⋃ j, B ∩ (Ms j).E),

        -- T is indep
        have hT : (T ⊆ ⋃ (i : ι), (Ms i).E) ∧ ∀ (i : ι), (Ms i).indep (T ∩ (Ms i).E),
          {
            refine ⟨_, _⟩,
            { -- question: how to rewrite using let expressions
              have : T = insert e (⋃ (j : ι), B ∩ (Ms j).E) := eq.refl T,
              rw this, clear this,
              -- end question
              rw [insert_eq, union_subset_iff, singleton_subset_iff],
              refine ⟨(subset_Union (λ i, (Ms i).E) i) (hTi.subset_ground he.1),
                Union_mono (λ i, inter_subset_right _ _)⟩ },
            {
              sorry
            }
          },
        
        have hBT : B ⊂ T,
          { rw ssubset_def,
            refine ⟨_, _⟩,
            { rw subset_eq_Union_inter_ground B Ms hB.1.1,
              exact subset_insert _ _ },
            { rw not_subset, have := he.2,
              rw [mem_inter_iff, not_and'] at this,
              exact ⟨e, mem_insert _ _, this (hTi.subset_ground he.1)⟩ } },

        exact (not_subset_of_proper_subset _ _ hBT) (hB.2 hT hBT.subset),
      },

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
        { refine λ j, subset_antisymm _
            (subset_inter (subset_Union Bs j) ((hBs j).1.subset_ground_left)),
          rw inter_Union_of_subsets_of_pairwise_disjoint Bs (λ i, (Ms i).E) hEs 
            (λ i, (hBs i).1.subset_ground_left) },
      simp_rw h', exact (hBs i).1.indep },
    { have hI : I = Union Is := 
        subset_eq_Union_inter_ground I Ms h₁I,
      rw [hI, Union_subset_iff],
      exact λ i, (hBs i).2.trans (subset_Union Bs i) },
    { rw Union_subset_iff,
      exact λ i, (hBs i).1.subset.trans (inter_subset_left X (Ms i).E) },
    { rintro J ⟨⟨h₁J, h₂J⟩, ⟨hIJ, hJX⟩⟩ hBsJs,
      let Js := λ i, J ∩ (Ms i).E,
      have Js_eq : J = Union Js := 
        subset_eq_Union_inter_ground J Ms h₁J,
      rw Js_eq at hBsJs hJX, rw [Js_eq, Union_subset_iff], rw ←Xs_eq at hJX,
      have hBs' : ∀ i, (Bs i) ⊆ (Js i) :=
        subsets_of_subsets_of_pairwise_disjoint Bs Js (λ i, (Ms i).E)
            hBsJs (λ i, (hBs i).1.subset_ground_left)
            (by simp only [inter_subset_right, implies_true_iff]) hEs,
      have hJs' : ∀ i, (Js i) ⊆ (Xs i) :=
        subsets_of_subsets_of_pairwise_disjoint Js Xs (λ i, (Ms i).E)
            hJX (by simp only [inter_subset_right, implies_true_iff])
            (by simp only [inter_subset_right, implies_true_iff]) hEs,
      have h₁ : ∀ i, J ∩ (Ms i).E = Js i :=
        by { simp only [eq_self_iff_true, implies_true_iff] },
      intro i,
      have := (hBs i).1.inter_eq_of_subset_indep (hBs' i) (h₂J i),
      rw inter_eq_left_iff_subset.mpr (hJs' i) at this, rw [h₁, this],
      exact subset_Union Bs i }
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

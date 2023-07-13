import .restriction
import mathlib.data.set.basic 
import .minor -- for deletion in direct_Sum

noncomputable theory
open_locale classical
open_locale big_operators

open set

namespace matroid_in

variables {α : Type*} {M : matroid_in α} {I J B C X Y : set α} {e f x y : α}

lemma subset_eq_Union_inter_ground {ι : Type*} (I : set α) (Ms : ι → matroid_in α)
  (hI : I ⊆ (⋃ i, (Ms i).E)) : I = Union (λ i, I ∩ (Ms i).E) :=
begin
  rw [←inter_Union, inter_eq_self_of_subset_left hI],
end

lemma not_mem_of_pairwise_disjoint
  {ι : Type*}
  {i j : ι}
  (e : α)
  (Es : ι → set α)
  (hEs : univ.pairwise_disjoint Es)
  (he : e ∈ Es i)
  (hij : i ≠ j) :
  e ∉ Es j :=
λ hej, hij (hEs.elim_set (mem_univ i) (mem_univ j) _ he hej)


lemma subsets_of_subsets_of_pairwise_disjoint
  {ι : Type*}
  (Is Js Es : ι → set α)
  (h : Union Is ⊆ Union Js)
  (hIs : ∀ i, Is i ⊆ Es i)
  (hJs : ∀ i, Js i ⊆ Es i)
  (hEs : univ.pairwise_disjoint Es) (i : ι) :
  Is i ⊆ Js i :=
begin
  rw [Union_subset_iff] at h,
  refine (subset_inter (hIs i) (h i)).trans _,
  rw [inter_Union, Union_subset_iff],
  refine λ j, (eq_or_ne i j).elim (by {rintro rfl, apply inter_subset_right}) (λ hne, _),
  rw [disjoint_iff_inter_eq_empty.mp],
  { exact empty_subset _},
  exact disjoint_of_subset_right (hJs j) (hEs (mem_univ i) (mem_univ j) hne),
end

lemma inter_Union_of_subsets_of_pairwise_disjoint
  {ι : Type*}
  (Is Es : ι → set α)
  (hEs : univ.pairwise_disjoint Es)
  (hIs : ∀ i, Is i ⊆ Es i) (i : ι) :
  Union Is ∩ Es i = Is i :=
begin
  rw [Union_inter, ←bUnion_univ],
  convert bUnion_insert i (univ \ {i}) (λ j, Is j ∩ Es i) using 1, 
  { rw [insert_diff_singleton, ←union_singleton, univ_union]  },  
  { rw [inter_eq_self_of_subset_left (hIs i), 
    Union₂_congr (_ : ∀ (x : ι) (H : x ∈ univ \ {i}), Is x ∩ Es i = ∅)],
    simp_rw [Union_empty, union_empty, ←disjoint_iff_inter_eq_empty],
    refine λ j hij, disjoint_of_subset_left (hIs j) (hEs (mem_univ j) (mem_univ i)
      (by { have := hij.2, rw mem_singleton_iff at this, exact this })) },
end

def direct_Sum' {ι : Type*} (Ms : ι → matroid_in α)
  (hEs : (univ : set ι).pairwise_disjoint (λ i, (Ms i).E)) : matroid_in α :=
  matroid_of_indep
  (⋃ i, (Ms i).E)
  (λ I, I ⊆ (⋃ i, (Ms i).E) ∧ ∀ i, (Ms i).indep (I ∩ (Ms i).E))
  ⟨empty_subset _, λ _, (by { rw empty_inter, exact empty_indep _ })⟩
  (λ I J ⟨h₁J, h₂J⟩ hIJ, ⟨hIJ.trans h₁J,
    λ i, (h₂J i).subset (((Ms i).E).inter_subset_inter_left hIJ)⟩)
  (begin -- augmentation
    rintro I B ⟨h₁I, h₂I⟩ hI hB,

    have hI' : ∃ i, ¬ (Ms i).base (I ∩ (Ms i).E),
      { by_contra' h, apply hI,
        refine ⟨⟨h₁I, h₂I⟩, _⟩,
        { rintro J ⟨h₁J, h₂J⟩ hIJ,
          rw [subset_eq_Union_inter_ground I Ms h₁I, subset_eq_Union_inter_ground J Ms h₁J] at hIJ,
          have hIsJs : ∀ i, I ∩ (Ms i).E ⊆ J ∩ (Ms i).E :=
            subsets_of_subsets_of_pairwise_disjoint
              (λ i, I ∩ (Ms i).E) (λ i, J ∩ (Ms i).E) (λ i, (Ms i).E)
              hIJ (by simp only [inter_subset_right, implies_true_iff])
              (by simp only [inter_subset_right, implies_true_iff]) hEs,
          rw [subset_eq_Union_inter_ground I Ms h₁I,
              subset_eq_Union_inter_ground J Ms h₁J],
          exact Union_mono
            (λ i, superset_of_eq ((h i).eq_of_subset_indep (h₂J i) (hIsJs i))),
        } },

    have hB' : ∀ i,   (Ms i).base (B ∩ (Ms i).E),
      { by_contra' h, obtain ⟨i, hi⟩ := h,
        obtain ⟨Ti, hTi⟩ := (Ms i).exists_base,
        obtain ⟨e, he, heTi⟩ := (hB.1.2 i).exists_insert_of_not_base hi hTi,

        let T := insert e (⋃ j, B ∩ (Ms j).E),

        -- T is indep
        have hT : (T ⊆ ⋃ (i : ι), (Ms i).E) ∧ ∀ (i : ι), (Ms i).indep (T ∩ (Ms i).E),
          { refine ⟨_, λ j, _⟩,
            { -- question: how to rewrite using let expressions
              have : T = insert e (⋃ (j : ι), B ∩ (Ms j).E) := eq.refl T,
              rw this, clear this,
              -- end question
              rw [insert_eq, union_subset_iff, singleton_subset_iff],
              exact ⟨(subset_Union (λ i, (Ms i).E) i) (hTi.subset_ground he.1),
                Union_mono (λ i, inter_subset_right _ _)⟩ },
            { by_cases hji : j = i,
              { subst hji, have h : T ∩ (Ms j).E = insert e (B ∩ (Ms j).E),
                  { refine subset_antisymm _ _,
                    { rintro f ⟨hf₁, hf₂⟩,
                      cases eq_or_mem_of_mem_insert hf₁ with g g,
                      { rw g, exact mem_insert e _ },
                      { rw mem_Union at g, obtain ⟨i, hi⟩ := g,
                        exact (subset_insert _ _) ⟨hi.1, hf₂⟩ } },
                    { rintro f hf,
                      cases eq_or_mem_of_mem_insert hf with g g,
                      { rw g, exact ⟨mem_insert _ _, hTi.subset_ground he.1⟩ },
                      { exact ⟨(subset_insert _ _) ((subset_Union _ j) g), g.2⟩ } } },
                rw h, exact heTi },
              { have h : T ∩ (Ms j).E = B ∩ (Ms j).E,
                  { refine subset_antisymm _ _,
                    { -- question: lambda expression
                      rintro f ⟨hf₁, hf₂⟩, refine ⟨_, hf₂⟩,
                      cases eq_or_mem_of_mem_insert hf₁ with g g,
                      { exfalso, subst g,
                        exact (not_mem_of_pairwise_disjoint
                            f (λ i, (Ms i).E) hEs hf₂ hji) (hTi.subset_ground he.1) },
                      { rw mem_Union at g, obtain ⟨k, hk⟩ := g, exact hk.1 } },
                    { exact λ f hf, ⟨(subset_Union _ j).trans (subset_insert _ _) hf, hf.2⟩ } },
                rw h, exact hB.1.2 j
              } } },
        
        have hBT : B ⊂ T,
          { rw ssubset_def,
            refine ⟨_, _⟩,
            { rw subset_eq_Union_inter_ground B Ms hB.1.1,
              exact subset_insert _ _ },
            { rw not_subset, have := he.2,
              rw [mem_inter_iff, not_and'] at this,
              exact ⟨e, mem_insert _ _, this (hTi.subset_ground he.1)⟩ } },

        exact hBT.2 (hB.2 hT hBT.subset),
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
            have : {e} ∩ (Ms j).E = ∅, -- question: better style
              { refine subset_antisymm _ (empty_subset _),
                rintro f ⟨hf₁, hf₂⟩, rw mem_singleton_iff at hf₁,
                have := (not_mem_of_pairwise_disjoint e (λ k, (Ms k).E) hEs he.1.2 hij),
                subst hf₁, contradiction },
            rw this, exact empty_subset _
          } },
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

-- add new matroid to Ms, the loopy matroid on
--    `⋂ i, (Ms i).E`
def direct_Sum {ι : Type*} (Ms : ι → matroid_in α) (k : ι) : matroid_in α :=
direct_Sum' (λ i, if i = k then Ms i else (Ms i) ⟍ (⋃ j ≠ i, (Ms j).E))
(begin
  rw [pairwise_disjoint, set.pairwise],
  rintro i hi j hj hij,
  simp only [ne.def, delete_ground, function.on_fun_apply, disjoint_iff],
  refine subset_antisymm _ (empty_subset _),
  rintro e ⟨⟨hei₁, hei₂⟩, ⟨hej₁, hej₂⟩⟩,
  rw mem_Union at hei₂,
  have : ∃ k, e ∈ ⋃ (x : k ≠ i), (Ms k).E,
    { refine ⟨j, _⟩, rw mem_Union,
      exact ⟨by { symmetry, exact hij }, hej₁⟩ },
  contradiction
end)

lemma direct_Sum_indep_iff {ι : Type*}
  (Ms : ι → matroid_in α) (hEs : (univ : set ι).pairwise_disjoint (λ i, (Ms i).E)) (I : set α) :
  (direct_Sum' Ms hEs).indep I ↔ (I ⊆ Union (λ i, (Ms i).E)) ∧
    (∀ i, (Ms i).indep (I ∩ (Ms i).E)) :=
by { rw [direct_Sum', matroid_of_indep_apply] }

@[simp] lemma direct_Sum_ground {ι : Type*}
  (Ms : ι → matroid_in α) (hEs : (univ : set ι).pairwise_disjoint (λ i, (Ms i).E)) :
  (direct_Sum' Ms hEs).E = Union (λ i, (Ms i).E) :=
begin
  sorry
end

@[simp] lemma direct_Sum_dep {ι : Type*}
  (Ms : ι → matroid_in α) (hEs : (univ : set ι).pairwise_disjoint (λ i, (Ms i).E)) (I : set α) :
  (direct_Sum' Ms hEs).dep I ↔ (I ⊆ Union (λ i, (Ms i).E)) ∧ ∃ i, (Ms i).dep (I ∩ (Ms i).E) :=
begin
  simp_rw [dep_iff, direct_Sum_ground, direct_Sum_indep_iff, not_and,
    (inter_subset_right _ _), and_true, not_forall],
  exact ⟨λ ⟨h₁, h₂⟩, ⟨h₂, h₁ h₂⟩, λ ⟨h₁, h₂⟩, ⟨λ _, h₂, h₁⟩⟩
end

lemma direct_Sum_indep_of_subset_iff {ι : Type*}
  (Ms : ι → matroid_in α) (hEs : (univ : set ι).pairwise_disjoint (λ i, (Ms i).E))
  (I : set α) (i : ι) (hI : I ⊆ (Ms i).E) :
  (direct_Sum' Ms hEs).indep I ↔ (Ms i).indep I :=
begin
  rw direct_Sum_indep_iff,
  exact ⟨λ ⟨_, h⟩, by { rw ←inter_eq_self_of_subset_left hI, exact h i },
    λ h, ⟨hI.trans (subset_Union (λ i, (Ms i).E) i), λ j, (eq_or_ne i j).elim
      (λ hij, by { rw [←hij, inter_eq_self_of_subset_left hI], exact h })
      (λ hij, by { rw disjoint_iff_inter_eq_empty.mp
        (disjoint.mono_left hI (hEs (mem_univ i) (mem_univ j) hij)), exact empty_indep _ })⟩⟩,
end

lemma direct_Sum_circuit_iff {ι : Type*}
  (Ms : ι → matroid_in α) (hEs : (univ : set ι).pairwise_disjoint (λ i, (Ms i).E)) (I : set α) :
  (direct_Sum' Ms hEs).circuit I ↔ ∃ i, (Ms i).circuit I :=
begin
  simp_rw circuit_iff_forall_ssubset,
  refine ⟨_, _⟩,
  { intro hI,
    have : ∃ i, I ⊆ (Ms i).E,
      { by_contra' h,
        have hIs : ∀ i, (Ms i).indep (I ∩ (Ms i).E),
          { intro i,
            have : I ∩ (Ms i).E ⊂ I,  
              { rw ssubset_def,
                refine ⟨by simp_rw [inter_subset_left], _⟩,
                rw [subset_inter_iff, not_and_distrib],
                right, exact h i },
            rwa ←direct_Sum_indep_of_subset_iff Ms hEs
              (I ∩ (Ms i).E) i (by simp_rw [inter_subset_right]),
            exact hI.2 (I ∩ (Ms i).E) this },
        exact hI.1.not_indep ((direct_Sum_indep_iff Ms hEs I).mpr ⟨hI.1.subset_ground, hIs⟩) },
    obtain ⟨i, hi⟩ := this,
    exact ⟨i,
      ⟨(not_iff_not_of_iff (direct_Sum_indep_of_subset_iff Ms hEs I i hi)).mp (hI.1.not_indep), hi⟩,
      λ J hJ, (direct_Sum_indep_of_subset_iff Ms hEs J i (hJ.subset.trans hi)).mp (hI.2 J hJ)⟩ },
  { rintro ⟨i, hi⟩,
    refine ⟨_, λ J hJI,
      (direct_Sum_indep_of_subset_iff Ms hEs J i (hi.2 J hJI).subset_ground).mpr (hi.2 J hJI)⟩,
    rw direct_Sum_dep,
    refine ⟨(hi.1.subset_ground).trans (subset_Union (λ (i : ι), (Ms i).E) i), i, _⟩,
    rw inter_eq_self_of_subset_left hi.1.subset_ground,
    exact hi.1 }
end

lemma maximal_union_iff {ι : Type*}
  (Is : ι → set α)
  (h_global : set α → Prop)
  (h_local  : ι → set α → Prop)
  (h : h_global (Union Is) ↔ ∀ i, h_local i (Is i)) :
  (Union Is) ∈ maximals (⊆) { X | h_global X } ↔
    ∀ i, (Is i) ∈ maximals (⊆) { X | ∀ i, h_local i X } :=
begin
  sorry
end

lemma direct_Sum_base_iff {ι : Type*}
  (Ms : ι → matroid_in α)
  (hEs : (univ : set ι).pairwise_disjoint (λ i, (Ms i).E))
  (Is : ι → set α) :
  (direct_Sum' Ms hEs).base (Union Is) ↔ ∀ i, (Ms i).base (Is i) :=
begin
  simp_rw base_iff_mem_maximals,
  -- let h_global := λ S, (direct_Sum' Ms hEs).indep S,
  -- let h_local  := λ i S, (Ms i).indep S,
  -- have h : h_global (Union Is) ↔ ∀ i, h_local i (Is i),
  --   sorry,
  -- rw maximal_union_iff Is h_global h_local h,

  rw maximal_union_iff Is (λ S, (direct_Sum' Ms hEs).indep S) (λ i S, (Ms i).indep S) sorry,
  simp,
  
end

lemma direct_Sum_basis_iff {ι : Type*}
  (Ms : ι → matroid_in α) (hEs : (univ : set ι).pairwise_disjoint (λ i, (Ms i).E))
  (B : set α) (hB : B ⊆ Union (λ i, (Ms i).E)) (X : set α) (hX : X ⊆ Union (λ i, (Ms i).E)) :
  (direct_Sum' Ms hEs).basis B X ↔
    ∀ i, (Ms i).basis (B ∩ (Ms i).E) (X ∩ (Ms i).E) :=
begin
  sorry
end
-- ⟨λ h, ((direct_Sum_basis_iff' Ms hEs B X).mp h).2.2,
--  λ h, ((direct_Sum_basis_iff' Ms hEs B X).mpr ⟨hB, hX, h⟩)⟩
-- `hB` and `hX` only needed for reverse direction

-- lemma direct_Sum_basis_iff' {ι : Type*}
--   (Ms : ι → matroid_in α) (hEs : (univ : set ι).pairwise_disjoint (λ i, (Ms i).E))
--   (B : set α) (X : set α) :
--   (direct_Sum' Ms hEs).basis B X ↔
--     B ⊆ Union (λ i, (Ms i).E) ∧
--     X ⊆ Union (λ i, (Ms i).E) ∧
--     ∀ i, (Ms i).basis (B ∩ (Ms i).E) (X ∩ (Ms i).E) :=
-- begin
--   sorry
-- end

-- translating skewness from `matroid/connectivity.lean`

def skew (M : matroid_in α) (X Y : set α) : Prop := (M ⟋ X) ‖ Y = M ‖ Y 

lemma skew_iff_project_lrestr_eq_lrestr : M.skew X Y ↔ (M ⟋ X) ‖ Y = M ‖ Y := iff.rfl 

lemma skew.project_lrestr_eq (h : M.skew X Y) : (M ⟋ X) ‖ Y = M ‖ Y := h 

lemma skew.symm (h : M.skew X Y) : M.skew Y X :=
begin
  sorry
  -- needs pseudominor
end 

end matroid_in

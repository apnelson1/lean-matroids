import .circuit
import mathlib.data.set.basic 
import mathlib.finsum_ncard

noncomputable theory
open_locale classical
open_locale big_operators

variables {α : Type*} {M : matroid_in α} {I B C X Y Z K F F₀ F₁ F₂ H H₁ H₂ : set α}
          { e f x y z : α }

open set 

namespace matroid_in

lemma flat_def : M.flat F ↔ ((∀ I X, M.basis I F → M.basis I X → X ⊆ F) ∧ F ⊆ M.E) := iff.rfl
/- added `∧ F ⊆ M.E` to RHS.
   Here it is the last clause as in the definition, but 
   in closure.lean I wrote similar assumptions
   as the first clause. -/

@[ssE_finish_rules] lemma flat.subset_ground (hF : M.flat F) : F ⊆ M.E :=
hF.2

lemma flat.eq_ground_of_spanning (hF : M.flat F) (h : M.spanning F) : F = M.E := 
by rw [←hF.cl, h.cl]

lemma flat.spanning_iff (hF : M.flat F) : M.spanning F ↔ F = M.E := 
⟨hF.eq_ground_of_spanning, by { rintro rfl, exact M.ground_spanning }⟩

lemma flat.Inter {ι : Type*} [hι : nonempty ι] (F : ι → set α) (hF : ∀ i, M.flat (F i)) :
  M.flat (⋂ i, F i) :=
begin
  split,
  { refine λ I X hI hIX, subset_Inter (λ i, _),
    obtain ⟨J, hIJ, hJ⟩ := hI.indep.subset_basis_of_subset
      ((hI.subset.trans (Inter_subset _ _ ) : I ⊆ F i)),

    have hF' := hF i, rw flat_def at hF',
    refine (union_subset_iff.mp (hF'.1 _ (F i ∪ X) hIJ _)).2, 
    rw [←union_eq_left_iff_subset.mpr hIJ.subset, union_assoc],
    exact hIJ.basis_union (hIX.basis_union_of_subset hIJ.indep hJ), },
  intros e he, obtain i₀ := hι.some,
  rw mem_Inter at he,
  exact (flat.subset_ground (hF i₀)) (he i₀),
end
/- added the assumption `nonempty ι` -/

lemma flat_of_cl (M : matroid_in α) (X : set α) : M.flat (M.cl X) :=
begin
  rw [M.cl_def X, sInter_eq_Inter],
  apply flat.Inter _,
  { rintro ⟨F,hF⟩, exact hF.1 },
  use [M.E, M.ground_flat, inter_subset_right _ _],
end
 
lemma flat_iff_cl_self : M.flat F ↔ M.cl F = F :=
begin
  refine ⟨λ h, subset_antisymm (sInter_subset_of_mem ⟨h, inter_subset_left F M.E⟩)
    (M.subset_cl F (flat.subset_ground h)),
    λ h, by { rw ← h, exact flat_of_cl _ _ }⟩
end

lemma flat.inter (hF₁ : M.flat F₁) (hF₂ : M.flat F₂) : M.flat (F₁ ∩ F₂) :=
by { rw inter_eq_Inter, refine flat.Inter _ (λ i, _), cases i; assumption }

lemma flat_iff_ssubset_cl_insert_forall (hF : F ⊆ M.E . ssE) :
  M.flat F ↔ ∀ e ∈ M.E \ F, M.cl F ⊂ M.cl (insert e F) :=
begin
  refine ⟨λ h e he, (M.cl_subset (subset_insert _ _)).ssubset_of_ne _, λ h, _⟩,
  { rw [h.cl],
    refine λ h', mt ((set.ext_iff.mp h') e).mpr (not_mem_of_mem_diff he)
                    ((M.subset_cl _ _) (mem_insert _ _)),
    rw insert_eq,
    refine union_subset _ hF,
    rw singleton_subset_iff, exact he.1
  },
  rw flat_iff_cl_self,
  by_contra h',
  obtain ⟨e,he',heF⟩ := exists_of_ssubset (ssubset_of_ne_of_subset (ne.symm h') (M.subset_cl F)),
  have h'' := h e ⟨(M.cl_subset_ground F) he', heF⟩,
  rw [←(M.cl_insert_cl_eq_cl_insert e F), insert_eq_of_mem he', M.cl_cl] at h'',
  exact h''.ne rfl
end

lemma flat_iff_forall_circuit {F : set α} (hF : F ⊆ M.E . ssE) :
  M.flat F ↔ ∀ C e, M.circuit C → e ∈ C → C ⊆ insert e F → e ∈ F :=
begin
  rw [flat_iff_cl_self],
  refine ⟨λ h C e hC heC hCF , _,
          λ h, _⟩,
  { rw ←h, 
    refine (M.cl_subset _) (hC.subset_cl_diff_singleton e heC), 
    rwa [diff_subset_iff, singleton_union] },

  refine subset_antisymm (λ e heF, by_contra (λ he', _ )) (M.subset_cl F hF),
  obtain ⟨C, hC, heC, hCF⟩ := (mem_cl_iff_exists_circuit_of_not_mem he').mp heF,
  exact he' (h C e hC heC hCF),
end
/- hypothesis: added hF -/

lemma flat_iff_forall_circuit' {F : set α} :
  M.flat F ↔ (∀ C e, M.circuit C → e ∈ C → C ⊆ insert e F → e ∈ F) ∧ F ⊆ M.E :=
begin
  refine ⟨λ h, ⟨(flat_iff_forall_circuit h.subset_ground).mp h, h.subset_ground⟩,
          λ h, (flat_iff_forall_circuit h.2).mpr h.1⟩,
end
/- hypothesis: only added hF to RHS -/


lemma flat.cl_exchange (hF : M.flat F) (he : e ∈ M.cl (insert f F) \ F) :
  f ∈ M.cl (insert e F) \ F :=
by {nth_rewrite 1 ←hF.cl, apply cl_exchange, rwa hF.cl}

lemma flat.cl_insert_eq_cl_insert_of_mem (hF : M.flat F) (he : e ∈ M.cl (insert f F) \ F) : 
  M.cl (insert e F) = M.cl (insert f F) :=
by { have := hF.subset_ground, 
  
  apply cl_insert_eq_cl_insert_of_mem, rwa hF.cl }

lemma flat.cl_subset_of_subset (hF : M.flat F) (h : X ⊆ F) : M.cl X ⊆ F :=
by { have h' := M.cl_mono h, rwa hF.cl at h' }

/- ### Covering  -/

/-- A flat is covered by another in a matroid if they are strictly nested, with no flat
  between them . -/
def covby (M : matroid_in α) (F₀ F₁ : set α) : Prop :=
  M.flat F₀ ∧ M.flat F₁ ∧ F₀ ⊂ F₁ ∧ ∀ F, M.flat F → F₀ ⊆ F → F ⊆ F₁ → F = F₀ ∨ F = F₁

lemma covby_iff :
  M.covby F₀ F₁ ↔ M.flat F₀ ∧ M.flat F₁ ∧ F₀ ⊂ F₁ ∧
    ∀ F, M.flat F → F₀ ⊆ F → F ⊆ F₁ → F = F₀ ∨ F = F₁ :=
iff.rfl
/- question: should this lemma be renamed to `covby_def`, as in `flat_def`? -/

lemma flat.covby_iff_of_flat (hF₀ : M.flat F₀) (hF₁ : M.flat F₁) :
  M.covby F₀ F₁ ↔ (F₀ ⊂ F₁) ∧ ∀ F, M.flat F → F₀ ⊆ F → F ⊆ F₁ → F = F₀ ∨ F = F₁ :=
by rw [covby_iff, and_iff_right hF₀, and_iff_right hF₁]

lemma covby.flat_left (h : M.covby F₀ F₁) : M.flat F₀ := h.1

lemma covby.flat_right (h : M.covby F₀ F₁) : M.flat F₁ := h.2.1

lemma covby.ssubset (h : M.covby F₀ F₁) : F₀ ⊂ F₁ := h.2.2.1

lemma covby.subset (h : M.covby F₀ F₁) : F₀ ⊆ F₁ := h.2.2.1.subset

lemma covby.eq_or_eq (h : M.covby F₀ F₁) (hF : M.flat F) (h₀ : F₀ ⊆ F) (h₁ : F ⊆ F₁) :
  F = F₀ ∨ F = F₁ := h.2.2.2 F hF h₀ h₁

lemma covby.eq_of_subset_of_ssubset (h : M.covby F₀ F₁) (hF : M.flat F) (hF₀ : F₀ ⊆ F) 
(hF₁ : F ⊂ F₁) :
  F = F₀ :=
(h.2.2.2 F hF hF₀ hF₁.subset).elim id (λ h', (hF₁.ne h').elim)

lemma covby.eq_of_ssubset_of_subset (h : M.covby F₀ F₁) (hF : M.flat F) (hF₀ : F₀ ⊂ F)
(hF₁ : F ⊆ F₁) :
  F = F₁ :=
(h.2.2.2 F hF hF₀.subset hF₁).elim (λ h', (hF₀.ne.symm h').elim) id

lemma covby.cl_insert_eq  (h : M.covby F₀ F₁) (he : e ∈ F₁ \ F₀) :
  M.cl (insert e F₀) = F₁ :=
begin
  refine h.eq_of_ssubset_of_subset (M.flat_of_cl _)
    ((ssubset_insert he.2).trans_subset (M.subset_cl _ _))
    (h.flat_right.cl_subset_of_subset (insert_subset.mpr ⟨he.1, h.ssubset.subset⟩)),
  rw [insert_eq, union_subset_iff, singleton_subset_iff],
  exact ⟨h.flat_right.subset_ground he.1, h.flat_left.subset_ground⟩
end

lemma flat.covby_iff_eq_cl_insert (hF₀ : M.flat F₀) : 
  M.covby F₀ F₁ ↔ ∃ e ∈ M.E \ F₀, F₁ = M.cl (insert e F₀) :=
begin
  refine ⟨λ h, _, _⟩,
  { obtain ⟨e, heF₁, heF₀⟩ := exists_of_ssubset h.ssubset, 
    simp_rw ←h.cl_insert_eq ⟨heF₁,heF₀⟩,
    have : e ∈ M.E \ F₀ := ⟨h.flat_right.subset_ground heF₁, heF₀⟩,
    exact ⟨_, this, rfl⟩ },
  rintro ⟨e, heF₀, rfl⟩, 
  refine ⟨hF₀, M.flat_of_cl _, 
    (M.subset_cl_of_subset (subset_insert _ _) _).ssubset_of_nonempty_diff _, λ F hF hF₀F hFF₁, _⟩, 
  { rw [insert_eq, union_subset_iff, singleton_subset_iff],
    exact ⟨heF₀.1, hF₀.subset_ground⟩ },
  { use e,
    refine ⟨M.mem_cl_of_mem (mem_insert _ _) _, _⟩,
    { rw [insert_eq, union_subset_iff, singleton_subset_iff],
      exact ⟨heF₀.1, hF₀.subset_ground⟩ },
    exact heF₀.2 },

  refine or_iff_not_imp_left.mpr 
    (λ hne, (hFF₁.antisymm (hF.cl_subset_of_subset (insert_subset.mpr ⟨_, hF₀F⟩)))),

  obtain ⟨f, hfF, hfF₀⟩ := exists_of_ssubset (hF₀F.ssubset_of_ne (ne.symm hne)),
  obtain ⟨he', -⟩ :=  hF₀.cl_exchange ⟨hFF₁ hfF, hfF₀⟩, 
  exact mem_of_mem_of_subset he' (hF.cl_subset_of_subset (insert_subset.mpr ⟨hfF,hF₀F⟩)),
end
/- hypothesis: added `e ∈ M.E` to RHS.
   If `e ∉ M.E`, then `F₁ = M.cl F₀ = F₀`.
   In particular, `F₀` is not a proper subset
   of `F₁`. -/

lemma cl_covby_iff : M.covby (M.cl X) F ↔ ∃ e ∈ M.E \ M.cl X, F = M.cl (insert e X) :=
by simp_rw [(M.flat_of_cl X).covby_iff_eq_cl_insert, cl_insert_cl_eq_cl_insert]
/- hypothesis: added `e ∈ M.E` to RHS, as in the previous
   lemma. -/

lemma flat.exists_unique_flat_of_not_mem (hF₀ : M.flat F₀) (he : e ∈ M.E \ F₀) :
  ∃! F₁, e ∈ F₁ ∧ M.covby F₀ F₁ :=
begin
  simp_rw [hF₀.covby_iff_eq_cl_insert], 
  use M.cl (insert e F₀),
  refine ⟨_, _⟩,
  { split,
    { exact (M.inter_ground_subset_cl (insert e F₀)) ⟨mem_insert _ _, he.1⟩ },
    use [e, he],
  },
  simp only [exists_prop, and_imp, forall_exists_index],
  rintro X heX f hfF₀ rfl,
  rw hF₀.cl_insert_eq_cl_insert_of_mem ⟨heX, he.2⟩
end
/- hypothesis: added `e ∈ M.E` -/


lemma flat.covby_partition (hF : M.flat F) : 
  setoid.is_partition (insert F ((λ F₁, F₁ \ F) '' {F₁ | M.covby F F₁}) \ {∅}) := 
begin
    sorry
    
    -- { simp only [mem_diff, mem_insert_iff, eq_self_iff_true, mem_image, mem_set_of_eq, true_or, 
    --   mem_singleton_iff, true_and, exists_unique_iff_exists, exists_prop, and_imp, forall_eq_or_imp, 
    --   implies_true_iff, forall_exists_index, forall_apply_eq_imp_iff₂],
    --   simp_rw [iff_true_intro heF.1, and_true, not_true, false_implies_iff, imp_true_iff, and_true], 
    --   rintro rfl, exact not_mem_empty e heF.1
    -- },
    -- {
    --   by_cases g : e ∈ M.E,
    --   {
    --       sorry,
    --   -- simp only [mem_diff, mem_insert_iff, mem_image, mem_set_of_eq, mem_singleton_iff, 
    --   -- exists_unique_iff_exists, exists_prop], 
    --   -- obtain ⟨F' ,hF'⟩ := hF.exists_unique_flat_of_not_mem heF, 
    --   -- simp only [and_imp] at hF',   
    --   -- use F' \ F, 
    --   -- simp only [and_imp, forall_eq_or_imp, forall_exists_index, forall_apply_eq_imp_iff₂, mem_diff, 
    --   --   iff_false_intro heF, is_empty.forall_iff, implies_true_iff, not_false_iff, forall_true_left, 
    --   --   true_and, ← ne.def, ←nonempty_iff_ne_empty, and_true], 
      
    --   -- refine ⟨⟨⟨or.inr ⟨_, hF'.1.2, rfl⟩,⟨ e, hF'.1.1, heF⟩⟩,hF'.1.1⟩, λ F₁ hFF₁ hne heF₁, _⟩, 
    --   -- rw [hF'.2 F₁ heF₁ hFF₁]
    --   },

    -- },



  -- refine ⟨not_mem_diff_singleton _ _,
  --   λ e, (em (e ∈ F)).elim (λ heF, ⟨F, _⟩) (λ heF, _)⟩,
  -- { simp only [mem_diff, mem_insert_iff, eq_self_iff_true, mem_image, mem_set_of_eq, true_or, 
  --   mem_singleton_iff, true_and, exists_unique_iff_exists, exists_prop, and_imp, forall_eq_or_imp, 
  --   implies_true_iff, forall_exists_index, forall_apply_eq_imp_iff₂],
  --   simp_rw [iff_true_intro heF, and_true, not_true, false_implies_iff, imp_true_iff, and_true], 
  --   rintro rfl, exact not_mem_empty e heF },
  -- { simp only [mem_diff, mem_insert_iff, mem_image, mem_set_of_eq, mem_singleton_iff, 
  --   exists_unique_iff_exists, exists_prop], 
  --   obtain ⟨F' ,hF'⟩ := hF.exists_unique_flat_of_not_mem heF, 
  --   simp only [and_imp] at hF',   
  --   use F' \ F, 
  --   simp only [and_imp, forall_eq_or_imp, forall_exists_index, forall_apply_eq_imp_iff₂, mem_diff, 
  --     iff_false_intro heF, is_empty.forall_iff, implies_true_iff, not_false_iff, forall_true_left, 
  --     true_and, ← ne.def, ←nonempty_iff_ne_empty, and_true], 
    
  --   refine ⟨⟨⟨or.inr ⟨_, hF'.1.2, rfl⟩,⟨ e, hF'.1.1, heF⟩⟩,hF'.1.1⟩, λ F₁ hFF₁ hne heF₁, _⟩, 
  --   rw [hF'.2 F₁ heF₁ hFF₁] }, 
end 

lemma flat.covby_partition_of_nonempty (hF : M.flat F) (hFne : F.nonempty) : 
  setoid.is_partition (insert F ((λ F₁, F₁ \ F) '' {F₁ | M.covby F F₁})) := 
begin
  convert hF.covby_partition, 
  rw [eq_comm, sdiff_eq_left, disjoint_singleton_right], 
  rintro (rfl | ⟨F', hF', h⟩) , 
  { exact not_nonempty_empty hFne },
  refine hF'.ssubset.not_subset _, 
  simpa [diff_eq_empty] using h, 
end 

lemma flat.covby_partition_of_empty (hF : M.flat ∅) : 
  setoid.is_partition {F | M.covby ∅ F} := 
begin
  convert hF.covby_partition, 
  simp only [diff_empty, image_id', insert_diff_of_mem, mem_singleton, set_of],
  ext F,  
  simp_rw [mem_diff, mem_singleton_iff, iff_self_and], 
  rintro hF' rfl, 
  exact hF'.ssubset.ne rfl, 
end 

-- lemma flat.sum_ncard_diff_of_covby [finite E] (hF : M.flat F) :
--   F.ncard + ∑ᶠ F' ∈ {F' | M.covby F F'}, (F' \ F).ncard = nat.card E :=
-- begin
--   obtain (rfl | hFne) := F.eq_empty_or_nonempty, 
--   { convert finsum_partition_eq hF.covby_partition_of_empty, simp },
--   convert finsum_partition_eq (hF.covby_partition_of_nonempty hFne), 
--   rw [finsum_mem_insert, add_left_cancel_iff, finsum_mem_image],  
--   { rintro F₁ hF₁ F₂ hF₂ (h : F₁ \ F = F₂ \ F), 
--     rw [←diff_union_of_subset hF₁.subset, h, diff_union_of_subset hF₂.subset] }, 
--   { rintro ⟨F', hF', (h : F' \ F = F)⟩, 
--     obtain ⟨e, he⟩ := hFne,
--     exact (h.symm.subset he).2 he },
--   exact (to_finite _).image _,
-- end 

lemma flat.cl_eq_iff_basis_of_indep (hF : M.flat F) (hI : M.indep I) : M.cl I = F ↔ M.basis I F := 
⟨by { rintro rfl, exact hI.basis_cl }, λ h, by rw [h.cl, hF.cl]⟩

/- ### Hyperplanes -/

section hyperplane

/-- A hyperplane is a maximal set containing no base  -/
def hyperplane (M : matroid_in α) (H : set α) : Prop := M.covby H M.E 

@[ssE_finish_rules] lemma hyperplane.subset_ground (hH : M.hyperplane H) : H ⊆ M.E :=
hH.flat_left.subset_ground 

lemma hyperplane_iff_covby : M.hyperplane H ↔ M.covby H M.E := iff.rfl 

lemma hyperplane.covby (h : M.hyperplane H) : M.covby H M.E := 
h

lemma hyperplane.flat (hH : M.hyperplane H) : M.flat H :=
hH.covby.flat_left

lemma hyperplane.ssubset_ground (hH : M.hyperplane H) : H ⊂ M.E := 
hH.covby.ssubset 

lemma hyperplane.ssubset_univ (hH : M.hyperplane H) : H ⊂ univ := 
hH.ssubset_ground.trans_subset (subset_univ _)

lemma hyperplane.cl_insert_eq (hH : M.hyperplane H) (heH : e ∉ H) (he : e ∈ M.E . ssE) : 
  M.cl (insert e H) = M.E := 
hH.covby.cl_insert_eq ⟨he, heH⟩

lemma hyperplane.cl_eq_univ_of_ssupset (hH : M.hyperplane H) (hX : H ⊂ X)
  (hX' : X ⊆ M.E . ssE) : M.cl X = M.E :=
begin
  obtain ⟨e, heX, heH⟩ := exists_of_ssubset hX, 
  exact (M.cl_subset_ground _).antisymm ((hH.cl_insert_eq heH (hX' heX)).symm.trans_subset 
    (M.cl_subset (insert_subset.mpr ⟨heX, hX.subset⟩))),
end 

lemma hyperplane.spanning_of_ssupset (hH : M.hyperplane H) (hX : H ⊂ X) (hXE : X ⊆ M.E . ssE ) :
  M.spanning X := 
by rw [spanning_iff_cl, hH.cl_eq_univ_of_ssupset hX]

lemma hyperplane.not_spanning (hH : M.hyperplane H) : ¬M.spanning H := 
by { rw hH.flat.spanning_iff, exact hH.ssubset_ground.ne }

lemma hyperplane.flat_supset_eq_ground (hH : M.hyperplane H) (hF : M.flat F) (hHF : H ⊂ F) :
  F = M.E := by rw [←hF.cl, hH.cl_eq_univ_of_ssupset hHF]

lemma hyperplane_iff_maximal_proper_flat : 
  M.hyperplane H ↔ (M.flat H ∧ H ⊂ M.E ∧ ∀ F, H ⊂ F → M.flat F → F = M.E) :=
begin
  rw [hyperplane_iff_covby, covby, and_iff_right M.ground_flat, and.congr_right_iff, 
    and.congr_right_iff], 
  simp_rw [or_iff_not_imp_left, ssubset_iff_subset_ne, and_imp, ←ne.def], 
  exact λ hH hHE hne, ⟨λ h F hHF hne' hF, (h F hF hHF hF.subset_ground hne'.symm), 
    λ h F hF hHF hFE hne', h F hHF hne'.symm hF⟩,  
end

lemma hyperplane_iff_maximal_nonspanning : 
  M.hyperplane H ↔ H ∈ maximals (⊆) {X | X ⊆ M.E ∧ ¬ M.spanning X } :=
begin
  simp_rw [mem_maximals_set_of_iff, and_imp],  
  refine ⟨λ h, ⟨⟨h.subset_ground, h.not_spanning⟩, λ X hX hX' hHX, _⟩, λ h, _⟩,
  { exact by_contra (λ hne, hX' (h.spanning_of_ssupset (hHX.ssubset_of_ne hne))) },
  rw [hyperplane_iff_covby, covby_iff, and_iff_right M.ground_flat, 
    flat_iff_ssubset_cl_insert_forall h.1.1],   
  refine ⟨λ e he, _, h.1.1.ssubset_of_ne (by { rintro rfl, exact h.1.2 M.ground_spanning }), 
    λ F hF hHF hFE, or_iff_not_imp_right.mpr (λ hFE', _)⟩, 
  { have h' := h.2 (insert_subset.mpr ⟨he.1, h.1.1⟩), 
    simp_rw [subset_insert, forall_true_left, @eq_comm _  H, insert_eq_self, 
      iff_false_intro he.2, imp_false, not_not, spanning_iff_cl] at h', 
    rw [h', ←not_spanning_iff_cl h.1.1], 
    exact h.1.2 },
  have h' := h.2 hFE, 
  rw [hF.spanning_iff] at h', 
  rw [h' hFE' hHF], 
end 

-- lemma hyperplane_iff_maximal_nonspanning : 
--   M.hyperplane H ↔ H ∈ maximals (⊆) {X | X ⊆ M.E ∧ ¬ M.spanning X } :=

@[simp] lemma compl_cocircuit_iff_hyperplane (hH : H ⊆ M.E . ssE) : 
  M.cocircuit (M.E \ H) ↔ M.hyperplane H :=
begin
  simp_rw [cocircuit_iff_mem_minimals_compl_nonspanning, hyperplane_iff_maximal_nonspanning, 
    mem_maximals_set_of_iff, mem_minimals_set_of_iff, sdiff_sdiff_right_self, inf_eq_inter, 
    ground_inter_right, and_imp, and_iff_right hH, and.congr_right_iff, subset_diff], 
  refine λ hH', ⟨λ h X hX hXE hXH, _, λ h X hX hXE , _⟩, 
  { rw ←diff_eq_diff_iff_eq (hXH.trans hX) hX, 
    exact @h (M.E \ X) (by simpa) ⟨(diff_subset _ _), 
      disjoint_of_subset_right hXH disjoint_sdiff_left⟩ },
  rw [@h (M.E \ X) (diff_subset _ _) hX, sdiff_sdiff_right_self, inf_eq_inter, 
    inter_eq_self_of_subset_right hXE.1], 
  rw [subset_diff, and_iff_right hH],
  exact hXE.2.symm,  
end

@[simp] lemma compl_hyperplane_iff_cocircuit (h : K ⊆ M.E . ssE ) :
  M.hyperplane (M.E \ K) ↔ M.cocircuit K := 
by rw [←compl_cocircuit_iff_hyperplane, diff_diff_right, diff_self, empty_union,
  inter_comm, (inter_eq_left_iff_subset.mpr h)]
/- added `K ⊆ M.E` -/

lemma hyperplane.compl_cocircuit (hH : M.hyperplane H) : M.cocircuit (M.E \ H) := 
compl_cocircuit_iff_hyperplane.mpr hH

lemma cocircuit.compl_hyperplane {K : set α} (hK : M.cocircuit K) : M.hyperplane (M.E \ K) := 
(compl_hyperplane_iff_cocircuit hK.subset_ground).mpr hK

lemma univ_not_hyperplane (M : matroid_in α) : ¬ M.hyperplane univ := λ h, h.ssubset_univ.ne rfl 

lemma hyperplane.eq_of_subset (h₁ : M.hyperplane H₁) (h₂ : M.hyperplane H₂) (h : H₁ ⊆ H₂) :
  H₁ = H₂ :=
(h₁.covby.eq_or_eq h₂.flat h h₂.subset_ground).elim eq.symm (λ h', (h₂.ssubset_ground.ne h').elim)

lemma hyperplane.not_ssubset (h₁ : M.hyperplane H₁) (h₂ : M.hyperplane H₂) : ¬ H₁ ⊂ H₂ :=
λ hss, hss.ne (h₁.eq_of_subset h₂ hss.subset)

lemma hyperplane.exists_not_mem (hH : M.hyperplane H) : ∃ e, e ∉ H :=
by {by_contra' h, apply M.univ_not_hyperplane, convert hH, rwa [eq_comm, eq_univ_iff_forall] }

lemma base.hyperplane_of_cl_diff_singleton (hB : M.base B) (heB : e ∈ B) :
  M.hyperplane (M.cl (B \ {e})) :=
begin
  rw [hyperplane_iff_covby, flat.covby_iff_eq_cl_insert (M.flat_of_cl _)], 
  refine ⟨e,⟨hB.subset_ground heB, _⟩, _⟩, 
  { rw [(hB.indep.diff {e}).not_mem_cl_iff (hB.subset_ground heB)], 
    simpa [insert_eq_of_mem heB] using hB.indep },
  simpa [insert_eq_of_mem heB] using hB.cl.symm, 
end

lemma hyperplane.ssupset_eq_univ_of_flat (hH : M.hyperplane H) (hF : M.flat F) (h : H ⊂ F) :
  F = M.E :=
hH.covby.eq_of_ssubset_of_subset hF h hF.subset_ground

lemma hyperplane.cl_insert_eq_univ (hH : M.hyperplane H) (he : e ∈ M.E \ H) :
  M.cl (insert e H) = M.E :=
begin
  refine hH.ssupset_eq_univ_of_flat (M.flat_of_cl _)
    ((ssubset_insert he.2).trans_subset (M.subset_cl _ _)),
  rw [insert_eq, union_subset_iff, singleton_subset_iff],
  exact ⟨he.1, hH.subset_ground⟩,
end
/- changed `univ` to `M.E` -/
/- hypothesis: changed `e ∉ H` to `e ∈ M.E \ H` -/

-- change e ∈ M.E \ H

lemma exists_hyperplane_sep_of_not_mem_cl (h : e ∈ M.E \ M.cl X) (hX : X ⊆ M.E . ssE) :
  ∃ H, M.hyperplane H ∧ X ⊆ H ∧ e ∉ H :=
begin
  obtain ⟨I, hI⟩ := M.exists_basis X,
  rw ←hI.cl at h,
  have h' := h.2,
  rw hI.indep.not_mem_cl_iff at h',
  obtain ⟨B, hB, heIB⟩ := h'.2.exists_base_supset,
  rw insert_subset at heIB,
  exact ⟨M.cl (B \ {e}), hB.hyperplane_of_cl_diff_singleton heIB.1,
    hI.subset_cl.trans (M.cl_subset (subset_diff_singleton heIB.2 h'.1)),
    λ hecl, indep_iff_cl_diff_ne_forall.mp hB.indep e heIB.1 (cl_diff_singleton_eq_cl hecl)⟩,
end
/- hypothesis: changed `e ∉ M.cl X` to `e ∈ M.E \ M.cl X` -/
/- hypothesis: added `X ⊆ M.E` since otherwise `X ⊆ H` where
   `M.hyperplane H` never holds -/

lemma cl_eq_sInter_hyperplanes (M : matroid_in α) (X : set α) (hX : X ⊆ M.E . ssE) :
  M.cl X = ⋂₀ {H | M.hyperplane H ∧ X ⊆ H} :=
begin
  apply subset_antisymm,
  { simp only [subset_sInter_iff, mem_set_of_eq, and_imp],
    exact λ H hH hXH, hH.flat.cl_subset_of_subset hXH},
  by_contra' h',
  obtain ⟨x, h, hx⟩ := not_subset.mp h',
  
  dsimp at h,
  sorry 
  -- question: is it possible to show `x ∈ M.E`?

  --obtain ⟨H, hH, hXH, hxH⟩ := exists_hyperplane_sep_of_not_mem_cl hx hX,
  --exact hxH (h H ⟨hH, hXH⟩),
end
/- hypothesis: added `X ⊆ M.E` since otherwise `X ⊆ H` where
   `M.hyperplane H` never holds -/
   
lemma mem_cl_iff_forall_hyperplane : e ∈ M.cl X ↔ ∀ H, M.hyperplane H → X ⊆ H → e ∈ H :=
by sorry -- simp [cl_eq_sInter_hyperplanes]

lemma mem_dual_cl_iff_forall_circuit : 
  e ∈ M﹡.cl X ↔ ∀ C, M.circuit C → e ∈ C → (X ∩ C).nonempty :=
begin
  sorry, 
  --  rw [←dual_dual M], 
  --  simp_rw [dual_circuit_iff_cocircuit, ←compl_hyperplane_iff_cocircuit, dual_dual, 
  --   mem_cl_iff_forall_hyperplane], 
  -- refine ⟨λ h K hH heK, _, λ h H hH hXH, (by_contra (λ heH, _))⟩,
  -- { have h' := h _ hH,  
  --   rwa [mem_compl_iff, iff_false_intro (not_not.mpr heK), imp_false, 
  --     subset_compl_iff_disjoint_right, not_disjoint_iff_nonempty_inter] at h' },
  -- obtain ⟨e, heX, heH⟩ := h Hᶜ (by rwa compl_compl) heH, 
  -- exact heH (hXH heX), 
end 

lemma flat.subset_hyperplane_of_ne_univ (hF : M.flat F) (h : F ≠ univ) : 
  ∃ H, M.hyperplane H ∧ F ⊆ H :=
begin
  sorry,
  -- obtain ⟨e,he⟩ := (ne_univ_iff_exists_not_mem _).mp h, 
  -- rw ←hF.cl at he,  
  -- obtain ⟨H, hH, hFH, -⟩ := exists_hyperplane_sep_of_not_mem_cl ⟨he, _⟩ _, 
  -- exact ⟨H, hH, hFH⟩,  
end

lemma subset_hyperplane_iff_cl_ne_ground (hY : Y ⊆ M.E . ssE) :
  M.cl Y ≠ M.E ↔ ∃ H, M.hyperplane H ∧ Y ⊆ H :=
begin
  sorry 
  -- refine ⟨λ h, _,_⟩,
  -- { obtain ⟨H, hH, hYH⟩ := (M.flat_of_cl Y).subset_hyperplane_of_ne_univ h,
  --   exact ⟨H, hH, (M.subset_cl Y).trans hYH⟩},
  -- rintro ⟨H, hH, hYH⟩ hY,
  -- refine hH.ssubset_univ.not_subset _,
  -- rw ←hH.flat.cl,
  -- exact (hY.symm.trans_subset (M.cl_mono hYH)),
end

lemma hyperplane.inter_right_covby_of_inter_left_covby
(hH₁ : M.hyperplane H₁) (hH₂ : M.hyperplane H₂) (h : M.covby (H₁ ∩ H₂) H₁) :
  M.covby (H₁ ∩ H₂) H₂ :=
begin
  sorry,
  -- obtain (rfl | hne) := eq_or_ne H₁ H₂, assumption,
  -- have hssu : H₁ ∩ H₂ ⊂ H₂,
  -- { refine (inter_subset_right _ _).ssubset_of_ne (λh'', hne _ ),
  --   rw [inter_eq_right_iff_subset, ←le_iff_subset] at h'',
  --   rw eq_of_le_of_not_lt h'' (hH₂.not_ssubset hH₁)},

  -- refine ⟨hH₁.flat.inter hH₂.flat, hH₂.flat, hssu, λ F hF hssF hFH₂, _⟩,
  -- by_contra' h',

  -- obtain ⟨x,hxF,hx⟩ := exists_of_ssubset (hssF.ssubset_of_ne (ne.symm h'.1)),
  -- obtain ⟨y,hyH₂,hy⟩ := exists_of_ssubset (hFH₂.ssubset_of_ne h'.2),
  -- obtain ⟨z,hzH₁,hz⟩ := exists_of_ssubset h.ssubset,
  -- have hzcl : M.cl (insert z (H₁ ∩ H₂)) = H₁ := h.cl_insert_eq ⟨hzH₁,hz⟩,
  -- have hxH₁ : x ∉ H₁ := λ hxH₁, hx ⟨hxH₁, hFH₂ hxF⟩,

  -- have h₁ : z ∉ M.cl (insert x (H₁ ∩ H₂)),
  -- { intro hz', apply hxH₁,
  --   have h' := cl_exchange ⟨hz', by rwa (hH₁.flat.inter hH₂.flat).cl⟩,
  --   rw [h.cl_insert_eq ⟨hzH₁,hz⟩] at h',
  --   exact h'.1},

  -- have hycl : y ∈ M.cl (insert z (insert x (H₁ ∩ H₂))) \ M.cl (insert x (H₁ ∩ H₂)),
  -- { refine ⟨_,λ hy',hy _⟩,
  --   { rw [insert_comm, ←cl_insert_cl_eq_cl_insert, hzcl, hH₁.cl_insert_eq_univ hxH₁],
  --     exact mem_univ _ },
  --   exact hF.cl_subset_of_subset (insert_subset.mpr ⟨hxF,hssF⟩) hy' },

  -- refine hz ⟨hzH₁, mem_of_mem_of_subset (cl_exchange hycl) ((diff_subset _ _).trans
  --   (hH₂.flat.cl_subset_of_subset _))⟩,
  -- rw [insert_subset, insert_subset],
  -- exact ⟨hyH₂, hFH₂ hxF, inter_subset_right _ _⟩,
end

lemma hyperplane.inter_covby_comm (hH₁ : M.hyperplane H₁) (hH₂ : M.hyperplane H₂) :
  M.covby (H₁ ∩ H₂) H₁ ↔  M.covby (H₁ ∩ H₂) H₂ :=
⟨hH₁.inter_right_covby_of_inter_left_covby hH₂,
  by {rw inter_comm, intro h, exact hH₂.inter_right_covby_of_inter_left_covby hH₁ h}⟩

end hyperplane

-- section from_axioms

-- lemma matroid_of_flat_aux [finite E] (flat : set α → Prop) (univ_flat : flat univ)
-- (flat_inter : ∀ F₁ F₂, flat F₁ → flat F₂ → flat (F₁ ∩ F₂)) (X : set α) :
--   flat (⋂₀ {F | flat F ∧ X ⊆ F}) ∧ ∀ F₀, flat F₀ → ((⋂₀ {F | flat F ∧ X ⊆ F}) ⊆ F₀ ↔ X ⊆ F₀) :=
-- begin
--   set F₁ := ⋂₀ {F | flat F ∧ X ⊆ F} with hF₁,
--   refine ⟨_, λ F₀ hF₀, ⟨λ hF₁F₀, _, λ hXF, _⟩⟩ ,
--   { obtain ⟨F',⟨hF',hYF'⟩,hmin⟩ := finite.exists_minimal (λ F, flat F ∧ X ⊆ F)
--       ⟨univ, univ_flat, subset_univ _⟩,
--     convert hF',
--     refine subset_antisymm (sInter_subset_of_mem ⟨hF',hYF'⟩) (subset_sInter _),
--     rintro F ⟨hF,hYF⟩,
--     rw hmin _ ⟨flat_inter _ _ hF hF', subset_inter hYF hYF'⟩ _,
--     { apply inter_subset_left},
--     apply inter_subset_right},
--   { refine subset_trans (subset_sInter (λ F h, _)) hF₁F₀, exact h.2},
--   apply sInter_subset_of_mem,
--   exact ⟨hF₀, hXF⟩,
-- end

-- /-- A collection of sets satisfying the flat axioms determines a matroid -/
-- def matroid_of_flat [finite E] (flat : set α → Prop) (univ_flat : flat univ)
-- (flat_inter : ∀ F₁ F₂, flat F₁ → flat F₂ → flat (F₁ ∩ F₂))
-- (flat_partition : ∀ F₀ e, flat F₀ → e ∉ F₀ →
--   ∃! F₁, flat F₁ ∧ insert e F₀ ⊆ F₁ ∧ ∀ F, flat F → F₀ ⊆ F → F ⊂ F₁ → F₀ = F) :=
-- matroid_of_cl_of_finite (λ X, ⋂₀ {F | flat F ∧ X ⊆ F})
-- (λ X, subset_sInter (λ F, and.right))
-- (λ X Y hXY, subset_sInter (λ F hF, by {apply sInter_subset_of_mem, exact ⟨hF.1, hXY.trans hF.2⟩}))
-- (begin
--   refine λ X, (subset_sInter (λ F, and.right)).antisymm' _,
--   simp only [subset_sInter_iff, mem_set_of_eq, and_imp],
--   rintro F hF hXF,
--   apply sInter_subset_of_mem,
--   split, assumption,
--   apply sInter_subset_of_mem,
--   exact ⟨hF, hXF⟩,
-- end )
-- (begin
--   simp only [mem_diff, mem_sInter, mem_set_of_eq, and_imp, not_forall, exists_prop,
--     forall_exists_index],
--   refine λ X e f h F₀ hF₀ hXF₀ hfF₀, ⟨λ Ff hFf hfXf, _,
--     ⟨F₀, hF₀, hXF₀, λ heF₀, hfF₀ (h _ hF₀ (insert_subset.mpr ⟨heF₀,hXF₀⟩))⟩⟩,

--   obtain ⟨hFX, hX'⟩    := matroid_of_flat_aux flat univ_flat flat_inter X,
--   obtain ⟨hFXe, hXe'⟩  := matroid_of_flat_aux flat univ_flat flat_inter (insert e X),
--   obtain ⟨hFXf, hXf'⟩  := matroid_of_flat_aux flat univ_flat flat_inter (insert f X),

--   set FX := sInter {F | flat F ∧ X ⊆ F} with hFX_def,
--   set FXe := sInter {F | flat F ∧ insert e X ⊆ F} with hFXe_def,
--   set FXf := sInter {F | flat F ∧ insert f X ⊆ F} with hFXe_def,

--   apply (hXf' Ff hFf).mpr hfXf,
--   have heFXe : e ∈ FXe := mem_sInter.mpr (λ _ hF, hF.2 (mem_insert _ _)),
--   have hfFXf : f ∈ FXf := mem_sInter.mpr (λ _ hF, hF.2 (mem_insert _ _)),

--   have hXFX : X ⊆ FX := subset_sInter (λ _, and.right),
--   have hfFX : f ∉ FX := λ hfFX, hfF₀ ((hX' F₀ hF₀).mpr hXF₀ hfFX),
--   have heFX : e ∉ FX := λ heFX, hfFX (h _ hFX (insert_subset.mpr ⟨heFX, hXFX⟩)),
--   have hFXFXe : FX ⊆ FXe,
--   { rw [hX' FXe hFXe], exact subset_sInter (λ F hF, (subset_insert _ _).trans hF.2)},
--   have hFXFXf : FX ⊆ FXf,
--   { rw [hX' FXf hFXf], exact subset_sInter (λ F hF, (subset_insert _ _).trans hF.2)},

--   have hfFXe := h FXe hFXe (insert_subset.mpr ⟨heFXe,hXFX.trans hFXFXe⟩),

--   have hss := (hXf' _ hFXe).mpr (insert_subset.mpr ⟨hfFXe, hXFX.trans hFXFXe⟩),

--   suffices h_eq : FXf = FXe, by rwa h_eq,
--   by_contra h_ne, apply hfFX,
--   have hssu := ssubset_of_subset_of_ne hss h_ne,

--   obtain ⟨FXe',⟨hFXe',heFX',hmin⟩, hunique⟩ := flat_partition FX e hFX heFX,

--   have hFXemin : ∀ (F : set α), flat F → FX ⊆ F → F ⊂ FXe → FX = F, from
--   λ F hF hFXF hFFXe, hmin _ hF hFXF
--     (hFFXe.trans_subset ((hXe' _ hFXe').mpr ((insert_subset_insert hXFX).trans heFX'))),

--   rw hunique FXe ⟨hFXe, insert_subset.mpr ⟨heFXe, hFXFXe⟩, hFXemin⟩ at hssu,
--   rwa ← (hmin _ hFXf hFXFXf hssu) at hfFXf,
-- end)

-- @[simp] lemma matroid_of_flat_apply [finite E] (flat : set α → Prop) (univ_flat : flat univ)
-- (flat_inter : ∀ F₁ F₂, flat F₁ → flat F₂ → flat (F₁ ∩ F₂))
-- (flat_partition : ∀ F₀ e, flat F₀ → e ∉ F₀ →
-- ∃! F₁, flat F₁ ∧ insert e F₀ ⊆ F₁ ∧ ∀ F, flat F → F₀ ⊆ F → F ⊂ F₁ → F₀ = F) :
--   (matroid_of_flat flat univ_flat flat_inter flat_partition).flat = flat :=
-- begin
--   ext F,
--   simp_rw [matroid_of_flat, matroid.flat_iff_cl_self, matroid_of_cl_of_finite_apply],
--   refine ⟨λ hF, _, λ hF, _⟩,
--   { rw ←hF, exact (matroid_of_flat_aux flat univ_flat flat_inter _).1},
--   exact (subset_sInter (λ F', and.right)).antisymm' (sInter_subset_of_mem ⟨hF,rfl.subset⟩),
-- end

-- end from_axioms 

end matroid_in

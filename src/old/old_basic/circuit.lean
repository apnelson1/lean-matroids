


import prelim.induction prelim.collections .rankfun .indep
import set_tactic.solver
open_locale classical
noncomputable theory

open set

universe u

variables {α : Type*} [fintype α]

namespace cct_family

-- This needs fixing

def C_to_I (M : cct_family α) : (set α → Prop) :=
  λ I, ∀ X, X ⊆ I → ¬M.cct X

lemma C_to_empty_indep (M : cct_family α) :
  satisfies_I1 (C_to_I M) :=
by {intro X, rw subset_empty_iff, intro hX, rw hX, exact M.C1}

lemma C_to_indep_of_subset_indep (M : cct_family α) :
  satisfies_I2 (C_to_I M) :=
λ I J hIJ hJ X hXI, hJ _ (subset.trans hXI hIJ)

lemma new_circuit_contains_new_elem {M : cct_family α} {I C : set α} {e : α} :
  C_to_I M I → C ⊆ (I ∪ {e}) → M.cct C → e ∈ C :=
λ hI hCIe hC, by {by_contra he, from hI C (subset_of_subset_add_nonmem hCIe he) hC}

lemma union_mem_singleton_unique_circuit {M : cct_family α} {I : set α} {e : α} :
  C_to_I M I → ¬C_to_I M (I ∪ {e}) → ∃! C, M.cct C ∧ C ⊆ I ∪ {e} :=
begin
  intros hI hIe, unfold C_to_I at hI hIe, push_neg at hIe,
  rcases hIe with ⟨C, ⟨hCI, hC⟩⟩, refine ⟨C,⟨⟨hC,hCI⟩,λ C' hC', _⟩⟩,
  have := mem_inter (new_circuit_contains_new_elem hI hCI hC)
                              (new_circuit_contains_new_elem hI hC'.2 hC'.1),
  by_contra hCC',
  cases M.C3 _ _ e (ne.symm hCC') hC hC'.1 this with C₀ hC₀,
  from hI _ (subset.trans hC₀.2 (removal_subset_of (union_subset hCI hC'.2))) hC₀.1,
end

lemma union_mem_singleton_le_one_circuit {M : cct_family α} {I C C': set α} (e : α) :
  C_to_I M I → (M.cct C ∧ C ⊆ I ∪ {e}) → (M.cct C' ∧ C' ⊆ I ∪ {e}) → C = C' :=
begin
  intros hI hC hC',
  by_cases h': C_to_I M (I ∪ {e}),
  exfalso, from h' _ hC.2 hC.1,
  rcases (union_mem_singleton_unique_circuit hI h') with ⟨ C₀,⟨ _,hC₀⟩⟩ ,
  from eq.trans (hC₀ _ hC) (hC₀ _ hC').symm,
end

lemma C_to_I3 (M : cct_family α) :
  satisfies_I3 (C_to_I M) :=
begin
  -- I3 states that there are no bad pairs
  let bad_pair : set α → set α → Prop :=
    λ I J, size I < size J ∧ C_to_I M I ∧ C_to_I M J ∧ ∀ (e:α), e ∈ J \ I → ¬C_to_I M (I ∪ {e}),
  suffices : ∀ I J, ¬bad_pair I J,
    push_neg at this, from λ I J hIJ hI hJ, this I J hIJ hI hJ,
  by_contra h, push_neg at h, rcases h with ⟨I₀,⟨J₀, h₀⟩⟩,
 
  --choose a bad pair with D = I-J minimal
  let bad_pair_diff : set α → Prop := λ D, ∃ I J, bad_pair I J ∧ I \ J = D,
  have hD₀ : bad_pair_diff (I₀ \ J₀) := ⟨I₀,⟨J₀,⟨h₀,rfl⟩⟩⟩,
  rcases minimal_example bad_pair_diff hD₀ with ⟨D,⟨_, ⟨⟨I, ⟨J, ⟨hbad, hIJD⟩⟩⟩,hDmin⟩⟩⟩, 
  rcases hbad with ⟨hsIJ, ⟨hI,⟨hJ,h_non_aug⟩ ⟩  ⟩ ,
  rw ←hIJD at hDmin, clear h_left hD₀ h₀ I₀ J₀ hIJD D,
  ------------------
 
  have hJI_nonempty : 0 < size (J \ I) := by
  { have := size_induced_partition I J,
    rw inter_comm at this,
    linarith [size_nonneg (I \ J), hsIJ, size_induced_partition J I]},
 
  have hIJ_nonempty : I \ J ≠ ∅ := by
  { intro h, rw diff_empty_iff_subset at h,
    cases exists_mem_of_size_pos hJI_nonempty with e he,
    refine h_non_aug e he (C_to_indep_of_subset_indep M _ _ (_ : I ∪ {e} ⊆ J) hJ),
    from union_subset h (subset_of_mem_of_subset he (diff_subset _ _))},
 
  cases ne_empty_has_mem hIJ_nonempty with e he, -- choose e from I -J

  --There exists f ∈ J-I contained in all ccts of J ∪ {e}
  have : ∃ f, f ∈ J \ I ∧ ∀ C, C ⊆ J ∪ {e} → M.cct C → f ∈ C := by
  begin
    by_cases hJe : C_to_I M (J ∪ {e}) , -- Either J ∪ {e} has a circuit or doesn't
    { cases exists_mem_of_size_pos hJI_nonempty with f hf,
      exact ⟨f, ⟨hf, λ C hCJe hC, false.elim ((hJe _ hCJe) hC)⟩ ⟩},
    
    -- let Ce be a circuit contained in J ∪ {e}
    unfold C_to_I at hJe, push_neg at hJe, rcases hJe with ⟨Ce, ⟨hCe₁, hCe₂⟩⟩ ,
 
    have : Ce ∩ (J \ I) ≠ ∅,
    { by_contra hn, push_neg at hn, rw ←subset_compl_iff_disjoint at hn,
      refine hI Ce _ hCe₂, 
      have hCeJI : Ce ⊆ J ∪ I,
      { refine subset.trans hCe₁ (union_subset (subset_union_left _ _) _),
        rw singleton_subset_iff, apply mem_of_mem_of_subset he,
        apply subset.trans (diff_subset _ _) (subset_union_right _ _), },
    refine subset.trans (subset_inter hCeJI hn) (λ x, _),
    simp only [mem_inter_iff, mem_union, mem_compl_iff, mem_diff, and_imp],
    tauto,},

    cases ne_empty_has_mem this with f hf,
    refine ⟨f, ⟨_, λ C hCJe hC, _⟩⟩, 
    apply mem_of_mem_of_subset hf (inter_subset_right _ _),
    rw ←(union_mem_singleton_le_one_circuit e hJ ⟨hC, hCJe⟩ ⟨hCe₂, hCe₁⟩) at hf,
    from mem_of_mem_of_subset hf (inter_subset_left _ _),
  end,
  rcases this with ⟨f, ⟨hFJI, hfC⟩⟩,
  set J' := (J ∪ {e}) \ {f} with hdefJ',
 
  have hJ'₀: J' \ I ⊆ (J ∪ I), {
    set_ext, simp, tauto,
    --intros x hx, simp at *, tauto,
  },
  /-
  { rw hdefJ',
    repeat {refine subset.trans (diff_subset _ _) _},
    apply union_subset (subset_union_left _ _),
    rw [singleton_subset_iff, mem_union], right,
    exact mem_of_mem_diff he, },
  -/
  have hJ' : C_to_I M (J'),
  { intros X hXJ' hX,
    rw hdefJ' at hXJ',
    have hf := hfC X (subset_of_subset_diff hXJ') hX,
    have := mem_of_mem_of_subset hf hXJ',
    rw mem_diff at this, tauto},

  have hJ's : size I < size J',
  { rw mem_diff at he hFJI,
    rwa [hdefJ', size_union_singleton_remove hFJI.1 he.2], },
 
  have hJ'ssu : I \ J' ⊂ I \ J,
  { rw hdefJ',
    rw mem_diff at hFJI,
    simp_rw [diff_eq, compl_compl_inter_right, compl_union, inter_distrib_left,
    inter_comm _ {f}, nonmem_disjoint hFJI.2, union_empty, ←inter_assoc, ←diff_eq],
    apply ssubset_of_remove_mem he, },
 
  have hIJ' : ¬bad_pair I J' :=
    λ hIJ', hDmin (I \ J') hJ'ssu ⟨I,⟨J',⟨hIJ', rfl⟩⟩⟩,
  push_neg at hIJ', rcases hIJ' hJ's hI hJ' with ⟨g,⟨hg₁,hg₂⟩⟩ ,

  by_cases g ∈ J \ I,
  from h_non_aug g h hg₂,
 
  specialize @hJ'₀ g hg₁,
  simp only [mem_inter_eq, not_and, mem_diff, mem_compl_eq, mem_union] at h ⊢ hJ'₀ hg₁,
  tauto, 
end

end cct_family

def indep_family.of_cct_family (M : cct_family α) : indep_family α :=
  ⟨M.C_to_I, M.C_to_empty_indep, M.C_to_indep_of_subset_indep, M.C_to_I3⟩

namespace matroid

def of_cct_family (M : cct_family α) : matroid α :=
  of_indep_family (indep_family.of_cct_family M)

lemma cct_of_cct_family (M : cct_family α) :
  (of_cct_family M).is_circuit = M.cct := 
begin
  ext C, rw [is_circuit],
  erw matroid.indep_of_indep_family, dsimp only,
  rw [indep_family.of_cct_family], dsimp only,
  rw [cct_family.C_to_I], dsimp only ,
  refine ⟨λ h, _, λ h, ⟨_,(λ Y hY X hX hXY, _)⟩⟩,
  rcases h with ⟨h₁,h₂⟩,
  push_neg at h₁,
  rcases h₁ with ⟨X,hX₁, hX₂⟩,
  cases subset_ssubset_or_eq hX₁,
  from false.elim (h₂ _ h _ (subset_refl _) hX₂),
  rw ←h, from hX₂,
  push_neg, from ⟨_, ⟨subset_refl _, h⟩⟩,
  from M.C2 _ _ hXY h (subset.lt_of_le_of_lt hX hY), 
end

end matroid 
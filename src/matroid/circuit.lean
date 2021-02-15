--try the set tactic on the sorrys below (line 102 )

import preflim.induction prelim.collections .rankfun .indep set_tactic.solver

open_locale classical 
noncomputable theory 

variables {U : Type}[fintype U]

namespace cct_family

def C_to_I (M : cct_family U): (set U → Prop) := 
  λ I, ∀ X, X ⊆ I → ¬M.cct X 

lemma C_to_I1 (M : cct_family U) :
  satisfies_I1 (C_to_I M) :=
  by {intros X hX, rw subset_empty hX, from M.C1}

lemma C_to_I2 (M : cct_family U) :
  satisfies_I2 (C_to_I M) :=
  λ I J hIJ hJ X hXI, hJ _ (subset.trans hXI hIJ)

lemma new_circuit_contains_new_elem {M : cct_family U}{I C : set U}{e : U}:
  C_to_I M I → C ⊆ (I ∪ {e}) → M.cct C → e ∈ C :=
  λ hI hCIe hC, by {by_contra he, from hI C (subset_of_subset_add_nonmem hCIe he) hC}

lemma add_elem_unique_circuit {M : cct_family U} {I : set U} {e : U}:
  C_to_I M I → ¬C_to_I M (I ∪ {e}) → ∃! C, M.cct C ∧ C ⊆ I ∪ {e} :=
  begin
    intros hI hIe, unfold C_to_I at hI hIe, push_neg at hIe, 
    rcases hIe with ⟨C, ⟨hCI, hC⟩⟩, refine ⟨C,⟨⟨hC,hCI⟩,λ C' hC', _⟩⟩,
    have := elem_inter (new_circuit_contains_new_elem hI hCI hC) 
                                (new_circuit_contains_new_elem hI hC'.2 hC'.1),
    by_contra hCC', 
    cases M.C3 _ _ e (ne.symm hCC') hC hC'.1 this with C₀ hC₀,
    from hI _ (subset.trans hC₀.2 (removal_subset_of (union_of_subsets hCI hC'.2))) hC₀.1,
  end 

lemma add_elem_le_one_circuit {M : cct_family U} {I C C': set U} (e : U):
  C_to_I M I → (M.cct C ∧ C ⊆ I ∪ {e}) → (M.cct C' ∧ C' ⊆ I ∪ {e}) → C = C' :=
  begin
    intros hI hC hC', 
    by_cases h': C_to_I M (I ∪ {e}), 
    exfalso, from h' _ hC.2 hC.1,
    rcases (add_elem_unique_circuit hI h') with ⟨ C₀,⟨ _,hC₀⟩⟩ , 
    from eq.trans (hC₀ _ hC) (hC₀ _ hC').symm, 
  end

lemma C_to_I3 (M : cct_family U) :
  satisfies_I3 (C_to_I M) :=
begin
  letI := ftype.ftype_mem U, 
  -- I3 states that there are no bad pairs 
  let bad_pair : set U → set U → Prop := λ I J, size I < size J ∧ C_to_I M I ∧ C_to_I M J ∧ ∀ (e:U), e ∈ J \ I → ¬C_to_I M (I ∪ {e}), 
  suffices : ∀ I J, ¬bad_pair I J, 
    push_neg at this, from λ I J hIJ hI hJ, this I J hIJ hI hJ,
  by_contra h, push_neg at h, rcases h with ⟨I₀,⟨J₀, h₀⟩⟩,
  
  --choose a bad pair with D = I-J minimal
  let bad_pair_diff : set U → Prop := λ D, ∃ I J, bad_pair I J ∧ I \ J = D, 
  have hD₀ : bad_pair_diff (I₀ \ J₀) := ⟨I₀,⟨J₀,⟨h₀,rfl⟩⟩⟩,
  rcases minimal_example bad_pair_diff hD₀ with ⟨D,⟨_, ⟨⟨I, ⟨J, ⟨hbad, hIJD⟩⟩⟩,hDmin⟩⟩⟩,  
  rcases hbad with ⟨hsIJ, ⟨hI,⟨hJ,h_non_aug⟩ ⟩  ⟩ ,
  rw ←hIJD at hDmin, clear h_left hD₀ h₀ I₀ J₀ hIJD D, 
  ------------------
  
  have hJI_nonempty : size (J \ I) > 0 := by 
    {have := size_induced_partition I J, rw inter_comm at this, linarith [size_nonneg (I \ J), hsIJ, size_induced_partition J I]},
  
  have hIJ_nonempty : I \ J ≠ ∅ := by 
  {
    intro h, rw diff_empty_iff_subset at h, 
    cases size_pos_has_mem hJI_nonempty with e he,
    refine h_non_aug e he (C_to_I2 M _ _ (_ : I ∪ {e} ⊆ J) hJ), 
    from union_of_subsets h (subset_of_mem_of_subset he (diff_subset _ _)), 
  },
  
  cases ne_empty_has_mem hIJ_nonempty with e he, -- choose e from I -J

  --There exists f ∈ J-I contained in all ccts of J ∪ {e} 
  have : ∃ f, f ∈ J \ I ∧ ∀ C, C ⊆ J ∪ {e} → M.cct C → f ∈ C := by
  {
      by_cases hJe : C_to_I M (J ∪ {e}) , -- Either J ∪ {e} has a circuit or doesn't
      
      cases size_pos_has_mem hJI_nonempty with f hf, 
      refine ⟨f, ⟨hf, λ C hCJe hC, _⟩ ⟩, exfalso, 
      from (hJe _ hCJe) hC,
      unfold C_to_I at hJe, push_neg at hJe, rcases hJe with ⟨Ce, ⟨hCe₁, hCe₂⟩⟩ , 

      have : Ce ∩ (J \ I) ≠ ∅ := λ h,  by {sorry, },
      cases ne_empty_has_mem this with f hf,
      refine ⟨f, ⟨_, λ C hCJe hC, _⟩⟩,  
      apply mem_of_mem_of_subset hf (inter_subset_right _ _), 
      rw ←(add_elem_le_one_circuit e hJ ⟨hC, hCJe⟩ ⟨hCe₂, hCe₁⟩) at hf,
      from mem_of_mem_of_subset hf (inter_subset_left _ _), 
  },
  rcases this with ⟨f, ⟨hFJI, hfC⟩⟩,
  set J' := (J ∪ {e}) \ f with hdefJ', 
  

  --- test case for set tactic 
  have hJ'₀: J' \ I ⊆ (J ∪ I) := by {sorry,}, 
  have hJ' : C_to_I M (J') := sorry,
  have hJ's : size I < size J' := sorry, 
  have hJ'ssu : I \ J' ⊂ I \ J := sorry, 
  
  have hIJ' : ¬bad_pair I J' := 
    λ hIJ', hDmin (I \ J') hJ'ssu ⟨I,⟨J',⟨hIJ', rfl⟩⟩⟩, 
  push_neg at hIJ', rcases hIJ' hJ's hI hJ' with ⟨g,⟨hg₁,hg₂⟩⟩ ,

  by_cases g ∈ J \ I,
  from h_non_aug g h hg₂, 
  rw [←elem_compl_iff] at h,  
  have := elem_inter hg₁ h, 
  rw [diff_eq, diff_eq, compl_inter, compl_compl, inter_distrib_left, inter_right_comm J', inter_right_comm _ _ I, 
      inter_assoc _ I _ ,inter_compl, inter_empty, union_empty, hdefJ', diff_eq, inter_assoc, inter_right_comm, 
      inter_distrib_right, ←inter_assoc, inter_compl, empty_inter, empty_union, inter_right_comm, ←compl_union] at this, -- tactic plz 
  have := mem_of_mem_of_subset this (inter_subset_right _ _),
  have := (elem_inter (mem_of_mem_of_subset hg₁ hJ'₀) this),
  rw inter_compl at this, from not_mem_empty g this, 
end 

end cct_family 


def indep_family.of_cct_family (M : cct_family U) : indep_family U :=
  ⟨M.C_to_I, M.C_to_I1, M.C_to_I2, M.C_to_I3⟩ 


namespace matroid 

def of_cct_family (M : cct_family U) : matroid U :=
  of_indep_family (indep_family.of_cct_family M)
 
lemma cct_of_cct_family (M : cct_family U) :
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
import ftype.basic ftype.induction ftype.collections .rankfun 
open ftype 

open_locale classical
noncomputable theory 
----------------------------------------------------------------

section indep 

variables {U :ftype}

/-- removing an element from an independent set preserves independence-/
def satisfies_weak_I2 : (set U → Prop) → Prop :=
  λ indep, ∀ I (e : U), e ∉ I → indep (I ∪ e) → indep I 

lemma weak_I2_to_I2 (indep : set U → Prop):  
  satisfies_weak_I2 indep → satisfies_I2  indep :=
  begin
    intros hwI2 I J hIJ hJ, 
    rcases minimal_example (λ K, I ⊆ K ∧ indep K) ⟨hIJ, hJ⟩ with ⟨K,⟨hKs,⟨⟨hIK,hKind⟩,hmin⟩⟩⟩,
    by_cases I = K, rw ←h at hKind, assumption, 
    rcases aug_of_ssubset (ssubset_of_subset_ne hIK h) with ⟨K',e,hIK',hK'K,hK'e⟩,
    have heK' : e ∉ K' := by {rw ssubset_of_add_nonelem_iff, rw hK'e, from hK'K },
    from false.elim (hmin K' hK'K ⟨hIK', by {rw ←hK'e at hKind, from hwI2 _ _ heK' hKind}⟩ )
  end

/-- B spans X and is independent -/
def indep.is_set_basis (M : indep_family U) := 
  λ B X, B ⊆ X ∧ M.indep B ∧ ∀ J, B ⊂ J → J ⊆ X → ¬M.indep J

lemma indep.extends_to_basis {M : indep_family U} {I X : set U} :
  I ⊆ X → M.indep I → ∃ B, I ⊆ B ∧ indep.is_set_basis M B X :=
  begin
    intros h₁ h₂, 
    rcases maximal_example (λ I, (I ⊆ X ∧ M.indep I)) ⟨h₁, h₂⟩ with ⟨B, ⟨hB, ⟨h₁B, h₂B⟩⟩⟩, use B, 
    from ⟨hB, ⟨h₁B.1,⟨h₁B.2,λ J h₁J h₂J, not_and.mp (h₂B J h₁J) h₂J⟩⟩⟩
  end 

/-- choose extension of an independent set I to a basis of X-/
def indep.choose_extension_to_basis (M : indep_family U) {I X : set U} (hIX : I ⊆ X) (hInd : M.indep I) : set U := 
  classical.some (indep.extends_to_basis hIX hInd)

/-- choose a basis of X -/
def indep.choose_set_basis (M : indep_family U) (X : set U) :=
  indep.choose_extension_to_basis M (empty_subset X) (M.I1)

/-- properties of the choice of a basis of X-/
def indep.choose_extension_to_basis_spec (M : indep_family U) {I X : set U} (hIX : I ⊆ X) (hInd : M.indep I) : _ := 
  classical.some_spec (indep.extends_to_basis hIX hInd)

lemma indep.choice_of_extension_to_basis_is_valid (M : indep_family U) {I X : set U} (hIX : I ⊆ X) (hInd : M.indep I) : 
  I ⊆ (indep.choose_extension_to_basis M hIX hInd) ∧ indep.is_set_basis M (indep.choose_extension_to_basis M hIX hInd) X :=
  classical.some_spec (indep.extends_to_basis hIX hInd)

lemma indep.choice_of_set_basis_is_valid (M : indep_family U) (X : set U) : 
  indep.is_set_basis M (indep.choose_set_basis M X) X :=
  (indep.choice_of_extension_to_basis_is_valid M (empty_subset X) (M.I1)).2 

lemma indep.has_ext_to_basis (M : indep_family U) {I X : set U}: 
  I ⊆ X → M.indep I → ∃ B, I ⊆ B ∧ indep.is_set_basis M B X := 
  λ hIX hI, by {use indep.choose_extension_to_basis M hIX hI, 
                  from indep.choice_of_extension_to_basis_is_valid M hIX hI}

lemma indep.has_basis (M : indep_family U) (X : set U):
  ∃ B, indep.is_set_basis M B X := 
  by {use indep.choose_set_basis M X, from indep.choice_of_set_basis_is_valid M X}

lemma indep.size_ind_le_size_set_basis {M : indep_family U}{I B X : set U}:
  I ⊆ X → M.indep I → indep.is_set_basis M B X → size I ≤ size B := 
  begin
    intros hIX hI hB, by_contra hlt, push_neg at hlt, 
    rcases M.I3 B I hlt hB.2.1 hI with ⟨e, ⟨h₁e, h₂e⟩ ⟩, 
    rw elem_diff_iff at h₁e, refine hB.2.2 (B ∪ e) _ _ h₂e, 
    from ssub_of_add_nonelem h₁e.2, 
    from union_of_subsets hB.1 (subset_of_elem_of_subset h₁e.1 hIX),
  end

lemma indep.set_bases_equicardinal {M : indep_family U}{X B₁ B₂ : set U} :
  indep.is_set_basis M B₁ X → indep.is_set_basis M B₂ X → size B₁ = size B₂ :=
begin
  intros h₁ h₂, apply le_antisymm, 
  from indep.size_ind_le_size_set_basis h₁.1 h₁.2.1 h₂, 
  from indep.size_ind_le_size_set_basis h₂.1 h₂.2.1 h₁, 
end 

--lemma basis_ext_inter_set {M : indep_family U}{X B₁ }

def indep.I_to_r {U : ftype}(M : indep_family U) : (set U → ℤ) := 
  λ X, size (indep.choose_set_basis M X)

lemma indep.I_to_r_max (M : indep_family U)(X : set U): 
  ∃ B, B ⊆ X ∧ M.indep B ∧ size B = indep.I_to_r M X := 
  by {use indep.choose_set_basis M X, have h := indep.choice_of_set_basis_is_valid M X, 
            from ⟨h.1,⟨h.2.1,rfl⟩⟩}
    
lemma indep.I_to_r_ub {M : indep_family U}{I X : set U}: 
  I ⊆ X → M.indep I → size I ≤ indep.I_to_r M X := 
begin
  intros hI hInd, by_contra a, push_neg at a, 
  let J := indep.choose_set_basis M X, 
  have : indep.is_set_basis M J X := indep.choice_of_set_basis_is_valid M X, 
  have := indep.size_ind_le_size_set_basis hI hInd this, 
  have : indep.I_to_r M X = size J := rfl, 
  linarith, 
end 

lemma indep.I_to_r_eq_iff {U : ftype}{M : indep_family U}{X : set U}{n : ℤ} :
  indep.I_to_r M X = n ↔ ∃ B, indep.is_set_basis M B X ∧ size B = n :=
  let B₀ := indep.choose_set_basis M X, hB₀ := indep.choice_of_set_basis_is_valid M X in 
begin
  refine ⟨λ h, ⟨B₀, ⟨hB₀,by {rw ←h, refl}⟩⟩, λ h,_⟩, 
  rcases h with ⟨B, ⟨hB, hBsize⟩⟩, 
  from (rfl.congr hBsize).mp (eq.symm (indep.set_bases_equicardinal hB hB₀)), 
end

lemma indep.has_set_basis_with_size {U : ftype}(M : indep_family U)(X : set U) : 
  ∃ B, indep.is_set_basis M B X ∧ size B = indep.I_to_r M X :=
  indep.I_to_r_eq_iff.mp (rfl : indep.I_to_r M X = indep.I_to_r M X)
 



lemma indep.I_to_r_of_set_basis {M : indep_family U}{B X : set U}:
  indep.is_set_basis M B X → indep.I_to_r M X = size B := 
  λ h, indep.set_bases_equicardinal (indep.choice_of_set_basis_is_valid M X) h

lemma indep.has_nested_basis_pair (M : indep_family U){X Y : set U}:
  X ⊆ Y → ∃ BX BY, BX ⊆ BY ∧ indep.is_set_basis M BX X ∧ indep.is_set_basis M BY Y :=
  by
  {
    intro hXY, rcases indep.has_basis M X with ⟨BX,hBX⟩, 
    rcases indep.has_ext_to_basis M (subset_trans hBX.1 hXY) hBX.2.1 with ⟨BY, hBY⟩, 
    use BX, use BY, from ⟨hBY.1,⟨hBX, hBY.2⟩⟩, 
  }



-----------------------------------------------------------------------

lemma indep.I_to_R0 (M : indep_family U): 
  satisfies_R0 (indep.I_to_r M) := 
  λ X, by {have := indep.I_to_r_ub (empty_subset X) (M.I1), rw size_empty at this, assumption}

lemma indep.I_to_R1 (M : indep_family U): 
  satisfies_R1 (indep.I_to_r M) := 
  λ X, by {rcases indep.I_to_r_max M X with ⟨B, ⟨hBX, ⟨_, hsB⟩⟩⟩, from (eq.symm hsB).trans_le (size_monotone hBX)}

lemma indep.I_to_r_of_indep (M : indep_family U)(I : set U): 
  M.indep I → indep.I_to_r M I = size I :=
  λ h, le_antisymm (indep.I_to_R1 M I) (indep.I_to_r_ub (subset_refl I) h)

lemma indep.I_to_R2 (M : indep_family U): 
  satisfies_R2 (indep.I_to_r M) := 
  begin 
    intros X Y hXY, rcases indep.I_to_r_max M X with ⟨B,⟨hBX,⟨hIB,hsB⟩⟩⟩, 
    have := indep.I_to_r_ub (subset_trans hBX hXY) hIB, rw hsB at this, assumption
  end 

lemma I_to_r_eq_rank_basis_union {M : indep_family U}{B X: set U}(Y : set U):
  indep.is_set_basis M B X → indep.I_to_r M (B ∪ Y) = indep.I_to_r M (X ∪ Y) := 
  begin
    intro h, 
    rcases indep.has_ext_to_basis M (subset_trans (h.1) (subset_union_left X Y)) h.2.1 with ⟨BU, ⟨hUs, hUb⟩⟩,
    have := indep.I_to_r_ub (_ : BU ⊆ B ∪ Y) hUb.2.1,  
    have := indep.I_to_R2 M _ _ (subset_union_subset_left B X Y h.1), 
    have := indep.I_to_r_of_set_basis hUb, linarith, 
    have : B = BU ∩ X := by
    {
      have := indep.I_to_r_ub (inter_subset_right BU X) (M.I2 _ _ (inter_subset_left BU X) hUb.2.1),
      rw [indep.I_to_r_of_set_basis h] at this, 
      from eq_of_ge_size_subset (subset_of_inter_mpr hUs h.1) this, 
    },
    have h' := subset_def_inter_mp hUb.1, rw [inter_distrib_left, ←this] at h', 
    rw ←h', from subset_union_subset_right _ _ _ (inter_subset_right BU Y),
  end


lemma indep.I_to_R3 (M : indep_family U): 
  satisfies_R3 (indep.I_to_r M) := 
  begin
    intros X Y, 
    rcases indep.has_nested_basis_pair M (inter_subset_left X Y) with ⟨BI, BX, ⟨hss, ⟨hBI, hBX⟩⟩⟩,   
    rcases indep.has_ext_to_basis M (subset_trans hBI.1 (inter_subset_right X Y)) hBI.2.1 with ⟨BY, ⟨hBIBY,hBY⟩⟩, 
    rcases indep.has_ext_to_basis M (subset_union_left BX BY) hBX.2.1 with ⟨BU, ⟨hBXBU,hBU⟩⟩, 
    rw [←I_to_r_eq_rank_basis_union Y hBX, union_comm BX _, ←I_to_r_eq_rank_basis_union BX hBY, union_comm BY], 
    rw [indep.I_to_r_of_set_basis hBI, indep.I_to_r_of_set_basis hBX, 
        indep.I_to_r_of_set_basis hBU, indep.I_to_r_of_set_basis hBY],
    have := size_monotone hBU.1, have := size_monotone (subset_of_inter_mpr hss hBIBY),
    linarith[size_modular BX BY]
  end 

def indep_family_to_rankfun (M : indep_family U) : rankfun U := 
  ⟨indep.I_to_r M, indep.I_to_R0 M, indep.I_to_R1 M, indep.I_to_R2 M, indep.I_to_R3 M⟩  




end indep 
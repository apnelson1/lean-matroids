
import rankfun boolalg boolalg_induction  boolalg_collections tactic.wlog matroid_basic
open boolalg 

local attribute [instance] classical.prop_decidable
noncomputable theory 
----------------------------------------------------------------

section rank 

variables {U :boolalg}

def satisfies_R0 : (U → ℤ) → Prop := 
  λ r, ∀ X, 0 ≤ r X 

def satisfies_R1 : (U → ℤ) → Prop := 
  λ r, ∀ X, r X ≤ size X

def satisfies_R2 : (U → ℤ) → Prop := 
  λ r, ∀ X Y, X ⊆ Y → r X ≤ r Y 

def satisfies_R3 : (U → ℤ) → Prop := 
  λ r, ∀ X Y, r (X ∪ Y) + r (X ∩ Y) ≤ r X + r Y

end rank 
section indep 

variables {U :boolalg}

def satisfies_I1 : (U → Prop) → Prop := 
  λ indep, indep ⊥ 

def satisfies_I2 : (U → Prop) → Prop := 
  λ indep, ∀ I J: U, I ⊆ J → indep J → indep I

def satisfies_I3 : (U → Prop) → Prop := 
  λ indep, ∀ I J, size I < size J → indep I → indep J → ∃ e, e ∈ J \ I ∧ indep (I ∪ e)

@[ext] structure indep_family (U : boolalg):= 
  (indep : U → Prop)
  (I1 : satisfies_I1 indep)
  (I2 : satisfies_I2 indep)
  (I3 : satisfies_I3 indep)

def satisfies_weak_I2 : (U → Prop) → Prop :=
  λ indep, ∀ I (e : single U), indep (I ∪ e) → indep I 

lemma weak_I2_to_I2 (indep : U → Prop):  
  satisfies_weak_I2 indep → satisfies_I2  indep :=
  begin
    intros h I J hIJ hJ, 
    rcases minimal_example (λ K, I ⊆ K ∧ indep K) ⟨hIJ, hJ⟩ with ⟨K,⟨hKs,⟨⟨hIK,hKind⟩,hmin⟩⟩⟩,
    by_cases I = K, rw ←h at hKind, assumption, 
    rcases aug_of_ssubset ⟨hIK, h⟩ with ⟨K',⟨e,⟨_,⟨_,_⟩⟩⟩⟩, 

  end



def indep.is_set_basis (M : indep_family U) := 
  λ B X, B ⊆ X ∧ M.indep B ∧ ∀ J, B ⊂ J → J ⊆ X → ¬M.indep J

lemma indep.extends_to_basis {M : indep_family U} {I X : U} :
  I ⊆ X → M.indep I → ∃ B, I ⊆ B ∧ indep.is_set_basis M B X :=
  begin
    intros h₁ h₂, 
    rcases maximal_example (λ I, (I ⊆ X ∧ M.indep I)) ⟨h₁, h₂⟩ with ⟨B, ⟨hB, ⟨h₁B, h₂B⟩⟩⟩, use B, 
    from ⟨hB, ⟨h₁B.1,⟨h₁B.2,λ J h₁J h₂J, not_and.mp (h₂B J h₁J) h₂J⟩⟩⟩
  end 

def indep.choose_extension_to_basis (M : indep_family U) {I X : U} (hIX : I ⊆ X) (hInd : M.indep I) : U := 
  classical.some (indep.extends_to_basis hIX hInd)

def indep.choose_set_basis (M : indep_family U) (X : U) :=
  indep.choose_extension_to_basis M (bot_subset X) (M.I1)

def indep.choose_extension_to_basis_spec (M : indep_family U) {I X : U} (hIX : I ⊆ X) (hInd : M.indep I) : _ := 
  classical.some_spec (indep.extends_to_basis hIX hInd)

lemma indep.choice_of_extension_to_basis_is_valid (M : indep_family U) {I X : U} (hIX : I ⊆ X) (hInd : M.indep I) : 
  I ⊆ (indep.choose_extension_to_basis M hIX hInd) ∧ indep.is_set_basis M (indep.choose_extension_to_basis M hIX hInd) X :=
  classical.some_spec (indep.extends_to_basis hIX hInd)

lemma indep.choice_of_set_basis_is_valid (M : indep_family U) (X : U) : 
  indep.is_set_basis M (indep.choose_extension_to_basis M (bot_subset X) (M.I1)) X :=
  (indep.choice_of_extension_to_basis_is_valid M (bot_subset X) (M.I1)).2 

def indep.has_ext_to_basis (M : indep_family U) {I X : U}: 
  I ⊆ X → M.indep I → ∃ B, I ⊆ B ∧ indep.is_set_basis M B X := 
  λ hIX hI, by {use indep.choose_extension_to_basis M hIX hI, 
                  from indep.choice_of_extension_to_basis_is_valid M hIX hI}

def indep.has_basis (M : indep_family U) (X : U):
  ∃ B, indep.is_set_basis M B X := 
  by {use indep.choose_set_basis M X, from indep.choice_of_set_basis_is_valid M X}

lemma indep.size_ind_le_size_set_basis {M : indep_family U}{I B X : U}:
  I ⊆ X → M.indep I → indep.is_set_basis M B X → size I ≤ size B := 
  begin
    intros hIX hI hB, by_contra hlt, push_neg at hlt, 
    rcases M.I3 B I hlt hB.2.1 hI with ⟨e, ⟨h₁e, h₂e⟩ ⟩, 
    rw elem_diff_iff at h₁e, refine hB.2.2 (B ∪ e) _ _ h₂e, 
    from ssub_of_add_nonelem h₁e.2, 
    from union_of_subsets hB.1 (subset_trans h₁e.1 hIX),
  end

lemma indep.set_bases_equicardinal {M : indep_family U}{X B₁ B₂ :U} :
  indep.is_set_basis M B₁ X → indep.is_set_basis M B₂ X → size B₁ = size B₂ :=
  begin
    intros h₁ h₂, apply le_antisymm, 
    from indep.size_ind_le_size_set_basis h₁.1 h₁.2.1 h₂, 
    from indep.size_ind_le_size_set_basis h₂.1 h₂.2.1 h₁, 
  end 

--lemma basis_ext_inter_set {M : indep_family U}{X B₁ }

def indep.I_to_r {U : boolalg}(M : indep_family U) : (U → ℤ) := 
  λ X, size (indep.choose_set_basis M X)

lemma indep.I_to_r_max (M : indep_family U)(X : U): 
  ∃ B, B ⊆ X ∧ M.indep B ∧ size B = indep.I_to_r M X := 
  by {use indep.choose_set_basis M X, have h := indep.choice_of_set_basis_is_valid M X, 
            from ⟨h.1,⟨h.2.1,rfl⟩⟩}
    
lemma indep.I_to_r_ub {M : indep_family U}{I X : U}: 
  I ⊆ X → M.indep I → size I ≤ indep.I_to_r M X := 
  begin
    intros hI hInd, by_contra a, push_neg at a, 
    let J := indep.choose_set_basis M X, 
    have : indep.is_set_basis M J X := indep.choice_of_set_basis_is_valid M X, 
    have := indep.size_ind_le_size_set_basis hI hInd this, 
    have : indep.I_to_r M X = size J := rfl, 
    linarith, 
  end 

lemma indep.I_to_r_of_set_basis {M : indep_family U}{B X : U}:
  indep.is_set_basis M B X → indep.I_to_r M X = size B := 
  λ h, indep.set_bases_equicardinal (indep.choice_of_set_basis_is_valid M X) h

lemma indep.has_nested_basis_pair (M : indep_family U){X Y : U}:
  X ⊆ Y → ∃ BX BY, BX ⊆ BY ∧ indep.is_set_basis M BX X ∧ indep.is_set_basis M BY Y :=
  by{
    intro hXY, rcases indep.has_basis M X with ⟨BX,hBX⟩, 
    rcases indep.has_ext_to_basis M (subset_trans hBX.1 hXY) hBX.2.1 with ⟨BY, hBY⟩, 
    use BX, use BY, from ⟨hBY.1,⟨hBX, hBY.2⟩⟩, 
  }

-----------------------------------------------------------------------

lemma indep.I_to_R0 (M : indep_family U): 
  satisfies_R0 (indep.I_to_r M) := 
  λ X, by {have := indep.I_to_r_ub (bot_subset X) (M.I1), rw size_bot at this, assumption}

lemma indep.I_to_R1 (M : indep_family U): 
  satisfies_R1 (indep.I_to_r M) := 
  λ X, by {rcases indep.I_to_r_max M X with ⟨B, ⟨hBX, ⟨_, hsB⟩⟩⟩, from (eq.symm hsB).trans_le (size_monotone hBX)}

lemma indep.I_to_r_of_indep (M : indep_family U)(I : U): 
  M.indep I → indep.I_to_r M I = size I :=
  λ h, le_antisymm (indep.I_to_R1 M I) (indep.I_to_r_ub (subset_refl I) h)

lemma indep.I_to_R2 (M : indep_family U): 
  satisfies_R2 (indep.I_to_r M) := 
  begin 
    intros X Y hXY, rcases indep.I_to_r_max M X with ⟨B,⟨hBX,⟨hIB,hsB⟩⟩⟩, 
    have := indep.I_to_r_ub (subset_trans hBX hXY) hIB, rw hsB at this, assumption
  end 

lemma I_to_r_eq_rank_basis_union {M : indep_family U}{B X: U}(Y : U):
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
    have h' := inter_subset_mp hUb.1, rw [inter_distrib_left, ←this] at h', 
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

section cct 

variables {U : boolalg}


def satisfies_C1 : (U → Prop) → Prop := 
  λ is_cct, ¬ is_cct ⊥ 

def satisfies_C2 : (U → Prop) → Prop := 
  λ is_cct, ∀ C₁ C₂, is_cct C₁ → is_cct C₂ → ¬(C₁ ⊂ C₂)

def satisfies_C3 : (U → Prop) → Prop := 
  λ is_cct, ∀ C₁ C₂ e, C₁ ≠ C₂ → is_cct C₁ → is_cct C₂ → e ∈ (C₁ ∩ C₂) → ∃ C₀ , is_cct C₀ ∧ C₀ ⊆ (C₁ ∪ C₂) \ e

@[ext] structure cct_family (U : boolalg) :=
  (cct : U → Prop)
  (C1 : satisfies_C1 cct)
  (C2 : satisfies_C2 cct)
  (C3 : satisfies_C3 cct)

def C_to_I (M : cct_family U): (U → Prop) := 
  λ I, ∀ X, X ⊆ I → ¬M.cct X 

lemma C_to_I1 (M : cct_family U) :
  satisfies_I1 (C_to_I M) :=
  by {intros X hX, rw subset_bot hX, from M.C1}

lemma C_to_I2 (M : cct_family U) :
  satisfies_I2 (C_to_I M) :=
  λ I J hIJ hJ X hXI, hJ _ (subset_trans hXI hIJ)

lemma new_circuit_contains_new_elem_C {M : cct_family U}{I C : U}{e : single U}:
  C_to_I M I → C ⊆ (I ∪ e) → M.cct C → e ∈ C :=
  λ hI hCIe hC, by {by_contra he, from hI C (subset_of_subset_add_nonelem hCIe he) hC}

lemma add_elem_unique_circuit_C {M : cct_family U} {I : U} {e : single U}:
  C_to_I M I → ¬C_to_I M (I ∪ e) → ∃! C, M.cct C ∧ C ⊆ I ∪ e :=
  begin
    intros hI hIe, unfold C_to_I at hI hIe, push_neg at hIe, 
    rcases hIe with ⟨C, ⟨hCI, hC⟩⟩, refine ⟨C,⟨⟨hC,hCI⟩,λ C' hC', _⟩⟩,
    have := subset_of_inter_mpr (new_circuit_contains_new_elem_C hI hCI hC) 
                                (new_circuit_contains_new_elem_C hI hC'.2 hC'.1),
    by_contra hCC', 
    cases M.C3 _ _ e (ne.symm hCC') hC hC'.1 this with C₀ hC₀,
    from hI _ (subset_trans hC₀.2 (removal_subset_of (union_of_subsets hCI hC'.2))) hC₀.1,
  end 

lemma add_elem_le_one_circuit_C {M : cct_family U} {I C C': U} (e : single U):
  C_to_I M I → (M.cct C ∧ C ⊆ I ∪ e) → (M.cct C' ∧ C' ⊆ I ∪ e) → C = C' :=
  begin
    intros hI hC hC', 
    by_cases h': C_to_I M (I ∪ e), 
    exfalso, from h' _ hC.2 hC.1,
    rcases (add_elem_unique_circuit_C hI h') with ⟨ C₀,⟨ _,hC₀⟩⟩ , 
    from eq.trans (hC₀ _ hC) (hC₀ _ hC').symm, 
  end

lemma C_to_I3 (M : cct_family U) :
  satisfies_I3 (C_to_I M) :=
  begin
    -- I3 states that there are no bad pairs 
    let bad_pair : U → U → Prop := λ I J, size I < size J ∧ C_to_I M I ∧ C_to_I M J ∧ ∀ e, e ∈ J \ I → ¬C_to_I M (I ∪ e), 
    suffices : ∀ I J, ¬bad_pair I J, 
      push_neg at this, from λ I J hIJ hI hJ, this I J hIJ hI hJ,
    by_contra h, push_neg at h, rcases h with ⟨I₀,⟨J₀, h₀⟩⟩,
    
    --choose a bad pair with D = I-J minimal
    let bad_pair_diff : U → Prop := λ D, ∃ I J, bad_pair I J ∧ I \ J = D, 
    have hD₀ : bad_pair_diff (I₀ \ J₀) := ⟨I₀,⟨J₀,⟨h₀,rfl⟩⟩⟩,
    rcases minimal_example bad_pair_diff hD₀ with ⟨D,⟨_, ⟨⟨I, ⟨J, ⟨hbad, hIJD⟩⟩⟩,hDmin⟩⟩⟩,  
    rcases hbad with ⟨hsIJ, ⟨hI,⟨hJ,h_non_aug⟩ ⟩  ⟩ ,
    rw ←hIJD at hDmin, clear h_left hD₀ h₀ I₀ J₀ hIJD D, 
    ------------------
    have hJI_nonbot : size (J \ I) > 0 := by 
      {have := size_induced_partition I J, rw inter_comm at this, linarith [size_nonneg (I \ J), hsIJ, size_induced_partition J I]},
    
    have hIJ_nonbot : I \ J ≠ ⊥ := by 
    {
      intro h, rw diff_bot_iff_subset at h, 
      cases size_pos_has_elem hJI_nonbot with e he,
      refine h_non_aug e he (C_to_I2 M _ _ (_ : I ∪ e ⊆ J) hJ), 
      from union_of_subsets h (subset_trans he (diff_subset _ _)), 
    },

    cases nonempty_has_elem hIJ_nonbot with e he, -- choose e from I -J

    --There exists f ∈ J-I contained in all ccts of J ∪ e 
    have : ∃ f, f ∈ J \ I ∧ ∀ C, C ⊆ J ∪ e → M.cct C → f ∈ C := by
    {
        by_cases hJe : C_to_I M (J ∪ e) , -- Either J ∪ e has a circuit or doesn't
        
        cases size_pos_has_elem hJI_nonbot with f hf, 
        refine ⟨f, ⟨hf, λ C hCJe hC, _⟩ ⟩, exfalso, 
        from (hJe _ hCJe) hC,
        unfold C_to_I at hJe, push_neg at hJe, rcases hJe with ⟨Ce, ⟨hCe₁, hCe₂⟩⟩ , 

        have : Ce ∩ (J \ I) ≠ ⊥ := λ h,  sorry ,
        cases nonempty_has_elem this with f hf,
        refine ⟨f, ⟨_, λ C hCJe hC, _⟩⟩,  
        apply subset_trans hf (inter_subset_right _ _), 
        rw ←(add_elem_le_one_circuit_C e hJ ⟨hC, hCJe⟩ ⟨hCe₂, hCe₁⟩) at hf,
        from subset_trans hf (inter_subset_left _ _), 
    },
    rcases this with ⟨f, ⟨hFJI, hfC⟩⟩,
    set J' := (J ∪ e) \ f with hdefJ', 
    
    have hJ'₀: J' \ I ⊆ (J ∪ I) := sorry, 
    have hJ' : C_to_I M (J') := sorry,
    have hJ's : size I < size J' := sorry, 
    have hJ'ssu : I \ J' ⊂ I \ J := sorry, 

    have hIJ' : ¬bad_pair I J' := 
      λ hIJ', hDmin (I \ J') hJ'ssu ⟨I,⟨J',⟨hIJ', rfl⟩⟩⟩, 
    push_neg at hIJ', rcases hIJ' hJ's hI hJ' with ⟨g,⟨hg₁,hg₂⟩⟩ ,

    by_cases g ∈ J \ I,
    from h_non_aug g h hg₂, 
    rw [nonelem_simp, ←elem_compl_iff] at h,  
    have := subset_of_inter_mpr hg₁ h, 
    rw [diff_def, diff_def, compl_inter, compl_compl, inter_distrib_left, inter_right_comm J', inter_right_comm _ _ I, 
        inter_assoc _ I _ ,inter_compl, inter_bot, union_bot, hdefJ', diff_def, inter_assoc, inter_right_comm, 
        inter_distrib_right, ←inter_assoc, inter_compl, bot_inter, bot_union, inter_right_comm, ←compl_union] at this, -- tactic plz 
    have := subset_trans this (inter_subset_right _ _),
    have := (subset_of_inter_mpr (subset_trans hg₁ hJ'₀) this),
    rw inter_compl at this, from nonelem_bot g this, 
  end 

  --  λ indep, ∀ I J, size I < size J → indep I → indep J → ∃ e, e ∈ J-I ∧ indep (I ∪ e)


def circuit_family_to_indep_family (M : cct_family U) : indep_family U :=
  ⟨C_to_I M, C_to_I1 M, C_to_I2 M, C_to_I3 M⟩ 

def circuit_family_to_rankfun (M : cct_family U) : rankfun U :=
  indep_family_to_rankfun (circuit_family_to_indep_family M)

end cct 

section basis

variables {U : boolalg}

def collection (U : boolalg) := U → Prop

def satisfies_B1 (basis : collection U) :=
  ∃ B, basis B.
def satisfies_B2 (basis : collection U) :=
  ∀ B₁ B₂, basis B₁ → basis B₂ →
    ∀ b₁, b₁ ∈ B₁ \ B₂ →
          ∃ b₂, (b₂ ∈ B₂ \ B₁) ∧ basis (B₁ \ b₁ ∪ b₂) 

@[ext] structure basis_family (U : boolalg) :=
  (basis : collection U)
  (B1 : satisfies_B1 basis)
  (B2 : satisfies_B2 basis)

lemma basis_have_same_size (M : basis_family U) (B₁ B₂ : U):
  M.basis B₁ → M.basis B₂ → size B₁ = size B₂ := sorry

def basis_to_indep (basis : collection U) : collection U :=
  λ I, ∃ B, basis B ∧ I ⊆ B.

def B_to_I1 (M : basis_family U) : satisfies_I1 (basis_to_indep M.basis) :=
begin
  simp only [basis_to_indep],
  have Hbasis := M.B1,
  cases M.B1 with B H,
    use B,
    split,
      assumption,
      apply bot_subset,
end

def B_to_I2 (M : basis_family U) : satisfies_I2 (basis_to_indep M.basis) :=
begin
  simp only [basis_to_indep, satisfies_I2, and_imp, exists_imp_distrib],
  intros I J HIJ B HB HindepJ,
  use B,
    split,
      assumption,
      apply subset_trans; tidy; assumption,
end

def B_to_I3 (M : basis_family U) : satisfies_I3 (basis_to_indep M.basis) :=
begin
  simp only [basis_to_indep, satisfies_I3, and_imp, exists_imp_distrib],
  intros I₁ I₂ HI₁ltI₂ B₁ HB₁ HIB₁ B₂ HB₂ HJB₂,
  
  -- B₁ = B₂ 

  have HB_case := equal_or_single_in_diff (basis_have_same_size M B₂ B₁ HB₂ HB₁),
  cases HB_case,
    {
      -- Here I and J are part of the same basis B, so we can add any element
      -- from J into_I I and still be contained in B,
      have Hb: ∃ b, b ∈ I₂ \ I₁,
      {
        -- |I| < |J|, so there is such an element.
        sorry,
      },
      cases Hb with b HbJI,
      use b, split,
        assumption,
        use B₁, split,
          assumption,
          have HIbB1 : I₁ ∪ b ⊆ B₁,
          {
            -- this is where it would be nice to_I have a tactic of sorts.
            -- split into_I I ⊆ B₁ and b ∈ B₁,
            -- first by assumption, second by b ∈ J ⊆ B₁
            sorry,
          },
          assumption,
    },
    -- B₁ <> B₂, hence there is an element e ∈ B₁ - B₂
    {
      -- so I₁  ⊆ B1,
      -- so I₂  ⊆ B2,
      have Hcase1 : (I₂ \ B₁ = I₂ \ I₁ ∨ ¬ I₂ \ B₁ = I₂ \ I₁), apply em,
      -- equal
      cases Hcase1,
      {
        have Hminimaldiff := @minimal_example U
          (fun (X : U), 
            ∃ B : U, M.basis B ∧ I₂ ⊆ B ∧ X = B \ (I₂ ∪ B₁))
          (B₂ \ (I₂ ∪ B₁))
          (begin
            use B₂, split,
              assumption,
              split,
                assumption,
                refl,
          end)
        ,
        simp only [not_exists, and_imp, not_and, ne.def, ssubset_iff] at Hminimaldiff,
        rcases Hminimaldiff with 
          ⟨X, ⟨_, ⟨⟨B₂', ⟨HB₂', ⟨HB₂'I₂, HX⟩⟩⟩, 
                    Hminimal⟩⟩⟩,
        -- Two cases: B₂ - (I₂ ∪ B₁) = ⊥ or not
        have Hcase2 : (B₂ \ (I₂ ∪ B₁) = ⊥ ∨ ¬ B₂ \ (I₂ ∪ B₁) = ⊥), apply em,
        cases Hcase2,
        {
          -- empty
          -- set facts
          -- B₂ - I₂ ∪ B₁ is empty,
          -- so everything in B₂ is in I₂ or in B₁,
          -- so the stuff not in B₁ (B₂ - B₁) is just
          -- I₂ - B₁, which from above (Hcase1) is I₂ - I₁
          have HB₂B₁ : B₂ \ B₁ = I₂ \ I₁ := sorry,

          -- Two cases:
          -- either B₁ - (I₁ ∪ B₂) = ⊥ or not
          have Hcase3 : (B₁ \ (I₁ ∪ B₂) = ⊥ ∨ ¬ B₁ \ (I₁ ∪ B₂) = ⊥), apply em,
          cases Hcase3,
          {
            -- empty, derive a contradiction.
            -- symmetrically, as B₁ - I₁ ∪ B₂ is empty,
            -- B₁ - B₂ = I₁ - B₂
            have HB₁B₂ : B₁ \ B₂ = I₁ \ B₂ := sorry,
            have Hsize := basis_have_same_size M B₁ B₂ HB₁ HB₂,
            -- set difference fact : |B₁| = |B₂| → |B₁ - B₂| = |B₂ - B₁| = |B_x| - |B₁ ∩ B₂|
            have Hsizeeq : size (B₁ \ B₂) = size (B₂ \ B₁) := sorry,
            -- now, as B₁ - B₂ ⊆ I₁ - B₂ ⊆ I₁ - I₂,
            -- |I₁ - I₂| ≥ |B₁ - B₂| = |B₂ - B₁| = |I₂ - I₁|,
            -- hence |I₁| ≥ |I₂|
            have : size I₁ ≥ size I₂ := sorry,
            linarith, 
          },
          {
            -- not empty, get goal.
            have Hx : (∃ x, x ∈ B₁ \ (I₁ ∪ B₂)) := sorry,
            cases Hx with x Hx,        
            -- again, tactic...
            have HB₁x : x ∈ B₁ \ B₂ := sorry,
            have := M.B2 B₁ B₂ HB₁ HB₂ x HB₁x,
            rcases this with ⟨y, ⟨_, H⟩⟩,
            use y,
            split,
              rw <- HB₂B₁, assumption,
              use (B₁ \ x) ∪ y, split,
                assumption,
                -- x ∉ I₁, so just set facts here now.
                sorry,
          }
        },
        {
          -- not empty, so there exists x it (probably a boolalg axiom)
          have Hx : (∃ x, x ∈ B₂ \ (I₂ ∪ B₁)) := sorry,
          cases Hx with x Hx,
          -- nice to_I have a tactic here
          have HB₂x : x ∈ B₂ \ B₁ := sorry,
          have := M.B2 B₂ B₁ HB₂ HB₁ x HB₂x,
          rcases this with ⟨y, ⟨_, H⟩⟩,
          set Z := ((B₂ \ x) ∪ y) \ (I₂ ∪ B₁),
          -- derive contradiction of minimality
          exfalso,
          apply (Hminimal Z), -- 5 goals
            -- set facts: if x ∈ (B₂ - x) ∪ y - (I₂ ∪ B₁),
            -- then it is in B₂ - (I₂ ∪ B₁) as y is in B₁.#check
            sorry,
            -- set facts: ¬ Z = X as x ∈ X, x ∉ Z,
            sorry,
            apply H,
            -- set facts : x ∈ B₂ - I₂ ∪ B₁, so x ∉ I₂,
            -- so I₂ ⊆ B₂ - x ⊆ B₂ - x ∪ y,
            sorry,
            -- just the definition of Z,
            refl,
        }
      },
      -- not equal
      {
        -- I₂ - B₁ ≠ I₂ - I₁, as I₁ ⊆ I₂ we have b ∈ I₂ - I₁ ∩ B₁
        have Hb : (∃ e, e ∈ (I₂ \ I₁) ∩ B₁) := sorry,
        cases Hb with b Hb,
        use b,
        split,
          -- b is in the difference (want something to_I turn ∩ <-> ∧)
          sorry,
          -- 
          use B₁, split, assumption,
            -- b ∈ I₁, so we're all good.
            sorry,
      },
    },
end


end basis

section cl /- closure -/ 

variables {U : boolalg}

def satisfies_cl1 : (U → U) → Prop := 
  λ cl, ∀ X, X ⊆ cl X

def satisfies_cl2 : (U → U) → Prop := 
  λ cl, ∀ X, cl (cl X) = cl X

def satisfies_cl3 : (U → U) → Prop := 
  λ cl, ∀ X Y, X ⊆ Y → cl X ⊆ cl Y 

def satisfies_cl4 : (U → U) → Prop :=
  λ cl, ∀ (X : U) (e f : single U), (e ∈ cl (X ∪ f) \ X) → (f ∈ cl (X ∪ e) \ X)

structure clfun (U : boolalg) := 
  (cl : U → U)
  (cl1 : satisfies_cl1 cl)
  (cl2 : satisfies_cl2 cl)
  (cl3 : satisfies_cl3 cl)
  (cl4 : satisfies_cl4 cl)

lemma cl.monotone (M : clfun U){X Y : U} :
  X ⊆ Y → M.cl X ⊆ M.cl Y :=
  λ h, M.cl3 _ _ h

lemma cl.subset_union (M : clfun U)(X Y : U) :
  M.cl X ∪ M.cl Y ⊆ M.cl (X ∪ Y) :=
  union_is_ub (M.cl3 _ _ (subset_union_left X Y)) (M.cl3 _ _ (subset_union_right X Y))
  

lemma cl.cl_union (M : clfun U)(X Y : U) :
  M.cl (X ∪ Y) = M.cl(M.cl X ∪ M.cl Y) :=
  begin
    apply subset_antisymm, 
    from cl.monotone M (union_subset_pairs (M.cl1 X) (M.cl1 Y)),
    have := cl.monotone M (cl.subset_union M X Y),
    rw M.cl2 at this, assumption
  end


lemma cl.union_pair (M : clfun U)(X Y Z: U): 
  M.cl X = M.cl Y → M.cl (X ∪ Z) = M.cl (Y ∪ Z) :=
  λ h, by rw [cl.cl_union _ X, cl.cl_union _ Y, h]


def cl.is_indep (M : clfun U) : U → Prop := 
  λ I, ∀ X, X ⊂ I → M.cl X ⊂ I 

lemma cl.satisfies_I1 (M : clfun U) : 
  satisfies_I1 (cl.is_indep M) :=
  λ X h, false.elim (ssubset_bot X h)
  
lemma cl.satisfies_I2 (M : clfun U) : 
  satisfies_I2 (cl.is_indep M) :=
  λ I J hIJ hJ X hX, by {have := hJ _ (ssubset_subset_trans hX hIJ), }

lemma cl.satisfies_I3 (M : clfun U) : 
  satisfies_I3 (cl.is_indep M) :=
  sorry 

def clfun_to_indep_family (M : clfun U) : indep_family U := 
⟨cl.is_indep M, cl.satisfies_I1 M, cl.satisfies_I2 M, cl.satisfies_I3 M⟩

def clfun_to_rankfun (M : clfun U) : rankfun U := 
  indep_family_to_rankfun (clfun_to_indep_family M)

end cl

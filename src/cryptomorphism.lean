
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
  λ indep, ∀ I J, size I < size J → indep I → indep J → ∃ e, e ∈ J-I ∧ indep (I ∪ e)

@[ext] structure indep_family (U : boolalg):= 
  (indep : U → Prop)
  (I1 : satisfies_I1 indep)
  (I2 : satisfies_I2 indep)
  (I3 : satisfies_I3 indep)

def is_set_basis_I (M : indep_family U) := 
  λ B X, B ⊆ X ∧ M.indep B ∧ ∀ J, B ⊂ J → J ⊆ X → ¬M.indep J

lemma extends_to_basis_I {M : indep_family U} {I X : U} :
  I ⊆ X → M.indep I → ∃ B, I ⊆ B ∧ is_set_basis_I M B X :=
  begin
    intros h₁ h₂, 
    rcases maximal_example (λ I, (I ⊆ X ∧ M.indep I)) ⟨h₁, h₂⟩ with ⟨B, ⟨hB, ⟨h₁B, h₂B⟩⟩⟩, use B, 
    exact ⟨hB, ⟨h₁B.1,⟨h₁B.2,λ J h₁J h₂J, not_and.mp (h₂B J h₁J) h₂J⟩⟩⟩
  end 

def choose_extension_to_basis_I (M : indep_family U) {I X : U} (hIX : I ⊆ X) (hInd : M.indep I) : U := 
  classical.some (extends_to_basis_I hIX hInd)

def choose_set_basis_I (M : indep_family U) (X : U) :=
  choose_extension_to_basis_I M (bot_subset X) (M.I1)

def choose_extension_to_basis_spec_I (M : indep_family U) {I X : U} (hIX : I ⊆ X) (hInd : M.indep I) : _ := 
  classical.some_spec (extends_to_basis_I hIX hInd)

lemma choice_of_extension_to_basis_is_valid_I (M : indep_family U) {I X : U} (hIX : I ⊆ X) (hInd : M.indep I) : 
  I ⊆ (choose_extension_to_basis_I M hIX hInd) ∧ is_set_basis_I M (choose_extension_to_basis_I M hIX hInd) X :=
  classical.some_spec (extends_to_basis_I hIX hInd)

lemma choice_of_set_basis_is_valid_I (M : indep_family U) (X : U) : 
  is_set_basis_I M (choose_extension_to_basis_I M (bot_subset X) (M.I1)) X :=
  (choice_of_extension_to_basis_is_valid_I M (bot_subset X) (M.I1)).2 

def has_ext_to_basis_I (M : indep_family U) {I X : U}: 
  I ⊆ X → M.indep I → ∃ B, I ⊆ B ∧ is_set_basis_I M B X := 
  λ hIX hI, by {use choose_extension_to_basis_I M hIX hI, exact choice_of_extension_to_basis_is_valid_I M hIX hI}

def has_basis_I (M : indep_family U) (X : U):
  ∃ B, is_set_basis_I M B X := 
  by {use choose_set_basis_I M X, exact choice_of_set_basis_is_valid_I M X}

lemma size_ind_le_size_set_basis_I {M : indep_family U}{I B X : U}:
  I ⊆ X → M.indep I → is_set_basis_I M B X → size I ≤ size B := 
  begin
    intros hIX hI hB, by_contra hlt, push_neg at hlt, 
    rcases M.I3 B I hlt hB.2.1 hI with ⟨e, ⟨h₁e, h₂e⟩ ⟩, 
    rw elem_diff_iff at h₁e, refine hB.2.2 (B ∪ e) _ _ h₂e, 
    exact ssub_of_add_nonelem h₁e.2, 
    exact union_of_subsets hB.1 (subset_trans h₁e.1 hIX),
  end

lemma set_bases_equicardinal_I {M : indep_family U}{X B₁ B₂ :U} :
  is_set_basis_I M B₁ X → is_set_basis_I M B₂ X → size B₁ = size B₂ :=
  begin
    intros h₁ h₂, apply le_antisymm, 
    exact size_ind_le_size_set_basis_I h₁.1 h₁.2.1 h₂, 
    exact size_ind_le_size_set_basis_I h₂.1 h₂.2.1 h₁, 
  end 

--lemma basis_ext_inter_set {M : indep_family U}{X B₁ }

def I_to_r {U : boolalg}(M : indep_family U) : (U → ℤ) := 
  λ X, size (choose_set_basis_I M X)

lemma I_to_r_max (M : indep_family U)(X : U): 
  ∃ B, B ⊆ X ∧ M.indep B ∧ size B = I_to_r M X := 
  by {use choose_set_basis_I M X, have h := choice_of_set_basis_is_valid_I M X, exact ⟨h.1,⟨h.2.1,rfl⟩⟩}
    
lemma I_to_r_ub {M : indep_family U}{I X : U}: 
  I ⊆ X → M.indep I → size I ≤ I_to_r M X := 
  begin
    intros hI hInd, by_contra a, push_neg at a, 
    let J := choose_set_basis_I M X, 
    have : is_set_basis_I M J X := choice_of_set_basis_is_valid_I M X, 
    have := size_ind_le_size_set_basis_I hI hInd this, 
    have : I_to_r M X = size J := rfl, 
    linarith, 
  end 

lemma I_to_r_of_set_basis {M : indep_family U}{B X : U}:
  is_set_basis_I M B X → I_to_r M X = size B := 
  λ h, set_bases_equicardinal_I (choice_of_set_basis_is_valid_I M X) h

lemma has_nested_basis_pair (M : indep_family U){X Y : U}:
  X ⊆ Y → ∃ BX BY, BX ⊆ BY ∧ is_set_basis_I M BX X ∧ is_set_basis_I M BY Y :=
  by{
    intro hXY, rcases has_basis_I M X with ⟨BX,hBX⟩, 
    rcases has_ext_to_basis_I M (subset_trans hBX.1 hXY) hBX.2.1 with ⟨BY, hBY⟩, 
    use BX, use BY, exact ⟨hBY.1,⟨hBX, hBY.2⟩⟩, 
  }

-----------------------------------------------------------------------

lemma I_to_R0 (M : indep_family U): 
  satisfies_R0 (I_to_r M) := 
  λ X, by {have := I_to_r_ub (bot_subset X) (M.I1), rw size_bot at this, assumption}

lemma I_to_R1 (M : indep_family U): 
  satisfies_R1 (I_to_r M) := 
  λ X, by {rcases I_to_r_max M X with ⟨B, ⟨hBX, ⟨_, hsB⟩⟩⟩, exact (eq.symm hsB).trans_le (size_monotone hBX)}

lemma I_to_r_of_indep (M : indep_family U)(I : U): 
  M.indep I → I_to_r M I = size I :=
  λ h, le_antisymm (I_to_R1 M I) (I_to_r_ub (subset_refl I) h)

lemma I_to_R2 (M : indep_family U): 
  satisfies_R2 (I_to_r M) := 
  begin 
    intros X Y hXY, rcases I_to_r_max M X with ⟨B,⟨hBX,⟨hIB,hsB⟩⟩⟩, 
    have := I_to_r_ub (subset_trans hBX hXY) hIB, rw hsB at this, assumption
  end 

lemma I_to_r_eq_rank_basis_union {M : indep_family U}{B X: U}(Y : U):
  is_set_basis_I M B X → I_to_r M (B ∪ Y) = I_to_r M (X ∪ Y) := 
  begin
    intro h, 
    rcases has_ext_to_basis_I M (subset_trans (h.1) (subset_union_left X Y)) h.2.1 with ⟨BU, ⟨hUs, hUb⟩⟩,
    have := I_to_r_ub (_ : BU ⊆ B ∪ Y) hUb.2.1,  
    have := I_to_R2 M _ _ (subset_union_subset_left B X Y h.1), 
    have := I_to_r_of_set_basis hUb, linarith, 
    have : B = BU ∩ X := by
    {
      have := I_to_r_ub (inter_subset_right BU X) (M.I2 _ _ (inter_subset_left BU X) hUb.2.1),
      rw [I_to_r_of_set_basis h] at this, 
      exact eq_of_ge_size_subset (subset_of_inter_mpr hUs h.1) this, 
    },
    have h' := inter_subset_mp hUb.1, rw [inter_distrib_left, ←this] at h', 
    rw ←h', exact subset_union_subset_right _ _ _ (inter_subset_right BU Y),
  end


lemma I_to_R3 (M : indep_family U): 
  satisfies_R3 (I_to_r M) := 
  begin
    intros X Y, 
    rcases has_nested_basis_pair M (inter_subset_left X Y) with ⟨BI, BX, ⟨hss, ⟨hBI, hBX⟩⟩⟩,   
    rcases has_ext_to_basis_I M (subset_trans hBI.1 (inter_subset_right X Y)) hBI.2.1 with ⟨BY, ⟨hBIBY,hBY⟩⟩, 
    rcases has_ext_to_basis_I M (subset_union_left BX BY) hBX.2.1 with ⟨BU, ⟨hBXBU,hBU⟩⟩, 
    rw [←I_to_r_eq_rank_basis_union Y hBX, union_comm BX _, ←I_to_r_eq_rank_basis_union BX hBY, union_comm BY], 
    rw [I_to_r_of_set_basis hBI, I_to_r_of_set_basis hBX, I_to_r_of_set_basis hBU, I_to_r_of_set_basis hBY],
    have := size_monotone hBU.1, have := size_monotone (subset_of_inter_mpr hss hBIBY),
    linarith[size_modular BX BY]
  end 

def indep_family_to_rankfun (M : indep_family U) : rankfun U := 
  ⟨I_to_r M, I_to_R0 M, I_to_R1 M, I_to_R2 M, I_to_R3 M⟩  

end indep 

section circuit 

variables {U : boolalg}


def satisfies_C1 : (U → Prop) → Prop := 
  λ is_cct, ¬ is_cct ⊥ 

def satisfies_C2 : (U → Prop) → Prop := 
  λ is_cct, ∀ C₁ C₂, is_cct C₁ → is_cct C₂ → ¬(C₁ ⊂ C₂)

def satisfies_C3 : (U → Prop) → Prop := 
  λ is_cct, ∀ C₁ C₂ e, C₁ ≠ C₂ → is_cct C₁ → is_cct C₂ → e ∈ (C₁ ∩ C₂) → ∃ C₀ , is_cct C₀ ∧ C₀ ⊆ (C₁ ∪ C₂ - e)

@[ext] structure cct_family (U : boolalg) :=
  (cct : U → Prop)
  (C1 : satisfies_C1 cct)
  (C2 : satisfies_C2 cct)
  (C3 : satisfies_C3 cct)

def C_to_I (M : cct_family U): (U → Prop) := 
  λ I, ∀ X, X ⊆ I → ¬M.cct X 

lemma C_to_I1 (M : cct_family U) :
  satisfies_I1 (C_to_I M) :=
  by {intros X hX, rw subset_bot hX, exact M.C1}

lemma C_to_I2 (M : cct_family U) :
  satisfies_I2 (C_to_I M) :=
  λ I J hIJ hJ X hXI, hJ _ (subset_trans hXI hIJ)

lemma new_circuit_contains_new_elem_C {M : cct_family U}{I C : U}{e : single U}:
  C_to_I M I → C ⊆ (I ∪ e) → M.cct C → e ∈ C :=
  λ hI hCIe hC, by {by_contra he, exact hI C (subset_of_subset_addition hCIe he) hC}

lemma add_elem_unique_circuit_C {M : cct_family U} {I : U} {e : single U}:
  C_to_I M I → ¬C_to_I M (I ∪ e) → ∃! C, M.cct C ∧ C ⊆ I ∪ e :=
  begin
    intros hI hIe, unfold C_to_I at hI hIe, push_neg at hIe, 
    rcases hIe with ⟨C, ⟨hCI, hC⟩⟩, refine ⟨C,⟨⟨hC,hCI⟩,λ C' hC', _⟩⟩,
    have := subset_of_inter_mpr (new_circuit_contains_new_elem_C hI hCI hC) 
                                (new_circuit_contains_new_elem_C hI hC'.2 hC'.1),
    by_contra hCC', 
    cases M.C3 _ _ e (ne.symm hCC') hC hC'.1 this with C₀ hC₀,
    have : C ∪ C' - e ⊆ I := by {refine subset_of_subset_addition  (_ : e ∉ C ∪ C') (_ : C ∪ C' ⊆ I ∪ e), }


  end 


lemma C_to_I3 (M : cct_family U) :
  satisfies_I3 (C_to_I M) :=
  begin
    
    intros I J hIJ hI hJ, by_contra h, push_neg at h, 
    let P_counterex : U → Prop := λ K, C_to_I M K ∧ ∀ e, e ∈ K-I → ¬C_to_I M (I ∪ e), 

    rcases maximal_example P_counterex ⟨hJ, h⟩ with ⟨J₁, hJJ₁, ⟨hJ₁, hJ₁max⟩⟩, 
    clear h hJ, 
    have J_max_ind : ∀ e, e ∈ I - J → ∃ C, M.cct C ∧ C ⊆ J ∪ e :=
    begin
      by_contra hc, push_neg at hc, rcases hc with ⟨e, ⟨heIJ, heJind⟩⟩ , 
      
    end
    --unfold C_to_I at h, 
    --have : ∀ e, e ∈ J-I → ∃ C f, f ∈ I-J ∧ M.cct C ∧ e ∈ C ∧ f ∈ C
    
    
  end 

  --  λ indep, ∀ I J, size I < size J → indep I → indep J → ∃ e, e ∈ J-I ∧ indep (I ∪ e)


def circuit_family_to_indep_family (M : cct_family U) : indep_family U :=
  ⟨C_to_I M, C_to_I1 M, C_to_I2 M, C_to_I3 M⟩ 

def circuit_family_to_rankfun (M : cct_family U) : rankfun U :=
  indep_family_to_rankfun (circuit_family_to_indep_family M)

end circuit 



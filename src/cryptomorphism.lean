
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
  λ I_prop, I_prop ⊥ 

def satisfies_I2 : (U → Prop) → Prop := 
  λ I_prop, ∀ I J: U, I ⊆ J → I_prop I → I_prop J

def satisfies_I3 : (U → Prop) → Prop := 
  λ I_prop, ∀ I J, size I < size J → I_prop I → I_prop J → ∃ e, e ∈ J-I ∧ I_prop (I ∪ e)

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

def has_extension_to_basis_I (M : indep_family U) {I X : U}: 
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

def I_to_r {U : boolalg }: indep_family U → (U → ℤ) := 
  λ M X, size (choose_set_basis_I M X)

lemma I_to_r_max (M : indep_family U)(X : U): 
  ∃ B, B ⊆ X ∧ M.indep B ∧ size B = I_to_r M X := 
  by {use choose_set_basis_I M X, have h := choice_of_set_basis_is_valid_I M X, exact ⟨h.1,⟨h.2.1,rfl⟩⟩}
    
lemma I_to_r_ub {M : indep_family U}(X : U): 
  ∀ I, I ⊆ X → M.indep I → size I ≤ I_to_r M X := 
  begin
    intros I hI hInd, by_contra a, push_neg at a, 
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
    rcases has_extension_to_basis_I M (subset_trans hBX.1 hXY) hBX.2.1 with ⟨BY, hBY⟩, 
    use BX, use BY, exact ⟨hBY.1,⟨hBX, hBY.2⟩⟩, 
  }

-----------------------------------------------------------------------

lemma I_to_R0 (M : indep_family U): 
  satisfies_R0 (I_to_r M) := 
  λ X, by {have := I_to_r_ub X ⊥ (bot_subset X) (M.I1), rw size_bot at this, assumption}

lemma I_to_R1 (M : indep_family U): 
  satisfies_R1 (I_to_r M) := 
  λ X, by {rcases I_to_r_max M X with ⟨B, ⟨hBX, ⟨_, hsB⟩⟩⟩, exact (eq.symm hsB).trans_le (size_monotone hBX)}

lemma I_to_r_of_indep (M : indep_family U)(I : U): 
  M.indep I → I_to_r M I = size I :=
  λ h, le_antisymm (I_to_R1 M I) (I_to_r_ub I I (subset_refl I) h)

lemma I_to_R2 (M : indep_family U): 
  satisfies_R2 (I_to_r M) := 
  λ X Y hXY, by {rcases I_to_r_max M X with ⟨B,⟨hBX,⟨hIB,hsB⟩⟩⟩, have := I_to_r_ub Y B (subset_trans hBX hXY) hIB, rw hsB at this, assumption}
  

lemma I_to_r_eq_rank_basis_union {M : indep_family U}{B X Y : U}:
  is_set_basis_I M B X → I_to_r M (B ∪ Y) = I_to_r M (X ∪ Y) := 
  begin
    intro h, 
    rcases has_nested_basis_pair M (subset_union_left X Y) with  ⟨BX, BXY, ⟨hXY, ⟨hBX,hBXY⟩⟩⟩,
    sorry  
  end


lemma I_to_R3 (M : indep_family U): 
  satisfies_R3 (I_to_r M) := 
  begin
    intros X Y, 
    rcases has_basis_I M (X ∩ Y) with ⟨BI,hBI⟩, 
    rcases has_extension_to_basis_I M (subset_trans hBI.1 (inter_subset_left X Y)) hBI.2.1 with ⟨BX, hBX⟩, 
    rcases has_extension_to_basis_I M (subset_trans hBI.1 (inter_subset_right X Y)) hBI.2.1 with ⟨BY, hBY⟩,    
    rcases has_extension_to_basis_I M (subset_trans hBX.2.1 (subset_union_left X Y)) hBX.2.2.1 with ⟨BU, hBU⟩, 
    rw [I_to_r_of_set_basis hBI, I_to_r_of_set_basis hBU.2, I_to_r_of_set_basis hBX.2, I_to_r_of_set_basis hBY.2], 
    sorry 
    --rcases I_to_r_max M (X ∩ Y) with ⟨B₀, ⟨hB₀, ⟨hIB₀, hsB₀⟩⟩⟩, sorry 
  end 

def I_to_rfun: indep_family U → rankfun U := 
  λ M, ⟨I_to_r M, I_to_R0 M, I_to_R1 M, I_to_R2 M, I_to_R3 M⟩  


end indep 


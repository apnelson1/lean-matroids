import ftype.basic ftype.induction ftype.collections .rankfun 
open ftype 

open_locale classical
noncomputable theory 
----------------------------------------------------------------

variables {U :ftype}

namespace indep_family' 

def r (M : indep_family' U) : (set U) → ℤ := 
  λ X, classical.some (M.I3' X)


def basis_of (M : indep_family' U)(B X : set U) :=
  B ⊆ X ∧ M.indep B ∧ (∀ Y, B ⊂ Y → Y ⊆ X → ¬M.indep Y)

lemma r_spec (M : indep_family' U) (X : set U): 
  ∀ B, M.basis_of B X → size B = M.r X :=
classical.some_spec (M.I3' X)

lemma extends_to_basis_of (M : indep_family' U)(I X : set U):
  I ⊆ X → M.indep I → ∃ B, I ⊆ B ∧ M.basis_of B X :=
begin
  intros hIX hI, 
  rcases maximal_example (λ B, B ⊆ X ∧ M.indep B) ⟨hIX, hI⟩ with ⟨B, hB₁, hB₂⟩,
  refine ⟨B, hB₁, hB₂.1.1, hB₂.1.2, λ Y hBY hYX hY, _⟩, 
  push_neg at hB₂,
  from hB₂.2 Y hBY hYX hY, 
end

lemma exists_basis_of (M : indep_family' U)(X : set U):
  ∃ B, M.basis_of B X := 
by {have := M.extends_to_basis_of ∅ X (empty_subset _) (M.I1), finish,}



lemma R0 (M : indep_family' U) (X : set U):
  0 ≤ M.r X := 
by {cases exists_basis_of M X with B hB, sorry , }

lemma I3 (M : indep_family' U) : 
  satisfies_I3 M.indep :=
begin
  intros I J hI hJ hIJ, 
  cases M.I3' (I ∪ J) with r hr, 
  sorry, 
end


end indep_family'


namespace indep_family  



--def from_indep_family' (M : indep_family') := 




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
def is_set_basis (M : indep_family U) := 
  λ B X, B ⊆ X ∧ M.indep B ∧ ∀ J, B ⊂ J → J ⊆ X → ¬M.indep J

lemma extends_to_basis {M : indep_family U} {I X : set U} :
  I ⊆ X → M.indep I → ∃ B, I ⊆ B ∧ M.is_set_basis B X :=
  begin
    intros h₁ h₂, 
    rcases maximal_example (λ I, (I ⊆ X ∧ M.indep I)) ⟨h₁, h₂⟩ with ⟨B, ⟨hB, ⟨h₁B, h₂B⟩⟩⟩, use B, 
    from ⟨hB, ⟨h₁B.1,⟨h₁B.2,λ J h₁J h₂J, not_and.mp (h₂B J h₁J) h₂J⟩⟩⟩
  end 

/-- choose extension of an independent set I to a basis of X-/
def choose_extension_to_basis (M : indep_family U) {I X : set U} (hIX : I ⊆ X) (hInd : M.indep I) : set U := 
  classical.some (extends_to_basis hIX hInd)

/-- choose a basis of X -/
def choose_set_basis (M : indep_family U) (X : set U) :=
  M.choose_extension_to_basis (empty_subset X) (M.I1)

/-- properties of the choice of a basis of X-/
def choose_extension_to_basis_spec (M : indep_family U) {I X : set U} (hIX : I ⊆ X) (hInd : M.indep I) : _ := 
  classical.some_spec (extends_to_basis hIX hInd)

lemma choice_of_extension_to_basis_is_valid (M : indep_family U) {I X : set U} (hIX : I ⊆ X) (hInd : M.indep I) : 
  I ⊆ (choose_extension_to_basis M hIX hInd) ∧ is_set_basis M (choose_extension_to_basis M hIX hInd) X :=
  classical.some_spec (extends_to_basis hIX hInd)

lemma choice_of_set_basis_is_valid (M : indep_family U) (X : set U) : 
  is_set_basis M (M.choose_set_basis X) X :=
  (choice_of_extension_to_basis_is_valid M (empty_subset X) (M.I1)).2 

lemma has_ext_to_basis (M : indep_family U) {I X : set U}: 
  I ⊆ X → M.indep I → ∃ B, I ⊆ B ∧ is_set_basis M B X := 
  λ hIX hI, by {use choose_extension_to_basis M hIX hI, 
                  from choice_of_extension_to_basis_is_valid M hIX hI}

lemma has_basis (M : indep_family U) (X : set U):
  ∃ B, M.is_set_basis B X := 
  by {use choose_set_basis M X, from choice_of_set_basis_is_valid M X}

lemma size_ind_le_size_set_basis {M : indep_family U}{I B X : set U}:
  I ⊆ X → M.indep I → M.is_set_basis B X → size I ≤ size B := 
  begin
    intros hIX hI hB, by_contra hlt, push_neg at hlt, 
    rcases M.I3 B I hlt hB.2.1 hI with ⟨e, ⟨h₁e, h₂e⟩ ⟩, 
    rw elem_diff_iff at h₁e, refine hB.2.2 (B ∪ e) _ _ h₂e, 
    from ssub_of_add_nonelem h₁e.2, 
    from union_of_subsets hB.1 (subset_of_elem_of_subset h₁e.1 hIX),
  end

lemma set_bases_equicardinal {M : indep_family U}{X B₁ B₂ : set U} :
  M.is_set_basis B₁ X → M.is_set_basis B₂ X → size B₁ = size B₂ :=
begin
  intros h₁ h₂, apply le_antisymm, 
  from size_ind_le_size_set_basis h₁.1 h₁.2.1 h₂, 
  from size_ind_le_size_set_basis h₂.1 h₂.2.1 h₁, 
end 

--lemma basis_ext_inter_set {M : indep_family U}{X B₁ }

def I_to_r {U : ftype}(M : indep_family U) : (set U → ℤ) := 
  λ X, size (M.choose_set_basis X)

lemma I_to_r_max (M : indep_family U)(X : set U): 
  ∃ B, B ⊆ X ∧ M.indep B ∧ size B = M.I_to_r X := 
  by {use M.choose_set_basis X, have h := M.choice_of_set_basis_is_valid X, 
            from ⟨h.1,⟨h.2.1,rfl⟩⟩}
    
lemma I_to_r_ub {M : indep_family U}{I X : set U}: 
  I ⊆ X → M.indep I → size I ≤ M.I_to_r X := 
begin
  intros hI hInd, by_contra a, push_neg at a, 
  let J := M.choose_set_basis X, 
  have : M.is_set_basis J X := M.choice_of_set_basis_is_valid X, 
  have := size_ind_le_size_set_basis hI hInd this, 
  have : M.I_to_r X = size J := rfl, 
  linarith, 
end 

lemma I_to_r_eq_iff {U : ftype}{M : indep_family U}{X : set U}{n : ℤ} :
  M.I_to_r X = n ↔ ∃ B, M.is_set_basis B X ∧ size B = n :=
  let B₀ := M.choose_set_basis X, hB₀ := M.choice_of_set_basis_is_valid X in 
begin
  refine ⟨λ h, ⟨B₀, ⟨hB₀,by {rw ←h, refl}⟩⟩, λ h,_⟩, 
  rcases h with ⟨B, ⟨hB, hBsize⟩⟩, 
  from (rfl.congr hBsize).mp (eq.symm (set_bases_equicardinal hB hB₀)), 
end

lemma has_set_basis_with_size {U : ftype}(M : indep_family U)(X : set U) : 
  ∃ B, M.is_set_basis B X ∧ size B = M.I_to_r X :=
  I_to_r_eq_iff.mp (rfl : M.I_to_r X = M.I_to_r X)
 
lemma I_to_r_of_set_basis {M : indep_family U}{B X : set U}:
  M.is_set_basis B X → M.I_to_r X = size B := 
  λ h, set_bases_equicardinal (M.choice_of_set_basis_is_valid X) h

lemma has_nested_basis_pair (M : indep_family U){X Y : set U}:
  X ⊆ Y → ∃ BX BY, BX ⊆ BY ∧ M.is_set_basis BX X ∧ M.is_set_basis BY Y :=
begin
  intro hXY, rcases M.has_basis X with ⟨BX,hBX⟩, 
  rcases M.has_ext_to_basis (subset_trans hBX.1 hXY) hBX.2.1 with ⟨BY, hBY⟩, 
  use BX, use BY, from ⟨hBY.1,⟨hBX, hBY.2⟩⟩, 
end



-----------------------------------------------------------------------

lemma I_to_R0 (M : indep_family U): 
  satisfies_R0 M.I_to_r := 
λ X, by {have := I_to_r_ub (empty_subset X) (M.I1), rw size_empty at this, assumption}

lemma I_to_R1 (M : indep_family U): 
  satisfies_R1 M.I_to_r := 
λ X, by {rcases M.I_to_r_max X with ⟨B, ⟨hBX, ⟨_, hsB⟩⟩⟩, from (eq.symm hsB).trans_le (size_monotone hBX)}

lemma I_to_r_of_indep (M : indep_family U)(I : set U): 
  M.indep I → M.I_to_r I = size I :=
λ h, le_antisymm (M.I_to_R1 I) (I_to_r_ub (subset_refl I) h)

lemma I_to_R2 (M : indep_family U): 
  satisfies_R2 M.I_to_r := 
begin 
  intros X Y hXY, rcases M.I_to_r_max X with ⟨B,⟨hBX,⟨hIB,hsB⟩⟩⟩, 
  have := I_to_r_ub (subset_trans hBX hXY) hIB, rw hsB at this, assumption
end 

lemma I_to_r_eq_rank_basis_union {M : indep_family U}{B X: set U}(Y : set U):
  M.is_set_basis B X → M.I_to_r (B ∪ Y) = M.I_to_r (X ∪ Y) := 
begin
  intro h, 
  rcases M.has_ext_to_basis (subset_trans (h.1) (subset_union_left X Y)) h.2.1 with ⟨BU, ⟨hUs, hUb⟩⟩,
  have := I_to_r_ub (_ : BU ⊆ B ∪ Y) hUb.2.1,  
  have := M.I_to_R2 _ _ (subset_union_subset_left B X Y h.1), 
  have := I_to_r_of_set_basis hUb, linarith, 
  have : B = BU ∩ X := by
  {
    have := I_to_r_ub (inter_subset_right BU X) (M.I2 _ _ (inter_subset_left BU X) hUb.2.1),
    rw [I_to_r_of_set_basis h] at this, 
    from eq_of_ge_size_subset (subset_of_inter_mpr hUs h.1) this, 
  },
  have h' := subset_def_inter_mp hUb.1, rw [inter_distrib_left, ←this] at h', 
  rw ←h', from subset_union_subset_right _ _ _ (inter_subset_right BU Y),
end


lemma I_to_R3 (M : indep_family U): 
  satisfies_R3 M.I_to_r := 
begin
  intros X Y, 
  rcases M.has_nested_basis_pair (inter_subset_left X Y) with ⟨BI, BX, ⟨hss, ⟨hBI, hBX⟩⟩⟩,   
  rcases M.has_ext_to_basis (subset_trans hBI.1 (inter_subset_right X Y)) hBI.2.1 with ⟨BY, ⟨hBIBY,hBY⟩⟩, 
  rcases M.has_ext_to_basis (subset_union_left BX BY) hBX.2.1 with ⟨BU, ⟨hBXBU,hBU⟩⟩, 
  rw [←I_to_r_eq_rank_basis_union Y hBX, union_comm BX _, 
          ←I_to_r_eq_rank_basis_union BX hBY, union_comm BY, 
            I_to_r_of_set_basis hBI, I_to_r_of_set_basis hBX, 
              I_to_r_of_set_basis hBU, I_to_r_of_set_basis hBY],
  have := size_monotone hBU.1, have := size_monotone (subset_of_inter_mpr hss hBIBY),
  linarith[size_modular BX BY]
end 

end indep_family 

namespace matroid 

def of_indep_family (MI: indep_family U) : matroid U := 
  ⟨MI.I_to_r, MI.I_to_R0, MI.I_to_R1, MI.I_to_R2, MI.I_to_R3⟩  

lemma indep_of_indep_family (MI : indep_family U) :
  (matroid.of_indep_family MI).is_indep = MI.indep := 
begin
  unfold is_indep of_indep_family, dsimp only, ext X, 
  rcases MI.has_set_basis_with_size X with ⟨B, ⟨hB₁, hB₂, hB₃⟩, hBX⟩, 
  refine ⟨λ h, _, λ h, _⟩,
  rw [←eq_of_eq_size_subset hB₁ _], from hB₂, 
  from eq.trans hBX h, 
  cases subset_ssubset_or_eq hB₁ with h' h',
  from false.elim (hB₃ _  h' (subset_refl _) h), 
  rw h' at hBX, from hBX.symm, 
end


end matroid 
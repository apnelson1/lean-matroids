import prelim.induction prelim.collections .rankfun
open set

universe u

open_locale classical
noncomputable theory
----------------------------------------------------------------

variables {α : Type*} [fintype α]

namespace indep_family


def is_set_basis (M : indep_family α) :=
  λ B X, B ⊆ X ∧ M.indep B ∧ ∀ J, B ⊂ J → J ⊆ X → ¬M.indep J

lemma extends_to_basis {M : indep_family α} {I X : set α} :
  I ⊆ X → M.indep I → ∃ B, I ⊆ B ∧ M.is_set_basis B X :=
  begin
    intros h₁ h₂,
    rcases maximal_example (λ I, (I ⊆ X ∧ M.indep I)) ⟨h₁, h₂⟩ with ⟨B, ⟨hB, ⟨h₁B, h₂B⟩⟩⟩, use B,
    from ⟨hB, ⟨h₁B.1,⟨h₁B.2,λ J h₁J h₂J, not_and.mp (h₂B J h₁J) h₂J⟩⟩⟩
  end

/-- choose extension of an independent set I to a basis of X-/
def choose_extension_to_basis (M : indep_family α) {I X : set α} (hIX : I ⊆ X) (hInd : M.indep I) : set α :=
  classical.some (extends_to_basis hIX hInd)

/-- choose a basis of X -/
def choose_set_basis (M : indep_family α) (X : set α) :=
  M.choose_extension_to_basis (empty_subset X) (M.I1)

/-- properties of the choice of a basis of X-/
def choose_extension_to_basis_spec (M : indep_family α) {I X : set α} (hIX : I ⊆ X) (hInd : M.indep I) : _ :=
  classical.some_spec (extends_to_basis hIX hInd)

lemma choice_of_extension_to_basis_is_valid (M : indep_family α) {I X : set α} (hIX : I ⊆ X) (hInd : M.indep I) :
  I ⊆ (choose_extension_to_basis M hIX hInd) ∧ is_set_basis M (choose_extension_to_basis M hIX hInd) X :=
  classical.some_spec (extends_to_basis hIX hInd)

lemma choice_of_set_basis_is_valid (M : indep_family α) (X : set α) :
  is_set_basis M (M.choose_set_basis X) X :=
  (choice_of_extension_to_basis_is_valid M (empty_subset X) (M.I1)).2

lemma has_ext_to_basis (M : indep_family α) {I X : set α} :
  I ⊆ X → M.indep I → ∃ B, I ⊆ B ∧ is_set_basis M B X :=
  λ hIX hI, by {use choose_extension_to_basis M hIX hI,
                  from choice_of_extension_to_basis_is_valid M hIX hI}

lemma has_basis (M : indep_family α) (X : set α) :
  ∃ B, M.is_set_basis B X :=
  by {use choose_set_basis M X, from choice_of_set_basis_is_valid M X}

lemma size_ind_le_size_set_basis {M : indep_family α} {I B X : set α} :
  I ⊆ X → M.indep I → M.is_set_basis B X → size I ≤ size B :=
  begin
    intros hIX hI hB, by_contra hlt, push_neg at hlt,
    rcases M.I3 B I hlt hB.2.1 hI with ⟨e, ⟨h₁e, h₂e⟩ ⟩,
    rw mem_diff_iff at h₁e, refine hB.2.2 (B ∪ {e}) _ _ h₂e,
    from ssub_of_add_nonmem h₁e.2,
    from union_subset hB.1 (subset_of_mem_of_subset h₁e.1 hIX),
  end

lemma set_bases_equicardinal {M : indep_family α} {X B₁ B₂ : set α} :
  M.is_set_basis B₁ X → M.is_set_basis B₂ X → size B₁ = size B₂ :=
begin
  intros h₁ h₂, apply le_antisymm,
  from size_ind_le_size_set_basis h₁.1 h₁.2.1 h₂,
  from size_ind_le_size_set_basis h₂.1 h₂.2.1 h₁,
end

--lemma basis_ext_inter_set {M : indep_family α} {X B₁ }

def I_to_r (M : indep_family α) : (set α → ℤ) :=
  λ X, size (M.choose_set_basis X)

lemma I_to_r_max (M : indep_family α) (X : set α) :
  ∃ B, B ⊆ X ∧ M.indep B ∧ size B = M.I_to_r X :=
  by {use M.choose_set_basis X, have h := M.choice_of_set_basis_is_valid X,
            from ⟨h.1,⟨h.2.1,rfl⟩⟩}

lemma I_to_r_ub {M : indep_family α} {I X : set α} :
  I ⊆ X → M.indep I → size I ≤ M.I_to_r X :=
begin
  intros hI hInd, by_contra a, push_neg at a,
  let J := M.choose_set_basis X,
  have : M.is_set_basis J X := M.choice_of_set_basis_is_valid X,
  have := size_ind_le_size_set_basis hI hInd this,
  have : M.I_to_r X = size J := rfl,
  linarith,
end

lemma I_to_r_eq_iff {M : indep_family α} {X : set α} {n : ℤ} :
  M.I_to_r X = n ↔ ∃ B, M.is_set_basis B X ∧ size B = n :=
  let B₀ := M.choose_set_basis X, hB₀ := M.choice_of_set_basis_is_valid X in
begin
  refine ⟨λ h, ⟨B₀, ⟨hB₀,by {rw ←h, refl}⟩⟩, λ h,_⟩,
  rcases h with ⟨B, ⟨hB, hBsize⟩⟩,
  from (rfl.congr hBsize).mp (eq.symm (set_bases_equicardinal hB hB₀)),
end

lemma has_set_basis_with_size (M : indep_family α) (X : set α) :
  ∃ B, M.is_set_basis B X ∧ size B = M.I_to_r X :=
  I_to_r_eq_iff.mp (rfl : M.I_to_r X = M.I_to_r X)

lemma I_to_r_of_set_basis {M : indep_family α} {B X : set α} :
  M.is_set_basis B X → M.I_to_r X = size B :=
  λ h, set_bases_equicardinal (M.choice_of_set_basis_is_valid X) h

lemma has_nested_basis_pair (M : indep_family α){X Y : set α} :
  X ⊆ Y → ∃ BX BY, BX ⊆ BY ∧ M.is_set_basis BX X ∧ M.is_set_basis BY Y :=
begin
  intro hXY, rcases M.has_basis X with ⟨BX,hBX⟩,
  rcases M.has_ext_to_basis (subset.trans hBX.1 hXY) hBX.2.1 with ⟨BY, hBY⟩,
  use BX, use BY, from ⟨hBY.1,⟨hBX, hBY.2⟩⟩,
end

-----------------------------------------------------------------------

lemma I_to_R0 (M : indep_family α) :
  satisfies_R0 M.I_to_r :=
λ X, by {have := I_to_r_ub (empty_subset X) (M.I1), rw size_empty at this, assumption}

lemma I_to_R1 (M : indep_family α) :
  satisfies_R1 M.I_to_r :=
λ X, by {rcases M.I_to_r_max X with ⟨B, ⟨hBX, ⟨_, hsB⟩⟩⟩, from (eq.symm hsB).trans_le (size_monotone hBX)}

lemma I_to_r_of_indep (M : indep_family α) (I : set α) :
  M.indep I → M.I_to_r I = size I :=
λ h, le_antisymm (M.I_to_R1 I) (I_to_r_ub (subset_refl I) h)

lemma I_to_R2 (M : indep_family α) :
  satisfies_R2 M.I_to_r :=
begin
  intros X Y hXY, rcases M.I_to_r_max X with ⟨B,⟨hBX,⟨hIB,hsB⟩⟩⟩,
  have := I_to_r_ub (subset.trans hBX hXY) hIB, rw hsB at this, assumption
end

lemma I_to_r_eq_rank_basis_union {M : indep_family α} {B X: set α} (Y : set α) :
  M.is_set_basis B X → M.I_to_r (B ∪ Y) = M.I_to_r (X ∪ Y) :=
begin
  intro h,
  rcases M.has_ext_to_basis (subset.trans (h.1) (subset_union_left X Y)) h.2.1 with ⟨Bα, ⟨hαs, hαb⟩⟩,
  have h₁ := I_to_r_ub (_ : Bα ⊆ B ∪ Y) hαb.2.1,
  { linarith [M.I_to_R2 _ _ (union_subset_union_left Y h.1), I_to_r_of_set_basis hαb]},
  have : B = Bα ∩ X := by
  { have := I_to_r_ub (inter_subset_right Bα X) (M.I2 _ _ (inter_subset_left Bα X) hαb.2.1),
    rw [I_to_r_of_set_basis h] at this,
    exact eq_of_le_size_subset (subset_inter hαs h.1) this, },
  have h' := subset_iff_inter_eq_left.mp hαb.1, rw [inter_distrib_left, ←this] at h',
  rw ←h',
  exact union_subset_union_right _ (inter_subset_right Bα Y),
end

lemma I_to_R3 (M : indep_family α) :
  satisfies_R3 M.I_to_r :=
begin
  intros X Y,
  rcases M.has_nested_basis_pair (inter_subset_left X Y) with ⟨BI, BX, ⟨hss, ⟨hBI, hBX⟩⟩⟩,
  rcases M.has_ext_to_basis (subset.trans hBI.1 (inter_subset_right X Y)) hBI.2.1 with ⟨BY, ⟨hBIBY,hBY⟩⟩,
  rcases M.has_ext_to_basis (subset_union_left BX BY) hBX.2.1 with ⟨Bα, ⟨hBXBα,hBα⟩⟩,
  rw [←I_to_r_eq_rank_basis_union Y hBX, union_comm BX _,
      ←I_to_r_eq_rank_basis_union BX hBY, union_comm BY,
       I_to_r_of_set_basis hBI, I_to_r_of_set_basis hBX,
       I_to_r_of_set_basis hBα, I_to_r_of_set_basis hBY],
  have := size_monotone hBα.1, have := size_monotone (subset_inter hss hBIBY),
  linarith[size_modular BX BY]
end

end indep_family

namespace matroid

def of_indep_family (MI: indep_family α) : matroid α :=
  ⟨MI.I_to_r, MI.I_to_R0, MI.I_to_R1, MI.I_to_R2, MI.I_to_R3⟩

lemma indep_of_indep_family (MI : indep_family α) :
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
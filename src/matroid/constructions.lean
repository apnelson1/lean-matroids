
import ftype.basic ftype.induction ftype.collections
import .rankfun .indep 

open ftype
open matroid 

section truncation 

noncomputable theory 

variables {U : ftype}

def trunc.indep (M : indep_family U) {n : ℤ}(hn : 0 ≤ n) : set U → Prop :=  
  λ X, M.indep X ∧ size X ≤ n

lemma trunc.I1 (M : indep_family U) {n : ℤ} (hn : 0 ≤ n): 
  satisfies_I1 (trunc.indep M hn) := 
  ⟨M.I1, by {rw size_empty, assumption}⟩

lemma trunc.I2 (M : indep_family U) {n : ℤ} (hn : 0 ≤ n) : 
  satisfies_I2 (trunc.indep M hn) := 
  λ I J hIJ hJ, ⟨M.I2 I J hIJ hJ.1, le_trans (size_monotone hIJ) hJ.2⟩ 

lemma trunc.I3 (M : indep_family U) {n : ℤ} (hn : 0 ≤ n): 
  satisfies_I3 (trunc.indep M hn) := 
begin
  intros I J hIJ hI hJ, 
  cases (M.I3 _ _ hIJ hI.1 hJ.1) with e he, 
  refine ⟨e, ⟨he.1, ⟨he.2,_ ⟩ ⟩⟩, 
  by_contra h_con, push_neg at h_con, 
  rw [(add_nonelem_size (elem_diff_iff.mp he.1).2)] at h_con, 
  linarith [int.le_of_lt_add_one h_con, hIJ, hJ.2], 
end

def truncate (M : matroid U){n : ℤ}(hn : 0 ≤ n) : matroid U := 
  let M_ind := M.to_indep_family in 
  matroid.of_indep_family ⟨trunc.indep M_ind hn, trunc.I1 M_ind hn, trunc.I2 M_ind hn, trunc.I3 M_ind hn⟩

-- in retrospect it would probably have been easier to define truncation in terms of rank. This is at least possible though. 
lemma truncate_rank (M : matroid U){n : ℤ}(hn : 0 ≤ n)(X : set U) :
  (truncate M hn).r X = min n (M.r X) :=
begin
  apply indep_family.I_to_r_eq_iff.mpr, 
  unfold indep_family.is_set_basis trunc.indep matroid.to_indep_family, 
  simp only [and_imp, not_and, not_le, ne.def, ssubset_iff], 
  cases M.exists_basis_of X with B hB, 
  rw matroid.basis_of_iff_indep_full_rank at hB, 
  rcases hB with ⟨hBX, ⟨hBI, hBS⟩⟩, 
  by_cases n ≤ size B,
  rcases has_subset_of_size hn h with ⟨B₀,⟨hB₀,hB₀s⟩⟩, 
  rw hBS at h, 
  refine ⟨B₀, ⟨⟨_,⟨⟨matroid.I2 hB₀ hBI,(eq.symm hB₀s).ge⟩,λ J hBJ1 hBJ2 hJX hJind, _⟩⟩,by finish⟩⟩, 
  from subset_trans hB₀ hBX, 
  linarith [size_strict_monotone (ssubset_of_subset_ne hBJ1 hBJ2)], 
  push_neg at h, 
  rw hBS at h, 
  refine ⟨B, ⟨⟨hBX,⟨⟨hBI,by linarith⟩,λ J hBJ1 hBJ2 hJX hJind, _⟩⟩,_⟩⟩, 
  rw matroid.indep_iff_r at hBI hJind, 
  linarith [rank_mono M hJX, M.rank_mono hBJ1, size_strict_monotone (ssubset_of_subset_ne hBJ1 hBJ2)], 
  have := le_of_lt h, 
  rw min_comm, 
  finish, 
end

end truncation 

section uniform


def free_matroid_on (U : ftype): matroid U := 
  { 
    r := size,
    R0 := size_nonneg,
    R1 := λ X, le_refl (size X),
    R2 := λ X Y hXY, size_monotone hXY,
    R3 := λ X Y, le_of_eq (size_modular X Y),  
  } 

lemma free_matroid_indep {U : ftype}(X : U) :
  (free_matroid_on U).is_indep X  := 
  by rw [free_matroid_on, indep_iff_r]

lemma free_iff_univ_indep {U : ftype}{M : matroid U}: 
   M = free_matroid_on U ↔ is_indep M univ := 
begin
  refine ⟨λ h, _, λ h,_⟩, 
  rw [indep_iff_r,h], finish,  
  ext X, simp_rw [free_matroid_on, ←indep_iff_r, I2 (subset_univ X) h], 
end


def loopy_matroid_on (U : ftype) : matroid U := 
  {
    r := λ X, 0, 
    R0 := λ X, le_refl 0, 
    R1 := λ X, size_nonneg X, 
    R2 := λ X Y hXY, le_refl 0, 
    R3 := λ X Y, rfl.ge
  }

def loopy_iff_univ_rank_zero {U : ftype}{M : matroid U}:
  M = loopy_matroid_on U ↔ M.r univ = 0 := 
begin
  refine ⟨λ h, by finish, λ h,_⟩,  
  ext X, simp_rw [loopy_matroid_on], 
  have := rank_mono M (subset_univ X), 
  rw h at this, 
  linarith [M.rank_nonneg X], 
end

lemma loopy_matroid_indep_iff_empty {U : ftype}{X : set U}:
  (loopy_matroid_on U).is_indep X ↔ X = ∅ := 
by {rw [indep_iff_r, ←size_zero_iff_empty, eq_comm], simp [loopy_matroid_on]}



def uniform_matroid_on (U : ftype){r : ℤ}(hr : 0 ≤ r) : matroid U := 
  truncate (free_matroid_on U) hr 

@[simp] lemma uniform_matroid_rank (U : ftype)(X : set U){r : ℤ}(hr : 0 ≤ r) :
  (uniform_matroid_on U hr).r X = min r (size X) := 
  by apply truncate_rank

lemma uniform_matroid_indep (U : ftype)(X : set U){r : ℤ}{hr : 0 ≤ r}  : 
  is_indep (uniform_matroid_on U hr) X ↔ size X ≤ r := 
  by {rw [indep_iff_r, uniform_matroid_rank], finish}

lemma uniform_dual (U : ftype){r : ℤ}(hr : 0 ≤ r)(hrn : r ≤ size (univ : set U)): 
  dual (uniform_matroid_on U hr) = uniform_matroid_on U (by linarith : 0 ≤ size (univ : set U) - r) :=
begin
  ext X, 
  simp_rw [dual, uniform_matroid_rank, compl_size, min_eq_left hrn], 
  rw [←min_add_add_left, ←(min_sub_sub_right), min_comm], simp, 
end

def circuit_matroid_on {U : ftype} (hU : nontriv U) : matroid U := 
  uniform_matroid_on U (by linarith [nontriv_size hU] : 0 ≤ size (univ : set U) - 1)

@[simp] lemma circuit_matroid_rank {U : ftype}(hU : nontriv U)(X : set U):
  (circuit_matroid_on hU).r X = min (size (univ : set U) - 1) (size X) := 
  uniform_matroid_rank _ _ _ 

lemma circuit_matroid_iff_univ_circuit {U : ftype} (hU : nontriv U){M : matroid U}:
  M = circuit_matroid_on hU ↔ is_circuit M univ := 
begin
  refine ⟨λ h, _, λ h, _⟩, 
  rw [circuit_iff_r, h], 
  simp_rw circuit_matroid_rank, 
  from ⟨min_eq_left (by linarith), λ Y hY, min_eq_right (by linarith [size_strict_monotone hY])⟩, 
  ext X, rw circuit_matroid_rank, 
  rw circuit_iff_r at h, 
  have h' : X ⊂ univ ∨ X = univ := _ , 
  cases h', 
  rw [h.2 X h', eq_comm], from min_eq_right (by linarith [size_strict_monotone h']), 
  rw [h', h.1, eq_comm], from min_eq_left (by linarith), 
  from subset_ssubset_or_eq (subset_univ _), 
end


end uniform

section relax
variables {U : ftype}[decidable_eq (set U)] 

def relax.r (M : matroid U)(C : set U) : set U → ℤ := 
  λ X, ite (X = C) (M.r X + 1) (M.r X)

lemma relax.r_of_C_eq_univ {M : matroid U}{C : set U}(hC : is_circuit_hyperplane M C) :
  relax.r M C C = M.r univ := 
  by {simp_rw [relax.r, if_pos rfl], linarith [circuit_hyperplane_rank hC]}

lemma relax.r_of_C {M : matroid U}{C : set U}(hC : is_circuit_hyperplane M C) :
  relax.r M C C = M.r C + 1 := 
  by {simp_rw [relax.r, if_pos rfl]}

lemma relax.r_of_not_C {M : matroid U}{C X: set U}(hC : is_circuit_hyperplane M C)(hXC : X ≠ C):
  relax.r M C X = M.r X := 
  by {unfold relax.r, finish}

lemma r_le_relax_r (M : matroid U)(C X : set U) :
  M.r X ≤ relax.r M C X := 
begin
  unfold relax.r, by_cases X = C, 
  rw if_pos h, linarith, 
  rw if_neg h,
end

lemma relax.r_le_univ {M : matroid U}{C : set U}(hC : is_circuit_hyperplane M C)(X : set U):
  relax.r M C X ≤ M.r univ := 
begin
  by_cases h : X = C, 
  rw [h, relax.r_of_C hC, circuit_hyperplane_rank hC], linarith, 
  rw [relax.r_of_not_C hC h], apply rank_le_univ, 
end 


lemma relax.R0 (M : matroid U)(C : set U) : 
  satisfies_R0 (relax.r M C) := 
  λ X, le_trans (M.rank_nonneg X) (r_le_relax_r M C X)

lemma relax.R1 {M : matroid U}{C : set U}(hC : is_circuit_hyperplane M C) : 
  satisfies_R1 (relax.r M C) := 
begin
  intro X, unfold relax.r, by_cases h : X = C, 
  rw if_pos h, 
  rcases hC with ⟨h₁,h₂⟩, 
  rw circuit_iff_r at h₁, 
  rw h, linarith,  
  rw if_neg h, 
  from M.rank_le_size X, 
end

lemma relax.R2 {M : matroid U}{C : set U}(hC : is_circuit_hyperplane M C) : 
  satisfies_R2 (relax.r M C) :=
begin
  intros X Y hXY,
  by_cases h: X = C, 
  rw [h, relax.r_of_C_eq_univ hC], 
  rw h at hXY, 
  cases subset_ssubset_or_eq hXY with h' h',
  linarith [circuit_hyperplane_ssupset_rank hC h', relax.r_of_not_C hC (ne_of_ssubset h').symm],
  rw [←h', relax.r_of_C_eq_univ], from hC, 
  linarith [relax.r_of_not_C hC h, r_le_relax_r M C Y, rank_mono M hXY],  
end

lemma relax.R3 {M : matroid U}{C : set U}(hC : is_circuit_hyperplane M C) : 
  satisfies_R3 (relax.r M C) :=
begin
  intros X Y, 
  by_cases hi : X ∩ Y = C; by_cases hu : X ∪ Y = C, 
  
  simp only [ eq_of_union_eq_inter (eq.trans hu hi.symm), inter_idem, union_self], 

  rw [relax.r_of_not_C hC hu,hi],  
  have hCXY' : (C ⊆ X) ∧ (C ⊆ Y) := by {simp_rw ←hi, from ⟨inter_subset_left _ _, inter_subset_right _ _⟩, },
  have hCXY : (C ⊂ X ∨ X = C) ∧ (C ⊂ Y ∨ Y = C) := by {simp_rw [eq_comm, ←subset_iff_ssubset_or_eq], from hCXY'},
  rcases hCXY with ⟨(hCX | hCX), (hCY|hCY)⟩, 
  rw [relax.r_of_not_C hC (ne.symm (ne_of_ssubset hCX)), circuit_hyperplane_ssupset_rank hC hCX],
  rw [relax.r_of_not_C hC (ne.symm (ne_of_ssubset hCY)), circuit_hyperplane_ssupset_rank hC hCY],
  linarith [rank_le_univ M (X ∪ Y), relax.r_of_C hC, circuit_hyperplane_rank hC], 
  rw [hCY, union_comm X, subset_def_union_mp hCXY'.1], 
  linarith [r_le_relax_r M C X], 
  rw [hCX, subset_def_union_mp hCXY'.2], 
  linarith [r_le_relax_r M C Y],
  rw [hCY, hCX, union_self], 
  linarith [r_le_relax_r M C C], 

  have hCXY' : (X ⊆ C) ∧ (Y ⊆ C) := by {simp_rw ←hu, from ⟨subset_union_left _ _, subset_union_right _ _⟩, },
  have hCXY : (X ⊂ C ∨ X = C) ∧ (Y ⊂ C ∨ Y = C) := by {simp_rw [←subset_iff_ssubset_or_eq], from hCXY'},
  rw [relax.r_of_not_C hC hi, hu], 
  rcases hCXY with ⟨(hCX|hCX),(hCY|hCY)⟩, 
  rw [relax.r_of_not_C hC (ne_of_ssubset hCX), circuit_hyperplane_ssubset_rank hC hCX],
  rw [relax.r_of_not_C hC (ne_of_ssubset hCY), circuit_hyperplane_ssubset_rank hC hCY],
  rw [relax.r_of_C hC, circuit_hyperplane_rank_size hC, ←hu], 
  linarith [size_modular X Y, M.rank_le_size (X ∩ Y)], 
  rw [hCY], linarith [relax.r_of_not_C hC (ne_of_ssubset hCX), M.rank_mono (inter_subset_left X C)], 
  rw [hCX], linarith [relax.r_of_not_C hC (ne_of_ssubset hCY), M.rank_mono (inter_subset_right C Y)],
  rw [hCY, hCX, inter_idem], linarith [r_le_relax_r M C C], 

  rw [relax.r_of_not_C hC hi, relax.r_of_not_C hC hu],  
  linarith [M.R3 X Y, r_le_relax_r M C X, r_le_relax_r M C Y],
end

def relax (M : matroid U)(C : set U)(hC : is_circuit_hyperplane M C) : matroid U := 
  ⟨relax.r M C, relax.R0 M C, relax.R1 hC, relax.R2 hC, relax.R3 hC⟩ 

theorem relax.dual {M : matroid U}{C : set U}(hC : is_circuit_hyperplane M C) :
  dual (relax M C hC) = relax (dual M) Cᶜ (circuit_hyperplane_dual.mp hC) := 
let hCc := circuit_hyperplane_dual.mp hC in 
begin
  ext X, 
  have hCuniv : univ ≠ C := λ h, 
    by {have := circuit_hyperplane_rank hC, rw ←h at this, linarith}, 
  by_cases h : X = Cᶜ,   
  simp_rw [dual_r, h, compl_compl, relax, relax.r_of_C hC, relax.r_of_C hCc],
  rw [dual_r, compl_compl, relax.r_of_not_C hC hCuniv], linarith, 
  have h' : Xᶜ ≠ C := λ hcon, by {rw [←hcon, compl_compl] at h, finish}, 
  simp_rw [relax, dual_r, relax.r_of_not_C hCc h, relax.r_of_not_C hC h', dual_r],
  rw relax.r_of_not_C hC hCuniv,  
end

theorem single_rank_disagreement_is_relaxation {M₁ M₂ : matroid U}{X : set U}: 
  M₁.r univ = M₂.r univ → M₁.r X < M₂.r X → (∀ Y, Y ≠ X → M₁.r Y = M₂.r Y) → ∃ h : is_circuit_hyperplane M₁ X, M₂ = relax M₁ X h :=
begin
  intros hr hX h_other, 
  have hne : M₁ ≠ M₂ := λ h, by {rw h at hX, from lt_irrefl _ hX },
  cases circuit_ind_of_distinct hne with X' hX', 
  have hXX' : X' = X := by
  {
    by_contra hXX', 
    simp_rw [circuit_iff_r, indep_iff_r] at hX', 
    cases hX';
    linarith [h_other _ hXX'], 
  },
  simp_rw hXX' at hX', 
  have : is_circuit M₁ X ∧ is_indep M₂ X := by 
  {
    cases hX', assumption, 
    simp_rw [circuit_iff_r, indep_iff_r] at hX', 
    linarith, 
  },
  cases this with hXcct hXind, 
  have hdne : dual M₁ ≠ dual M₂ := λ heq, hne (dual_inj heq), 
  cases circuit_ind_of_distinct hdne with Z hZ, 
  have hXZ : Zᶜ = X := by 
  {
    by_contra hXZ, 
    repeat {rw [←is_cocircuit] at hZ}, 
    simp_rw [cocircuit_iff_r, coindep_iff_r] at hZ,
    cases hZ;
    linarith [h_other _ hXZ], 
  },
  have : is_circuit (dual M₁) Z ∧ is_indep (dual M₂) Z := by 
  {
    cases hZ, 
    assumption, 
    rw [←is_cocircuit, cocircuit_iff_r, coindep_iff_r, hXZ] at hZ, 
    linarith,   
  },
  rw (compl_pair hXZ) at this, 
  cases this with hXhp _, 
  rw [←is_cocircuit, cocircuit_iff_compl_hyperplane, compl_compl] at hXhp,
  let hch : is_circuit_hyperplane M₁ X := ⟨hXcct, hXhp⟩, 
  use hch,
  ext Y,
  by_cases hYX : Y = X,   
  simp_rw [hYX, relax, relax.r_of_C hch],   
  linarith [r_cct hXcct, r_indep hXind], 
  simp_rw [relax, relax.r_of_not_C hch hYX, eq_comm],
  from h_other Y hYX,  
end

lemma single_rank_disagreement_univ (hU : nontriv U){M₁ M₂ : matroid U}:
   M₁.r univ < M₂.r univ → (∀ X, X ≠ univ → M₁.r X = M₂.r X) → 
    M₁ = circuit_matroid_on hU ∧ M₂ = free_matroid_on U  := 
begin
  intros huniv hother, 
  rw [circuit_matroid_iff_univ_circuit, free_iff_univ_indep], 
  have hM₁M₂ : M₁ ≠ M₂ := λ h, by {rw h at huniv, from lt_irrefl _ huniv}, 
  cases circuit_ind_of_distinct hM₁M₂ with Z hZ, 
  by_cases Z = univ; cases hZ, 
  rw h at hZ, assumption, 
  rw [h,circuit_iff_r, indep_iff_r] at hZ, linarith,
  rw [circuit_iff_r, indep_iff_r] at hZ, linarith [hother Z h], 
  rw [circuit_iff_r, indep_iff_r] at hZ, linarith [hother Z h], 
end

end relax 


 
import prelim.induction prelim.collections
import matroid.rankfun matroid.indep matroid.submatroid.order 
import .uniform 

open matroid set 
open_locale classical big_operators 



noncomputable theory 


section relax
variables {U : Type}[nonempty (fintype U)] --[decidable_eq (set U)] 

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
  
  simp only [ eq_of_union_eq_inter (eq.trans hu hi.symm), inter_self, union_self], 

  rw [relax.r_of_not_C hC hu,hi],  
  have hCXY' : (C ⊆ X) ∧ (C ⊆ Y) := by {simp_rw ←hi, from ⟨inter_subset_left _ _, inter_subset_right _ _⟩, },
  have hCXY : (C ⊂ X ∨ X = C) ∧ (C ⊂ Y ∨ Y = C) := by {simp_rw [eq_comm, ←subset_iff_ssubset_or_eq], from hCXY'},
  rcases hCXY with ⟨(hCX | hCX), (hCY|hCY)⟩, 
  rw [relax.r_of_not_C hC (ne.symm (ne_of_ssubset hCX)), circuit_hyperplane_ssupset_rank hC hCX],
  rw [relax.r_of_not_C hC (ne.symm (ne_of_ssubset hCY)), circuit_hyperplane_ssupset_rank hC hCY],
  linarith [rank_le_univ M (X ∪ Y), relax.r_of_C hC, circuit_hyperplane_rank hC], 
  rw [hCY, union_comm X, subset_iff_union_eq_left.mp hCXY'.1], 
  linarith [r_le_relax_r M C X], 
  rw [hCX, subset_iff_union_eq_left.mp hCXY'.2], 
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
  rw [hCY, hCX, inter_self], linarith [r_le_relax_r M C C], 

  rw [relax.r_of_not_C hC hi, relax.r_of_not_C hC hu],  
  linarith [M.R3 X Y, r_le_relax_r M C X, r_le_relax_r M C Y],
end

/-- relaxation of the circuit_hyperplane C in M -/
def relax (M : matroid U)(C : set U)(hC : is_circuit_hyperplane M C) : matroid U := 
  ⟨relax.r M C, relax.R0 M C, relax.R1 hC, relax.R2 hC, relax.R3 hC⟩ 

lemma relax_weak_image (M : matroid U)(C : set U)(hC : is_circuit_hyperplane M C): 
  M ≤ (relax M C hC) :=
λ X, r_le_relax_r _ _ X 

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

theorem single_rank_neq_is_relaxation {M₁ M₂ : matroid U}{X : set U}(hr : M₁.r univ = M₂.r univ)
(hX : M₁.r X < M₂.r X)(h_other : ∀ Y, Y ≠ X → M₁.r Y = M₂.r Y): 
  ∃ h : is_circuit_hyperplane M₁ X, M₂ = relax M₁ X h :=
begin
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
    M₁ = unif.circuit_matroid_on U hU ∧ M₂ = unif.free_matroid_on U  := 
begin
  intros huniv hother, 
  rw [unif.circuit_matroid_iff_univ_circuit, unif.free_iff_univ_indep], 
  have hM₁M₂ : M₁ ≠ M₂ := λ h, by {rw h at huniv, from lt_irrefl _ huniv}, 
  cases circuit_ind_of_distinct hM₁M₂ with Z hZ, 
  by_cases Z = univ; cases hZ, 
  rw h at hZ, assumption, 
  rw [h,circuit_iff_r, indep_iff_r] at hZ, linarith,
  rw [circuit_iff_r, indep_iff_r] at hZ, linarith [hother Z h], 
  rw [circuit_iff_r, indep_iff_r] at hZ, linarith [hother Z h], 
end

end relax 
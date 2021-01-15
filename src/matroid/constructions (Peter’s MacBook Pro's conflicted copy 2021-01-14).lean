
import boolalg.basic boolalg.induction boolalg.collections boolalg.examples 
import .rankfun .indep 

namespace boolalg 

section free

noncomputable theory 


  def free_matroid_on (U : boolalg): rankfun U := 
  { 
    r := size,
    R0 := size_nonneg,
    R1 := λ X, le_refl (size X),
    R2 := λ X Y hXY, size_monotone hXY,
    R3 := λ X Y, le_of_eq (size_modular X Y),  
  } 

  def loopy_matroid_on (U : boolalg) : rankfun U := 
  {
    r := λ X, 0, 
    R0 := λ X, le_refl 0, 
    R1 := λ X, size_nonneg X, 
    R2 := λ X Y hXY, le_refl 0, 
    R3 := λ X Y, rfl.ge
  }

end free 


section truncation 

variables {U : boolalg}

def trunc.indep (M : indep_family U) {n : ℤ}(hn : 0 ≤ n) : U → Prop :=  
  λ X, M.indep X ∧ size X ≤ n

lemma trunc.I1 (M : indep_family U) {n : ℤ} (hn : 0 ≤ n): 
  satisfies_I1 (trunc.indep M hn) := 
  ⟨M.I1, by {rw size_bot, assumption}⟩

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

def truncate (M : rankfun U){n : ℤ}(hn : 0 ≤ n) : rankfun U := 
  let M_ind := rankfun_to_indep_family M in 
  indep_family_to_rankfun ⟨trunc.indep M_ind hn, trunc.I1 M_ind hn, trunc.I2 M_ind hn, trunc.I3 M_ind hn⟩

-- in retrospect it would probably have been easier to define truncation in terms of rank. This is at least possible though. 
lemma truncate_rank (M : rankfun U){n : ℤ}(hn : 0 ≤ n)(X : U) :
  (truncate M hn).r X = min n (M.r X) :=
begin
  apply indep.I_to_r_eq_iff.mpr, 
  unfold indep.is_set_basis trunc.indep rankfun_to_indep_family, 
  simp only [and_imp, not_and, not_le, ne.def, ssubset_iff], 
  cases exists_basis_of M X with B hB, 
  rw basis_of_iff_indep_full_rank at hB, 
  rcases hB with ⟨hBX, ⟨hBI, hBS⟩⟩, 
  by_cases n ≤ size B,
  rcases has_subset_of_size hn h with ⟨B₀,⟨hB₀,hB₀s⟩⟩, 
  rw hBS at h, 
  refine ⟨B₀, ⟨⟨_,⟨⟨_,_⟩,λ J hBJ1 hBJ2 hJX hJind, _⟩⟩,_⟩⟩, 
  from subset_trans hB₀ hBX, 
  from I2 hB₀ hBI,
  from (eq.symm hB₀s).ge,
  linarith [size_strict_monotone ⟨hBJ1, hBJ2⟩], 
  finish, 
  push_neg at h, 
  rw hBS at h, 
  refine ⟨B, ⟨⟨hBX,⟨⟨hBI,by linarith⟩,λ J hBJ1 hBJ2 hJX hJind, _⟩⟩,_⟩⟩, 
  rw indep_iff_r at hBI hJind, 
  linarith [R2 M hJX, R2 M hBJ1, size_strict_monotone ⟨hBJ1, hBJ2⟩], 
  have := le_of_lt h, 
  rw min_comm, 
  finish, 
end

end truncation 

section uniform


def uniform_matroid_on (U : boolalg){r : ℤ}(hr : 0 ≤ r) : rankfun U := 
  truncate (free_matroid_on U) hr 

lemma uniform_matroid_rank (U : boolalg)(X : U){r : ℤ}(hr : 0 ≤ r) :
  (uniform_matroid_on U hr).r X = min r (size X) := 
  by apply truncate_rank


end uniform

section relax
variables {U : boolalg}[decidable_eq U] 

def relax.r (M : rankfun U)(C : U) : U → ℤ := 
  λ X, ite (X = C) (M.r X + 1) (M.r X)

lemma relax.r_of_C_eq_top {M : rankfun U}{C : U}(hC : is_circuit_hyperplane M C) :
  relax.r M C C = M.r ⊤ := 
  by {simp_rw [relax.r, if_pos rfl], linarith [circuit_hyperplane_rank hC]}

lemma relax.r_of_C {M : rankfun U}{C : U}(hC : is_circuit_hyperplane M C) :
  relax.r M C C = M.r C + 1 := 
  by {simp_rw [relax.r, if_pos rfl]}

lemma relax.r_of_not_C {M : rankfun U}{C X: U}(hC : is_circuit_hyperplane M C)(hXC : X ≠ C):
  relax.r M C X = M.r X := 
  by {unfold relax.r, finish}

lemma r_le_relax_r (M : rankfun U)(C X : U) :
  M.r X ≤ relax.r M C X := 
begin
  unfold relax.r, by_cases X = C, 
  rw if_pos h, linarith, 
  rw if_neg h,
end

lemma relax.r_le_top {M : rankfun U}{C : U}(hC : is_circuit_hyperplane M C)(X : U):
  relax.r M C X ≤ M.r ⊤ := 
begin
  by_cases h : X = C, 
  rw [h, relax.r_of_C hC, circuit_hyperplane_rank hC], linarith, 
  rw [relax.r_of_not_C hC h], apply rank_le_top, 
end 

def relax.R0 (M : rankfun U)(C : U) : 
  satisfies_R0 (relax.r M C) := 
  λ X, le_trans (M.R0 X) (r_le_relax_r M C X)

lemma relax.R1 {M : rankfun U}{C : U}(hC : is_circuit_hyperplane M C) : 
  satisfies_R1 (relax.r M C) := 
begin
  intro X, unfold relax.r, by_cases h : X = C, 
  rw if_pos h, 
  rcases hC with ⟨h₁,h₂⟩, 
  rw circuit_iff_r at h₁, 
  rw h, linarith,  
  rw if_neg h, 
  from M.R1 X, 
end

lemma relax.R2 {M : rankfun U}{C : U}(hC : is_circuit_hyperplane M C) : 
  satisfies_R2 (relax.r M C) :=
begin
  intros X Y hXY,
  by_cases h: X = C, 
  rw [h, relax.r_of_C_eq_top hC], 
  rw h at hXY, 
  cases subset_ssubset_or_eq hXY with h' h',
  linarith [circuit_hyperplane_ssupset_rank hC h', relax.r_of_not_C hC (h'.2.symm)],
  rw [←h', relax.r_of_C_eq_top], from hC, 
  linarith [relax.r_of_not_C hC h, r_le_relax_r M C Y, R2 M hXY],  
end

lemma relax.R3 {M : rankfun U}{C : U}(hC : is_circuit_hyperplane M C) : 
  satisfies_R3 (relax.r M C) :=
begin
  intros X Y, 
  by_cases hi : X ∩ Y = C;
  by_cases hu : X ∪ Y = C, 
  simp only [ eq_of_union_eq_inter (eq.trans hu hi.symm), inter_idem, union_idem], 
  rw hi, 
  have hCY : C ⊆ Y := by {rw ← hi, apply inter_subset_right},
  have hCX : C ⊆ X := by {rw ← hi, apply inter_subset_left},
  by_cases hX: X = C; by_cases hY: Y = C, 
  rw [hX, hY, union_idem] at hu, 
  from false.elim (hu rfl), 
  rw [relax.r_of_not_C hC hu, relax.r_of_not_C hC hY, hX],
  linarith [rank_le_top M (C ∪ Y), circuit_hyperplane_ssupset_rank hC ⟨hCY, ne.symm hY⟩], 
  rw [relax.r_of_not_C hC hu, relax.r_of_not_C hC hX, hY],
  linarith [rank_le_top M (X ∪ C), circuit_hyperplane_ssupset_rank hC ⟨hCX, ne.symm hX⟩], 
  rw [relax.r_of_not_C hC hX, relax.r_of_not_C hC hY, 
        circuit_hyperplane_ssupset_rank hC ⟨hCX, ne.symm hX⟩, circuit_hyperplane_ssupset_rank hC ⟨hCY, ne.symm hY⟩] ,
  linarith [relax.r_le_top hC (X ∪ Y), relax.r_le_top hC C], 
  by_cases hX : X = C; by_cases hY : Y = C, 
  rw [hu, hX, hY, inter_idem], 
  rw [hu, hX], linarith [relax.R2 hC _ _ (inter_subset_right C Y)], 
  rw [hu, hY], linarith [relax.R2 hC _ _ (inter_subset_left X C)], 
  have hXC : X ⊂ C := ⟨by {rw ←hu, apply subset_union_left},hX⟩,
  have hYC : Y ⊂ C := ⟨by {rw ←hu, apply subset_union_right},hY⟩,
  have hXY : X ∩ Y ⊂ C := inter_of_ssubsets _ _ _ hXC , 
  rw [relax.r_of_not_C hC hX, relax.r_of_not_C hC hY, relax.r_of_not_C hC hi, hu, relax.r_of_C hC, circuit_hyperplane_rank_size hC],
  rw [← hu, circuit_hyperplane_ssubset_rank hC hXC, circuit_hyperplane_ssubset_rank hC hYC, circuit_hyperplane_ssubset_rank hC hXY],
  linarith [size_modular X Y],
  rw [relax.r_of_not_C hC hi, relax.r_of_not_C hC hu], 
  linarith [r_le_relax_r M C X, r_le_relax_r M C Y, M.R3 X Y], 
end

def relaxation [decidable_eq U](M : rankfun U){C : U}(hC : is_circuit_hyperplane M C) : rankfun U:=
  ⟨relax.r M C, relax.R0 M C, relax.R1 hC, relax.R2 hC, relax.R3 hC⟩
  
theorem single_rank_disagreement_is_relaxation [decidable_eq U]{M₁ M₂ : rankfun U}{X : U}: 
  M₁.r X < M₂.r X → (∀ Y, Y ≠ X → M₁.r Y = M₂.r Y) → ∃ h : is_circuit_hyperplane M₁ X, M₂ = relaxation M₁ h :=
begin
  intros hX h_other, 
  sorry, 

end


end relax 


end boolalg 

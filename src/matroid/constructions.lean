
import boolalg.basic boolalg.induction boolalg.collections boolalg.examples 
import .basic .cryptomorphism

namespace boolalg 
namespace cryptomorphism 

section free

noncomputable theory 

variables {U : boolalg}

  def free_matroid_on (X : U) : rankfun (subalg X) := 
  { 
    r := size,
    R0 := size_nonneg,
    R1 := λ X, le_refl (size X),
    R2 := λ X Y hXY, size_monotone hXY,
    R3 := λ X Y, le_of_eq (size_modular X Y),  
  } 

  def loopy_matroid_on (X : U) : rankfun (subalg X) := 
  {
    r := λ X, 0, 
    R0 := λ X, le_refl 0, 
    R1 := λ X, size_nonneg X, 
    R2 := λ X Y hXY, le_refl 0, 
    R3 := λ X Y, rfl.ge
  }

end free 


section truncation 

variables {U : boolalg}{M : indep_family U}

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
  
lemma truncate_rank (M : rankfun U){n : ℤ}(hn : 0 ≤ n)(X : U) :
  (truncate M hn).r X = min n (M.r X) :=
begin
  apply indep.I_to_r_eq_iff.mpr, 
  unfold indep.is_set_basis trunc.indep rankfun_to_indep_family, 
  simp only [and_imp, not_and, not_le, ne.def, ssubset_iff], 
  by_cases n ≤ M.r X, 
  sorry, 
  cases exists_basis_of M X with B hB, 
  
  rcases hB with ⟨hBi, ⟨hBX,hBr⟩⟩, 
  refine ⟨B, ⟨⟨hBX,⟨⟨hBi,_⟩,λ J hBJ hBne hJX hJi, _⟩⟩,_⟩⟩ , 
  rw indep_iff_r at hBi, linarith, 
   

  --have := indep.has_set_basis_with_size M X, 
  --unfold truncate,
  


end



end truncation 
end cryptomorphism
end boolalg 

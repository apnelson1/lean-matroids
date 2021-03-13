
import prelim.induction prelim.collections 
import matroid.rankfun matroid.indep matroid.submatroid.order

open matroid set 
noncomputable theory 
namespace trunc 

variables {α : Type*} [fintype α]

def indep (M : indep_family α) (n : ℤ) : set α → Prop :=  
  λ X, M.indep X ∧ size X ≤ max 0 n 

lemma I1 (M : indep_family α) (n : ℤ) : 
  satisfies_I1 (trunc.indep M n) := 
⟨M.I1, by {rw size_empty, apply le_max_left, }⟩

lemma I2 (M : indep_family α) (n : ℤ) : 
  satisfies_I2 (trunc.indep M n) := 
λ I J hIJ hJ, ⟨M.I2 I J hIJ hJ.1, le_trans (size_monotone hIJ) hJ.2⟩ 

lemma I3 (M : indep_family α) (n : ℤ) : 
  satisfies_I3 (trunc.indep M n) := 
begin
  intros I J hIJ hI hJ, 
  cases (M.I3 _ _ hIJ hI.1 hJ.1) with e he, 
  refine ⟨e, ⟨he.1, ⟨he.2,_ ⟩ ⟩⟩, 
  by_contra h_con, push_neg at h_con, 
  rw [(size_union_nonmem_singleton (mem_diff_iff.mp he.1).2)] at h_con, 
  linarith [int.le_of_lt_add_one h_con, hIJ, hJ.2], 
end

def tr (M : matroid α) (n : ℤ) : matroid α := 
  let M_ind := M.to_indep_family in 
  matroid.of_indep_family ⟨indep M_ind n, I1 M_ind n, I2 M_ind n, I3 M_ind n⟩

-- in retrospect it would probably have been easier to define truncation in terms of rank. This is at least possible though. 
lemma r_eq (M : matroid α){n : ℤ} (hn : 0 ≤ n) (X : set α) :
  (tr M n).r X = min n (M.r X) :=
begin
  have hn' : max 0 n = n := max_eq_right hn, 
  apply indep_family.I_to_r_eq_iff.mpr, 
  unfold indep_family.is_set_basis trunc.indep matroid.to_indep_family, 
  simp only [and_imp, not_and, not_le, ne.def, ssubset_iff_subset_ne], 
  cases M.exists_basis_of X with B hB, 
  rw matroid.basis_of_iff_indep_full_rank at hB, 
  rcases hB with ⟨hBX, ⟨hBI, hBS⟩⟩, 
  by_cases n ≤ size B,
  rcases has_subset_of_size hn h with ⟨B₀,⟨hB₀,hB₀s⟩⟩, 
  rw hBS at h, 
  simp_rw hn', 
  refine ⟨B₀, ⟨⟨_,⟨⟨matroid.indep_of_subset_indep hB₀ hBI,(eq.symm hB₀s).ge⟩,λ J hBJ1 hBJ2 hJX hJind, _⟩⟩,by finish⟩⟩, 
  from subset.trans hB₀ hBX, 
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

lemma weak_image (M : matroid α){n : ℤ} (hn : 0 ≤ n) : 
  (tr M n) ≤ M := 
λ X, by {rw r_eq, simp, tauto, tauto }

end trunc

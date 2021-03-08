
import prelim.induction prelim.collections 
import matroid.rankfun matroid.indep matroid.submatroid.order

open matroid set 
noncomputable theory 
namespace trunc 

variables {U : Type}[fintype U]

def indep (M : indep_family U) {n : ℤ}(hn : 0 ≤ n) : set U → Prop :=  
  λ X, M.indep X ∧ size X ≤ n

lemma I1 (M : indep_family U) {n : ℤ} (hn : 0 ≤ n): 
  satisfies_I1 (trunc.indep M hn) := 
⟨M.I1, by {rw size_empty, assumption}⟩

lemma I2 (M : indep_family U) {n : ℤ} (hn : 0 ≤ n) : 
  satisfies_I2 (trunc.indep M hn) := 
λ I J hIJ hJ, ⟨M.I2 I J hIJ hJ.1, le_trans (size_monotone hIJ) hJ.2⟩ 

lemma I3 (M : indep_family U) {n : ℤ} (hn : 0 ≤ n): 
  satisfies_I3 (trunc.indep M hn) := 
begin
  intros I J hIJ hI hJ, 
  cases (M.I3 _ _ hIJ hI.1 hJ.1) with e he, 
  refine ⟨e, ⟨he.1, ⟨he.2,_ ⟩ ⟩⟩, 
  by_contra h_con, push_neg at h_con, 
  rw [(size_insert_nonmem (elem_diff_iff.mp he.1).2)] at h_con, 
  linarith [int.le_of_lt_add_one h_con, hIJ, hJ.2], 
end

def tr (M : matroid U){n : ℤ}(hn : 0 ≤ n) : matroid U := 
  let M_ind := M.to_indep_family in 
  matroid.of_indep_family ⟨indep M_ind hn, I1 M_ind hn, I2 M_ind hn, I3 M_ind hn⟩

-- in retrospect it would probably have been easier to define truncation in terms of rank. This is at least possible though. 
lemma r_eq (M : matroid U){n : ℤ}(hn : 0 ≤ n)(X : set U) :
  (tr M hn).r X = min n (M.r X) :=
begin
  apply indep_family.I_to_r_eq_iff.mpr, 
  unfold indep_family.is_set_basis trunc.indep matroid.to_indep_family, 
  simp only [and_imp, not_and, not_le, ne.def, ssubset_iff_subset_ne], 
  cases M.exists_basis_of X with B hB, 
  rw matroid.basis_of_iff_indep_full_rank at hB, 
  rcases hB with ⟨hBX, ⟨hBI, hBS⟩⟩, 
  by_cases n ≤ size B,
  rcases has_subset_of_size hn h with ⟨B₀,⟨hB₀,hB₀s⟩⟩, 
  rw hBS at h, 
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

lemma weak_image (M : matroid U){n : ℤ}(hn : 0 ≤ n) : 
  (tr M hn) ≤ M := 
λ X, by {rw r_eq, simp, tauto,}

end trunc

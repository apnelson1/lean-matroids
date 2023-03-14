import ..basic --matroid.indep matroid.submatroid.order
--import prelim.induction prelim.collections 

open matroid set 
noncomputable theory 
namespace trunc 

variables {α : Type*} [fintype α]

/-def indep (M : indep_family α) (n : ℤ) : set α → Prop :=  
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
end-/

/-def tr (M : matroid α) (n : ℤ) : matroid α := 
  let M_ind := M.to_indep_family in 
  matroid.of_indep_family ⟨indep M_ind n, I1 M_ind n, I2 M_ind n, I3 M_ind n⟩-/
def tr'' (M : matroid α) (n : ℕ) [decidable_eq α] (h : n ≤ M.rk) : matroid α := 
{ base := λ X, M.indep X ∧ nat.card X = n,
  exists_base' := 
    begin
      cases M.exists_base' with B h2,
      rw base_iff_indep_r at h2,
      cases h2 with h1 h2,
      rw indep_iff_r_eq_card at h1,
      rw h2 at h1, 
      
      sorry,
    end,
  base_exchange' := _ }
-- do we need the assumption that n ≤ M.r? i think so

-- tried my hand at defining truncation w.r.t rank
def matroid.tr_r (M : matroid α) (n : ℕ) : set α → ℕ := λ X, min (M.r X) n

lemma tr_r_le_card (M : matroid α) (n : ℕ) : ∀ X, (M.tr_r n X) ≤ nat.card X := λ X, 
begin
  rw matroid.tr_r,
  simp,
  left,
  rw nat.card_eq_to_finset_card,
  apply M.r_le_card
end

lemma tr_r_mono (M : matroid α) (n : ℕ) : ∀ X Y, X ⊆ Y → M.tr_r n X ≤ M.tr_r n Y :=
begin
  intros X Y hXY,
  rw matroid.tr_r,
  simp,
  by_cases hX : M.r X < n,
  { by_cases hY : M.r Y < n,
    { left,
      refine ⟨M.r_mono hXY, le_of_lt hX⟩ },
    { right,
      push_neg at hY,
      exact hY } },
  { by_cases hY : M.r Y < n,
    { by_contra,
      apply hX (lt_of_le_of_lt (M.r_mono hXY) hY) },
    { right,
      push_neg at hY,
      exact hY } },
end

theorem set.inter_subset_union (s t : set α) : s ∩ t ⊆ s ∪ t := λ x h, (mem_union_left t) (mem_of_mem_inter_left h)

lemma tr_r_submod (M : matroid α) (n : ℕ) : 
  ∀ X Y, M.tr_r n (X ∩ Y) + M.tr_r n (X ∪ Y) ≤ M.tr_r n X + M.tr_r n Y :=
begin
  intros X Y,
  rw matroid.tr_r,
  simp,
  simp_rw ← min_add_add_right,
  simp,
  simp_rw ← min_add_add_left,
  simp,
  by_cases hInter : (M.r (X ∩ Y) < n),
  { left,
    by_cases hUnion : (M.r (X ∪ Y) < n),
    { by_cases hX : (M.r (X) < n),
      { by_cases hY : (M.r (Y) < n),
        { split,
          { left,
            refine ⟨M.r_inter_add_r_union_le_r_add_r X Y, 
            le_trans (M.r_inter_add_r_union_le_r_add_r X Y) 
            (le_of_lt ((add_lt_add_iff_left (M.r X)).2 hY))⟩ },
          { left,
            refine ⟨le_trans (M.r_inter_add_r_union_le_r_add_r X Y) 
            (le_of_lt ((add_lt_add_iff_right (M.r Y)).2 hX)), _⟩,
            apply le_of_lt,
            linarith } },
        { by_contra,
          apply hY (lt_of_le_of_lt (M.r_mono (subset_union_right X Y)) hUnion) } },
      { by_contra,
        apply hX (lt_of_le_of_lt (M.r_mono (subset_union_left X Y)) hUnion) } },
    by_cases hX : (M.r (X) < n),
    { push_neg at hUnion,
      by_cases hY : (M.r (Y) < n),
      { split,
        { right,
          refine ⟨le_trans (add_le_add le_rfl hUnion) (M.r_inter_add_r_union_le_r_add_r X Y), M.r_mono (inter_subset_left X Y)⟩ },
        { right,
          split,
          rw add_comm,
          apply add_le_add (le_refl n) (M.r_mono (inter_subset_right X Y)),
          apply le_of_lt hInter } },
      { push_neg at hY,
        have h2 := add_le_add (M.r_mono (inter_subset_left X Y)) (le_refl n),
        split, 
        { right,
          split,
          linarith,
          apply M.r_mono (inter_subset_left X Y) },
        { right,
          split,
          linarith,
          linarith } } },
    { push_neg at hUnion,
      push_neg at hX,
      have h2 := M.r_inter_add_r_union_le_r_add_r X Y,
      split,
      right,
      split,
      linarith,
      linarith,
      right,
      split,
      rw add_comm,
      simp,
      apply M.r_mono (inter_subset_right X Y),
      linarith } },
  { by_cases hUnion : (M.r (X ∪ Y) < n),
    { by_contra,
      apply hInter (lt_of_le_of_lt (M.r_mono (set.inter_subset_union X Y)) hUnion) },
    { by_cases hX : (M.r (X) < n),
      { by_contra,
        apply hInter (lt_of_le_of_lt (M.r_mono (inter_subset_left X Y)) hX) },
      { by_cases hY : (M.r (Y) < n),
        { by_contra,
          apply hInter (lt_of_le_of_lt (M.r_mono (inter_subset_right X Y)) hY) },
       {  push_neg at hInter,
          push_neg at hUnion,
          push_neg at hX,
          push_neg at hY,
          right,
          split,
          right,
          split,
          linarith,
          linarith,
          right,
          exact hY } } } },
end

def tr (M : matroid α) (n : ℕ) : matroid α := 
  matroid_of_r (M.tr_r n) (tr_r_le_card M n) (tr_r_mono M n) (tr_r_submod M n)

/-lemma weak_image (M : matroid α){n : ℕ} (hn : 0 ≤ n) : 
  (tr M n) ≤ M := 
λ X, by {rw r_eq, simp, tauto, tauto }-/

-- in retrospect it would probably have been easier to define truncation in terms of rank. This is at least possible though. 
lemma r_eq (M : matroid α){n : ℕ} (hn : 0 ≤ n) (X : set α) :
  (tr M n).r X = min n (M.r X) :=
begin
  rw tr,
  simp,
  rw matroid.tr_r,
  simp,
  rw min_comm,
end

end trunc

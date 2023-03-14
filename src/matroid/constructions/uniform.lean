import matroid.rank --matroid.submatroid.order matroid.simple 
--import prelim.induction prelim.collections 
import .truncation 

open matroid set 
open_locale classical

universes u 

noncomputable theory 

namespace unif

variables {α : Type*} [fintype α]

/-def free_matroid_on (α : Type*) [fintype α]: matroid α := 
{ r := size,
  R0 := size_nonneg,
  R1 := λ X, le_refl (size X),
  R2 := λ X Y hXY, size_monotone hXY,
  R3 := λ X Y, le_of_eq (size_modular X Y),} -/

def free_matroid_on (α : Type*) [fintype α]: matroid α := 
{ base := λ s, s = univ,
  exists_base' := 
    begin
      use univ,
    end,
  base_exchange' := λ X Y hX hY a ha, 
    begin
      simp at hX,
      simp at hY,
      rw [hX, hY] at ha,
      simp at ha,
      by_contra,
      exact ha,
    end } 

lemma free_indep (X : set α) :
  (free_matroid_on α).indep X  := 
begin
  rw [free_matroid_on, indep_iff_subset_base],
  simp only [exists_eq_left, subset_univ],
end

lemma free_iff_univ_indep {M : matroid α} : 
   M = free_matroid_on α ↔ indep M univ := 
begin
  refine ⟨λ h, _, λ h,_⟩, 
  { rw [indep_iff_subset_base, h],
    use univ,
    rw free_matroid_on,
    finish },  
  { ext X,
    simp_rw [free_matroid_on],
    refine ⟨λ h3, base.eq_of_subset_indep h3 h (subset_univ X), λ h3,_⟩, 
    rw [base_iff_maximal_indep, h3],
    refine ⟨h, λ I hI huI, eq.symm (univ_subset_iff.1 huI)⟩ },  
end

/-def loopy (α : Type*) [fintype α]: matroid α := 
{ r := λ X, 0, 
  R0 := λ X, le_refl 0, 
  R1 := λ X, size_nonneg X, 
  R2 := λ X Y hXY, le_refl 0, 
  R3 := λ X Y, rfl.ge }-/

def loopy (α : Type*) [fintype α]: matroid α := 
{ base := λ X, X = ∅,
  exists_base' := 
    begin
      use ∅,
    end,
  base_exchange' := λ X Y hX hY a ha,
    begin
      simp at hX,
      simp at hY,
      rw [hX, hY] at ha,
      simp at ha,
      by_contra,
      exact ha,
    end }

lemma loopy_matroid_base_iff_empty {X : set α} :
  (loopy α).base X ↔ X = ∅ := 
begin
  refine ⟨λ h, _, λ h,_⟩, 
  rw loopy at h,
  simp at h,
  exact h,
  rw loopy,
  simp,
  exact h,
end

lemma loopy_matroid_indep_iff_empty {X : set α} :
  (loopy α).indep X ↔ X = ∅ := 
begin
  simp_rw [indep_iff_subset_base, ← loopy_matroid_base_iff_empty, loopy],
  refine ⟨λ h, _, λ h,_⟩, 
  rcases h with ⟨h0, ⟨h1, h2⟩⟩,
  rw h1 at h2,
  apply subset_empty_iff.1 h2,
  use ∅,
  rw h,
  simp only [eq_self_iff_true, empty_subset, and_self],
end

lemma loopy_iff_univ_rank_zero {M : matroid α} :
  M = loopy α ↔ M.r univ = 0 := 
begin
  simp_rw [eq_r_iff, ← base_iff_basis_univ, loopy], 
  refine ⟨λ h, _, λ h,_⟩,  
  { use ∅,
    refine ⟨_, _⟩,
    rw h,
    simp only,
    simp only [to_finset_empty, finset.card_empty]},
  ext X,
  rcases h with ⟨I, ⟨h2, h3⟩⟩,
  rw [finset.card_eq_zero, to_finset_eq_empty] at h3,
  rw h3 at h2,
  refine ⟨λ h4, _, _⟩, 
  { rw ← base.eq_of_subset_base h2 h4 (empty_subset X),
    simp only },
  { intros h4, -- for some reason simp at h4 doesn't work with lambda
    simp only at h4,
    rw h4,
    exact h2 },
end

def uniform_matroid_on (α : Type*) [fintype α] (r : ℤ) : matroid α := 
  trunc.tr (free_matroid_on α) r 

lemma uniform_matroid_rank {r : ℤ} (hr : 0 ≤ r) (X : set α) :
  (uniform_matroid_on α r).r X = min r (size X) := 
trunc.r_eq _ hr _ 

lemma uniform_matroid_rank_univ {r : ℤ} (hr : 0 ≤ r) (hr' : r ≤ size (univ : set α)) : 
  (uniform_matroid_on α r).r univ = r :=
by {rw [uniform_matroid_rank hr, min_eq_left hr'],  }
 
lemma uniform_matroid_indep_iff {X : set α} {r : ℤ} (hr : 0 ≤ r)  : 
  is_indep (uniform_matroid_on α r) X ↔ size X ≤ r := 
by {rw [indep_iff_r, uniform_matroid_rank hr], finish}

lemma uniform_dual {r : ℤ} (hr : 0 ≤ r) (hrn : r ≤ size (univ : set α)) : 
  dual (uniform_matroid_on α r) 
  = uniform_matroid_on α (size (univ : set α) - r) :=
begin
  ext X, 
  rw [dual_r, uniform_matroid_rank hr, uniform_matroid_rank hr, 
      uniform_matroid_rank (_ : 0 ≤ size univ - r), min_eq_left hrn, 
      compl_size, ← min_add_add_left, ← min_sub_sub_right, min_comm], 
  congr, 
  all_goals {linarith}, 
end

def circuit_matroid_on (α : Type*) [fintype α]: matroid α := 
  uniform_matroid_on α (type_size α - 1)

@[simp] lemma circuit_matroid_rank (hα : nonempty α) (X : set α) :
  (circuit_matroid_on α).r X = min (size (univ : set α) - 1) (size X) := 
by {convert uniform_matroid_rank  _ X, linarith [one_le_type_size_of_nonempty hα]}

lemma circuit_matroid_iff_univ_circuit (hα : nonempty α){M : matroid α} :
  M = circuit_matroid_on α ↔ is_circuit M univ := 
begin
  refine ⟨λ h, _, λ h, _⟩, 
  rw [circuit_iff_r, h], 
  simp_rw circuit_matroid_rank hα, 
  from ⟨min_eq_left (by linarith), λ Y hY, min_eq_right (by linarith [size_strict_monotone hY])⟩, 
  ext X, rw circuit_matroid_rank hα, 
  rw circuit_iff_r at h, 
  have h' : X ⊂ univ ∨ X = univ := _ , 
  rcases h' with (h' | rfl ), 
  { rw [h.2 X h', eq_comm], from min_eq_right (by linarith [size_strict_monotone h'])}, 
  { rw [h.1, eq_comm], from min_eq_left (by linarith)}, 
  from subset_ssubset_or_eq (subset_univ _), 
end

lemma uniform_matroid_simple_iff (α : Type*)[fintype α] (hα : 2 ≤ type_size α){r : ℤ} (hr : 0 ≤ r) : 
  (unif.uniform_matroid_on α r).is_simple ↔ 2 ≤ r :=
begin
  rw type_size_eq at hα, 
  refine ⟨λ h, by_contra (λ hn, _), λ h, _⟩, 
  { push_neg at hn, 
    obtain ⟨X,hX⟩ := has_set_of_size  (by norm_num : (0 : ℤ) ≤ 2) hα, 
    have h' := (h X (subset_univ X) (le_of_eq hX)), 
    rw [indep_iff_r, hX] at h', 
    have h'' := rank_le_univ (uniform_matroid_on α r) X, 

    rw [h', uniform_matroid_rank hr, min_eq_left] at h'';
    linarith},
  rintros X - hX, 
  rw [indep_iff_r, uniform_matroid_rank hr, min_eq_right], 
  -- linarith fails here - why???
  exact le_trans hX h, 
end


lemma uniform_matroid_loopless_iff (α : Type*) [fintype α] {r : ℤ} (hr : 0 ≤ r) 
(hα : 1 ≤ type_size α):
  (unif.uniform_matroid_on α r).is_loopless ↔ 1 ≤ r := 
begin
  simp_rw [loopless_iff_all_nonloops, nonloop_iff_r], 
  by_cases (r ≤ 0), 
  { rw [le_antisymm h hr], 
    norm_num, 
    obtain ⟨e⟩ :=  nonempty_of_type_size_pos hα, 
    exact ⟨e, by {rw [uniform_matroid_rank, min_eq_left (size_nonneg _)]; norm_num,  }⟩}, 
  have : 1 ≤ r, rwa not_le at h, 
  convert (iff_true _).mpr _, simpa only [iff_true, eq_iff_iff], 
  intro e,
  rw uniform_matroid_rank hr, 
  rw [size_singleton, min_eq_right this], 
end

lemma unif_simple_of_two_le_r (α : Type*)[fintype α] {r : ℤ} (hr : 2 ≤ r) : 
  (unif.uniform_matroid_on α r).is_simple :=
begin
  rintros X - hX, 
  rw [indep_iff_r, uniform_matroid_rank (by linarith : 0 ≤ r), min_eq_right], 
  exact le_trans hX hr, 
end

end unif 


/-! 
  The canonical uniform matroid is defined to have a fixed ground set. 
-/
section canonical 

variables {a b : ℤ}

/-- the rank-a uniform matroid on b elements with ground set `fin' b`. Junk unless `0 ≤ a ≤ b`. -/
def canonical_unif (a b : ℤ) : 
  matroid (fin' b) := 
unif.uniform_matroid_on (fin' b) a

lemma canonical_unif_simple_iff (ha : 0 ≤ a) (hb : 2 ≤ b) : 
  (canonical_unif a b).is_simple ↔ 2 ≤ a := 
begin
 convert unif.uniform_matroid_simple_iff (fin' b) _ ha, 
 rwa size_fin' b (by linarith : 0 ≤ b), 
end

lemma canonical_unif_loopless_iff (ha : 0 ≤ a) (hb : 1 ≤ b): 
  (canonical_unif a b).is_loopless ↔ 1 ≤ a := 
begin
  convert unif.uniform_matroid_loopless_iff (fin' b) _ _, 
  assumption, 
  convert hb, rw size_fin' b (by linarith : 0 ≤ b), 
end
lemma canonical_unif_simple_of_two_le_r (ha : 2 ≤ a) : 
  (canonical_unif a b).is_simple :=
unif.unif_simple_of_two_le_r _ ha

@[simp] lemma canonical_unif_r (ha : 0 ≤ a) (X : set (fin' b)) :
  (canonical_unif a b).r X = min a (size X) :=
unif.uniform_matroid_rank ha _

end canonical 
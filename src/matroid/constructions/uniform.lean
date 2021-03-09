


import prelim.induction prelim.collections 
import matroid.rankfun matroid.indep matroid.submatroid.order matroid.simple 
import .truncation 

open matroid set 
open_locale classical

noncomputable theory 

namespace unif

variables {α : Type}[fintype α]

def free_matroid_on (α : Type)[fintype α]: matroid α := 
{ r := size,
  R0 := size_nonneg,
  R1 := λ X, le_refl (size X),
  R2 := λ X Y hXY, size_monotone hXY,
  R3 := λ X Y, le_of_eq (size_modular X Y),} 

lemma free_indep (X : set α) :
  (free_matroid_on α).is_indep X  := 
by rw [free_matroid_on, indep_iff_r]

lemma free_iff_univ_indep {M : matroid α}: 
   M = free_matroid_on α ↔ is_indep M univ := 
begin
  refine ⟨λ h, _, λ h,_⟩, 
  rw [indep_iff_r,h], finish,  
  ext X, simp_rw [free_matroid_on, ←indep_iff_r, indep_of_subset_indep (subset_univ X) h], 
end

def loopy (α : Type)[fintype α]: matroid α := 
{ r := λ X, 0, 
  R0 := λ X, le_refl 0, 
  R1 := λ X, size_nonneg X, 
  R2 := λ X Y hXY, le_refl 0, 
  R3 := λ X Y, rfl.ge }

lemma loopy_iff_univ_rank_zero {M : matroid α}:
  M = loopy α ↔ M.r univ = 0 := 
begin
  refine ⟨λ h, by finish, λ h,_⟩,  
  ext X, simp_rw [loopy], 
  have := rank_mono M (subset_univ X), 
  rw h at this, 
  linarith [M.rank_nonneg X], 
end

lemma loopy_matroid_indep_iff_empty {X : set α}:
  (loopy α).is_indep X ↔ X = ∅ := 
by {rw [indep_iff_r, ←size_zero_iff_empty, eq_comm], simp [loopy]}

def uniform_matroid_on (α : Type)[fintype α](r : ℤ) : matroid α := 
  trunc.tr (free_matroid_on α) r 

lemma uniform_matroid_rank {r : ℤ}(hr : 0 ≤ r)(X : set α) :
  (uniform_matroid_on α r).r X = min r (size X) := 
trunc.r_eq _ hr _ 

lemma uniform_matroid_rank_univ {r : ℤ}(hr : 0 ≤ r)(hr' : r ≤ size (univ : set α)): 
  (uniform_matroid_on α r).r univ = r :=
by {rw [uniform_matroid_rank hr, min_eq_left hr'],  }
 
lemma uniform_matroid_indep_iff {X : set α}{r : ℤ}(hr : 0 ≤ r)  : 
  is_indep (uniform_matroid_on α r) X ↔ size X ≤ r := 
by {rw [indep_iff_r, uniform_matroid_rank hr], finish}

lemma uniform_dual {r : ℤ}(hr : 0 ≤ r)(hrn : r ≤ size (univ : set α)): 
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

def circuit_matroid_on (α : Type)[fintype α]: matroid α := 
  uniform_matroid_on α (type_size α - 1)

@[simp] lemma circuit_matroid_rank (hα : nonempty α)(X : set α):
  (circuit_matroid_on α).r X = min (size (univ : set α) - 1) (size X) := 
by {convert uniform_matroid_rank  _ X, linarith [one_le_type_size_of_nonempty hα]}

lemma circuit_matroid_iff_univ_circuit (hα : nonempty α){M : matroid α}:
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

lemma uniform_matroid_simple_iff (α : Type)[fintype α](hα : 2 ≤ type_size α){r : ℤ}(hr : 0 ≤ r): 
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

end unif 

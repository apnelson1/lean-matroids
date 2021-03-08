


import prelim.induction prelim.collections 
import matroid.rankfun matroid.indep matroid.submatroid.order 
import .truncation 

open matroid set 
open_locale classical

noncomputable theory 

namespace unif

variables (α : Type)[fintype α]

def free_matroid_on : matroid α := 
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

def loopy : matroid α := 
{ r := λ X, 0, 
  R0 := λ X, le_refl 0, 
  R1 := λ X, size_nonneg X, 
  R2 := λ X Y hXY, le_refl 0, 
  R3 := λ X Y, rfl.ge }

def loopy_iff_univ_rank_zero {M : matroid α}:
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


def uniform_matroid_on {r : ℤ}(hr : 0 ≤ r) : matroid α := 
  trunc.tr (free_matroid_on α) hr 

@[simp] lemma uniform_matroid_rank {r : ℤ}(hr : 0 ≤ r)(X : set α) :
  (uniform_matroid_on α hr).r X = min r (size X) := 
by apply trunc.r_eq

lemma uniform_matroid_indep_iff (X : set α){r : ℤ}{hr : 0 ≤ r}  : 
  is_indep (uniform_matroid_on α hr) X ↔ size X ≤ r := 
by {rw [indep_iff_r, uniform_matroid_rank], finish}

lemma uniform_dual {r : ℤ}(hr : 0 ≤ r)(hrn : r ≤ size (univ : set α)): 
  dual (uniform_matroid_on α hr) 
  = uniform_matroid_on α (by linarith : 0 ≤ size (univ : set α) - r) :=
begin
  ext X, 
  simp_rw [dual, uniform_matroid_rank, compl_size, min_eq_left hrn], 
  rw [←min_add_add_left, ←(min_sub_sub_right), min_comm], simp, 
end

def circuit_matroid_on (hα : nonempty α) : matroid α := 
  uniform_matroid_on α (by linarith [one_le_size_univ_of_nonempty hα] : 0 ≤ size (univ : set α) - 1)

@[simp] lemma circuit_matroid_rank (hα : nonempty α)(X : set α):
  (circuit_matroid_on α hα).r X = min (size (univ : set α) - 1) (size X) := 
uniform_matroid_rank α _ X

lemma circuit_matroid_iff_univ_circuit (hα : nonempty α){M : matroid α}:
  M = circuit_matroid_on α hα ↔ is_circuit M univ := 
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

end unif 

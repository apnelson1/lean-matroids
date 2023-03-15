import .circuit 

noncomputable theory
open_locale classical

variables {E : Type*} [finite E] {M M₁ M₂ : matroid E} 
  {I C C' C₁ C₂ X Y Z F : set E} {e f x y z : E}

open set 

namespace matroid 

/-- The closure of a set in a matroid `M` -/
def matroid.cl (M : matroid E) : set E → set E :=
  λ X, {e | ∃ C ⊆ X ∪ {e}, M.circuit C ∧ e ∈ C}
--  λ X, {e | M.r X = M.r (insert e X)} 

/-- A flat of a matroid -/
def matroid.flat (M : matroid E) : set E → Prop := 
  λ F, ∃ X, F = M.cl X 

-- M.r X = M.r (insert e X)

lemma mem_cl_iff : 
  e ∈ M.cl X ↔ M.r X = M.r (insert e X) := 
begin
  split, 
  { rintros ⟨C, hCX, hC, heC⟩, 
    refine le_antisymm _ _, z},
end 

lemma subset_cl (M : matroid E) (X : set E) :
  X ⊆ M.cl X :=
λ x hx, by rw [mem_cl, insert_eq_self.mpr hx]  

@[simp] lemma r_cl (M : matroid E) (X : set E) : 
  M.r (M.cl X) = M.r X :=
(r_eq_of_r_all_insert_eq (M.subset_cl X) (λ e, id)).symm 

@[simp] lemma cl_cl (M : matroid E) (X : set E) : 
  M.cl (M.cl X) = M.cl X :=
begin
  ext x, 
  simp_rw [mem_cl, r_cl], 
  refine ⟨λ h, (M.r_mono (subset_insert _ _)).antisymm _, λ h, _⟩, 
  { rw h, 
    exact M.r_mono (insert_subset_insert (M.subset_cl _))}, 
  convert @r_union_eq_of_subset_of_r_eq _ _ M _ _ (M.cl X) (subset_insert x X) h using 1,
  { rw [union_eq_right_iff_subset.mpr (M.subset_cl X), r_cl]}, 
  rw [insert_union, union_eq_right_iff_subset.mpr (M.subset_cl X)],
end 

lemma r_insert_eq_add_one_of_not_mem_cl (h : e ∉ M.cl X) : 
  M.r (insert e X) = M.r X + 1 :=
r_insert_eq_add_one_of_r_ne (ne.symm h)

lemma not_mem_cl_of_r_insert_gt (h : M.r X < M.r (insert e X)) : 
  e ∉ M.cl X := 
h.ne 

lemma not_mem_cl_iff_r_insert_eq_add_one  : 
  e ∉ M.cl X ↔ M.r (insert e X) = M.r X + 1 :=
⟨r_insert_eq_add_one_of_not_mem_cl, λ h, not_mem_cl_of_r_insert_gt (by {rw h, apply lt_add_one})⟩ 

lemma mem_cl_insert (he : e ∉ M.cl X) (hef : e ∈ M.cl (insert f X)) : 
  f ∈ M.cl (insert e X) :=
begin
  by_contra hf, 
  rw not_mem_cl_iff_r_insert_eq_add_one at he hf, 
  rw [mem_cl, insert_comm, hf, he] at hef, 
  have h := M.r_insert_le_add_one X f,
  rw hef at h, 
  exact (lt_add_one _).not_le h, 
end  


end matroid 
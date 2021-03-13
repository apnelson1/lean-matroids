
import prelim.induction prelim.collections prelim.presetoid
import matroid.rankfun matroid.indep 
import .uniform .direct_sum

open matroid set 
open_locale classical big_operators 

noncomputable theory 


namespace partition

variables {α ι : Type*} [fintype α] (f : α → ι){b : ι → ℤ}

/-- the partition matroid - given a partition of α encoded by a function f : α → ι, the independent 
sets are those whose intersection with each cell i has size at most b i -/
def M (f : α → ι) (b : ι → ℤ) : matroid α := idsum.M f (λ i, unif.uniform_matroid_on _ (b i))

lemma indep_iff (hb : ∀ i, 0 ≤ b i) (X : set α) : 
  (M f b).is_indep X ↔ ∀ i, size {x ∈ X | f x = i} ≤ b i :=
begin
  simp_rw [M, idsum.indep_iff, ← idsum.size_coe_eq], 
  refine ⟨λ h, λ i, _, λ h, λ i, _⟩, 
  {exact (unif.uniform_matroid_indep_iff (hb i)).mp (h i), }, 
  exact (unif.uniform_matroid_indep_iff (hb i)).mpr (h i), 
end 

lemma r_eq (hb : ∀ i, 0 ≤ b i) (X : set α) : 
  (M f b).r X = ∑ᶠ (i : ι), (min (b i) (size {x ∈ X | f x = i})) :=
begin
  simp_rw [M, idsum.r_eq, ← idsum.size_coe_eq],
  convert rfl, ext i, rw unif.uniform_matroid_rank (hb i), 
end 

end partition

section presetoid_class

variables {α : Type*} [fintype α] (S : presetoid α)

namespace presetoid_matroid

/- Given a presetoid S on α, we construct a matroid on α whose independent sets are those containing
no elements of the kernel of α, and at most one element of each class of α -/

def partition_fn : set α → ℤ := 
  λ X, ite (X = ∅) 0 1 

lemma partition_fn_nonneg: 
  ∀ (X : set α), 0 ≤ partition_fn X := 
λ X, by {unfold partition_fn, split_ifs; norm_num,}

def M : matroid α := partition.M S.cl partition_fn

lemma M_def : 
  M S = partition.M S.cl partition_fn := 
rfl 

lemma r_eq (X : set α) : 
  (M S).r X = size {P ∈ S.classes | (X ∩ P).nonempty} := 
begin
  rw [M_def, partition.r_eq, ← sum_size_fiber_eq_size _ id], 
  rotate, apply_instance, apply partition_fn_nonneg, 
  --{ swap, apply_instance} swap, apply partition_fn_nonneg}, 
  convert rfl, funext, 
  rw partition_fn, dsimp only [id.def], split_ifs, 
  { subst h, 
    rw min_eq_left (size_nonneg {x ∈ X | S.cl x = ∅}), 
    simp only [and_imp, mem_sep_eq, size_zero_iff_empty, presetoid.mem_classes_iff, 
    id.def, sep_in_eq_empty_iff, exists_imp_distrib], 
    rintros P x hx rfl - hx', 
    exact S.cl_eq_empty_iff.mp hx' hx, },
  by_cases hi : ∃ x ∈ X, S.cl x = i, swap,
  { convert (min_eq_right (zero_le_one : (0 :ℤ) ≤ 1 )).symm,  
    { simp only [and_imp, mem_sep_eq, size_zero_iff_empty, presetoid.mem_classes_iff, 
        sep_in_eq_empty_iff, exists_imp_distrib], 
      rintros s x hx rfl hxX rfl,
      obtain ⟨x',hx'⟩ := hxX, 
      rw mem_inter_iff at hx', 
      exact hi ⟨x', hx'.1, S.cl_eq_cl_of_rel (S.mem_cl_iff.mp hx'.2)⟩ }, 
    simp only [size_zero_iff_empty, sep_in_eq_empty_iff], 
    exact λ x hx hS, hi ⟨x,hx,hS⟩},
  obtain ⟨x,hx,rfl⟩ := hi, 
  rw [presetoid.cl_eq_empty_iff, not_not] at h, 
  convert (λ m hm, by {rw min_eq_left hm} : (∀ m : ℤ, 1 ≤ m → 1 = min 1 m)) _ _,  
  { rw size_one_iff_eq_singleton, 
    refine ⟨S.cl x, ext_iff.mpr (λ f, _)⟩,
    simp only [mem_sep_eq, presetoid.mem_classes_iff, mem_singleton_iff, 
    and_iff_right_iff_imp],  
    rintros rfl, 
    exact ⟨⟨x, h, rfl⟩,⟨x,mem_inter hx (S.mem_cl_iff.mpr h)⟩⟩}, 
  exact one_le_size_iff_has_mem.mpr ⟨x, by {simpa using hx}⟩, 
end

lemma indep_iff (I : set α) :
  (M S).is_indep I ↔ disjoint I S.kernel ∧ ∀ P ∈ S.classes, size (I ∩ P) ≤ 1 :=
begin
  rw [M_def, partition.indep_iff, partition_fn, disjoint_right], 
  swap, apply partition_fn_nonneg, 
  simp only [and_imp, presetoid.mem_classes_iff, exists_imp_distrib, S.mem_kernel_iff, not_imp_not], 
  refine ⟨λ h, ⟨by {simpa using h ∅}, _⟩, λ h P, _⟩, 
  { rintros P x hx rfl, 
    convert h (S.cl x),
    { ext, rw [eq_comm, S.cl_eq_cl_iff hx, S.rel_comm, ← S.mem_cl_iff], refl},
    suffices : (S.cl x) ≠ ∅, split_ifs; tauto,   
    simp_rw [ne_empty_iff_has_mem, S.mem_cl_iff], 
    exact ⟨x,hx⟩ },
  by_cases hP : ∃ x, P = S.cl x, 
  { obtain ⟨x,rfl⟩ := hP, 
    by_cases hx : S.rel x x, 
    { convert h.2 (S.cl x) _ hx rfl, 
      {ext y, rw [eq_comm, S.cl_eq_cl_iff hx, S.rel_comm, S.mem_cl_iff]},
      simpa using hx},
    rw [S.cl_eq_empty_iff.mpr hx], 
    simpa using h.1},
  convert (λ Q, by {split_ifs; norm_num} : ∀ Q: Prop, (0 : ℤ) ≤ ite Q (0 : ℤ) 1) _ , 
  rw [size_zero_iff_empty, sep_in_eq_empty_iff], 
  exact λ x hx hxP, hP ⟨x, hxP.symm⟩, 
end




end presetoid_matroid

end presetoid_class 





 
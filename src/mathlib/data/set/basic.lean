import data.set.basic

variables {α : Type*} {s : set α} {a : α}

namespace set

lemma singleton_inter_eq_of_mem {x : α} (hx : x ∈ s) :
  {x} ∩ s = {x} :=
(inter_subset_left _ _).antisymm (subset_inter subset_rfl (singleton_subset_iff.mpr hx))

lemma inter_singleton_eq_of_mem {α : Type*} {x : α} {s : set α} (hx : x ∈ s) :
  s ∩ {x} = {x} :=
(inter_subset_right _ _).antisymm (subset_inter (singleton_subset_iff.mpr hx) subset_rfl)

@[simp] lemma not_mem_diff_singleton {α : Type*} (x : α) (s : set α) :
  x ∉ s \ {x} :=
not_mem_diff_of_mem $ mem_singleton _

end set
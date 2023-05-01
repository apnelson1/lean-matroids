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

lemma ssubset_iff_subset_diff_singleton {α : Type*} {s t : set α} :
  s ⊂ t ↔ ∃ x ∈ t, s ⊆ t \ {x} :=
begin
  refine ⟨λ h, _,_⟩, 
  { obtain ⟨x,hxt,hxs⟩ := exists_of_ssubset h,  
    refine ⟨x, hxt, subset_diff_singleton h.subset hxs⟩ },
   rintro ⟨x, hxt, hs⟩, 
  exact hs.trans_ssubset (diff_singleton_ssubset.mpr hxt), 
end 

lemma inter_subset_union (s t : set α) : s ∩ t ⊆ s ∪ t := 
(inter_subset_left _ _).trans (subset_union_left _ _)  

lemma union_diff_cancel_of_subset {s s' : set α} (t : set α) (h : s' ⊆ s) : s ∪ (t \ s') = s ∪ t := 
by rw [←union_eq_self_of_subset_right h, union_assoc, union_diff_self, union_assoc]

@[simp] lemma symm_diff_univ (s : set α) : s ∆ univ = sᶜ := symm_diff_top s
  
end set
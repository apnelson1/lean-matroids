import data.set.basic

variables {α : Type*} {s t r : set α} {a : α}

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

lemma has_subset.subset.ssubset_of_nonempty_diff {α : Type*} {s t : set α} 
  (hst : s ⊆ t) (he : (t \ s).nonempty) : s ⊂ t :=
hst.ssubset_of_ne (by { rintro rfl, simpa using he })

lemma inter_subset_union (s t : set α) : s ∩ t ⊆ s ∪ t := 
(inter_subset_left _ _).trans (subset_union_left _ _)  

lemma union_diff_cancel_of_subset {s s' : set α} (t : set α) (h : s' ⊆ s) : s ∪ (t \ s') = s ∪ t := 
by rw [←union_eq_self_of_subset_right h, union_assoc, union_diff_self, union_assoc]

@[simp] lemma symm_diff_univ (s : set α) : s ∆ univ = sᶜ := symm_diff_top s
  
/-- `r` is an explicit parameter here for ease of rewriting. -/
lemma diff_subset_diff_iff (r : set α) (hs : s ⊆ r) (ht : t ⊆ r) : (r \ s) ⊆ (r \ t) ↔ t ⊆ s :=
begin
  rw [subset_diff, and_iff_right (diff_subset _ _), ←subset_compl_iff_disjoint_left, diff_eq, 
    compl_inter, compl_compl], 
  exact ⟨λ h x hxt, (h hxt).elim (λ h', (h' (ht hxt)).elim) id, 
    λ h, h.trans (subset_union_right _ _)⟩,
end   

lemma subset_diff_iff_disjoint_left (hsr : s ⊆ r) : s ⊆ r \ t ↔ disjoint s t :=
by rw [subset_diff, and_iff_right hsr]

lemma subset_diff_iff_disjoint_right (hsr : s ⊆ r) : s ⊆ r \ t ↔ disjoint t s :=
by rw [subset_diff_iff_disjoint_left hsr, disjoint.comm] 

lemma subset_diff_comm (hsr : s ⊆ r) (htr : t ⊆ r) : s ⊆ r \ t ↔ t ⊆ r \ s :=
by rw [subset_diff_iff_disjoint_left hsr, disjoint.comm, subset_diff_iff_disjoint_left htr]

lemma diff_eq_diff_iff_inter_eq_inter : r \ s = r \ t ↔ r ∩ s = r ∩ t := 
by simp only [set.ext_iff, mem_diff, and.congr_right_iff, mem_inter_iff, not_iff_not]

@[simp] lemma diff_inter_diff_right (s t r : set α) : (s \ r) ∩ (t \ r) = (s ∩ t) \ r := 
by { ext, simp only [mem_inter_iff, mem_diff], tauto }

lemma inter_diff_right_comm (s t r : set α) : s ∩ t \ r = (s \ r) ∩ t := 
by rw [diff_eq, inter_right_comm, ←diff_eq]

end set
import .set
-- Singles

open set 

local attribute [instance] classical.prop_decidable

variables {A : Type}
  


lemma elem_coe_inj_iff {e f : A} :
  ({e} : set A) = ({f}  : set A) ↔ e = f := 
by {exact singleton_eq_singleton_iff}

lemma singleton_nonmem_iff {e : A}{X : set A} : 
  e ∉ X ↔ ¬({e}: set A) ⊆ X := 
by rw [not_iff_not, singleton_subset_iff]

lemma singleton_ne_empty (e : A) : 
  ({e}: set A) ≠ ∅ := 
λ h, by {rw set.ext_iff at h, exact not_mem_empty e ((h e).mp (by simp)),}--have := size_singleton e, rw [h,size_empty] at this, linarith}

@[simp] lemma singleton_nonmem_compl_self (e : A) :
  e ∉ ({e}: set A)ᶜ := 
λ h, by {rw ←singleton_subset_iff at h, from singleton_ne_empty e (subset_own_compl h)}

lemma subset_of_mem_of_subset {e : A}{X Y : set A}(h : e ∈ X)(h' : X ⊆ Y): 
  {e} ⊆ Y := 
singleton_subset_iff.mpr (mem_of_mem_of_subset h h')

lemma union_subset_of_mem_of_mem {e f : A}{X : set A}:
  e ∈ X → f ∈ X → ({e} ∪ {f} : set A) ⊆ X := 
λ he hf, by {refine union_of_subsets _ _, tidy} 

lemma union_singleton_subset_of_subset_mem {X Y : set A}{e : A}:
  X ⊆ Y → e ∈ Y → X ∪ {e} ⊆ Y := 
by {rw ←singleton_subset_iff, apply union_of_subsets } 

lemma ne_empty_has_mem {X : set A}  : 
  X ≠ ∅ → ∃ e, e ∈ X := 
by {rw [ne_empty_iff_nonempty, nonempty_def], from id}

lemma ne_empty_iff_has_mem {X : set A} : 
  X ≠ ∅ ↔ ∃ e, e ∈ X :=
⟨λ h, ne_empty_has_mem h, λ h, λ hb, by {cases h with e he, rw hb at he, exact not_mem_empty e he}⟩ 

lemma ne_univ_iff_has_nonmem {X : set A}:
  X ≠ univ ↔ ∃ e, e ∉ X := 
by {rw [←not_forall, not_iff_not], refine ⟨λ h x, _, λ h, _⟩, rw h, from mem_univ x, ext, tidy}

lemma nested_singletons_eq {e f: A} (hef : ({e}: set A) ⊆ ({f} : set A)):
   e = f :=
by rwa [singleton_subset_iff, mem_singleton_iff] at hef 
  
lemma nonmem_disjoint {e : A} {X : set A}: 
  e ∉ X → ({e} ∩ X : set A) = ∅ :=
by tidy
  
lemma nonmem_disjoint_iff {e : A} {X : set A}: 
  e ∉ X ↔ {e} ∩ X = ∅ := 
by {refine ⟨λ h, nonmem_disjoint h, λ h he, _⟩, 
  rw [←singleton_subset_iff, subset_def_inter,h] at he, 
  exact singleton_ne_empty e he.symm,}

lemma inter_distinct_singles {e f : A}: 
  e ≠ f → ({e} ∩ {f} : set A) = ∅ := 
λ hef, nonmem_disjoint (λ h, hef (nested_singletons_eq (singleton_subset_iff.mpr h)))

lemma mem_union_of_mem_left {e : A}{X : set A}(Y : set A)(h : e ∈ X) : 
  e ∈ X ∪ Y :=
mem_of_mem_of_subset h (subset_union_left X Y)

lemma mem_union_of_mem_right {e : A}{X : set A}(Y : set A)(h : e ∈ Y) : 
  e ∈ X ∪ Y :=
mem_of_mem_of_subset h (subset_union_right X Y)

lemma singleton_nonmem_compl_self_iff {X : set A}{e : A} :
  e ∉ Xᶜ ↔ e ∈ X  := 
by {rw ←mem_compl_iff, rw [compl_compl]}

lemma elem_union_iff {e : A} {X Y : set A} : 
  e ∈ X ∪ Y ↔ e ∈ X ∨ e ∈ Y :=
by simp only [mem_union_eq]

lemma elem_inter_iff {e : A}{X Y : set A}: 
  e ∈ X ∩ Y ↔ e ∈ X ∧ e ∈ Y := 
mem_inter_iff e X Y

lemma elem_inter {e : A}{X Y : set A} : 
  e ∈ X → e ∈ Y → e ∈ X ∩ Y := 
mem_inter

lemma nonmem_inter_iff {e : A} {X Y : set A} :
   e ∉ X ∩ Y ↔ e ∉ X ∨ e ∉ Y := 
by rw [←mem_compl_iff, compl_inter, elem_union_iff, mem_compl_iff, mem_compl_iff] 

lemma elem_diff_iff {e : A}{X Y : set A} : 
  e ∈ X \ Y ↔ e ∈ X ∧ e ∉ Y :=
by simp only [mem_diff]
  
lemma subset_iff_elems_contained {X Y : set A} :
  X ⊆ Y ↔ ∀ e, e ∈ X → e ∈ Y := 
by refl 

lemma elem_of_subset {X Y: set A}{e : A}:
  X ⊆ Y → e ∈ X → e ∈ Y := 
λ h he, subset_iff_elems_contained.mp h e he 


lemma nonmem_of_nonmem_diff {X Y : set A}{e : A} :
  e ∉ X \ Y → e ∉ Y → e ∉ X := 
by tidy

lemma nonmem_diff_of_nonmem {X : set A}(Y : set A){e : A}: 
  e ∉ X → e ∉ X\Y :=
by tidy 

lemma eq_iff_same_elems {X Y : set A} :
  X = Y ↔ ∀ e, e ∈ X ↔ e ∈ Y :=
⟨λ h e, by rw h, λ h, by {ext, from h x}⟩

lemma nonmem_removal (X : set A)(e : A) :
  e ∉ X \ {e} := 
by tidy 

lemma subset_of_removal {X Y : set A}{e : A} :
  X ⊆ Y → e ∉ X → X ⊆ Y \ {e} :=
by tidy
  
lemma subset_of_subset_add_nonmem {X Y: set A}{e : A} :
  X ⊆ Y ∪ {e} → e ∉ X → X ⊆ Y :=
begin
  intros hXY heX, 
  simp only [subset_def_inter] at hXY ⊢, 
  rw [nonmem_disjoint_iff, inter_comm] at heX,
  rw [inter_distrib_left, heX, union_empty] at hXY, 
  from hXY, 
end


lemma removal_subset_of {X Y : set A}{e : A} :
  X ⊆ Y ∪ {e} → X \ {e} ⊆ Y :=
begin
  intro h, 
  simp only [subset_def_inter, diff_eq] at h ⊢, 
  nth_rewrite 1 ← h,
  rw [inter_distrib_left, inter_distrib_right, inter_assoc _ {e}, inter_right_comm _ _ Y], 
  simp only [inter_compl_self, union_empty, inter_empty], 
end
  
lemma ssub_of_add_compl {X : set A} {e : A} : 
  e ∈ Xᶜ → X ⊂ X ∪ {e} := 
begin
  refine λ hXe, ssubset_of_subset_ne (subset_union_left _ _) _, intro h, rw [h, compl_union] at hXe, 
  cases hXe, solve_by_elim,
end

lemma ssub_of_add_nonmem {X : set A} {e : A}: 
  e ∉ X → X ⊂ X ∪ {e} := 
λ hXe, ssub_of_add_compl (by {rwa mem_compl_iff })

lemma ssubset_of_add_nonmem_iff {X : set A} {e : A} :
  e ∉ X ↔ X ⊂ X ∪ {e} :=
by {refine ⟨λ h, ssub_of_add_nonmem h, λ h, λ hex, _⟩, rw [←singleton_subset_iff, subset_def_union, union_comm] at hex, rw hex at h, from ssubset_irrefl _ h}

lemma add_elem {X : set A} {e : A}: 
  e ∈ X → X ∪ {e} = X := 
λ h, by {tidy,}

lemma elem_diff_ssubset {X Y : set A} : 
  X ⊂ Y → ∃ e, e ∈ Y \ X :=
λ h, ssubset_diff_nonempty h
    
lemma elem_only_larger_ssubset {X Y : set A} :
  X ⊂ Y → ∃ e, e ∈ Y ∧ e ∉ X :=
λ h, by {have := elem_diff_ssubset h, simp_rw elem_diff_iff at this, assumption}


lemma compl_single_remove {X : set A} {e : A} : 
  e ∈ X → (X \ {e})ᶜ = Xᶜ ∪ {e} := 
λ _, by rw [diff_eq, compl_inter, compl_compl]

lemma remove_add_elem {X : set A} {e : A}: 
  e ∈ X → (X \ {e}) ∪ {e} = X := 
λ heX, by {rw [←singleton_subset_iff, subset_def_union,union_comm] at heX, 
          rw [diff_eq, union_distrib_right, compl_union_self, inter_univ, heX]}
   
lemma add_remove_nonmem {X : set A} {e : A}: 
  e ∉ X → (X ∪ {e}) \ {e} = X := 
begin
  intro h, 
  rw [←mem_compl_iff, ←singleton_subset_iff, subset_def_union] at h, 
  rw [diff_eq, inter_distrib_right], 
  simp only [inter_compl_self, union_empty], 
  rw [←compl_compl_inter_left, inter_comm, compl_inj_iff] at h, 
  from h, 
end


lemma remove_single_subset (X : set A) (e : A) : 
  X \ {e} ⊆ X := 
diff_subset X {e} 

lemma nonmem_of_subset_remove_single (X : set A) (e : A):
  X ⊆ X \ {e} → e ∉ X :=
by {rw diff_eq, tidy} 

lemma ne_of_mem_diff {X : set A}{e f: A}(h : e ∈ X \ {f}):
  e ≠ f := 
λ h', by {rw h' at h, apply nonmem_removal _ _ h,}

lemma ssubset_of_remove_mem {X : set A} {e : A}(heX : e ∈ X) :
   X \ {e} ⊂ X := 
ssubset_of_subset_ne 
  (diff_subset _ _) 
  (λ h, by {rw [ext_iff] at h, specialize h e, rw mem_diff at h, tauto,  })



lemma add_from_nonempty_diff {X Y : set A} :
  X ⊂ Y ↔ ∃ e : A, e ∉ X ∧ X ∪ {e} ⊆ Y := 
begin
  refine ⟨λ h,_, λ h, ssubset_of_subset_ne _ (λ hne, _)⟩, 
  cases nonempty_def.mp (ssubset_diff_nonempty h) with e he, 
  { rw mem_diff at he, exact ⟨e, he.2,union_of_subsets h.1 (singleton_subset_iff.mpr he.1)⟩, },
  { rcases h with ⟨e, h, h'⟩, exact subset.trans (subset_union_left _ _) h', },
  rcases h with ⟨e, h,h'⟩,  rw ←hne at h', 
  exact ssubset_irrefl _ (subset.lt_of_lt_of_le (ssub_of_add_nonmem h) h'), 
end

 
lemma aug_of_ssubset {X Y : set A} : 
  X ⊂ Y → ∃ Z (e : A), X ⊆ Z ∧ Z ⊂ Y ∧ Z ∪ {e} = Y :=
begin
  intro hXY, 
  rcases elem_only_larger_ssubset hXY with ⟨e, ⟨heY, heX⟩⟩, 
  refine ⟨Y \ {e}, e, ⟨subset_of_removal hXY.1 heX ,⟨ _, _⟩ ⟩⟩,
  from ssubset_of_remove_mem heY, 
  from remove_add_elem heY, 
end 

lemma exchange_comm {X : set A}{e f : A} : 
  e ∈ X → f ∉ X → (X \ {e}) ∪ {f} = (X ∪ {f}) \ {e} := 
begin
  intros he hf, 
  simp only [diff_eq], rw [inter_distrib_right],
  have : ({f} ∩ {e}ᶜ : set A) = {f} := 
    by {rw [←subset_def_inter, ←disjoint_iff_subset_compl, inter_distinct_singles], by_contra h, push_neg at h, rw h at hf, from hf he},
  rw this, 
end

lemma union_singletons_eq_pair {e f : A}:
  ({e} : set A) ∪ ({f} : set A) = {e,f} :=
singleton_union

lemma remove_remove_single (X : set A)(e f : A):
  X \ {e} \ {f} = X \ {e,f} :=
by rw [diff_diff, union_singletons_eq_pair]

lemma subset_single {e : A}{X : set A} :
  X ⊆ {e} → X = ∅ ∨ X = {e} := 
begin
  rw subset_singleton_iff,  intro h', 
  by_cases h'' : e ∈ X, 
  right, 
  { ext, rw ←singleton_subset_iff at h'', exact ⟨λ h, h' _ h, λ h, mem_of_mem_of_subset h h''⟩, }, 
  left, 
  ext, simp only [set.mem_empty_eq, iff_false], 
  exact λ h, h'' (by rwa ←(h' _ h)),
end

lemma ssubset_pair {e f : A}{X : set A}:
  X ⊂ {e,f} → X = ∅ ∨ (X = {e}) ∨ (X = {f}) :=
begin
  intro h, rw [ssubset_iff_subset_ne, ←union_singletons_eq_pair] at h, 
  cases h with hs hne, rw [subset_def_inter, inter_distrib_left] at hs,
  cases subset_single (inter_subset_right X {e}),
  rw [h, empty_union, ←subset_def_inter] at hs, cases subset_single hs, exact or.inl h_1, apply or.inr, exact or.inr h_1,
  rw [inter_comm, ←subset_def_inter] at h, apply or.inr, cases subset_single (inter_subset_right X {f}),
  rw [h_1, union_empty, ←subset_def_inter] at hs,  exact or.inl (subset.antisymm hs h), 
  rw [subset_def_inter, inter_comm] at h,
  rw [h_1, h] at hs, exfalso, exact hne hs.symm, 
end

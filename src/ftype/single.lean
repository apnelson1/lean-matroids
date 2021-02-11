import .basic
namespace ftype 
-- Singles

open set 

local attribute [instance] classical.prop_decidable

variables {A : ftype}

instance coe_single {A : ftype} : has_coe A (set A) := ⟨λ e, {e}⟩  

lemma elem_coe_inj_iff {e f : A} :
  (e : set A) = (f : set A) ↔ e = f := 
by {unfold_coes, tidy}

lemma elem_iff_subset {e : A}{X : set A} :
   e ∈ X ↔ (e: set A) ⊆ X := 
by tidy 

lemma nonelem_iff_subset {e : A}{X : set A} : 
  e ∉ X ↔ ¬(e: set A) ⊆ X := 
by rw elem_iff_subset

lemma elem_to_subset {e : A}{X : set A} : 
  e ∈ X → (e : set A) ⊆ X := 
elem_iff_subset.mp  

lemma subset_to_elem  {e : A}{X : set A} :
  (e : set A) ⊆ X → e ∈ X := 
elem_iff_subset.mpr

@[simp] lemma size_single {A : ftype} (e : A) :
   size (e : set A) = 1 := by apply size_single_ax

@[simp] lemma size_single_set {A : ftype} (e : A) :
   size ({e} : set A) = 1 := by apply size_single_ax

lemma single_ne_empt (e : A) : 
  (e: set A) ≠ ∅ := 
λ h, by {have := size_single e, rw [h,size_empty] at this, linarith}

@[simp] lemma single_nonempty (e : A) : 
  (e: set A).nonempty  := 
by {rw ←ne_empty_iff_nonempty, from single_ne_empt e} 

@[simp] lemma nonelem_empty (e : A) : 
  e ∉ (∅: set A) := 
by {rw nonelem_iff_subset, intro h, replace h := size_monotone h, simp at h, linarith [size_empty]}

@[simp] lemma elem_univ (e : A):
  e ∈ (univ : set A) := 
by {rw [elem_iff_subset], from subset_univ _,}

@[simp] lemma nonelem_compl (e : A) :
  e ∉ (e: set A)ᶜ := 
λ h, by {rw elem_iff_subset at h, from single_ne_empt e (subset_own_compl h)}

lemma subset_compl_single_iff {e : A}{X : set A}: 
  X ⊆ (e : set A)ᶜ ↔ e ∉ X := 
by tidy 

lemma elem_of_elem_of_subset {e : A}{X Y : set A}: 
  e ∈ X → X ⊆ Y → e ∈ Y := 
mem_of_mem_of_subset

lemma subset_of_elem_of_subset {e : A}{X Y : set A}: 
  e ∈ X → X ⊆ Y → (e : set A) ⊆ Y := 
by {rw ←@elem_iff_subset _ _ Y, from mem_of_mem_of_subset}

lemma union_subset_of_elem_of_elem {e f : A}{X : set A}:
  e ∈ X → f ∈ X → (e ∪ f : set A) ⊆ X := 
λ he hf, by {refine union_is_ub _ _, tidy} 

lemma subset_of_union_subset_elem {X Y : set A}{e : A}:
  X ⊆ Y → e ∈ Y → X ∪ e ⊆ Y := 
by {rw elem_iff_subset, apply union_is_ub, } 

lemma ne_empty_has_elem {X : set A}  : 
  X ≠ ∅ → ∃ e, e ∈ X := 
by {rw [ne_empty_iff_nonempty, nonempty_def], from id}

lemma ne_empty_iff_has_elem {X : set A} : 
  X ≠ ∅ ↔ ∃ e, e ∈ X :=
⟨λ h, ne_empty_has_elem h, λ h, λ hb, by {cases h with e he, rw hb at he, exact nonelem_empty e he}⟩ 

lemma ne_univ_iff_has_nonelem {X : set A}:
  X ≠ univ ↔ ∃ e, e ∉ X := 
by {rw [←not_forall, not_iff_not], refine ⟨λ h x, _, λ h, _⟩, rw h, from elem_univ x, ext, tidy}

lemma size_pos_has_elem {X : set A}: 
  0 < size X → ∃ e, e ∈ X := 
λ h, (ne_empty_iff_has_elem.mp (λ h', by {rw [h',size_empty] at h, exact lt_irrefl 0 h}))

lemma size_pos_iff_has_elem {X : set A}: 
  0 < size X ↔ ∃ e, e ∈ X := 
⟨λ h, size_pos_has_elem h, λ h, by {cases h with e he, have := size_monotone (elem_to_subset he), rw size_single at this, linarith}⟩ 

lemma size_zero_iff_has_no_elem {X : set A}:
  size X = 0 ↔ ¬ ∃ e, e ∈ X := 
begin
  rw [iff.comm, ←not_iff, ←size_pos_iff_has_elem, not_iff], 
  refine ⟨λ h, _, λ h, by linarith ⟩ ,
  linarith [size_nonneg X, not_lt.mp h]
end

lemma nested_singles_eq {e f: A} :
  (e: set A) ⊆ (f : set A) → e = f :=
begin
  intro hef, rw ←elem_coe_inj_iff, 
  from eq_of_eq_size_subset hef (by {simp_rw [size_single]}), 
end

lemma nonelem_disjoint {e : A} {X : set A}: 
  e ∉ X → (e ∩ X : set A) = ∅ :=
by tidy
  
lemma nonelem_disjoint_iff {e : A} {X : set A}: 
  e ∉ X ↔ (e ∩ X : set A) = ∅ := 
by {refine ⟨λ h, nonelem_disjoint h, λ h he, _⟩, rw [elem_iff_subset, subset_def_inter, h, eq_comm] at he, exact single_ne_empt _ he}

lemma inter_distinct_singles {e f : A}: 
  e ≠ f → (e ∩ f : set A) = ∅ := 
λ hef, nonelem_disjoint (λ h, hef (nested_singles_eq (elem_to_subset h)))

lemma elem_compl_iff {X : set A}{e : A} :
  e ∈ Xᶜ ↔ e ∉ X := 
by simp only [mem_compl_eq]

lemma elem_union_left {e : A}{X Y : set A} : 
  e ∈ X → e ∈ X ∪ Y :=
λ h, elem_of_elem_of_subset h (subset_union_left X Y)

lemma elem_union_right {e : A}{X Y : set A} : 
  e ∈ Y → e ∈ X ∪ Y :=
λ h, elem_of_elem_of_subset h (subset_union_right X Y)

lemma nonelem_compl_iff {X : set A}{e : A} :
  e ∉ Xᶜ ↔ e ∈ X  := 
by {rw ←elem_compl_iff, rw [compl_compl]}

lemma elem_union_iff {e : A} {X Y : set A} : 
  e ∈ X ∪ Y ↔ e ∈ X ∨ e ∈ Y :=
by simp only [mem_union_eq]

lemma elem_inter_iff {e : A}{X Y : set A}: 
  e ∈ X ∩ Y ↔ e ∈ X ∧ e ∈ Y := 
mem_inter_iff e X Y

lemma elem_inter {e : A}{X Y : set A} : 
  e ∈ X → e ∈ Y → e ∈ X ∩ Y := 
mem_inter

lemma nonelem_inter_iff {e : A} {X Y : set A} :
   e ∉ X ∩ Y ↔ e ∉ X ∨ e ∉ Y := 
by rw [←elem_compl_iff, compl_inter, elem_union_iff, elem_compl_iff, elem_compl_iff] 

lemma elem_diff_iff {e : A}{X Y : set A} : 
  e ∈ X \ Y ↔ e ∈ X ∧ e ∉ Y :=
by simp only [mem_diff]
  
lemma subset_iff_elems_contained {X Y : set A} :
  X ⊆ Y ↔ ∀ e, e ∈ X → e ∈ Y := 
by refl 

lemma elem_of_subset {X Y: set A}{e : A}:
  X ⊆ Y → e ∈ X → e ∈ Y := 
λ h he, subset_iff_elems_contained.mp h e he 


lemma nonelem_of_nonelem_diff {X Y : set A}{e : A} :
  e ∉ X \ Y → e ∉ Y → e ∉ X := 
by tidy

lemma nonelem_diff_of_nonelem {X : set A}(Y : set A){e : A}: 
  e ∉ X → e ∉ X\Y :=
by tidy 

lemma eq_iff_same_elems {X Y : set A} :
  X = Y ↔ ∀ e, e ∈ X ↔ e ∈ Y :=
⟨λ h e, by rw h, λ h, by {ext, from h x}⟩

lemma nonelem_removal (X : set A)(e : A) :
  e ∉ X \ e := 
by tidy 

lemma subset_of_removal {X Y : set A}{e : A} :
  X ⊆ Y → e ∉ X → X ⊆ Y \ e :=
by tidy
  
lemma subset_of_subset_add_nonelem {X Y: set A}{e : A} :
  X ⊆ Y ∪ e → e ∉ X → X ⊆ Y :=
begin
  intros hXY heX, 
  simp only [subset_def_inter] at hXY ⊢, 
  rw [nonelem_disjoint_iff, inter_comm] at heX,
  rw [inter_distrib_left, heX, union_empty] at hXY, 
  from hXY, 
end


lemma removal_subset_of {X Y : set A}{e : A} :
  X ⊆ Y ∪ e → X \ e ⊆ Y :=
begin
  intro h, 
  simp only [subset_def_inter, diff_def] at h ⊢, 
  nth_rewrite 1 ← h,
  rw [inter_distrib_left, inter_distrib_right, inter_assoc _ (e: set A), inter_right_comm _ _ Y], 
  simp only [inter_compl, union_empty, inter_empty], 
end

lemma ssub_of_add_compl {X : set A} {e : A} : 
  e ∈ Xᶜ → X ⊂ X ∪ e := 
begin
  refine λ hXe, ssubset_of_subset_ne (subset_union_left _ _) _, intro h, rw [h, compl_union] at hXe, 
  cases hXe, solve_by_elim,
end

lemma ssub_of_add_nonelem {X : set A} {e : A}: 
  e ∉ X → X ⊂ X ∪ e := 
λ hXe, ssub_of_add_compl (elem_compl_iff.mpr hXe)

lemma ssubset_of_add_nonelem_iff {X : set A} {e : A} :
  e ∉ X ↔ X ⊂ X ∪ e :=
by {refine ⟨λ h, ssub_of_add_nonelem h, λ h, λ hex, _⟩, rw [elem_iff_subset, subset_def_union, union_comm] at hex, rw hex at h, from ssubset_irrefl _ h}

lemma add_elem {X : set A} {e : A}: 
  e ∈ X → X ∪ e = X := 
λ h, by {tidy,}

lemma elem_diff_ssubset {X Y : set A} : 
  X ⊂ Y → ∃ e, e ∈ Y \ X :=
λ h, ssubset_diff_nonempty h
   
lemma elem_only_larger_ssubset {X Y : set A} :
  X ⊂ Y → ∃ e, e ∈ Y ∧ e ∉ X :=
λ h, by {have := elem_diff_ssubset h, simp_rw elem_diff_iff at this, assumption}

lemma elem_diff_of_size_lt {X Y : set A}(h : size X < size Y):
  ∃ (e : A), e ∈ Y ∧ e ∉ X :=
begin
  suffices : 0 < size (Y \ X), rw [size_pos_iff_has_elem] at this, tauto, 
  rw diff_def, linarith [size_induced_partition_inter Y X, size_mono_inter_right Y X], 
end 

lemma add_compl_single_size {X : set A} {e : A} :
  e ∈ Xᶜ → size (X ∪ e) = size X + 1 := 
begin
  intro hXe, have := size_modular X e, 
  rw [inter_comm X, nonelem_disjoint (elem_compl_iff.mp hXe), size_single, size_empty] at this, 
  linarith, 
end

lemma add_size_ub {X : set A}{e : A}:
  size (X ∪ e) ≤ size X + 1 := 
by linarith [size_nonneg (X ∩ e), size_modular X e, size_single e]

lemma add_nonelem_size {X : set A} {e : A}: 
  e ∉ X →  size (X ∪ e) = size X + 1 := 
λ hXe, by {apply add_compl_single_size, exact elem_compl_iff.mpr hXe}

lemma compl_single_remove {X : set A} {e : A} : 
  e ∈ X → (X \ e)ᶜ = Xᶜ ∪ e := 
λ _, by rw [diff_def, compl_inter, compl_compl]

lemma remove_add_elem {X : set A} {e : A}: 
  e ∈ X → (X\e) ∪ e = X := 
λ heX, by {rw [elem_iff_subset, subset_def_union,union_comm] at heX, 
          rw [diff_def, union_distrib_right, union_compl_left, inter_univ, heX]}
   
lemma add_remove_nonelem {X : set A} {e : A}: 
  e ∉ X → (X ∪ e) \ e = X := 
begin
  intro h, 
  rw [←elem_compl_iff, elem_iff_subset, subset_def_union] at h, 
  rw [diff_def, inter_distrib_right], 
  simp only [inter_compl, union_empty], 
  rw [←compl_compl_inter_left, inter_comm, compl_inj_iff] at h, 
  from h, 
end

lemma remove_single_size {X : set A}{e : A} :
  e ∈ X → size (X \ e) = size X - 1 := 
begin
  intro heX, 
  have h: e ∈ (X\e)ᶜ := by {rw [elem_iff_subset, compl_single_remove heX], apply subset_union_right}, 
  nth_rewrite 1 ←remove_add_elem  heX, linarith [add_compl_single_size h], 
end




lemma remove_single_subset (X : set A) (e : A) : 
  X \ e ⊆ X := 
diff_subset X e 

lemma nonelem_of_subset_remove_single (X : set A) (e : A):
  X ⊆ X \ e → e ∉ X :=
by tidy 

lemma remove_single_ssubset {X : set A} {e : A} :
  e ∈ X → X \ e ⊂ X := 
λ heX, ssubset_of_subset_ne (diff_subset _ _) (λ h, by {have := remove_single_size heX, rw h at this, linarith})

lemma nonempty_single_removal {X : set A}:
  X ≠ ∅ → ∃ Y : set A, Y ⊂ X ∧ size Y = size X - 1 := 
λ hX, by {cases ne_empty_has_elem hX with e he, exact ⟨X\e, ⟨remove_single_ssubset he,remove_single_size he⟩ ⟩}

lemma ssubset_univ_of_ne_univ {X : set A}:
  X ≠ univ → X ⊂ univ := 
  by tidy 

lemma ne_univ_single_addition {X : set A}:
  X ≠ univ → ∃ Y, X ⊂ Y ∧ size Y = size X + 1 := 
begin
  intro hX, rcases nonempty_single_removal (λ h, _ : Xᶜ ≠ ∅) with ⟨Y, ⟨h₁,h₂⟩ ⟩, 
  refine ⟨Yᶜ , ⟨ssubset_compl_right h₁, _⟩⟩,
  linarith [size_compl X, size_compl Y], 
  exact hX (univ_of_compl_empty h), 
end

lemma ne_univ_single_addition_element {X : set A}:
  X ≠ univ → ∃ (e:A), X ⊂ X ∪ e ∧ size (X ∪ e) = size X + 1 := 
begin
  intro hX, 
  rcases elem_only_larger_ssubset (ssubset_univ_of_ne_univ hX) with ⟨e,⟨_,he⟩⟩, 
  refine ⟨e, ⟨ssub_of_add_nonelem he, add_nonelem_size he⟩⟩, 
end

lemma add_from_nonempty_diff {X Y : set A} :
  X ⊂ Y ↔ ∃ e : A, e ∉ X ∧ X ∪ e ⊆ Y := 
begin
  refine ⟨λ h,_, λ h, ssubset_of_subset_ne _ (λ hne, _)⟩, 
  cases nonempty_def.mp (ssubset_diff_nonempty h) with e he, use e, 
  tidy, 
end

 
lemma aug_of_ssubset {X Y : set A} : 
  X ⊂ Y → ∃ Z (e : A), X ⊆ Z ∧ Z ⊂ Y ∧ Z ∪ e = Y :=
begin
  intro hXY, 
  rcases elem_only_larger_ssubset hXY with ⟨e, ⟨heY, heX⟩⟩, 
  refine ⟨Y \ e, e, ⟨subset_of_removal hXY.1 heX ,⟨ _, _⟩ ⟩⟩,
  from remove_single_ssubset heY, 
  from remove_add_elem heY, 
end 

lemma exchange_comm {X : set A}{e f : A} : 
  e ∈ X → f ∉ X → (X \ e) ∪ f = (X ∪ f) \ e := 
begin
  intros he hf, 
  simp only [diff_def], rw [inter_distrib_right],
  have : (f ∩ eᶜ : set A) = f := 
    by {rw [←subset_def_inter, ←disjoint_iff_subset_compl, inter_distinct_singles], by_contra h, push_neg at h, rw h at hf, from hf he},
  rw this, 
end

lemma exchange_size {X : set A}{e f : A} : 
  e ∈ X → f ∉ X → size ((X \ e) ∪ f) = size X := 
λ he hf, by linarith [add_nonelem_size (nonelem_diff_of_nonelem (e: set A) hf),remove_single_size he]

lemma exchange_pair_sizes {X Y : set A}{e f : A}: 
  size X = size Y → e ∈ X\Y → f ∈ Y \ X → size ((X\e) ∪ f) = size ((Y \ f) ∪ e) :=
λ h he hf, by {rw elem_diff_iff at he hf, rw [exchange_size hf.1 he.2, exchange_size he.1 hf.2], exact h}

lemma size_union_distinct_singles {e f : A}: 
  e ≠ f → size (e ∪ f : set A) = 2 :=
begin
  intros hef, 
  have : e ∉ (f : set A) := by {rw nonelem_iff_subset, from λ h, hef (nested_singles_eq h)}, 
  have := add_nonelem_size this, 
  rw [union_comm, size_single] at this, 
  linarith, 
end 

lemma size_union_singles_lb (e f : A): 
  1 ≤ size (e ∪ f : set A) := 
by {linarith [size_monotone (subset_union_left (e: set A) f), size_single e]}

lemma size_union_singles_ub (e f : A):
  size (e ∪ f : set A) ≤ 2 := 
by {by_cases e = f, rw [h, union_self, size_single], linarith, linarith [size_union_distinct_singles h]}

lemma subset_single {e : A}{X : set A} :
  X ⊆ e → X = ∅ ∨ X = e := 
begin
  intro h, cases lt_or_ge 0 (size X), 
  apply or.inr, exact eq_of_eq_size_subset h (by linarith [size_single e, size_monotone h]), 
  apply or.inl, exact (size_zero_empty (by linarith [size_nonneg X])),
end

lemma ssubset_pair {e f : A}{X : set A}:
  X ⊂ (e ∪ f : set A) → X = ∅ ∨ (X = e) ∨ (X = f) :=
begin
  intro h, rw ssubset_iff_subset_ne at h, 
  cases h with hs hne, rw [subset_def_inter, inter_distrib_left] at hs,
  cases subset_single (inter_subset_right X e),
  rw [h, empty_union, ←subset_def_inter] at hs, cases subset_single hs, exact or.inl h_1, apply or.inr, exact or.inr h_1,
  rw [inter_comm, ←subset_def_inter] at h, apply or.inr, cases subset_single (inter_subset_right X f),
  rw [h_1, union_empty, ←subset_def_inter] at hs,  exact or.inl (subset_antisymm hs h), 
  rw [subset_def_inter, inter_comm] at h,
  rw [h_1, h] at hs, exfalso, exact hne hs.symm, 
end

lemma equal_or_single_in_diff {X Y : set A} :
  size X = size Y → X = Y ∨  ∃ e, e ∈ X \ Y :=
begin
  intros hs, by_contra h, rw not_or_distrib at h, cases h with h1 h2, 
  rw ←ne_empty_iff_has_elem at h2, push_neg at h2,  
  rw diff_empty_iff_subset at h2, 
  from h1 (eq_of_eq_size_subset h2 hs),
end



lemma size_one_iff_eq_singleton {X : set A}:
  size X = 1 ↔ ∃ e, X = {e} := 
begin
  refine ⟨λ hX, _, λ h, _⟩,
  simp_rw eq_singleton_iff_nonempty_unique_mem,
  have := size_pos_iff_nonempty.mpr (by linarith : 0 < size X), 
  have := this, 
  cases this with e he,
  refine ⟨e, ⟨this, λ x hx, _⟩⟩,
  by_contra, 
  have hu := size_union_distinct_singles h, 
  have hss := union_subset_of_elem_of_elem hx he, 
  have hs := size_monotone hss,
  rw [hu, hX] at hs, 
  norm_num at hs, 
  cases h with e he, rw he, apply size_single, 

  -- this can certainly be improved 
end

end ftype 
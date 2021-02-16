
import tactic 
import .int_lemmas .set .single 

open_locale classical 
noncomputable theory 

open set 

variables {A : Type}[fintype A]

/------------------------------------------------------------

We define size manually by hooking into finset.card. The following
small set of lemmas characterizes the size function 

- Size -----------------------------------------------------/

def size_nat (U : Type)[fintype U](X : set U) := X.to_finset.card 

/-- the size of a set, as an integer -/
def size {U : Type}[fintype U](X : set U) : ℤ := (size_nat U X)

@[simp] lemma size_empty (A : Type)[fintype A] :
   size (∅ : set A) = 0 := 
by simp [size, size_nat]

@[simp] lemma size_singleton (e : A): 
  size ({e}: set A) = 1 := 
begin
  simp only  [size, size_nat, to_finset_card], 
  norm_cast, 
  rw fintype.card_eq_one_iff, 
  use e; simp, 
end

lemma size_modular (X Y : set A): 
  size (X ∪ Y) + size (X ∩ Y) = size X + size Y :=
begin
  simp only [size, size_nat], norm_cast, 
  convert finset.card_union_add_card_inter _ _, 
  { ext, simp only [mem_to_finset, finset.mem_union, mem_union]}, 
  { ext, simp only [mem_to_finset, finset.mem_inter, mem_inter_iff]}, 
  exact classical.dec_eq A, 
end

lemma size_nonneg (X : set A) : 0 ≤ size X := 
  by {simp only [size, size_nat], norm_cast, apply zero_le}  

-------------------------------------------------------------
open set 


-- Size 

lemma compl_size (X : set A) : size Xᶜ = size (univ : set A) - size X :=
  calc size Xᶜ = size (X ∪ Xᶜ) + size (X ∩ Xᶜ) - size X : by linarith [size_modular X Xᶜ]
  ...          = size (univ : set A)  + size (∅ : set A)  - size X : by rw [union_compl_self X, inter_compl_self X]
  ...          = size (univ : set A) - size X                  : by linarith [size_empty A]

lemma size_compl (X : set A) : size X = size (univ : set A) - size(Xᶜ) := 
  by linarith [compl_size X]

lemma contains_single (X : set A) : X.nonempty → (∃ Y, Y ⊆ X ∧ size Y = 1) :=
begin
  rintros ⟨e,he⟩,  
  from ⟨{e},⟨set.singleton_subset_iff.mpr he, size_singleton e⟩⟩, 
end
  




lemma ssubset_size {X Y : set A} : (X ⊆ Y) → (size X < size Y) → (X ⊂ Y) := 
  λ h h', by {rw ssubset_iff_subset_ne, from ⟨h, λ h'', by {rw h'' at h', linarith}⟩}


lemma size_monotone {X Y: set A} (hXY : X ⊆ Y) : size X ≤ size Y := 
  by {have := size_modular X (Y \ X), rw union_diff_of_subset  hXY at this      , 
        rw inter_diff at this, linarith [size_nonneg(Y \ X), size_empty A]}

lemma size_subadditive {X Y : set A} : size (X ∪ Y) ≤ size X + size Y :=
  by linarith [size_modular X Y, size_nonneg (X ∩ Y)] 

lemma compl_inter_size (X Y : set A) : size (X ∩ Y) + size (Xᶜ ∩ Y) = size Y := 
  by rw [←size_modular, ←inter_distrib_right, union_compl_self, univ_inter, ←inter_distrib_inter_left, inter_compl_self, empty_inter, size_empty]; ring

lemma compl_inter_size_subset {X Y : set A} : X ⊆ Y → size (Xᶜ ∩ Y) = size Y - size X := 
  λ hXY, by {have := compl_inter_size X Y, rw subset_def_inter_mp hXY at this, linarith} 

lemma diff_size {X Y : set A} : X ⊆ Y → size (Y \ X) = size Y - size X :=  
  λ hXY, by rw [diff_eq, inter_comm, compl_inter_size_subset hXY]

lemma size_diff_le_size (X Y : set A) : size (X \ Y) ≤ size X := 
  size_monotone (diff_subset _ _) 

lemma size_disjoint_sum {X Y : set A}: X ∩ Y = ∅ → size (X ∪ Y) = size X + size Y := 
  λ hXY, by {have := size_modular X Y, rw [hXY, size_empty] at this, linarith}

lemma size_modular_diff (X Y : set A) : size (X ∪ Y) = size (X \ Y) + size (Y \ X) + size (X ∩ Y) :=
  by {rw [←size_disjoint_sum (diffs_disj X Y)], have := (symm_diff_alt X Y), 
        unfold symm_diff at this,rw this, linarith [diff_size (inter_subset_union X Y)]  }


lemma size_induced_partition (X Y : set A) : size X = size (X ∩ Y) + size (X \ Y) := 
  by {nth_rewrite 0 ←diff_union X Y, refine size_disjoint_sum _, apply partition_inter}

lemma size_induced_partition_inter (X Y : set A) : size X = size (X ∩ Y) + size (X ∩ Yᶜ) := 
  by {rw ←diff_eq, apply size_induced_partition,}

lemma size_compl_sum (X : set A) : size X + size Xᶜ = size (univ : set A) := 
  by {have := size_disjoint_sum (inter_compl_self X), rw (union_compl_self X) at this, linarith}

lemma size_mono_inter_left (X Y : set A) : size (X ∩ Y) ≤ size X := 
size_monotone (inter_subset_left _ _)

lemma size_mono_inter_right (X Y : set A) : size (X ∩ Y) ≤ size Y := 
size_monotone (inter_subset_right _ _)

lemma size_mono_union_left (X Y : set A) : size X ≤ size (X ∪ Y)  := 
size_monotone (subset_union_left _ _)

lemma size_mono_union_right (X Y : set A) : size Y ≤ size (X ∪ Y) := 
size_monotone (subset_union_right _ _)


lemma size_zero_empty {X : set A} : (size X = 0) → X = ∅ := 
begin
  contrapose!, intros hne hs, 
  rw [push_neg.not_eq, set.ne_empty_iff_nonempty] at hne, 
  cases contains_single X hne with Y hY,
  linarith [size_monotone hY.1], 
end  

lemma size_zero_iff_empty {X : set A} : (size X = 0) ↔ (X = ∅) := 
  by {split, apply size_zero_empty, intros h, rw h, exact size_empty A}

lemma size_nonempty {X : set A} : X.nonempty → 0 < size X  := 
begin
  rw ←set.ne_empty_iff_nonempty, 
  from λ hX, lt_of_le_of_ne (size_nonneg X) (λ h, hX (size_zero_empty h.symm)), 
end

lemma size_pos_iff_nonempty {X : set A} : X.nonempty ↔ 0 < size X := 
begin
  refine ⟨λ h, size_nonempty h, λ h, _⟩,
  rw ←set.ne_empty_iff_nonempty, 
  from λ h', by {rw [h', size_empty] at h, from lt_irrefl 0 h} 
end

lemma one_le_size_iff_nonempty {X : set A} : X.nonempty ↔ 1 ≤ size X := 
  size_pos_iff_nonempty


lemma nontriv_size (hA: nontriv A): 1 ≤ size (univ : set A) := 
  one_le_size_iff_nonempty.mp hA 

lemma size_strict_monotone {X Y : set A} : X ⊂ Y → size X < size Y := 
λ hXY, by {rw [size_induced_partition Y X, inter_comm, subset_def_inter_mp hXY.1], 
              linarith [size_nonempty (ssubset_diff_nonempty hXY)]} 

lemma eq_of_eq_size_subset {X Y : set A} : (X ⊆ Y) → (size X = size Y) → X = Y :=
  λ hXY, by {cases subset_ssubset_or_eq hXY, intros sXY, exfalso, replace h := size_strict_monotone h, linarith, exact λ h', h}

lemma eq_of_eq_size_subset_iff {X Y : set A} : (X ⊆ Y) → ((size X = size Y) ↔ X = Y) :=
  λ hXY, ⟨λ h, eq_of_eq_size_subset hXY h, λ h, by {rw h}⟩

lemma eq_of_le_size_subset {X Y : set A} : (X ⊆ Y) → (size Y ≤ size X) → X = Y :=
  λ hXY hXY', by {apply eq_of_eq_size_subset hXY, exact le_antisymm (size_monotone hXY) hXY'}

lemma size_eq_of_supset {X Y : set A} : (X ⊆ Y) → (size Y ≤ size X) → size X = size Y := 
  λ hss hs, by linarith[size_monotone hss]

lemma single_subset (X : set A) : X.nonempty → (∃ Y Z, Y ∩ Z = ∅ ∧ Y ∪ Z = X ∧ size Y = 1) := 
  begin
    intro h, cases contains_single X h with Y hY, use Y, use X \ Y, 
    exact ⟨inter_diff _ _,⟨union_diff_of_subset  hY.1,hY.2⟩⟩,
  end


lemma single_subset_nonempty {X : set A}: X.nonempty → (∃ Y Z, Y ∩ Z = ∅ ∧ Y ∪ Z = X ∧ size Y = 1) := 
  λ hX, single_subset X hX 

lemma union_ssubsets (X : set A) : 1 < size X  → ∃ Y Z : set A, Y ⊂ X ∧ Z ⊂ X ∧ Y ∩ Z = ∅ ∧ Y ∪ Z = X := 
begin
  intros hX, 
  have h : X.nonempty := by {rw size_pos_iff_nonempty, linarith}, 
  rcases single_subset X h with ⟨Y,⟨Z,⟨hI,hU,h1⟩⟩⟩, use Y, use Z, 
  simp_rw ←hU at ⊢ hX, 
  refine ⟨ssubset_of_subset_ne _ (λ h, _), ssubset_of_subset_ne _ (λ h, _), hI, rfl⟩, 
  apply subset_union_left, 
  rw ←h at hX, linarith, 
  apply subset_union_right,
  have := size_modular Y Z, 
  rw [hU, hI, size_empty, h1, ←hU, ←h] at this,
  linarith, 
end


lemma size_pos_has_mem {X : set A}: 
  0 < size X → ∃ e, e ∈ X := 
λ h, (ne_empty_iff_has_mem.mp (λ h', by {rw [h',size_empty] at h, exact lt_irrefl 0 h}))

lemma size_pos_iff_has_mem {X : set A}: 
  0 < size X ↔ ∃ e, e ∈ X := 
⟨λ h, size_pos_has_mem h, λ h, by {cases h with e he, have := size_monotone (singleton_subset_iff.mpr he), rw size_singleton at this, linarith}⟩ 

lemma size_zero_iff_has_no_mem {X : set A}:
  size X = 0 ↔ ¬ ∃ e, e ∈ X := 
begin
  rw [iff.comm, ←not_iff, ←size_pos_iff_has_mem, not_iff], 
  refine ⟨λ h, _, λ h, by linarith ⟩ ,
  linarith [size_nonneg X, not_lt.mp h]
end


lemma elem_diff_of_size_lt {X Y : set A}(h : size X < size Y):
  ∃ (e : A), e ∈ Y ∧ e ∉ X :=
begin
  suffices : 0 < size (Y \ X), rw [size_pos_iff_has_mem] at this, tauto, 
  rw diff_eq, linarith [size_induced_partition_inter Y X, size_mono_inter_right Y X], 
end 

lemma add_compl_single_size {X : set A} {e : A} :
  e ∈ Xᶜ → size (X ∪ {e}) = size X + 1 := 
begin
  intro hXe, have := size_modular X {e}, 
  rw [inter_comm X, nonmem_disjoint (by rwa ←mem_compl_iff), size_singleton, size_empty] at this, 
  linarith, 
end

lemma add_size_ub {X : set A}{e : A}:
  size (X ∪ {e}) ≤ size X + 1 := 
by linarith [size_nonneg (X ∩ {e}), size_modular X {e}, size_singleton e]

lemma add_nonmem_size {X : set A} {e : A}: 
  e ∉ X →  size (X ∪ {e}) = size X + 1 := 
λ hXe, by {apply add_compl_single_size, rwa ←mem_compl_iff at hXe}


lemma remove_single_size {X : set A}{e : A} :
  e ∈ X → size (X \ {e}) = size X - 1 := 
begin
  intro heX, 
  have h: e ∈ (X \ {e})ᶜ := by 
  { rw [←singleton_subset_iff, compl_single_remove heX], 
    apply subset_union_right}, 
  nth_rewrite 1 ←remove_add_elem  heX, 
  linarith [add_compl_single_size h], 
end


lemma nonempty_single_removal {X : set A}:
  X ≠ ∅ → ∃ Y : set A, Y ⊂ X ∧ size Y = size X - 1 := 
λ hX, by {cases ne_empty_has_mem hX with e he, 
exact ⟨X \ {e}, ⟨ssubset_of_remove_mem he,remove_single_size he⟩ ⟩}

lemma ne_univ_single_addition {X : set A}:
  X ≠ univ → ∃ Y, X ⊂ Y ∧ size Y = size X + 1 := 
begin
  intro hX, rcases nonempty_single_removal (λ h, _ : Xᶜ ≠ ∅) with ⟨Y, ⟨h₁,h₂⟩ ⟩, 
  refine ⟨Yᶜ , ⟨scompl_subset_comm.mpr h₁, _⟩⟩,
  linarith [size_compl X, size_compl Y], 
  exact hX (compl_empty_iff.mp h), 
end

lemma ne_univ_single_addition_element {X : set A}:
  X ≠ univ → ∃ (e:A), X ⊂ X ∪ {e} ∧ size (X ∪ {e}) = size X + 1 := 
begin
  intro hX, 
  rcases elem_only_larger_ssubset (ssubset_univ_of_ne_univ hX) with ⟨e,⟨_,he⟩⟩, 
  refine ⟨e, ⟨ssub_of_add_nonmem he, add_nonmem_size he⟩⟩, 
end

lemma size_remove_insert {X : set A}{e f : A}(he : e ∈ X)(hf : f ∉ X) : 
  size ((X \ {e}) ∪ {f}) = size X := 
by linarith [add_nonmem_size (nonmem_diff_of_nonmem {e} hf),remove_single_size he]

lemma size_insert_remove {X : set A}{e f : A}(he : e ∈ X)(hf : f ∉ X) : 
  size ((X ∪ {f}) \ {e}) = size X := 
by linarith [add_nonmem_size hf, remove_single_size (mem_union_of_mem_left {f} he)]

lemma exchange_pair_sizes {X Y : set A}{e f : A}: 
  size X = size Y → e ∈ X\Y → f ∈ Y \ X → size ((X\{e}) ∪ {f}) = size ((Y \ {f}) ∪ {e}) :=
λ h he hf, by {rw elem_diff_iff at he hf, rw [size_remove_insert hf.1 he.2, size_remove_insert he.1 hf.2], exact h}

lemma size_union_distinct_singles {e f : A}: 
  e ≠ f → size ({e,f} : set A) = 2 :=
begin
  intros hef, 
  have : e ∉ ({f} : set A) := by {rw ←singleton_subset_iff, from λ h, hef (nested_singletons_eq h)}, 
  have := add_nonmem_size this, 
  rw [union_comm, size_singleton, union_singletons_eq_pair] at this, 
  linarith, 
end 

lemma size_union_singles_lb (e f : A): 
  1 ≤ size ({e,f} : set A) := 
by {rw ←union_singletons_eq_pair, 
    linarith [size_monotone (@subset_union_left A {e} {f}),size_singleton e],}

lemma size_union_singles_ub (e f : A):
  size ({e,f} : set A) ≤ 2 := 
begin
  by_cases e = f, 
  rw [h, pair_eq_singleton, size_singleton], linarith, 
  linarith [size_union_distinct_singles h],
end 

lemma equal_or_single_in_diff {X Y : set A} :
  size X = size Y → X = Y ∨  ∃ e, e ∈ X \ Y :=
begin
  intros hs, by_contra h, rw not_or_distrib at h, cases h with h1 h2, 
  rw ←ne_empty_iff_has_mem at h2, push_neg at h2,  
  rw diff_empty_iff_subset at h2, 
  from h1 (eq_of_eq_size_subset h2 hs),
end

lemma size_one_iff_eq_singleton {X : set A}:
  size X = 1 ↔ ∃ e, X = {e} := 
begin
  refine ⟨λ hX, _, λ h, _⟩, swap,  
    cases h with e he, rw he, apply size_singleton, 
  simp_rw eq_singleton_iff_nonempty_unique_mem,
  have := size_pos_iff_nonempty.mpr (by linarith : 0 < size X), 
  have := this, 
  cases this with e he,
  refine ⟨e, ⟨this, λ x hx, _⟩⟩,
  by_contra, 
  have hu := size_union_distinct_singles h, 
  have hss := union_subset_of_mem_of_mem hx he, 
  have hs := size_monotone hss,
  rw [union_singletons_eq_pair, hu, hX] at hs, 
  norm_num at hs, 
end

lemma size_le_one_iff_empty_or_singleton {X : set A}:
  size X ≤ 1 ↔ X = ∅ ∨ ∃ e, X = {e} :=
begin
  refine ⟨λ h, _, λ h, _⟩, swap, 
  { rcases h with (rfl | ⟨e, rfl⟩); simp only [size_singleton, size_empty], norm_num,},
  by_cases h' : size X ≤ 0, 
  { left, rw ←size_zero_iff_empty, linarith [size_nonneg X],},
  right, rw ←size_one_iff_eq_singleton, 
  exact le_antisymm h (by linarith), 
end

lemma size_eq_two_iff_pair {X : set A}:
  size X = 2 ↔ ∃ (e f : A), e ≠ f ∧ X = {e,f} :=
begin
  refine ⟨λ h, _, λ h, _⟩, swap, 
  { rcases h with ⟨e,f,hef,rfl⟩, apply size_union_distinct_singles hef},
  cases size_pos_has_mem (by {rw h, norm_num} : 0 < size X) with e he,
  cases size_pos_has_mem (by {rw [remove_single_size he,h], norm_num } : 0 < size (X \ {e})) with f hf, 
  refine ⟨e,f,ne.symm (ne_of_mem_diff hf), _⟩,  
  rw eq_comm, apply eq_of_eq_size_subset, 
  { rw ←union_singletons_eq_pair, 
    apply union_of_subsets (singleton_subset_iff.mpr he),  
    simp only [set.mem_diff, set.mem_singleton_iff] at hf, 
    exact singleton_subset_iff.mpr hf.1, },
  rwa [eq_comm, size_union_distinct_singles  (ne.symm (ne_of_mem_diff hf))],  
end 
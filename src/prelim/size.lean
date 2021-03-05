
import tactic 
import .int_lemmas .set .single finsum.fin_api

open_locale classical big_operators 
noncomputable theory 

open set 

variables {A : Type}
/- ----------------------------------------------------------

We define size by hooking into fincard. The following
small set of lemmas characterizes the size function 

- Size -----------------------------------------------------/


/-- the size of a set, as an integer -/
def size {U : Type*}(X : set U) : ℤ := (fincard X)

lemma size_def {U : Type*}(X : set U): 
  size X = fincard X := 
rfl 

def type_size (U : Type) : ℤ := size (univ : set U)

lemma type_size_eq (U : Type):
  type_size U = size (univ : set U) := rfl 

@[simp] lemma size_empty (A : Type) :
   size (∅ : set A) = 0 := 
by simp [size]

@[simp] lemma size_singleton (e : A): 
  size ({e}: set A) = 1 := 
by simp [size]

lemma size_modular [nonempty (fintype A)](X Y : set A): 
  size (X ∪ Y) + size (X ∩ Y) = size X + size Y :=
by {letI := classical.choice _inst_1, simp_rw size, norm_cast, apply fincard_modular; apply finite.of_fintype} 

lemma size_union [nonempty (fintype A)](X Y : set A): 
  size (X ∪ Y) = size X + size Y - size (X ∩ Y) := 
by linarith [size_modular X Y]

lemma size_nonneg (X : set A) : 
  0 ≤ size X := 
by {simp only [size], norm_cast, apply zero_le}  

lemma finsum_ones_eq_size (X : set A) : 
  ∑ᶠ x in X, (1 : ℤ) = size X := 
by {rw [size, fincard, nat.coe_int_distrib_finsum_in], refl}

lemma sum_size_fiber_eq_size [nonempty (fintype A)]{ι : Type}(s : set A)(f : A → ι):
  ∑ᶠ (i : ι), size {a ∈ s | f a = i} = size s := 
by simp_rw [size_def, ← nat.coe_int_distrib_finsum, fin.sum_fincard_fiber_eq_fincard s f]




-------------------------------------------------------------
open set 


-- Size 

lemma compl_size [nonempty (fintype A)](X : set A) : size Xᶜ = size (univ : set A) - size X :=
  calc size Xᶜ = size (X ∪ Xᶜ) + size (X ∩ Xᶜ) - size X : by linarith [size_modular X Xᶜ]
  ...          = size (univ : set A)  + size (∅ : set A)  - size X : by rw [union_compl_self X, inter_compl_self X]
  ...          = size (univ : set A) - size X                  : by linarith [size_empty A]

lemma size_compl [nonempty (fintype A)](X : set A) : size X = size (univ : set A) - size(Xᶜ) := 
  by linarith [compl_size X]

lemma contains_singleton (X : set A) : X.nonempty → (∃ Y, Y ⊆ X ∧ size Y = 1) :=
begin
  rintros ⟨e,he⟩,  
  from ⟨{e},⟨set.singleton_subset_iff.mpr he, size_singleton e⟩⟩, 
end


lemma ssubset_size {X Y : set A} : (X ⊆ Y) → (size X < size Y) → (X ⊂ Y) := 
  λ h h', by {rw ssubset_iff_subset_ne, from ⟨h, λ h'', by {rw h'' at h', linarith}⟩}


lemma size_monotone [nonempty (fintype A)]{X Y: set A} (hXY : X ⊆ Y) : size X ≤ size Y := 
  by {have := size_modular X (Y \ X), rw union_diff_of_subset  hXY at this      , 
        rw inter_diff at this, linarith [size_nonneg(Y \ X), size_empty A]}

lemma size_subadditive [nonempty (fintype A)]{X Y : set A} : size (X ∪ Y) ≤ size X + size Y :=
  by linarith [size_modular X Y, size_nonneg (X ∩ Y)] 

lemma compl_inter_size [nonempty (fintype A)](X Y : set A) : size (X ∩ Y) + size (Xᶜ ∩ Y) = size Y := 
  by rw [←size_modular, ←inter_distrib_right, union_compl_self, univ_inter, ←inter_distrib_inter_left, 
  inter_compl_self, empty_inter, size_empty]; ring

lemma compl_inter_size_subset [nonempty (fintype A)]{X Y : set A} : 
  X ⊆ Y → size (Xᶜ ∩ Y) = size Y - size X := 
  λ hXY, by {have := compl_inter_size X Y, rw subset_iff_inter_eq_left.mp hXY at this, linarith} 

lemma diff_size [nonempty (fintype A)]{X Y : set A} : X ⊆ Y → size (Y \ X) = size Y - size X :=  
  λ hXY, by rw [diff_eq, inter_comm, compl_inter_size_subset hXY]

lemma size_diff_le_size [nonempty (fintype A)](X Y : set A) : size (X \ Y) ≤ size X := 
  size_monotone (diff_subset _ _) 

lemma size_disjoint_sum [nonempty (fintype A)]{X Y : set A}: X ∩ Y = ∅ → size (X ∪ Y) = size X + size Y := 
  λ hXY, by {have := size_modular X Y, rw [hXY, size_empty] at this, linarith}

lemma size_modular_diff [nonempty (fintype A)](X Y : set A) : size (X ∪ Y) = size (X \ Y) + size (Y \ X) + size (X ∩ Y) :=
  by {rw [←size_disjoint_sum (diffs_disj X Y)], have := (symm_diff_alt X Y), 
        unfold symm_diff at this,rw this, linarith [diff_size (inter_subset_union X Y)]  }


lemma size_induced_partition [nonempty (fintype A)](X Y : set A) : size X = size (X ∩ Y) + size (X \ Y) := 
  by {nth_rewrite 0 ←diff_union X Y, refine size_disjoint_sum _, apply partition_inter}

lemma size_induced_partition_inter [nonempty (fintype A)](X Y : set A) : size X = size (X ∩ Y) + size (X ∩ Yᶜ) := 
  by {rw ←diff_eq, apply size_induced_partition,}

lemma size_compl_sum [nonempty (fintype A)](X : set A) : size X + size Xᶜ = size (univ : set A) := 
  by {have := size_disjoint_sum (inter_compl_self X), rw (union_compl_self X) at this, linarith}

lemma size_mono_inter_left [nonempty (fintype A)](X Y : set A) : size (X ∩ Y) ≤ size X := 
size_monotone (inter_subset_left _ _)

lemma size_mono_inter_right [nonempty (fintype A)](X Y : set A) : size (X ∩ Y) ≤ size Y := 
size_monotone (inter_subset_right _ _)

lemma size_mono_union_left [nonempty (fintype A)](X Y : set A) : size X ≤ size (X ∪ Y)  := 
size_monotone (subset_union_left _ _)

lemma size_mono_union_right [nonempty (fintype A)](X Y : set A) : size Y ≤ size (X ∪ Y) := 
size_monotone (subset_union_right _ _)


lemma size_zero_empty [nonempty (fintype A)]{X : set A} : (size X = 0) → X = ∅ := 
begin
  contrapose!, intros hne hs, 
  rw [push_neg.not_eq, set.ne_empty_iff_nonempty] at hne, 
  cases contains_singleton X hne with Y hY,
  linarith [size_monotone hY.1], 
end  

lemma size_zero_iff_empty [nonempty (fintype A)]{X : set A} : (size X = 0) ↔ (X = ∅) := 
  by {split, apply size_zero_empty, intros h, rw h, exact size_empty A}

lemma size_nonempty [nonempty (fintype A)]{X : set A} : X.nonempty → 0 < size X  := 
begin
  rw ←set.ne_empty_iff_nonempty, 
  from λ hX, lt_of_le_of_ne (size_nonneg X) (λ h, hX (size_zero_empty h.symm)), 
end

lemma size_pos_iff_nonempty [nonempty (fintype A)]{X : set A} : X.nonempty ↔ 0 < size X := 
begin
  refine ⟨λ h, size_nonempty h, λ h, _⟩,
  rw ←set.ne_empty_iff_nonempty, 
  from λ h', by {rw [h', size_empty] at h, from lt_irrefl 0 h} 
end

lemma one_le_size_iff_nonempty [nonempty (fintype A)]{X : set A} : X.nonempty ↔ 1 ≤ size X := 
  size_pos_iff_nonempty


lemma nontriv_size [nonempty (fintype A)](hA: nontriv A): 1 ≤ size (univ : set A) := 
  one_le_size_iff_nonempty.mp hA 

lemma size_strict_monotone [nonempty (fintype A)]{X Y : set A} : X ⊂ Y → size X < size Y := 
λ hXY, by {rw [size_induced_partition Y X, inter_comm, subset_iff_inter_eq_left.mp hXY.1], 
              linarith [size_nonempty (ssubset_diff_nonempty hXY)]} 

lemma eq_of_eq_size_subset [nonempty (fintype A)]{X Y : set A} : (X ⊆ Y) → (size X = size Y) → X = Y :=
  λ hXY, by {cases subset_ssubset_or_eq hXY, intros sXY, exfalso, 
  replace h := size_strict_monotone h, linarith, exact λ h', h}

lemma eq_of_eq_size_subset_iff [nonempty (fintype A)]{X Y : set A} : 
  (X ⊆ Y) → ((size X = size Y) ↔ X = Y) :=
  λ hXY, ⟨λ h, eq_of_eq_size_subset hXY h, λ h, by {rw h}⟩

lemma eq_of_le_size_subset [nonempty (fintype A)]{X Y : set A} : 
  (X ⊆ Y) → (size Y ≤ size X) → X = Y :=
  λ hXY hXY', by {apply eq_of_eq_size_subset hXY, exact le_antisymm (size_monotone hXY) hXY'}

lemma size_eq_of_supset [nonempty (fintype A)]{X Y : set A} : (X ⊆ Y) → (size Y ≤ size X) → size X = size Y := 
  λ hss hs, by linarith[size_monotone hss]

lemma single_subset (X : set A) : X.nonempty → (∃ Y Z, Y ∩ Z = ∅ ∧ Y ∪ Z = X ∧ size Y = 1) := 
  begin
    intro h, cases contains_singleton X h with Y hY, use Y, use X \ Y, 
    exact ⟨inter_diff _ _,⟨union_diff_of_subset  hY.1,hY.2⟩⟩,
  end


lemma single_subset_nonempty {X : set A}: X.nonempty → (∃ Y Z, Y ∩ Z = ∅ ∧ Y ∪ Z = X ∧ size Y = 1) := 
  λ hX, single_subset X hX 

lemma union_ssubsets [nonempty (fintype A)](X : set A) : 
  1 < size X  → ∃ Y Z : set A, Y ⊂ X ∧ Z ⊂ X ∧ Y ∩ Z = ∅ ∧ Y ∪ Z = X := 
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


lemma size_pos_has_mem [nonempty (fintype A)]{X : set A}: 
  0 < size X → ∃ e, e ∈ X := 
λ h, (ne_empty_iff_has_mem.mp (λ h', by {rw [h',size_empty] at h, exact lt_irrefl 0 h}))

lemma size_pos_iff_has_mem [nonempty (fintype A)]{X : set A}: 
  0 < size X ↔ ∃ e, e ∈ X := 
⟨λ h, size_pos_has_mem h, λ h, by {cases h with e he, have := size_monotone (singleton_subset_iff.mpr he), rw size_singleton at this, linarith}⟩ 


lemma one_le_size_iff_has_mem [nonempty (fintype A)][X : set A]: 
  1 ≤ size X ↔ ∃ e, e ∈ X := 
by {convert size_pos_iff_has_mem, apply_instance, }


lemma size_zero_iff_has_no_mem [nonempty (fintype A)]{X : set A}:
  size X = 0 ↔ ¬ ∃ e, e ∈ X := 
begin
  rw [iff.comm, ←not_iff, ←size_pos_iff_has_mem, not_iff], 
  refine ⟨λ h, _, λ h, by linarith ⟩ ,
  linarith [size_nonneg X, not_lt.mp h]
end

lemma size_le_zero_iff_has_no_mem [nonempty (fintype A)]{X : set A}:
  size X ≤ 0 ↔ ¬ ∃ e, e ∈ X := 
begin
  rw ←size_zero_iff_has_no_mem, split, 
  { intro, linarith [size_nonneg X]}, 
  intro h, rw h, 
end



lemma elem_diff_of_size_lt [nonempty (fintype A)]{X Y : set A}(h : size X < size Y):
  ∃ (e : A), e ∈ Y ∧ e ∉ X :=
begin
  suffices : 0 < size (Y \ X), rw [size_pos_iff_has_mem] at this, tauto, 
  rw diff_eq, linarith [size_induced_partition_inter Y X, size_mono_inter_right Y X], 
end 

lemma size_insert_mem_compl [nonempty (fintype A)]{X : set A} {e : A} :
  e ∈ Xᶜ → size (X ∪ {e}) = size X + 1 := 
begin
  intro hXe, have := size_modular X {e}, 
  rw [inter_comm X, nonmem_disjoint (by rwa ←mem_compl_iff), size_singleton, size_empty] at this, 
  linarith, 
end

lemma size_insert_ub [nonempty (fintype A)]{X : set A}{e : A}:
  size (X ∪ {e}) ≤ size X + 1 := 
by linarith [size_nonneg (X ∩ {e}), size_modular X {e}, size_singleton e]

lemma size_insert_nonmem [nonempty (fintype A)]{X : set A} {e : A}: 
  e ∉ X → size (X ∪ {e}) = size X + 1 := 
λ hXe, by {apply size_insert_mem_compl, rwa ←mem_compl_iff at hXe}


lemma size_remove_mem [nonempty (fintype A)]{X : set A}{e : A} :
  e ∈ X → size (X \ {e}) = size X - 1 := 
begin
  intro heX, 
  have h: e ∈ (X \ {e})ᶜ := by 
  { rw [←singleton_subset_iff, compl_single_remove heX], 
    apply subset_union_right}, 
  nth_rewrite 1 ←remove_add_elem  heX, 
  linarith [size_insert_mem_compl h], 
end


lemma nonempty_has_sub_one_size_ssubset [nonempty (fintype A)]{X : set A}:
  X ≠ ∅ → ∃ Y : set A, Y ⊂ X ∧ size Y = size X - 1 := 
λ hX, by {cases ne_empty_has_mem hX with e he, 
exact ⟨X \ {e}, ⟨ssubset_of_remove_mem he,size_remove_mem he⟩ ⟩}

lemma ne_univ_has_add_one_size_ssupset [nonempty (fintype A)]{X : set A}:
  X ≠ univ → ∃ Y, X ⊂ Y ∧ size Y = size X + 1 := 
begin
  intro hX, rcases nonempty_has_sub_one_size_ssubset (λ h, _ : Xᶜ ≠ ∅) with ⟨Y, ⟨h₁,h₂⟩ ⟩, 
  refine ⟨Yᶜ , ⟨scompl_subset_comm.mpr h₁, _⟩⟩,
  linarith [size_compl X, size_compl Y], 
  exact hX (compl_empty_iff.mp h), 
end

lemma ne_univ_has_add_one_size_ssupset_element [nonempty (fintype A)]{X : set A}:
  X ≠ univ → ∃ (e:A), X ⊂ X ∪ {e} ∧ size (X ∪ {e}) = size X + 1 := 
begin
  intro hX, 
  rcases elem_only_larger_ssubset (ssubset_univ_of_ne_univ hX) with ⟨e,⟨_,he⟩⟩, 
  refine ⟨e, ⟨ssub_of_add_nonmem he, size_insert_nonmem he⟩⟩, 
end

lemma size_remove_insert [nonempty (fintype A)]{X : set A}{e f : A}(he : e ∈ X)(hf : f ∉ X) : 
  size ((X \ {e}) ∪ {f}) = size X := 
by linarith [size_insert_nonmem (nonmem_diff_of_nonmem {e} hf),size_remove_mem he]

lemma size_insert_remove [nonempty (fintype A)]{X : set A}{e f : A}(he : e ∈ X)(hf : f ∉ X) : 
  size ((X ∪ {f}) \ {e}) = size X := 
by linarith [size_insert_nonmem hf, size_remove_mem (mem_union_of_mem_left {f} he)]

lemma exchange_pair_sizes [nonempty (fintype A)]{X Y : set A}{e f : A}: 
  size X = size Y → e ∈ X\Y → f ∈ Y \ X → size ((X\{e}) ∪ {f}) = size ((Y \ {f}) ∪ {e}) :=
λ h he hf, by {rw elem_diff_iff at he hf, rw [size_remove_insert hf.1 he.2, size_remove_insert he.1 hf.2], exact h}

lemma size_union_distinct_singles [nonempty (fintype A)]{e f : A}: 
  e ≠ f → size ({e,f} : set A) = 2 :=
begin
  intros hef, 
  have : e ∉ ({f} : set A) := by {rw ←singleton_subset_iff, from λ h, hef (nested_singletons_eq h)}, 
  have := size_insert_nonmem this, 
  rw [union_comm, size_singleton, union_singletons_eq_pair] at this, 
  linarith, 
end 

lemma two_le_size_iff_has_distinct [nonempty (fintype A)]{X : set A}:
  2 ≤ size X ↔ ∃ e f ∈ X, e ≠ f :=
begin
  split, 
  { intro h, 
    obtain ⟨e,he⟩ := @size_pos_has_mem _ _ X (by linarith),
    obtain ⟨f,hf⟩ := @size_pos_has_mem _ _ (X \ {e}) (by linarith [size_remove_mem he]), 
    refine ⟨e,f,he,mem_of_mem_of_subset hf (diff_subset _ _), _⟩, 
    rintro rfl, simpa using hf,},
  rintro ⟨e,f,he,hf,hef⟩, 
  rw ← size_union_distinct_singles hef, 
  apply size_monotone, 
  rw pair_subset_iff, tauto, 
end

lemma size_union_singles_lb [nonempty (fintype A)](e f : A): 
  1 ≤ size ({e,f} : set A) := 
by {rw ←union_singletons_eq_pair, 
    linarith [size_monotone (@subset_union_left A {e} {f}),size_singleton e],}

lemma size_union_singles_ub [nonempty (fintype A)](e f : A):
  size ({e,f} : set A) ≤ 2 := 
begin
  by_cases e = f, 
  rw [h, pair_eq_singleton, size_singleton], linarith, 
  linarith [size_union_distinct_singles h],
end 

lemma equal_or_single_in_diff [nonempty (fintype A)]{X Y : set A} :
  size X = size Y → X = Y ∨  ∃ e, e ∈ X \ Y :=
begin
  intros hs, by_contra h, rw not_or_distrib at h, cases h with h1 h2, 
  rw ←ne_empty_iff_has_mem at h2, push_neg at h2,  
  rw diff_empty_iff_subset at h2, 
  from h1 (eq_of_eq_size_subset h2 hs),
end

lemma size_one_iff_eq_singleton [nonempty (fintype A)]{X : set A}:
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

lemma size_le_one_iff_empty_or_singleton [nonempty (fintype A)]{X : set A}:
  size X ≤ 1 ↔ X = ∅ ∨ ∃ e, X = {e} :=
begin
  refine ⟨λ h, _, λ h, _⟩, swap, 
  { rcases h with (rfl | ⟨e, rfl⟩); simp only [size_singleton, size_empty], norm_num,},
  by_cases h' : size X ≤ 0, 
  { left, rw ←size_zero_iff_empty, linarith [size_nonneg X],},
  right, rw ←size_one_iff_eq_singleton, 
  exact le_antisymm h (by linarith), 
end

lemma size_le_one_iff_mem_unique [nonempty (fintype A)]{X : set A}: 
  size X ≤ 1 ↔ ∀ e f ∈ X, e = f := 
begin
  split, 
  { rw size_le_one_iff_empty_or_singleton, 
    rintros (rfl | ⟨e,rfl⟩); simp [mem_singleton_iff], rintros e f rfl rfl, refl,},
  refine λ h, by_contra (λ hn, _), 
  rw [not_le] at hn, replace hn := int.add_one_le_of_lt hn, norm_num at hn,
  rw two_le_size_iff_has_distinct at hn, 
  obtain ⟨e,f,he,hf,hef⟩ := hn, exact hef (h e f he hf),   
end

lemma size_eq_two_iff_pair [nonempty (fintype A)]{X : set A}:
  size X = 2 ↔ ∃ (e f : A), e ≠ f ∧ X = {e,f} :=
begin
  refine ⟨λ h, _, λ h, _⟩, swap, 
  { rcases h with ⟨e,f,hef,rfl⟩, apply size_union_distinct_singles hef},
  cases size_pos_has_mem (by {rw h, norm_num} : 0 < size X) with e he,
  cases size_pos_has_mem (by {rw [size_remove_mem he,h], norm_num } : 0 < size (X \ {e})) with f hf, 
  refine ⟨e,f,ne.symm (ne_of_mem_diff hf), _⟩,  
  rw eq_comm, apply eq_of_eq_size_subset, 
  { rw ←union_singletons_eq_pair, 
    apply union_of_subsets (singleton_subset_iff.mpr he),  
    simp only [set.mem_diff, set.mem_singleton_iff] at hf, 
    exact singleton_subset_iff.mpr hf.1, },
  rwa [eq_comm, size_union_distinct_singles  (ne.symm (ne_of_mem_diff hf))],  
end 


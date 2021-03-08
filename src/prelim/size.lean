
import tactic 
import .int_lemmas .set .single finsum.fin_api

open_locale classical big_operators 
noncomputable theory 

open set 

variables {α : Type}[fintype α]
/- ----------------------------------------------------------

γe define size simply as the cast of fincard to int. 

- Size -----------------------------------------------------/


/-- the size of a set, as an integer -/
def size {α : Type*}(X : set α) : ℤ := (fincard X)

lemma size_def {α : Type*}(X : set α): 
  size X = fincard X := 
rfl 

def type_size (α : Type) : ℤ := size (univ : set α)

lemma type_size_eq (α : Type):
  type_size α = size (univ : set α) := rfl 

@[simp] lemma size_empty (α : Type) :
   size (∅ : set α) = 0 := 
by simp [size]

@[simp] lemma size_singleton (e : α): 
  size ({e}: set α) = 1 := 
by simp [size]

lemma size_modular [fintype α](X Y : set α): 
  size (X ∪ Y) + size (X ∩ Y) = size X + size Y :=
by {simp_rw size, norm_cast, apply fincard_modular; apply finite.of_fintype} 

lemma size_union [fintype α](X Y : set α): 
  size (X ∪ Y) = size X + size Y - size (X ∩ Y) := 
by linarith [size_modular X Y]

lemma size_nonneg (X : set α) : 
  0 ≤ size X := 
by {simp only [size], norm_cast, apply zero_le}  

@[simp] lemma finsum_ones_eq_size {α : Type}(X : set α) : 
  ∑ᶠ x in X, (1 : ℤ) = size X := 
by {rw [size, fincard, nat.coe_int_distrib_finsum_in], refl}

@[simp] lemma finsum_ones_eq_type_size (B : Type*) : 
  ∑ᶠ (x : B), (1 : ℤ) = type_size B := 
by {rw [finsum_eq_finsum_in_univ, finsum_ones_eq_size], refl}

@[simp] lemma int.finsum_const_eq_mul_type_size (B : Type*)(b : ℤ):
  ∑ᶠ (x : B), b = b * type_size B := 
by rw [← mul_one b, ← finsum_ones_eq_type_size, ← mul_distrib_finsum, mul_one]

@[simp] lemma int.finsum_in_const_eq_mul_size (X : set α)(b : ℤ):
  ∑ᶠ x in X, b = b * size X := 
by rw [← mul_one b, ← finsum_ones_eq_size, ← mul_distrib_finsum_in, mul_one]

lemma sum_size_fiber_eq_size {ι : Type}(s : set α)(f : α → ι):
  ∑ᶠ (i : ι), size {a ∈ s | f a = i} = size s := 
by simp_rw [size_def, ← nat.coe_int_distrib_finsum, fin.sum_fincard_fiber_eq_fincard s f]

lemma size_set_subtype_eq_size_set (P Q : α → Prop):
  size {x : {y // P y} | Q (coe x)} = size { x | P x ∧ Q x } := 
by {simp_rw ← finsum_ones_eq_size, apply finsum_set_subtype_eq_finsum_set (1 : α → ℤ)} 




-- size {P ∈ M.ps.classes | (X ∩ P).nonempty} = size {P : M.parallel_class | (X ∩ ↑P).nonempty}
-------------------------------------------------------------
open set 

-- Size 

lemma compl_size (X : set α) : size Xᶜ = size (univ : set α) - size X :=
  calc size Xᶜ = size (X ∪ Xᶜ) + size (X ∩ Xᶜ) - size X : by linarith [size_modular X Xᶜ]
  ...          = size (univ : set α)  + size (∅ : set α)  - size X : by rw [union_compl_self X, inter_compl_self X]
  ...          = size (univ : set α) - size X                  : by linarith [size_empty α]

lemma size_compl (X : set α) : size X = size (univ : set α) - size(Xᶜ) := 
  by linarith [compl_size X]

lemma contains_singleton (X : set α) : X.nonempty → (∃ Y, Y ⊆ X ∧ size Y = 1) :=
begin
  rintros ⟨e,he⟩,  
  from ⟨{e},⟨set.singleton_subset_iff.mpr he, size_singleton e⟩⟩, 
end


lemma ssubset_size {X Y : set α} : (X ⊆ Y) → (size X < size Y) → (X ⊂ Y) := 
  λ h h', by {rw ssubset_iff_subset_ne, from ⟨h, λ h'', by {rw h'' at h', linarith}⟩}


lemma size_monotone {X Y: set α} (hXY : X ⊆ Y) : size X ≤ size Y := 
  by {have := size_modular X (Y \ X), rw union_diff_of_subset  hXY at this      , 
        rw inter_diff at this, linarith [size_nonneg(Y \ X), size_empty α]}

lemma size_subadditive {X Y : set α} : size (X ∪ Y) ≤ size X + size Y :=
  by linarith [size_modular X Y, size_nonneg (X ∩ Y)] 

lemma compl_inter_size (X Y : set α) : size (X ∩ Y) + size (Xᶜ ∩ Y) = size Y := 
  by rw [←size_modular, ←inter_distrib_right, union_compl_self, univ_inter, ←inter_distrib_inter_left, 
  inter_compl_self, empty_inter, size_empty]; ring

lemma compl_inter_size_subset {X Y : set α} : 
  X ⊆ Y → size (Xᶜ ∩ Y) = size Y - size X := 
  λ hXY, by {have := compl_inter_size X Y, rw subset_iff_inter_eq_left.mp hXY at this, linarith} 

lemma diff_size {X Y : set α} : X ⊆ Y → size (Y \ X) = size Y - size X :=  
  λ hXY, by rw [diff_eq, inter_comm, compl_inter_size_subset hXY]

lemma size_diff_le_size (X Y : set α) : size (X \ Y) ≤ size X := 
  size_monotone (diff_subset _ _) 

lemma size_disjoint_sum {X Y : set α}: X ∩ Y = ∅ → size (X ∪ Y) = size X + size Y := 
  λ hXY, by {have := size_modular X Y, rw [hXY, size_empty] at this, linarith}

lemma size_modular_diff (X Y : set α) : size (X ∪ Y) = size (X \ Y) + size (Y \ X) + size (X ∩ Y) :=
  by {rw [←size_disjoint_sum (diffs_disj X Y)], have := (symm_diff_alt X Y), 
        unfold symm_diff at this,rw this, linarith [diff_size (inter_subset_union X Y)]  }


lemma size_induced_partition (X Y : set α) : size X = size (X ∩ Y) + size (X \ Y) := 
  by {nth_rewrite 0 ←diff_union X Y, refine size_disjoint_sum _, apply partition_inter}

lemma size_induced_partition_inter (X Y : set α) : size X = size (X ∩ Y) + size (X ∩ Yᶜ) := 
  by {rw ←diff_eq, apply size_induced_partition,}

lemma size_compl_sum (X : set α) : size X + size Xᶜ = size (univ : set α) := 
  by {have := size_disjoint_sum (inter_compl_self X), rw (union_compl_self X) at this, linarith}

lemma size_mono_inter_left (X Y : set α) : size (X ∩ Y) ≤ size X := 
size_monotone (inter_subset_left _ _)

lemma size_mono_inter_right (X Y : set α) : size (X ∩ Y) ≤ size Y := 
size_monotone (inter_subset_right _ _)

lemma size_mono_union_left (X Y : set α) : size X ≤ size (X ∪ Y)  := 
size_monotone (subset_union_left _ _)

lemma size_mono_union_right (X Y : set α) : size Y ≤ size (X ∪ Y) := 
size_monotone (subset_union_right _ _)


lemma size_zero_empty {X : set α} : (size X = 0) → X = ∅ := 
begin
  contrapose!, intros hne hs, 
  rw [push_neg.not_eq, set.ne_empty_iff_nonempty] at hne, 
  cases contains_singleton X hne with Y hY,
  linarith [size_monotone hY.1], 
end  

@[simp] lemma size_zero_iff_empty {X : set α} : (size X = 0) ↔ (X = ∅) := 
  by {split, apply size_zero_empty, intros h, rw h, exact size_empty α}

@[simp] lemma size_le_zero_iff_eq_empty {X : set α}:
  size X ≤ 0 ↔ X = ∅ := 
by {rw [← size_zero_iff_empty], exact ⟨λ h, le_antisymm h (size_nonneg _), λ h, le_of_eq h⟩} 



lemma size_nonempty {X : set α} : X.nonempty → 0 < size X  := 
begin
  rw ←set.ne_empty_iff_nonempty, 
  from λ hX, lt_of_le_of_ne (size_nonneg X) (λ h, hX (size_zero_empty h.symm)), 
end

lemma size_pos_iff_nonempty {X : set α} : X.nonempty ↔ 0 < size X := 
begin
  refine ⟨λ h, size_nonempty h, λ h, _⟩,
  rw ←set.ne_empty_iff_nonempty, 
  from λ h', by {rw [h', size_empty] at h, from lt_irrefl 0 h} 
end

lemma size_pos_iff_ne_empty {X : set α}:
  0 < size X ↔ X ≠ ∅ := 
by rw [← size_pos_iff_nonempty, ← ne_empty_iff_nonempty]

lemma one_le_size_iff_nonempty {X : set α} : X.nonempty ↔ 1 ≤ size X := 
  size_pos_iff_nonempty

lemma one_le_size_univ_of_nonempty (hα: nonempty α): 1 ≤ size (univ : set α) := 
by rwa [nonempty_iff_univ_nonempty, one_le_size_iff_nonempty] at hα
  --one_le_size_iff_nonempty.mp hα 

lemma size_strict_monotone {X Y : set α} : X ⊂ Y → size X < size Y := 
λ hXY, by {rw [size_induced_partition Y X, inter_comm, subset_iff_inter_eq_left.mp hXY.1], 
              linarith [size_nonempty (ssubset_diff_nonempty hXY)]} 

lemma eq_of_eq_size_subset {X Y : set α} : (X ⊆ Y) → (size X = size Y) → X = Y :=
  λ hXY, by {cases subset_ssubset_or_eq hXY, intros sXY, exfalso, 
  replace h := size_strict_monotone h, linarith, exact λ h', h}

lemma eq_of_eq_size_subset_iff {X Y : set α} : 
  (X ⊆ Y) → ((size X = size Y) ↔ X = Y) :=
  λ hXY, ⟨λ h, eq_of_eq_size_subset hXY h, λ h, by {rw h}⟩

lemma eq_of_le_size_subset {X Y : set α} : 
  (X ⊆ Y) → (size Y ≤ size X) → X = Y :=
  λ hXY hXY', by {apply eq_of_eq_size_subset hXY, exact le_antisymm (size_monotone hXY) hXY'}

lemma size_eq_of_supset {X Y : set α} : (X ⊆ Y) → (size Y ≤ size X) → size X = size Y := 
  λ hss hs, by linarith[size_monotone hss]

lemma single_subset (X : set α) : X.nonempty → (∃ Y Z, Y ∩ Z = ∅ ∧ Y ∪ Z = X ∧ size Y = 1) := 
  begin
    intro h, cases contains_singleton X h with Y hY, use Y, use X \ Y, 
    exact ⟨inter_diff _ _,⟨union_diff_of_subset  hY.1,hY.2⟩⟩,
  end


lemma single_subset_nonempty {X : set α}: X.nonempty → (∃ Y Z, Y ∩ Z = ∅ ∧ Y ∪ Z = X ∧ size Y = 1) := 
  λ hX, single_subset X hX 

lemma union_ssubsets (X : set α) : 
  1 < size X  → ∃ Y Z : set α, Y ⊂ X ∧ Z ⊂ X ∧ Y ∩ Z = ∅ ∧ Y ∪ Z = X := 
begin
  intros hX, 
  have h : X.nonempty := by {rw size_pos_iff_nonempty, linarith}, 
  rcases single_subset X h with ⟨Y,⟨Z,⟨hI,hα,h1⟩⟩⟩, use Y, use Z, 
  simp_rw ←hα at ⊢ hX, 
  refine ⟨ssubset_of_subset_ne _ (λ h, _), ssubset_of_subset_ne _ (λ h, _), hI, rfl⟩, 
  apply subset_union_left, 
  rw ←h at hX, linarith, 
  apply subset_union_right,
  have := size_modular Y Z, 
  rw [hα, hI, size_empty, h1, ←hα, ←h] at this,
  linarith, 
end


lemma size_pos_has_mem {X : set α}: 
  0 < size X → ∃ e, e ∈ X := 
λ h, (ne_empty_iff_has_mem.mp (λ h', by {rw [h',size_empty] at h, exact lt_irrefl 0 h}))

lemma size_pos_iff_has_mem {X : set α}: 
  0 < size X ↔ ∃ e, e ∈ X := 
⟨λ h, size_pos_has_mem h, λ h, by {cases h with e he, have := size_monotone (singleton_subset_iff.mpr he), rw size_singleton at this, linarith}⟩ 


lemma one_le_size_iff_has_mem {X : set α}: 
  1 ≤ size X ↔ ∃ e, e ∈ X := 
by {convert size_pos_iff_has_mem, apply_instance, }


lemma size_zero_iff_has_no_mem {X : set α}:
  size X = 0 ↔ ¬ ∃ e, e ∈ X := 
begin
  rw [iff.comm, ←not_iff, ←size_pos_iff_has_mem, not_iff], 
  refine ⟨λ h, _, λ h, by linarith ⟩ ,
  linarith [size_nonneg X, not_lt.mp h]
end

lemma size_le_zero_iff_has_no_mem {X : set α}:
  size X ≤ 0 ↔ ¬ ∃ e, e ∈ X := 
begin
  rw ←size_zero_iff_has_no_mem, split, 
  { intro, linarith [size_nonneg X]}, 
  intro h, rw h, 
end



lemma elem_diff_of_size_lt {X Y : set α}(h : size X < size Y):
  ∃ (e : α), e ∈ Y ∧ e ∉ X :=
begin
  suffices : 0 < size (Y \ X), rw [size_pos_iff_has_mem] at this, tauto, 
  rw diff_eq, linarith [size_induced_partition_inter Y X, size_mono_inter_right Y X], 
end 

lemma size_insert_mem_compl {X : set α} {e : α} :
  e ∈ Xᶜ → size (X ∪ {e}) = size X + 1 := 
begin
  intro hXe, have := size_modular X {e}, 
  rw [inter_comm X, nonmem_disjoint (by rwa ←mem_compl_iff), size_singleton, size_empty] at this, 
  linarith, 
end

lemma size_insert_ub {X : set α}{e : α}:
  size (X ∪ {e}) ≤ size X + 1 := 
by linarith [size_nonneg (X ∩ {e}), size_modular X {e}, size_singleton e]

lemma size_insert_nonmem {X : set α} {e : α}: 
  e ∉ X → size (X ∪ {e}) = size X + 1 := 
λ hXe, by {apply size_insert_mem_compl, rwa ←mem_compl_iff at hXe}


lemma size_remove_mem {X : set α}{e : α} :
  e ∈ X → size (X \ {e}) = size X - 1 := 
begin
  intro heX, 
  have h: e ∈ (X \ {e})ᶜ := by 
  { rw [←singleton_subset_iff, compl_single_remove heX], 
    apply subset_union_right}, 
  nth_rewrite 1 ←remove_add_elem  heX, 
  linarith [size_insert_mem_compl h], 
end


lemma nonempty_has_sub_one_size_ssubset {X : set α}:
  X ≠ ∅ → ∃ Y : set α, Y ⊂ X ∧ size Y = size X - 1 := 
λ hX, by {cases ne_empty_has_mem hX with e he, 
exact ⟨X \ {e}, ⟨ssubset_of_remove_mem he,size_remove_mem he⟩ ⟩}

lemma ne_univ_has_add_one_size_ssupset {X : set α}:
  X ≠ univ → ∃ Y, X ⊂ Y ∧ size Y = size X + 1 := 
begin
  intro hX, rcases nonempty_has_sub_one_size_ssubset (λ h, _ : Xᶜ ≠ ∅) with ⟨Y, ⟨h₁,h₂⟩ ⟩, 
  refine ⟨Yᶜ , ⟨scompl_subset_comm.mpr h₁, _⟩⟩,
  linarith [size_compl X, size_compl Y], 
  exact hX (compl_empty_iff.mp h), 
end

lemma ne_univ_has_add_one_size_ssupset_element {X : set α}:
  X ≠ univ → ∃ (e:α), X ⊂ X ∪ {e} ∧ size (X ∪ {e}) = size X + 1 := 
begin
  intro hX, 
  rcases elem_only_larger_ssubset (ssubset_univ_of_ne_univ hX) with ⟨e,⟨_,he⟩⟩, 
  refine ⟨e, ⟨ssub_of_add_nonmem he, size_insert_nonmem he⟩⟩, 
end

lemma size_remove_insert {X : set α}{e f : α}(he : e ∈ X)(hf : f ∉ X) : 
  size ((X \ {e}) ∪ {f}) = size X := 
by linarith [size_insert_nonmem (nonmem_diff_of_nonmem {e} hf),size_remove_mem he]

lemma size_insert_remove {X : set α}{e f : α}(he : e ∈ X)(hf : f ∉ X) : 
  size ((X ∪ {f}) \ {e}) = size X := 
by linarith [size_insert_nonmem hf, size_remove_mem (mem_union_of_mem_left {f} he)]

lemma exchange_pair_sizes {X Y : set α}{e f : α}: 
  size X = size Y → e ∈ X\Y → f ∈ Y \ X → size ((X\{e}) ∪ {f}) = size ((Y \ {f}) ∪ {e}) :=
λ h he hf, by {rw elem_diff_iff at he hf, rw [size_remove_insert hf.1 he.2, size_remove_insert he.1 hf.2], exact h}

lemma size_union_distinct_singles {e f : α}: 
  e ≠ f → size ({e,f} : set α) = 2 :=
begin
  intros hef, 
  have : e ∉ ({f} : set α) := by {rw ←singleton_subset_iff, from λ h, hef (nested_singletons_eq h)}, 
  have := size_insert_nonmem this, 
  rw [union_comm, size_singleton, union_singletons_eq_pair] at this, 
  linarith, 
end 

lemma two_le_size_iff_has_distinct {X : set α}:
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

lemma size_union_singles_lb (e f : α): 
  1 ≤ size ({e,f} : set α) := 
by {rw ←union_singletons_eq_pair, 
    linarith [size_monotone (@subset_union_left α {e} {f}),size_singleton e],}

lemma size_union_singles_ub (e f : α):
  size ({e,f} : set α) ≤ 2 := 
begin
  by_cases e = f, 
  rw [h, pair_eq_singleton, size_singleton], linarith, 
  linarith [size_union_distinct_singles h],
end 

lemma equal_or_single_in_diff {X Y : set α} :
  size X = size Y → X = Y ∨  ∃ e, e ∈ X \ Y :=
begin
  intros hs, by_contra h, rw not_or_distrib at h, cases h with h1 h2, 
  rw ←ne_empty_iff_has_mem at h2, push_neg at h2,  
  rw diff_empty_iff_subset at h2, 
  from h1 (eq_of_eq_size_subset h2 hs),
end

lemma size_one_iff_eq_singleton {X : set α}:
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

lemma size_le_one_iff_empty_or_singleton {X : set α}:
  size X ≤ 1 ↔ X = ∅ ∨ ∃ e, X = {e} :=
begin
  refine ⟨λ h, _, λ h, _⟩, swap, 
  { rcases h with (rfl | ⟨e, rfl⟩); simp only [size_singleton, size_empty], norm_num,},
  by_cases h' : size X ≤ 0, 
  { left, rw ←size_zero_iff_empty, linarith [size_nonneg X],},
  right, rw ←size_one_iff_eq_singleton, 
  exact le_antisymm h (by linarith), 
end

lemma size_le_one_iff_mem_unique {X : set α}: 
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

lemma size_eq_two_iff_pair {X : set α}:
  size X = 2 ↔ ∃ (e f : α), e ≠ f ∧ X = {e,f} :=
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


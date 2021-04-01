import .finsum_more prelim.single data.nat.parity data.zmod.basic data.zmod.parity data.fincard
import prelim.induction .fin_api
open_locale classical big_operators 
noncomputable theory 

universes u v w

variables {α : Type*} {β : Type*} {s t : set α} {e f x : α}

open set 

section basic 

def fincard (s : set α) : ℕ := ∑ᶠ x in s, 1  

lemma fincard_eq_sum_ones (s : set α) : fincard s = ∑ᶠ x in s, 1 := rfl 

lemma finite.fincard_eq_finset_card {s : set α} (hs : s.finite) :
  fincard s = finset.card (hs.to_finset) :=
begin
  convert (finset.card_eq_sum_ones (hs.to_finset)).symm, 
  exact finsum_in_eq_finset_sum''' (1 : α → ℕ) hs, 
end

lemma fincard_eq_finset_card (s : set α)[fintype α]: 
  fincard s = s.to_finset.card := 
begin
  convert (finset.card_eq_sum_ones (s.to_finset)).symm, 
  exact finsum_in_eq_finset_sum' (1 : α → ℕ) _, 
end

lemma fincard_of_infinite {s : set α} (hs : s.infinite) :
  fincard s = 0 := 
by {rw [fincard, finsum_in_eq_zero_of_infinite], convert hs, ext, simp}

lemma nat_card_eq_fincard_univ (α : Type*) : 
  nat.card α = fincard (set.univ : set α) := 
begin
  by_cases h : nonempty (fintype α), 
  { obtain ⟨f⟩ := h, haveI := f, 
    rw [nat.card_eq_fintype_card, fincard_eq_finset_card],  
    simp [finset.card_univ]},
  simp only [not_nonempty_fintype] at h, haveI := h, 
  rw [nat.card_eq_zero_of_infinite, fincard_of_infinite], 
  exact set.infinite_univ, 
end

lemma nat_card_eq_sum_ones (α : Type*) : 
  nat.card α = ∑ᶠ (x : α), 1 := 
by rw [nat_card_eq_fincard_univ, fincard_eq_sum_ones, finsum_eq_finsum_in_univ]

lemma nat_card_subtype_eq_fincard (s : set α) :
  nat.card s = fincard s := 
by {rw [nat_card_eq_sum_ones], exact finsum_subtype_eq_finsum_in (1) s}

@[simp] lemma support_const [has_zero β] {b : β} (hb : b ≠ 0) : 
  function.support (λ x : α, b) = univ :=
by {ext, simp [hb], }

@[simp] lemma support_one : 
  function.support (1 : α → ℕ) = univ :=
support_const (by simp : 1 ≠ 0)

lemma finite_of_fincard_pos {s : set α} (hs : 0 < fincard s) :
  s.finite := 
by_contra (λ hn, by {rw fincard_of_infinite hn at hs, exact lt_irrefl _ hs, })

@[simp] lemma fincard_empty :
  fincard (∅ : set α) = 0 := 
by simp [fincard]

lemma fincard_eq_zero_iff_empty {s : set α} (hs : s.finite) : 
  fincard s = 0 ↔ s = ∅ := 
begin
  rw [fincard_eq_sum_ones, finsum_in_eq_zero_iff _], 
    swap, simpa using hs, 
  exact ⟨λ h, by {ext, simp at *, tauto,}, λ h, by {rw h, simp,}⟩,
end

lemma nonempty_of_fincard_pos {s : set α} (hs : 0 < fincard s): s.nonempty := 
begin
  by_contra hn, 
  rw [← ne_empty_iff_nonempty, not_not] at hn, 
  rw [hn, fincard_empty] at hs,
  exact lt_irrefl _ hs, 
end 

lemma fincard_insert {s : set α} {e : α} (hes : e ∉ s) (hs : s.finite) : 
  fincard (insert e s) = 1 + fincard s :=
finsum_in_insert _ hes hs 

lemma fincard_remove {s : set α} { e : α} (hes : e ∈ s) (hs : s.finite) : 
  fincard s = 1 + fincard (s \ {e}) := 
begin
  convert fincard_insert (nonmem_removal s e) (finite.diff hs _), 
  rw [remove_insert, insert_eq_of_mem hes], 
end

@[simp] lemma fincard_singleton (e : α) : 
  fincard ({e} : set α) = 1 := 
by simp [fincard]

lemma fincard_of_finite_eq_card {s : set α} (hs : s.finite) : 
  fincard s = (hs.to_finset).card := 
begin
  rw [fincard_eq_sum_ones, finset.card_eq_sum_ones, finsum_in_eq_finset_sum],  simp,
  exact set.finite.subset hs (inter_subset_left _ _), 
end

lemma fincard_image_emb (f : α ↪ β) (s : set α) : 
  fincard (f '' s) = fincard s := 
begin
  by_cases hs : s.finite,
  { rw [fincard_eq_sum_ones, fincard_eq_sum_ones, finsum_in_image' hs], 
    exact (set.inj_on_of_injective f.inj' _)},
  rw [fincard_of_infinite, fincard_of_infinite], assumption, 
  rw set.infinite_image_iff, assumption, 
  exact (set.inj_on_of_injective f.inj' _), 
end

@[simp] lemma nat.finsum_const_eq_mul_nat_card (b : ℕ) : 
  ∑ᶠ (i : α), b = b * (nat.card α) := 
by rw [← mul_one b, ← mul_distrib_finsum, nat_card_eq_sum_ones, mul_one]

@[simp] lemma nat.finsum_in_const_eq_mul_fincard (b : ℕ){s : set α} : 
  ∑ᶠ i in s, b = b * (fincard s) := 
by rw [← mul_one b, ← mul_distrib_finsum_in, fincard_eq_sum_ones, mul_one]

 
lemma finite_set_induction (P : set α → Prop): 
  (P ∅) → (∀ (s : set α) (e : α), e ∉ s → P s → P (insert e s)) → (∀ (s : set α), s.finite → P s) :=
begin
  suffices h' : ∀ n : ℕ, (P ∅) → (∀ (s : set α) (e : α), e ∉ s → P s → P (insert e s)) 
    → (∀ (s : set α), s.finite → fincard s = n → P s), 
  { exact λ hbase ih s hs, h' (fincard s) hbase ih _ hs rfl},
  intros n hempt, 
  induction n with n ih,
  { intros ih s hfin hfincard, rwa (fincard_eq_zero_iff_empty hfin).mp hfincard, }, 
  intros h' s hfin hcard,  
  obtain ⟨e,he⟩ := nonempty_of_fincard_pos (by {rw hcard, simp} : 0 < fincard s), 
  rw [fincard_remove he hfin, nat.one_add] at hcard, 
  convert h' _ _ (nonmem_removal s e) (ih h' (s \ {e}) (finite.diff hfin _) (nat.succ.inj hcard)), 
  rw [remove_insert, insert_eq_of_mem he], 
end


/-!
This file contains an API for `fincard`, which is the noncomputable function assigning each finite
set to its fincard as an integer, and each infinite set to zero. Also `nat.card` is defined similarly 
for types. Most lemmas are only true in a finite setting, and have two versions, one with explicit
finiteness assumptions, and one in which they are derived from a `fintype` instance . Lemmas of the 
former type are usually less useful for us, and go in the `finite` namespace. 
-/

/-! Basic lemmas about fincard.  -/

--lemma nat_card_eq_fincard (α : Type*) : nat.card α = fincard (set.univ : set α) := rfl 


lemma nat_card_coe_set_eq_fincard (s : set α) :
  nat.card s = fincard s := 
by rw [nat_card_subtype_eq_fincard]

lemma nat_card_type_of_eq_fincard_set_of (P : α → Prop): 
  nat.card {x // P x} = fincard {x | P x} :=
nat_card_coe_set_eq_fincard P

/-- a positive type fincard gives rise to a fintype -/
def fintype_of_nat_card_pos {α : Type*} (hα : 0 < nat.card α) : 
  fintype α := 
set.fintype_of_univ_finite (by {rw [nat_card_eq_fincard_univ] at hα, exact finite_of_fincard_pos hα,})

lemma contains_singleton {s : set α} : s.nonempty → (∃ t, t ⊆ s ∧ fincard t = 1) :=
λ ⟨e,he⟩, ⟨{e},⟨set.singleton_subset_iff.mpr he, fincard_singleton e⟩⟩

lemma exists_mem_of_fincard_pos (h : 0 < fincard s) : 
  ∃ e, e ∈ s := 
(ne_empty_iff_has_mem.mp (λ hs, lt_irrefl _ (by {rwa [hs, fincard_empty] at h})))

@[simp] lemma finsum_ones_eq_fincard (s : set α) : 
  ∑ᶠ x in s, 1 = fincard s := 
by rw [fincard]

@[simp] lemma finsum_ones_eq_nat_card (α : Type*) : 
  ∑ᶠ (x : α), 1 = nat.card α := 
by rw [finsum_eq_finsum_in_univ, finsum_ones_eq_fincard, nat_card_eq_fincard_univ]

lemma fincard_set_of_eq_fincard_subtype (P : α → Prop):
  fincard {x | P x} = nat.card {x // P x} :=
by rw [← finsum_ones_eq_fincard, ← finsum_ones_eq_nat_card, ← finsum_subtype_eq_finsum_in_set_of]

lemma fincard_set_of_push (P Q : α → Prop) :
  fincard {x : {y // P y} | Q (x : α)} = fincard { x | P x ∧ Q x } := 
by {rw [← finsum_ones_eq_fincard, ← finsum_ones_eq_fincard], 
    convert finsum_set_subtype_eq_finsum_set (1 : α → ℕ) P Q,  }


end basic 

/-! The lemmas in this section are true without any finiteness assumptions -/
section general 


lemma fincard_one_iff_eq_singleton :
  fincard s = 1 ↔ ∃ e, s = {e} := 
begin
  refine ⟨λ h, _, λ h, _⟩, swap,  
    cases h with e he, rw he, apply fincard_singleton, 
  
  have hs := finite_of_fincard_pos (by linarith : 0 < fincard s), 
  obtain ⟨e,he⟩ := exists_mem_of_fincard_pos (by linarith : 0 < fincard s), 
  use e, 
  ext, 
  simp only [set.mem_singleton_iff],
  refine ⟨λ h', _, λ h', by {rwa ← h' at he}⟩, 
  rw ← finsum_ones_eq_fincard at h,
  have hs' := finsum_in_subset_le_finsum_in_of_nonneg hs 
    (_ : {e,x} ⊆ s) (λ x hx, (by norm_num: 0 ≤ 1)), 
  { by_contra hxe, 
    rw [finsum_pair (ne.symm hxe), h, add_le_iff_nonpos_right] at hs',
    norm_num at hs'}, 
  rw ← set.singleton_subset_iff at he h', 
  convert set.union_subset he h', 
end

lemma eq_of_mems_fincard_one (hs : fincard s = 1) (he : e ∈ s) (hf : f ∈ s):
  e = f := 
begin
  obtain ⟨x, rfl⟩ := fincard_one_iff_eq_singleton.mp hs, 
  rw set.mem_singleton_iff at he hf, 
  rw [he,hf], 
end

lemma fincard_pair (hef : e ≠ f) : 
  fincard ({e,f} : set α) = 2 :=
by {rw [← finsum_ones_eq_fincard, finsum_pair hef]}


end general 

/-! Lemmas about the relationship between fincard and finsumming ones -/


/-! 
This section contains lemmas that require finiteness of sets to be true. These versions 
all have explicit set.finite assumptions; the versions that use an instance are later. 
-/

section finite

open set 

namespace set.finite



lemma fincard_modular (s t : set α) (hs : s.finite) (ht : t.finite) : 
  fincard (s ∪ t) + fincard (s ∩ t) = fincard s + fincard t :=
finsum_in_union_inter hs ht

lemma fincard_union {s t : set α} (hs : s.finite) (ht : t.finite):
  (fincard (s ∪ t) : ℤ) = fincard s + fincard t - fincard (s ∩ t) := 
by linarith [fincard_modular _ _ hs ht]

lemma fincard_union_disj {s t : set α} (hs : s.finite) (ht : t.finite) (hst : disjoint s t) :
  fincard (s ∪ t) = fincard s + fincard t := 
by {zify, simp [fincard_union hs ht,  disjoint_iff_inter_eq_empty.mp hst]}

lemma fincard_diff {s t : set α} (hs : s.finite) (hst : t ⊆ s) : 
  (fincard (s \ t) : ℤ) = fincard s - fincard t :=
begin
  unfold fincard, 
  have := @finsum_in_sdiff _ _ _ (1 : α → ℕ) _ _ hs hst,  
  change ∑ᶠ (i : α) in t, 1 + ∑ᶠ (i : α) in s \ t, 1 = ∑ᶠ (i : α) in s, 1 at this, 
  simp [← this], 
end

lemma fincard_symm_diff {s t : set α} (hs : s.finite) (ht : t.finite): 
  (fincard (s.symm_diff t) : ℤ) = fincard s + fincard t - 2 * fincard (s ∩ t) :=
begin
  rw [
    symm_diff_alt, 
    fincard_diff (hs.union ht) (subset.trans (inter_subset_left _ _) (subset_union_left _ _)), 
    fincard_union hs ht],
  linarith,   
end

lemma fincard_symm_diff_mod2 {s t : set α} (hs : s.finite) (ht : t.finite) :
  (fincard (s.symm_diff t) : zmod 2) = fincard s + fincard t := 
begin
  rw [← int.cast_coe_nat, fincard_symm_diff hs ht, int.cast_sub], 
  convert sub_zero _, swap, simp, 
  rw [int.cast_mul], 
  convert zero_mul _, 
end


lemma fincard_monotone (ht : t.finite) (hst : s ⊆ t) : fincard s ≤ fincard t := 
begin
  have hs := subset ht hst, 
  have := fincard_modular s (t \ s) hs (ht.diff s), 
  rw [union_diff_of_subset hst, inter_diff, fincard_empty] at this, 
  linarith,
end 

lemma ssubset_fincard (hs : s.finite) (ht : t.finite) (hst : s ⊆ t) (hst' : fincard s < fincard t) :
  s ⊂ t := 
by {rw set.ssubset_iff_subset_ne, from ⟨hst, λ hn, by {rw hn at hst', exact lt_irrefl _ hst'}⟩}

lemma fincard_subadditive (hs : s.finite) (ht : t.finite) : fincard (s ∪ t) ≤ fincard s + fincard t :=
  by linarith [fincard_modular s t hs ht] 

lemma compl_inter_fincard (s t : set α) (ht : t.finite) : 
  fincard (s ∩ t) + fincard (sᶜ ∩ t) = fincard t := 
by {rw [←fincard_modular, ←inter_distrib_right, union_compl_self, univ_inter, 
  ←inter_distrib_inter_left, inter_compl_self, empty_inter, fincard_empty, add_zero];
  exact inter_right (by assumption) _, }

lemma compl_inter_fincard_subset (ht : t.finite) (hst : s ⊆ t) : 
  (fincard (sᶜ ∩ t) : ℤ) = fincard t - fincard s := 
by {have := compl_inter_fincard s t ht, rw subset_iff_inter_eq_left.mp hst at this, linarith} 

lemma diff_fincard (ht : t.finite) (hst : s ⊆ t) : (fincard (t \ s) : ℤ) = fincard t - fincard s :=  
by rw [diff_eq, inter_comm, compl_inter_fincard_subset ht hst]

lemma fincard_diff_le_fincard (s t : set α) (hs : s.finite) : fincard (s \ t) ≤ fincard s := 
  fincard_monotone hs (diff_subset _ _) 
-- the above lemma is also true if just `s ∩ t` is finite 

lemma fincard_union_of_inter_empty (hs : s.finite) (ht : t.finite) (hst : s ∩ t = ∅) :
  fincard (s ∪ t) = fincard s + fincard t := 
by {have := fincard_modular s t hs ht, rw [hst, fincard_empty] at this, linarith}

lemma fincard_union_of_disjoint (hs : s.finite) (ht : t.finite) (hst : disjoint s t) :
  fincard (s ∪ t) = fincard s + fincard t := 
fincard_union_of_inter_empty hs ht (disjoint_iff_inter_eq_empty.mp hst)

lemma fincard_modular_diff (s t : set α) (hs : s.finite) (ht : t.finite) : 
  fincard (s ∪ t) = fincard (s \ t) + fincard (t \ s) + fincard (s ∩ t) :=
begin
  rw [←fincard_union_of_inter_empty _ _ (inter_diffs_eq_empty s t)],
  { have := (symm_diff_alt s t), 
    unfold symm_diff at this,
    rw this, 
    linarith [diff_fincard (union hs ht) (inter_subset_union s t)]}, 
  repeat {apply diff, assumption}, 
end

lemma fincard_induced_partition (s t : set α) (hs : s.finite)  :
  fincard s = fincard (s ∩ t) + fincard (s \ t) := 
begin
  nth_rewrite 0 ←diff_union s t, 
  refine fincard_union_of_inter_empty (inter_left hs _) (diff hs _) (partition_inter _ _), 
end 

lemma fincard_induced_partition_inter (s t : set α) (hs : s.finite) :
  fincard s = fincard (s ∩ t) + fincard (s ∩ tᶜ) := 
by {rw ←diff_eq, apply fincard_induced_partition _ _ hs, }

lemma fincard_mono_inter_left (s t : set α) (hs : s.finite) : fincard (s ∩ t) ≤ fincard s := 
fincard_monotone hs (inter_subset_left _ _)

lemma fincard_mono_inter_right (s t : set α) (ht : t.finite) : fincard (s ∩ t) ≤ fincard t := 
fincard_monotone ht (inter_subset_right _ _)

lemma fincard_mono_union_left (s t : set α) (ht : t.finite) : fincard s ≤ fincard (s ∪ t)  := 
begin
  by_cases hs : s.finite, 
  apply fincard_monotone (union hs ht) (subset_union_left _ _), 
  rw [fincard_of_infinite hs, fincard_of_infinite], 
  exact infinite_mono (subset_union_left _ _) hs, 
end 

lemma fincard_mono_union_right (s t : set α) (hs : s.finite) : fincard t ≤ fincard (s ∪ t) := 
by {rw union_comm, apply fincard_mono_union_left _ _ hs}

lemma empty_of_fincard_zero (hs : s.finite) (hfincard : fincard s = 0) : s = ∅ := 
begin
  rw eq_empty_iff_forall_not_mem, intros x hx, 
  have h' := fincard_monotone hs (singleton_subset_iff.mpr hx), 
  rw [hfincard, fincard_singleton] at h', 
  linarith, 
end  

lemma fincard_zero_iff_empty (hs : s.finite) : (fincard s = 0) ↔ (s = ∅) := 
  by {split, apply empty_of_fincard_zero hs, intros h, rw h, exact fincard_empty}

lemma fincard_le_zero_iff_eq_empty (hs : s.finite) :
  fincard s ≤ 0 ↔ s = ∅ := 
by rw [← fincard_zero_iff_empty hs, nat.le_zero_iff]

lemma fincard_nonempty (hs : s.finite) (hne : s.nonempty) : 0 < fincard s  := 
begin
  suffices h' : 0 ≠ fincard s, exact zero_lt_iff.mpr (ne.symm h'),
  rw [←set.ne_empty_iff_nonempty] at hne,  
  exact λ h, hne (empty_of_fincard_zero hs h.symm), 
end

lemma nonempty_iff_fincard_pos (hs : s.finite) : s.nonempty ↔ 0 < fincard s := 
begin
  refine ⟨λ h, fincard_nonempty hs h, λ h, _⟩,
  rw ←set.ne_empty_iff_nonempty, 
  exact λ h', by {rw [h', fincard_empty] at h, from lt_irrefl 0 h}, 
end

lemma one_le_fincard_iff_nonempty (hs : s.finite) : s.nonempty ↔ 1 ≤ fincard s := 
  nonempty_iff_fincard_pos hs 


lemma one_le_fincard_of_nonempty (hs : s.nonempty) (hs' : s.finite) : 1 ≤ fincard s := 
  (one_le_fincard_iff_nonempty hs').mp hs 

lemma fincard_strict_monotone (ht : t.finite) (hst : s ⊂ t) : fincard s < fincard t := 
begin
  rw [fincard_induced_partition t s ht, inter_comm, subset_iff_inter_eq_left.mp hst.1], 
  linarith [fincard_nonempty (diff ht _) (ssubset_diff_nonempty hst)], 
end 

lemma eq_of_eq_fincard_subset (ht : t.finite) (hst : s ⊆ t) (hfincard : fincard s = fincard t) :
  s = t :=
begin
  unfreezingI {rcases subset_ssubset_or_eq hst with (hst' | rfl)},
    swap, refl, 
  have := fincard_strict_monotone ht hst', rw hfincard at this, 
  exact false.elim (lt_irrefl _ this),
end 

lemma eq_of_eq_fincard_subset_iff (ht : t.finite) (hst : s ⊆ t) : 
  ((fincard s = fincard t) ↔ s = t) :=
⟨λ h, eq_of_eq_fincard_subset ht hst h, λ h, by {rw h}⟩

lemma eq_of_le_fincard_subset (ht : t.finite) (hst : s ⊆ t) (hfincard : fincard t ≤ fincard s) : 
  s = t :=
by {apply eq_of_eq_fincard_subset ht hst, exact le_antisymm (fincard_monotone ht hst) hfincard}

lemma fincard_eq_of_supset (ht : t.finite) (hst : s ⊆ t) (hfincard : fincard t ≤ fincard s) :
  fincard s = fincard t := 
by linarith [fincard_monotone ht hst]

lemma fincard_pos_iff_has_mem (hs : s.finite) : 
  0 < fincard s ↔ ∃ e, e ∈ s := 
by rw [← nonempty_iff_fincard_pos hs, set.nonempty_def] 

lemma one_le_fincard_iff_has_mem (hs : s.finite) : 
  1 ≤ fincard s ↔ ∃ e, e ∈ s := 
by {convert fincard_pos_iff_has_mem hs}

lemma fincard_zero_iff_has_no_mem (hs : s.finite) :
  fincard s = 0 ↔ ¬ ∃ e, e ∈ s := 
begin
  rw [iff.comm, ←not_iff, ←(fincard_pos_iff_has_mem hs), not_iff], 
  refine ⟨λ h, _, λ h, by linarith ⟩ ,
  linarith [not_lt.mp h], 
end

lemma fincard_le_zero_iff_has_no_mem (hs : s.finite) :
  fincard s ≤ 0 ↔ ¬ ∃ e, e ∈ s := 
by {rw ←(fincard_zero_iff_has_no_mem hs), split, { intro, linarith}, intro h, rw h}

lemma mem_diff_of_fincard_lt (hs : s.finite) (hst : fincard s < fincard t) :
  ∃ (e : α), e ∈ t ∧ e ∉ s :=
begin  
  suffices h' : 0 < fincard (t \ s), 
    obtain ⟨e, he⟩ := exists_mem_of_fincard_pos h', tauto, 
  have ht := finite_of_fincard_pos (lt_of_le_of_lt (nat.zero_le _) hst), 
  linarith [fincard_induced_partition t s ht, fincard_mono_inter_right t s hs], 
end 

lemma fincard_union_singleton_compl (hs : s.finite) (hes : e ∈ sᶜ) :
  fincard (s ∪ {e}) = fincard s + 1 := 
begin
  have := fincard_modular s {e} hs (finite_singleton e), 
  rwa [inter_comm s, nonmem_disjoint (by rwa ←mem_compl_iff), fincard_singleton, 
  fincard_empty, add_zero] at this, 
end

lemma fincard_union_nonmem_singleton (hs : s.finite) (he : e ∉ s) : 
  fincard (s ∪ {e}) = fincard s + 1 := 
by {apply fincard_union_singleton_compl hs, rwa ←mem_compl_iff at he, }

lemma fincard_insert_nonmem (hs : s.finite) (he : e ∉ s) : 
  fincard (has_insert.insert e s) = fincard s + 1 := 
by {convert fincard_union_nonmem_singleton hs he, rw union_singleton}

lemma fincard_remove_mem_add_one_eq (hs : s.finite) (he : e ∈ s): 
  fincard (s \ {e}) + 1 = fincard s := 
begin
  convert (fincard_insert_nonmem (hs.diff _) (nonmem_removal _ _)).symm, 
  rw [insert_diff_singleton, insert_eq_of_mem he], 
end

lemma fincard_remove_mem (hs : s.finite) (he : e ∈ s) :
  (fincard (s \ {e}) :ℤ) = fincard s - 1 := 
by {linarith [fincard_remove_mem_add_one_eq hs he]}

lemma has_sub_one_fincard_ssubset_of_ne_empty (hs : s.finite) (hne : s ≠ ∅) :
  ∃ t, t ⊂ s ∧ (fincard t : ℤ) = fincard s - 1 := 
by {cases ne_empty_has_mem hne with e he, 
exact ⟨s \ {e}, ⟨ssubset_of_remove_mem he, fincard_remove_mem hs he⟩ ⟩}

lemma has_sub_one_fincard_ssubset_of_nonempty (hs : s.finite) (hne : s.nonempty) :
  ∃ t, t ⊂ s ∧ (fincard t : ℤ)  = fincard s - 1 := 
has_sub_one_fincard_ssubset_of_ne_empty hs (ne_empty_iff_nonempty.mpr hne)

lemma ne_univ_has_add_one_fincard_ssupset (hs : s.finite) (hne : s ≠ univ) :
  ∃ t, s ⊂ t ∧ fincard t = fincard s + 1 := 
let ⟨e,he⟩ := ne_univ_iff_has_nonmem.mp hne in 
  ⟨has_insert.insert e s, ssubset_insert he, fincard_insert_nonmem hs he⟩

lemma ne_univ_has_add_one_fincard_ssupset_element (hs : s.finite) (hne : s ≠ univ) :
  ∃ e, s ⊂ s ∪ {e} ∧ fincard (s ∪ {e}) = fincard s + 1 := 
let ⟨e,he⟩ := ne_univ_iff_has_nonmem.mp hne in 
   ⟨e, by {rw union_singleton, exact ssubset_insert he}, fincard_union_nonmem_singleton hs he⟩ 

lemma eq_or_exists_mem_diff_of_fincard_eq (ht : t.finite) (hst : fincard s = fincard t) :
  s = t ∨ ∃ e, e ∈ s \ t :=
begin
  by_contra h, rw not_or_distrib at h, cases h with h1 h2, 
  rw ←ne_empty_iff_has_mem at h2, push_neg at h2,  
  rw diff_empty_iff_subset at h2, 
  refine h1 (eq_of_eq_fincard_subset ht h2 hst),
end

lemma fincard_le_one_iff_empty_or_singleton (hs : s.finite) :
  fincard s ≤ 1 ↔ s = ∅ ∨ ∃ e, s = {e} :=
begin
  refine ⟨λ h, _, λ h, _⟩, swap, 
  { unfreezingI {rcases h with (rfl | ⟨e, rfl⟩)}; 
  simp only [fincard_singleton, fincard_empty], norm_num,},
  by_cases h' : fincard s ≤ 0, 
  { left, rw ←fincard_zero_iff_empty hs, linarith,},
  right, rw ←fincard_one_iff_eq_singleton, 
  exact le_antisymm h (by linarith), 
end 

lemma two_le_fincard_iff_has_distinct (hs : s.finite) :
  2 ≤ fincard s ↔ ∃ e f ∈ s, e ≠ f :=
begin
  split, 
  { intro h, 
    obtain ⟨e,he⟩ := @exists_mem_of_fincard_pos _ s (by linarith),
    obtain ⟨f,hf⟩ := @exists_mem_of_fincard_pos _ (s \ {e}) 
      (by { linarith [fincard_remove_mem_add_one_eq hs he]}), 
    refine ⟨e,f,he,mem_of_mem_of_subset hf (diff_subset _ _), _⟩, 
    rintro rfl, simpa using hf,},
  rintro ⟨e,f,he,hf,hef⟩, 
  rw ← fincard_pair hef, 
  apply fincard_monotone hs (pair_subset_iff.mpr ⟨he, hf⟩), 
end

lemma fincard_le_one_iff_mem_unique (hs : s.finite) : 
  fincard s ≤ 1 ↔ ∀ e f ∈ s, e = f := 
begin
  split, 
  { rw [fincard_le_one_iff_empty_or_singleton hs], 
    unfreezingI {rintros (rfl | ⟨e,rfl⟩)},
      simp [mem_singleton_iff], 
    simp only [mem_singleton_iff], 
    unfreezingI {rintros e f rfl rfl}, 
    refl,},
  refine λ h, by_contra (λ hn, _), 
  rw [not_le, ← nat.add_one_le_iff] at hn, norm_num at hn,
  rw two_le_fincard_iff_has_distinct hs at hn, 
  obtain ⟨e,f,he,hf,hef⟩ := hn, 
  exact hef (h e f he hf),   
end

variables {k : set (set α)}

lemma fincard_sUnion (hk : k.finite) (hk' : ∀ s ∈ k, set.finite s) (hdisj : pairwise_disjoint k) : 
  fincard (⋃₀ k) = ∑ᶠ s in k, fincard s := 
by {convert finsum_in_sUnion' (1 : α → ℕ) hk hk' hdisj; {simp_rw ← finsum_ones_eq_fincard, refl}}

lemma fincard_collection_le_fincard_union (hk : ∀ s ∈ k, set.finite s) 
(hk' : ∀ s ∈ k, set.nonempty s) (hdisj : pairwise_disjoint k): 
  (fincard k ≤ fincard (⋃₀ k)) := 
begin
  by_cases hk'' : k.finite, swap,
  { convert nat.zero_le _, rw fincard_of_infinite hk''},
  rw [fincard_sUnion hk'' hk hdisj, ← finsum_ones_eq_fincard], 
  refine finsum_in_le_finsum_in hk'' (λ x hx, _),  
  rw ← (one_le_fincard_iff_nonempty (hk x hx)), 
  exact hk' x hx, 
end

lemma singletons_of_fincard_collection_eq_fincard_union (hk : k.finite) (hk' : ∀ s ∈ k, set.finite s)
(hk'' : ∀ s ∈ k, set.nonempty s) (hdisj : pairwise_disjoint k) (hfincard : fincard k = fincard (⋃₀ k)): 
  ∀ s ∈ k, fincard s = 1 :=
begin
  rw [fincard_sUnion hk hk' hdisj, ← finsum_ones_eq_fincard] at hfincard,
  conv in (_ = _) {rw eq_comm}, 
  convert (finsum_in_eq_finsum_in_iff_of_le hk (λ x hx, _)).mp hfincard, 
  apply one_le_fincard_of_nonempty (hk'' _ hx) (hk' _ hx), 
end

lemma fincard_collection_eq_fincard_union_iff (hk : k.finite) (hk' : ∀ s ∈ k, set.finite s)
(hk'' : ∀ s ∈ k, set.nonempty s) (hdisj : pairwise_disjoint k) :
  fincard k = fincard (⋃₀ k) ↔ ∀ s ∈ k, fincard s = 1 :=
begin
  refine ⟨λ h, singletons_of_fincard_collection_eq_fincard_union hk hk' hk'' hdisj h, λ h, _⟩, 
  rw [fincard_sUnion hk hk' hdisj, ← finsum_ones_eq_fincard, eq_comm], 
  exact finsum_in_eq_of_eq h, 
end



end set.finite 

end finite 





/-! Lemmas that don't need any finiteness assumptions. Some are proved by splitting into
finite and infinite cases, which is why these lemmas need to appear after the previous 
section.  -/
section general

open set 

lemma compl_nonempty_of_fincard_lt_nat_card (hs : fincard s < nat.card α):  
  sᶜ.nonempty :=
begin
  rw nat_card_eq_fincard_univ at hs,
  exact nonempty_compl.mpr (λ h, lt_irrefl (fincard s) (by {rwa ← h at hs})), 
end

lemma fincard_union_singleton_ub :
  fincard (s ∪ {e}) ≤ fincard s + 1 := 
begin
  by_cases hs : s.finite, 
    linarith [finite.fincard_modular s {e} hs (finite_singleton e), fincard_singleton e], 
  rw [fincard_of_infinite (infinite_mono (subset_union_left s {e}) hs)], 
  linarith, 
end 

lemma fincard_insert_ub : 
  fincard (insert e s) ≤ fincard s + 1 := 
by {rw ← union_singleton, apply fincard_union_singleton_ub, }

lemma single_subset' (hs : s.nonempty) : 
  (∃ t t', t ∩ t' = ∅ ∧ t ∪ t' = s ∧ fincard t = 1) := 
begin
  obtain ⟨t,ht⟩ := contains_singleton hs,
  refine ⟨t, s \ t, set.inter_diff _ _,  _, ht.2⟩, 
  rw [set.union_diff_self, set.subset_iff_union_eq_left.mp ht.1], 
end

lemma single_subset (hs : s.nonempty) : 
  (∃ t t', disjoint t t' ∧ t ∪ t' = s ∧ fincard t = 1) := 
by {simp_rw set.disjoint_iff_inter_eq_empty, exact single_subset' hs}

lemma fincard_remove_union_singleton (he : e ∈ s) (hf : f ∉ s) : 
  fincard ((s \ {e}) ∪ {f}) = fincard s := 
begin
  by_cases hs : s.finite, 
  { have h1 := hs.fincard_remove_mem he, 
    have h2 := finite.fincard_union_nonmem_singleton 
      (hs.diff _) 
      (nonmem_diff_of_nonmem {e} hf), 
    linarith},
  rw [fincard_of_infinite hs, fincard_of_infinite _], 
  apply infinite_of_union, 
  exact infinite_of_finite_diff (finite_singleton e) hs, 
end

lemma fincard_union_singleton_remove (he : e ∈ s) (hf : f ∉ s) : 
  fincard ((s ∪ {f}) \ {e}) = fincard s :=
begin
  convert fincard_remove_union_singleton he hf, 
  rw [union_diff_distrib], 
  convert rfl,
  rw remove_nonmem, 
  simp only [mem_singleton_iff], 
  rintro rfl, 
  exact hf he, 
end  

lemma exchange_pair_fincards (hst : fincard s = fincard t) (he : e ∈ s \ t) (hf : f ∈ t \ s) : 
  fincard (s \ {e} ∪ {f}) = fincard (t \ {f} ∪ {e}) :=
begin
  rw mem_diff_iff at he hf, 
  rwa [fincard_remove_union_singleton hf.1 he.2, fincard_remove_union_singleton he.1 hf.2],
end 

lemma eq_of_pair_fincard_one (h : fincard ({e,f} : set α) = 1) : 
  e = f :=
by_contra (λ hn, by {rw fincard_pair hn at h, norm_num at h})

lemma fincard_eq_one_iff_nonempty_unique_mem : 
  fincard s = 1 ↔ s.nonempty ∧ ∀ x y ∈ s, x = y := 
begin
  rw fincard_one_iff_eq_singleton, 
  split, { rintros ⟨e,rfl⟩, tidy, }, rintros ⟨⟨e,he⟩, h⟩, use e, tidy, 
end

lemma fincard_eq_two_iff_pair {s : set α} :
  fincard s = 2 ↔ ∃ (e f : α), e ≠ f ∧ s = {e,f} :=
begin
  refine ⟨λ h, _, λ h, _⟩, swap, 
  { rcases h with ⟨e,f,hef,rfl⟩, apply fincard_pair hef},
  by_cases hs : s.finite, 
  { obtain ⟨e,he⟩ := exists_mem_of_fincard_pos (by {rw h, norm_num} : 0 < fincard s),
    obtain ⟨f,hf⟩ := exists_mem_of_fincard_pos 
      (by {linarith [finite.fincard_remove_mem_add_one_eq hs he]} : 0 < fincard (s \ {e})),
    refine ⟨e,f,ne.symm (ne_of_mem_diff hf), _⟩,  
    rw eq_comm, apply finite.eq_of_eq_fincard_subset hs, 
    { rw ←union_singletons_eq_pair, 
      apply union_subset (singleton_subset_iff.mpr he),  
      simp only [set.mem_diff, set.mem_singleton_iff] at hf, 
      exact singleton_subset_iff.mpr hf.1, },
    rwa [eq_comm, fincard_pair  (ne.symm (ne_of_mem_diff hf))]}, 
  rw fincard_of_infinite hs at h, 
  norm_num at h, 
end 

lemma fincard_pair_lb (e f : α) : 
  1 ≤ fincard ({e,f} : set α) := 
by {rcases em (e = f) with (rfl | hef), simp, rw fincard_pair hef, norm_num}

lemma fincard_pair_ub (e f : α) :
  fincard ({e,f} : set α) ≤ 2 := 
begin
  rcases em (e = f) with (rfl | hef), 
  { simp only [pair_eq_singleton, fincard_singleton], norm_num},
  rw fincard_pair hef,
end 

lemma has_distinct_of_two_le_fincard (hs : 2 ≤ fincard s):
  ∃ e f ∈ s, e ≠ f := 
(finite.two_le_fincard_iff_has_distinct (finite_of_fincard_pos (by linarith))).mp hs 

lemma has_distinct_of_one_lt_fincard (hs : 1 < fincard s):
  ∃ e f ∈ s, e ≠ f := 
(finite.two_le_fincard_iff_has_distinct (finite_of_fincard_pos (by linarith))).mp hs 
  
lemma has_subset_of_fincard {n : ℕ} (hnx : n ≤ fincard t) :
  ∃ s ⊆ t, fincard s = n :=
begin
  revert t, induction n with n ih, 
  {exact λ _ _, ⟨∅, empty_subset _, fincard_empty⟩}, 

  intros t ht, 
  have ht': 0 < fincard t := lt_of_lt_of_le (nat.zero_lt_succ _ ) ht, 
  
  obtain ⟨e,he⟩ := exists_mem_of_fincard_pos ht',  
  obtain ⟨s, hst, hs⟩ := @ih (t \ {e}) _, swap, 
  { rw ← nat.succ_le_succ_iff, 
    convert ht, 
    convert finite.fincard_remove_mem_add_one_eq (finite_of_fincard_pos ht') he}, 
  
  refine ⟨insert e s, _, _⟩, 
  { rw insert_subset, exact ⟨he, subset.trans hst (diff_subset _ _)⟩, },
  { convert finite.fincard_insert_nonmem _ _, 
      rw hs, 
      exact ((finite_of_fincard_pos ht').diff _).subset hst, 
    exact nonmem_of_nonmem_supset (nonmem_removal _ _) hst},
end

lemma has_set_of_fincard {n : ℕ} (h' : n ≤ nat.card α) :
  ∃ (Y : set α), fincard Y = n :=
by {rw nat_card_eq_fincard_univ at h', obtain ⟨Y,-,hY⟩ := has_subset_of_fincard h', tauto}
 
lemma has_subset_of_fincard_of_infinite {n : ℕ} (ht : t.infinite) :
  ∃ s ⊆ t, fincard s = n :=
begin
  revert n, 
  refine nat_induction _ ⟨∅, empty_subset _, fincard_empty⟩ _, 
  rintros n ⟨s, hs, hs'⟩, 
  by_cases hf : s.finite, 
  { obtain ⟨e, he⟩ := set.infinite.nonempty (set.infinite_of_finite_diff hf ht), 
    refine ⟨s ∪ {e}, union_singleton_subset_of_subset_mem hs (mem_of_mem_diff he), _⟩, 
    rw ← hs', refine finite.fincard_union_nonmem_singleton hf (not_mem_of_mem_diff he)},
  obtain ⟨e,he⟩ := set.infinite.nonempty ht, 
  refine ⟨{e}, singleton_subset_iff.mpr he, _⟩, 
  rw [fincard_singleton, ← hs', fincard_of_infinite hf], 
end

lemma has_distinct_mems_of_infinite (ht : t.infinite) : 
  ∃ e f ∈ t, e ≠ f := 
begin
  obtain ⟨s,hst, hs⟩ := has_subset_of_fincard_of_infinite  ht, 
  obtain ⟨e, f, hef, rfl⟩ := fincard_eq_two_iff_pair.mp hs, 
  refine ⟨e,f,_,_,hef⟩,
  { rw [← singleton_subset_iff], apply subset.trans (singleton_subset_pair_left _ _) hst},
  rw [← singleton_subset_iff], apply subset.trans (singleton_subset_pair_right _ _) hst,
end

end general 


/-!
This section (nearly) contains only copies of lemmas above, but with the finiteness assumptions
wrapped in a `fintype` instance, as well as a couple of lemmas about type fincards which need
`fintype` for the statement to even be sensible. All lemmas fail without finiteness, and 
nearly all are proved by just grabbing finiteness assumptions from the instance and invoking
the versions with explicit assumptions. 
-/

section fintype  

open set 

variables  [fintype α] [fintype β] 

lemma fincard_monotone (hst : s ⊆ t) : 
  fincard s ≤ fincard t :=
by {apply finite.fincard_monotone _ hst, apply finite.of_fintype, }

lemma fincard_le_nat_card (s : set α):
  fincard s ≤ nat.card α :=
by {convert fincard_monotone (subset_univ _),  rw nat_card_eq_fincard_univ, apply_instance }

lemma fincard_modular (s t : set α) : 
  fincard (s ∪ t) + fincard (s ∩ t) = fincard s + fincard t :=
by {apply finite.fincard_modular; apply finite.of_fintype, }

lemma fincard_add_compl_fincard (s : set α): 
  fincard s + fincard sᶜ = fincard (univ : set α) :=
by {simpa using (fincard_modular s sᶜ).symm}

lemma compl_fincard (s : set α) :
  (fincard sᶜ : ℤ) = fincard (univ : set α) - fincard s := 
by {linarith [fincard_add_compl_fincard s]}

lemma fincard_compl (s : set α) :
  (fincard s : ℤ) = fincard (univ : set α) - fincard sᶜ := 
by {linarith [fincard_add_compl_fincard s]}

lemma fincard_union (s t : set α) : 
  (fincard (s ∪ t) : ℤ) = fincard s + fincard t - fincard (s ∩ t) := 
by {apply finite.fincard_union; apply finite.of_fintype,}

lemma ssubset_fincard (hst : s ⊆ t) (hst' : fincard s < fincard t) :
  s ⊂ t := 
by {apply finite.ssubset_fincard _ _ hst hst'; apply finite.of_fintype,  }

lemma fincard_subadditive (s t : set α) : fincard (s ∪ t) ≤ fincard s + fincard t :=
by {apply finite.fincard_subadditive; apply finite.of_fintype }

lemma compl_inter_fincard (s t : set α) : fincard (s ∩ t) + fincard (sᶜ ∩ t) = fincard t := 
by {apply finite.compl_inter_fincard, apply finite.of_fintype,}

lemma compl_inter_fincard_subset (hst : s ⊆ t) : 
  (fincard (sᶜ ∩ t) : ℤ) = fincard t - fincard s := 
by {apply finite.compl_inter_fincard_subset _ hst, apply finite.of_fintype, }

lemma diff_fincard (hst : s ⊆ t) : (fincard (t \ s) : ℤ) = fincard t - fincard s :=  
by {apply finite.diff_fincard _ hst, apply finite.of_fintype }

lemma fincard_diff_le_fincard (s t : set α) : fincard (s \ t) ≤ fincard s := 
by {apply finite.fincard_diff_le_fincard, apply finite.of_fintype}

lemma fincard_union_of_inter_empty (hst : s ∩ t = ∅) : 
  fincard (s ∪ t) = fincard s + fincard t := 
by {apply finite.fincard_union_of_inter_empty _ _ hst ; apply finite.of_fintype}

lemma fincard_union_of_disjoint (hst : disjoint s t) : 
  fincard (s ∪ t) = fincard s + fincard t := 
by {apply finite.fincard_union_of_disjoint _ _ hst ; apply finite.of_fintype}

lemma fincard_modular_diff (s t : set α) : 
  fincard (s ∪ t) = fincard (s \ t) + fincard (t \ s) + fincard (s ∩ t) :=
by {apply finite.fincard_modular_diff; apply finite.of_fintype }

lemma fincard_induced_partition (s t : set α) :
  fincard s = fincard (s ∩ t) + fincard (s \ t) := 
by {apply finite.fincard_induced_partition, apply finite.of_fintype}

lemma fincard_induced_partition_inter (s t : set α) :
  fincard s = fincard (s ∩ t) + fincard (s ∩ tᶜ) := 
by {apply finite.fincard_induced_partition, apply finite.of_fintype}

lemma fincard_mono_inter_left (s t : set α) : fincard (s ∩ t) ≤ fincard s := 
by {apply finite.fincard_mono_inter_left, apply finite.of_fintype}

lemma fincard_mono_inter_right (s t : set α) : fincard (s ∩ t) ≤ fincard t := 
by {apply finite.fincard_mono_inter_right, apply finite.of_fintype}

lemma fincard_mono_union_left (s t : set α) : fincard s ≤ fincard (s ∪ t)  := 
by {apply finite.fincard_mono_union_left, apply finite.of_fintype}

lemma fincard_mono_union_right (s t : set α) : fincard t ≤ fincard (s ∪ t) := 
by {apply finite.fincard_mono_union_right, apply finite.of_fintype}

lemma empty_of_fincard_zero (hfincard : fincard s = 0) : s = ∅ := 
by {apply finite.empty_of_fincard_zero _ hfincard, apply finite.of_fintype, }

@[simp] lemma fincard_zero_iff_empty : (fincard s = 0) ↔ (s = ∅) := 
by {apply finite.fincard_zero_iff_empty, apply finite.of_fintype, }

@[simp] lemma fincard_le_zero_iff_eq_empty : fincard s ≤ 0 ↔ s = ∅ := 
by {apply finite.fincard_le_zero_iff_eq_empty, apply finite.of_fintype, }

lemma fincard_nonempty (hne : s.nonempty) : 0 < fincard s  := 
by {apply finite.fincard_nonempty _ hne, apply finite.of_fintype, }

lemma nonempty_iff_fincard_pos : s.nonempty ↔ 0 < fincard s := 
by {apply finite.nonempty_iff_fincard_pos, apply finite.of_fintype, }

lemma one_le_fincard_iff_nonempty : s.nonempty ↔ 1 ≤ fincard s := 
nonempty_iff_fincard_pos

lemma one_le_fincard_univ_of_nonempty (hα : nonempty α) : 1 ≤ fincard (univ : set α) := 
by rwa [nonempty_iff_univ_nonempty, one_le_fincard_iff_nonempty] at hα

lemma one_le_nat_card_of_nonempty (hα: nonempty α) : 1 ≤ nat.card α  := 
by {rw [nat_card_eq_fincard_univ], apply one_le_fincard_univ_of_nonempty hα}

lemma fincard_strict_monotone (hst : s ⊂ t) : fincard s < fincard t := 
by {apply finite.fincard_strict_monotone _ hst; apply finite.of_fintype }

lemma eq_of_eq_fincard_subset (hst : s ⊆ t) (hfincard : fincard s = fincard t) : s = t :=
by {apply finite.eq_of_eq_fincard_subset _ hst hfincard, apply finite.of_fintype }

lemma eq_of_eq_fincard_subset_iff (hst : s ⊆ t) : 
  ((fincard s = fincard t) ↔ s = t) :=
by {apply finite.eq_of_eq_fincard_subset_iff _ hst; apply finite.of_fintype }

lemma eq_of_le_fincard_subset (hst : s ⊆ t) (hfincard : fincard t ≤ fincard s) : 
  s = t :=
by {apply finite.eq_of_le_fincard_subset _ hst hfincard, apply finite.of_fintype }

lemma fincard_eq_of_supset (hst : s ⊆ t) (hfincard : fincard t ≤ fincard s) :
  fincard s = fincard t := 
by {apply finite.fincard_eq_of_supset _ hst hfincard, apply finite.of_fintype }

lemma fincard_pos_iff_has_mem : 
  0 < fincard s ↔ ∃ e, e ∈ s := 
by rw [← nonempty_iff_fincard_pos, set.nonempty_def] 

lemma one_le_fincard_iff_has_mem : 
  1 ≤ fincard s ↔ ∃ e, e ∈ s := 
by {convert fincard_pos_iff_has_mem, apply_instance}

lemma fincard_zero_iff_has_no_mem :
  fincard s = 0 ↔ ¬ ∃ e, e ∈ s := 
by {rw finite.fincard_zero_iff_has_no_mem, apply finite.of_fintype}

lemma fincard_le_zero_iff_has_no_mem :
  fincard s ≤ 0 ↔ ¬ ∃ e, e ∈ s := 
by {rw finite.fincard_le_zero_iff_has_no_mem, apply finite.of_fintype}

lemma mem_diff_of_fincard_lt (h : fincard s < fincard t) :
  ∃ (e : α), e ∈ t ∧ e ∉ s :=
by {apply finite.mem_diff_of_fincard_lt _ h, apply finite.of_fintype}

lemma fincard_union_singleton_compl (he : e ∈ sᶜ) :
  fincard (s ∪ {e}) = fincard s + 1 := 
by {apply finite.fincard_union_singleton_compl _ he, apply finite.of_fintype}

lemma fincard_union_nonmem_singleton (hes : e ∉ s) : 
  fincard (s ∪ {e}) = fincard s + 1 := 
by {apply finite.fincard_union_singleton_compl _ hes, apply finite.of_fintype}

lemma fincard_remove_mem_add_one_eq (he : e ∈ s): 
  fincard (s \ {e}) + 1 = fincard s := 
finite.fincard_remove_mem_add_one_eq (finite.of_fintype _) he

lemma fincard_remove_mem (he : e ∈ s) :
  (fincard (s \ {e}) : ℤ) = fincard s - 1 := 
by {apply finite.fincard_remove_mem _ he, apply finite.of_fintype}

lemma fincard_insert_nonmem (he : e ∉ s): 
  fincard (has_insert.insert e s) = fincard s + 1 := 
by {apply finite.fincard_insert_nonmem _ he, apply finite.of_fintype, }

lemma has_sub_one_fincard_ssubset_of_ne_empty (hne : s ≠ ∅) :
  ∃ t, t ⊂ s ∧ (fincard t : ℤ) = fincard s - 1 := 
by {apply finite.has_sub_one_fincard_ssubset_of_ne_empty _ hne, apply finite.of_fintype}

lemma has_sub_one_fincard_ssubset_of_nonempty (hne : s.nonempty) :
  ∃ t, t ⊂ s ∧ (fincard t : ℤ) = fincard s - 1 := 
by {apply finite.has_sub_one_fincard_ssubset_of_nonempty _ hne, apply finite.of_fintype}

lemma ne_univ_has_add_one_fincard_ssupset (hne : s ≠ univ) :
  ∃ t, s ⊂ t ∧ fincard t = fincard s + 1 := 
by {apply finite.ne_univ_has_add_one_fincard_ssupset _ hne, apply finite.of_fintype}

lemma ne_univ_has_add_one_fincard_ssupset_element (hne : s ≠ univ) :
  ∃ e, s ⊂ s ∪ {e} ∧ fincard (s ∪ {e}) = fincard s + 1 := 
by {apply finite.ne_univ_has_add_one_fincard_ssupset_element _ hne, apply finite.of_fintype}   

lemma eq_or_exists_mem_diff_of_fincard_eq (hst : fincard s = fincard t) :
  s = t ∨ ∃ e, e ∈ s \ t :=
by {apply finite.eq_or_exists_mem_diff_of_fincard_eq _ hst, apply finite.of_fintype}

lemma fincard_le_one_iff_empty_or_singleton :
  fincard s ≤ 1 ↔ s = ∅ ∨ ∃ e, s = {e} :=
by {apply finite.fincard_le_one_iff_empty_or_singleton, apply finite.of_fintype,}

lemma fincard_le_one_iff_mem_unique : 
  fincard s ≤ 1 ↔ ∀ e f ∈ s, e = f := 
by {apply finite.fincard_le_one_iff_mem_unique, apply finite.of_fintype}

lemma fincard_sUnion {k : set (set α)} (hdisj : pairwise_disjoint k) : 
  fincard (⋃₀ k) = ∑ᶠ s in k, fincard s := 
by {apply finite.fincard_sUnion _ (λ b hb, _) hdisj; apply finite.of_fintype, } 

lemma fincard_Union {t : β → set α} (h : ∀ x y, x ≠ y → disjoint (t x) (t y)) :
  fincard (⋃ x : β, t x) = ∑ᶠ i, (fincard (t i)) :=
by {simp_rw [← finsum_ones_eq_fincard], apply fin.finsum_in_Union h, }

lemma fincard_bUnion {t : β → set α} {b : set β} (h : ∀ x y ∈ b, x ≠ y → disjoint (t x) (t y)):  
  fincard (⋃ (x : β) (H : x ∈ b), t x) = ∑ᶠ i in b, fincard (t i) :=
begin
  rw [← finsum_subtype_eq_finsum_in, ← fincard_Union], simp,  
  rintros ⟨x,hx⟩ ⟨y,hy⟩ hxy, 
  refine h x y hx hy _,
  simpa using hxy, 
end

lemma eq_univ_of_fincard_eq_nat_card (hs : fincard s = nat.card α) : s = univ :=
begin
  rw [← finsum_ones_eq_fincard, ← finsum_ones_eq_nat_card, finsum_eq_finsum_in_univ] at hs, 
  have h := fin.eq_zero_of_finsum_in_subset_eq_finsum_in_of_nonneg (subset_univ s) _ hs.symm.le,
  swap, norm_num, 
  simp only [one_ne_zero, univ_diff, mem_compl_eq, imp_false, not_not] at h, 
  ext, 
  tauto,
end

variables {k : set (set α)}

lemma fincard_collection_le_fincard_union (hk : ∀ s ∈ k, set.nonempty s) (hdisj : pairwise_disjoint k): 
  (fincard k ≤ fincard (⋃₀ k)) := 
finite.fincard_collection_le_fincard_union (λ _ _, finite.of_fintype _) hk hdisj

lemma singletons_of_fincard_collection_eq_fincard_union (hk : ∀ s ∈ k, set.nonempty s) 
(hdisj : pairwise_disjoint k) (hfincard : fincard k = fincard (⋃₀ k)): 
  ∀ s ∈ k, fincard s = 1 :=
by apply finite.singletons_of_fincard_collection_eq_fincard_union _ (λ _ _, _) hk hdisj hfincard;
   apply finite.of_fintype 

lemma fincard_collection_eq_fincard_union_iff 
(hk : ∀ s ∈ k, set.nonempty s) (hdisj : pairwise_disjoint k): 
  fincard k = fincard (⋃₀ k) ↔ ∀ s ∈ k, fincard s = 1 := 
by apply finite.fincard_collection_eq_fincard_union_iff _ (λ _ _, _) hk hdisj; apply finite.of_fintype

lemma fincard_disjoint_collection_le_nat_card {k : set (set α)} (hk' : ∀ s ∈ k, set.nonempty s)
(hdisj : pairwise_disjoint k): 
  fincard k ≤ nat.card α :=
le_trans (fincard_collection_le_fincard_union hk' hdisj) (fincard_le_nat_card _)

lemma fincard_disjoint_collection_eq_nat_card_iff (hk : ∀ s ∈ k, set.nonempty s)
(hdisj : pairwise_disjoint k): 
  fincard k = nat.card α ↔ ⋃₀ k = univ ∧ ∀ s ∈ k, fincard s = 1 := 
begin
  refine ⟨λ h, _, λ h, _⟩,  
  {  obtain ⟨h₁, h₂⟩ := squeeze_le_trans 
      (fincard_collection_le_fincard_union hk hdisj) 
      (fincard_le_nat_card _) 
      h, 
    exact ⟨eq_univ_of_fincard_eq_nat_card h₂, 
            singletons_of_fincard_collection_eq_fincard_union hk hdisj h₁⟩},
  rw [(fincard_collection_eq_fincard_union_iff hk hdisj).mpr h.2, h.1, nat_card_eq_fincard_univ], 
end

end fintype 


section embeddings

theorem fincard_preimage_eq_sum' (f : α → β){s : set α} {t : set β}
(hs : s.finite) (ht : t.finite) :
fincard (s ∩ f⁻¹' t) = ∑ᶠ y in t, fincard {x ∈ s | f x = y} := 
begin
  simp_rw fincard, 
  have := @finsum_in_bUnion α ℕ _ β (λ _, 1) t (λ y, {x ∈ s | f x = y}) ht _ _, rotate, 
  { intro b, apply set.finite.subset hs, intros x hx, simp only [mem_sep_eq] at hx, exact hx.1},
  { rintro x hx y hy hxy, 
    simp only [disjoint_left, and_imp, mem_sep_eq, not_and], 
    rintros a ha rfl - rfl, exact hxy rfl},
  convert this, {ext, simp, tauto}, 
end

theorem fincard_preimage_eq_sum (f : α → β){t : set β}
(ht : t.finite) (ht' : (f ⁻¹' t).finite) :
fincard (f⁻¹' t) = ∑ᶠ y in t, fincard {x | f x = y} := 
begin
  have := fincard_preimage_eq_sum' f ht' ht, rw inter_self at this,  
  rw [this, finsum_in_def, finsum_in_def], congr', ext, 
  split_ifs, swap, refl, 
  convert fincard_image_emb (function.embedding.refl α) _, 
  ext, simp, rintro rfl, assumption,  
end

lemma fincard_image_inj {f : α → β} (hf : function.injective f) (s : set α) : 
  fincard (f '' s) = fincard s := 
fincard_image_emb ⟨f , hf⟩ s

lemma fincard_image_equiv (f : α ≃ β) (s : set α) :
  fincard (f '' s) = fincard s :=
fincard_image_emb (f.to_embedding) s 

lemma fincard_range_emb (f : α ↪ β):
  fincard (range f) = nat.card α :=
by rw [← image_univ, fincard_image_emb, nat_card_eq_fincard_univ]

lemma fincard_range_inj (f : α → β)(hf : function.injective f):
  fincard (range f) = nat.card α :=
by rw [← image_univ, fincard_image_inj hf, nat_card_eq_fincard_univ]

lemma nat_card_eq_nat_card_equiv (f : α ≃ β) : 
  nat.card α = nat.card β := 
by rw [nat_card_eq_fincard_univ, nat_card_eq_fincard_univ, 
      ← fincard_image_equiv f, ← f.range_eq_univ, image_univ]

lemma nat_card_eq_iff_equiv [fintype α] [fintype β]: 
  nat.card α = nat.card β ↔ nonempty (α ≃ β) :=
by simp_rw [nat.card_eq_fintype_card, fintype.card_eq]
  
/-- Gives an equivalence between two types of equal fincard -/
def equiv_of_nat_card_eq [fintype α] [fintype β] (h : nat.card α = nat.card β ): α ≃ β :=
classical.choice (nat_card_eq_iff_equiv.mp h)

@[simp] lemma equiv.image_mem_image_iff_mem {f : α ≃ β} {x : α} {s : set α} : 
  f x ∈ f '' s ↔ x ∈ s := 
begin
  rw mem_image, split, 
  { rintros ⟨y, hy, hyx⟩, rw equiv.apply_eq_iff_eq at hyx, rwa ←hyx},
  exact λ hx, ⟨x, hx, rfl⟩, 
end

@[simp] lemma fincard_preimage_equiv (f : α ≃ β) (s : set β) :
  fincard (f ⁻¹' s) = fincard s :=
begin
  unfold_coes, 
  rw ←set.image_eq_preimage_of_inverse f.right_inv f.left_inv, 
  convert fincard_image_emb (f.symm.to_embedding) s, 
end

lemma fincard_preimage_embed_subset_range (f : α ↪ β) (s : set β) (hs : s ⊆ range f) : 
  fincard (f ⁻¹' s) = fincard s := 
begin
  suffices h: f '' (f ⁻¹' s) = s, 
  { rw eq_comm, nth_rewrite 0 ← h, apply fincard_image_emb}, 
  apply image_preimage_eq_of_subset hs, 
end 

lemma fincard_subtype_image {E : set α} (s : set E) : 
  fincard (subtype.val '' s) = fincard s :=
begin
  let f : E ↪ α := ⟨subtype.val, λ x y hxy, 
    by {cases x, cases y, simp only [subtype.mk_eq_mk], exact hxy}⟩, 
  apply fincard_image_emb f, 
end

@[simp] lemma fincard_image_coe {E : set α} (s : set E) : 
  fincard (coe '' s : set α) = fincard s := 
fincard_subtype_image s 

@[simp] lemma fincard_preimage_coe {E : set α} (s : set α) : 
  fincard (coe ⁻¹' s : set E) = fincard (s ∩ E) := 
by {rw ← fincard_image_coe (coe ⁻¹' s : set E), simp, }

@[simp] lemma nat_card_fin (n : ℕ) :
  nat.card (fin n) = n := 
by simp [nat.card_eq_fintype_card]

lemma nat_card_eq_iff_fin_equiv [fintype α] {n : ℕ} : 
  nat.card α = n ↔ nonempty (α ≃ fin n) := 
by {nth_rewrite 0 ← nat_card_fin n, apply nat_card_eq_iff_equiv} 

lemma equiv_fin_nat_card [fintype α]: 
  nonempty (α ≃ fin (nat.card α)) := 
nat_card_eq_iff_fin_equiv.mp rfl 

lemma fin_equiv (α : Type*) [fintype α]: 
  nonempty (α ≃ fin (nat.card α)) :=
nat_card_eq_iff_equiv.mp (by simp)

lemma nat_card_le_nat_card_inj [fintype β] (f : α ↪ β) : 
  nat.card α ≤ nat.card β := 
begin
  rw [nat_card_eq_fincard_univ, nat_card_eq_fincard_univ, ← fincard_image_emb f], 
  refine fincard_monotone (subset_univ _),
end 


lemma finite.embedding_inf {α β : Type*} [fintype α] [infinite β] : 
  nonempty (α ↪ β) := 
begin
  obtain ⟨e₁⟩ := fin_equiv α, 
  obtain e₂ : fin (nat.card α) ↪ ℕ := ⟨λ x, x.1, λ x y h, by {cases x, cases y, simpa using h}⟩,
  exact ⟨(e₁.to_embedding.trans e₂).trans (infinite.nat_embedding β)⟩,  
end

lemma exists_emb_of_fincard_le_fincard {α β : Type*} [fintype α] : 
  nat.card α ≤ nat.card β → nonempty (α ↪ β) := 
begin
  intro h, 
  obtain ⟨f₁⟩ := fin_equiv α, 
  by_cases hβ : nonempty (fintype β), 
  { obtain ⟨f⟩ := hβ, letI := f, 
    obtain ⟨f₂⟩  := fin_equiv β, 
    let e : fin (nat.card α) ↪ fin (nat.card β) := 
      ⟨λ x, ⟨x.1, lt_of_lt_of_le x.2 h⟩, λ x y h, by {cases x, cases y, simpa using h}⟩,  
    exact ⟨(f₁.to_embedding.trans e).trans (f₂.symm.to_embedding)⟩}, 
  exact @finite.embedding_inf _ _ _ (by simpa using hβ), 
end

lemma nat_card_le_iff_emb {α β : Type*} [fintype α] [fintype β] : 
  nat.card α ≤ nat.card β ↔ nonempty (α ↪ β) := 
begin
  refine ⟨exists_emb_of_fincard_le_fincard, λ h, _⟩, swap, 
  { obtain ⟨f⟩ := h, 
    rw [← fincard_range_emb f, nat_card_eq_fincard_univ], 
    exact fincard_monotone (subset_univ _) },
end

/-- chooses a bijection between α and fin (fincard α) -/
def choose_fin_bij [fintype α]: 
  α ≃ fin (nat.card α) :=
classical.choice equiv_fin_nat_card 


/-! This section covers the relationship between fincard and functions between sets (mostly embeddings
and bijections) . -/


lemma nonempty_fin_emb_of_nat_card {n : ℕ} (hα : n ≤ nat.card α) : 
  nonempty ((fin n) ↪ α) := 
begin
  cases n, { exact ⟨⟨λ x, fin_zero_elim x, λ x, fin_zero_elim x⟩⟩},
  haveI := fintype_of_nat_card_pos (lt_of_le_of_lt (nat.zero_le _) (nat.succ_le_iff.mp hα)), 
  rw ←nat_card_le_iff_emb, convert hα, simp, 
end

/-- an embedding from `fin' n` into `α`, provided that `n ≤ nat.card α` -/
def choose_fin'_inj_of_nat_card {n : ℕ} (hα : n ≤ nat.card α) :
  (fin n) ↪ α :=
classical.choice (nonempty_fin_emb_of_nat_card hα)

lemma exists_emb_of_nat_card_le_fincard_set {α : Type*} [fintype α] {β : Type*} {s : set β} 
(hfincard : nat.card α ≤ fincard s ) : 
  ∃ (emb : α ↪ β), set.range emb ⊆ s := 
begin
  rw ← nat_card_coe_set_eq_fincard at hfincard, 
  obtain ⟨emb⟩ := exists_emb_of_fincard_le_fincard hfincard, 
  exact ⟨emb.trans ⟨subtype.val, subtype.val_injective ⟩, λ x, by tidy⟩, 
end

lemma set.finite.exists_emb_of_nat_card_eq_fincard_set {α : Type*} [fintype α] {β : Type*} 
{s : set β} (hs : s.finite) (hfincard : nat.card α = fincard s ) : 
  ∃ (emb : α ↪ β), set.range emb = s := 
begin
  convert exists_emb_of_nat_card_le_fincard_set (le_of_eq hfincard), 
  ext emb, 
  split, 
  { unfreezingI {rintro rfl}, exact subset_refl _, }, 
  intros hss, 
  apply set.finite.eq_of_eq_fincard_subset hs hss,
  rw [← image_univ, fincard_image_emb],  
  convert hfincard, 
  rw nat_card_eq_fincard_univ, 
end

lemma exists_emb_of_nat_card_eq_fincard_set {α : Type*} [fintype α] {β : Type*} [fintype β]
{s : set β} (hfincard : nat.card α = fincard s ) : 
  ∃ (emb : α ↪ β), set.range emb = s := 
by {apply set.finite.exists_emb_of_nat_card_eq_fincard_set _ hfincard, apply finite.of_fintype }

lemma nat_card_lt_of_nonmem_range_emb {α β : Type* } [fintype β] (emb : α ↪ β) {b : β}
(hb : b ∉ range emb): 
  nat.card α < nat.card β :=
begin
  refine lt_of_le_of_ne (by { rw [← fincard_range_emb emb], apply fincard_le_nat_card, }) (λ h, _),
  letI : fintype α := fintype.of_injective _ (emb.injective), 
  let eq := equiv_of_nat_card_eq h.symm, 
  have h' := fincard_image_equiv eq (has_insert.insert b (range emb)), 
  rw [fincard_insert_nonmem hb, fincard_range_emb] at h', 
  linarith [fincard_le_nat_card (eq '' insert b (range ⇑emb))], 
end

lemma nat_card_lt_iff_exists_proper_emb {α β : Type*} [fintype α] [fintype β] : 
  nat.card α < nat.card β ↔ ∃ (emb : α ↪ β) (b : β), b ∉ range emb := 
begin
  refine ⟨λ h, _, λ ⟨emb, b, hb⟩, nat_card_lt_of_nonmem_range_emb emb hb⟩,
  obtain ⟨emb⟩ := nat_card_le_iff_emb.mp (le_of_lt h), 
  refine ⟨emb, compl_nonempty_iff_exists_nonmem.mp (compl_nonempty_of_fincard_lt_nat_card _)⟩,
  rwa fincard_range_emb, 
end

end embeddings 

section sums 


@[simp] lemma int.finsum_const_eq_mul_nat_card (α : Type*) (b : ℕ) :
  ∑ᶠ (x : α), b = b * nat.card α := 
by rw [← mul_one b, ← finsum_ones_eq_nat_card, ← mul_distrib_finsum, mul_one]

@[simp] lemma int.finsum_in_const_eq_mul_fincard (s : set α) (b : ℕ) :
  ∑ᶠ x in s, b = b * fincard s := 
by rw [← mul_one b, ← finsum_ones_eq_fincard, ← mul_distrib_finsum_in, mul_one]

lemma finite.sum_fincard_fiber_eq_fincard {s : set α} (f : α → β)
(hs : s.finite) : 
∑ᶠ (b : β), fincard {a ∈ s | f a = b} = fincard s := 
begin
  set t := f '' s with ht, 
  have hs' : s = s ∩ f ⁻¹' t, 
  { rw [eq_comm, ← set.subset_iff_inter_eq_left, ht], exact subset_preimage_image f s,  },
  rw [eq_comm, hs', fincard_preimage_eq_sum' _ hs (finite.image _ hs), finsum_eq_finsum_in_subset], 
  { convert rfl, ext, congr', rw ← hs', }, 
  intro x, 
  rw [fincard_eq_zero_iff_empty, mem_image], swap, 
  { apply set.finite.subset hs, intro y, rw mem_sep_eq, exact λ h, h.1 },
  intro hx, ext y, 
  rw [mem_sep_eq, mem_empty_eq], 
  exact ⟨λ h, hx ⟨y,h⟩, λ h, false.elim h⟩, 
end

lemma sum_fincard_fiber_eq_fincard [fintype α] {ι : Type*} (s : set α) (f : α → ι) :
  ∑ᶠ (i : ι), fincard {a ∈ s | f a = i} = fincard s := 
by {rw [finite.sum_fincard_fiber_eq_fincard f], apply finite.of_fintype}

lemma fincard_set_subtype_eq_fincard_set (P Q : α → Prop) :
  fincard {x : {y // P y} | Q (coe x)} = fincard { x | P x ∧ Q x } := 
by {simp_rw ← finsum_ones_eq_fincard, apply finsum_set_subtype_eq_finsum_set (1 : α → ℕ)} 

end sums 



section incl_excl 
  
variables {M : Type*} [add_comm_group M]

def signed_convolution (f : set α → M) (s : set α) : M :=
  ∑ᶠ a in s.powerset, ((-1)^(fincard a)) •ℤ (f a)

lemma twice {f : set α → M} {s : set α} (hs : s.finite): 
  signed_convolution (signed_convolution f) s = f s:=
begin
 
  unfold signed_convolution, 
  have hs' : s.powerset.finite := set.finite.finite_subsets hs,
  have ha_fin : ∀ (a : set α), a ∈ s.powerset → a.powerset.finite, 
    from λ a ha, hs'.subset (set.powerset_mono.mpr ha), 
  convert @finsum_in_eq_of_eq _ _ _ _ _ _ 
    (λ (a : set α) ha, @gsmul_distrib_finsum_in _ _ _ 
      (λ x, ((-1)^(fincard x)) •ℤ (f x)) 
      (a.powerset) 
      ((-1)^(fincard a)) 
      (set.finite.subset (ha_fin _ ha) (inter_subset_left _ _))), 
  
  rw finsum_comm_dep, rotate, 
  { apply hs'.subset, rintros x ⟨hx, hx'⟩, assumption},
  { exact λ a ha, set.finite.subset (ha_fin _ ha) (inter_subset_left _ _)},

  convert (finsum_ite_singleton_eq s).symm, 
  funext, 
  split_ifs with h, 
  { convert (finsum_ite_singleton_eq y), 
    { change _ = {y}, ext x, simp [h, subset.antisymm_iff]}, 
    simp only [←gsmul_mul,  ← pow_add, ← two_mul, nat.neg_one_pow_of_even ⟨_,rfl⟩, one_gsmul]}, 

  by_cases hsy : s ⊆ y, 
  { convert finsum_in_empty, 
    ext, 
    simp only [mem_sep_eq, mem_empty_eq, not_and, mem_powerset_iff, iff_false], 
    exact λ hxs hyx, h (subset.antisymm (subset.trans hyx hxs) hsy)},

  rw [subset_def] at hsy, push_neg at hsy, 
  obtain ⟨e, hes, hey⟩ := hsy, 

  apply finsum_in_involution (λ (x : set α), x.symm_diff {e}), 
  { rintros a ⟨has, hya⟩, 
    rw ←  add_gsmul, 
    convert zero_gsmul _,
    apply nat.neg_one_pow_sum_eq_zero_of_sum_odd,    
    rw [← zmod.eq_one_iff_odd, nat.cast_add, 
      set.finite.fincard_symm_diff_mod2 (hs.subset has) (set.finite_singleton _), 
      add_comm, ← add_assoc, ← two_mul], 
    convert zero_add _, 
      convert zero_mul _, 
    simp},
  { exact λ a ⟨has, hya⟩, ⟨subset.trans (symm_diff_subset_union _ _) 
                                        (union_subset has (singleton_subset_iff.mpr hes)), 
                           subset.trans (subset_diff_singleton hya hey)
                                        (diff_subset_symm_diff _ _ )⟩},
  { simp},
  refine λ a _ ha, false.elim _,
  simp only [symm_diff_eq_self_iff] at ha, 
  exact singleton_ne_empty _ ha, 
end

end incl_excl 
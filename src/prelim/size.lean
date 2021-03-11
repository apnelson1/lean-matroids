
import tactic 
import .int_lemmas .set .single finsum.fin_api

open_locale classical big_operators 
noncomputable theory 

universes u v w 

/-!

This file contains an API for 'size', which is the noncomputable function assigning each finite
set to its size, and each infinite set to zero. Also type_size is defined similarly for types. 
Most lemmas are only true in a finite setting, and have two versions, one with explicit finiteness
assumptions, and one in which they are derived from a `fintype` instance . Lemmas of the former
type are usually less useful for us, and go in the `finite` namespace. 
-/


section defs 

/-- The size of a set, as an integer. Zero if the set is infinite -/
def size {α : Type u}(s : set α) : ℤ := (fincard s)

/-- The size of a type, as an integer. Zero if the type is infinite -/
def type_size (α : Type u ) : ℤ := size (set.univ : set α)

end defs 

/-! Basic lemmas about size. In particular those that don't need fintype   -/

section basic 

variable {α : Type u}

lemma size_def {α : Type u}(s : set α): 
  size s = fincard s := 
rfl 

lemma type_size_eq (α : Type u): type_size α = size (set.univ : set α) := rfl 

lemma type_size_eq_fincard_t (α : Type u): type_size α = fincard_t α := 
by {rw [type_size, size_def], norm_num, refl,  }

@[simp] lemma size_empty (α : Type u) : size (∅ : set α) = 0 := 
by simp [size]

@[simp] lemma size_singleton (e : α) : size ({e}: set α) = 1 := 
by simp [size]

lemma size_nonneg (s : set α) : 0 ≤ size s := 
by {simp only [size], norm_cast, apply zero_le}  

lemma type_size_nonneg (α : Type u) : 0 ≤ type_size α := 
size_nonneg _

lemma size_zero_of_infinite {s : set α}(hs : s.infinite): 
  size s = 0 := 
by rw [size, fincard_of_infinite hs, int.coe_nat_zero]

lemma finite_of_size_pos {s : set α}(hs : 0 < size s): 
  s.finite := 
by {rw size at hs, norm_num at hs, exact finite_of_fincard_pos hs, }

lemma nonempty_of_size_pos {s : set α} (hs : 0 < size s):
  s.nonempty := 
by {rw ← set.ne_empty_iff_nonempty, rintro rfl, linarith [size_empty α], }

lemma contains_singleton {s : set α}: s.nonempty → (∃ t, t ⊆ s ∧ size t = 1) :=
λ ⟨e,he⟩, ⟨{e},⟨set.singleton_subset_iff.mpr he, size_singleton e⟩⟩


lemma single_subset' {s : set α} (hs : s.nonempty) : 
  (∃ t t', t ∩ t' = ∅ ∧ t ∪ t' = s ∧ size t = 1) := 
begin
  obtain ⟨t,ht⟩ := contains_singleton hs,
  refine ⟨t, s \ t, set.inter_diff _ _,  _, ht.2⟩, 
  rw [set.union_diff_self, set.subset_iff_union_eq_left.mp ht.1], 
end

lemma single_subset {s : set α} (hs : s.nonempty) : 
  (∃ t t', disjoint t t' ∧ t ∪ t' = s ∧ size t = 1) := 
by {simp_rw set.disjoint_iff_inter_eq_empty, exact single_subset' hs}

lemma size_pos_has_mem {s : set α}: 
  0 < size s → ∃ e, e ∈ s := 
λ h, (ne_empty_iff_has_mem.mp (λ hs, lt_irrefl _ (by {rwa [hs, size_empty] at h})))


end basic 

/-! Lemmas about the relationship between size and finsumming ones -/

section sums 

variables {α : Type u}

@[simp] lemma finsum_ones_eq_size (s : set α) : 
  ∑ᶠ x in s, (1 : ℤ) = size s := 
by {rw [size, fincard, nat.coe_int_distrib_finsum_in], refl}

@[simp] lemma finsum_ones_eq_type_size (α : Type u) : 
  ∑ᶠ (x : α), (1 : ℤ) = type_size α := 
by {rw [finsum_eq_finsum_in_univ, finsum_ones_eq_size], refl}

@[simp] lemma int.finsum_const_eq_mul_type_size (α : Type u) (b : ℤ):
  ∑ᶠ (x : α), b = b * type_size α := 
by rw [← mul_one b, ← finsum_ones_eq_type_size, ← mul_distrib_finsum, mul_one]

@[simp] lemma int.finsum_in_const_eq_mul_size (s : set α) (b : ℤ):
  ∑ᶠ x in s, b = b * size s := 
by rw [← mul_one b, ← finsum_ones_eq_size, ← mul_distrib_finsum_in, mul_one]

lemma sum_size_fiber_eq_size {ι : Type} [fintype α] (s : set α) (f : α → ι):
  ∑ᶠ (i : ι), size {a ∈ s | f a = i} = size s := 
by simp_rw [size_def, ← nat.coe_int_distrib_finsum, fin.sum_fincard_fiber_eq_fincard s f]

lemma finite.sum_size_fiber_eq_size {ι : Type} {s : set α} (hs : s.finite) (f : α → ι):
  ∑ᶠ (i : ι), size {a ∈ s | f a = i} = size s := 
by simp_rw [size_def, ← nat.coe_int_distrib_finsum, sum_fincard_fiber_eq_fincard f hs]

lemma size_set_subtype_eq_size_set (P Q : α → Prop):
  size {x : {y // P y} | Q (coe x)} = size { x | P x ∧ Q x } := 
by {simp_rw ← finsum_ones_eq_size, apply finsum_set_subtype_eq_finsum_set (1 : α → ℤ)} 

end sums 

/-! This section deals with fin', an analogue of fin that is defined for all n; it is 
an empty type whenever `n ≤ 0`. -/


section fin'

/-- the same as fin, but defined for all integers (empty if `n < 0`)-/
def fin' (n : ℤ) := fin (n.to_nat)

lemma fin'_eq_fin {n : ℕ}:
  fin' n = fin n := 
rfl 

lemma fin'_neg_elim {n : ℤ}(hn : n < 0)(x : fin' n): 
  false :=
by {cases x with x hx, rw int.to_nat_zero_of_neg hn at hx, exact nat.not_lt_zero _ hx,  }

lemma fin'_le_zero_elim {n : ℤ}(hn : n ≤ 0)(x : fin' n): 
  false :=
begin
  cases x with x hx,
  rcases eq_or_lt_of_le hn with (rfl | hn), 
  { exact nat.not_lt_zero _ hx, },
  rw int.to_nat_zero_of_neg hn at hx, 
  exact nat.not_lt_zero _ hx,
end 

instance {n : ℤ}: fintype (fin' n) := by {unfold fin', apply_instance}

@[simp] lemma size_fin (n : ℕ): 
  type_size (fin n) = n := 
by {rw [type_size_eq_fincard_t], norm_num}

@[simp] lemma size_fin' (n : ℤ)(hn : 0 ≤ n): 
  type_size (fin' n) = n := 
by {convert size_fin (n.to_nat), exact (int.to_nat_of_nonneg hn).symm}

@[simp] lemma size_fin'_univ (n : ℤ)(hn : 0 ≤ n): 
  size (set.univ : set (fin' n)) = n := 
by {convert size_fin (n.to_nat), exact (int.to_nat_of_nonneg hn).symm}

lemma type_size_eq_iff_equiv_fin' {α : Type} [fintype α] {n : ℤ} (hn : 0 ≤ n): 
  type_size α = n ↔ nonempty (equiv α (fin' n)) :=
begin
  obtain ⟨m,rfl⟩ := int.eq_coe_of_zero_le hn, 
  rw [fin'_eq_fin, ← fincard_t_eq_iff_fin_equiv, type_size_eq_fincard_t, int.coe_nat_inj'],
end

def choose_equiv_to_fin {α : Type} [fintype α] :
  equiv α (fin' (type_size α)) :=
classical.choice ((type_size_eq_iff_equiv_fin' (type_size_nonneg α)).mp rfl)

end fin' 

section finite

namespace set.finite

open set 

variables {α : Type u}{s t : set α}{e f : α}

lemma of_diff (hs : s.finite) (t : set α): (s \ t).finite :=  
  set.finite.subset hs (diff_subset _ _)

lemma of_inter_left (hs : s.finite) (t : set α): (s ∩ t).finite := 
  set.finite.subset hs (inter_subset_left _ _)

lemma of_inter_right (ht : t.finite) (s : set α ) : (s ∩ t).finite := 
  set.finite.subset ht (inter_subset_right _ _)

lemma size_modular (s t : set α)(hs : s.finite)(ht : t.finite): 
  size (s ∪ t) + size (s ∩ t) = size s + size t :=
by {simp_rw size, norm_cast, apply fincard_modular; assumption} 

lemma size_union (s t : set α)(hs : s.finite)(ht : t.finite): 
  size (s ∪ t) = size s + size t - size (s ∩ t) := 
by linarith [size_modular s t hs ht]

lemma size_monotone (ht : t.finite) (hst : s ⊆ t) : size s ≤ size t := 
begin
  have hs := subset ht hst, 
  have := size_modular s (t \ s) hs (of_diff ht s), 
  rw [union_diff_of_subset hst, inter_diff] at this, 
  linarith [size_nonneg (t \ s), size_empty α],
end 

lemma ssubset_size (hs : s.finite) (ht : t.finite) (hst : s ⊆ t) (hst' : size s < size t) :
  s ⊂ t := 
by {rw set.ssubset_iff_subset_ne, from ⟨hst, λ hn, by {rw hn at hst', exact lt_irrefl _ hst'}⟩}

lemma size_subadditive (hs : s.finite) (ht : t.finite) : size (s ∪ t) ≤ size s + size t :=
  by linarith [size_modular s t hs ht, size_nonneg (s ∩ t)] 

lemma compl_inter_size (s t : set α) (ht : t.finite): 
  size (s ∩ t) + size (sᶜ ∩ t) = size t := 
by {rw [←size_modular, ←inter_distrib_right, union_compl_self, univ_inter, 
  ←inter_distrib_inter_left, inter_compl_self, empty_inter, size_empty, add_zero];
  exact of_inter_right (by assumption) _, }

lemma compl_inter_size_subset (ht : t.finite) (hst : s ⊆ t): 
  size (sᶜ ∩ t) = size t - size s := 
by {have := compl_inter_size s t ht, rw subset_iff_inter_eq_left.mp hst at this, linarith} 

lemma diff_size (ht : t.finite) (hst : s ⊆ t) : size (t \ s) = size t - size s :=  
by rw [diff_eq, inter_comm, compl_inter_size_subset ht hst]

lemma size_diff_le_size (s t : set α) (hs : s.finite) : size (s \ t) ≤ size s := 
  size_monotone hs (diff_subset _ _) 
-- the above lemma is also true if just `s ∩ t` is finite 

lemma size_union_of_inter_empty (hs : s.finite) (ht : t.finite) (hst : s ∩ t = ∅) :
  size (s ∪ t) = size s + size t := 
by {have := size_modular s t hs ht, rw [hst, size_empty] at this, linarith}

lemma size_union_of_disjoint (hs : s.finite) (ht : t.finite) (hst : disjoint s t) :
  size (s ∪ t) = size s + size t := 
size_union_of_inter_empty hs ht (disjoint_iff_inter_eq_empty.mp hst)

lemma size_modular_diff (s t : set α) (hs : s.finite) (ht : t.finite): 
  size (s ∪ t) = size (s \ t) + size (t \ s) + size (s ∩ t) :=
begin
  rw [←size_union_of_inter_empty _ _ (inter_diffs_eq_empty s t)],
  { have := (symm_diff_alt s t), 
    unfold symm_diff at this,
    rw this, 
    linarith [diff_size (union hs ht) (inter_subset_union s t)]}, 
  repeat {apply of_diff, assumption}, 
end

lemma size_induced_partition (hs : s.finite) (s t : set α) :
  size s = size (s ∩ t) + size (s \ t) := 
begin
  nth_rewrite 0 ←diff_union s t, 
  refine size_union_of_inter_empty (of_inter_left hs _) (of_diff hs _) (partition_inter _ _), 
end 

lemma size_induced_partition_inter (s t : set α) (hs : s.finite) :
  size s = size (s ∩ t) + size (s ∩ tᶜ) := 
by {rw ←diff_eq, apply size_induced_partition _ _ hs, }

lemma size_mono_inter_left (s t : set α) (hs : s.finite) : size (s ∩ t) ≤ size s := 
size_monotone hs (inter_subset_left _ _)

lemma size_mono_inter_right (s t : set α) (ht : t.finite) : size (s ∩ t) ≤ size t := 
size_monotone ht (inter_subset_right _ _)

lemma size_mono_union_left (s t : set α) (ht : t.finite): size s ≤ size (s ∪ t)  := 
begin
  by_cases hs : s.finite, 
  apply size_monotone (union hs ht) (subset_union_left _ _), 
  rw [size_zero_of_infinite hs, size_zero_of_infinite], 
  exact infinite_mono (subset_union_left _ _) hs, 
end 

lemma size_mono_union_right (s t : set α) (hs : s.finite): size t ≤ size (s ∪ t) := 
by {rw union_comm, apply size_mono_union_left _ _ hs}

lemma empty_of_size_zero (hs : s.finite) (hsize : size s = 0) : s = ∅ := 
begin
  rw eq_empty_iff_forall_not_mem, intros x hx, 
  have h' := size_monotone hs (singleton_subset_iff.mpr hx), 
  rw [hsize, size_singleton] at h', 
  linarith, 
end  

lemma size_zero_iff_empty (hs : s.finite) : (size s = 0) ↔ (s = ∅) := 
  by {split, apply empty_of_size_zero hs, intros h, rw h, exact size_empty α}

lemma size_le_zero_iff_eq_empty (hs : s.finite):
  size s ≤ 0 ↔ s = ∅ := 
by {rw [← size_zero_iff_empty hs], exact ⟨λ h, le_antisymm h (size_nonneg _), λ h, le_of_eq h⟩} 

lemma size_nonempty (hs : s.finite) (hne : s.nonempty) : 0 < size s  := 
begin
  suffices h' : 0 ≠ size s, exact lt_of_le_of_ne (size_nonneg _) h', 
  rw [←set.ne_empty_iff_nonempty] at hne,  
  exact λ h, hne (empty_of_size_zero hs h.symm), 
end

lemma nonempty_iff_size_pos (hs : s.finite) : s.nonempty ↔ 0 < size s := 
begin
  refine ⟨λ h, size_nonempty hs h, λ h, _⟩,
  rw ←set.ne_empty_iff_nonempty, 
  exact λ h', by {rw [h', size_empty] at h, from lt_irrefl 0 h}, 
end

lemma one_le_size_iff_nonempty (hs : s.finite) : s.nonempty ↔ 1 ≤ size s := 
  nonempty_iff_size_pos hs 

lemma size_strict_monotone (ht : t.finite) (hst : s ⊂ t) : size s < size t := 
begin
  rw [size_induced_partition t s ht, inter_comm, subset_iff_inter_eq_left.mp hst.1], 
  linarith [size_nonempty (of_diff ht _) (ssubset_diff_nonempty hst)], 
end 

lemma eq_of_eq_size_subset (ht : t.finite) (hst : s ⊆ t) (hsize : size s = size t):
  s = t :=
begin
  unfreezingI {rcases subset_ssubset_or_eq hst with (hst' | rfl)},
    swap, refl, 
  have := size_strict_monotone ht hst', rw hsize at this, 
  exact false.elim (lt_irrefl _ this),
end 

lemma eq_of_eq_size_subset_iff (ht : t.finite) (hst : s ⊆ t) : 
  ((size s = size t) ↔ s = t) :=
⟨λ h, eq_of_eq_size_subset ht hst h, λ h, by {rw h}⟩

lemma eq_of_le_size_subset (ht : t.finite) (hst : s ⊆ t) (hsize : size t ≤ size s): 
  s = t :=
by {apply eq_of_eq_size_subset ht hst, exact le_antisymm (size_monotone ht hst) hsize}

lemma size_eq_of_supset (ht : t.finite) (hst : s ⊆ t) (hsize : size t ≤ size s) :
  size s = size t := 
by linarith [size_monotone ht hst]

lemma size_pos_iff_has_mem (hs : s.finite): 
  0 < size s ↔ ∃ e, e ∈ s := 
by rw [← nonempty_iff_size_pos hs, set.nonempty_def] 

lemma one_le_size_iff_has_mem (hs : s.finite): 
  1 ≤ size s ↔ ∃ e, e ∈ s := 
by {convert size_pos_iff_has_mem hs}

lemma size_zero_iff_has_no_mem (hs : s.finite):
  size s = 0 ↔ ¬ ∃ e, e ∈ s := 
begin
  rw [iff.comm, ←not_iff, ←(size_pos_iff_has_mem hs), not_iff], 
  refine ⟨λ h, _, λ h, by linarith ⟩ ,
  linarith [size_nonneg s, not_lt.mp h], 
end

lemma size_le_zero_iff_has_no_mem (hs : s.finite):
  size s ≤ 0 ↔ ¬ ∃ e, e ∈ s := 
by {rw ←(size_zero_iff_has_no_mem hs), split, { intro, linarith [size_nonneg s]}, intro h, rw h}

lemma mem_diff_of_size_lt (hs : s.finite) (hst : size s < size t):
  ∃ (e : α), e ∈ t ∧ e ∉ s :=
begin  
  suffices h' : 0 < size (t \ s), 
    obtain ⟨e, he⟩ := size_pos_has_mem h', tauto, 
  have ht := finite_of_size_pos (lt_of_le_of_lt (size_nonneg _) hst), 
  linarith [size_induced_partition ht t s, size_mono_inter_right Y X], 
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




end set.finite 

end finite 

section fintype  

open set 

variables {α : Type u}{s t : set α}{e f : α}

lemma size_modular [fintype α](s t : set α): 
  size (s ∪ t) + size (s ∩ t) = size s + size t :=
by {apply finite.size_modular; apply finite.of_fintype, }

lemma size_union [fintype α](s t : set α): 
  size (s ∪ t) = size s + size t - size (s ∩ t) := 
by {apply finite.size_union; apply finite.of_fintype,}

lemma ssubset_size [fintype α] (hst : s ⊆ t) (hst' : size s < size t) :
  s ⊂ t := 
by {apply finite.ssubset_size _ _ hst hst'; apply finite.of_fintype,  }

lemma size_subadditive [fintype α] (s t : set α) : size (s ∪ t) ≤ size s + size t :=
by {apply finite.size_subadditive; apply finite.of_fintype }

lemma compl_inter_size [fintype α] (s t : set α) : size (s ∩ t) + size (sᶜ ∩ t) = size t := 
by {apply finite.compl_inter_size, apply finite.of_fintype,}

lemma compl_inter_size_subset [fintype α](hst : s ⊆ t) : 
  size (sᶜ ∩ t) = size t - size s := 
by {apply finite.compl_inter_size_subset _ hst, apply finite.of_fintype, }

lemma diff_size [fintype α] (hst : s ⊆ t) : size (t \ s) = size t - size s :=  
by {apply finite.diff_size _ hst, apply finite.of_fintype }

lemma size_diff_le_size [fintype α](s t : set α) : size (s \ t) ≤ size s := 
by {apply finite.size_diff_le_size, apply finite.of_fintype}

lemma size_union_of_inter_empty [fintype α](hst : s ∩ t = ∅): 
  size (s ∪ t) = size s + size t := 
by {apply finite.size_union_of_inter_empty _ _ hst ; apply finite.of_fintype}

lemma size_union_of_disjoint [fintype α](hst : disjoint s t): 
  size (s ∪ t) = size s + size t := 
by {apply finite.size_union_of_disjoint _ _ hst ; apply finite.of_fintype}

lemma size_modular_diff [fintype α] (s t : set α) : 
  size (s ∪ t) = size (s \ t) + size (t \ s) + size (s ∩ t) :=
by {apply finite.size_modular_diff; apply finite.of_fintype }

lemma size_induced_partition [fintype α] (s t : set α):
  size s = size (s ∩ t) + size (s \ t) := 
by {apply finite.size_induced_partition, apply finite.of_fintype}

lemma size_induced_partition_inter [fintype α] (s t : set α) :
  size s = size (s ∩ t) + size (s ∩ tᶜ) := 
by {apply finite.size_induced_partition, apply finite.of_fintype}

lemma size_mono_inter_left [fintype α] (s t : set α) : size (s ∩ t) ≤ size s := 
by {apply finite.size_mono_inter_left, apply finite.of_fintype}

lemma size_mono_inter_right [fintype α] (s t : set α) : size (s ∩ t) ≤ size t := 
by {apply finite.size_mono_inter_right, apply finite.of_fintype}

lemma size_mono_union_left [fintype α] (s t : set α) : size s ≤ size (s ∪ t)  := 
by {apply finite.size_mono_union_left, apply finite.of_fintype}

lemma size_mono_union_right [fintype α] (s t : set α): size t ≤ size (s ∪ t) := 
by {apply finite.size_mono_union_right, apply finite.of_fintype}

lemma empty_of_size_zero [fintype α](hsize : size s = 0) : s = ∅ := 
by {apply finite.empty_of_size_zero _ hsize, apply finite.of_fintype, }

lemma size_zero_iff_empty [fintype α] : (size s = 0) ↔ (s = ∅) := 
by {apply finite.size_zero_iff_empty, apply finite.of_fintype, }

lemma size_le_zero_iff_eq_empty [fintype α] : size s ≤ 0 ↔ s = ∅ := 
by {apply finite.size_le_zero_iff_eq_empty, apply finite.of_fintype, }

lemma size_nonempty (hne : s.nonempty) [fintype α] : 0 < size s  := 
by {apply finite.size_nonempty _ hne, apply finite.of_fintype, }

lemma nonempty_iff_size_pos [fintype α]: s.nonempty ↔ 0 < size s := 
by {apply finite.nonempty_iff_size_pos, apply finite.of_fintype, }

lemma one_le_size_iff_nonempty [fintype α] : s.nonempty ↔ 1 ≤ size s := 
  nonempty_iff_size_pos

lemma one_le_size_univ_of_nonempty [fintype α] (hα: nonempty α): 1 ≤ size (univ : set α) := 
by rwa [nonempty_iff_univ_nonempty, one_le_size_iff_nonempty] at hα
  --one_le_size_iff_nonempty.mp hα 

lemma one_le_type_size_of_nonempty [fintype α] (hα: nonempty α): 1 ≤ type_size α  := 
one_le_size_univ_of_nonempty hα

lemma size_strict_monotone [fintype α] (hst : s ⊂ t) : size s < size t := 
by {apply finite.size_strict_monotone _ hst; apply finite.of_fintype }

lemma eq_of_eq_size_subset [fintype α] (hst : s ⊆ t) (hsize : size s = size t) : s = t :=
by {apply finite.eq_of_eq_size_subset _ hst hsize, apply finite.of_fintype }

lemma eq_of_eq_size_subset_iff [fintype α] (hst : s ⊆ t) : 
  ((size s = size t) ↔ s = t) :=
by {apply finite.eq_of_eq_size_subset_iff _ hst; apply finite.of_fintype }

lemma eq_of_le_size_subset [fintype α] (hst : s ⊆ t) (hsize : size t ≤ size s): 
  s = t :=
by {apply finite.eq_of_le_size_subset _ hst hsize, apply finite.of_fintype }

lemma size_eq_of_supset [fintype α] (hst : s ⊆ t) (hsize : size t ≤ size s) :
  size s = size t := 
by {apply finite.size_eq_of_supset _ hst hsize, apply finite.of_fintype }

lemma size_pos_iff_has_mem [fintype α]: 
  0 < size s ↔ ∃ e, e ∈ s := 
by rw [← nonempty_iff_size_pos, set.nonempty_def] 

lemma one_le_size_iff_has_mem [fintype α]: 
  1 ≤ size s ↔ ∃ e, e ∈ s := 
by {convert size_pos_iff_has_mem, apply_instance}

lemma size_zero_iff_has_no_mem [fintype α]:
  size s = 0 ↔ ¬ ∃ e, e ∈ s := 
by {rw finite.size_zero_iff_has_no_mem, apply finite.of_fintype}

lemma size_le_zero_iff_has_no_mem [fintype α]:
  size s ≤ 0 ↔ ¬ ∃ e, e ∈ s := 
by {rw finite.size_le_zero_iff_has_no_mem, apply finite.of_fintype}

lemma mem_diff_of_size_lt {X Y : set α}(h : size X < size Y):
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
λ h he hf, by {rw elem_diff_iff at he hf, rw [size_remove_insert hf.1 he.2, 
  size_remove_insert he.1 hf.2], exact h}

lemma size_pair {e f : α}: 
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
  rw ← size_pair hef, 
  apply size_monotone, 
  rw pair_subset_iff, tauto, 
end

lemma size_pair_lb (e f : α): 
  1 ≤ size ({e,f} : set α) := 
by {rw ←union_singletons_eq_pair, 
    linarith [size_monotone (@subset_union_left α {e} {f}),size_singleton e],}

lemma size_pair_ub (e f : α):
  size ({e,f} : set α) ≤ 2 := 
begin
  by_cases e = f, 
  rw [h, pair_eq_singleton, size_singleton], linarith, 
  linarith [size_pair h],
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
  have := nonempty_iff_size_pos.mpr (by linarith : 0 < size X), 
  have := this, 
  cases this with e he,
  refine ⟨e, ⟨this, λ x hx, _⟩⟩,
  by_contra, 
  have hu := size_pair h, 
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


lemma eq_of_pair_size_one {e f : α}(h : size ({e,f} : set α) = 1 ): 
  e = f :=
by {refine size_le_one_iff_mem_unique.mp (by rw h) _ _ _ _; simp} 




lemma size_eq_two_iff_pair {X : set α}:
  size X = 2 ↔ ∃ (e f : α), e ≠ f ∧ X = {e,f} :=
begin
  refine ⟨λ h, _, λ h, _⟩, swap, 
  { rcases h with ⟨e,f,hef,rfl⟩, apply size_pair hef},
  cases size_pos_has_mem (by {rw h, norm_num} : 0 < size X) with e he,
  cases size_pos_has_mem (by {rw [size_remove_mem he,h], norm_num } : 0 < size (X \ {e})) with f hf, 
  refine ⟨e,f,ne.symm (ne_of_mem_diff hf), _⟩,  
  rw eq_comm, apply eq_of_eq_size_subset, 
  { rw ←union_singletons_eq_pair, 
    apply union_of_subsets (singleton_subset_iff.mpr he),  
    simp only [set.mem_diff, set.mem_singleton_iff] at hf, 
    exact singleton_subset_iff.mpr hf.1, },
  rwa [eq_comm, size_pair  (ne.symm (ne_of_mem_diff hf))],  
end 


end fintype 
import data.set.ncard

variables {α : Type*} {s t r : set α} {x y z : α}


lemma enat.exists_eq_top_or_coe (n : ℕ∞) : n = ⊤ ∨ (∃ n₀ : ℕ, n = n₀) :=
by { cases n, exact or.inl rfl, exact or.inr ⟨_, rfl⟩ }

lemma enat.coe_inj {m n : ℕ} : (m : ℕ∞) = n ↔ m = n := 
nat.cast_inj

lemma enat.coe_le_coe_iff {m n : ℕ} : (m : ℕ∞) ≤ n ↔ m ≤ n :=
nat.cast_le  

lemma enat.to_nat_le_to_nat_of_ne_top {m n : ℕ∞} (hle : m ≤ n) (hn : n ≠ ⊤) :
  m.to_nat ≤ n.to_nat :=
begin
  have hm : m ≠ ⊤, rintro rfl, rw [top_le_iff] at hle, contradiction, 
  rw [←with_top.coe_untop _ hn, ←with_top.coe_untop _ hm, enat.coe_le_coe_iff] at hle, 
  rwa [←with_top.coe_untop _ hn, ←with_top.coe_untop _ hm, enat.to_nat_coe, enat.to_nat_coe], 
end

lemma enat.eq_of_top_of_add_pos_le {m n : ℕ∞} (hn : 0 < n) (hmn : m + n ≤ m) : m = ⊤ :=
begin
  obtain (rfl | ⟨m, rfl⟩) := m.exists_eq_top_or_coe, refl, exfalso, 
  obtain (rfl | ⟨n,rfl⟩) := n.exists_eq_top_or_coe,  
  simpa using hmn, 
  rw [←enat.coe_add, enat.coe_le_coe_iff, add_le_iff_nonpos_right, le_zero_iff] at hmn, 
  subst hmn, 
  simpa using hn, 
end 

/-- This should be a `with_top` lemma-/
lemma enat.add_eq_add_iff_left {n a b : ℕ∞} (hn : n ≠ ⊤) : n + a = n + b ↔ a = b := 
by rw [le_antisymm_iff, with_top.add_le_add_iff_left hn, with_top.add_le_add_iff_left hn, 
    le_antisymm_iff]

lemma enat.add_eq_add_iff_right {n a b : ℕ∞} (hn : n ≠ ⊤) : a + n = b + n ↔ a = b := 
by rw [add_comm a, add_comm b, enat.add_eq_add_iff_left hn]


namespace set 

/-- A fixed version that asserts in the conclusion that the set is finite. -/
theorem infinite.exists_supset_ncard_eq' 
 (ht : t.infinite) (hst : s ⊆ t) (hs : s.finite) {k : ℕ} (hsk : s.ncard ≤ k) :
∃ (s' : set α), s ⊆ s' ∧ s' ⊆ t ∧ s'.finite ∧ s'.ncard = k := 
begin
  obtain ((rfl : k = 0) | (hpos : 0 < k)) := eq_zero_or_pos, 
  { rw [le_zero_iff, ncard_eq_zero hs] at hsk,
    subst hsk, 
    exact ⟨∅, subset.rfl, empty_subset _, to_finite _, ncard_empty _⟩ },
  obtain ⟨s', hss', hs't, rfl⟩ := ht.exists_supset_ncard_eq hst hs hsk, 
  exact ⟨s', hss', hs't, finite_of_ncard_pos hpos, rfl⟩, 
end 

/-- The cardinality of a set as a member of `enat`. -/
noncomputable def encard (s : set α) : ℕ∞ := part_enat.with_top_equiv (part_enat.card s)

lemma finite.encard_eq (hs : s.finite) : s.encard = (s.ncard : ℕ∞) := 
begin
  obtain ⟨s, rfl⟩ := hs.exists_finset_coe, 
  simp_rw [encard, part_enat.card_eq_coe_fintype_card,ncard_coe_finset,  
    part_enat.with_top_equiv_coe, nat.cast_inj, finset.coe_sort_coe, fintype.card_coe], 
end 

@[simp] lemma encard_empty (α : Type*) : (∅ : set α).encard = 0 := 
by simp [encard]
 
@[simp] lemma encard_singleton (x : α) : ({x} : set α).encard = 1 :=
by { rw [finite.encard_eq (finite_singleton x), ncard_singleton], refl }

lemma infinite.encard_eq (hs : s.infinite) : s.encard = ⊤ := 
begin
  haveI := hs.to_subtype, 
  rw [encard, part_enat.card_eq_top_of_infinite, part_enat.with_top_equiv_top], 
end 

@[simp] lemma encard_to_nat_eq (s : set α) : s.encard.to_nat = s.ncard :=
begin
  obtain (h | h) := s.finite_or_infinite, 
  simp [h.encard_eq], 
  simp [h.ncard, h.encard_eq], 
end 

lemma ncard_eq_ncard_of_encard_eq_encard (h : s.encard = t.encard) : s.ncard = t.ncard :=
by rw [←encard_to_nat_eq, h, encard_to_nat_eq]

lemma finite.encard_eq_encard_of_ncard_eq_ncard (hs : s.finite) (ht : t.finite) 
(h : s.ncard = t.ncard) : s.encard = t.encard := 
by rw [hs.encard_eq, ht.encard_eq, h]

lemma encard_insert_of_not_mem (h : x ∉ s) : (insert x s).encard = s.encard + 1 :=
begin
  obtain (hs | hs) := s.finite_or_infinite, 
  { rw [hs.encard_eq, (hs.insert x).encard_eq, ncard_insert_of_not_mem h hs], simp },
  rw [hs.encard_eq, (hs.mono (subset_insert _ _)).encard_eq, with_top.top_add],  
end 

@[simp] lemma encard_eq_top_iff_infinite : s.encard = ⊤ ↔ s.infinite :=
begin
  refine ⟨λ h hfin, _, infinite.encard_eq⟩,
  rw hfin.encard_eq at h, 
  simpa only [with_top.nat_ne_top] using h, 
end 

@[simp] lemma encard_lt_top_iff_finite : s.encard < ⊤ ↔ s.finite :=
by rw [lt_top_iff_ne_top, ←not_infinite, ←encard_eq_top_iff_infinite]

@[simp] lemma encard_ne_top_iff_finite : s.encard ≠ ⊤ ↔ s.finite := 
by rw [←not_infinite, ←encard_eq_top_iff_infinite]

lemma finite.encard_lt_top (hs : s.finite) : s.encard < ⊤ :=
encard_lt_top_iff_finite.mpr hs

lemma finite_of_encard_le_coe {k : ℕ} (h : s.encard ≤ k) : s.finite :=
encard_lt_top_iff_finite.mp (h.trans_lt (with_top.coe_lt_top k))

lemma finite_of_encard_lt {k : ℕ∞} (h : s.encard < k) : s.finite := 
by { rw [←encard_lt_top_iff_finite], exact h.trans_le le_top }

lemma encard_le_coe_iff {k : ℕ} : s.encard ≤ k ↔ s.finite ∧ s.ncard ≤ k :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { have hs := finite_of_encard_le_coe h, 
    rw [hs.encard_eq, nat.cast_le] at h,
    exact ⟨hs, h⟩ },
  rw [h.1.encard_eq, nat.cast_le], 
  exact h.2, 
end 

lemma finite.ncard_le_ncard_of_encard_le_encard (ht : t.finite) (h : s.encard ≤ t.encard) :
  s.ncard ≤ t.ncard :=
by { rw [ht.encard_eq, encard_le_coe_iff] at h, exact h.2 }

lemma encard_eq_coe_iff {k : ℕ} : s.encard = k ↔ s.finite ∧ s.ncard = k :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { have hs := finite_of_encard_le_coe h.le, 
    rw [hs.encard_eq, nat.cast_inj] at h,
    exact ⟨hs,h⟩},
  rw [h.1.encard_eq, h.2], 
end 

@[simp] lemma encard_eq_zero : s.encard = 0 ↔ s = ∅ :=
begin
  refine ⟨λ h, _, _⟩,
  { rw [←nat.cast_zero, encard_eq_coe_iff] at h, exact (ncard_eq_zero h.1).mp h.2 },
  rintro rfl, simp, 
end 

lemma encard_eq_ite (s : set α) [decidable (s.finite)] : 
  s.encard = if s.finite then (s.ncard : ℕ∞) else ⊤ := 
begin
  obtain (h | h) := s.finite_or_infinite, 
  { rw [h.encard_eq, if_pos h] },
  rw [h.encard_eq, if_neg h],
end 

lemma encard_subset_le (hst : s ⊆ t) : s.encard ≤ t.encard := 
begin
  obtain (ht | ht) := t.finite_or_infinite, 
  { rw [ht.encard_eq, (ht.subset hst).encard_eq, nat.cast_le],
    exact ncard_le_of_subset hst ht },
  exact le_top.trans_eq ht.encard_eq.symm, 
end 

lemma encard_mono : monotone (encard : set α → ℕ∞) :=
λ _ _, encard_subset_le 

lemma exists_supset_subset_encard_eq {k : ℕ∞} (hs : s.encard ≤ k) (ht : k ≤ t.encard) (hst : s ⊆ t) : 
  ∃ r, s ⊆ r ∧ r ⊆ t ∧ r.encard = k :=
begin
  obtain (rfl | ⟨k, rfl⟩) := k.exists_eq_top_or_coe, 
  { exact ⟨t, hst, subset.rfl, ht.antisymm' le_top⟩ },
  rw encard_le_coe_iff at hs, 
  obtain (htfin | htinf) := t.finite_or_infinite, 
  { rw [htfin.encard_eq, nat.cast_le] at ht,
    obtain ⟨r, hsr, hrt, rfl⟩ := exists_intermediate_set' hs.2 ht hst, 
    exact ⟨r, hsr, hrt, by rw [(htfin.subset hrt).encard_eq]⟩ },
  obtain ⟨r, hsr, hrt, hr, rfl⟩ := htinf.exists_supset_ncard_eq' hst hs.1 hs.2, 
  exact ⟨r, hsr, hrt, hr.encard_eq⟩, 
end  

lemma exists_subset_encard_eq {k : ℕ∞} (h : k ≤ s.encard) : ∃ t ⊆ s, t.encard = k := 
begin
  obtain ⟨t, -, hts, rfl⟩ := exists_supset_subset_encard_eq (by simp) h (empty_subset s),  
  exact ⟨_, hts, rfl⟩,  
end 

lemma encard_union_eq (h : disjoint s t) : (s ∪ t).encard = s.encard + t.encard :=
begin
  obtain (hf | hi) := (s ∪ t).finite_or_infinite, 
  { obtain ⟨hs, ht⟩ := finite_union.mp hf,  
    rw [hf.encard_eq, hs.encard_eq, ht.encard_eq, ←nat.cast_add, nat.cast_inj, 
      ncard_union_eq h hs ht] },
  rw [hi.encard_eq],
  obtain (h | h) := infinite_union.mp hi; simp [h.encard_eq], 
end 

lemma encard_diff_add_encard_inter (s t : set α) : 
  (s \ t).encard + (s ∩ t).encard = s.encard :=
by rw [←encard_union_eq (disjoint_of_subset_right (inter_subset_right _ _) disjoint_sdiff_left), 
    diff_union_inter]

lemma encard_diff_add_encard_of_subset (h : s ⊆ t) : 
  (t \ s).encard + s.encard = t.encard :=
by { nth_rewrite 0 ←encard_diff_add_encard_inter t s, rw inter_eq_self_of_subset_right h }

lemma encard_union_add_encard_inter (s t : set α) :
  (s ∪ t).encard + (s ∩ t).encard = s.encard + t.encard :=
by rw [←diff_union_self, encard_union_eq disjoint_sdiff_left, add_right_comm, 
  encard_diff_add_encard_inter]

lemma encard_union_le (s t : set α) : (s ∪ t).encard ≤ s.encard + t.encard :=
by { rw ←encard_union_add_encard_inter, exact le_self_add }

lemma finite_iff_finite_of_encard_eq_encard (h : s.encard = t.encard) : s.finite ↔ t.finite :=
by rw [←encard_lt_top_iff_finite, ←encard_lt_top_iff_finite, h]

lemma infinite_iff_infinite_of_encard_eq_encard (h : s.encard = t.encard) : 
  s.infinite ↔ t.infinite := by rw [←encard_eq_top_iff_infinite, h, encard_eq_top_iff_infinite]

lemma finite.finite_of_encard_le (ht : t.finite) (hst : s.encard ≤ t.encard) : s.finite :=
by { rw [←encard_lt_top_iff_finite] at *, exact hst.trans_lt ht }

lemma finite.eq_of_subset_of_encard_le (ht : t.finite) (hst : s ⊆ t) (hts : t.encard ≤ s.encard) :
  s = t :=
eq_of_subset_of_ncard_le hst ((ht.subset hst).ncard_le_ncard_of_encard_le_encard hts) ht

lemma finite.eq_of_subset_of_encard_le' (hs : s.finite) (hst : s ⊆ t) (hts : t.encard ≤ s.encard) :
  s = t := 
finite.eq_of_subset_of_encard_le (hs.finite_of_encard_le hts) hst hts


end set 




-- begin
  
--   have i : ℕ∞ ≃ part_enat, exact part_enat.with_top_equiv.symm, 
-- end 
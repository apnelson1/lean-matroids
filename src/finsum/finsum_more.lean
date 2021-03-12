import finsum.finsum algebra.ring.basic prelim.intervals 

open_locale big_operators classical 



universes u v w 

section general 

-- lemmas in this section maybe belong in the mathlib api 

variables {α : Type u} {M: Type v} [add_comm_monoid M] {f g : α → M} {s t : set α} {x y : α}

lemma finsum_eq_zero_of_infinite 
  (hs : ¬ (function.support f).finite) : ∑ᶠ i, f i = 0 :=
by {rw [finsum_eq_finsum_in_univ, finsum_in_eq_zero_of_infinite], rwa set.univ_inter}

lemma finsupp_of_finsum_nonzero (h : ∑ᶠ i, f i ≠ 0) : 
  (function.support f).finite :=
by_contra (λ hn, by {rw finsum_eq_zero_of_infinite hn at h, exact h rfl, })

lemma finsupp_of_finsum_in_nonzero (h : ∑ᶠ i in s, f i ≠ 0) : 
  (s ∩ function.support f).finite :=
by_contra (λ hn, by {rw finsum_in_eq_zero_of_infinite hn at h, exact h rfl, })

@[simp] lemma finsum_empty_set_type:
  ∑ᶠ (i : ((∅ : set α) : Type)), f i = 0 :=
begin
  rw [finsum_eq_finsum_in_univ, set.univ_eq_empty_iff.mpr, finsum_in_empty],  
  by_contra, obtain ⟨x,hx⟩ := h, 
  rwa set.mem_empty_eq at hx, 
end

@[simp] lemma finsum_in_zero: 
  ∑ᶠ i in s, (0 : M) = 0 := 
by {rw finsum_in_inter_support, convert finsum_in_empty, simp}

@[simp] lemma finsum_zero: 
  ∑ᶠ (i : α), (0 : M) = 0 := 
by rw [finsum_eq_finsum_in_univ, finsum_in_zero]

@[simp] lemma finsum_fin_zero {f : fin 0 → M} : 
  ∑ᶠ (i : fin 0), f i = 0 := 
by {convert finsum_zero}

@[simp] lemma finsum_fin_one {f : fin 1 → M} : 
  ∑ᶠ (i : fin 1), f i = f (0 : fin 1) := 
by {convert finsum_singleton, simp,} 

lemma finsum_in_eq_of_eq (h : ∀ i ∈ s, f i = g i) :
  ∑ᶠ i in s, f i = ∑ᶠ i in s, g i :=
by {apply @finsum_in_eq_of_bij_on α M _ α s s f g id, tidy} 

lemma finsum_eq_of_eq (h : ∀ i, f i = g i) :
  ∑ᶠ i, f i = ∑ᶠ i, g i :=
by {repeat {rw finsum_eq_finsum_in_univ}, exact finsum_in_eq_of_eq (λ i _, h i)}

lemma finsum_in_eq_finset_sum_filter_union [add_comm_monoid M] 
(hf: (s ∩ function.support f).finite) (hg: (s ∩ function.support g).finite) :
  ∑ᶠ (i : α) in s, f i = (finset.filter s (hf.to_finset ∪ hg.to_finset)).sum f :=
begin
  rw finsum_in_eq_finset_sum f hf, 
  simp only, 
  have h : hf.to_finset ⊆ finset.filter s (hf.to_finset ∪ hg.to_finset), 
  { intro x, simp only [and_imp, set.mem_inter_eq, set.finite.mem_to_finset, ne.def, 
      finset.mem_union, finset.mem_filter, function.mem_support], 
    tauto,  },
  rw finset.sum_subset h,
  intros x hx hx', 
  rw [set.finite.mem_to_finset, set.mem_inter_iff, not_and, function.mem_support, not_not] at hx', 
  exact hx' (finset.mem_filter.mp hx).2,
end 

lemma finsum_in_eq_finsum_in_subset 
(h : s ⊆ t) (hf : ∀ x, x ∈ t → x ∉ s → f x = 0) :
  ∑ᶠ x in s, f x = ∑ᶠ x in t, f x := 
begin
  by_cases ht : (t ∩ function.support f).finite,
  { have hs : (s ∩ function.support f).finite, from 
      set.finite.subset ht (set.inter_subset_inter_left _ h),
    rw [finsum_in_eq_finset_sum _ hs, finsum_in_eq_finset_sum _ ht],
    refine finset.sum_subset (λ x hxs, _) (λ x hxt hxs, _),
    { simp only [set.mem_inter_eq, set.finite.mem_to_finset, function.mem_support] at hxs ⊢, 
      tauto, },
    rw [set.finite.mem_to_finset] at hxs, simp at hxs hxt, tauto},
  have hs : (s ∩ function.support f).infinite, 
  { refine set.infinite_mono (λ x hx, _) ht, 
    rw [set.mem_inter_iff, function.mem_support] at hx ⊢,
    exact ⟨by_contra (λ hn, hx.2 (hf _ hx.1 hn)),λ hn, hx.2 hn⟩},
  rw [finsum_in_eq_zero_of_infinite hs, finsum_in_eq_zero_of_infinite ht],  
end

lemma finsum_eq_finsum_in_subset 
(hf : ∀ x, x ∉ s → f x = 0) :
  ∑ᶠ x in s, f x = ∑ᶠ x, f x :=
begin 
  rw finsum_eq_finsum_in_univ, 
  exact finsum_in_eq_finsum_in_subset (set.subset_univ _) (λ x _ hx, hf x hx),
end 

@[simp] lemma finsum_subtype_eq_finsum_in (f : α → M) (s : set α) :
 ∑ᶠ (x : s), f x = ∑ᶠ x in s, f x  :=
begin
  rw finsum_eq_finsum_in_univ, 
  convert (finsum_in_eq_of_bij_on subtype.val _ (λ _ _, rfl)), 
  convert set.inj_on.bij_on_image (set.inj_on_of_injective (subtype.val_injective) _), 
  rw [set.image_univ, subtype.range_val],
end 

lemma finsum_set_subtype_eq_finsum_set (f : α → M) (P Q : α → Prop) :
  ∑ᶠ (x : {y // P y}) in {x : {y // P y} | Q (coe x)}, f x = ∑ᶠ x in { x | P x ∧ Q x }, f x := 
by {convert (finsum_in_image _).symm, tidy,}

end general 

section nat 

lemma nat.coe_int_distrib_finsum_in {α : Type u} (f : α → ℕ) (s : set α) : 
  (((∑ᶠ i in s, f i) : ℕ ) : ℤ) = ∑ᶠ i in s, (f i : ℤ) := 
begin
  by_cases hs : (s ∩ function.support f).finite, 
  { simpa using (finsum_in_hom''' (nat.cast_add_monoid_hom ℤ) hs).symm,  },
  repeat {rw finsum_in_eq_zero_of_infinite}, 
    exact int.coe_nat_zero, 
    swap, assumption, 
  convert hs using 2, ext, simp, 
end

lemma nat.coe_int_distrib_finsum {α : Type u} (f : α → ℕ) : 
  (((∑ᶠ (i : α), f i) : ℕ ) : ℤ) = ∑ᶠ (i : α), (f i : ℤ) := 
by rw [finsum_eq_finsum_in_univ, nat.coe_int_distrib_finsum_in, ← finsum_eq_finsum_in_univ]

end nat 

section ring

variables {α : Type u} {M: Type v} [comm_semiring M] {f g : α → M} {s : set α}

lemma mul_distrib_finsum_in' 
(hs : (s ∩ function.support f).finite) (c : M) :
  c * (∑ᶠ x in s, f x) = ∑ᶠ x in s, c * f x := 
(finsum_in_hom' (add_monoid_hom.mul_left c) hs).symm 

lemma mul_distrib_finsum_in [no_zero_divisors M] (c : M) :
  c * (∑ᶠ x in s, f x) = ∑ᶠ x in s, c * f x := 
begin
  by_cases hs : (s ∩ function.support f).finite,
    apply mul_distrib_finsum_in' hs, 
  by_cases hc : c = 0, simp [hc], 
  rw [finsum_in_eq_zero_of_infinite hs, finsum_in_eq_zero_of_infinite, mul_zero],
  convert hs using 3,
  ext, simp [hc],   
end

lemma mul_distrib_finsum'
(h : (function.support f).finite) (c : M) :
  c * (∑ᶠ x, f x) = ∑ᶠ x, c * f x := 
begin
  rw [finsum_eq_finsum_in_univ, finsum_eq_finsum_in_univ],
  apply mul_distrib_finsum_in', 
  rwa set.univ_inter, 
end

lemma mul_distrib_finsum [no_zero_divisors M] (c : M) :
  c * (∑ᶠ x, f x) = ∑ᶠ x, c * f x := 
by {rw [finsum_eq_finsum_in_univ, finsum_eq_finsum_in_univ], apply mul_distrib_finsum_in}
  
end ring 

section group 

variables {α : Type u} {M: Type v} [add_comm_group M] {f g : α → M} {s : set α}

lemma finsum_in_neg_distrib (f : α → M) (s : set α) : 
  ∑ᶠ i in s, - f i = - ∑ᶠ i in s, f i :=   
begin
  by_cases hs : (s ∩ function.support f).finite, 
    exact finsum_in_hom' (- (add_monoid_hom.id M)) hs, 
  repeat {rw [finsum_in_eq_zero_of_infinite]}; simp [hs], 
end 

lemma finsum_neg_distrib (f : α → M) : 
  ∑ᶠ i, - f i = - ∑ᶠ i, f i :=   
by {repeat {rw finsum_eq_finsum_in_univ}, exact finsum_in_neg_distrib _ _} 

--lemma finsum_in_sub_distrib {M : Type*} [add_comm_group M] {f g : α → M} {s : set α} : 

lemma finsum_in_sub_distrib' 
  (hf : (s ∩ function.support f).finite) (hg : (s ∩ function.support g).finite) :
  ∑ᶠ i in s, (f - g) i = ∑ᶠ i in s, f i - ∑ᶠ i in s, g i :=
begin
  simp_rw [sub_eq_add_neg, ← finsum_in_neg_distrib], 
  convert finsum_in_add_distrib' _ _, assumption, 
  rwa ← function.support_neg at hg,  
end

lemma finsum_in_sub_distrib (hs : s.finite) :
  ∑ᶠ i in s, (f - g) i = ∑ᶠ i in s, f i - ∑ᶠ i in s, g i :=
by {apply finsum_in_sub_distrib'; exact set.finite.subset hs (set.inter_subset_left _ _), }

lemma finsum_sub_distrib 
(hf : (function.support f).finite) (hg : (function.support g).finite) :
  ∑ᶠ (i : α), (f - g) i = ∑ᶠ (i : α), f i - ∑ᶠ (i : α), g i :=
by {repeat {rw finsum_eq_finsum_in_univ}, apply finsum_in_sub_distrib'; 
    exact set.finite.subset (by assumption) (set.inter_subset_right _ _), }

end group

section order

open_locale big_operators 

variables {α : Type u} {M: Type v} {f g : α → M} {s t : set α}

lemma nonneg_of_finsum_in_nonneg [ordered_add_comm_monoid M] (hf : ∀ i ∈ s, 0 ≤ f i) : 
  0 ≤ ∑ᶠ i in s, f i := 
finsum_in_induction _ (le_refl _) (λ _ _ ha hb, add_nonneg ha hb) hf

lemma nonneg_of_finsum_nonneg [ordered_add_comm_monoid M] (hf : ∀ i, 0 ≤ f i) : 
  0 ≤ ∑ᶠ (i : α), f i := 
by {rw finsum_eq_finsum_in_univ, exact nonneg_of_finsum_in_nonneg (λ i _, hf i)}

lemma finsum_in_le_finsum_in' [ordered_add_comm_monoid M ] (hfg : ∀ x ∈ s, f x ≤ g x)
(hf : (s ∩ function.support f).finite) (hg : (s ∩ function.support g).finite) : 
  ∑ᶠ i in s, f i ≤ ∑ᶠ i in s, g i := 
begin 
  convert @finset.sum_le_sum _ _ ((hf.to_finset ∪ hg.to_finset).filter s) f g _ _,
  { apply finsum_in_eq_finset_sum_filter_union hf hg},
  { rw finset.union_comm, apply finsum_in_eq_finset_sum_filter_union hg hf},
  exact λ x hx, hfg _ (finset.mem_filter.mp hx).2, 
end

lemma finsum_in_le_finsum_in [ordered_add_comm_monoid M] (hfg : ∀ x ∈ s, f x ≤ g x) (hs : s.finite) : 
  ∑ᶠ i in s, f i ≤ ∑ᶠ i in s, g i := 
by {apply finsum_in_le_finsum_in' hfg;  exact set.finite.subset hs (set.inter_subset_left _ _)}

lemma finsum_in_le_finsum_in_of_pos [ordered_add_comm_monoid M]
(hfg : ∀ x ∈ s, f x ≤ g x) (hg : 0 < ∑ᶠ i in s, g i) :
  ∑ᶠ i in s, f i ≤ ∑ᶠ i in s, g i := 
begin
  have hg' : (s ∩ function.support g).finite, from
    by_contra (λ hn, by {rw finsum_in_eq_zero_of_infinite hn at hg, exact lt_irrefl _ hg, }),
  by_cases hf : (s ∩ function.support f).finite, 
    exact finsum_in_le_finsum_in' hfg hf hg', 
  rw finsum_in_eq_zero_of_infinite hf, 
  exact le_of_lt hg,
end 

lemma finsum_le_finsum [ordered_add_comm_monoid M] (hfg : ∀ x, f x ≤ g x)
(hf : (function.support f).finite) (hg : (function.support g).finite) : 
  ∑ᶠ (i : α), f i ≤ ∑ᶠ (i : α), g i := 
begin
  repeat {rw finsum_eq_finsum_in_univ}, 
  apply finsum_in_le_finsum_in' (λ x hx, hfg x); 
  exact set.finite.subset (by assumption) (set.inter_subset_right _ _), 
end

lemma finsum_le_finsum_of_pos [ordered_add_comm_monoid M] (hfg : ∀ x, f x ≤ g x)
(hg : 0 < ∑ᶠ i, g i) :
  ∑ᶠ (i : α), f i ≤ ∑ᶠ (i : α), g i := 
begin
  simp_rw finsum_eq_finsum_in_univ at *, 
  apply finsum_in_le_finsum_in_of_pos (λ x hx, hfg x) hg, 
end

lemma finsum_in_eq_zero_iff_of_nonneg [ordered_add_comm_monoid M] 
(hs : (s ∩ function.support f).finite) (hf : ∀ x ∈ s, 0 ≤ f x) : 
  ∑ᶠ x in s, f x = 0 ↔ ∀ x ∈ s, f x = 0 := 
begin
  rw [finsum_in_eq_finset_sum _ hs, finset.sum_eq_zero_iff_of_nonneg], simp, 
  simp_rw [set.finite.mem_to_finset, set.mem_inter_iff], tauto, 
end


lemma finsum_in_le_zero_iff_of_nonneg [ordered_add_comm_monoid M] 
(hs : (s ∩ function.support f).finite) (hf : ∀ x ∈ s, 0 ≤ f x) : 
  ∑ᶠ x in s, f x ≤ 0 ↔ ∀ x ∈ s, f x = 0 := 
begin
  convert finsum_in_eq_zero_iff_of_nonneg hs hf, 
  exact iff_iff_eq.mp ⟨λ h, le_antisymm h (nonneg_of_finsum_in_nonneg hf), λ h, by rw h⟩ , 
end

lemma finsum_eq_zero_iff_of_nonneg [ordered_add_comm_monoid M] 
(h : (function.support f).finite) (hf : ∀ x, 0 ≤ f x) : 
  ∑ᶠ x, f x = 0 ↔ ∀ x, f x = 0 := 
begin
  rw [finsum_eq_finsum_in_univ, finsum_in_eq_zero_iff_of_nonneg], 
  tauto, rwa [set.univ_inter], tauto,  
end

lemma finsum_le_zero_iff_of_nonneg [ordered_add_comm_monoid M] 
(h : (function.support f).finite) (hf : ∀ x, 0 ≤ f x) : 
  ∑ᶠ x, f x ≤ 0 ↔ ∀ x, f x = 0 := 
begin
  convert finsum_eq_zero_iff_of_nonneg h hf, 
  exact iff_iff_eq.mp ⟨λ h, le_antisymm h (nonneg_of_finsum_nonneg hf), λ h, by rw h⟩ , 
end


@[simp] lemma finsum_in_eq_zero_iff [canonically_ordered_add_monoid M] 
(hs : (s ∩ function.support f).finite) : 
  ∑ᶠ x in s, f x = 0 ↔ ∀ x ∈ s, f x = 0 := 
finsum_in_eq_zero_iff_of_nonneg hs (by simp)

@[simp] lemma finsum_eq_zero_iff [canonically_ordered_add_monoid M] 
(h : (function.support f).finite) : 
  ∑ᶠ x, f x = 0 ↔ ∀ x, f x = 0 := 
finsum_eq_zero_iff_of_nonneg h (by simp)

lemma finsum_in_exists_lt_of_finsum_lt [linear_ordered_cancel_add_comm_monoid M]
(hf : (s ∩ function.support f).finite) (hg : (s ∩ function.support g).finite)
(hlt : ∑ᶠ x in s, f x < ∑ᶠ x in s, g x) : 
  ∃ i ∈ s, f i < g i := 
by_contra (λ hn, by {push_neg at hn, exact not_lt_of_le (finsum_in_le_finsum_in' hn hg hf) hlt})

lemma finsum_exists_lt_of_finsum_lt [linear_ordered_cancel_add_comm_monoid M]
(hf : (function.support f).finite) (hg : (function.support g).finite)
(hlt : ∑ᶠ x, f x < ∑ᶠ x, g x) : 
  ∃ i, f i < g i := 
begin 
  repeat {rw finsum_eq_finsum_in_univ at hlt},
  obtain ⟨i,-,hi⟩ := finsum_in_exists_lt_of_finsum_lt _ _ hlt, exact ⟨i,hi⟩,
  { apply set.finite.subset hf _, exact set.inter_subset_right _ _, },
  apply set.finite.subset hg _, exact set.inter_subset_right _ _, 
end 

lemma finsum_in_lt_finsum_in [ordered_cancel_add_comm_monoid M]
(hf : (s ∩ function.support f).finite) (hg : (s ∩ function.support g).finite)
(hle : ∀ i ∈ s, f i ≤ g i) (hlt : ∃ i ∈ s, f i < g i) : 
  ∑ᶠ i in s, f i < ∑ᶠ i in s, g i := 
begin
  convert @finset.sum_lt_sum α M ((hf.to_finset ∪ hg.to_finset).filter s) f g _ _ _,
  { apply finsum_in_eq_finset_sum_filter_union hf hg}, 
  { rw finset.union_comm, apply finsum_in_eq_finset_sum_filter_union hg hf},  
  { exact λ x hx, hle _ (finset.mem_filter.mp hx).2}, 
  obtain ⟨i,his, hi⟩ := hlt,
  refine ⟨i, _, hi⟩,
  simp only [set.mem_inter_eq, set.finite.mem_to_finset, finset.mem_union, 
  finset.mem_filter, function.mem_support, ← and_or_distrib_left], 
  refine ⟨⟨his, by_contra (λ hn, _)⟩, his⟩, 
  push_neg at hn, rw [hn.1, hn.2] at hi, 
  exact lt_irrefl _ hi,
end

lemma finsum_lt_finsum [ordered_cancel_add_comm_monoid M]
(hf : (function.support f).finite) (hg : (function.support g).finite)
(hle : ∀ i, f i ≤ g i) (hlt : ∃ i, f i < g i) : 
  ∑ᶠ i, f i < ∑ᶠ i, g i := 
begin
  repeat {rw finsum_eq_finsum_in_univ}, apply finsum_in_lt_finsum_in, 
  { apply set.finite.subset hf _, exact set.inter_subset_right _ _, },
  { apply set.finite.subset hg _, exact set.inter_subset_right _ _, }, 
  { exact λ i hi, hle i, },
  exact (let ⟨i, hi⟩ := hlt in ⟨i, set.mem_univ _, hi⟩),   
end

lemma finsum_in_eq_finsum_in_iff_of_le [ordered_cancel_add_comm_monoid M]
(hf : (s ∩ function.support f).finite) (hg : (s ∩ function.support g).finite)
(hfg : ∀ x ∈ s, f x ≤ g x) : 
  ∑ᶠ i in s, f i = ∑ᶠ i in s, g i ↔ ∀ i ∈ s, f i = g i := 
begin
  refine ⟨λ h, λ i hi, by_contra (λ hn, _), finsum_in_eq_of_eq⟩, 
  exact ne_of_lt (finsum_in_lt_finsum_in hf hg hfg ⟨i, hi, (ne.le_iff_lt hn).mp (hfg i hi)⟩) h, 
end

lemma finsum_in_ge_finsum_in_iff_of_le [ordered_cancel_add_comm_monoid M]
(hf : (s ∩ function.support f).finite) (hg : (s ∩ function.support g).finite)
(hfg : ∀ x ∈ s, f x ≤ g x) : 
  ∑ᶠ i in s, g i ≤ ∑ᶠ i in s, f i ↔ ∀ i ∈ s, f i = g i := 
begin
  convert finsum_in_eq_finsum_in_iff_of_le hf hg hfg, 
  refine iff_iff_eq.mp ⟨λ h, le_antisymm (finsum_in_le_finsum_in' hfg hf hg) h, λ h, by rw h⟩,
end

lemma finsum_eq_finsum_iff_of_le [ordered_cancel_add_comm_monoid M]
(hf : (function.support f).finite) (hg : (function.support g).finite)
(hfg : ∀ x, f x ≤ g x) : 
  ∑ᶠ i, f i = ∑ᶠ i, g i ↔ ∀ i, f i = g i := 
begin
  repeat {rw finsum_eq_finsum_in_univ}, rw finsum_in_eq_finsum_in_iff_of_le, tauto, 
  { apply set.finite.subset hf _, exact set.inter_subset_right _ _, },
  { apply set.finite.subset hg _, exact set.inter_subset_right _ _, }, 
  exact λ x _, hfg x, 
end


lemma finsum_in_subset_le_finsum_in_of_nonneg [ordered_add_comm_monoid M] 
(ht : (t ∩ (function.support f)).finite)
(hst : s ⊆ t) (hf : ∀ x ∈ t, 0 ≤ f x) :
  ∑ᶠ x in s, f x ≤ ∑ᶠ x in t, f x :=
begin 
  have hs := set.finite.subset ht ((function.support f).inter_subset_inter_left hst),
  have hs' := set.finite.subset ht 
    ((function.support f).inter_subset_inter_left (set.diff_subset t s)),
  have h' := finsum_in_union' hs hs' (set.disjoint_diff), 
  rw (set.union_diff_cancel hst) at h', 
  rw h', 
  exact le_add_of_nonneg_right (nonneg_of_finsum_in_nonneg (λ i hi, hf i (set.mem_of_mem_diff hi)))
end

lemma finsum_in_subset_le_finsum_in_of_nonneg' [ordered_add_comm_monoid M] 
(ht : t.finite)
(hst : s ⊆ t) (hf : ∀ x ∈ t, 0 ≤ f x) :
  ∑ᶠ x in s, f x ≤ ∑ᶠ x in t, f x :=
begin 
  refine finsum_in_subset_le_finsum_in_of_nonneg _ hst hf, 
  apply set.finite.subset ht (set.inter_subset_left _ _), 
end


lemma eq_zero_of_finsum_in_subset_le_finsum_in_of_nonneg [ordered_cancel_add_comm_monoid M] 
(ht : (t ∩ (function.support f)).finite)
(hst : s ⊆ t) (hf : ∀ x ∈ t, 0 ≤ f x) (h : ∑ᶠ x in t, f x ≤ ∑ᶠ x in s, f x) :
  ∀ x ∈ t \ s, f x = 0 :=
begin
  have hs := set.finite.subset ht ((function.support f).inter_subset_inter_left hst),
  have hs' := set.finite.subset ht 
    ((function.support f).inter_subset_inter_left (set.diff_subset t s)),
  have h' := finsum_in_union' hs hs' (set.disjoint_diff), 
  rw (set.union_diff_cancel hst) at h', 
  rwa [h', add_le_iff_nonpos_right, finsum_in_le_zero_iff_of_nonneg hs'] at h, 
  exact λ x hx, hf x (set.mem_of_mem_diff hx), 
end

lemma eq_zero_of_finsum_in_subset_eq_finsum_in_of_nonneg' [ordered_cancel_add_comm_monoid M] 
(ht : t.finite)
(hst : s ⊆ t) (hf : ∀ x ∈ t, 0 ≤ f x) (h : ∑ᶠ x in t, f x ≤ ∑ᶠ x in s, f x) :
  ∀ x ∈ t \ s, f x = 0 :=
begin
  refine eq_zero_of_finsum_in_subset_le_finsum_in_of_nonneg _ hst hf h,
  apply set.finite.subset ht (set.inter_subset_left _ _), 
end

end order

section intervals 

variables {α : Type u} [ordered_cancel_add_comm_monoid α][has_exists_add_of_le α]
{M : Type v} [add_comm_monoid M]

lemma finsum_Icc_shift (a b d : α) (f : α → M) : 
  ∑ᶠ i in set.Icc a b, f (i + d) = ∑ᶠ i in set.Icc (a + d) (b + d), f i := 
finsum_in_eq_of_bij_on _ (Icc_add_bij _ _ _) (λ _ _, rfl)

lemma finsum_Ico_shift (a b d : α) (f : α → M) : 
  ∑ᶠ i in set.Ico a b, f (i + d) = ∑ᶠ i in set.Ico (a + d) (b + d), f i := 
finsum_in_eq_of_bij_on _ (Ico_add_bij _ _ _) (λ _ _, rfl)

lemma finsum_Ioc_shift (a b d : α) (f : α → M) : 
  ∑ᶠ i in set.Ioc a b, f (i + d) = ∑ᶠ i in set.Ioc (a + d) (b + d), f i := 
finsum_in_eq_of_bij_on _ (Ioc_add_bij _ _ _) (λ _ _, rfl)

lemma finsum_Ioo_shift (a b d : α) (f : α → M) : 
  ∑ᶠ i in set.Ioo a b, f (i + d) = ∑ᶠ i in set.Ioo (a + d) (b + d), f i := 
finsum_in_eq_of_bij_on _ (Ioo_add_bij _ _ _) (λ _ _, rfl)


 

end intervals 


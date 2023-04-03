
import .finsum_more prelim.single data.nat.parity data.zmod.basic data.zmod.parity

open_locale classical big_operators
noncomputable theory

universes u v w

variables {α : Type*} {β : Type*}

open set

def fincard (s : set α) : ℕ := ∑ᶠ x in s, 1

def fincard_t (α : Type*) := fincard (set.univ : set α)

lemma fincard_def (s : set α) :
  fincard s = ∑ᶠ x in s, 1 :=
rfl

lemma fincard_t_def (α : Type*) :
  fincard_t α = fincard (set.univ : set α) :=
rfl

lemma fincard_t_eq_sum_ones (α : Type*) :
  fincard_t α = ∑ᶠ (x : α), 1 :=
by rw [fincard_t, fincard_def, finsum_eq_finsum_in_univ]

lemma fincard_eq_finset_card' (s : set α) (hs : s.finite) :
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

lemma fincard_t_eq_fintype_card [fintype α]:
  fincard_t α = fintype.card α :=
by {rw [fincard_t_def, fincard_eq_finset_card, ← finset.card_univ, ← to_finset_univ], congr', }

lemma fincard_t_subtype_eq_fincard (s : set α) :
  fincard_t s = fincard s :=
by {rw [fincard_t_eq_sum_ones], exact finsum_subtype_eq_finsum_in (1) s}

@[simp] lemma support_const [has_zero β] {b : β} (hb : b ≠ 0) :
  function.support (λ x : α, b) = univ :=
by {ext, simp [hb], }

@[simp] lemma support_one :
  function.support (1 : α → ℕ) = univ :=
support_const (by simp : 1 ≠ 0)

lemma fincard_of_infinite {s : set α} (hs : s.infinite) :
  fincard s = 0 :=
by {rw [fincard, finsum_in_eq_zero_of_infinite], simpa using hs,}

lemma finite_of_fincard_pos {s : set α} (hs : 0 < fincard s) :
  s.finite :=
by_contra (λ hn, by {rw fincard_of_infinite hn at hs, exact lt_irrefl _ hs, })

@[simp] lemma fincard_empty :
  fincard (∅ : set α) = 0 :=
by simp [fincard]

lemma fincard_eq_zero_iff_empty {s : set α} (hs : s.finite) :
  fincard s = 0 ↔ s = ∅ :=
begin
  rw [fincard_def, finsum_in_eq_zero_iff _],
    swap, simpa using hs,
  exact ⟨λ h, by {ext, simp at *, tauto,}, λ h, by {rw h, simp,}⟩,
end

lemma nonempty_of_fincard_pos {s : set α} (hs : 0 < fincard s):
  s.nonempty :=
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


@[simp] lemma fincard_t_fin (n : ℕ) :
  fincard_t (fin n) = n :=
by simp [fincard_t_eq_fintype_card]

lemma fincard_t_eq_iff_equiv [fintype α] [fintype β]:
  fincard_t α = fincard_t β ↔ nonempty (α ≃ β) :=
by simp_rw [fincard_t_eq_fintype_card, fintype.card_eq]

lemma fincard_t_eq_iff_fin_equiv [fintype α] {n : ℕ} :
  fincard_t α = n ↔ nonempty (α ≃ fin n) :=
by {nth_rewrite 0 ← fincard_t_fin n, apply fincard_t_eq_iff_equiv}

lemma equiv_fin_fincard_t [fintype α]:
  nonempty (α ≃ fin (fincard_t α)) :=
fincard_t_eq_iff_fin_equiv.mp rfl



/-- chooses a bijection between α and fin (fincard α) -/
def choose_fin_bij [fintype α]:
  α ≃ fin (fincard_t α) :=
classical.choice equiv_fin_fincard_t

@[simp] lemma fincard_singleton (e : α) :
  fincard ({e} : set α) = 1 :=
by simp [fincard]

lemma fincard_modular {s t : set α} (hs : s.finite) (ht : t.finite) :
  fincard (s ∪ t) + fincard (s ∩ t) = fincard s + fincard t :=
by simp [fincard, finsum_in_union_inter hs ht]

lemma fincard_nonneg (s : set α) : 0 ≤ fincard s :=
nonneg_of_finsum_nonneg (λ i, by {split_ifs; simp})

lemma fincard_img_emb (f : α ↪ β) (s : set α) :
  fincard (f '' s) = fincard s :=
begin
  by_cases hs : s.finite,
  { rw [fincard_def, fincard_def, finsum_in_image' hs],
    exact (set.inj_on_of_injective f.inj' _)},
  rw [fincard_of_infinite, fincard_of_infinite], assumption,
  rw set.infinite_image_iff, assumption,
  exact (set.inj_on_of_injective f.inj' _),
end

lemma fincard_of_finite_eq_card {s : set α} (hs : s.finite) :
  fincard s = (hs.to_finset).card :=
begin
  rw [fincard_def, finset.card_eq_sum_ones, finsum_in_eq_finset_sum],  simp,
  exact set.finite.subset hs (inter_subset_left _ _),
end

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
  convert fincard_img_emb (function.embedding.refl α) _,
  ext, simp, rintro rfl, assumption,
end

@[simp] lemma nat.finsum_const_eq_mul_fincard_t (b : ℕ) :
  ∑ᶠ (i : α), b = b * (fincard_t α) :=
by rw [← mul_one b, ← mul_distrib_finsum, fincard_t_eq_sum_ones, mul_one]

@[simp] lemma nat.finsum_in_const_eq_mul_fincard (b : ℕ){s : set α} :
  ∑ᶠ i in s, b = b * (fincard s) :=
by rw [← mul_one b, ← mul_distrib_finsum_in, fincard_def, mul_one]

lemma sum_fincard_fiber_eq_fincard {s : set α} (f : α → β)
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

lemma fincard_union {s t : set α} (hs : s.finite) (ht : t.finite):
  (fincard (s ∪ t) : ℤ) = fincard s + fincard t - fincard (s ∩ t) :=
by linarith [fincard_modular hs ht]

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

lemma finite_set_induction (P : set α → Prop):
  (P ∅) → (∀ (s : set α) (e : α), e ∉ s → P s → P (insert e s)) → (∀ (s : set α), s.finite → P s) :=
begin
  suffices h' : ∀ n : ℕ, (P ∅) → (∀ (s : set α) (e : α), e ∉ s → P s → P (insert e s))
    → (∀ (s : set α), s.finite → fincard s = n → P s),
  { exact λ hbase ih s hs, h' (fincard s) hbase ih _ hs rfl},
  intros n hempt,
  induction n with n ih,
  { intros ih s hfin hsize, rwa (fincard_eq_zero_iff_empty hfin).mp hsize, },
  intros h' s hfin hcard,
  obtain ⟨e,he⟩ := nonempty_of_fincard_pos (by {rw hcard, simp} : 0 < fincard s),
  rw [fincard_remove he hfin, nat.one_add] at hcard,
  convert h' _ _ (nonmem_removal s e) (ih h' (s \ {e}) (finite.diff hfin _) (nat.succ.inj hcard)),
  rw [remove_insert, insert_eq_of_mem he],
end



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
      fincard_symm_diff_mod2 (hs.subset has) (set.finite_singleton _),
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
/-

lemma finsum_incl_excl {s : set (set α)} (f : α → M) (hs : s.finite) :
  ∑ᶠ x in ⋃₀ s, f x = ∑ᶠ t in s.powerset, (∑ᶠ x in ⋂₀ t, group_sign (fincard t) (f x) ) :=
begin
  sorry,
end


lemma finsum_incl_excl' {s : set (set α)} {f : α → M}
(hf : (⋃₀ s ∩ function.support f).finite):
  ∑ᶠ x in ⋃₀ s, f x = ∑ᶠ t in s.powerset, (∑ᶠ x in ⋂₀ t, group_sign (fincard t) (f x) ) :=
begin
  set s' := (λ t, t ∩ function.support f) '' s with hs',
  have hfin : (⋃₀ s').finite,
  { convert hf, rw hs', ext x, simp, tauto},
  have hs' : s'.finite,
  { apply finite.subset (finite.finite_subsets hfin),
    exact λ t ht, mem_set_of_eq.mpr (λ x hx, mem_sUnion.mpr ⟨t,ht,hx⟩)},
  convert finsum_incl_excl f hs' using 1,
  { sorry},
  rw [finsum_in_inter_support,  finsum_in_inter_support _ (s'.powerset)],
-/



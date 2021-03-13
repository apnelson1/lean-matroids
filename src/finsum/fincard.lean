
import .finsum_more

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

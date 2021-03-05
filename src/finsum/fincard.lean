
import .finsum .is_finite 

open_locale classical big_operators 
noncomputable theory 

variables {α β : Type*}

open set 

def fincard (s : set α) : ℕ := ∑ᶠ x in s, (λ _, (1 : ℕ)) x  

def fincard_t (α : Type) := fincard (set.univ : set α)

lemma fincard_def (s : set α) : 
  fincard s = ∑ᶠ x in s, (λ _, (1 : ℕ)) x := 
rfl 

@[simp] lemma support_const [has_zero β]{b : β}(hb : b ≠ 0): 
  function.support (λ x : α, b) = univ :=
by {ext, simp [hb], }

@[simp] lemma support_one : 
  function.support (λ x : α, (1 : ℕ)) = univ :=
support_const (by simp)

lemma fincard_of_infinite {s : set α}(hs : s.infinite):
  fincard s = 0 := 
by {rw [fincard, finsum_in_eq_zero_of_infinite], simpa using hs,}

@[simp] lemma fincard_empty :
   fincard (∅ : set α) = 0 := 
by simp [fincard]

@[simp] lemma fincard_singleton (e : α): 
  fincard ({e}: set α) = 1 := 
by simp [fincard]

lemma fincard_modular {s t : set α} (hs : s.finite)(ht : t.finite): 
  fincard (s ∪ t) + fincard (s ∩ t) = fincard s + fincard t :=
by simp [fincard, finsum_in_union_inter hs ht]

lemma fincard_nonneg (s : set α) : 0 ≤ fincard s := 
nonneg_of_finsum_nonneg (λ i, by {split_ifs; simp})

lemma fincard_img_emb (f : α ↪ β)(s : set α): 
  fincard (f '' s) = fincard s := 
begin
  by_cases hs : s.finite,
  { rw [fincard_def, fincard_def, finsum_in_image' hs], 
    exact (set.inj_on_of_injective f.inj' _)},
  rw [fincard_of_infinite, fincard_of_infinite], assumption, 
  rw set.infinite_image_iff, assumption, 
  exact (set.inj_on_of_injective f.inj' _), 
end

lemma fincard_of_finite_eq_card {s : set α}(hs : s.finite): 
  fincard s = (hs.to_finset).card := 
begin
  rw [fincard_def, finset.card_eq_sum_ones, finsum_in_eq_finset_sum],  simp,
  exact set.finite.subset hs (inter_subset_left _ _), 
end

theorem fincard_preimage_eq_sum' {α β : Type}(f : α → β){s : set α}{t : set β}
(hs : s.finite)(ht : t.finite) :
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

theorem fincard_preimage_eq_sum {α β : Type}(f : α → β){t : set β}
(ht : t.finite)(ht' : (f ⁻¹' t).finite) :
fincard (f⁻¹' t) = ∑ᶠ y in t, fincard {x | f x = y} := 
begin
  have := fincard_preimage_eq_sum' f ht' ht, rw inter_self at this,  
  rw [this, finsum_in_def, finsum_in_def], congr', ext, 
  split_ifs, swap, refl, 
  convert fincard_img_emb (function.embedding.refl α) _, 
  ext, simp, rintro rfl, assumption,  
end

theorem fincard_univ_eq_sum_fincard_preimage {α β : Type}
[nonempty (fintype α)]

/-

@[simp] lemma finsum_in_image' {s : set β} {g : β → α} (hs : s.finite) (hg : set.inj_on g s) :
  ∑ᶠ j in (g '' s), f j = ∑ᶠ i in s, (f ∘ g) i :=
begin
  rw [finsum_in_eq_finset_sum''' (f ∘ g) hs, finsum_in_eq_finset_sum''' f (set.finite.image g hs),
    ←finset.sum_image
    (λ x hx y hy hxy, hg ((set.finite.mem_to_finset hs).1 hx) ((set.finite.mem_to_finset hs).1 hy) hxy)],
  congr, ext, simp
end
-/

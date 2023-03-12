
import data.finite.card

open nat

noncomputable theory 
open_locale classical 

variables {α β : Type*} {s t : set α} {a b x y : α} {f : α → β}

namespace set 

def ncard (s : set α) := nat.card s 

lemma ncard_def (s : set α) : s.ncard = nat.card s := rfl 

lemma ncard_eq_to_finset_card (s : set α) [finite s] : 
  s.ncard = finset.card (@set.to_finset α s (fintype.of_finite s)) :=
begin  
  haveI := fintype.of_finite s, 
  rw [ncard, nat.card_eq_fintype_card, set.to_finset_card], 
  congr', 
end

lemma ncard_le_of_subset [finite t] (hst : s ⊆ t) :
  s.ncard ≤ t.ncard := 
begin
  haveI := ((to_finite t).subset hst).to_subtype,
  simp_rw ncard_eq_to_finset_card, 
  apply finset.card_mono,
  simpa, 
end 

@[simp] lemma ncard_eq_zero [finite s] : 
  s.ncard = 0 ↔ s = ∅ := 
by simp [ncard_def, finite.card_eq_zero_iff]

@[simp] lemma ncard_eq_zero_of_infinite (s : set α) [infinite s] : 
  s.ncard = 0 := 
nat.card_eq_zero_of_infinite

lemma infinite.ncard_eq_zero (hs : s.infinite) : 
  s.ncard = 0 :=
by {haveI := hs.to_subtype, exact s.ncard_eq_zero_of_infinite,}

lemma ncard_pos [finite s] : 
  0 < s.ncard ↔ s.nonempty := 
by simp [ncard_def, finite.card_pos_iff]

lemma ncard_ne_zero_of_mem [finite s] (h : a ∈ s) :
  s.ncard ≠ 0 :=
(ncard_pos.mpr ⟨a,h⟩).ne.symm

lemma finite_of_ncard_ne_zero (hs : s.ncard ≠ 0) : 
  s.finite := 
s.finite_or_infinite.elim id (λ h, (hs h.ncard_eq_zero).elim)

lemma nonempty_of_ncard_ne_zero (hs : s.ncard ≠ 0) : 
  s.nonempty := 
by {rw nonempty_iff_ne_empty, rintro rfl, simpa using hs}

@[simp] lemma ncard_singleton (a : α) : 
  ({a} : set α).ncard = 1 :=   
by simp [ncard_eq_to_finset_card]

lemma ncard_singleton_inter : ({a} ∩ s).ncard ≤ 1 := 
begin
  rw [←inter_self {a}, inter_assoc, ncard_eq_to_finset_card, to_finset_inter, to_finset_singleton], 
  apply finset.card_singleton_inter, 
end  

section insert_erase

@[simp] lemma ncard_insert_of_not_mem [finite s] (h : a ∉ s) : 
  (insert a s).ncard = s.ncard + 1 :=
begin
  haveI := fintype.of_finite s, 
  rw [ncard_eq_to_finset_card, ncard_eq_to_finset_card, to_finset_insert, 
    finset.card_insert_of_not_mem],
  { congr,},
  simpa, 
end 

lemma ncard_insert_of_mem (h : a ∈ s) : 
  ncard (insert a s) = s.ncard := 
by rw insert_eq_of_mem h

lemma card_insert_le (a : α) (s : set α) : (insert a s).ncard ≤ s.ncard + 1 :=
begin
  obtain (hs | hs) := s.finite_or_infinite,  
  { haveI := hs.to_subtype, 
    exact (em (a ∈ s)).elim (λ h, (ncard_insert_of_mem h).trans_le (le_succ _)) (λ h, by rw ncard_insert_of_not_mem h), },
  rw (hs.mono (subset_insert a s)).ncard_eq_zero, 
  exact nat.zero_le _, 
end 

lemma ncard_insert_eq_ite [finite s] : 
  ncard (insert a s) = if a ∈ s then s.ncard else s.ncard + 1 :=
begin
  by_cases h : a ∈ s,
  { rw [ncard_insert_of_mem h, if_pos h] },
  { rw [ncard_insert_of_not_mem h, if_neg h] }
end

@[simp] lemma card_doubleton (h : a ≠ b) : ({a, b} : set α).ncard = 2 :=
by {rw [ncard_insert_of_not_mem, ncard_singleton], simpa}

@[simp] lemma ncard_diff_singleton_add_one [finite s] (h : a ∈ s) :
  (s \ {a}).ncard + 1 = s.ncard := 
begin
  have h' : a ∉ s \ {a}, by {rw [mem_diff_singleton], tauto},
  rw ←ncard_insert_of_not_mem h', congr', simpa, 
end 

@[simp] lemma ncard_diff_singleton_of_mem [finite s] (h : a ∈ s) :
  (s \ {a}).ncard = s.ncard - 1 := 
eq_tsub_of_add_eq (ncard_diff_singleton_add_one h)
  
lemma ncard_diff_singleton_lt_of_mem [finite s] (h : a ∈ s) : 
  (s \ {a}).ncard < s.ncard := 
by {rw [←ncard_diff_singleton_add_one h], apply lt_add_one}

lemma ncard_diff_singleton_le (s : set α) (a : α) : 
  (s \ {a}).ncard ≤ s.ncard := 
begin
  obtain (hs | hs) := s.finite_or_infinite,  
  { haveI := hs.to_subtype, 
    apply ncard_le_of_subset (diff_subset _ _), assumption},
  convert zero_le _, 
  exact (hs.diff (by simp : set.finite {a})).ncard_eq_zero, 
end 

lemma pred_ncard_le_ncard_diff_singleton (s : set α) (a : α) : 
  s.ncard - 1 ≤ (s \ {a}).ncard :=
begin
  cases s.finite_or_infinite, 
  { haveI := h.to_subtype,
    by_cases h : a ∈ s, 
    { rw ncard_diff_singleton_of_mem h, },
    rw diff_singleton_eq_self h, 
    apply pred_le},
  convert nat.zero_le _,
  rw h.ncard_eq_zero, 
end

end insert_erase

lemma ncard_image_le [finite s] : 
  (f '' s).ncard ≤ s.ncard :=
begin
  rw ncard_eq_to_finset_card, 
  haveI := fintype.of_finite s, 
  convert @finset.card_image_le _ _ s.to_finset f _, 
  { convert rfl, ext, simp, },
  rw ncard_eq_to_finset_card, congr', 
end 

lemma ncard_image_of_inj_on (H : set.inj_on f s) : 
  (f '' s).ncard = s.ncard :=
begin 
  cases s.finite_or_infinite, 
  { haveI := @fintype.of_finite s h.to_subtype,
    haveI := @fintype.of_finite _ (h.image f).to_subtype,  
    convert card_image_of_inj_on H; simp [ncard_def]},
  rw [h.ncard_eq_zero, ((infinite_image_iff H).mpr h).ncard_eq_zero], 
end 

lemma inj_on_of_ncard_image_eq [finite s] (H : (f '' s).ncard = s.ncard) : 
  set.inj_on f s :=
begin
  haveI := fintype.of_finite s, 
  haveI := @fintype.of_finite _ ((to_finite s).image f).to_subtype,  
  simp_rw ncard_eq_to_finset_card at H, 
  rw ← coe_to_finset s,  
  apply finset.inj_on_of_card_image_eq, 
  convert H, 
  ext, 
  simp, 
end

lemma ncard_image_iff [finite s] : 
  (f '' s).ncard = s.ncard ↔ set.inj_on f s :=
⟨inj_on_of_ncard_image_eq, ncard_image_of_inj_on⟩

lemma ncard_image_of_injective (s : set α) (H : f.injective) :
  (s.image f).ncard = s.ncard :=
ncard_image_of_inj_on $ λ x _ y _ h, H h

lemma fiber_ncard_ne_zero_iff_mem_image [finite s] {y : β}:
  {x | x ∈ s ∧ f x = y}.ncard ≠ 0 ↔ y ∈ f '' s :=
begin
  refine ⟨nonempty_of_ncard_ne_zero, _⟩,
  rintros ⟨y,hy,rfl⟩, 
  exact @ncard_ne_zero_of_mem _ _ y _ (by simpa),  
end 

@[simp] lemma ncard_map (f : α ↪ β) : 
  (f '' s).ncard = s.ncard := 
ncard_image_of_injective _ f.injective

@[simp] lemma ncard_subtype (P : α → Prop) (s : set α) : 
  {x : subtype P | (x : α) ∈ s}.ncard = (s ∩ (set_of P)).ncard :=
begin
  convert (ncard_image_of_injective _ (@subtype.coe_injective _ P)).symm, 
  ext, rw inter_comm, simp,  
end 

lemma ncard_inter_le_ncard_left (s t : set α) [finite s] : 
  (s ∩ t).ncard ≤ s.ncard :=
ncard_le_of_subset (inter_subset_left _ _)

lemma ncard_inter_le_ncard_right (s t : set α) [finite t] : 
  (s ∩ t).ncard ≤ t.ncard :=
ncard_le_of_subset (inter_subset_right _ _)

lemma eq_of_subset_of_ncard_le  [finite t] (h : s ⊆ t) (h₂ : t.ncard ≤ s.ncard) : 
  s = t :=
begin
  haveI := ((to_finite t).subset h).to_subtype,   
  rw ←@to_finset_inj _ _ _ (fintype.of_finite s) (fintype.of_finite t), 
  apply finset.eq_of_subset_of_card_le,
  { simpa, }, 
  rwa [←ncard_eq_to_finset_card, ←ncard_eq_to_finset_card], 
end 

lemma subset_iff_eq_of_ncard_le [finite t] (h : t.ncard ≤ s.ncard) : 
  s ⊆ t ↔ s = t :=
⟨λ hst, eq_of_subset_of_ncard_le hst h, eq.subset'⟩

lemma map_eq_of_subset [finite s] {f : α ↪ α} (hs : f '' s ⊆ s) : f '' s = s :=
  eq_of_subset_of_ncard_le hs (ncard_map _).ge

lemma set_of_ncard_eq {P : α → Prop} [finite s] (h : {x ∈ s | P x}.ncard = s.ncard) (ha : a ∈ s) :
  P a :=
sep_eq_self_iff_mem_true.mp (eq_of_subset_of_ncard_le (by simp) h.symm.le) _ ha
  
lemma ncard_lt_ncard (h : s ⊂ t) [finite t] : s.ncard < t.ncard := 
begin
  haveI := ((to_finite t).subset h.subset).to_subtype, 
  simp_rw [ncard_eq_to_finset_card],
  apply finset.card_lt_card, 
  simpa, 
end 

lemma ncard_eq_of_bijective [finite s] {n : ℕ} (f : ∀ i, i < n → α) 
  (hf : ∀ a ∈ s, ∃ i, ∃ h : i < n, f i h = a)
  (hf' : ∀ i (h : i < n), f i h ∈ s) 
  (f_inj : ∀ i j (hi : i < n) (hj : j < n), f i hi = f j hj → i = j) :
  s.ncard = n :=
begin
  rw ncard_eq_to_finset_card, 
  apply finset.card_eq_of_bijective, 
  all_goals {simpa}, 
end 

lemma ncard_congr {t : set β} [finite s] (f : Π a ∈ s, β) (h₁ : ∀ a ha, f a ha ∈ t)
(h₂ : ∀ a b ha hb, f a ha = f b hb → a = b) (h₃ : ∀ b ∈ t, ∃ a ha, f a ha = b) :
  s.ncard = t.ncard :=
begin
  set f' : s → t := λ x, ⟨f x.1 x.2, h₁ _ _⟩ with hf',
  have hbij : f'.bijective, 
  { split, 
    { rintros ⟨x,hx⟩ ⟨y,hy⟩ hxy, 
      simp only [hf', subtype.val_eq_coe, subtype.coe_mk, subtype.mk_eq_mk] at hxy ⊢, 
      apply h₂ _ _ hx hy hxy},
    rintro ⟨y,hy⟩, 
    obtain ⟨a, ha, rfl⟩ := h₃ y hy, 
    simp only [subtype.val_eq_coe, subtype.coe_mk, subtype.mk_eq_mk, set_coe.exists],
    exact ⟨_,ha,rfl⟩},
  haveI := @fintype.of_finite _ (finite.of_bijective hbij), 
  haveI := fintype.of_finite s, 
  convert fintype.card_of_bijective hbij; 
  rw [ncard_def, nat.card_eq_fintype_card],
end 

lemma ncard_le_ncard_of_inj_on {t : set β} [finite t] (f : α → β) (hf : ∀ a ∈ s, f a ∈ t)
(f_inj : inj_on f s) :
  s.ncard ≤ t.ncard :=
begin
  cases s.finite_or_infinite, 
  { haveI := h.to_subtype,
    simp_rw [ncard_eq_to_finset_card],
    exact finset.card_le_card_of_inj_on f (by simpa) (by simpa)},
  convert nat.zero_le _, 
  rw h.ncard_eq_zero, 
end 

lemma exists_ne_map_eq_of_ncard_lt_of_maps_to {t : set β} [finite t] (hc : t.ncard < s.ncard)
{f : α → β} (hf : ∀ a ∈ s, f a ∈ t) :
  ∃ (x ∈ s) (y ∈ s), x ≠ y ∧ f x = f y :=
begin
  by_contra h', 
  simp only [ne.def, exists_prop, not_exists, not_and, not_imp_not] at h', 
  exact (ncard_le_ncard_of_inj_on f hf h').not_lt hc, 
end

lemma le_ncard_of_inj_on_range [finite s] {n : ℕ} (f : ℕ → α) (hf : ∀ i < n, f i ∈ s)
  (f_inj : ∀ (i < n) (j < n), f i = f j → i = j) :
  n ≤ s.ncard :=
by {rw ncard_eq_to_finset_card, apply finset.le_card_of_inj_on_range; simpa}

lemma surj_on_of_inj_on_of_ncard_le {t : set β} [finite t] (f : Π a ∈ s, β) 
(hf : ∀ a ha, f a ha ∈ t) (hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂) 
(hst : t.ncard ≤ s.ncard) :
  ∀ b ∈ t, ∃ a ha, b = f a ha :=
begin
  intros b hb, 
  set f' : s → t := λ x, ⟨f x.1 x.2, hf _ _⟩ with hf', 
  have finj: f'.injective, 
  { rintros ⟨x,hx⟩ ⟨y,hy⟩ hxy, 
    simp only [hf', subtype.val_eq_coe, subtype.coe_mk, subtype.mk_eq_mk] at hxy ⊢, 
    apply hinj _ _ hx hy hxy}, 
  haveI := fintype.of_finite t, 
  haveI := fintype.of_injective f' finj,
  simp_rw [ncard_eq_to_finset_card] at hst, 
  set f'' : ∀ a, a ∈ s.to_finset → β := λ a h, f a (by simpa using h) with hf'',
  convert @finset.surj_on_of_inj_on_of_card_le _ _ _ t.to_finset f'' (by simpa) (by simpa) 
    (by convert hst) b (by simpa), 
  simp, 
end 

lemma inj_on_of_surj_on_of_ncard_le [finite s] {t : set β} (f : Π a ∈ s, β) 
  (hf : ∀ a ha, f a ha ∈ t) (hsurj : ∀ b ∈ t, ∃ a ha, b = f a ha) (hst : s.ncard ≤ t.ncard) 
  ⦃a₁ a₂⦄ (ha₁ : a₁ ∈ s) (ha₂ : a₂ ∈ s) (ha₁a₂: f a₁ ha₁ = f a₂ ha₂) :
  a₁ = a₂ :=
begin
   set f' : s → t := λ x, ⟨f x.1 x.2, hf _ _⟩ with hf',
  have hsurj : f'.surjective, 
  { rintro ⟨y,hy⟩, 
    obtain ⟨a, ha, rfl⟩ := hsurj y hy, 
    simp only [subtype.val_eq_coe, subtype.coe_mk, subtype.mk_eq_mk, set_coe.exists],
    exact ⟨_,ha,rfl⟩},
  haveI := fintype.of_finite s, 
  haveI := fintype.of_surjective _ hsurj, 
  simp_rw [ncard_eq_to_finset_card] at hst, 
  set f'' : ∀ a, a ∈ s.to_finset → β := λ a h, f a (by simpa using h) with hf'',
  exact @finset.inj_on_of_surj_on_of_card_le _ _ _ t.to_finset f'' (by simpa) (by simpa) 
    (by convert hst) a₁ a₂ (by simpa) (by simpa) (by simpa), 
end 

section lattice

lemma ncard_union_add_ncard_inter (s t : set α) [finite s] [finite t] : 
  (s ∪ t).ncard + (s ∩ t).ncard = s.ncard + t.ncard :=
begin
  haveI := finite.set.finite_union s t, 
  haveI := finite.set.finite_inter_of_left s t, 
  haveI := fintype.of_finite s, 
  haveI := fintype.of_finite t, 
  simp_rw [ncard_eq_to_finset_card, to_finset_union, to_finset_inter], 
  convert finset.card_union_add_card_inter _ _, 
end 

lemma ncard_inter_add_ncard_union (s t : set α) [finite s] [finite t] : 
  (s ∩ t).ncard + (s ∪ t).ncard = s.ncard + t.ncard :=
by rw [add_comm, ncard_union_add_ncard_inter]

lemma ncard_union_le (s t : set α) : 
  (s ∪ t).ncard ≤ s.ncard + t.ncard :=
begin
  cases (s ∪ t).finite_or_infinite,
  { haveI := h.to_subtype, 
    haveI := finite.set.subset _ (subset_union_left s t),
    haveI := finite.set.subset _ (subset_union_right s t),  
    haveI := fintype.of_finite s,
    haveI := fintype.of_finite t, 
    simp_rw [ncard_eq_to_finset_card, to_finset_union],
    convert finset.card_union_le _ _, }, 
  convert nat.zero_le _, 
  rw h.ncard_eq_zero, 
end 

lemma ncard_union_eq [finite s] [finite t] (h : disjoint s t) : 
  (s ∪ t).ncard = s.ncard + t.ncard :=
begin
  haveI := finite.set.finite_union s t,   
  haveI := fintype.of_finite s,
  haveI := fintype.of_finite t,
  simp_rw [ncard_eq_to_finset_card, to_finset_union], 
  convert finset.card_union_eq _,  
  simpa, 
end 

lemma ncard_diff_add_ncard_eq_ncard [finite t] (h : s ⊆ t) : 
  (t \ s).ncard + s.ncard = t.ncard :=
begin
  have ht := to_finite t, 
  haveI := ((to_finite t).subset h).to_subtype,
  haveI := ((to_finite t).diff s).to_subtype,
  haveI := fintype.of_finite s, 
  haveI := fintype.of_finite t, 
  simp_rw [ncard_eq_to_finset_card],  rw to_finset_diff, 
  convert finset.card_sdiff_add_card_eq_card _,
  simpa,   
end 

lemma ncard_diff [finite t] (h : s ⊆ t) : 
  (t \ s).ncard = t.ncard - s.ncard := 
by rw [←ncard_diff_add_ncard_eq_ncard h, add_tsub_cancel_right] 

lemma ncard_le_ncard_diff_add_ncard (s t : set α) [finite t] : 
  s.ncard ≤ (s \ t).ncard + t.ncard :=
begin
  cases s.finite_or_infinite, 
  { haveI := h.to_subtype, 
    rw [←diff_inter_self_eq_diff, ←ncard_diff_add_ncard_eq_ncard (inter_subset_right t s),
      add_le_add_iff_left],
    apply ncard_inter_le_ncard_left},
  convert nat.zero_le _,
  rw h.ncard_eq_zero,  
end 

lemma le_ncard_diff (s t : set α) [finite s] : 
  t.ncard - s.ncard ≤ (t \ s).ncard :=
begin
  refine tsub_le_iff_left.mpr _, 
  rw add_comm, 
  apply ncard_le_ncard_diff_add_ncard,
end 

lemma ncard_sdiff_add_ncard (s t : set α) [finite s] [finite t] : 
  (s \ t).ncard + t.ncard = (s ∪ t).ncard :=
begin
  haveI := finite.set.finite_union s t,   
  rw [← (by {ext, simp} : (s ∪ t) \ t = s \ t), ncard_diff_add_ncard_eq_ncard], 
  apply subset_union_right, 
end 

end lattice

-- lemma filter_card_add_filter_neg_card_eq_card (p : α → Prop) [decidable_pred p] :
--   (s.filter p).card + (s.filter (not ∘ p)).card = s.card :=
-- by { classical, simp [←card_union_eq, filter_union_filter_neg_eq, disjoint_filter] }

-- /-- Given a set `A` and a set `B` inside it, we can shrink `A` to any appropriate size, and keep `B`
-- inside it. -/
-- lemma exists_intermediate_set {A B : finset α} (i : ℕ) (h₁ : i + card B ≤ card A) (h₂ : B ⊆ A) :
--   ∃ (C : finset α), B ⊆ C ∧ C ⊆ A ∧ card C = i + card B :=
-- begin
--   classical,
--   rcases nat.le.dest h₁ with ⟨k, _⟩,
--   clear h₁,
--   induction k with k ih generalizing A,
--   { exact ⟨A, h₂, subset.refl _, h.symm⟩ },
--   have : (A \ B).nonempty,
--   { rw [←card_pos, card_sdiff h₂, ←h, nat.add_right_comm,
--         add_tsub_cancel_right, nat.add_succ],
--     apply nat.succ_pos },
--   rcases this with ⟨a, ha⟩,
--   have z : i + card B + k = card (erase A a),
--   { rw [card_erase_of_mem (mem_sdiff.1 ha).1, ←h],
--     refl },
--   rcases ih _ z with ⟨B', hB', B'subA', cards⟩,
--   { exact ⟨B', hB', trans B'subA' (erase_subset _ _), cards⟩ },
--   { rintro t th,
--     apply mem_erase_of_ne_of_mem _ (h₂ th),
--     rintro rfl,
--     exact not_mem_sdiff_of_mem_right th ha }
-- end

-- /-- We can shrink `A` to any smaller size. -/
-- lemma exists_smaller_set (A : finset α) (i : ℕ) (h₁ : i ≤ card A) :
--   ∃ (B : finset α), B ⊆ A ∧ card B = i :=
-- let ⟨B, _, x₁, x₂⟩ := exists_intermediate_set i (by simpa) (empty_subset A) in ⟨B, x₁, x₂⟩

-- lemma exists_subset_or_subset_of_two_mul_lt_card [decidable_eq α] {X Y : finset α} {n : ℕ}
--   (hXY : 2 * n < (X ∪ Y).card) :
--   ∃ C : finset α, n < C.card ∧ (C ⊆ X ∨ C ⊆ Y) :=
-- begin
--   have h₁ : (X ∩ (Y \ X)).card = 0 := finset.card_eq_zero.mpr (finset.inter_sdiff_self X Y),
--   have h₂ : (X ∪ Y).card = X.card + (Y \ X).card,
--   { rw [←card_union_add_card_inter X (Y \ X), finset.union_sdiff_self_eq_union, h₁, add_zero] },
--   rw [h₂, two_mul] at hXY,
--   rcases lt_or_lt_of_add_lt_add hXY with h|h,
--   { exact ⟨X, h, or.inl (finset.subset.refl X)⟩ },
--   { exact ⟨Y \ X, h, or.inr (finset.sdiff_subset Y X)⟩ }
-- end

-- /-! ### Explicit description of a finset from its card -/

-- lemma card_eq_one : s.card = 1 ↔ ∃ a, s = {a} :=
-- by cases s; simp only [multiset.card_eq_one, finset.card, ←val_inj, singleton_val]

-- lemma exists_eq_insert_iff [decidable_eq α] {s t : finset α} :
--   (∃ a ∉ s, insert a s = t) ↔ s ⊆ t ∧ s.card + 1 = t.card :=
-- begin
--   split,
--   { rintro ⟨a, ha, rfl⟩,
--     exact ⟨subset_insert _ _, (card_insert_of_not_mem ha).symm⟩ },
--   { rintro ⟨hst, h⟩,
--     obtain ⟨a, ha⟩ : ∃ a, t \ s = {a},
--     { exact card_eq_one.1 (by rw [card_sdiff hst, ←h, add_tsub_cancel_left]) },
--     refine ⟨a, λ hs, (_ : a ∉ {a}) $ mem_singleton_self _,
--       by rw [insert_eq, ←ha, sdiff_union_of_subset hst]⟩,
--     rw ←ha,
--     exact not_mem_sdiff_of_mem_right hs }
-- end

-- lemma card_le_one : s.card ≤ 1 ↔ ∀ (a ∈ s) (b ∈ s), a = b :=
-- begin
--   obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty,
--   { simp },
--   refine (nat.succ_le_of_lt (card_pos.2 ⟨x, hx⟩)).le_iff_eq.trans (card_eq_one.trans ⟨_, _⟩),
--   { rintro ⟨y, rfl⟩,
--     simp },
--   { exact λ h, ⟨x, eq_singleton_iff_unique_mem.2 ⟨hx, λ y hy, h _ hy _ hx⟩⟩ }
-- end

-- lemma card_le_one_iff : s.card ≤ 1 ↔ ∀ {a b}, a ∈ s → b ∈ s → a = b := by { rw card_le_one, tauto }

-- lemma card_le_one_iff_subset_singleton [nonempty α] : s.card ≤ 1 ↔ ∃ (x : α), s ⊆ {x} :=
-- begin
--   refine ⟨λ H, _, _⟩,
--   { obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty,
--     { exact ⟨classical.arbitrary α, empty_subset _⟩ },
--     { exact ⟨x, λ y hy, by rw [card_le_one.1 H y hy x hx, mem_singleton]⟩ } },
--   { rintro ⟨x, hx⟩,
--     rw ←card_singleton x,
--     exact card_le_of_subset hx }
-- end

-- /-- A `finset` of a subsingleton type has cardinality at most one. -/
-- lemma card_le_one_of_subsingleton [subsingleton α] (s : finset α) : s.card ≤ 1 :=
-- finset.card_le_one_iff.2 $ λ _ _ _ _, subsingleton.elim _ _

-- lemma one_lt_card : 1 < s.card ↔ ∃ (a ∈ s) (b ∈ s), a ≠ b :=
-- by { rw ←not_iff_not, push_neg, exact card_le_one }

-- lemma one_lt_card_iff : 1 < s.card ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b :=
-- by { rw one_lt_card, simp only [exists_prop, exists_and_distrib_left] }

-- lemma two_lt_card_iff : 2 < s.card ↔ ∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c :=
-- begin
--   classical,
--   refine ⟨λ h, _, _⟩,
--   { obtain ⟨c, hc⟩ := card_pos.mp (zero_lt_two.trans h),
--     have : 1 < (s.erase c).card := by rwa [←add_lt_add_iff_right 1, card_erase_add_one hc],
--     obtain ⟨a, b, ha, hb, hab⟩ := one_lt_card_iff.mp this,
--     exact ⟨a, b, c, mem_of_mem_erase ha, mem_of_mem_erase hb, hc,
--       hab, ne_of_mem_erase ha, ne_of_mem_erase hb⟩ },
--   { rintros ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩,
--     rw [←card_erase_add_one hc, ←card_erase_add_one (mem_erase_of_ne_of_mem hbc hb),
--         ←card_erase_add_one (mem_erase_of_ne_of_mem hab (mem_erase_of_ne_of_mem hac ha))],
--     apply nat.le_add_left },
-- end

-- lemma two_lt_card : 2 < s.card ↔ ∃ (a ∈ s) (b ∈ s) (c ∈ s), a ≠ b ∧ a ≠ c ∧ b ≠ c :=
-- by simp_rw [two_lt_card_iff, exists_prop, exists_and_distrib_left]

-- lemma exists_ne_of_one_lt_card (hs : 1 < s.card) (a : α) : ∃ b, b ∈ s ∧ b ≠ a :=
-- begin
--   obtain ⟨x, hx, y, hy, hxy⟩ := finset.one_lt_card.mp hs,
--   by_cases ha : y = a,
--   { exact ⟨x, hx, ne_of_ne_of_eq hxy ha⟩ },
--   { exact ⟨y, hy, ha⟩ }
-- end

-- lemma card_eq_succ [decidable_eq α] : s.card = n + 1 ↔ ∃ a t, a ∉ t ∧ insert a t = s ∧ t.card = n :=
-- ⟨λ h,
--   let ⟨a, has⟩ := card_pos.mp (h.symm ▸ nat.zero_lt_succ _ : 0 < s.card) in
--     ⟨a, s.erase a, s.not_mem_erase a, insert_erase has,
--       by simp only [h, card_erase_of_mem has, add_tsub_cancel_right]⟩,
--   λ ⟨a, t, hat, s_eq, n_eq⟩, s_eq ▸ n_eq ▸ card_insert_of_not_mem hat⟩

-- lemma card_eq_two [decidable_eq α] : s.card = 2 ↔ ∃ x y, x ≠ y ∧ s = {x, y} :=
-- begin
--   split,
--   { rw card_eq_succ,
--     simp_rw [card_eq_one],
--     rintro ⟨a, _, hab, rfl, b, rfl⟩,
--     exact ⟨a, b, not_mem_singleton.1 hab, rfl⟩ },
--   { rintro ⟨x, y, h, rfl⟩,
--     exact card_doubleton h }
-- end

-- lemma card_eq_three [decidable_eq α] :
--   s.card = 3 ↔ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z} :=
-- begin
--   split,
--   { rw card_eq_succ,
--     simp_rw [card_eq_two],
--     rintro ⟨a, _, abc, rfl, b, c, bc, rfl⟩,
--     rw [mem_insert, mem_singleton, not_or_distrib] at abc,
--     exact ⟨a, b, c, abc.1, abc.2, bc, rfl⟩ },
--   { rintro ⟨x, y, z, xy, xz, yz, rfl⟩,
--     simp only [xy, xz, yz, mem_insert, card_insert_of_not_mem, not_false_iff, mem_singleton,
--       or_self, card_singleton] }
-- end

-- /-! ### Inductions -/

-- /-- Suppose that, given objects defined on all strict subsets of any finset `s`, one knows how to
-- define an object on `s`. Then one can inductively define an object on all finsets, starting from
-- the empty set and iterating. This can be used either to define data, or to prove properties. -/
-- def strong_induction {p : finset α → Sort*} (H : ∀ s, (∀ t ⊂ s, p t) → p s) :
--   ∀ (s : finset α), p s
-- | s := H s (λ t h, have t.card < s.card, from card_lt_card h, strong_induction t)
-- using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf card⟩]}

-- lemma strong_induction_eq {p : finset α → Sort*} (H : ∀ s, (∀ t ⊂ s, p t) → p s) (s : finset α) :
--   strong_induction H s = H s (λ t h, strong_induction H t) :=
-- by rw strong_induction

-- /-- Analogue of `strong_induction` with order of arguments swapped. -/
-- @[elab_as_eliminator] def strong_induction_on {p : finset α → Sort*} (s : finset α) :
--   (∀ s, (∀ t ⊂ s, p t) → p s) → p s :=
-- λ H, strong_induction H s

-- lemma strong_induction_on_eq {p : finset α → Sort*} (s : finset α) (H : ∀ s, (∀ t ⊂ s, p t) → p s) :
--   s.strong_induction_on H = H s (λ t h, t.strong_induction_on H) :=
-- by { dunfold strong_induction_on, rw strong_induction }

-- @[elab_as_eliminator] lemma case_strong_induction_on [decidable_eq α] {p : finset α → Prop}
--   (s : finset α) (h₀ : p ∅) (h₁ : ∀ a s, a ∉ s → (∀ t ⊆ s, p t) → p (insert a s)) :
--   p s :=
-- finset.strong_induction_on s $ λ s,
-- finset.induction_on s (λ _, h₀) $ λ a s n _ ih, h₁ a s n $
-- λ t ss, ih _ (lt_of_le_of_lt ss (ssubset_insert n) : t < _)

-- /-- Suppose that, given that `p t` can be defined on all supersets of `s` of cardinality less than
-- `n`, one knows how to define `p s`. Then one can inductively define `p s` for all finsets `s` of
-- cardinality less than `n`, starting from finsets of card `n` and iterating. This
-- can be used either to define data, or to prove properties. -/
-- def strong_downward_induction {p : finset α → Sort*} {n : ℕ} (H : ∀ t₁, (∀ {t₂ : finset α},
--   t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁) :
--   ∀ (s : finset α), s.card ≤ n → p s
-- | s := H s (λ t ht h, have n - t.card < n - s.card,
--      from (tsub_lt_tsub_iff_left_of_le ht).2 (finset.card_lt_card h),
--   strong_downward_induction t ht)
-- using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ (t : finset α), n - t.card)⟩]}

-- lemma strong_downward_induction_eq {p : finset α → Sort*}
--   (H : ∀ t₁, (∀ {t₂ : finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁)
--   (s : finset α) :
--   strong_downward_induction H s = H s (λ t ht hst, strong_downward_induction H t ht) :=
-- by rw strong_downward_induction

-- /-- Analogue of `strong_downward_induction` with order of arguments swapped. -/
-- @[elab_as_eliminator] def strong_downward_induction_on {p : finset α → Sort*} (s : finset α)
--   (H : ∀ t₁, (∀ {t₂ : finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁) :
--   s.card ≤ n → p s :=
-- strong_downward_induction H s

-- lemma strong_downward_induction_on_eq {p : finset α → Sort*} (s : finset α) (H : ∀ t₁,
--   (∀ {t₂ : finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁) :
--   s.strong_downward_induction_on H = H s (λ t ht h, t.strong_downward_induction_on H ht) :=
-- by { dunfold strong_downward_induction_on, rw strong_downward_induction }

-- lemma lt_wf {α} : well_founded (@has_lt.lt (finset α) _) :=
-- have H : subrelation (@has_lt.lt (finset α) _)
--     (inv_image ( < ) card),
--   from λ x y hxy, card_lt_card hxy,
-- subrelation.wf H $ inv_image.wf _ $ nat.lt_wf

-- end finset

end set 

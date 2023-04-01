import data.finset.card

namespace finset
variables {α : Type*} {s t : finset α}

lemma exists_mem_sdiff_of_card_lt_card (h : s.card < t.card) : ∃ e, e ∈ t ∧ e ∉ s :=
begin
  refine by_contra (λ h', h.not_le (card_mono (λ x hx, _))),
  push_neg at h',
  exact h' _ hx,
end

variables [decidable_eq α]

@[simp] lemma card_inter_add_card_sdiff_eq_card (s t : finset α) :
  (s ∩ t).card + (s \ t).card = s.card :=
by {convert @card_sdiff_add_card_eq_card _ _ _ _ _; simp}

lemma card_sdiff_eq_card_sdiff_iff_card_eq_card : s.card = t.card ↔ (s \ t).card = (t \ s).card :=
by rw [←card_inter_add_card_sdiff_eq_card s t, ←card_inter_add_card_sdiff_eq_card t s,
    inter_comm, add_right_inj]

lemma card_le_card_iff_card_sdiff_le_card_sdiff : s.card ≤ t.card ↔ (s \ t).card ≤ (t \ s).card :=
by rw [←card_inter_add_card_sdiff_eq_card s t, ←card_inter_add_card_sdiff_eq_card t s,
  inter_comm, add_le_add_iff_left]

lemma card_lt_card_iff_card_sdiff_lt_card_sdiff : s.card < t.card ↔ (s \ t).card < (t \ s).card :=
by rw [←card_inter_add_card_sdiff_eq_card s t, ←card_inter_add_card_sdiff_eq_card t s,
    inter_comm, add_lt_add_iff_left]

end finset
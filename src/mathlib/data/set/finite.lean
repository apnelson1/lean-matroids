import data.set.finite

variables {α β : Type*}

namespace set

theorem finite.exists_minimal_wrt [partial_order β] (f : α → β) {s : set α} (h : s.finite) :
  s.nonempty → (∃ (a : α) (H : a ∈ s), ∀ (a' : α), a' ∈ s → f a' ≤ f a → f a = f a') :=
@set.finite.exists_maximal_wrt α (order_dual β) _ f s h

lemma finite.exists_maximal [finite α] [partial_order α] (P : α → Prop) (h : ∃ x, P x) :
  ∃ m, P m ∧ ∀ x, P x → m ≤ x → m = x :=
begin
  obtain ⟨m, hm,hm'⟩ := finite.exists_maximal_wrt (@id α) (set_of P) (to_finite _) h,
  exact ⟨m, hm, hm'⟩,
end

lemma finite.exists_minimal [finite α] [partial_order α] (P : α → Prop)
(h : ∃ x, P x) : ∃ m, P m ∧ ∀ x, P x → x ≤ m → m = x :=
@finite.exists_maximal (order_dual α) _ _ P h

lemma finite.exists_minimal_subset {s : set α} {P : set α → Prop} (hs : s.finite) (hsP : P s) :
  ∃ t ⊆ s, P t ∧ ∀ t' ⊂ t, ¬ P t' :=
begin
  haveI := hs.to_subtype,
  obtain ⟨t₀, ht₀, ht₀min⟩ := finite.exists_minimal (P ∘ set.image (coe : s → α)) ⟨univ, by simpa⟩,
  refine ⟨coe '' t₀, by simp, ht₀, λ t' ht' hPt', ht'.ne _⟩,
  have ht's : t' ⊆ s, from ht'.subset.trans (by simp),
  have ht'' := subtype.coe_image_of_subset ht's,
  simp_rw function.comp_app at ht₀ ht₀min,
  rw [ht₀min {x : s | ↑x ∈ t'} (by rwa ht''), ht''],
  convert @preimage_mono _ _ (coe : s → α)   _ _ ht'.subset,
  rw preimage_image_eq _ subtype.coe_injective,
end

lemma finite.strong_induction_on {s : set α} {P : set α → Prop} (hs : s.finite) 
(IH : ∀ t ⊆ s, (∀ t₀ ⊂ t, P t₀) → P t) : P s :=
begin
  by_contra' hs', 
  obtain ⟨s₀, hs₀, hmin⟩ := finite.exists_minimal_subset hs hs', 
  simp_rw [not_not] at hmin, 
  exact hmin.1 (IH _ hs₀ hmin.2), 
end 

end set
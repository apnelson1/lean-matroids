import data.finset.locally_finite
import data.nat.interval 
import order.minimal

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

lemma finite.maximals_nonempty_of_exists {s : set α} (hs : s.finite) (P : set α → Prop)
{s₀ : set α} (hs₀s : s₀ ⊆ s) (hs₀ : P s₀) : 
  (maximals (⊆) {t | t ⊆ s ∧ P t}).nonempty := 
begin
  haveI := hs.to_subtype, 
  obtain ⟨t, ht⟩ := finite.exists_maximal (P ∘ set.image (coe : s → α)) 
    ⟨coe ⁻¹' s₀, by rwa [function.comp_app, subtype.image_preimage_coe, 
      inter_eq_self_of_subset_left hs₀s] ⟩, 
  
  simp only [function.comp_app, le_eq_subset] at ht, 
  refine ⟨coe '' t, ⟨(image_subset_range _ _).trans_eq subtype.range_coe,ht.1⟩, 
    λ t' ht' htt', _⟩,
  obtain ⟨t',rfl⟩ := subset_range_iff_exists_image_eq.mp (ht'.1.trans_eq subtype.range_coe.symm), 
  rw ht.2 t' ht'.2 ((image_subset_image_iff subtype.coe_injective).mp htt'),
end 

/-- This seems a strict improvement over the nonprimed version in mathlib - only the image 
needs to be finite, not the set itself.  -/
lemma finite.exists_maximal_wrt' {α β : Type*} [partial_order β] (f : α → β) (s : set α) 
(h : (f '' s).finite) (h₀ : s.nonempty) : 
  (∃ (a : α) (H : a ∈ s), ∀ (a' : α), a' ∈ s → f a ≤ f a' → f a = f a') :=
begin
  obtain  ⟨_ ,⟨a,ha,rfl⟩, hmax⟩ := finite.exists_maximal_wrt id (f '' s) h (h₀.image f), 
  exact ⟨a, ha, λ a' ha' hf, hmax _ (mem_image_of_mem f ha') hf⟩, 
end 


/-- Is this somewhere in mathlib? Can't find it-/
lemma nat.finite_iff_exists_ub {s : set ℕ} : s.finite ↔ ∃ m, ∀ x ∈ s, x ≤ m := 
begin
  refine ⟨λ h, (eq_empty_or_nonempty s).elim (λ he, ⟨0, by simp [he]⟩) (λ hs, _), 
    λ ⟨m,hm⟩, {x | x ≤ m}.to_finite.subset hm⟩,

  refine (finite.exists_maximal_wrt id s h hs).imp (λ m hm x hxs, le_of_not_lt (λ hlt, _)), 
  obtain ⟨-, h⟩:= hm,  
  exact hlt.ne (h x hxs hlt.le), 
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
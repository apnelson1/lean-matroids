
-- various flavours of induction 

import  .int_lemmas 
----------------------------------------------------------------
open_locale classical 
noncomputable theory 

universe u 

open set 

variables {α : Type*} 

section numbers 

variables (P : ℤ → Prop)

/-- Strong induction (with base case 0) for the nonnegative integers -/
lemma nonneg_int_strong_induction : 
  P 0 → (∀ n, 0 < n → (∀ m, 0 ≤ m → m < n → P m) → P n) → (∀ n₀, 0 ≤ n₀ → P n₀) := 
begin
  intros h0 IH n₀ hn₀, 
  set Q : ℕ → Prop := λ s, (∀ t, t ≤ s → P t) with hQ,
  suffices : Q (n₀.to_nat), 

  have h' := this n₀.to_nat (le_of_eq _), 
  rw (int.to_nat_of_nonneg hn₀) at h', from h', refl,

  apply nat.case_strong_induction_on _, 
  refine λ t ht, _, 
  rw nat.eq_zero_of_le_zero ht, norm_cast, from h0, 

  intros n hn t ht, 
  cases (nat.eq_zero_or_pos t), 
  rw h, norm_cast, from h0, 

  apply IH t _, 
  intros m h0m hmt, 
  have := hn (m.to_nat) _ (m.to_nat) (le_refl _), 
  rw (int.to_nat_of_nonneg h0m) at this, from this,

  rw int.to_nat_le, 
  rw [←int.coe_nat_le_coe_nat_iff, ←int.coe_nat_add_one_out] at ht, linarith, 

  exact int.coe_nat_pos.mpr h, 
end

/-- Induction on nonnegative integers with base case 0, and inductive step n-1 → n -/
lemma nonneg_int_induction_minus : 
  P 0 → (∀ n, 0 < n → P (n-1) → P n) → (∀ n₀, 0 ≤ n₀ → P n₀) := 
begin
  intros h0 IH, 
  apply nonneg_int_strong_induction _ h0, 
  from λ n hn0 IHs, IH n hn0 (IHs _ (int.le_sub_one_of_lt hn0) (sub_one_lt _)),  
end

/-- Induction on nonnegative integers with base case 0, and inductive step n → n+1 -/
lemma nonneg_int_induction : 
  P 0 → (∀ n, 0 ≤ n → P n → P (n+1)) → (∀ n₀, 0 ≤ n₀ → P n₀) := 
begin
  refine λ h IHplus, (nonneg_int_induction_minus P h (λ n hn, _)), 
  have := λ hminus, IHplus (n-1) (int.le_sub_one_of_lt hn) hminus,  
  norm_num at this, assumption, 
end

lemma nat_induction_zero_one (P : ℕ → Prop) (n₀ : ℕ) : 
  P 0 → P 1 → (∀ n, 2 ≤ n → P (n-1) → P n) → P n₀ :=
begin
  intros h0 h1 hind, 
  induction n₀ with m,
  from h0, 
  cases nat.eq_zero_or_pos m, 
  rw h, from h1, 
  have : 2 ≤ m.succ := by {rw nat.succ_eq_add_one, linarith},
  from hind _ this n₀_ih, 
end

/-- Proves that P holds for all elements of a type α by 
    strong induction on the value of a nonnegative parameter f on α -/

lemma nonneg_int_strong_induction_param (P : α → Prop) (f : α → ℤ)
(f_nonneg : ∀ a : α, 0 ≤ f a) :
  (∀ a, f a = 0 → P a) → (∀ a : α, 0 < f a → (∀ a', f a' < f a → P a') → P a) → (∀ a, P a) :=
begin
  let Q : ℤ → Prop := λ s, ∀ a, f a = s → P a,
  intros h h', 
  suffices : ∀ n₀, 0 ≤ n₀ → Q n₀, 
    from λ a, this (f a) (f_nonneg _) _ rfl, 
  apply nonneg_int_strong_induction Q h,
  intros n hn hnI a ha,
  refine h' _ (by {rw ha, from hn}) (λ a' ha', _), 
  from hnI (f a') (f_nonneg a') (by {rw ←ha ,from ha'}) _ rfl,  
end

lemma min_counterexample_nonneg_int_param (P : α → Prop) (f : α → ℤ)
(f_nonneg : ∀ a : α, 0 ≤ f a) :
  ¬ (∀ a, P a) → ∃ x, (¬ P x ∧ ∀ x', f x' < f x → P x') :=
begin
  contrapose!, 
  refine λ h, nonneg_int_strong_induction_param P f f_nonneg 
    (λ a ha, by_contra (λ hn, _)) 
    (λ a ha h', by_contra (λ hn, (let ⟨a',h₁,h₂⟩ := h _ hn in h₂ (h' _ h₁)))),
  obtain ⟨a', h', -⟩ :=  h _ hn,
  have := f_nonneg a', 
    -- linarith should work here before the rw but for some reason it doesn't. Look into this.
  rw ha at h',
  linarith,   
end

end numbers 

 
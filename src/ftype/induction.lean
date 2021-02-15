
-- various flavours of induction 

import .basic .single .int_lemmas 
----------------------------------------------------------------
open_locale classical 
noncomputable theory 


open ftype set 

variables {A: ftype}

section numbers 

/-- Strong induction (with base case 0) for the nonnegative integers -/
lemma nonneg_int_strong_induction (P : ℤ → Prop) : 
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
lemma nonneg_int_induction_minus (P : ℤ → Prop): 
  P 0 → (∀ n, 0 < n → P (n-1) → P n) → (∀ n₀, 0 ≤ n₀ → P n₀) := 
begin
  intros h0 IH, 
  apply nonneg_int_strong_induction _ h0, 
  from λ n hn0 IHs, IH n hn0 (IHs _ (int.le_sub_one_of_lt hn0) (sub_one_lt _)),  
end

/-- Induction on nonnegative integers with base case 0, and inductive step n → n+1 -/
lemma nonneg_int_induction (P : ℤ → Prop): 
  P 0 → (∀ n, 0 ≤ n → P n → P (n+1)) → (∀ n₀, 0 ≤ n₀ → P n₀) := 
begin
  refine λ h IHplus, (nonneg_int_induction_minus P h (λ n hn, _)), 
  have := λ hminus, IHplus (n-1) (int.le_sub_one_of_lt hn) hminus,  
  norm_num at this, assumption, 
end


lemma nat_induction_zero_one (P : ℕ → Prop)(n₀ : ℕ): 
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

lemma nonneg_int_strong_induction_param {α : Type}(P : α → Prop)(f : α → ℤ)(f_nonneg : ∀ a : α, 0 ≤ f a):
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



end numbers 

section sets 


/-- P holds for all proper subsets of Y-/
def below (P : set A → Prop) (Y : set A) : Prop :=
  forall (X :  set A), X ⊂ Y → (P X)

/-- if P holds for all proper subsets of Y, it holds for Y-/
def augment (P : set A → Prop) : Prop :=
  forall (Y : set A), (below P Y) → (P Y)

lemma strong_induction (P : set A → Prop) :
  (augment P) → (forall (Z : set A), P Z) :=
begin
  intros h_augment, 
  let  Q : ℤ → Prop := λ n, ∀ Y : set A, size Y = n → P Y,
  suffices : ∀ n, 0 ≤ n → Q n,  
  from λ Z, this (size Z) (size_nonneg _)  Z rfl, 
  refine nonneg_int_strong_induction Q _ _,
  
  intros Y hY, rw [size_zero_iff_empty] at hY, rw hY, 
  refine h_augment _ _, 
  from λ X hX, false.elim (ssubset_empty _ hX), 
  intros n h0n hn X hXn, 
  refine h_augment _ _,
  intros Y hY, 
  refine hn (size Y) (size_nonneg Y) _ Y rfl, 
  rw ←hXn, 
  from size_strict_monotone hY, 
end

lemma minimal_example (P : set A → Prop){X : set A}: 
  (P X) → ∃ Y, Y ⊆ X ∧ P Y ∧ ∀ Z, Z ⊂ Y → ¬P Z := 
begin
  set minimal_P := λ (Y : set A), P Y ∧ ∀ (Z : set A), Z ⊂ Y → ¬ P Z with hmin, 
  revert X, refine strong_induction _ _, intros T hT hPT, 
  by_cases ∀ Z, Z ⊂ T → ¬P Z, use T, exact ⟨subset_refl T, ⟨hPT, h⟩⟩, 
  push_neg at h, rcases h with ⟨Z, ⟨hZT, hPZ⟩⟩, 
  specialize hT Z hZT hPZ, rcases hT with ⟨Y, ⟨hYZ, hQY⟩⟩, 
  use Y, exact ⟨subset.trans hYZ hZT.1, hQY⟩, 
end

lemma maximal_example (P : set A → Prop){X : set A}: 
  (P X) → ∃ Y, X ⊆ Y ∧ P Y ∧ ∀ Z, Y ⊂ Z → ¬P Z := 
begin
  intro h, rw ←compl_compl X at h, 
  rcases minimal_example (λ S, P Sᶜ) h with ⟨Y,⟨hY₁, hY₂, hY₃⟩⟩, 
  use Yᶜ, refine ⟨subset_compl_comm.mpr hY₁, hY₂,λ Z hZ, _⟩,  
  rw ←compl_compl Z, exact hY₃ Zᶜ (scompl_subset_comm.mp hZ), 
end

lemma maximal_example_from_empty (P : set A → Prop): 
  P ∅ → ∃ Y, P Y ∧ ∀ Z, Y ⊂ Z → ¬P Z := 
  λ h, by {rcases maximal_example P h with ⟨Y, ⟨_,h'⟩⟩, from ⟨Y,h'⟩  }

lemma maximal_example_aug (P : set A → Prop){X : set A}: 
  (P X) → ∃ Y, X ⊆ Y ∧ P Y ∧ ∀ (e : A), e ∉ Y → ¬P (Y ∪ e) := 
begin
  intro hPX, 
  rcases maximal_example P hPX with ⟨Y, ⟨hXY, ⟨hPY, hmax⟩⟩⟩, 
  from ⟨Y, ⟨hXY, ⟨hPY, λ e he, hmax (Y ∪ e) (ssub_of_add_nonelem he) ⟩⟩⟩,  
end 

lemma maximal_example_aug_from_empty (P : set A → Prop): 
  P ∅ → ∃ Y, P Y ∧ ∀ (e : A), e ∉ Y → ¬P (Y ∪ e) := 
  λ h, by {rcases maximal_example_aug P h with ⟨Y, ⟨_,h'⟩⟩, from ⟨Y,h'⟩}

lemma minimal_example_remove (P : set A → Prop){X : set A}: 
  (P X) → ∃ Y, Y ⊆ X ∧ P Y ∧ ∀ (e : A), e ∈ Y → ¬P (Y \ e) := 
begin
  intro hPX, 
  rcases minimal_example P hPX with ⟨Y, ⟨hXY, ⟨hPY, hmin⟩⟩⟩, 
  from ⟨Y, ⟨hXY, ⟨hPY, λ e he, hmin (Y \ e) (remove_single_ssubset he) ⟩⟩⟩,  
end 

/-lemma minimal_example_size (P : set A → Prop)(hP : set.nonempty P):
  ∃ X, P X ∧ ∀ Y, size Y < size X → ¬ P Y := 
begin
  by_contra h, push_neg at h, 
end-/

end sets 

 
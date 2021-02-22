import tactic 
----------------------------------------------------------------
open_locale classical big_operators
open set 

variables {α β : Type}[add_comm_monoid β]

lemma fin_sum_empty (f : α → β) : 
  ∑ (a : (∅ : set α)), f a = 0 :=  
finset.sum_empty 

lemma fin_sum_eq (f : α → β)(X : set α)[fintype X]: 
  ∑ (a : X), f a = ∑ a in X.to_finset, f a := 
let φ : X ↪ α := ⟨coe, subtype.coe_injective⟩ in (finset.sum_map (finset.univ) φ f).symm

lemma fin_sum_insert (f : α → β){X : set α}{e : α}(he : e ∉ X)[fintype ↥X][fintype ↥(X ∪ {e})]:
   ∑ (a : X ∪ {e}), f a = (∑ (a : X), f a) + f e :=
begin
  unfreezingI {obtain ⟨X', rfl⟩ := finite.exists_finset_coe ⟨‹fintype ↥X›⟩ },
  rw [fin_sum_eq, fin_sum_eq, add_comm, ←finset.sum_insert],
  { congr', ext, simp },
  simpa using he,
end

lemma induction_foo [fintype α](P : set α → Prop): 
  (P ∅) → (∀ (X : set α)(e : α), e ∉ X → P X → P (X ∪ {e})) → (∀ X, P X) := 
sorry 

lemma fin_sum_one_eq_card [fintype α](X : set α): 
  ∑ (a : X), (1 : α → ℤ) a = X.to_finset.card := 
begin
  revert X, apply induction_foo, 
  {rw [to_finset_card, empty_card'], convert fin_sum_empty _, }, 
  
  intros X e he hX, 
  -- rw fin_sum_insert _ he, 
  -- doesn't work 

  rw fin_sum_insert, swap, assumption, 
  --works

  sorry,
end
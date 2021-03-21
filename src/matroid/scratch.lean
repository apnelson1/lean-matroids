import tactic data.real.basic 
----------------------------------------------------------------\


--- ℕ = {0,1,2,3,4,5, ... }

def is_even (n : ℕ) := 
  ∃ (m : ℕ), n = 2*m 

lemma double_is_even (n : ℕ): 
  is_even (2*n) :=
begin
  unfold is_even, 
  use n,   
end

def is_prime (p : ℕ) :=
  ∀ a b : ℕ, (1 < a) → (1 < b) → a*b ≠ p  

  -- ((1< a) ∧ (1 < b)) → a*b ≠ p 

lemma six_not_prime : 
  ¬ is_prime 6 := 
begin
  unfold is_prime, 
  push_neg, 
  use 2, 
  use 3, 
  split, 
  norm_num, 
  split, 
  norm_num, 
  norm_num, 
end

theorem goldbach (n : ℕ) (hn : 2 < n) (h_even : is_even n): 
  ∃ p q, (is_prime p) ∧ (is_prime q) ∧ n = p + q := 
begin
  sorry, 
end 

theorem infinitely_many_primes (k : ℕ) : 
  ∃ p, is_prime p ∧ k < p := 
begin
  have gold := goldbach (2*k+4) (by {linarith}) (by {use k+2, linarith }), 
  obtain ⟨p, q, hp, hq, hpq⟩ := gold, 
  by_contra hn, push_neg at hn, 
  have hp' := hn p hp,   
  have hq' := hn q hq, 
  linarith, 
end

import tactic

def divides (a b : ℕ) : Prop :=  ∃ d, a*d = b 

def prime (p : ℕ) : Prop := (1 < p) ∧ (∀ x, divides x p → x = 1 ∨ x = p)

lemma even_not_prime (x : ℕ) (h : 1 < x) : ¬ prime (2*x) := 
λ h', (h'.2 2 ⟨_,rfl⟩).elim (λ _, by linarith) (λ _, h.ne (by linarith))


lemma foo (α : Type) (s t : set α) (h_squirrel : s.finite) (ht : t.finite) : 
  (s ∪ t).finite := 
 h_squirrel.union ht
-- begin
--   exact set.finite.union hs ht, 
-- end 

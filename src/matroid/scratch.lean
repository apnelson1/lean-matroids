import tactic 

variables {P Q R : ℕ → Prop}

lemma p_implies_r (n : ℕ) : P n → R n := sorry 

lemma q_implies_r (n : ℕ) : Q n → R n := sorry 

lemma r_implies_iff (n : ℕ) : R n → (P n ↔ Q n) := sorry 

exampl

lemma foo {n : ℕ} : (P n ↔ Q n) := 
begin
  suffices 
end 
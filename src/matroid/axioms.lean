
import boolalg.basic
open boolalg 
section rank 

variables {U : boolalg}

def satisfies_R0 : (U → ℤ) → Prop := 
  λ r, ∀ X, 0 ≤ r X 

def satisfies_R1 : (U → ℤ) → Prop := 
  λ r, ∀ X, r X ≤ size X

def satisfies_R2 : (U → ℤ) → Prop := 
  λ r, ∀ X Y, X ⊆ Y → r X ≤ r Y 

def satisfies_R3 : (U → ℤ) → Prop := 
  λ r, ∀ X Y, r (X ∪ Y) + r (X ∩ Y) ≤ r X + r Y

@[ext] structure rankfun (B : boolalg) :=
  (r : B → ℤ)
  (R0 : satisfies_R0 r)
  (R1 : satisfies_R1 r)
  (R2 : ∀ (X Y : B), X ⊆ Y → r X ≤ r Y)
  (R3 : ∀ (X Y : B), r (X ∪ Y) + r (X ∩ Y) ≤ r X + r Y)

end rank 

end boolalg 
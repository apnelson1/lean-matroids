

example
  (a b c d : ℕ)
  (h₁ : a = b)
  (h₂ : c = a + b + 10)
  (h₃ : d + b = a - 3)
  (h₄ : c = 24)
    : a = 7 :=
begin
  subst h₁,
end

import tactic 

lemma foo {x : int} : 1 ≤ x → 1 ≤ x*x := sorry 

lemma bar (x y: int)(h : 1 ≤ x)(h' : 0 ≤ y) : 1 ≤ y + x*x  := 
begin
  linarith [foo h], 
end


import tactic 
----------------------------------------------------------------
open_locale classical big_operators
open set 

structure foo :=
(a : ℤ)

structure bar (c : ℤ):= 
(f : foo)
(h : c - 3 = f.a)

def bar.a {c : ℤ}(b : bar c) := b.f.a 

def sq (x : ℤ) := x*x

lemma baz1 {c : ℤ}(b : bar c) : 
  c = b.a + 3 := 
by {show c = b.f.a + 3, linarith [b.h]}

lemma baz2 (c : ℤ)(b : bar c): 
  (sq c) + 5 = 10 :=
by {rw (baz1 b), }





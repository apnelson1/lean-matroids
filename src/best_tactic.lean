import boolalg  
import boolalg_ring
import init.meta.interactive_base

open boolalg
variables {A : boolalg} (X : A)

namespace freealg
--variables (n : nat)
-- 
def freealg : nat → Type
| 0 := bool
| (n+1) := (freealg n) × (freealg n)

def zero : forall {n : nat}, (freealg n)
| 0 := ff
| (n+1) := (zero, zero)

def one : forall {n : nat}, (freealg n)
| 0 := tt
| (n+1) := (one, one)

lemma test (n m : nat) (hn : n < m+1 ) (hn' : n ≠ m) : n < m := array.push_back_idx hn hn'

def var : forall {n : nat} {i : nat}, (i < n) → (freealg n)
| 0 i Hi := false.elim (nat.not_lt_zero i Hi)
| (n+1) i Hi := if hin : (i = n) then (one, zero) 
                                 else let v : freealg n := var (nat.lt_of_le_and_ne (nat.le_of_lt_succ Hi) hin ) in (v, v)

def plus : forall {n : nat}, (freealg n) → (freealg n) → (freealg n)
| 0 a b := bxor a b 
| (n+1) a b := (plus a.1 b.1, plus a.2 b.2)

def times : forall {n : nat}, (freealg n) → (freealg n) → (freealg n)
| 0 a b := band a b
| (n+1) a b := (times a.1 b.1, times a.2 b.2)

def map : forall (n : nat), (nat → A) → (freealg n) → A 
| 0 vars ff := 0
| 0 vars tt := 1
| (n+1) vars a := (map n vars a.1)*(vars n) + (map n vars a.2)*(vars n + 1)

lemma on_zero (n : nat)(vars : nat → A) : 0 = map n vars zero :=
  by {apply eq.symm, induction n with n IH IH, refl, unfold map zero, rw IH, simp}
  
lemma on_one (n : nat)(vars : nat → A) : 1 = map n vars one :=
  by {apply eq.symm, induction n with n IH IH, refl, unfold map one, rw IH, simp}

lemma on_var (n i : nat)(vars : nat → A)(hi : i < n) : vars i = map n vars (var hi) :=
begin
  apply eq.symm, induction n with n IH,  
  --base case
  exact false.elim (nat.not_lt_zero i hi),
  
  --successor case
  unfold map var,  
  by_cases i = n,
  {split_ifs, rw [←on_one, ←on_zero, h], simp only [times_one, mult_comm, zero_times, plus_zero]},
  {specialize IH (nat.lt_of_le_and_ne (nat.le_of_lt_succ hi) h),  split_ifs, rw IH, simp only [distrib_cancel]}
end

lemma on_plus (n : nat)(vars : nat → A)(a b : freealg n) :map n vars a + map n vars b = map n vars (plus a b)  := 
begin
  apply eq.symm, induction n with n IH, 
  --base case
  {unfold plus, cases a; cases b; unfold map; simp; refl },
  -- successor case 
  {unfold map plus, rw [IH a.1 b.1, IH a.2 b.2], ring SOP}
end

lemma on_times (n : nat)(vars : nat → A)(a b : freealg n) :  map n vars a * map n vars b = map n vars (times a b) := 
begin
  apply eq.symm, induction n with n IH, 
  {unfold times, cases a; cases b; unfold map; simp; refl},
  {unfold map times, rw [IH a.1 b.1, IH a.2 b.2, ←expand_product]}
end

lemma foo (X : A):  Xᶜᶜᶜᶜ = X :=
begin
  let vars := λ n : nat, X, 
  set_to_ring_eqn,
  have := on_zero 1 vars,
  have : X = _ := on_var 1 0 vars zero_lt_one,
  rw this, 
  --erw [(rfl : X = vars 1)], --, on_var vars (one_lt_two)],
  simp only [on_zero 1 vars , on_one 1 vars, on_plus 1 vars, on_times 1 vars],
  refl, 
  
end


lemma bar (X Y Z P Q W: A): (X ∪ (Y ∪ Z)) ∪ ((W ∩ P ∩ Q)ᶜ ∪ (P ∪ W ∪ Q)) = ⊤ :=
begin
  let vars := λ n : nat, if (n = 0) then X 
                         else if (n = 1) then Y 
                         else if (n = 2) then Z
                         else if (n = 3) then P
                         else if (n = 4) then W
                         else Q, 
  set_to_ring_eqn, 
  
  have hx : X = _ := on_var _ _ vars (by norm_num : 0 < 6),
  have hy : Y = _ := on_var _ _ vars (by norm_num : 1 < 6),
  have hz : Z = _ := on_var _ _ vars (by norm_num : 2 < 6),
  have hp : P = _ := on_var _ _ vars (by norm_num : 3 < 6),
  have hw : W = _ := on_var _ _ vars (by norm_num : 4 < 6),
  have hq : Q = _ := on_var _ _ vars (by norm_num : 5 < 6),

  rw [hx, hy, hz, hw, hp, hq],
  
  simp only [on_zero 6 vars , on_one 6 vars, on_plus 6 vars, on_times 6 vars],
  refl, 
end
end freealg

open interactive
open lean.parser
meta def ids_list : lean.parser (list name) := types.list_of ident

  
meta def tactic.interactive.introduce_varmap (vars : parse ids_list) : tactic unit := do
  tactic.trace vars

lemma baz (A : boolalg) : false := begin
  introduce_varmap [a,b,c],
  --have hx : X = _ := on_var _ _ vars (by norm_num : 0 < 6),
end


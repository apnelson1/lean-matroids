import boolalg  
import boolalg_ring

open boolalg

----------------------------------------------------------------

namespace freealg
variables {A : boolalg} -- {n : nat}

def freealg : nat → Type
| 0 := bool
| (n+1) := (freealg n) × (freealg n)

def zero : forall {n : nat}, (freealg n)
| 0 := ff
| (n+1) := (zero, zero)

def one : forall {n : nat}, (freealg n)
| 0 := tt
| (n+1) := (one, one)

def var : forall {n : nat} (i : nat), (i < n) → (freealg n)
| 0 i Hi := false.elim (nat.not_lt_zero i Hi)
| (n+1) 0 Hi := (one, zero)
| (n+1) (i+1) Hi := let coeff : freealg n := var i (nat.lt_of_succ_lt_succ Hi) in (coeff, coeff)

def plus : forall {n : nat}, (freealg n) → (freealg n) → (freealg n)
| 0 a b := bxor a b 
| (n+1) a b := (plus a.1 b.1, plus a.2 b.2)

def times : forall {n : nat}, (freealg n) → (freealg n) → (freealg n)
| 0 a b := band a b
| (n+1) a b := (times a.1 b.1, times a.2 b.2)

def map : forall {n : nat} (V : vector A n), (freealg n) → A
| 0 V ff := 0
| 0 V tt := 1
| (n+1) V a := (map V.tail a.1) * V.head + (map V.tail a.2) * (V.head + 1)

lemma on_zero : forall {n : nat} (V : vector A n),
0 = map V zero
  | 0 V := rfl
  | (n+1) V := calc
      0   = 0 * V.head + 0 * (V.head + 1)                                 : by ring
      ... = (map V.tail zero) * V.head + (map V.tail zero) * (V.head + 1) : by rw on_zero

lemma on_one : forall {n : nat} (V : vector A n),
1 = map V one
  | 0 V := rfl
  | (n+1) V := calc
      1   = V.head + (V.head + 1)                                       : (plus_self_left _ _).symm
      ... = 1 * V.head + 1 * (V.head + 1)                               : by ring
      ... = (map V.tail one) * V.head + (map V.tail one) * (V.head + 1) : by rw on_one

lemma on_var : forall {n : nat} (V : vector A n) (i : nat) (Hi : i < n),
V.nth ⟨i, Hi⟩ = map V (var i Hi)
  | 0 V i Hi := false.elim (nat.not_lt_zero i Hi)
  | (n+1) V 0 Hi := calc
      V.nth ⟨0, Hi⟩ = V.head                                                       : by simp
      ...           = 1 * V.head + 0 * (V.head + 1)                                : by ring
      ...           = (map V.tail one) * V.head + (map V.tail zero) * (V.head + 1) : by rw [on_zero, on_one]
  | (n+1) V (i+1) Hi := let
      Hip : (i < n) := nat.lt_of_succ_lt_succ Hi,
      tail_var := map V.tail (var i Hip)
      in calc V.nth ⟨i + 1, Hi⟩ = V.tail.nth ⟨i, Hip⟩                         : by rw [vector.nth_tail, fin.succ.equations._eqn_1]
      ...                       = tail_var                                    : on_var _ _ _
      ...                       = _                                           : (plus_self_left (tail_var * V.head) _).symm
      ...                       = tail_var * V.head + tail_var * (V.head + 1) : by ring


/-
structure map {n : nat} (V : vector A n) :=
  (f : freealg n → A)
  (on_zero : 0 = f zero)
  (on_one : 1 = f one)
  (on_var (i : nat) (Hi : i < n) : V.nth ⟨i, Hi⟩ = f (var i Hi))
  (on_plus (a b : freealg n) : (f a) + (f b) = f (plus a b))
  (on_times (a b : freealg n) : (f a) * (f b) = f (times a b))

def map.from_vector {n : nat} (V : vector A n) : map V := {
  f := (fun a, _),
  on_zero := _,
  on_one := _,
  on_var := _,
  on_plus := _,
  on_times := _,
}
-/

end /-namespace-/ freealg

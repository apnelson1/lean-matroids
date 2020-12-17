import boolalg  
import boolalg_ring

open boolalg
variables {A : boolalg} (X : A)

inductive freealg0 : Type
| zero 
| one

namespace freealg0

def plus : freealg0 → freealg0 → freealg0
| zero X := X
| one zero := one
| one one := zero 

def times : freealg0 → freealg0 → freealg0
| zero X := zero 
| one X := X

def map (A : boolalg) : freealg0 → A
| zero := 0
| one := 1

lemma on_zero : 0 = map A zero := rfl
lemma on_one : 1 = map A one := rfl

lemma on_plus (X Y : freealg0) :
  (map A X) + (map A Y) = map A (plus X Y) :=
begin
  cases X; cases Y;
  try {rw <- on_zero}; 
  try {rw <- on_one}; 
  simp only [plus] with bla; 
  refl,
end

lemma on_times (X Y : freealg0) :
  (map A X) * (map A Y) = map A (times X Y) :=
begin
  cases X; cases Y;
  try {rw <- on_zero}; 
  try {rw <- on_one}; 
  simp only [times] with bla;
  refl,
end

lemma foo : (⊥ : A)ᶜ = ⊤ :=
begin
  set_to_ring_eqn,
  simp only [on_zero, on_one, on_plus, on_times],
  refl,
end

end /-namespace-/ freealg0

----------------------------------------------------------------

def freealg1 : Type := bool × bool

namespace freealg1

def zero : freealg1 := (ff, ff)
def one : freealg1 := (tt, tt)

def plus : freealg1 → freealg1 → freealg1 :=
fun a b, (bxor a.1 b.1, bxor a.2 b.2)

def times : freealg1 → freealg1 → freealg1 :=
fun a b, (band a.1 b.1, band a.2 b.2)

def map : freealg1 → A
| (ff, ff) := 0
| (ff, tt) := X + 1
| (tt, ff) := X
| (tt, tt) := 1

def map2 : freealg1 → A :=
fun a, (if a.1 then X else 0) + (if a.2 then X+1 else 0)

lemma on_zero : 0 = map X zero := rfl
lemma on_one : 1 = map X one := rfl

lemma on_var : X = map X (tt, ff) := rfl

lemma on_plus (a b : freealg1) :
  (map X a) + (map X b) = map X (plus a b) :=
begin
  cases a; cases b; cases a_fst; cases b_fst; cases a_snd; cases b_snd;
  try {rw <- on_zero}; 
  try {rw <- on_one}; 
  simp only [map, plus] with bla; 
  try {refl}; simp with bla,
end

lemma on_times (a b : freealg1) :
  (map X a) * (map X b) = map X (times a b) :=
begin
  cases a; cases b; cases a_fst; cases b_fst; cases a_snd; cases b_snd;
  try {rw <- on_zero}; 
  try {rw <- on_one}; 
  simp only [map, times] with bla;
  simp with bla; try {refl}; ring SOP; simp only with bla; refl,
end

lemma foo : Xᶜᶜᶜᶜ = X :=
begin
  set_to_ring_eqn,
  rw on_var X,
  simp only [on_zero X, on_one X, on_plus X, on_times X],
  refl,
end


lemma bar : (Xᶜ ∪ Xᶜᶜ)ᶜ ∪ (X - (Xᶜ ∩ Xᶜᶜ)) ∩ X = X :=
begin
  set_to_ring_eqn,
  rw on_var X,
  simp only [on_zero X, on_one X, on_plus X, on_times X],
  refl,
end

end /-namespace-/ freealg1

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

lemma on_zero {n : nat}(vars : nat → A) : 0 = map n vars zero :=
  by {apply eq.symm, induction n with n IH IH, refl, unfold map zero, rw IH, simp}
  
lemma on_one {n : nat}(vars : nat → A) : 1 = map n vars one :=
  by {apply eq.symm, induction n with n IH IH, refl, unfold map one, rw IH, simp}

lemma on_var {n i : nat}(vars : nat → A)(hi : i < n) : vars i = map n vars (var hi) :=
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

lemma on_plus {n : nat}(vars : nat → A)(a b : freealg n) : map n vars (plus a b) = map n vars a + map n vars b := 
begin
  induction n with n IH, 
  --base case
  {unfold plus, cases a; cases b; unfold map; simp; refl },
  -- successor case 
  {unfold map plus, rw [IH a.1 b.1, IH a.2 b.2], ring SOP}
end

lemma on_times {n : nat}(vars : nat → A)(a b : freealg n) : map n vars (times a b) = map n vars a * map n vars b := 
begin
  induction n with n IH, 
  {unfold times, cases a; cases b; unfold map; simp; refl},
  {unfold map times, rw [IH a.1 b.1, IH a.2 b.2, ←expand_product]}
end

lemma foo (X : A):  Xᶜᶜᶜᶜ = X :=
begin
  let vars := λ n : nat, X, 
  set_to_ring_eqn,
  --erw [(rfl : X = vars 1)], --, on_var vars (one_lt_two)],
  simp only [on_zero vars , on_one vars, on_plus vars, on_times vars, on_var vars (one_lt_two)],
  refl,
end


end freealg

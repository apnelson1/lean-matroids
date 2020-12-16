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

def var : forall {n : nat} (i : nat), (i < n) → (freealg n)
| 0 i Hi := false.elim (nat.not_lt_zero i Hi)
| (n+1) 0 Hi := (one, zero)
| (n+1) (i+1) Hi := let v : freealg n := var i (nat.lt_of_succ_lt_succ Hi) in (v, v)

def plus : forall {n : nat}, (freealg n) → (freealg n) → (freealg n)
| 0 a b := bxor a b 
| (n+1) a b := (plus a.1 b.1, plus a.2 b.2)

def times : forall {n : nat}, (freealg n) → (freealg n) → (freealg n)
| 0 a b := band a b
| (n+1) a b := (times a.1 b.1, times a.2 b.2)

end freealg

import boolalg  
import boolalg_ring
import init.meta.interactive_base

open boolalg

----------------------------------------------------------------

namespace freealg
variables {A : boolalg}

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

lemma on_plus : forall {n : nat} (V : vector A n) (a b : freealg n),
(map V a) + (map V b) = map V (plus a b)
  | 0 V a b :=
      begin
        cases a; cases b; unfold map plus bxor; ring,
        exact two_eq_zero,
      end
  | (n+1) V a b :=
      begin
        unfold map plus,
        rw [←on_plus V.tail a.1 b.1, ←on_plus V.tail a.2 b.2],
        ring,
      end

lemma on_times : forall {n : nat} (V : vector A n) (a b : freealg n),
(map V a) * (map V b) = map V (times a b)
  | 0 V a b := by cases a; cases b; unfold map plus band; ring
  | (n+1) V a b :=
      begin
        unfold map times,
        rw [←on_times V.tail a.1 b.1, ←on_times V.tail a.2 b.2,←expand_product],
      end

----------------------------------------------------------------

lemma foo (X : A):  Xᶜᶜᶜᶜ = X :=
begin
  let vars := vector.cons X (vector.nil),
  set_to_ring_eqn,
  have := on_zero vars,
  have : X = _ := on_var vars 0 zero_lt_one,
  rw this, 
  --erw [(rfl : X = vars 1)], --, on_var vars (one_lt_two)],
  simp only [on_zero vars , on_one vars, on_plus vars, on_times vars],
  refl, 
end

end /-namespace-/ freealg


open interactive
open lean.parser


  --have hx : X = _ := on_var _ _ vars (by norm_num : 0 < 6),
open tactic
open tactic.interactive 
open freealg

meta def ids_list : lean.parser (list name) := types.list_of ident
meta def meta_build_vector : list pexpr -> pexpr
| [] := ``(vector.nil)
| (v :: vs) := ``(vector.cons %%v %%(meta_build_vector vs))
meta def list_with_idx {T : Type} : (list T) → nat -> list (nat × T)
| [] n := []
| (v :: vs) n := (n, v) :: list_with_idx vs (n + 1)


meta def tactic.interactive.introduce_varmap_rewrite (vname : parse ident) (vars : parse ids_list) : tactic unit :=
  do
    names <- vars.mmap (fun name, get_local name),
    («let» vname ``(vector _ %%(vars.length)) $ meta_build_vector (names.map to_pexpr)),
    mmap 
      (λ (pair : (nat × expr)),
        let name := prod.snd pair in
        let idx := prod.fst pair in
        do 
          vname_expr <- get_local vname,
          hname <- get_unused_name `Hv,
          («have» hname ``(%%name = _) ``(on_var %%vname_expr %%idx (by norm_num))),
          hname_expr <- get_local hname,
          tactic.try (rewrite_target hname_expr),
          return ())
      (list_with_idx names 0),
    return ()

meta def tactic.interactive.simplify_sets (sets : parse ids_list): tactic unit :=
  do
    -- TODO: actually check the goal is of the form of some boolalg equation
    --       also -- do something about hypotheses...
    vname <- get_unused_name `V,
    tactic.interactive.introduce_varmap_rewrite vname sets,
    vname_expr <- get_local vname,
    set_to_ring_eqn,
    simp none tt ([``(freealg.on_one %%vname_expr),
                   ``(freealg.on_plus %%vname_expr),
                   ``(freealg.on_times %%vname_expr),
                   ``(freealg.on_zero %%vname_expr),
                   ``(freealg.on_var %%vname_expr)].map simp_arg_type.expr)
                    list.nil loc.wildcard,
    refl

--#print tactic.interactive.simplify_sets 

lemma baz {A : boolalg} (X Y Z : A) : X = X := begin
  introduce_varmap_rewrite V [X, Y, Z],
  refl,
end

--set_option pp.notation false
--set_option pp.implicit false


lemma bar {A : boolalg} (X Y Z P Q W: A): (X ∪ (Y ∪ Z)) ∪ ((W ∩ P ∩ Q)ᶜ ∪ (P ∪ W ∪ Q)) = ⊤ :=
begin
  simplify_sets [X, Y, Z, P, Q, W],
end

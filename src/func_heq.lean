/-

Some toy examples of working with heterogeneous equality,
in particular for dependent functions and structures.

-/

import tactic.ext

#check @eq_rec_heq
/-
eq_rec_heq :
∀ {α : Sort u_1}
  {φ : α → Sort u_2}
  {a a' : α}
  (h : a = a')
  (p : φ a),
h.rec_on p == p

This seems to be the fundamental idea of heq:
Casting a term to another type (using eq.rec or similar)
necessarily gives something which can't be eq, but it can be heq.

The following lemma, if true, would give a partial converse:
-/
lemma converse (P Q : Sort*) (p : P) (q : Q) (h : P = Q) :
  (p == q) → (h.rec_on p = q) := sorry

/-
The following lemma gives an actual eq for type casting using eq.rec,
by casting both the argument type and the function input type
in a function application.

The key is on the line marked (*), which works because of two facts:
1. The proof (_ : A₁ = A₁) is automatically equal to (eq.refl A₁)
2. When eq.rec is applied to a proof of the form (eq.refl x), the
   term can be evaluated, getting rid of eq.rec
-/
lemma cast_func_apply_eq
  (A₁ A₂ B : Type)
  (h₁₂ : A₁ = A₂)
  (f : A₁ → B)
  (a : A₁)
:
  (@eq.rec Type A₁ (fun A, A → B) f A₂ h₁₂)
  (@eq.rec Type A₁ (fun A, A)     a A₂ h₁₂) =
  (f a)
:=
  @eq.rec Type A₁
  (fun A₃, forall (h₁₃ : A₁ = A₃),
    (@eq.rec Type A₁ (fun A, A → B) f A₃ h₁₃)
    (@eq.rec Type A₁ (fun A, A)     a A₃ h₁₃) =
    (f a))
  (fun (_ : A₁ = A₁), eq.refl (f a)) -- (*)
  A₂ h₁₂ h₁₂

/-
The following lemma can be used to prove that two functions with
different domains are heq (even when they can't be eq).

It concerns two partial functions from A to B,
f₁ : {a : A // P₁ a} → B
f₂ : {a : A // P₂ a} → B
where the two propositions are equivalent (∀ a : A, (P₁ a) ↔ (P₂ a)),
so that the domains are mathematically equal,
but not syntactically equal.

The main complication is that funext can only be applied to
functions whose domains are syntactically equal, so it's necessary
to cast back and forth between the two domains using eq.rec.
-/
lemma subtype_func_ext
  (A B : Type)
  (P₁ P₂ : A → Prop)
  (f₁ : subtype P₁ → B)
  (f₂ : subtype P₂ → B)
  (hP : P₁ = P₂)
  (hf : forall (a : A) (h₁ : P₁ a) (h₂ : P₂ a),
    (f₁ ⟨a, h₁⟩) = (f₂ ⟨a, h₂⟩))
:
  (f₁ == f₂)
:=
  let f (P : A → Prop) : (P₁ = P) → subtype P → B :=
    (@eq.rec (A → Prop) P₁ (fun P, subtype P → B) f₁ P)
  in @eq.rec (subtype P₂ → B) (f P₂ hP) (fun f, f₁ == f)
  -- rewrite (heq.refl : f₁ == f₁) into (_ : f₁ == hP.rec_on f₁)
  (@eq.rec (A → Prop) P₁ (fun P, forall h : P₁ = P, f₁ == f P h) (fun _, heq.refl f₁) P₂ hP hP)
  -- then prove that (hP.rec_on f₁ = f₂) using funext
  f₂
  (funext (@subtype.rec A P₂ (fun x, f P₂ hP x = f₂ x) (fun a h₂,
  let h₁ : P₁ a := (eq.rec h₂ hP.symm) in calc
  (f P₂ hP ⟨a, h₂⟩) = (f₁ ⟨a, h₁⟩) : (@eq.rec (A → Prop) P₁
                                       (fun P, forall h : P₁ = P, f P h ⟨a, eq.rec h₁ h⟩ = f₁ ⟨a, h₁⟩)
                                       (fun _, eq.refl (f₁ ⟨a, h₁⟩)) P₂ hP hP)
  ...               = (f₂ ⟨a, h₂⟩) : (hf a h₁ h₂))))

/-
The lemma subtype_func_ext might be used to show equality between
two structures which have function fields, as below.
-/
@[ext] structure bla :=
  (A : Type)
  (f : A → nat)

inductive AB | A | B
lemma distinct : AB.A ≠ AB.B := @AB.no_confusion _ _ _

def Aeq : Type := {x : AB // x = AB.A}
def Ane : Type := {x : AB // x ≠ AB.B}
lemma same : Aeq = Ane := 
  congr_arg (@subtype AB) (funext (@AB.rec (fun x, (x = AB.A) = (x ≠ AB.B))
  (propext (iff.intro (fun _, distinct) (fun _, eq.refl AB.A)))
  (propext (iff.intro (fun h _, distinct h.symm) (fun h, false.elim (h (eq.refl AB.B)))))))

def bla_eq : bla := {A := Aeq, f := (fun _, 0)}
def bla_ne : bla := {A := Ane, f := (fun _, 0)}

example : bla_eq = bla_ne := begin
  ext,
  exact same,
  exact same,
  intros aeq ane h, -- h : aeq == ane
  -- TODO: what now?
  sorry
end

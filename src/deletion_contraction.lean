/-
Goal: state and prove the relationship between deletion, contraction, and duality.
-/


-- (U : boolalg) (A B : U) : (A = B) → iso (subalg A) (subalg B)

-- (B₁ B₂ : boolalg) (f : iso B₁ B₂) : rankfun B₁ → rankfun B₂
-- singleton {F : fintype} : F → powersetalg F


import boolalg rankfun

open boolalg

def push {U : boolalg} (E : U) :
  {X : U // X ⊆ E} → subalg E :=
sorry

def pull {U : boolalg} (E : U) :
  subalg E → {X : U // X ⊆ E} :=
sorry

def dual {B : boolalg} :
  rankfun B → rankfun B :=
fun M, {
  r := (fun X, size X + M.r Xᶜ - M.r ⊤),
  R0 := sorry,
  R1 := sorry,
  R2 := sorry,
  R3 := sorry,
}

#check @subtype.map
/-
subtype.map :
Π {α : Sort u_1}
  {β : Sort u_2}
  {p : α → Prop}
  {q : β → Prop}
  (f : α → β),
  (∀ (a : α), p a → q (f a)) →
  subtype p →
subtype q
-/

def delete {U : boolalg} (D E : U) : (D ⊆ E) →
  rankfun (subalg E) → rankfun (subalg (Dᶜ ∩ E)) :=
fun hDE M, let
  emb : subalg (Dᶜ ∩ E) → subalg E := fun X, push E (subtype.map id _ (pull _ X))
in {
  r := (fun X, M.r (emb X)),
  R0 := sorry,
  R1 := sorry,
  R2 := sorry,
  R3 := sorry,
}

def contract {U : boolalg} (C E : U) : (C ⊆ E) →
  rankfun (subalg E) → rankfun (subalg (Cᶜ ∩ E)) :=
fun hCE M, let
  emb : subalg (Cᶜ ∩ E) → subalg E := sorry
in {
  r := (fun X, M.r ((emb X) ∪ C) - M.r C),  -- errors, need push/pull
  R0 := sorry,
  R1 := sorry,
  R2 := sorry,
  R3 := sorry,
}

-- I would prefer (S₁ ∪ S₂)ᶜ ∩ E in the output type, need to apply an iso
def compose {U : boolalg}
  (f₁ f₂ : forall (S E : U), (S ⊆ E) → rankfun (subalg E) → rankfun (subalg (Sᶜ ∩ E)))
  (S₁ S₂ E : U) : (S₁ ∩ S₂ = ⊥) → (S₁ ⊆ E) → (S₂ ⊆ E) → rankfun (subalg E) → rankfun (subalg (S₂ᶜ ∩ (S₁ᶜ ∩ E))) :=
fun hS₁S₂ hS₁E hS₂E M, let
  h : (S₂ ⊆ (S₁ᶜ ∩ E)) := sorry
in f₂ S₂ (S₁ᶜ ∩ E) h (f₁ S₁ E hS₁E M)

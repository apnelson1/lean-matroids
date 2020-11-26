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

/-- subalg Dᶜ .... -/
def delete {U : boolalg} (D E : U) : (D ⊆ E) →
  rankfun (subalg E) → rankfun (subalg (Dᶜ ∩ E)) :=
fun hDE M, let
  emb : embed (subalg (Dᶜ ∩ E)) (subalg E) := embed.from_nested_pair (inter_subset_right _ _),
  f := emb.f, 
  DE := push E ⟨D, hDE⟩
in {
  r := (fun X, M.r (f X)),
  R0 := λ X, by apply M.R0,
  R1 := λ X, by apply M.R1,
  R2 := λ X Y hXY, by apply M.R2; apply emb.on_subset; exact hXY,
  R3 := λ X Y, by apply M.R3,
}

def contract {U : boolalg} (C E : U) : (C ⊆ E) →
  rankfun (subalg E) → rankfun (subalg (Cᶜ ∩ E)) :=
fun hCE M, let
  emb : embed (subalg (Cᶜ ∩ E)) (subalg E) := embed.from_nested_pair (inter_subset_right _ _),
  f := emb.f, 
  CE := push E ⟨C, hCE⟩
in {
  r := (fun X, M.r ((f X) ∪ CE) - M.r CE),
  R0 := λ X, by linarith [M.R2 _ _ (by apply subset_union_right : CE ⊆ f X ∪ CE)],
  R1 := λ X, by linarith [emb.on_size X, M.R0 (f X ∩ CE), M.R3 (f X) CE, M.R1 (f X)],
  R2 := λ X Y hXY, by linarith[M.R2 (f X ∪ CE) (f Y ∪ CE) (subset_union_subset_left (f X) (f Y) CE (emb.on_subset hXY ))],
  R3 := λ X Y,
  begin
    have hu : (f X ∪ CE) ∪ (f Y ∪ CE) = f (X ∪ Y) ∪ CE := by rw [←union_distrib_union_left,←emb.on_union],
    have hi : (f X ∪ CE) ∩ (f Y ∪ CE) = f (X ∩ Y) ∪ CE := by rw [←union_distrib_right, ←emb.on_inter], 
    have hs := M.R3 (f X ∪ CE) (f Y ∪ CE), 
    rw [hu, hi] at hs,
    linarith [hs],      
  end,
}

/- TODO: coerce stuff????
structure foo := 
  (f : ℤ → ℤ)
  (p : forall (i : ℤ), (0 ≤ i) → (0 ≤ f i))
instance foo.has_coe_to_fun : has_coe_to_fun foo := {
  F := fun _, ℤ → ℤ,
  coe := fun f, f.f
}

def foobar (x : ℤ) := x + 1
def foobar_s : foo := {
  f := foobar,
  p := begin
    intros x hx, 
    unfold foobar,
    linarith
  end
}
-/



/-instance embed.coe_to_fun {A B : boolalg.boolalg} : has_coe_to_fun (boolalg.embed A B) := {
  F := (λ _, A → B),
  coe := λ emb, emb.f,
}-/

-- I would prefer (S₁ ∪ S₂)ᶜ ∩ E in the output type, need to apply an iso
def compose {U : boolalg}
  (f₁ f₂ : forall (S E : U), (S ⊆ E) → rankfun (subalg E) → rankfun (subalg (Sᶜ ∩ E)))
  (S₁ S₂ E : U) : (S₁ ∩ S₂ = ⊥) → (S₁ ⊆ E) → (S₂ ⊆ E) → rankfun (subalg E) → rankfun (subalg (S₂ᶜ ∩ (S₁ᶜ ∩ E))) :=
fun hS₁S₂ hS₁E hS₂E M, let
  h : (S₂ ⊆ (S₁ᶜ ∩ E)) := sorry
in f₂ S₂ (S₁ᶜ ∩ E) h (f₁ S₁ E hS₁E M)

-- Next: state that M/C\D and M\D/C are equal, etc.


def apply_iso {A B : boolalg} : (iso A B) → (rankfun A) → (rankfun B) := sorry 


def deletion_contraction_commute {U : boolalg} (C D E : U)
  (hCD : C ∩ D = ⊥) (hCE : C ⊆ E) (hDE : D ⊆ E)
  (M : rankfun (subalg E)) :
let
  i₁ : iso (subalg (Dᶜ ∩ (Cᶜ ∩ E))) (subalg ((C ∪ D)ᶜ ∩ E)) := sorry,
  i₂ : iso (subalg (Cᶜ ∩ (Dᶜ ∩ E))) (subalg ((C ∪ D)ᶜ ∩ E)) := sorry,
  hDC : D ∩ C = ⊥ := sorry
in
  apply_iso i₁ (compose contract delete C D E hCD hCE hDE M) =  
  apply_iso i₂ (compose delete contract D C E hDC hDE hCE M) :=
sorry

#check (fun A B, A ≅ B)
/-
Goal: state and prove the relationship between deletion, contraction, and duality.

Existence of a normal form:
  expressions of the form M/C\D are closed under deletion and contraction,
  and together with M*/C\D they are closed under duality.

Current idea: define boolalg deletion map from (subalg E) to (subalg E-D).
-/

import boolalg rankfun
open boolalg

----------------------------------------------------------------

-- For this file, we'll define matroids as living inside a common universe U.
def matroid_on {U : boolalg} (E : U) : Type :=
  rankfun (subalg E)

----------------------------------------------------------------

section matroid_heq
variables
  {U : boolalg}
  {E₁ E₂ E₃ : U}
  {M₁ : matroid_on E₁}
  {M₂ : matroid_on E₂}
  {M₃ : matroid_on E₃}

-- Since we have a common universe, we can talk about matroid equality.
def matroid_heq (M₁ : matroid_on E₁) (M₂ : matroid_on E₂) : Prop :=
  (E₁ = E₂) ∧ forall (X : U) (h₁ : X ⊆ E₁) (h₂ : X ⊆ E₂),
  M₁.r ⟨X, h₁⟩ = M₂.r ⟨X, h₂⟩
notation M₁ ` ≅ ` M₂ := matroid_heq M₁ M₂

-- This is an equivalence relation, unsurprisingly: reflexive, symmetric, transitive.
lemma matroid_heq.refl {E : U} (M : matroid_on E) :
  (M ≅ M) :=
⟨rfl, fun _ _ _, rfl⟩

lemma matroid_heq.symm :
  (M₁ ≅ M₂) → (M₂ ≅ M₁) :=
fun ⟨hE, hr⟩, ⟨hE.symm, fun X h₂ h₁, (hr X h₁ h₂).symm⟩

lemma matroid_heq.trans :
  (M₁ ≅ M₂) → (M₂ ≅ M₃) → (M₁ ≅ M₃) :=
fun ⟨hE₁₂, hr₁₂⟩ ⟨hE₂₃, hr₂₃⟩, ⟨hE₁₂.trans hE₂₃, fun X h₁ h₃, let h₂ : X ⊆ E₂ := eq.rec h₁ hE₁₂ in (hr₁₂ X h₁ h₂).trans (hr₂₃ X h₂ h₃)⟩

-- If the ground sets are defeq, we can upgrade matroid_heq to an eq of rankfun.
lemma matroid_heq.to_eq {E : U} {M₁ M₂ : matroid_on E} :
  (M₁ ≅ M₂) → (M₁ = M₂) :=
fun ⟨_, hr⟩, rankfun.ext _ _ (funext (@subtype.rec _ _ (fun X, M₁.r X = M₂.r X) (fun X h, hr X h h)))

end /-section-/ matroid_heq

----------------------------------------------------------------

section dual
variables {U : boolalg} {E : U}

-- Every matroid has a dual.
def dual :
  matroid_on E → matroid_on E :=
fun M, {
  r := (fun X, size X + M.r Xᶜ - M.r ⊤),
  R0 := (fun X,
    calc 0 ≤ M.r X  + M.r Xᶜ - M.r (X ∪ Xᶜ) - M.r (X ∩ Xᶜ) : by linarith [M.R3 X Xᶜ]
    ...    = M.r X  + M.r Xᶜ - M.r ⊤        - M.r ⊥        : by rw [union_compl X, inter_compl X]
    ...    ≤ size X + M.r Xᶜ - M.r ⊤                       : by linarith [M.R1 X, rank_bot M]),
  R1 := (fun X, by linarith [M.R2 _ _ (subset_top Xᶜ)]),
  R2 := (fun X Y h, let
    Z := Xᶜ ∩ Y,
    h₁ :=
      calc Yᶜ ∪ Z = (Xᶜ ∩ Y) ∪ Yᶜ        : by apply union_comm
      ...         = (Xᶜ ∪ Yᶜ) ∩ (Y ∪ Yᶜ) : by apply union_distrib_right
      ...         = (X ∩ Y)ᶜ ∩ ⊤         : by rw [compl_inter X Y, union_compl Y]
      ...         = (X ∩ Y)ᶜ             : by apply inter_top
      ...         = Xᶜ                   : by rw [inter_subset h],
    h₂ :=
      calc Yᶜ ∩ Z = (Xᶜ ∩ Y) ∩ Yᶜ : by apply inter_comm
      ...         = Xᶜ ∩ (Y ∩ Yᶜ) : by apply inter_assoc
      ...         = Xᶜ ∩ ⊥        : by rw [inter_compl Y]
      ...         = ⊥             : by apply inter_bot,
    h₃ :=
      calc M.r Xᶜ = M.r Xᶜ + M.r ⊥              : by linarith [rank_bot M]
      ...         = M.r (Yᶜ ∪ Z) + M.r (Yᶜ ∩ Z) : by rw [h₁, h₂]
      ...         ≤ M.r Yᶜ + M.r Z              : by apply M.R3
      ...         ≤ M.r Yᶜ + size Z             : by linarith [M.R1 Z]
      ...         = M.r Yᶜ + size (Xᶜ ∩ Y)      : by refl
      ...         = M.r Yᶜ + size Y - size X    : by linarith [compl_inter_size_subset h]
    in by linarith),
  R3 := (fun X Y,
    calc  size (X ∪ Y) + M.r (X ∪ Y)ᶜ  - M.r ⊤ + (size (X ∩ Y) + M.r (X ∩ Y)ᶜ  - M.r ⊤)
        = size (X ∪ Y) + M.r (Xᶜ ∩ Yᶜ) - M.r ⊤ + (size (X ∩ Y) + M.r (Xᶜ ∪ Yᶜ) - M.r ⊤) : by rw [compl_union X Y, compl_inter X Y]
    ... ≤ size X       + M.r Xᶜ        - M.r ⊤ + (size Y       + M.r Yᶜ        - M.r ⊤) : by linarith [size_modular X Y, M.R3 Xᶜ Yᶜ]),
}

-- The double dual of a matroid is itself.
lemma dual_dual (M : matroid_on E) :
  dual (dual M) ≅ M :=
⟨rfl, fun X h₁ h₂, let
  X₁ : ↥(subalg E) := ⟨X, h₁⟩,
  X₂ : ↥(subalg E) := ⟨X, h₂⟩
in calc
  (dual (dual M)).r X₁ = size X₁ + (size X₁ᶜ + M.r X₁ᶜᶜ - M.r ⊤) - (size (⊤ : subalg E) + M.r ⊤ᶜ - M.r ⊤) : rfl
  ...                  = size X₁ + (size X₁ᶜ + M.r X₁ - M.r ⊤) - (size (⊤ : subalg E) + M.r ⊥ - M.r ⊤) : by simp only [compl_compl, boolalg.compl_top]
  ...                  = M.r X₁ : by linarith [size_compl X₁, rank_bot M]
  ...                  = M.r X₂ : rfl⟩

end /-section-/ dual

----------------------------------------------------------------

-- Deletion map between subalg's.
def subalg.delete {U : boolalg} {E : U} (D : subalg E) :
  subalg E → subalg (E - D.val) :=
subtype.map (fun X, X - D.val) (fun X (h : X ⊆ E), subset_inter_subset_left _ _ _ h)
-- Note that \setminus is not backslash.
notation X `∖` D := subalg.delete D X

----------------------------------------------------------------

section delete
variables {U : boolalg} {E : U}

def delete (D : subalg E) :
  matroid_on E → matroid_on (E - D.val) :=
fun M, let
  emb : embed (subalg (E - D.val)) (subalg E) := embed.from_nested_pair (inter_subset_left _ _)
in {
  r := (fun X, M.r (emb.f X)),
  R0 := (fun X,     by apply M.R0),
  R1 := (fun X,     by apply M.R1),
  R2 := (fun X Y h, by apply M.R2 ; apply emb.on_subset ; assumption),
  R3 := (fun X Y,   by rw [emb.on_inter X Y, emb.on_union X Y] ; apply M.R3),
}

lemma delete_delete (D₁ D₂ : subalg E) (M : matroid_on E) :
  delete (D₂∖D₁) (delete D₁ M) ≅ delete (D₁ ∪ D₂) M
:= ⟨
  (calc E - D₁.val - (D₂∖D₁).val
      = (E ∩ D₁.valᶜ) ∩ (D₂.val ∩ D₁.valᶜ)ᶜ : rfl
  ... = E ∩ (D₁.val ∪ (D₂.val ∩ D₁.valᶜ))ᶜ  : by simp only [inter_assoc, compl_union]
  ... = E ∩ (D₁.val ∪ D₂.val)ᶜ              : by simp only [union_distrib_left, union_compl, inter_top]
  ... = E - (D₁ ∪ D₂).val                   : rfl),
  (fun X h₁ h₂, rfl),
⟩

end /-section-/ delete

----------------------------------------------------------------

section contract
variables {U : boolalg} {E : U}

def contract (C : subalg E) :
  matroid_on E → matroid_on (E - C.val) :=
fun M, let
  emb : embed (subalg (E - C.val)) (subalg E) := embed.from_nested_pair (inter_subset_left _ _)
in {
  r := (fun X, M.r (emb.f X ∪ C) - M.r C),
  R0 := sorry,
  R1 := sorry,
  R2 := sorry,
  R3 := sorry,
}

lemma contract_contract (C₁ C₂ : subalg E) (M : matroid_on E) :
  contract (C₂∖C₁) (contract C₁ M) ≅ contract (C₁ ∪ C₂) M
:= ⟨
  (calc E - C₁.val - (C₂∖C₁).val
      = (E ∩ C₁.valᶜ) ∩ (C₂.val ∩ C₁.valᶜ)ᶜ : rfl
  ... = E ∩ (C₁.val ∪ (C₂.val ∩ C₁.valᶜ))ᶜ  : by simp only [inter_assoc, compl_union]
  ... = E ∩ (C₁.val ∪ C₂.val)ᶜ              : by simp only [union_distrib_left, union_compl, inter_top]
  ... = E - (C₁ ∪ C₂).val                   : rfl),
  (fun X h₁ h₂, let
  h₃ := calc (C₂.val ∩ C₁.valᶜ) ∪ C₁.val
           = C₁.val ∪ (C₁.valᶜ ∩ C₂.val)            : by simp only [inter_comm, union_comm]
       ... = (C₁.val ∪ C₁.valᶜ) ∩ (C₁.val ∪ C₂.val) : by apply union_distrib_left
       ... = C₁.val ∪ C₂.val                        : by simp only [union_compl, top_inter],
  h₄ := calc X ∪ (C₂.val ∩ C₁.valᶜ) ∪ C₁.val
           = X ∪ ((C₂.val ∩ C₁.valᶜ) ∪ C₁.val) : by apply union_assoc
       ... = X ∪ (C₁.val ∪ C₂.val)             : by rw [h₃],
  h₅ : (C₁.val ∪ C₂.val) ⊆ E := sorry,
  h₆ : X ∪ (C₁.val ∪ C₂.val) ⊆ E := sorry,
  h₇ (a b c : ℤ) : (a - c) - (b - c) = a - b := by linarith
  in calc (contract (C₂∖C₁) (contract C₁ M)).r ⟨X, h₁⟩
        = (contract C₁ M).r (⟨X, _⟩ ∪ (C₂∖C₁)) - (contract C₁ M).r (C₂∖C₁) : rfl
    ... = (M.r ⟨X ∪ (C₂.val ∩ C₁.valᶜ) ∪ C₁.val, _⟩ - M.r C₁)
        - (M.r ⟨    (C₂.val ∩ C₁.valᶜ) ∪ C₁.val, _⟩ - M.r C₁) : rfl
    ... = M.r ⟨X ∪ (C₂.val ∩ C₁.valᶜ) ∪ C₁.val, _⟩ - M.r ⟨(C₂.val ∩ C₁.valᶜ) ∪ C₁.val, _⟩ : h₇ _ _ _
    ... = (contract (C₁ ∪ C₂) M).r ⟨X, h₂⟩ : sorry),
⟩

end /-section-/ contract

----------------------------------------------------------------

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

/-
Goal: state and prove the relationship between deletion, contraction, and duality.

Existence of a normal form:
  expressions of the form M/C\D are closed under deletion and contraction,
  and together with M*/C\D they are closed under duality.

Current idea: define restriction and corestriction from U to subalg E
Then deletion and contraction are instances of these maps
And a sequence of deletions and contractions with disjoint arguments can be composed
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
variables {U : boolalg}

-- Every matroid has a dual.
def dual :
  rankfun U → rankfun U :=
fun M, {
  r := (fun X, size X + M.r Xᶜ - M.r ⊤),
  R0 := (fun X,
    calc 0 ≤ M.r X  + M.r Xᶜ - M.r (X ∪ Xᶜ) - M.r (X ∩ Xᶜ) : by linarith [M.R3 X Xᶜ]
    ...    = M.r X  + M.r Xᶜ - M.r ⊤        - M.r ⊥        : by rw [union_compl_self X, inter_compl_self X]
    ...    ≤ size X + M.r Xᶜ - M.r ⊤                       : by linarith [M.R1 X, rank_bot M]),
  R1 := (fun X, by linarith [M.R2 _ _ (subset_top Xᶜ)]),
  R2 := (fun X Y h, let
    Z := Xᶜ ∩ Y,
    h₁ :=
      calc Yᶜ ∪ Z = (Xᶜ ∩ Y) ∪ Yᶜ        : by apply union_comm
      ...         = (Xᶜ ∪ Yᶜ) ∩ (Y ∪ Yᶜ) : by apply union_distrib_right
      ...         = (X ∩ Y)ᶜ ∩ ⊤         : by rw [compl_inter X Y, union_compl_self Y]
      ...         = (X ∩ Y)ᶜ             : by apply inter_top
      ...         = Xᶜ                   : by rw [inter_subset h],
    h₂ :=
      calc Yᶜ ∩ Z = (Xᶜ ∩ Y) ∩ Yᶜ : by apply inter_comm
      ...         = Xᶜ ∩ (Y ∩ Yᶜ) : by apply inter_assoc
      ...         = Xᶜ ∩ ⊥        : by rw [inter_compl_self Y]
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
lemma dual_dual (M : rankfun U) :
  dual (dual M) = M :=
begin
  apply rankfun.ext, apply funext, intro X, calc
  (dual (dual M)).r X = size X + (size Xᶜ + M.r Xᶜᶜ - M.r ⊤) - (size (⊤ : U) + M.r ⊤ᶜ - M.r ⊤) : rfl
  ...                 = size X + (size Xᶜ + M.r X   - M.r ⊤) - (size (⊤ : U) + M.r ⊥  - M.r ⊤) : by rw [compl_compl, boolalg.compl_top]
  ...                 = M.r X                                                                  : by linarith [size_compl X, rank_bot M]
end

end /-section-/ dual

----------------------------------------------------------------

section restrict
variables {U : boolalg}

-- The restriction of a rankfun to a subalg is still a rankfun.
-- This is the same as deleting Eᶜ.
def restrict (E : U) :
  rankfun U → matroid_on E :=
fun M, {
  r := (fun X, M.r X.val),
  R0 := (by intro X;      apply M.R0),
  R1 := (by intro X;      apply M.R1),
  R2 := (by intros X Y h; apply M.R2; exact congr_arg subtype.val h),
  R3 := (by intros X Y;   apply M.R3),
}

end /-section-/ restrict

----------------------------------------------------------------

section corestrict
variables {U : boolalg}

-- The corestriction is the same as contracting Eᶜ.
def corestrict (E : U) :
  rankfun U → matroid_on E :=
fun M, {
  r := (fun X, M.r (X.val ∪ Eᶜ) - M.r Eᶜ),
  R0 := (by intro X; linarith [M.R2 _ _ (subset_union_right X.val Eᶜ)]),
  R1 := sorry,
  R2 := (by intros X Y h; linarith [M.R2 _ _ (subset_union_subset_left X.val Y.val Eᶜ (congr_arg subtype.val h))]),
  R3 := sorry,
}

end /-section-/ corestrict

----------------------------------------------------------------

-- Restriction and corestriction (so, deletion and contraction) are duals
lemma dual_restrict {U : boolalg} (E : U) (M : rankfun U) :
  dual (restrict E M) = corestrict E (dual M) :=
begin
  apply rankfun.ext, apply funext, intro X,
  have h₁ : size (X.val ∪ Eᶜ) = size X.val + size Eᶜ := size_union_of_inter_empty (calc
    X.val ∩ Eᶜ = (X.val ∩ {e}) ∩ Eᶜ : by rw [(eq.symm X.prop : X.val ∩ {e} = X.val)]
    ...        = X.val ∩ (E ∩ Eᶜ) : by apply inter_assoc
    ...        = X.val ∩ ⊥        : by rw [inter_compl_self]
    ...        = ⊥                : by apply inter_bot),
  have h₂ : Eᶜᶜ = E := compl_compl E,
  have h₃ := (calc
    (X.val ∪ Eᶜ)ᶜ = X.valᶜ ∩ Eᶜᶜ : by apply compl_union
    ...           = X.valᶜ ∩ {e}   : by rw [compl_compl]
    ...           = E ∩ X.valᶜ   : by apply inter_comm),
  calc
  (dual (restrict E M)).r X = size X.val + M.r (E ∩ X.valᶜ) - M.r E           : rfl
  ...                       = (size (X.val ∪ Eᶜ) + M.r (E ∩ X.valᶜ) - M.r ⊤)
                            - (size          Eᶜ  + M.r  E           - M.r ⊤)  : by linarith [h₁]
  ...                       = (size (X.val ∪ Eᶜ) + M.r (X.val ∪ Eᶜ)ᶜ - M.r ⊤)
                            - (size          Eᶜ  + M.r          Eᶜ ᶜ - M.r ⊤) : by rw [h₂, h₃]
  ...                       = (corestrict E (dual M)).r X                     : rfl
end

lemma restrict_dual {U : boolalg} (E : U) (M : rankfun U) :
  restrict E (dual M) = dual (corestrict E M) :=
begin
  apply rankfun.ext, apply funext, intro X,
  have h₁ : E ∪ Eᶜ = ⊤ := by apply union_compl_self,
  have h₂ := (calc
    (E ∩ X.valᶜ) ∪ Eᶜ = (E ∪ Eᶜ) ∩ (X.valᶜ ∪ Eᶜ) : by apply union_distrib_right
    ...               = X.valᶜ ∪ Eᶜ              : by simp only [union_compl_self, top_inter]
    ...               = (X.val ∩ {e})ᶜ             : by apply eq.symm; apply compl_inter
    ...               = X.valᶜ                   : by rw [(eq.symm X.prop : X.val ∩ {e} = X.val)]),
  calc
  (restrict E (dual M)).r X = size X.val + M.r X.valᶜ - M.r ⊤                 : rfl
  ...                       = size X.val + (M.r X.valᶜ - M.r Eᶜ)
                                         - (M.r ⊤      - M.r Eᶜ)              : by linarith
  ...                       = size X.val + (M.r ((E ∩ X.valᶜ) ∪ Eᶜ) - M.r Eᶜ)
                                         - (M.r ( E           ∪ Eᶜ) - M.r Eᶜ) : by rw [h₁, h₂]
  ...                       = (dual (corestrict E M)).r X                     : rfl

end

----------------------------------------------------------------

def unnest {U : boolalg} {E : U} {F : subalg E} :
  subalg F → subalg (F.val) :=
fun X, ⟨X.val.val, congr_arg subtype.val X.prop⟩

def nest {U : boolalg} {E : U} (F : subalg E) :
  subalg (F.val) → subalg F :=
fun X, ⟨⟨X.val, subset.trans X.prop F.prop⟩, subtype.ext X.prop⟩

-- Deletion and contraction commute.

def delete_then_contract {U : boolalg} (C D : U) (h_disjoint : C ∩ D = ⊥) :
  rankfun U → matroid_on (Cᶜ ∩ Dᶜ) :=
fun M, let
  M_del     : matroid_on Dᶜ := restrict Dᶜ M,
  E         : ↥(subalg Dᶜ)  := ⟨Cᶜ ∩ Dᶜ, by apply inter_subset_right⟩,
  M_del_con : matroid_on E  := corestrict E M_del
in {
  r := (fun X, M_del_con.r (nest E X)),
  R0 := (by intro X; apply M_del_con.R0),
  R1 := (by intro X; apply M_del_con.R1),
  R2 := (begin
    intros X Y h,
    apply M_del_con.R2,
    apply subtype.ext,
    apply subtype.ext,
    show X.val = X.val ∩ Y.val,
    exact congr_arg subtype.val h
  end),
  R3 := (by intros X Y; apply M_del_con.R3),
}

def contract_then_delete {U : boolalg} (C D : U) (h_disjoint : C ∩ D = ⊥) :
  rankfun U → matroid_on (Cᶜ ∩ Dᶜ) :=
fun M, let
  M_con     : matroid_on Cᶜ := corestrict Cᶜ M,
  E         : ↥(subalg Cᶜ)  := ⟨Cᶜ ∩ Dᶜ, by apply inter_subset_left⟩,
  M_con_del : matroid_on E  := restrict E M_con
in {
  r := (fun X, M_con_del.r (nest E X)),
  R0 := (by intro X; apply M_con_del.R0),
  R1 := (by intro X; apply M_con_del.R1),
  R2 := (begin
    intros X Y h,
    apply M_con_del.R2,
    apply subtype.ext,
    apply subtype.ext,
    show X.val = X.val ∩ Y.val,
    exact congr_arg subtype.val h
  end),
  R3 := (by intros X Y; apply M_con_del.R3),
}

lemma same_same {U : boolalg} (C D : U) (h_disjoint : C ∩ D = ⊥) (M : rankfun U) :
  (delete_then_contract C D h_disjoint M) = (contract_then_delete C D h_disjoint M) :=
begin
  apply rankfun.ext, apply funext, intro X,
  unfold delete_then_contract contract_then_delete,
  simp,
  unfold restrict corestrict,
  simp,



end

/-
lemma del_con {U : boolalg} (C D : U) (h_disjoint : C ∩ D = ⊥) (M : rankfun U) :
  let
    E₁ : ↥(subalg Dᶜ) := ⟨Cᶜ ∩ Dᶜ, by apply inter_subset_right⟩,
    E₂ : ↥(subalg Cᶜ) := ⟨Cᶜ ∩ Dᶜ, by apply inter_subset_left⟩
  in
    corestrict E₁ (restrict Dᶜ M) = restrict E₂ (corestrict Cᶜ M) :=
sorry
-/
----------------------------------------------------------------
/-

----------------------------------------------------------------


lemma contract_contract (C₁ C₂ : subalg E) (M : matroid_on E) :
  contract (C₂∖C₁) (contract C₁ M) ≅ contract (C₁ ∪ C₂) M
:= ⟨
  (calc E - C₁.val - (C₂∖C₁).val
      = (E ∩ C₁.valᶜ) ∩ (C₂.val ∩ C₁.valᶜ)ᶜ : rfl
  ... = E ∩ (C₁.val ∪ (C₂.val ∩ C₁.valᶜ))ᶜ  : by simp only [inter_assoc, compl_union]
  ... = E ∩ (C₁.val ∪ C₂.val)ᶜ              : by simp only [union_distrib_left, union_compl_self, inter_top]
  ... = E - (C₁ ∪ C₂).val                   : rfl),
  (fun X h₁ h₂, let
  h₃ := calc (C₂.val ∩ C₁.valᶜ) ∪ C₁.val
           = C₁.val ∪ (C₁.valᶜ ∩ C₂.val)            : by simp only [inter_comm, union_comm]
       ... = (C₁.val ∪ C₁.valᶜ) ∩ (C₁.val ∪ C₂.val) : by apply union_distrib_left
       ... = C₁.val ∪ C₂.val                        : by simp only [union_compl_self, top_inter],
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
  rankfun (subalg E) → rankfun (subalg (Dᶜ ∩ {e})) :=
fun hDE M, let
  emb : embed (subalg (Dᶜ ∩ {e})) (subalg E) := embed.from_nested_pair (inter_subset_right _ _),
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
  rankfun (subalg E) → rankfun (subalg (Cᶜ ∩ {e})) :=
fun hCE M, let
  emb : embed (subalg (Cᶜ ∩ {e})) (subalg E) := embed.from_nested_pair (inter_subset_right _ _),
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
-/
/-
Goal: state and prove the relationship between deletion, contraction, and duality.

Existence of a normal form:
  expressions of the form M/C\D are closed under deletion and contraction,
  and together with M*/C\D they are closed under duality.

Current idea: define restriction and corestriction from U to subalg E
Then deletion and contraction are instances of these maps
And a sequence of deletions and contractions with disjoint arguments can be composed
-/

import rankfun boolalg boolalg_induction 
open boolalg 
--open boolalg_induction 

local attribute [instance] classical.prop_decidable

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
      ...         = Xᶜ                   : by rw [inter_subset_mp h],
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


section indep
variables {U : boolalg}

def is_indep (M : rankfun U) : U → Prop :=
  fun X, M.r X = size X

def boolalg_singleton : Type := {X : U // size X = 1}

notation x ` ∈ ` X := x.1 ⊆ X


lemma I1 (M : rankfun U) : is_indep M ⊥ := 
  calc M.r (⊥ : U) = 0 : rank_bot M ... = size (⊥ : U) : (@size_bot U).symm

lemma I2 (M : rankfun U) (X Y : U) : is_indep M Y → (X ⊆ Y) → is_indep M X := 
begin
    intros hY hXY,
    have h0 : M.r Y ≤ M.r X + M.r (Y - X) := sorry, 
    have h1 : size X  + size (Y - X) = size Y := sorry, 
    have h2 : M.r (Y-X)  ≤ size (Y-X) := sorry, 
    have h3 : M.r X ≤ size X := sorry,
    have h4 : size Y = M.r Y := sorry, 
    have h5 : size X = M.r X := by linarith, 
    exact h5.symm,   
end

lemma I3 (M : rankfun U) (X Y : U) : is_indep M X → is_indep M Y → size X < size Y → 
  (∃ e : boolalg_singleton, e.val ⊆ Y ∧ ¬(e.val ⊆ X) ∧ is_indep M (X ∪ e.val)) := 
begin
  intros hIX,
  set P : U → Prop := λ Z, ((X ∩ Z = ⊥) → (M.r (X ∪ Z) > M.r X) → ∃ z : boolalg_singleton, (z.val ⊆ Z) ∧ (M.r (X ∪ z.val) > M.r X)) with hP,  
  suffices h : ∀ Z, P Z, 
  sorry, 
  --specialize h (Y-X) (sorry : X ∩ (Y - X) = ⊥), 

  --apply strong_induction, 
  sorry, 
end

lemma I3' (M : rankfun U) (X Y : U) : is_indep M X → is_indep M Y → size X < size Y → 
  (∃ X': U, X ⊆ X' ∧ X' ⊆ X ∪ Y ∧ is_indep M X' ∧ size X' = size X +1 ) := sorry 

lemma I3'' (M : rankfun U) (X Z : U) : (M.r X < M.r Z) → 
  ∃ z: boolalg_singleton, z.1 ⊆ Z ∧ M.r X < M.r (X ∪ z.1) := 
begin
  revert Z, 
  set P : U → Prop := λ Z', M.r X < M.r Z' → ∃ z' : boolalg_singleton, z'.1 ⊆ Z' ∧ M.r X < M.r (X ∪ z'.1) with hP, 
  apply strong_induction P, rw hP at *, clear hP P,
  intros Z hBelow hRankDiff, 
  by_contradiction, push_neg at a, 
  --specialize
  sorry, 

end


lemma loopy_rank_zero (M : rankfun U) (X : U) : (∀ e : boolalg_singleton, e.1 ⊆ X → M.r e.1 = 0) → (M.r X = 0) :=
begin
  revert X, refine strong_induction _ _,
  intros X hX hSing,  
  by_cases hSize : (size X > 1),
  rcases (union_ssubsets X hSize) with ⟨Y, ⟨Z, ⟨hY, hZ, hI, hU⟩⟩⟩, 
  have := M.R3 Y Z,
  rw [hU,hI,rank_bot] at this, 
  have := hX Y hY (λ (e : boolalg_singleton) (he : e.val ⊆ Y), hSing e (subset_trans he hY.1)), 
  have := hX Z hZ (λ (e : boolalg_singleton) (he : e.val ⊆ Z), hSing e (subset_trans he hZ.1)), 
  linarith [M.R0 X], 
  by_cases (size X = 0), rw size_zero_bot h, exact rank_bot M, 
  exact hSing ⟨X, by linarith [int.add_one_le_of_lt (lt_of_le_of_ne (size_nonneg X) (ne.symm h))]⟩ (subset_refl X),    
end 

 

def is_coindep (M : rankfun U) : U → Prop :=
  is_indep (dual M)

lemma coindep_iff_complement_fullrank {M : rankfun U} (X : U) :
  is_coindep M X ↔ (M.r Xᶜ = M.r ⊤) := 
begin 
  unfold is_coindep is_indep dual, simp only [], split; {intros h, linarith},
end

inductive minor_expression {U : boolalg} : U → Type
| univ : minor_expression ⊤
| restrict   (X : U) {E : U} : (X ⊆ E) → minor_expression E → minor_expression X
| corestrict (X : U) {E : U} : (X ⊆ E) → minor_expression E → minor_expression X
open minor_expression

def to_minor {U : boolalg} {E : U} :
  minor_expression E → rankfun U → matroid_on E :=
begin
  intros min_expr rfun, 
  induction min_expr with X E₀ hXE₀ min_expr₀ M₀ X E₀ hXE₀ min_expr₀ M₀,
  exact restrict rfun ⊤, 
  exact restrict_subalg hXE₀ M₀,
  exact corestrict_subalg hXE₀ M₀,  
end

lemma to_minor.delete_delete {U : boolalg} {D₁ D₂ : U} (h : D₁ ∩ D₂ = ⊥) :
let
  h₁ : (D₁ ∪ D₂)ᶜ ⊆ D₁ᶜ := sorry,
  h₂ :  D₁ᶜ       ⊆ ⊤   := sorry,
  h₃ : (D₁ ∪ D₂)ᶜ ⊆ ⊤   := sorry
in
  to_minor (restrict (D₁ ∪ D₂)ᶜ h₁
           (restrict  D₁ᶜ       h₂ univ)) =
  to_minor (restrict (D₁ ∪ D₂)ᶜ h₃ univ) :=
begin
  sorry
end

def contract_delete {U : boolalg} (C D : U) :
  (C ∩ D = ⊥) → minor_expression (C ∪ D)ᶜ :=
fun h, restrict (C ∪ D)ᶜ (calc (C ∪ D)ᶜ = Cᶜ ∩ Dᶜ : compl_union _ _ ... ⊆ Cᶜ : inter_subset_left _ _ ) (corestrict Cᶜ (subset_top _) univ)

structure minor {U : boolalg} :=
  (r : rankfun U)
  {E : U}
  (exp : minor_expression E)


lemma has_representation {M : rankfun U} {E : U} (expr : minor_expression E) :
  (∃ (C D : U) (hCD : C ∩ D = ⊥),  
    (C ∪ D)ᶜ = E 
    ∧ ((to_minor (contract_delete C D hCD) M) ≅ (to_minor expr M))) :=
begin
  intros,
  induction expr with X₁ E₁ hXE minor_expr IH 
                      X₁ E₁ hXE minor_expr IH,
  {
    use ⊥, use ⊥, use (inter_idem ⊥), split, 
    rw [union_idem, boolalg.compl_bot],
    sorry, /- until we fill in to_minor -/
  },
  {
    rcases IH with ⟨C,D,⟨hCD,⟨h₁,h₂⟩⟩⟩,  
    use C, use D ∪ (E₁ - X₁), use (sorry : C ∩ (D ∪ (E₁ - X₁)) = ⊥), split,  
    sorry, -- some boolalg stuff
    sorry,
  },
  {
    rcases IH with ⟨C,D,⟨hCD,⟨h₁,h₂⟩⟩⟩,  
    use C ∪ (E₁ - X₁), use D, use (sorry : (C ∪ (E₁ - X₁)) ∩ D = ⊥), split,  
    sorry, -- some boolalg stuff
    sorry, -- until we fill in to_minor
  }
end


lemma has_good_representation {M : rankfun U} {E : U} (expr : minor_expression E) :
  (∃ (C D : U) (hCD : C ∩ D = ⊥),  
    (C ∪ D)ᶜ = E ∧
    is_indep M C ∧ is_coindep M D 
    ∧ ((to_minor (contract_delete C D hCD) M) ≅ (to_minor expr M))) := sorry
  
end /-section-/ indep

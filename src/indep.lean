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

lemma eq_to_matroid_heq {E : U} {M₁ M₂ : matroid_on E} : 
  (M₁ = M₂) → (M₁ ≅ M₂) := 
  λ h, by {rw h, apply matroid_heq.refl}

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

section minor 

variables {U : boolalg}

inductive minor_expression  : U → Type
| self                       : minor_expression ⊤
| restrict   (X : U) {E : U} : (X ⊆ E) → minor_expression E → minor_expression X
| corestrict (X : U) {E : U} : (X ⊆ E) → minor_expression E → minor_expression X
open minor_expression

/-
def to_minor {E : U} :
  minor_expression E → rankfun U → matroid_on E :=
begin
  intros min_expr rfun, 
  induction min_expr with X E₀ hXE₀ min_expr₀ M₀ X E₀ hXE₀ min_expr₀ M₀,
  exact restrict_subset ⊤ rfun, 
  exact restrict_nested_pair hXE₀ M₀,
  exact corestrict_nested_pair hXE₀ M₀,  
end
-/

/-- term for above -/
def to_minor : Π {E : U}, minor_expression E → rankfun U → matroid_on E
| _ self r := restrict_subset _ r
| _ (restrict _ hE' expr) r := restrict_nested_pair hE' (to_minor expr r)
| _ (corestrict _ hE' expr) r := corestrict_nested_pair hE' (to_minor expr r)

/-
example (E : U) (expr : minor_expression E) (r : rankfun U) :
   to_minor_alg expr r = to_minor expr r :=
begin
  induction expr,
  { refl, },
  {
    unfold to_minor_alg,
    rewrite expr_ih,
    refl,
  },
  {
    unfold to_minor_alg,
    rewrite expr_ih,
    refl,
  }
end
-/

lemma to_minor.delete_delete {D₁ D₂ : U} (h : D₁ ∩ D₂ = ⊥) :
let
  h₁ : (D₁ ∪ D₂)ᶜ ⊆ D₁ᶜ := sorry,
  h₂ :  D₁ᶜ       ⊆ ⊤   := sorry,
  h₃ : (D₁ ∪ D₂)ᶜ ⊆ ⊤   := sorry
in
  to_minor (restrict (D₁ ∪ D₂)ᶜ h₁
           (restrict  D₁ᶜ       h₂ self)) =
  to_minor (restrict (D₁ ∪ D₂)ᶜ h₃ self) :=
begin
  intros,
  delta to_minor,
  refl,
end



@[simp] def contract_delete  (C D : U) :
  (C ∩ D = ⊥) → minor_expression (C ∪ D)ᶜ :=
fun h, restrict (C ∪ D)ᶜ (calc (C ∪ D)ᶜ = Cᶜ ∩ Dᶜ : compl_union _ _ ... ⊆ Cᶜ : inter_subset_left _ _ ) (corestrict Cᶜ (subset_top _) self)

--simplified minor expression - corestrict to Z, then restrict to A 



lemma switch_restrict_corestrict {M : rankfun U} (A Z : U) (hAZ : A ⊆ Z) : 
  to_minor (restrict A hAZ ((corestrict Z (subset_top Z)) self)) M = to_minor (corestrict A (subset_union_left A Zᶜ) ((restrict (A ∪ Zᶜ) (subset_top (A ∪ Zᶜ))) self)) M :=
  let f := (embed.from_subset A).f, hAZc := subset_union_left A Zᶜ, hAZc_top := subset_top (A ∪ Zᶜ) in 
  begin
    ext X, 
    have set_eq : A ∪ Zᶜ - A = ⊤ - Z := by {simp, unfold has_sub.sub, rw [inter_distrib_right, inter_compl,bot_union, ←compl_union, union_comm, union_subset_mp hAZ]}, 
    have RHS : (to_minor (corestrict A hAZc (restrict (A ∪ Zᶜ) hAZc_top self)) M).r X = M.r (f X ∪ (A ∪ Zᶜ - A)) - M.r (A ∪ Zᶜ - A) := rfl, 
    rw set_eq at RHS, 
    exact RHS.symm, 
  end


lemma dual_restrict_corestrict {M : rankfun U} (A Z : U) (hAZ : A ⊆ Z) : 
  dual (to_minor (restrict A hAZ (corestrict Z (subset_top Z) self)) M) = to_minor (corestrict A hAZ (restrict Z (subset_top Z) self)) (dual M) := 
  let emb := embed.from_subset A in 
  begin
    rw switch_restrict_corestrict, ext X, apply eq.symm, 
    have hJ : ∀ (J : U) (hJ : J ⊆ A), (J ∪ (Z-A))ᶜ = (A - J) ∪ (⊤ - Z) := 
      λ J hJ, by rw [compl_union, top_diff, compl_diff, diff_def, inter_distrib_left, ←compl_union, union_subset_mp (subset_trans hJ hAZ), inter_comm, union_comm], 
    have hset : size ((X:U) ∩ (Z - A)) = 0 := 
      by {suffices : ((X:U) ∩ (Z-A)) = ⊥, rw this, exact size_bot U, apply subset_bot, refine subset_trans (subset_inter_subset_left (X :U ) A (Z-A) X.2) _, rw inter_diff, apply subset_refl},
    have hbot : (Z-A)ᶜ = A ∪ (⊤ - Z) := 
      by {rw [←bot_union (Z-A), hJ ⊥ (bot_subset _), diff_bot]},

    calc _ = (size ((X:U) ∪ (Z-A)) + M.r ((X ∪ (Z-A))ᶜ) - M.r ⊤) - (size (Z-A) + M.r (Z-A)ᶜ - M.r ⊤ )       : rfl 
       ... = size (X:U) + M.r ((X ∪ (Z-A))ᶜ) - M.r  (Z-A)ᶜ                                                   : by linarith [size_modular (X :U) (Z -A), hset, emb.on_size X]
       ... = size (X:U) + M.r ((A- X) ∪ (⊤ - Z)) - M.r (A ∪ (⊤ - Z))                                        : by rw [(hJ X X.2 : ((X:U) ∪ (Z-A))ᶜ = (A- X) ∪ (⊤ - Z)), hbot]
       ... = size (X:U) + (M.r ((A- X) ∪ (⊤ - Z)) - M.r (⊤ - Z)) - (M.r (A ∪ (⊤ - Z)) - M.r (⊤ - Z))        : by linarith 
       ... = (dual (to_minor (restrict A hAZ (corestrict Z (subset_top Z) self)) M)).r X                     : rfl 
       ... = _ : by rw switch_restrict_corestrict,             
  end

lemma dual_corestrict_restrict {M : rankfun U} (A Z : U) (hAZ : A ⊆ Z) : 
  dual (to_minor (corestrict A hAZ (restrict Z (subset_top Z) self)) M) = to_minor (restrict A hAZ (corestrict Z (subset_top Z) self)) (dual M) := 
  by {nth_rewrite 0 ←(dual_dual M), rw [←dual_restrict_corestrict, dual_dual]}


lemma restrict_top {M : rankfun U}{A : U} (expr: minor_expression A) : 
  to_minor (restrict A (subset_refl A) expr) M = to_minor expr M := 
  by {ext X,cases X,refl}

lemma corestrict_top {M : rankfun U}{A : U} (expr: minor_expression A) : 
  to_minor (corestrict A (subset_refl A) expr) M = to_minor expr M :=
begin
  simp [to_minor],
  set M' := to_minor expr M,
  apply rankfun.ext,
  ext X, 
  simp,
  set f := (embed.from_nested_pair (subset_refl A)).f,
  have : (embed.to_subalg A A _) = ⊤ := rfl,
  rw this,  
  rw [boolalg.compl_top, union_bot], 
  rw [rank_bot M'],
  have : (f X) = X := by cases X; refl,
  rw this, linarith,
end

lemma dual_restrict {M: rankfun U} (A : U) : 
  dual (to_minor (restrict A (subset_top A) self) M) = to_minor (corestrict A (subset_top A) self) (dual M) := 
    by rw [←(corestrict_top (restrict A (subset_top A) self)), dual_corestrict_restrict, restrict_top]
    
lemma dual_corestrict {M: rankfun U} (A : U) : 
  dual (to_minor (corestrict A (subset_top A) self) M) = to_minor (restrict A (subset_top A) self) (dual M) := 
    by rw [←(restrict_top (corestrict A (subset_top A) self)), dual_restrict_corestrict, corestrict_top]

lemma switch_corestrict_restrict {M : rankfun U} (A Z : U) (hAZ : A ⊆ Z) : 
  to_minor (corestrict A hAZ ((restrict Z (subset_top Z)) self)) M = to_minor (restrict A (subset_union_left A Zᶜ) ((corestrict (A ∪ Zᶜ) (subset_top (A ∪ Zᶜ))) self)) M :=
  by {nth_rewrite 0 ←(dual_dual M), rw [←dual_restrict_corestrict, switch_restrict_corestrict, dual_corestrict_restrict, dual_dual]}


lemma restrict_restrict {M : rankfun U} (A Z : U) (hAZ : A ⊆ Z) : 
  to_minor (restrict A hAZ (restrict Z (subset_top Z) self)) M = to_minor (restrict A (subset_top A) self) M :=
  let f := (embed.from_subset A).f in 
  by {ext X,calc _ = M.r (f X) : rfl ...= _ : rfl}
     
lemma corestrict_corestrict {M : rankfun U} (A Z : U) (hAZ : A ⊆ Z) : 
  to_minor (corestrict A hAZ (corestrict Z (subset_top Z) self)) M = to_minor (corestrict A (subset_top A) self) M :=   
  begin
    let M₀ := to_minor (corestrict Z (subset_top Z) self) M,  
    --nth_rewrite 0 ←(dual_dual M),
    
    
    --have := 
    --calc  
    sorry, 
  end

@[simp] def reduced_expr  (A Z : U) (hAZ : A ⊆ Z) : minor_expression A := 
  restrict A hAZ ((corestrict Z (subset_top Z)) self)

lemma restriction_of_reduced  {M : rankfun U} (A Z A' : U) (hA'A : A' ⊆ A) (hAZ : A ⊆ Z) : 
  to_minor (restrict A' hA'A (reduced_expr A Z hAZ)) M = to_minor (reduced_expr A' Z (subset_trans hA'A hAZ)) M := rfl

lemma corestriction_of_reduced' {M : rankfun U} (A Z Z' : U) (hZ'A : Z' ⊆ A) (hAZ : A ⊆ Z) : 
  to_minor (corestrict Z' hZ'A (reduced_expr A Z hAZ) ) M = to_minor (reduced_expr Z' (Z' ∪ (Z - A)) (subset_union_left Z' _)) M := 
  begin
    unfold reduced_expr, 

    calc to_minor (corestrict Z' hZ'A (reduced_expr A Z hAZ) ) M = to_minor (corestrict Z' hZ'A (reduced_expr A Z hAZ) ) M : rfl 
                                                             ... = to_minor (reduced_expr Z' (Z' ∪ (Z - A)) (subset_union_left Z' _)) M :sorry, 
  end 

lemma corestriction_of_reduced {M : rankfun U} (A Z Z' : U) (hZ'A : Z' ⊆ A) (hAZ : A ⊆ Z) : 
  to_minor (corestrict Z' hZ'A (reduced_expr A Z hAZ) ) M = to_minor (reduced_expr Z' (Z' ∪ (Z - A)) (subset_union_left Z' _)) M := 
  let  J  := Z' ∪ (Z - A),
       M' := to_minor (reduced_expr A Z hAZ) M, 
       N  := (to_minor (reduced_expr Z' J (subset_union_left _ _)) M) in 
  begin
    ext, rename x X, 
    have equiv : (A - Z') ∪ (⊤ - Z) = (⊤ - J) := by 
    {
      simp only [J], unfold has_sub.sub, 
      rw [top_inter, top_inter, compl_union, compl_inter, compl_compl, union_distrib_right, 
            ←compl_inter, inter_subset_mp (subset_trans hZ'A hAZ : Z' ⊆ Z), inter_comm, union_comm],
    }, 
    have LHS := 
    calc     (to_minor (corestrict Z' hZ'A (reduced_expr A Z hAZ)) M).r X
           = (corestrict_nested_pair hZ'A M').r X                                                 : rfl 
      ...  = M.r (X ∪ (A - Z') ∪ (⊤-Z)) - M.r (⊤ - Z)  - (M.r ((A - Z') ∪ (⊤ - Z)) - M.r (⊤ -Z)) : rfl  
      ...  = M.r (X ∪ (A - Z') ∪ (⊤-Z)) - M.r ((A - Z') ∪ (⊤ - Z))                               : by linarith
      ...  = M.r (X ∪ (⊤ - J)) - M.r (⊤ - J)                                                     : by rw [union_assoc, equiv],

    rw LHS, apply eq.symm, clear LHS, calc N.r X = _ : rfl, 
  end


-- Every minor expression is equivalent to a reduced one. 

lemma has_reduced_expr {M : rankfun U} {E : U} (expr : minor_expression E) :
  ∃ (Z : U) (hZ : E ⊆ Z), 
  to_minor (reduced_expr E Z hZ) M = to_minor expr M := 
begin
  induction expr with X₁ E₁ hX₁E₁ minor_expr IH 
                    X₁ A₁ hX₁A₁ minor_expr IH,
  /- self -/                  
  { use ⊤,  use subset_refl ⊤, simp [reduced_expr], rw [restrict_top, corestrict_top] },
  /-restrict-/
  {
    rcases IH with ⟨Z, ⟨hE₁Z, h⟩⟩,
    use Z, use subset_trans hX₁E₁ hE₁Z, 
    rw ← restriction_of_reduced,
    dunfold to_minor,
    rw h,
  },
  /-corestrict-/
  {
    rcases IH with ⟨Z, ⟨hA₁Z, h⟩⟩,
    use X₁ ∪ (Z - A₁), use subset_union_left X₁ _,
    rw ←corestriction_of_reduced _ _ _ hX₁A₁ hA₁Z,
    dunfold to_minor,
    rw h, 
  }
end

lemma has_representation {M : rankfun U} {E : U} (expr : minor_expression E) :
  (∃ (C D : U) (hCD : C ∩ D = ⊥),  
    (C ∪ D)ᶜ = E 
    ∧ ((to_minor (contract_delete C D hCD) M) ≅ (to_minor expr M))) :=
begin
  sorry, 
end


/-lemma has_good_representation {M : rankfun U} {E : U} (expr : minor_expression E) :
  (∃ (C D : U) (hCD : C ∩ D = ⊥),  
    (C ∪ D)ᶜ = E ∧
    is_indep M C ∧ is_coindep M D 
    ∧ ((to_minor (contract_delete C D hCD) M) ≅ (to_minor expr M))) := sorry-/
  
end minor 

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

-- Sets containing only loops have rank zero. 

lemma loopy_rank_zero (M : rankfun U) (X : U) : (∀ e : boolalg.singleton U, (e : U) ⊆ X → M.r e = 0) → (M.r X = 0) :=
begin
  revert X, refine strong_induction _ _,
  intros X hX hSing,  
  by_cases hSize : (size X > 1),
  rcases (union_ssubsets X hSize) with ⟨Y, ⟨Z, ⟨hY, hZ, hI, hU⟩⟩⟩, 
  have := M.R3 Y Z,
  rw [hU,hI,rank_bot] at this, 
  have := hX Y hY (λ (e : boolalg.singleton U) (he : (e:U) ⊆ Y), hSing e (subset_trans he hY.1)), 
  have := hX Z hZ (λ (e : boolalg.singleton U) (he : (e:U) ⊆ Z), hSing e (subset_trans he hZ.1)), 
  linarith [M.R0 X], 
  by_cases (size X = 0), rw size_zero_bot h, exact rank_bot M, 
  exact hSing ⟨X, by linarith [int.add_one_le_of_lt (lt_of_le_of_ne (size_nonneg X) (ne.symm h))]⟩ (subset_refl X),    
end 

set_option pp.proofs true
open minor_expression

-- A larger-rank set can be used to augment a smaller-rank one. 
lemma rank_augment (M : rankfun U) (X Z : U) : (M.r X < M.r Z) → 
  ∃ z: boolalg.singleton U, (z:U) ⊆ Z ∧ M.r X < M.r (X ∪ z) := 
let M' := to_minor (corestrict (Z - X) (subset_trans (diff_subset Z X) (subset_union_right X Z)) (restrict (X ∪ Z) (subset_top (X ∪ Z)) self)) M in
begin
  
  intros hrXrZ,
  by_contradiction h, push_neg at h, 
  have hdiff : (X ∪ Z) - (Z-X) = X := union_diff_diff _ _,
  have hunion: (Z-X) ∪ X = X ∪ Z := by rw [union_comm _ X, union_diff],

  --let emb := embed.from_subset (Z-X),
  let hrM' : ∀ (J : subalg (Z-X)), M'.r J = M.r (J ∪ X) - M.r (X) := by {intros J, sorry, }, 
  have : M'.r ⊤ ≠ 0 := 
  begin
    have :=  
    calc M'.r ⊤ = M.r ((Z-X) ∪ ((X ∪ Z)-(Z-X)))- M.r ((X ∪ Z)-(Z-X))  : rfl
            ... = M.r (X ∪ Z) - M.r X                                 : by rw [hdiff, hunion] 
            ... ≥ M.r Z - M.r X                                       : by linarith[M.R2 Z (X ∪ Z) (subset_union_right X Z)],
    linarith,
  end,
  apply this, apply loopy_rank_zero, intros e he,
  specialize h e (subset_trans (sorry : (e :U) ⊆ Z - X) (sorry: Z-X ⊆ Z)), 
  
  have := calc  M'.r e 
              = M.r ((e:U) ∪ ((X ∪ Z)-(Z-X))) - M.r ((X ∪ Z)-(Z-X)) : rfl
          ... = M.r (X ∪ e) - M.r X : by rw [(sorry: (X ∪ Z) - (Z-X) = X), union_comm],
  suffices : M.r (X ∪ e) ≤ M.r X, by linarith [M'.R0 e],
  
  refine h, 
end




def is_coindep (M : rankfun U) : U → Prop :=
  is_indep (dual M)

lemma coindep_iff_complement_fullrank {M : rankfun U} (X : U) :
  is_coindep M X ↔ (M.r Xᶜ = M.r ⊤) := 
begin 
  unfold is_coindep is_indep dual, simp only [], split; {intros h, linarith},
end

end indep 
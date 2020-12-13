/-
Goal: state and prove the relationship between deletion, contraction, and duality.

Existence of a normal form:
  expressions of the form M/C\D are closed under deletion and contraction,
  and together with M*/C\D they are closed under duality.

Current idea: define restriction and corestriction from U to subalg E
Then deletion and contraction are instances of these maps
And a sequence of deletions and contractions with disjoint arguments can be composed
-/

import rankfun boolalg boolalg_induction  boolalg_collections
open boolalg 
--open boolalg_induction 

local attribute [instance] classical.prop_decidable
noncomputable theory 
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

lemma dual_r (M : rankfun U)(X : U):
   (dual M).r X = size X + M.r Xᶜ - M.r ⊤ := 
   rfl 

end /-section-/ dual

----------------------------------------------------------------

section minor 

variables {U : boolalg}

inductive minor_on  : U → Type
| self                       : minor_on ⊤
| restrict   (X : U) {E : U} : (X ⊆ E) → minor_on E → minor_on X
| corestrict (X : U) {E : U} : (X ⊆ E) → minor_on E → minor_on X
open minor_on



def to_minor : Π {E : U}, minor_on E → rankfun U → matroid_on E
| _ self r := restrict_subset _ r
| _ (restrict _ hE' expr) r := restrict_nested_pair hE' (to_minor expr r)
| _ (corestrict _ hE' expr) r := corestrict_nested_pair hE' (to_minor expr r)


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
  (C ∩ D = ⊥) → minor_on (C ∪ D)ᶜ :=
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


lemma restrict_top {M : rankfun U}{A : U} (expr: minor_on A) : 
  to_minor (restrict A (subset_refl A) expr) M = to_minor expr M := 
  by {ext X,cases X,refl}

lemma corestrict_top {M : rankfun U}{A : U} (expr: minor_on A) : 
  to_minor (corestrict A (subset_refl A) expr) M = to_minor expr M :=
begin
  simp [to_minor],
  set M' := to_minor expr M,
  apply rankfun.ext, ext X, 
  simp only,
  set f := (embed.from_nested_pair (subset_refl A)).f,
  have : (embed.to_subalg A A _) = ⊤ := rfl,
  rw [this,  boolalg.compl_top, union_bot, rank_bot M'],
  rw [(by cases X; refl: f X = X)],
  linarith,
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

@[simp] def reduced_expr  (A Z : U) (hAZ : A ⊆ Z) : minor_on A := 
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

lemma has_reduced_expr {M : rankfun U} {E : U} (expr : minor_on E) :
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

lemma has_representation {M : rankfun U} {E : U} (expr : minor_on E) :
  (∃ (C D : U) (hCD : C ∩ D = ⊥),  
    (C ∪ D)ᶜ = E 
    ∧ ((to_minor (contract_delete C D hCD) M) ≅ (to_minor expr M))) :=
begin
  sorry, 
end


/-lemma has_good_representation {M : rankfun U} {E : U} (expr : minor_on E) :
  (∃ (C D : U) (hCD : C ∩ D = ⊥),  
    (C ∪ D)ᶜ = E ∧
    is_indep M C ∧ is_coindep M D 
    ∧ ((to_minor (contract_delete C D hCD) M) ≅ (to_minor expr M))) := sorry-/
  
end minor 

section /- rank -/ rank
variables {U : boolalg}
-- Loops 


-- Sets containing only loops have rank zero. 


lemma loopy_rank_zero (M : rankfun U) (X : U) : (∀ e : boolalg.single U, (e : U) ⊆ X → M.r e = 0) → (M.r X = 0) :=
begin
  revert X, refine strong_induction _ _,
  intros X hX hSing,  
  by_cases hSize : (size X > 1),
  rcases (union_ssubsets X hSize) with ⟨Y, ⟨Z, ⟨hY, hZ, hI, hU⟩⟩⟩, 
  have := M.R3 Y Z,
  rw [hU,hI,rank_bot] at this, 
  have := hX Y hY (λ (e : boolalg.single U) (he : (e:U) ⊆ Y), hSing e (subset_trans he hY.1)), 
  have := hX Z hZ (λ (e : boolalg.single U) (he : (e:U) ⊆ Z), hSing e (subset_trans he hZ.1)), 
  linarith [M.R0 X], 
  by_cases (size X = 0), rw size_zero_bot h, exact rank_bot M, 
  exact hSing ⟨X, by linarith [int.add_one_le_of_lt (lt_of_le_of_ne (size_nonneg X) (ne.symm h))]⟩ (subset_refl X),    
end 

--set_option pp.proofs true
open minor_on

-- A larger-rank set can be used to augment a smaller-rank one. 
lemma rank_augment (M : rankfun U) (X Z : U) : (M.r X < M.r Z) → 
  ∃ z: boolalg.single U, (z:U) ⊆ Z ∧ M.r X < M.r (X ∪ z) := 
let 
    hcr    : Z-X ⊆ X ∪ Z         := subset_trans (diff_subset Z X) (subset_union_right X Z),
    hr     : X ∪ Z ⊆ ⊤           :=  subset_top (X ∪ Z),  
    hdiff  : (X ∪ Z) - (Z-X) = X := union_diff_diff _ _,
    hunion : (Z-X) ∪ X = X ∪ Z   := by rw [union_comm _ X, union_diff] 
in 
begin
  intros hrXrZ, by_contradiction h, push_neg at h, 
  --pertinent minor M' : restrict to X ∪ Z then corestrict to Z-X
  let M' := to_minor (corestrict (Z - X) hcr (restrict (X ∪ Z) hr self)) M, 
  -- simplified rank function of M' 
  have hrM' : ∀ (J : subalg (Z-X)), M'.r J = M.r (J ∪ X) - M.r (X) := 
    by {intros J, calc _  = M.r (J ∪ ((X ∪ Z) - (Z-X))) - M.r ((X ∪ Z) - (Z-X)) : rfl ... = _ : by rw hdiff}, 

  have hr'top := hrM' ⊤, 
  rw [coe_top (Z-X), hunion] at hr'top, 

  have : M'.r ⊤ ≠ 0 := by linarith [by calc M'.r ⊤ = _ : hr'top ... ≥ M.r Z - M.r X : by linarith [M.R2 Z (X ∪ Z) (subset_union_right X Z)]],

  apply this, apply loopy_rank_zero, intros e he,
  specialize h e (subset_trans ((e: subalg (Z-X)).property) (diff_subset _ _ )), 
  rw coe_single_subalg_compose at h, 
  rw [hrM' e, union_comm, coe_subalg_single_compose],
  linarith [M.R2 _ _ (subset_union_left X e)],
end

-- same as R2 but with implicit X Y
lemma R2 (M : rankfun U){X Y : U}(hXY : X ⊆ Y) :
  M.r X ≤ M.r Y := 
  M.R2 X Y hXY

lemma R2_u (M : rankfun U)(X Y : U) : 
  M.r X ≤ M.r (X ∪ Y) := 
  R2 M (subset_union_left X Y)

lemma rank_single_ub (M : rankfun U)(e : single U):
  M.r e ≤ 1 := 
  by {rw ←(size_coe_single e), exact M.R1 e}

lemma rank_le_top (M : rankfun U)(X : U) : 
  M.r X ≤ M.r ⊤ := 
  R2 M (subset_top X)

lemma rank_eq_of_supset {M : rankfun U}{X Y : U}:
  X ⊆ Y → (M.r Y ≤ M.r X) → M.r X = M.r Y :=
  λ h h', (le_antisymm (R2 M h) h') 

lemma rank_eq_of_union {M : rankfun U}{X Y : U}:
  M.r (X ∪ Y) ≤ M.r X → M.r (X ∪ Y) = M.r X :=
  λ h, ((rank_eq_of_supset ((subset_union_left X Y))) h).symm

lemma rank_eq_of_union_supset {M : rankfun U}(X Y Z: U):
  X ⊆ Y → M.r X = M.r Y → M.r (X ∪ Z) = M.r (Y ∪ Z) := 
  begin
    intros hXY hr, apply rank_eq_of_supset (subset_union_subset_left X Y Z hXY), 
    have : M.r ((X ∪ Z) ∩ Y) = _ := by rw [inter_distrib_right, inter_subset_mp hXY],
    have : M.r ((X ∪ Z) ∪ Y) = _ := by rw [union_assoc, union_comm Z Y, ←union_assoc, union_subset_mp hXY ],
    linarith [M.R3 (X ∪ Z) Y , R2_u M X (Z ∩ Y) ], 
  end 

lemma rank_subadditive (M : rankfun U)(X Y : U) : 
  M.r (X ∪ Y) ≤ M.r X + M.r Y :=
  by linarith [M.R3 X Y, M.R0 (X ∩ Y)]

lemma rank_add_single_ub (M : rankfun U)(X : U)(e : single U): 
  M.r (X ∪ e) ≤ M.r X + 1 := 
  by linarith [rank_subadditive M X e, rank_single_ub M e]

lemma rank_diff_subadditive (M : rankfun U){X Y : U}(hXY : X ⊆ Y) :
  M.r Y ≤ M.r X + M.r (Y - X) := 
  by {nth_rewrite 0 (by apply diff_union_subset hXY : Y = X ∪ (Y-X)), apply rank_subadditive}

lemma rank_diff_le_size_diff (M : rankfun U){X Y : U}(hXY : X ⊆ Y) :
  M.r Y - M.r X ≤ size Y - size X := 
  by linarith [(rank_diff_subadditive M hXY), diff_size hXY, M.R1 (Y-X)]
     
lemma submod_three_sets (M : rankfun U)(X Y Y' :U) :
  M.r (X ∪ (Y ∪ Y')) + M.r (X ∪ (Y ∩ Y')) ≤ M.r (X ∪ Y) + M.r (X ∪ Y') := 
  by {have := M.R3 (X ∪ Y) (X ∪ Y'), rw [←union_distrib_left, ←union_distrib_union_right] at this, exact this}

lemma submod_three_sets_disj (M : rankfun U)(X Y Y' :U)(hYY' : Y ∩ Y' = ⊥) :
  M.r (X ∪ (Y ∪ Y')) + M.r (X) ≤ M.r (X ∪ Y) + M.r (X ∪ Y') := 
  by {have := submod_three_sets M X Y Y', rw [hYY', union_bot] at this, exact this}


  
end rank 

-- Independence 

section indep
variables {U : boolalg}

def is_indep (M : rankfun U) : U → Prop :=
  λ X, M.r X = size X


def indep (M : rankfun U) : Type := { I : U // is_indep M I}

instance coe_indep {M : rankfun U} : has_coe (indep M) U := coe_subtype   

def is_dep (M : rankfun U) : U → Prop := 
   λ X, ¬(is_indep M X)



lemma indep_iff_r {M : rankfun U} (X : U): 
  is_indep M X ↔ M.r X = size X := 
  by refl 

lemma dep_iff_r {M : rankfun U} (X : U):
  is_dep M X ↔ M.r X < size X := 
  by {unfold is_dep, rw indep_iff_r, exact ⟨λ h, (ne.le_iff_lt h).mp (M.R1 X), λ h, by linarith⟩}

def is_coindep (M : rankfun U) : U → Prop :=
  is_indep (dual M)

def is_codep (M : rankfun U) : U → Prop := 
  is_dep (dual M)

--instance coe_coindep {M : rankfun U} : has_coe (coindep M) U := ⟨λ I, I.val⟩  

lemma indep_or_dep (M : rankfun U) (X : U): 
  is_indep M X ∨ is_dep M X := 
  by {rw [dep_iff_r, indep_iff_r], exact eq_or_lt_of_le (M.R1 X)}

lemma dep_iff_not_indep {M : rankfun U} (X : U): 
  is_dep M X ↔ ¬is_indep M X := 
  by {rw [indep_iff_r, dep_iff_r], exact ⟨λ h, by linarith, λ h, (ne.le_iff_lt h).mp (M.R1 X)⟩}

lemma indep_iff_not_dep {M : rankfun U} (X : U): 
  is_indep M X ↔ ¬is_dep M X := 
  by {rw dep_iff_not_indep, simp}

lemma coindep_iff_r {M : rankfun U} (X : U) :
  is_indep (dual M) X ↔ (M.r Xᶜ = M.r ⊤) := 
  by {unfold is_coindep is_indep dual, simp only [], split; {intros h, linarith}}

lemma codep_iff_r {M : rankfun U} (X : U) : 
  is_dep (dual M) X ↔ (M.r Xᶜ < M.r ⊤) := 
  by {rw [dep_iff_not_indep, coindep_iff_r], exact ⟨λ h, (ne.le_iff_lt h).mp (rank_le_top M Xᶜ), λ h, by linarith⟩}
    
lemma bot_indep {M : rankfun U} :
  is_indep M ⊥ :=  
  by rw [indep_iff_r, size_bot, rank_bot]

lemma dep_nonbot {M : rankfun U} {X : U} (hdep : is_dep M X ):
  X ≠ ⊥ := 
  λ h, by {have := @bot_indep _ M, rw ←h at this, exact hdep this}

lemma I1 (M : rankfun U) : is_indep M ⊥ := 
  calc M.r (⊥ : U) = 0 : rank_bot M ... = size (⊥ : U) : (@size_bot U).symm

lemma I1_r (M : rankfun U) :
   M.r ⊥ = size (⊥ : U) :=
  (I1 M)

lemma I2 (M : rankfun U) {X Y : U}: 
  X ⊆ Y → is_indep M Y → is_indep M X := 
  begin 
    intro hXY, simp_rw indep_iff_r, intro hY, 
    linarith [M.R1 X, M.R1 (Y-X), diff_size hXY, rank_diff_subadditive M hXY]
  end 

lemma I2_r (M : rankfun U) {X Y : U} (hXY: X ⊆ Y) : M.r Y = size Y → M.r X = size X := 
  by {have := I2 M hXY, rw [indep_iff_r, indep_iff_r] at this, assumption} 

lemma I3 (M : rankfun U) (X Y : U) : 
  is_indep M X → is_indep M Y → size X < size Y → 
  (∃ e : boolalg.single U, (e : U) ⊆ Y ∧ ¬((e: U) ⊆ X) ∧ is_indep M (X ∪ e)) := 
begin
  simp_rw indep_iff_r, intros hIX hIY hXY,
  rcases rank_augment M X Y (by linarith) with ⟨e,⟨h₁, h₂⟩⟩, 
  have hx := (λ he, by {rw [union_comm, union_subset_mp he] at h₂, linarith}: ¬((e:U) ⊆ X)), 
  refine ⟨e,⟨h₁,_,_⟩⟩, exact hx, 
  have hs := (size_modular X e),
  rw [ eq.trans (inter_comm X (e: U)) (nonelement_disjoint hx), size_bot] at hs, 
  linarith [size_coe_single e, M.R1 (X ∪ e), int.add_one_le_iff.mpr h₂],  
end

lemma dep_subset_dep (M : rankfun U){X Y : U}: 
  X ⊆ Y → is_dep M X → is_dep M Y := 
  by {intro hXY, repeat {rw dep_iff_not_indep}, contrapose!, exact I2 M hXY}



end indep 



section /-Circuits-/ circuit
variables {U : boolalg}


def is_circuit (M : rankfun U) : U → Prop := 
  λ X, (is_dep M X ∧  ∀ Y: U, Y ⊂ X → is_indep M Y)

def is_cocircuit (M : rankfun U) : U → Prop := 
  is_circuit (dual M)

def circuit (M : rankfun U) : Type := { C : U // is_circuit M C }

instance coe_circuit {M : rankfun U} : has_coe (circuit M) U := coe_subtype   



lemma circuit_iff_r {M : rankfun U} (X : U) :
  is_circuit M X ↔ (M.r X = size X-1) ∧ (∀ Y:U, Y ⊂ X → M.r Y = size Y) := 
  begin
    unfold is_circuit,
    simp_rw indep_iff_r, 
    split, rintros ⟨hr, hmin⟩,
    split, rcases nonbot_single_removal (dep_nonbot hr) with ⟨Y, ⟨hY₁, hY₂⟩⟩, specialize hmin Y hY₁,
    rw dep_iff_r at hr, linarith [M.R2 _ _ hY₁.1],  
    intros Y hY, exact hmin _ hY, 
    rintros ⟨h₁, h₂⟩, rw dep_iff_r, refine ⟨by linarith, λ Y hY, _ ⟩,  exact h₂ _ hY, 
  end

lemma r_cct {M : rankfun U} {C : U} :
  is_circuit M C → M.r C = size C - 1 := 
  λ hC, ((circuit_iff_r C).mp hC).1
  
lemma r_cct_ssub {M : rankfun U} {C Y : U} : 
  is_circuit M C → (Y ⊂ C) → M.r Y = size Y :=
  λ hC hYC, (((circuit_iff_r C).mp hC).2 Y hYC)

lemma cocircuit_iff_r {M : rankfun U} (X : U):
  is_cocircuit M X ↔ (M.r Xᶜ = M.r ⊤ - 1) ∧ (∀ Y: U, Y ⊂ X → M.r Yᶜ = M.r ⊤) := 
  by 
  {
    unfold is_cocircuit is_circuit, simp_rw [codep_iff_r, coindep_iff_r],
    split, rintros ⟨h₁, h₂⟩, split, 
    have h_nonbot : X ≠ ⊥ := by {intros h, rw [h,boolalg.compl_bot] at h₁, exact int.lt_irrefl _ h₁}, 
    rcases (nonbot_single_removal h_nonbot) with ⟨Y,⟨hY₁, hY₂⟩⟩ ,
    specialize h₂ _ hY₁,  
    rw [←compl_compl Y, ←compl_compl X, compl_size, compl_size Xᶜ] at hY₂, 
    linarith[rank_diff_le_size_diff M (subset_to_compl hY₁.1)], 
    exact h₂, rintros ⟨h₁, h₂⟩, exact ⟨by linarith, h₂⟩, 
  }

lemma dep_iff_contains_circuit {M : rankfun U} (X : U) :
  is_dep M X ↔ ∃ C, is_circuit M C ∧ C ⊆ X := 
  begin
    refine ⟨λ h, _, λ h, _ ⟩, 
    rcases (minimal_example _ X h) with ⟨Z,⟨h₁Z,h₂Z, h₃Z⟩⟩, 
    refine ⟨Z, ⟨⟨h₂Z, (λ Y hY, _)⟩, h₁Z⟩⟩, 
    rw indep_iff_not_dep, exact h₃Z Y hY,  
    cases h with C hC, exact dep_subset_dep M hC.2 hC.1.1, 
  end 

lemma C1 (M : rankfun U): 
  ¬is_circuit M ⊥ := 
  by {rw circuit_iff_r, intros h, have := h.1, linarith [rank_bot M, size_bot U]}

lemma C2 (M : rankfun U) {C₁ C₂ : U}: 
  C₁ ⊆ C₂ → is_circuit M C₁ → is_circuit M C₂ → C₁ = C₂ := 
  by {intros hC₁C₂, repeat {rw circuit_iff_r}, rintros ⟨h₁l,_⟩ ⟨_,h₂r⟩, by_contra, linarith [h₁l, h₂r _ ⟨hC₁C₂,a⟩]}


lemma inter_circuits_ssubset {M : rankfun U}{C₁ C₂ : U}:
  is_circuit M C₁ → is_circuit M C₂ → C₁ ≠ C₂ → C₁ ∩ C₂ ⊂ C₁ := 
  λ hC₁ hC₂ hC₁C₂, by {refine ⟨inter_subset_left _ _,λ h, _⟩, rw ←inter_subset at h, exact hC₁C₂ (C2 M h hC₁ hC₂ )}

lemma C3 {M : rankfun U} {C₁ C₂ : U} {e : single U}: 
  is_circuit M C₁ → is_circuit M C₂ → C₁ ≠ C₂ → (e : U) ⊆ C₁ ∩ C₂ → ∃ C, is_circuit M C ∧ C ⊆ (C₁ ∪ C₂ - e) := 
  begin
    intros hC₁ hC₂ hC₁C₂ he, rw [←dep_iff_contains_circuit, dep_iff_r], 
    have hI : C₁ ∩ C₂ ⊂ C₁ := inter_circuits_ssubset hC₁ hC₂ hC₁C₂, 
    have heU : (e : U) ⊆ C₁ ∪ C₂ := subset_trans he (subset_trans hI.1 (subset_union_left C₁ _)),
    have hcalc : M.r (C₁ ∪ C₂ - e) ≤ size (C₁ ∪ C₂ -e) -1 := by linarith [R2 M (diff_subset (C₁ ∪ C₂) e ), M.R3 C₁ C₂, 
      r_cct hC₁, r_cct hC₂, r_cct_ssub hC₁ hI, size_modular C₁ C₂, remove_single_size heU],
    exact int.le_sub_one_iff.mp hcalc,
  --More verbosely: 
  /-have := calc M.r (C₁ ∪ C₂ - e) ≤ M.r (C₁ ∪ C₂)                                : R2 M (diff_subset (C₁ ∪ C₂) e ) 
                              ...  ≤ M.r C₁ + M.r C₂ - M.r (C₁ ∩ C₂)              : by linarith [M.R3 C₁ C₂]
                              ...  = (size C₁ -1 ) + (size C₂-1) - size (C₁ ∩ C₂) : by rw [rank_of_circuit hC₁, rank_of_circuit hC₂, rank_of_circuit_ssubset hC₁ hI]
                              ...  = size (C₁ ∪ C₂) -2                            : by linarith [size_modular C₁ C₂]
                              ...  = size (C₁ ∪ C₂ - e) - 1                       : by linarith [remove_single_size heU], -/
  end 

lemma C3_subtype {M : rankfun U} {C₁ C₂ : circuit M} {e : single U}: 
  C₁ ≠ C₂ → (e : U) ⊆ C₁ ∩ C₂ → ∃ (C : circuit M), (C :U) ⊆ (C₁ ∪ C₂ - e) := 
  by{intros hne he, cases C3 C₁.2 C₂.2 _ he with C hC, use ⟨C, hC.1⟩, exact hC.2, exact λ h, hne (subtype.eq h)}

end circuit

section /-Bases-/ basis

variables {U : boolalg}

def is_basis (M : rankfun U): U → Prop := 
  λ B, is_indep M B ∧ ∀ X, B ⊂ X → ¬is_indep M X

def is_cobasis (M : rankfun U): U → Prop := 
  λ B, is_basis (dual M) B 

lemma basis_iff_r {M : rankfun U} (B : U) :
  is_basis M B ↔ M.r B = size B ∧ ∀ X, B ⊂ X → M.r X < size X :=
  by {unfold is_basis, simp_rw ←dep_iff_not_indep, rw indep_iff_r, simp_rw dep_iff_r}

lemma cobasis_iff_r {M : rankfun U} (B : U): 
  is_cobasis M B ↔ M.r Bᶜ = M.r ⊤ ∧ ∀ Y, B ⊂ Y → M.r Yᶜ < M.r ⊤ :=
  by {unfold is_cobasis is_basis, rw coindep_iff_r, simp_rw ←dep_iff_not_indep, simp_rw codep_iff_r}

lemma cobasis_iff_compl_basis {M : rankfun U}(B : U):
  is_cobasis M B ↔ is_basis M Bᶜ :=
begin
  rw [basis_iff_r, cobasis_iff_r], sorry, 
end

end basis

section closure

variables {U : boolalg}


@[simp] def is_spanning (M : rankfun U) : U → Prop := 
  λ X, M.r X = M.r ⊤ 

@[simp] def is_nonspanning (M : rankfun U) : U → Prop := 
  λ X, M.r X < M.r ⊤ 

def spans (M : rankfun U) : U → U → Prop := 
  λ X Y, M.r (X ∪ Y) = M.r X 

lemma spans_iff_r {M : rankfun U} {X Y :U} :
  spans M X Y ↔ M.r (X ∪ Y) = M.r X :=
  by refl 

lemma not_spans_iff_r {M : rankfun U}{X Y : U}: 
  ¬spans M X Y ↔ M.r X < M.r (X ∪ Y) :=
  by {rw [spans_iff_r, eq_comm], exact ⟨λ h, lt_of_le_of_ne (R2_u M _ _) h, λ h, ne_of_lt h⟩}

lemma spanning_or_nonspanning (M : rankfun U) (X : U) :
  is_spanning M X ∨ is_nonspanning M X := 
  by { sorry }

lemma spanned_union (M : rankfun U){X Y Y' : U} :
  spans M X Y → spans M X Y' → spans M X (Y ∪ Y') := 
  begin
    unfold spans, intros h h', 
    have := submod_three_sets M X Y Y', 
    have := R2 M (subset_union_left X (Y ∩ Y')), 
    have := R2 M (subset_union_left X (Y ∪ Y')), 
    linarith, 
  end

lemma spanned_union_closed (M : rankfun U)(X : U):
   union_closed (λ Y, spans M X Y) :=
  begin
    refine ⟨_, λ Y Y' hY hY', spanned_union M hY hY'⟩, 
    have : M.r (X ∪ ⊥) = M.r X := by rw union_bot, assumption, 
  end

lemma spans_refl (M : rankfun U) (X : U): 
  spans M X X :=
  by {unfold spans, rw [union_idem]} 

lemma spans_subset (M : rankfun U){X Y Y' :U} : 
  Y ⊆ Y' → spans M X Y' → spans M X Y :=
  begin
    unfold spans, intros hYY' hXY, 
    linarith [R2 M (subset_union_left X Y),  R2 M (subset_union_subset_right _ _ X hYY')], 
  end

def cl (M : rankfun U) : U → U :=
  λ X, max_of_union_closed (spanned_union_closed M X)

-- cl X is the (unique) maximal set that is spanned by X
lemma cl_iff_max {M : rankfun U}{X F : U} : 
  cl M X = F ↔ spans M X F ∧ ∀ Y, F ⊂ Y → ¬spans M X Y :=
  let huc := spanned_union_closed M X,
      h_eq := (union_closed_max_iff_in_and_ub huc F) in 
  by {dsimp at h_eq, unfold is_maximal at h_eq, rw [h_eq], 
        unfold cl, rw [eq_comm, ←is_max_of_union_closed_iff huc]}
  
-- cl X is also the set spanned by X that contains all sets spanned by X
lemma cl_iff_spanned_ub {M : rankfun U}{X F : U}:
   cl M X = F ↔ spans M X F ∧ ∀ Y, spans M X Y → Y ⊆ F := 
   by {unfold cl, rw [eq_comm, is_max_of_union_closed_iff], refl}

lemma cl_iff_spanned_ub_r {M : rankfun U}{X F : U}:
   cl M X = F ↔ M.r (X ∪ F) = M.r X ∧ ∀ Y, (M.r (X ∪ Y) = M.r X) → Y ⊆ F := 
   by {unfold cl, rw [eq_comm, is_max_of_union_closed_iff], refl}

lemma cl_is_max {M : rankfun U}{X : U}:
  spans M X (cl M X) ∧ ∀ Y, (cl M X) ⊂ Y → ¬spans M X Y :=
  cl_iff_max.mp rfl

lemma cl_is_ub {M : rankfun U}{X : U}:
  ∀ Y, spans M X Y → Y ⊆ (cl M X) := 
  (cl_iff_spanned_ub.mp rfl).2 

lemma subset_cl (M : rankfun U)(X : U) : 
  X ⊆ cl M X := 
  (cl_iff_spanned_ub.mp rfl).2 _ (spans_refl M X)

lemma spans_cl (M : rankfun U)(X : U) :
  spans M X (cl M X) := 
  (cl_iff_max.mp rfl).1 

lemma supset_cl {M : rankfun U}(X : U) :
  ∀ Y, (cl M X ⊂ Y) → ¬spans M X Y := 
  (cl_iff_max.mp rfl).2

lemma spanned_subset_cl {M : rankfun U}{X Y : U}: 
  spans M X Y → Y ⊆ cl M X := 
  λ h, cl_is_ub Y h 

lemma subset_cl_iff {M : rankfun U}(X Y: U) :
  Y ⊆ cl M X ↔ spans M X Y := 
  ⟨λ h, spans_subset M h (spans_cl _ _ ), λ h, spanned_subset_cl h⟩ 

lemma subset_cl_iff_r {M : rankfun U}(X Y : U) :
  Y ⊆ cl M X ↔ M.r (X ∪ Y) = M.r X :=
  by {rw subset_cl_iff, refl}

lemma spanning_iff_cl_top {M : rankfun U}(X : U):
  is_spanning M X ↔ cl M X = ⊤ :=
  begin
    rw cl_iff_spanned_ub, unfold spans is_spanning, refine ⟨λ h, ⟨_,λ Y hY, _⟩, λ h, _⟩, 
    rw [h, union_top], apply subset_top, rw [←h.1, union_top], 
  end   
  
lemma cl_top (M : rankfun U):
  cl M ⊤ = ⊤ := 
  by {rw ←spanning_iff_cl_top, obviously}

lemma rank_cl (M : rankfun U)(X : U) : 
  M.r (cl M X) = M.r X := 
  begin
    have : M.r (X ∪ cl M X) = M.r X := spans_cl M X,
    linarith [R2 M (subset_union_right X (cl M X)), R2 M (subset_cl M X)], 
  end 

lemma union_cl_rank_left (M : rankfun U)(X Y : U) :
  M.r ((cl M X) ∪ Y) = M.r (X ∪ Y) := 
  by {rw eq_comm, exact rank_eq_of_union_supset _ _ _ (subset_cl _ _) (rank_cl _ _).symm}
  
lemma union_cl_rank_right (M : rankfun U)(X Y : U) :
  M.r (X ∪ (cl M Y)) = M.r (X ∪ Y) :=
  by {rw [union_comm, union_comm _ Y], apply union_cl_rank_left} 


lemma cl_idem (M : rankfun U)(X : U) :
  cl M (cl M X) = cl M X := 
  begin
    rw cl_iff_spanned_ub, refine ⟨by apply spans_refl, λ Y hY, _⟩,  
    rw subset_cl_iff, unfold spans, unfold spans at hY, 
    apply rank_eq_of_union, 
    linarith [rank_cl M X, union_cl_rank_left M X Y], 
  end


lemma spans_iff_cl_spans {M : rankfun U}{X Y : U}:
  spans M X Y ↔ spans M (cl M X) Y :=
  by{
    repeat {rw spans_iff_r}, 
    rw [rank_eq_of_union_supset X (cl M X), rank_cl],  
    apply subset_cl, exact (rank_cl _ _).symm,  
  }

lemma subset_cl_of_subset (M : rankfun U){X Y : U}:
  X ⊆ Y → cl M X ⊆ cl M Y :=
  λ h, by {rw subset_cl_iff_r, apply rank_eq_of_union, rw [union_cl_rank_right, union_comm, union_subset_mp h]}
  
  

lemma nonelem_cl_iff_r {M : rankfun U}{X : U}{e : single U} :
  e ∉ cl M X ↔ M.r (X ∪ e) = M.r X + 1 :=
  begin
    rw [notelem_iff, subset_cl_iff_r], refine ⟨λ h, _, λ _, λ _, by linarith⟩, 
    linarith [rank_add_single_ub M X e, int.add_one_le_iff.mpr ((ne.symm h).le_iff_lt.mp (R2_u M X e))]
  end

lemma elem_cl_iff_r {M : rankfun U}{X : U}{e : single U} : 
  e ∈ cl M X ↔ M.r (X ∪ e) = M.r X := 
  by rw [elem_iff, subset_cl_iff_r]

lemma elem_cl_iff_spans {M : rankfun U}{X : U}{e : single U}:
  e ∈ cl M X ↔ spans M X e :=
  by rw [spans_iff_r,elem_cl_iff_r]

lemma nonelem_cl_iff_nonspans {M : rankfun U}{X : U}{e : single U}:
  e ∉ cl M X ↔ ¬spans M X e :=
  ⟨λ h, λ hn, h (elem_cl_iff_spans.mpr hn), λ h, λ hn, h (elem_cl_iff_spans.mp hn)⟩

lemma cl4 (M : rankfun U)(X : U)(e f : single U) : 
  e ∈ cl M (X ∪ f) - cl M X  → f ∈ cl M (X ∪ e) - cl M X := 
  begin 
    repeat {rw [elem_diff_iff, nonelem_cl_iff_r, elem_cl_iff_r]}, 
    rw union_perm_23, refine λ h, ⟨_,_⟩, 
    apply rank_eq_of_union, linarith [rank_add_single_ub M X f],  
    cases h with h1 h2, 
    linarith [h2, rank_add_single_ub M X f, R2_u M (X ∪ e) f],  
  end


end closure 


section /-Flats-/ flat
variables {U : boolalg} 

def is_flat (M : rankfun U) : U → Prop := 
  λ F, ∀ (X : U), F ⊂ X → M.r F < M.r X

def is_hyperplane (M : rankfun U) : U → Prop := 
  λ H, (is_flat M H) ∧ M.r H = M.r ⊤ - 1

def is_rank_k_flat (M : rankfun U) (k : ℤ) : U → Prop := 
  λ F, is_flat M F ∧ M.r F = k 

def is_loops (M : rankfun U) : U → Prop := 
  λ F, is_rank_k_flat M 0 F

def is_point (M : rankfun U) : U → Prop := 
  λ F, is_rank_k_flat M 1 F

def is_line (M : rankfun U) : U → Prop := 
  λ F, is_rank_k_flat M 2 F

def is_plane (M : rankfun U) : U → Prop := 
  λ F, is_rank_k_flat M 3 F

lemma flat_iff_r {M : rankfun U} (X : U) :
  is_flat M X ↔ ∀ Y, X ⊂ Y → M.r X < M.r Y := 
  by refl 

lemma cl_is_flat {M : rankfun U} (X : U): 
  is_flat M (cl M X) := 
  begin
    rw flat_iff_r, intros Y hY, have hne := cl_is_max.2 _ hY, 
    rw [spans_iff_cl_spans, spans_iff_r] at hne, 
    rw ←union_subset_mp hY.1, 
    exact lt_of_le_of_ne (R2 M (subset_union_left (cl M X) Y)) (ne.symm hne), 
  end

lemma flat_iff_own_cl {M : rankfun U}{F : U}:
  is_flat M F ↔ cl M F = F :=
  begin
    refine ⟨λ h, _, λ h, by {have := cl_is_flat F, rw h at this, exact this}⟩,
    rw [cl_iff_max, spans_iff_r], simp_rw not_spans_iff_r,  
    exact ⟨by rw union_idem, λ Y hFY, lt_of_lt_of_le (h Y hFY) (by {rw union_comm, apply R2_u})⟩,
  end 

lemma flat_iff_is_cl {M : rankfun U}{F : U}: 
  is_flat M F ↔ ∃ X : U, cl M X = F := 
  ⟨λ h, ⟨F, flat_iff_own_cl.mp h⟩, λ h, by {cases h with X hX, rw flat_iff_own_cl, rw ←hX, apply cl_idem}⟩

lemma flat_iff_augment_r {M : rankfun U}{F : U}:
  is_flat M F ↔ ∀ e, e ∉ F → M.r F < M.r (F ∪ e) :=
  begin
    rw flat_iff_r, 
    refine ⟨λ h, λ e he, h _ (augment_nonelem_ssubset he), λ h, λ Y hY, _⟩,
    cases augment_from_nonempty_diff.mp hY with e he, 
    exact lt_of_lt_of_le (h e he.1) (R2 M he.2), 
  end

lemma flat_iff_augment {M : rankfun U}{F : U}:
  is_flat M F ↔ ∀ (e : single U), e ∉ F → ¬spans M F e := 
  by {rw [flat_iff_augment_r], simp_rw not_spans_iff_r}

lemma is_loops_cl_bot (M : rankfun U):
  is_loops M (cl M ⊥) := 
  by {unfold is_loops is_rank_k_flat, refine ⟨cl_is_flat ⊥, by {rw [rank_cl, rank_bot] }⟩} 

lemma is_loops_iff_cl_bot {M : rankfun U}{L : U}:
  is_loops M L ↔ L = cl M ⊥ := 
  begin
    refine ⟨λ h, _, λ h, by {rw h, exact is_loops_cl_bot M}⟩, 
    cases h with hF h0, rw flat_iff_is_cl at hF, cases hF with X hX, rw ←hX, 
    have := calc M.r X ≤ M.r (cl M X) : R2 M (subset_cl M X) ... = M.r L : by rw hX ...= 0 : h0, 
    replace this : M.r (cl M X) = 0 := by linarith [rank_cl M X, M.R0 (cl M X)], 
    rw [eq_comm, cl_iff_spanned_ub_r ], refine ⟨_,λ Y hY, _⟩,
    rw [bot_union, rank_bot], exact this, 
    rw subset_cl_iff_r, apply rank_eq_of_union,
    rw [bot_union, rank_bot] at hY, 
    linarith [rank_subadditive M X Y], 
  end

lemma hyperplane_iff_r {M : rankfun U} (X : U) :
  is_hyperplane M X ↔ M.r X = M.r ⊤ -1 ∧ ∀ Y, X ⊂ Y → M.r Y = M.r ⊤ := 
  begin
    unfold is_hyperplane, rw flat_iff_r, 
    refine ⟨λ h, ⟨h.2, λ Y hXY, _ ⟩, λ h, ⟨λ Y hXY, _, h.1⟩ ⟩,
    have := h.1 Y hXY, rw h.2 at this, linarith [rank_le_top M Y],  
    rw [h.1,h.2 Y hXY], exact sub_one_lt _,   
  end

lemma hyperplane_iff_maximal_nonspanning {M : rankfun U} (X : U): 
  is_hyperplane M X ↔ is_nonspanning M X ∧ ∀ (Y: U), X ⊂ Y → is_spanning M Y :=
  begin
    split, 
    intro h, simp, split, linarith [h.2],
    intros Y hXY hne, linarith [h.1 Y ⟨hXY,hne⟩, h.2, rank_le_top M Y],
    rintros ⟨h1,h2⟩, simp at h1 h2, split, 
    intros Z hZ, specialize h2 Z hZ.1 hZ.2, linarith, 
    by_cases X = ⊤, rw h at h1, linarith, 
    rcases nonempty_contains_single ((λ hX, h (top_of_compl_bot hX)) : Xᶜ ≠ ⊥) with ⟨e, he⟩,
    specialize h2 (X ∪ e) (augment_from_compl_ssubset he).1 (λ h_ne, _), 
    linarith [rank_subadditive M X e, M.R1 e, size_coe_single e],
    rw [union_comm, eq_comm, ←union_subset] at h_ne, rw elem_compl_iff at he, 
    exact he h_ne, 
  end 

lemma cocircuit_iff_compl_hyperplane {M : rankfun U} (X : U): 
  is_cocircuit M X ↔ is_hyperplane M Xᶜ := 
  begin
    rw [cocircuit_iff_r, hyperplane_iff_r], 
    refine ⟨λ h, ⟨h.1,λ Y hXY, _⟩ , λ h, ⟨h.1,λ Y hXY, h.2 _ (ssubset_to_compl hXY)⟩⟩, 
    rw [←(h.2 _ (ssubset_compl_left hXY)), compl_compl], 
  end

lemma inter_flats_is_flat (M : rankfun U) (F₁ F₂ : U) :
  is_flat M F₁ ∧ is_flat M F₂ → is_flat M (F₁ ∩ F₂) := 
  begin 
    repeat {rw [flat_iff_augment]}, simp_rw ←nonelem_cl_iff_nonspans, rintros ⟨h₁, h₂⟩ e he,
    rw nonelem_inter_iff at he, cases he, 
    exact λ h, (h₁ e he) (subset_trans h (subset_cl_of_subset M (inter_subset_left F₁ F₂))), 
    exact λ h, (h₂ e he) (subset_trans h (subset_cl_of_subset M (inter_subset_right F₁ F₂))), 
  end

end flat

section /- Series and Parallel -/ series_parallel 

variables {U : boolalg}

def is_loop (M : rankfun U) : single U → Prop := 
  λ e, M.r e = 0 

def is_nonloop (M : rankfun U) : single U → Prop := 
  λ e, M.r e = 1 

def is_coloop (M : rankfun U) : single U → Prop := 
  λ e, is_loop (dual M) e  

def is_noncoloop (M : rankfun U) : single U → Prop := 
  λ e, is_coloop (dual M) e

lemma nonloop_iff_not_loop {M : rankfun U} (e : single U) : 
  is_nonloop M e ↔ ¬ is_loop M e := 
  begin 
    unfold is_loop is_nonloop, refine ⟨λ h, _ ,λ h, _⟩,rw h ,
    simp only [not_false_iff, one_ne_zero], 
    have := M.R1 e, rw size_coe_single at this,       
    linarith [(ne.le_iff_lt (ne.symm h)).mp (M.R0 e)],  
  end

lemma coloop_iff_r {M : rankfun U} (e : single U) :
  is_coloop M e ↔ M.r eᶜ = M.r ⊤ - 1 := 
  begin
    unfold is_coloop is_loop, rw [dual_r,size_coe_single],
    exact ⟨λh, by linarith,λ h, by linarith⟩,   
  end

lemma coloop_iff_r_less {M : rankfun U} (e : single U) :
  is_coloop M e ↔ M.r eᶜ < M.r ⊤ := 
  begin
    unfold is_coloop is_loop, rw [dual_r,size_coe_single],
    refine ⟨λh,by linarith,λ h,_⟩, 
    have := rank_diff_le_size_diff M (subset_top (eᶜ : U)), 
    rw [←size_compl (e :U),size_coe_single] at this, 
    linarith [int.le_sub_one_iff.mpr h],
  end



def nonloop (M : rankfun U) : Type := { e : single U // is_nonloop M e}

instance coe_nonloop {M : rankfun U} : has_coe (nonloop M) (single U) := ⟨λ e, e.val⟩  
--def noncoloop (M : rankfun U) : Type := { e : single U // is_nonloop (dual M) e}

lemma rank_union_nonloops_lb {M : rankfun U} (e f : nonloop M) :
  1 ≤ M.r (e ∪ f) := 
  by {have : M.r e = 1 := e.property, have := R2_u M e f, linarith}

lemma rank_union_nonloops_ub {M : rankfun U} (e f : nonloop M) : 
  M.r (e ∪ f) ≤ 2 := 
  by {have : M.r e = 1 := e.property, have : M.r f = 1 := f.property, linarith [M.R0 (e ∩ f), M.R3 e f]}


def parallel (M : rankfun U) : nonloop M → nonloop M → Prop := 
  λ e f, M.r (e ∪ f) = 1 

def series (M : rankfun U) : nonloop (dual M) → nonloop (dual M) → Prop := 
  λ e f, parallel (dual M) e f 

lemma parallel_refl {M : rankfun U} (e : nonloop M) : 
  parallel M e e := 
  by {unfold parallel, rw union_idem, exact e.property}

lemma parallel_symm {M : rankfun U} ⦃e f : nonloop M⦄ :
  parallel M e f → parallel M f e :=
  by {unfold parallel, intro h, rw union_comm, exact h}

lemma parallel_iff_dep {M: rankfun U}{e f : nonloop M} : 
  parallel M e f ↔ (e = f ∨ is_dep M (e ∪ f)) :=
  begin
    unfold parallel, rw dep_iff_r,  refine ⟨λ h, ((or_iff_not_imp_left.mpr (λ hne, _))), λ h, _ ⟩,
    have := size_union_distinct_singles (λ h', hne (subtype.ext h')) , 
    rw h, unfold_coes at *, linarith,  
    cases h, rw [h, union_idem], exact f.property, 
    have := rank_union_nonloops_lb e f, 
    have := size_union_singles_ub e.1 f.1,
    unfold_coes at *, rw ←int.le_sub_one_iff at h, linarith, 
  end

lemma parallel_iff_cct {M: rankfun U}{e f : nonloop M} : 
  parallel M e f ↔ (e = f ∨ is_circuit M (e ∪ f)) :=
  begin
    refine ⟨λ h, _, λ h, (parallel_iff_dep.mpr (or.imp_right _ h : (e = f) ∨ is_dep M (e ∪ f)))⟩, 
    replace h := parallel_iff_dep.mp h, cases h, exact or.inl h, apply or_iff_not_imp_left.mpr, intro h', 
    refine ⟨h,λ Y hY, _⟩, rcases ssubset_pair hY, 
    rw h_1, exact bot_indep, unfold_coes at h_1,  cases h_1, 
    rw [h_1, indep_iff_r], have := e.property, unfold is_nonloop at this, erw this, exact e.val.property.symm,
    rw [h_1, indep_iff_r], have := f.property, unfold is_nonloop at this, erw this, exact f.val.property.symm,  
    exact λ h, h.1, 
  end

lemma parallel_trans {M : rankfun U} ⦃e f g : nonloop M⦄ :
  parallel M e f → parallel M f g → parallel M e g :=
  begin
    unfold parallel, intros hef hfg, 
    have := M.R3 (e ∪ f) (f ∪ g), rw [hef, hfg] at this, 
    have : 1 ≤ M.r ((e ∪ f) ∩ (f ∪ g)) := _, 
    have := R2 M (_ : (e ∪ g : U) ⊆ ((e ∪ f) ∪ (f ∪ g) : U)), 
    linarith [(rank_union_nonloops_lb e g)],  
    rw [union_comm (e:U) f, ←union_distrib_union_right], apply subset_union_right,  
    calc _ = M.r f : f.property.symm ... ≤ _ : R2 M (inter_of_supsets (subset_union_right (e:U) f) (subset_union_left (f:U) g)), 
  end

lemma parallel_equiv (M : rankfun U) : equivalence (parallel M) := 
    ⟨parallel_refl, ⟨parallel_symm,parallel_trans⟩⟩
  
lemma series_refl {M : rankfun U} (e : nonloop (dual M)) :
  series M e e :=
  parallel_refl e

lemma series_symm {M : rankfun U} ⦃e f : nonloop (dual M)⦄ :
  series M e f → series M f e :=
  @parallel_symm _ _ e f

lemma series_trans {M : rankfun U} ⦃e f g : nonloop (dual M)⦄ :
  series M e f → series M f g → series M e g :=
  @parallel_trans _ _ e f g

lemma series_equiv (M : rankfun U): 
  equivalence (series M) :=
  parallel_equiv _ 

def parallel_classes_setoid (M : rankfun U) : setoid (nonloop M) := 
  ⟨parallel M, parallel_equiv M⟩ 

def parallel_classes_quot (M : rankfun U) := quotient (parallel_classes_setoid M)

  
/-lemma point_iff_parallel_class_and_loops {M : rankfun U} {P: U} : 
  is_point M P ↔ ∃  :=
  begin
     
  end-/



end series_parallel 
import boolalg.basic boolalg.examples
import .basic .dual 

namespace boolalg 

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

section minor 

variables {U : boolalg}

inductive minor_on : U → Type
| self                       : minor_on ⊤
| restrict   (X : U) {E : U} : (X ⊆ E) → minor_on E → minor_on X
| corestrict (X : U) {E : U} : (X ⊆ E) → minor_on E → minor_on X
open minor_on


def to_minor : Π {E : U}, minor_on E → rankfun U → matroid_on E
| _ self r := restrict_subset _ r
| _ (restrict _ hE' expr) r := restrict_nested_pair hE' (to_minor expr r)
| _ (corestrict _ hE' expr) r := corestrict_nested_pair hE' (to_minor expr r)


/-lemma to_minor.delete_delete {D₁ D₂ : U} (h : D₁ ∩ D₂ = ⊥) :
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
end-



@[simp] def contract_delete  (C D : U) :
  (C ∩ D = ⊥) → minor_on (C ∪ D)ᶜ :=
fun h, restrict (C ∪ D)ᶜ (calc (C ∪ D)ᶜ = Cᶜ ∩ Dᶜ : compl_union _ _ ... ⊆ Cᶜ : inter_subset_left _ _ ) (corestrict Cᶜ (subset_top _) self)
-/


--simplified minor expression \ corestrict to Z, then restrict to A 

lemma switch_restrict_corestrict {M : rankfun U} (A Z : U) (hAZ : A ⊆ Z) : 
  to_minor (restrict A hAZ ((corestrict Z (subset_top Z)) self)) M = to_minor (corestrict A (subset_union_left A Zᶜ) ((restrict (A ∪ Zᶜ) (subset_top (A ∪ Zᶜ))) self)) M :=
  let f := (embed.from_subset A).f, hAZc := subset_union_left A Zᶜ, hAZc_top := subset_top (A ∪ Zᶜ) in 
  begin
    ext X, 
    have set_eq : (A ∪ Zᶜ) \ A = ⊤ \ Z 
      := by {rw [diff_def, inter_distrib_right, ←compl_union, union_comm Z, 
                subset_def_union_mp hAZ], simp},
    let M' := (to_minor (corestrict A hAZc (restrict (A ∪ Zᶜ) hAZc_top self)) M), 
    have RHS : M'.r X = M.r (X ∪ ((A ∪ Zᶜ) \ A)) - M.r ((A ∪ Zᶜ) \ A) := by refl, 
    rw set_eq at RHS, 
    exact RHS.symm, 
  end


lemma dual_restrict_corestrict {M : rankfun U} (A Z : U) (hAZ : A ⊆ Z) : 
  dual (to_minor (restrict A hAZ (corestrict Z (subset_top Z) self)) M) = to_minor (corestrict A hAZ (restrict Z (subset_top Z) self)) (dual M) := 
  let emb := embed.from_subset A in 
  begin
    rw switch_restrict_corestrict, ext X, apply eq.symm, 
    have hJ : ∀ (J : U) (hJ : J ⊆ A), (J ∪ (Z\A))ᶜ = (A \ J) ∪ (⊤ \ Z) := 
      λ J hJ, by rw [compl_union, top_diff, compl_diff, diff_def, inter_distrib_left, ←compl_union, subset_def_union_mp (subset_trans hJ hAZ), inter_comm, union_comm], 
    have hset : size ((X:U) ∩ (Z \ A)) = 0 := 
      by {suffices : ((X:U) ∩ (Z \ A)) = ⊥, rw this, exact size_bot U, apply subset_bot, refine subset_trans (subset_inter_subset_left (X :U ) A (Z\A) X.2) _, rw inter_diff, apply subset_refl},
    have hbot : (Z\A)ᶜ = A ∪ (⊤ \ Z) := 
      by {rw [←bot_union (Z\A), hJ ⊥ (bot_subset _), diff_bot]},

    calc _ = (size ((X:U) ∪ (Z\A)) + M.r ((X ∪ (Z\A))ᶜ) - M.r ⊤) - (size (Z\A) + M.r (Z\A)ᶜ - M.r ⊤ )       : rfl 
       ... = size (X:U) + M.r ((X ∪ (Z\A))ᶜ) - M.r  (Z\A)ᶜ                                                   : by linarith [size_modular (X :U) (Z\A), hset, emb.on_size X]
       ... = size (X:U) + M.r ((A \ X) ∪ (⊤ \ Z)) - M.r (A ∪ (⊤ \ Z))                                        : by rw [(hJ X X.2 : ((X:U) ∪ (Z\A))ᶜ = (A\X) ∪ (⊤ \ Z)), hbot]
       ... = size (X:U) + (M.r ((A \ X) ∪ (⊤ \ Z)) - M.r (⊤ \ Z)) - (M.r (A ∪ (⊤ \ Z)) - M.r (⊤ \ Z))        : by linarith 
       ... = (dual (to_minor (restrict A hAZ (corestrict Z (subset_top Z) self)) M)).r X                     : rfl 
       ... = _ : by rw switch_restrict_corestrict,             
  end

lemma dual_corestrict_restrict {M : rankfun U} (A Z : U) (hAZ : A ⊆ Z) : 
  dual (to_minor (corestrict A hAZ (restrict Z (subset_top Z) self)) M) = to_minor (restrict A hAZ (corestrict Z (subset_top Z) self)) (dual M) := 
  by {nth_rewrite 0 ←(dual_dual M), rw [←dual_restrict_corestrict, dual_dual]}


lemma restrict_top (M : rankfun U){A : U} (expr: minor_on A) : 
  to_minor (restrict A (subset_refl A) expr) M = to_minor expr M := 
  by {ext X,cases X,refl}

lemma corestrict_top (M : rankfun U){A : U} (expr: minor_on A) : 
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

lemma dual_restrict (M: rankfun U) (A : U) : 
  dual (to_minor (restrict A (subset_top A) self) M) = to_minor (corestrict A (subset_top A) self) (dual M) := 
    by rw [←(corestrict_top _ (restrict A (subset_top A) self)), dual_corestrict_restrict, restrict_top]
    
lemma dual_corestrict (M: rankfun U) (A : U) : 
  dual (to_minor (corestrict A (subset_top A) self) M) = to_minor (restrict A (subset_top A) self) (dual M) := 
    by rw [←(restrict_top _ (corestrict A (subset_top A) self)), dual_restrict_corestrict, corestrict_top]

lemma switch_corestrict_restrict (M : rankfun U) (A Z : U) (hAZ : A ⊆ Z) : 
  to_minor (corestrict A hAZ ((restrict Z (subset_top Z)) self)) M = to_minor (restrict A (subset_union_left A Zᶜ) ((corestrict (A ∪ Zᶜ) (subset_top (A ∪ Zᶜ))) self)) M :=
  by {nth_rewrite 0 ←(dual_dual M), rw [←dual_restrict_corestrict, switch_restrict_corestrict, dual_corestrict_restrict, dual_dual]}


lemma restrict_restrict (M : rankfun U) (A Z : U) (hAZ : A ⊆ Z) : 
  to_minor (restrict A hAZ (restrict Z (subset_top Z) self)) M = to_minor (restrict A (subset_top A) self) M :=
  let f := (embed.from_subset A).f in 
  by {ext X,calc _ = M.r (f X) : rfl ...= _ : rfl}
     
#check minor_on 

/-lemma corestrict_corestrict {M : rankfun U} (A Z : U) (hAZ : A ⊆ Z) : 
  to_minor (corestrict A hAZ (corestrict Z (subset_top Z) self)) M = to_minor (corestrict A (subset_top A) self) M :=   
  begin
    nth_rewrite 0 ←(dual_dual M), 
    have := dual_restrict (dual M) A, 
    
    --unfold to_minor at *,
    
    
    
    --←dual_restrict, 
    /-let U' := subalg Z, 
    let expr := ((corestrict ⊤ (subset_refl ⊤) self) : minor_on (⊤ : U')),
    let M₀ := to_minor expr, 
    have := corestrict_top M₀ expr-/
    --have := @corestrict_top (subalg Z) M₀ ⊤ expr, 
    --nth_rewrite 0 ←(dual_dual M),
    
    
    --have := 
    --calc  
    sorry, 
  end-/

@[simp] def reduced_expr  (A Z : U) (hAZ : A ⊆ Z) : minor_on A := 
  restrict A hAZ ((corestrict Z (subset_top Z)) self)

lemma restriction_of_reduced  {M : rankfun U} (A Z A' : U) (hA'A : A' ⊆ A) (hAZ : A ⊆ Z) : 
  to_minor (restrict A' hA'A (reduced_expr A Z hAZ)) M = to_minor (reduced_expr A' Z (subset_trans hA'A hAZ)) M := rfl

lemma corestriction_of_reduced {M : rankfun U} (A Z Z' : U) (hZ'A : Z' ⊆ A) (hAZ : A ⊆ Z) : 
  to_minor (corestrict Z' hZ'A (reduced_expr A Z hAZ) ) M = to_minor (reduced_expr Z' (Z' ∪ (Z \ A)) (subset_union_left Z' _)) M := 
  let  J  := Z' ∪ (Z \ A),
       M' := to_minor (reduced_expr A Z hAZ) M, 
       N  := (to_minor (reduced_expr Z' J (subset_union_left _ _)) M) in 
  begin
    ext, rename x X, 
    have equiv : (A \ Z') ∪ (⊤ \ Z) = (⊤ \ J) := by 
    {
      simp only [top_diff, J, diff_def, top_inter],
      rw [compl_union, compl_inter, inter_distrib_left, ←compl_union Z', 
          (subset_def_union_mp (subset_trans hZ'A hAZ)), compl_compl, union_comm Zᶜ, inter_comm A], 
    }, 
    have LHS := 
    calc     (to_minor (corestrict Z' hZ'A (reduced_expr A Z hAZ)) M).r X
           = (corestrict_nested_pair hZ'A M').r X                                                   : rfl 
      ...  = M.r (X ∪ (A \ Z') ∪ (⊤ \ Z)) - M.r (⊤ \ Z) - (M.r ((A \ Z') ∪ (⊤ \ Z)) - M.r (⊤ \ Z)) : rfl  
      ...  = M.r (X ∪ (A \ Z') ∪ (⊤ \ Z)) - M.r ((A \ Z') ∪ (⊤ \ Z))                                : by linarith
      ...  = M.r (X ∪ (⊤ \ J)) - M.r (⊤ \ J)                                                        : by rw [union_assoc, equiv],

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
    use X₁ ∪ (Z \ A₁), use subset_union_left X₁ _,
    rw ←corestriction_of_reduced _ _ _ hX₁A₁ hA₁Z,
    dunfold to_minor,
    rw h, 
  }
end

/-lemma has_representation {M : rankfun U} {E : U} (expr : minor_on E) :
  (∃ (C D : U) (hCD : C ∩ D = ⊥),  
    (C ∪ D)ᶜ = E 
    ∧ ((to_minor (contract_delete C D hCD) M) ≅ (to_minor expr M))) :=
begin
  sorry, 
end-/


/-lemma has_good_representation {M : rankfun U} {E : U} (expr : minor_on E) :
  (∃ (C D : U) (hCD : C ∩ D = ⊥),  
    (C ∪ D)ᶜ = E ∧
    is_indep M C ∧ is_coindep M D 
    ∧ ((to_minor (contract_delete C D hCD) M) ≅ (to_minor expr M))) := sorry-/
  
end minor 
end boolalg 




-- A larger-rank set can be used to add a smaller-rank one. Old proof that takes a minor

/-lemma rank_augment {M : rankfun U} {X Z : U} : (M.r X < M.r Z) → 
  ∃ z, z ∈ Z ∧ M.r X < M.r (X ∪ z) := 
let 
    hcr    : Z \ X ⊆ X ∪ Z         := subset_trans (diff_subset Z X) (subset_union_right X Z),
    hr     : X ∪ Z ⊆ ⊤             :=  subset_top (X ∪ Z),  
    hdiff  : (X ∪ Z) \ (Z \ X) = X := union_diff_diff _ _,
    hunion : (Z \ X) ∪ X = X ∪ Z   := by rw [union_comm _ X, union_diff] 
in 
begin
  intros hrXrZ, by_contradiction h, push_neg at h, 
  --pertinent minor M' : restrict to X ∪ Z then corestrict to Z-X
  let M' := to_minor (corestrict (Z \ X) hcr (restrict (X ∪ Z) hr self)) M, 
  -- simplified rank function of M' 
  have hrM' : ∀ (J : subalg (Z \ X)), M'.r J = M.r (J ∪ X) - M.r (X) := 
    by {intros J, calc _  = M.r (J ∪ ((X ∪ Z) \ (Z \ X))) - M.r ((X ∪ Z) \ (Z \ X)) : rfl ... = _ : by rw hdiff}, 

  have hr'top := hrM' ⊤, 
  rw [coe_top (Z \ X), hunion] at hr'top, 

  have : M'.r ⊤ ≠ 0 := by linarith [by calc M'.r ⊤ = _ : hr'top ... ≥ M.r Z - M.r X : by linarith [M.R2 Z (X ∪ Z) (subset_union_right X Z)]],

  apply this, apply loopy_rank_zero, intros e he,
  specialize h e (subset_trans ((e: subalg (Z \ X)).property) (diff_subset _ _ )), 
  rw coe_single_subalg_compose at h, 
  rw [hrM' e, union_comm, coe_subalg_single_compose],
  linarith [M.R2 _ _ (subset_union_left X e)],
end
-/
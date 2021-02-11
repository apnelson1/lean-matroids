import ftype.basic ftype.embed
import .rankfun .dual 

namespace ftype 
noncomputable theory 

@[simp] def restrict_subset {B : ftype} (R : set B) (rfun : rankfun B)  : rankfun (subftype R) := 
{ 
  r := λ X, rfun.r X,
  R0 := λ X, rfun.R0 X,
  R1 := λ X, by {simp only [subftype_coe_size], from rfun.R1 X},
  R2 := λ X Y, by {intros H, simp, apply rfun.R2, simp at H, apply H,},
  R3 := λ X Y, by {simp, from rfun.R3 X Y}
}
-- simp [-has_univ.univ]
-- #check has_univ.univ

-- def image (f : α → β) (s : set α) : set β :=
-- {b | ∃ a, a ∈ s ∧ f a = b}

--let f := (embed.from_subftype R).f in 
--⟨λ X, rfun.r X, λ X, rfun.R0 X, λ X, rfun.R1 X, λ X Y, rfun.R2 X Y, λ X Y, rfun.R3 X Y⟩ 

@[simp] def restrict_nested_pair {B : ftype} {R₀ R : set B} (h : R₀ ⊆ R) (rfun : rankfun (subftype R)) : rankfun (subftype R₀)  := 
let f := embed.from_nested_pair h in 
{ 
  r := λ X, rfun.r (f.img X),
  R0 := λ X, rfun.R0 (f.img X),
  R1 := λ X, by {rw ←f.on_size, from rfun.R1 (f.img X)},
  R2 := λ X Y hXY, rfun.R2 _ _ (f.on_subset hXY), 
  R3 := λ X Y, by {have := rfun.R3 (f.img X) (f.img Y), rw [←f.on_union, ←f.on_inter] at this, from this},
}

--⟨λ X, rfun.r (f X), λ X, rfun.R0 (f X), λ X, rfun.R1 (f X), λ X Y, rfun.R2 (f X) (f Y), λ X Y, rfun.R3 (f X) (f Y)⟩ 
@[simp] def corestrict_subset {U : ftype} (R : set U) (M : rankfun U)  : rankfun (subftype R) := 
let C := Rᶜ, f := embed.from_subftype R in 
⟨ 
  λ X_foo, M.r ((X_foo : set U) ∪ C) - M.r C,
  λ X, by {rw sub_nonneg, exact M.R2 C (X ∪ C) (subset_union_right X C)},
  λ X, by {simp only, linarith [M.R0 (X ∩ C), M.R3 X C, M.R1 X, subftype_coe_size X]},
  λ X Y hXY, by {simp only, linarith [M.R2 (X ∪ C) (Y ∪ C) (subset_union_subset_left _ _ C (f.on_subset hXY))]}, 
  λ X Y, by
  {
    suffices : M.r (coe (X ∪ Y) ∪ C) + M.r (coe (X ∩ Y) ∪ C) ≤ M.r (X ∪ C) + M.r (Y ∪ C), 
      by {simp only, linarith}, 
    simp only [subftype_coe_inter, subftype_coe_union], 
    have h := M.R3 (X ∪ C) (Y ∪ C), 
    rw [←union_distrib_right, ←union_distrib_union_left] at h,  
    assumption,
  },
⟩ 

@[simp] def corestrict_nested_pair {B : ftype} {R₀ R₁ : set B} (h : R₀ ⊆ R₁) (M : rankfun (subftype R₁)) : rankfun (subftype R₀)  := 
let 
  r := M.r, 
  f := (embed.from_nested_pair h),  
  φ := f.img, 
  C := (φ (set.univ))ᶜ in 
⟨
  λ X, r (φ X ∪ C) - r C, 
  λ X, by {rw sub_nonneg, exact M.R2 C (φ X ∪ C) (subset_union_right (φ X) C)}, 
  λ X, by {simp only, linarith [f.on_size X, M.R0 ((φ X) ∩ C), M.R3 (φ X) C, M.R1 (φ X)]}, 
  λ X Y hXY, by {simp only, linarith [M.R2 ((φ X) ∪ C) ((φ Y) ∪ C) (subset_union_subset_left _ _ C (f.on_subset hXY))]}, 
  λ X Y, by 
  {
    simp only, 
    suffices : M.r (φ (X ∪ Y) ∪ C) + M.r (φ (X ∩ Y) ∪ C) ≤ M.r ((φ X) ∪ C) + M.r ((φ Y) ∪ C), by linarith, 
    have h := M.R3 ((f.img X) ∪ C) ((f.img Y) ∪ C), 
    rw [←union_distrib_right, ←union_distrib_union_left, ←f.on_inter, ←f.on_union] at h, 
    from h, 
  },
⟩

--- Below here still needs refactor

def matroid_on {U : ftype}(E : set U) := rankfun (subftype E)

section minor 

variables {U : ftype}

inductive minor_on : set U → Type
| self                       : minor_on univ
| restrict   (X : set U) {E : set U} : (X ⊆ E) → minor_on E → minor_on X
| corestrict (X : set U) {E : set U} : (X ⊆ E) → minor_on E → minor_on X
open minor_on


def to_minor : Π {E : set U}, minor_on E → rankfun U → matroid_on E
| _ self r := restrict_subset _ r
| _ (restrict _ hE' expr) r := restrict_nested_pair hE' (to_minor expr r)
| _ (corestrict _ hE' expr) r := corestrict_nested_pair hE' (to_minor expr r)

/--simplified minor expression \ corestrict to Z, then restrict to A -/

lemma restrict_rank {M : rankfun U}(A : set U)(X : set (subftype A)): 
  (to_minor (restrict A (subset_univ A) self) M).r X = M.r X :=
by simp [to_minor]

lemma corestrict_rank {M : rankfun U}(A : set U)(X : set (subftype A)): 
  (to_minor (corestrict A (subset_univ A) self) M).r X = M.r (X ∪ (univ \ A)) - M.r (univ \ A) :=
by simp [to_minor]

lemma switch_restrict_corestrict {M : rankfun U} (A Z : set U) (hAZ : A ⊆ Z) : 
  to_minor (restrict A hAZ ((corestrict Z (subset_univ Z)) self)) M = to_minor (corestrict A (subset_union_left A Zᶜ) ((restrict (A ∪ Zᶜ) (subset_univ (A ∪ Zᶜ))) self)) M :=
  let f := (embed.from_subftype A).f, hAZc := subset_union_left A Zᶜ, hAZc_univ := subset_univ (A ∪ Zᶜ) in 
  begin
    
    ext X, 
    have set_eq : (A ∪ Zᶜ) \ A = univ \ Z 
      := by {rw [diff_def, inter_distrib_right, ←compl_union, union_comm Z, 
                subset_def_union_mp hAZ], simp},
    set M' := (to_minor (corestrict A hAZc (restrict (A ∪ Zᶜ) hAZc_univ self)) M) with hM', 

    have RHS : M'.r X = M.r (X ∪ ((A ∪ Zᶜ) \ A)) - M.r ((A ∪ Zᶜ) \ A) := 
      by {rw hM',convert rfl; simp,},
    
    rw set_eq at RHS, 
    convert RHS.symm, 
    simp [to_minor],
  end


lemma dual_restrict_corestrict {M : rankfun U} (A Z : set U) (hAZ : A ⊆ Z) : 
  dual (to_minor (restrict A hAZ (corestrict Z (subset_univ Z) self)) M) = to_minor (corestrict A hAZ (restrict Z (subset_univ Z) self)) (dual M) := 
  let emb := embed.from_subftype A in 
  begin
    rw switch_restrict_corestrict, ext X, apply eq.symm, 
    have hJ : ∀ (J : set U) (hJ : J ⊆ A), (J ∪ (Z\A))ᶜ = (A \ J) ∪ (univ \ Z) := 
      λ J hJ, by rw [compl_union, univ_diff, compl_diff, diff_def, inter_distrib_left, ←compl_union, subset_def_union_mp (subset_trans hJ hAZ), inter_comm, union_comm], 
    have hset : size ((X:set U) ∩ (Z \ A)) = 0 := by 
    {
      suffices : ((X:set U) ∩ (Z \ A)) = ∅, 
      rw this, exact size_empty U,
      have := coe_set_is_subset X, 
      tidy, 
    },
    have hempty : (Z\A)ᶜ = A ∪ (univ \ Z) := 
      by {rw [←empty_union (Z\A), hJ ∅ (empty_subset _), diff_empty]},
    
    
    have := calc (to_minor (corestrict A hAZ (restrict Z (subset_univ Z) self)) (dual M)).r X
           = (size ((X:set U) ∪ (Z\A)) + M.r ((X ∪ (Z\A))ᶜ) - M.r univ) - (size (Z\A) + M.r (Z\A)ᶜ - M.r univ )       
            : by {simp [to_minor, dual], } 
       ... = size (X:set U) + M.r ((X ∪ (Z\A))ᶜ) - M.r  (Z\A)ᶜ                                                   
            : by linarith [size_modular (X :set U) (Z\A), hset, emb.on_size X]
       ... = size (X:set U) + M.r ((A \ X) ∪ (univ \ Z)) - M.r (A ∪ (univ \ Z))                                        
            : by {congr', finish}
       ... = size (X:set U) + (M.r ((A \ X) ∪ (univ \ Z)) - M.r (univ \ Z)) - (M.r (A ∪ (univ \ Z)) - M.r (univ \ Z))        
            : by linarith 
       ... = (dual (to_minor (restrict A hAZ (corestrict Z (subset_univ Z) self)) M)).r X                     
            : by {simp [dual, to_minor],} , 

    rw ←switch_restrict_corestrict, assumption,         
  end

lemma dual_corestrict_restrict {M : rankfun U} (A Z : set U) (hAZ : A ⊆ Z) : 
  dual (to_minor (corestrict A hAZ (restrict Z (subset_univ Z) self)) M) = to_minor (restrict A hAZ (corestrict Z (subset_univ Z) self)) (dual M) := 
  by {nth_rewrite 0 ←(dual_dual M), rw [←dual_restrict_corestrict, dual_dual]}


lemma restrict_univ (M : rankfun U){A : set U} (expr: minor_on A) : 
  to_minor (restrict A (subset_refl A) expr) M = to_minor expr M := 
  by {ext X, simp [to_minor], congr',    }-- cases X,refl}

lemma corestrict_univ (M : rankfun U){A : set U} (expr: minor_on A) : 
  to_minor (corestrict A (subset_refl A) expr) M = to_minor expr M :=
begin
  simp [to_minor],
  set M' := to_minor expr M,
  apply rankfun.ext, ext X, 
  simp only,
  set f := (embed.from_nested_pair (subset_refl A)).f,
  have : (embed.to_subftype A A _) = univ := rfl,
  rw [this,  ftype.compl_univ, union_empty, rank_empty M'],
  rw [(by cases X; refl: f X = X)],
  linarith,
end

lemma dual_restrict (M: rankfun U) (A : set U) : 
  dual (to_minor (restrict A (subset_univ A) self) M) = to_minor (corestrict A (subset_univ A) self) (dual M) := 
    by rw [←(corestrict_univ _ (restrict A (subset_univ A) self)), dual_corestrict_restrict, restrict_univ]
    
lemma dual_corestrict (M: rankfun U) (A : set U) : 
  dual (to_minor (corestrict A (subset_univ A) self) M) = to_minor (restrict A (subset_univ A) self) (dual M) := 
    by rw [←(restrict_univ _ (corestrict A (subset_univ A) self)), dual_restrict_corestrict, corestrict_univ]

lemma switch_corestrict_restrict (M : rankfun U) (A Z : set U) (hAZ : A ⊆ Z) : 
  to_minor (corestrict A hAZ ((restrict Z (subset_univ Z)) self)) M = to_minor (restrict A (subset_union_left A Zᶜ) ((corestrict (A ∪ Zᶜ) (subset_univ (A ∪ Zᶜ))) self)) M :=
  by {nth_rewrite 0 ←(dual_dual M), rw [←dual_restrict_corestrict, switch_restrict_corestrict, dual_corestrict_restrict, dual_dual]}


lemma restrict_restrict (M : rankfun U) (A Z : set U) (hAZ : A ⊆ Z) : 
  to_minor (restrict A hAZ (restrict Z (subset_univ Z) self)) M = to_minor (restrict A (subset_univ A) self) M :=
  let f := (embed.from_subftype A).f in 
  by {ext X,calc _ = M.r (f X) : rfl ...= _ : rfl}
     
#check minor_on 

/-lemma corestrict_corestrict {M : rankfun U} (A Z : set U) (hAZ : A ⊆ Z) : 
  to_minor (corestrict A hAZ (corestrict Z (subset_univ Z) self)) M = to_minor (corestrict A (subset_univ A) self) M :=   
  begin
    nth_rewrite 0 ←(dual_dual M), 
    have := dual_restrict (dual M) A, 
    
    --unfold to_minor at *,
    
    
    
    --←dual_restrict, 
    /-let U' := subftype Z, 
    let expr := ((corestrict univ (subset_refl univ) self) : minor_on (univ : set U')),
    let M₀ := to_minor expr, 
    have := corestrict_univ M₀ expr-/
    --have := @corestrict_univ (subftype Z) M₀ univ expr, 
    --nth_rewrite 0 ←(dual_dual M),
    
    
    --have := 
    --calc  
    sorry, 
  end-/

@[simp] def reduced_expr  (A Z : set U) (hAZ : A ⊆ Z) : minor_on A := 
  restrict A hAZ ((corestrict Z (subset_univ Z)) self)

lemma restriction_of_reduced  {M : rankfun U} (A Z A' : set U) (hA'A : A' ⊆ A) (hAZ : A ⊆ Z) : 
  to_minor (restrict A' hA'A (reduced_expr A Z hAZ)) M = to_minor (reduced_expr A' Z (subset_trans hA'A hAZ)) M := rfl

lemma corestriction_of_reduced {M : rankfun U} (A Z Z' : set U) (hZ'A : Z' ⊆ A) (hAZ : A ⊆ Z) : 
  to_minor (corestrict Z' hZ'A (reduced_expr A Z hAZ) ) M = to_minor (reduced_expr Z' (Z' ∪ (Z \ A)) (subset_union_left Z' _)) M := 
  let  J  := Z' ∪ (Z \ A),
       M' := to_minor (reduced_expr A Z hAZ) M, 
       N  := (to_minor (reduced_expr Z' J (subset_union_left _ _)) M) in 
  begin
    ext, rename x X, 
    have equiv : (A \ Z') ∪ (univ \ Z) = (univ \ J) := by 
    {
      simp only [univ_diff, J, diff_def, univ_inter],
      rw [compl_union, compl_inter, inter_distrib_left, ←compl_union Z', 
          (subset_def_union_mp (subset_trans hZ'A hAZ)), compl_compl, union_comm Zᶜ, inter_comm A], 
    }, 
    have LHS := 
    calc     (to_minor (corestrict Z' hZ'A (reduced_expr A Z hAZ)) M).r X
           = (corestrict_nested_pair hZ'A M').r X                                                   : rfl 
      ...  = M.r (X ∪ (A \ Z') ∪ (univ \ Z)) - M.r (univ \ Z) - (M.r ((A \ Z') ∪ (univ \ Z)) - M.r (univ \ Z)) : rfl  
      ...  = M.r (X ∪ (A \ Z') ∪ (univ \ Z)) - M.r ((A \ Z') ∪ (univ \ Z))                                : by linarith
      ...  = M.r (X ∪ (univ \ J)) - M.r (univ \ J)                                                        : by rw [union_assoc, equiv],

    rw LHS, apply eq.symm, clear LHS, calc N.r X = _ : rfl, 
  end


-- Every minor expression is equivalent to a reduced one. 

lemma has_reduced_expr {M : rankfun U} {E : set U} (expr : minor_on E) :
  ∃ (Z : set U) (hZ : E ⊆ Z), 
  to_minor (reduced_expr E Z hZ) M = to_minor expr M := 
begin
  induction expr with X₁ E₁ hX₁E₁ minor_expr IH 
                    X₁ A₁ hX₁A₁ minor_expr IH,
  /- self -/                  
  { use univ,  use subset_refl univ, simp [reduced_expr], rw [restrict_univ, corestrict_univ] },
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

/-lemma has_representation {M : rankfun U} {E : set U} (expr : minor_on E) :
  (∃ (C D : set U) (hCD : C ∩ D = ∅),  
    (C ∪ D)ᶜ = E 
    ∧ ((to_minor (contract_delete C D hCD) M) ≅ (to_minor expr M))) :=
begin
  sorry, 
end-/


/-lemma has_good_representation {M : rankfun U} {E : set U} (expr : minor_on E) :
  (∃ (C D : set U) (hCD : C ∩ D = ∅),  
    (C ∪ D)ᶜ = E ∧
    is_indep M C ∧ is_coindep M D 
    ∧ ((to_minor (contract_delete C D hCD) M) ≅ (to_minor expr M))) := sorry-/
  
end minor 
end ftype 




-- A larger-rank set can be used to add a smaller-rank one. Old proof that takes a minor

/-lemma rank_augment {M : rankfun U} {X Z : set U} : (M.r X < M.r Z) → 
  ∃ z, z ∈ Z ∧ M.r X < M.r (X ∪ z) := 
let 
    hcr    : Z \ X ⊆ X ∪ Z         := subset_trans (diff_subset Z X) (subset_union_right X Z),
    hr     : X ∪ Z ⊆ univ             :=  subset_univ (X ∪ Z),  
    hdiff  : (X ∪ Z) \ (Z \ X) = X := union_diff_diff _ _,
    hunion : (Z \ X) ∪ X = X ∪ Z   := by rw [union_comm _ X, union_diff] 
in 
begin
  intros hrXrZ, by_contradiction h, push_neg at h, 
  --pertinent minor M' : restrict to X ∪ Z then corestrict to Z-X
  let M' := to_minor (corestrict (Z \ X) hcr (restrict (X ∪ Z) hr self)) M, 
  -- simplified rank function of M' 
  have hrM' : ∀ (J : subftype (Z \ X)), M'.r J = M.r (J ∪ X) - M.r (X) := 
    by {intros J, calc _  = M.r (J ∪ ((X ∪ Z) \ (Z \ X))) - M.r ((X ∪ Z) \ (Z \ X)) : rfl ... = _ : by rw hdiff}, 

  have hr'univ := hrM' univ, 
  rw [coe_univ (Z \ X), hunion] at hr'univ, 

  have : M'.r univ ≠ 0 := by linarith [by calc M'.r univ = _ : hr'univ ... ≥ M.r Z - M.r X : by linarith [M.R2 Z (X ∪ Z) (subset_union_right X Z)]],

  apply this, apply loopy_rank_zero, intros e he,
  specialize h e (subset_trans ((e: subftype (Z \ X)).property) (diff_subset _ _ )), 
  rw coe_single_subftype_compose at h, 
  rw [hrM' e, union_comm, coe_subftype_single_compose],
  linarith [M.R2 _ _ (subset_union_left X e)],
end
-/
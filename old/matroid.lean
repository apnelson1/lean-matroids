--Matroids, after Chapter 1 of Oxley, Matroid Theory, 1992.

import data.finset data.equiv.list tactic finset_add tactic.interactive data.set 
-- import tactic.interactive



variables {α : Type*} {β : Type*} [decidable_eq α]

-- variables 

open_locale classical

namespace matroid
open finset
--open set  

structure rank_matroid (E : finset α) :=
(r (X : finset α) (hX : X ⊆ E) : ℤ)
-- (R1)
(R1 {X : finset α} (hX : X ⊆ E) : 0 ≤ r X hX ∧ r X hX ≤ size X)
-- (R2)
(R2 {X Y : finset α} (hXY : X ⊆ Y) (hY : Y ⊆ E) :
 r X (subset.trans hXY hY) ≤ r Y hY)
-- (R3)
(R3 {X Y : finset α} (hX : X ⊆ E) (hY : Y ⊆ E) :
r (X ∪ Y) (union_subset hX hY) + r (X ∩ Y) (inter_subset hX hY) ≤ r X hX + r Y hY)

-- structure rank_matroid' {γ : Type*} :=
-- (r (X : finset α) (hX : X ⊆ E) : ℤ)
-- -- (R1)
-- (R1 {X : finset α} (hX : X ⊆ E) : 0 ≤ r X hX ∧ r X hX ≤ size X)
-- -- (R2)
-- (R2 {X Y : finset α} (hXY : X ⊆ Y) (hY : Y ⊆ E) :
--  r X (subset.trans hXY hY) ≤ r Y hY)
-- -- (R3)
-- (R3 {X Y : finset α} (hX : X ⊆ E) (hY : Y ⊆ E) :
-- r (X ∪ Y) (union_subset hX hY) + r (X ∩ Y) (inter_subset hX hY) ≤ r X hX + r Y hY)

def foo [fintype β]: set β → ℕ  := sizeof

--example [fintype β] : fintype (set β) := set.fintype

-- def 


lemma empty_rank_zero {E : finset α} (M: rank_matroid E) : M.r ∅ (em_ss) = (0 : ℤ) := 
begin
  cases M.R1 ((by exact em_ss):(∅ ⊆ E)),
  rw size_empt at right,
  linarith,
end

lemma rank_superadditive {E A B : finset α} (M: rank_matroid E) (hA : A ⊆ E) (hB: B ⊆ E) : M.r A hA + M.r B hB ≥ M.r (A ∪ B) (union_subset hA hB) := 
begin
    linarith [M.R3 hA hB, (M.R1 (inter_subset hA hB)).1]
end

def restriction {E: finset α} (M: rank_matroid E) (R: finset α) (hR : R ⊆ E): rank_matroid (R) :=
    let UssE := (λ {U : finset α} (hU: U ⊆ R) , subset.trans hU hR) in 
    ⟨ 
    λ X hX, M.r X (UssE hX), 
    λ X hX, M.R1 (UssE hX), 
    λ X Y hXY hY, M.R2 hXY (UssE hY),
    λ X Y hX hY, M.R3 (UssE hX) (UssE hY),
    ⟩ -- all just trivial

def deletion {E: finset α} (M: rank_matroid E) (D: finset α) (hD : D ⊆ E): rank_matroid (E \ D) := restriction M (E \ D) (sdiff_subset E D)


lemma eq_ss {A B E: finset α}: (A ⊆ E) → (A = B)  → (B ⊆ E) :=
    begin
        finish [finset.subset_iff],
    end

@[simp] lemma eq_r {E: finset α} (M: rank_matroid E) {A B: finset α} (hA: A ⊆ E) (hAB: A = B) 
  : ((M.r A hA) = (M.r B (eq_ss hA hAB) )) :=  
  begin
    simp [hAB],    
  end 
  

def rank {E : finset α} (M: rank_matroid E) := M.r E (subset.refl E)



@[simp] def is_loop {E : finset α} (M: rank_matroid E) (e : α) (he : e ∈ E) := (M.r {e} (singleton_subset_iff.mpr he) = 0)

@[simp] lemma l1 {E: finset α}(M: rank_matroid E) (e: α) (he : e ∈ E) (hr: M.r {e} (by tidy) ≤ 0) : is_loop M e (by tidy) := 
begin
  --have := (by simp):({e} ⊆ E),
  have := (M.R1 (by tidy : {e} ⊆ E) ).1,
  simp, 
  linarith,
end 


def is_flat {E : finset α} (M: rank_matroid E) (F : finset α) (hF : F ⊆ E) := ∀ {X : finset α}(hX : X ⊆ E), F ⊂ X → M.r F hF < M.r X hX

def is_indep {E: finset α} (M: rank_matroid E) (X : finset α) (hX : X ⊆ E) :=  
    M.r X hX = size X

def is_dep {E: finset α} (M: rank_matroid E) (X : finset α) (hX : X ⊆ E) := M.r X hX ≤ size X - 1  

def is_spanning {E: finset α} (M: rank_matroid E) (X : finset α) (hX : X ⊆ E) := (M.r X hX = M.r E (subset.refl E))  

def is_hyperplane {E : finset α} (M: rank_matroid E) (H: finset α)(hH : H ⊆ E) := is_flat M H hH ∧ M.r H hH = M.r E (subset.refl E) - 1

def is_circuit {E : finset α} (M: rank_matroid E) (C: finset α)(hC : C ⊆ E) := (is_dep M C hC) ∧ ∀ X ⊂ C, is_indep M X 
(by tidy : X ⊆ E)

def is_basis {E : finset α} (M: rank_matroid E) (B : finset α) (hB : B ⊆ E) :=
    is_indep M B hB ∧ (∀ {X: finset α} (hbX : B ⊂ X) (hX : X ⊆ E), ¬ is_indep M X hX)

--def is_isomorphism {E₁ E₂ : finset α} (ϕ : (fintype.of_finset E₁ → fintype.of_finset E₂))(M₁ : rank_matroid E₁)(M₂ : rank_matroid E₂) := false 

--def isomorphic {E₁ E₂ : finset α}(M₁ : rank_matroid M₁)(M₂ : rank_matroid M₂): ∃ ϕ : 


def dual {E: finset α} (M: rank_matroid E) : rank_matroid E := 
let 
    hXc := (λ {X: finset α} (hX: X ⊆ E), sdiff_subset E X),
    hE  := subset.refl E,
    hO  := empty_subset E
in 
⟨ 
    -- dual rank fn
    (λ X hX, size X - M.r E (hE) + M.r (E \ X) (hXc hX)),
    -- R1*
    begin

      intros X hX,
      let E' := X ∪ (E \ X), let O' := X ∩ (E \ X),
      have hEE' : E = E', exact (union_sdiff_of_subset hX).symm,
      have hOO' : ∅ = O', exact (comp_int X E).symm,
      split,
      {
        --have: (M.r E hE) = (M.r E' (eq_ss hE hEE')), simp, 
        have : M.r E (hE) ≤ size X + M.r (E \ X) (hXc hX),
        {
            calc M.r E (hE) ≤ (M.r E hE) + (M.r ∅ hO) : by linarith [(M.R1 hO).1]
            ...           = (M.r E' (eq_ss hE hEE') )  + (M.r O' (eq_ss hO hOO')) : by simp [eq_r M hE hEE', eq_r M hO hOO']
            ...           ≤ M.r X (hX) + M.r (E \ X) (hXc hX) : by linarith [M.R3 hX (hXc hX)]
            ...           ≤ size X + M.r (E \ X) (hXc hX) : by linarith [(M.R1 hX).2],
        },
        linarith,        
      },  
      {
        have : M.r (E \ X) (hXc hX) ≤ M.r E hE, exact M.R2 (hXc hX) hE,
        linarith,
      },
    end,
    -- R2*
    begin
      intros X Y hXY hY,
      let B := Y \ X,
      let A := (E \ Y ) ∪ (Y \ X), 
      let C := (E \ Y) ∩ (Y \ X),
      have hA : A = E \ X, exact sdiff_tel hXY hY,
      have hB : B ⊆ E, exact  subset.trans (sdiff_subset Y X) hY,
      have hC : C = ∅, tidy,

      have hXC : E \ X ⊆ E, exact sdiff_subset E X,
      --have : M.r (E \ Y) (hXc hY) + M.r B hB ≥ M.r (E \ X) (hXC),
      --{
      have := eq_r M (by tidy: (E \ Y) ∪ B ⊆ E) (sdiff_tel hXY hY: (E \ Y) ∪ B = E \ X),
      have := (M.R1 (by tidy: ((E \ Y) ∩ B ⊆ E))).1,
      have := M.R3 (by tidy: E \ Y ⊆ E) hB,
      --  linarith,
      --} 
      
      have : M.r B hB ≤ size Y - size X, 
      {
        calc M.r B hB          = M.r (Y \ X) _    : by trivial
                           ... ≤ size (Y \ X)     : (M.R1 hB).2
                           ... = size Y - size X  : by linarith [(begin unfold size, apply finset.card_sdiff, end: (size (Y \ X ) = size Y - size X))],
      },
      linarith,   
    end ,
    -- R3*
    begin
      intros X Y hX hY, 
      let UC := (E \ X) ∪ (E \ Y),
      let CU := E \ (X ∪ Y),
      let IC := (E \ X) ∩ (E \ Y),
      let CI := E \ (X ∩ Y),
      have UCI : UC = CI, exact (sdiff_inter_distrib_right E X Y).symm,
      have ICU : IC = CU, exact (sdiff_union_distrib E X Y).symm,
      have hUC: UC ⊆ E, exact union_subset (hXc hX) (hXc hY),
      have hIC: IC ⊆ E, exact subset.trans (inter_subset_left (E \ X) (E \ Y)) (hXc hX),

      have cardmod : size (X ∪ Y) + size (X ∩ Y) = size X + size Y,  exact (finset_card X Y).symm,
      have : M.r CU (eq_ss hIC ICU) + M.r CI (eq_ss hUC UCI) ≤ M.r (E \ X) (hXc hX) + M.r (E \ Y) (hXc hY), 
      {
        
        calc M.r CU (eq_ss hIC ICU) + M.r CI (eq_ss hUC UCI) = M.r IC (hIC) + M.r UC (hUC)                 : by simp [eq_r M hUC UCI, eq_r M hIC ICU]
                                                    ...      ≤ M.r (E \ X) _        + M.r (E \ Y) _        : by linarith [M.R3 (hXc hX) (hXc hY)],
      },
      linarith, 

    end,
⟩ 


def rw_ground_set {E E': finset α}(M: rank_matroid E) (hEE': E = E') : rank_matroid E' := 
let ss := λ {X: finset α}(hX: X ⊆ E'), ((ss_eq hX (hEE'.symm)):(X ⊆ E)) in 
⟨ 
    λ X hX, M.r X (ss hX),
    λ X hX , M.R1 (ss hX),
    λ X Y hXY hY, M.R2 hXY (ss hY),
    λ X Y hX hY, M.R3 (ss hX) (ss hY),
⟩

def contraction {E: finset α} (M: rank_matroid E) (C: finset α )(hC: C ⊆ E): rank_matroid (E \ C) := 
    let UssE := (λ {U : finset α} (hU: U ⊆ E \ C) , subset.trans hU sdiff_subset_self),
    UCssE := (λ {U : finset α} (hU: U ⊆ E \ C) , union_subset (UssE hU) (hC) ) in
        --(union_subset hU hC) sdiff_subset_self) in 
    ⟨
        --definition of rank in M/C 
        λ X hX, ((M.r (X ∪ C) (UCssE hX)) - (M.r C hC)),
        -- proof of R1
        begin
            intros X hX, 
            
            have hXuC := UCssE hX,
            have hXiC := subset.trans (inter_subset_left X C) (UssE hX),
            have hXiCpos := (M.R1 hXiC).1,
            
            split,
            have hlbound: M.r C (hC) ≤ M.r (X ∪ C) (UCssE hX), exact M.R2 (subset_union_right X C) (UCssE hX),
            linarith,

            have hubound : (M.r (X ∪ C) (UCssE hX)) ≤ size X + (M.r C hC),
            {
                have := M.R3 (UssE hX) hC,
                calc M.r (X ∪ C) (hXuC)    ≤  M.r (X ∪ C) _ + M.r (X ∩ C) _       : by linarith [hXiCpos]
                          ...              ≤  M.r X _ + M.r C _                    : (M.R3 (UssE hX) hC )
                          ...              ≤  size X + M.r C _                    : by linarith [(M.R1 (UssE hX)).2], 
            },
            linarith,
        end,
        -- proof of R2
        begin
            intros X Y hXY hY,
            have : (X ∪ C) ⊆ (Y ∪ C), exact union_subset_union_left C hXY,
            have := M.R2 this (UCssE hY),
            linarith, 
        end,
        -- proof of R3
        begin
            intros X Y hX hY,
            let XYu := (X ∪ C) ∪ (Y ∪ C),
            let XYu' := X ∪ Y ∪ C,
            let XYi := (X ∪ C) ∩ (Y ∪ C),
            let XYi' := (X ∩ Y) ∪ C,
            have hXYu := union_subset (UCssE hX) (UCssE hY),
            have hXYi := subset.trans (inter_subset_left (X ∪ C) (Y ∪ C)) (UCssE hX),
            

            have simp_u: (X ∪ C) ∪ (Y ∪ C) = (X ∪ Y) ∪ C, sorry,
            have simp_i: (X ∪ C) ∩ (Y ∪ C) = (X ∩ Y) ∪ C, sorry,
              
            rw simp_u at hXYu,
            rw simp_i at hXYi,

            have : (M.r (X ∪ C) (UCssE hX)) + (M.r (Y ∪ C) (UCssE hY)) ≥ (M.r XYu' hXYu) + (M.r XYi' hXYi),
            {
                rw ← simp_u at hXYu,
                rw ← simp_i at hXYi,
                have := M.R3 (UCssE hX) (UCssE hY),
                have := eq_r M hXYu simp_u,
                have := eq_r M hXYi simp_i,
                linarith,                               
            },
            linarith,
        end,
    ⟩

lemma same_ranks_same_matroid {E : finset α}(M₁ M₂: rank_matroid E): 
  (∀ (X : finset α) (hX: X ⊆ E), M₁.r X hX = M₂.r X hX)  → (M₁ = M₂) := 
begin
  intros h,
  cases M₁,
  cases M₂,
  simp,
  ext X hX,
  exact h X hX,
end

--def corestriction {E: finset α} (M: rank_matroid E) (X: finset α )(hX: X ⊆ E): rank_matroid (X) := rw_ground_set (contraction M (E \ X) sorry) (sorry: E \ (E \ X) = X) 



lemma rank_con {E C: finset α}(M: rank_matroid E)(hC: C ⊆ E) : rank (contraction M C hC) = rank M - M.r C hC := 
begin
  calc rank (contraction M C hC) = (contraction M C hC).r (E \ C) _         : by trivial 
                          ...    = M.r ((E \ C) ∪ C) _  - M.r C hC          : by trivial
                          ...    = M.r (E) _  - M.r C hC                    : by linarith [eq_r M ((sorry):((E \ C) ∪ C ⊆ E)) ((sorry):((E \ C) ∪ C = E))],
end


lemma loopy_rank_zero {E: finset α }(M : rank_matroid E) : ( ∀ (e : α)( he : e ∈ E), M.r {e} sorry = 0)  → rank M = 0 := 
begin
  unfold rank,
  intros hloops,
  suffices : (∀ (U: finset α) (hU: U ⊆ E), M.r U hU = 0), exact this E (subset.refl E),
  intros X hX, 
  induction h : X using finset.induction with a X₀ ha ih generalizing X,
  -- base case
  {
    simp [eq_r M hX h],
    exact empty_rank_zero M,
  },
  -- inductive step 
  {
    have hUnion : X = {a} ∪ X₀, finish [insert_eq a X₀],
    have ha  : {a} ⊆ E, sorry,
    have hX₀ : X₀ ⊆ E, sorry,
    specialize ih X₀ hX₀ (by trivial),
    specialize hloops a (sorry),
    --unfold is_loop at hloops,
    have : M.r X hX  ≤ 0, 
    {
      calc M.r X hX = M.r ({a} ∪ X₀) (by finish)  : eq_r M hX hUnion
      ...           ≤ M.r {a} ha  + M.r X₀ hX₀    : rank_superadditive M ha hX₀
      ...           ≤ 0                           : by linarith [ih, hloops],
    },
    linarith [(M.R1 hX).1],
  },
end


lemma dep_or_indep {E: finset α} (M: rank_matroid E) (X : finset α) (hX : X ⊆ E) : ¬ is_indep M X hX ↔ is_dep M X hX :=  
begin
  unfold is_dep,
  unfold is_indep,
  split,
  intros hi,
  have := (M.R1 hX).2,
  linarith[lt_of_le_of_ne this hi],
  intros hd,
  linarith,
end

lemma subset_of_indep_indep {I J E: finset α} (M : rank_matroid E)(hIJ : I ⊆ J){hJ: J ⊆ E}(J_ind: is_indep M J hJ): is_indep M I (subset.trans hIJ hJ) := 
begin
  unfold is_indep at J_ind,
  have hI:= subset.trans hIJ hJ,
  by_contradiction hc,
  rw dep_or_indep at hc,
  unfold is_dep at hc,
  have hJI : J = I ∪ (J \ I), sorry,--exact (union_sdiff_of_subset hIJ).symm,
  have hJIE : J \ I ⊆ E, sorry,
  have : M.r J hJ ≤  size J - 1,
  {
    calc M.r J hJ = M.r (I ∪ (J \ I)) _              : eq_r M hJ hJI
             ...  ≤ M.r I hI + M.r (J \ I) hJIE      : rank_superadditive M _ _ 
             ...  ≤ size I - 1 + size (J \ I)        : by linarith [hc, (M.R1 hJIE ).2]
             ...  = size J - 1                       : by linarith [(sorry: size I + size (J \ I) = size J)],
  },
  linarith,
end


lemma con_del_dual {E : finset α}(M : rank_matroid E)(X : finset α)(hX : X ⊆ E): contraction (dual M) X hX = dual (deletion M X hX) := 
begin
  let MconX := contraction M X hX,
  let MdelX := deletion M X hX,
  let hEmX := sdiff_subset E X,
  
  --let hEmXmA :=  
  apply same_ranks_same_matroid,
  intros A hA,
  have hAE : A ⊆ E, exact subset.trans hA hEmX,
  have hAUX := union_subset hAE hX,
  have hEmAUX := sdiff_subset E (A ∪ X), 
  have Ems : E \ (A ∪ X) = E \ X \ A, sorry,
  have EAU: size A + size X = size (A ∪ X), sorry, 

  have : (contraction (dual M) X hX).r A hA = (size A) + (M.r (E \ X \ A) (eq_ss hEmAUX Ems)) - (M.r (E \ X) hEmX),
  {
    calc (contraction (dual M) X hX).r A hA = ((dual M).r (A ∪ X) _ ) - ((dual M).r X _)                                                       : by trivial 
                                      ...   = (size (A ∪ X)) - (M.r E _ ) + (M.r (E \ (A ∪ X)) _ ) - ((size X) - (M.r E _) + (M.r (E \ X) _ )) : by trivial
                                      ...   = size A + (M.r (E \ X \ A) _ ) - (M.r (E \ X) _)                                                  : by linarith [eq_r M hEmAUX Ems, EAU],
  },
  have: (dual (deletion M X hX)).r A hA = size A  - (M.r (E \ X) _ ) + (M.r (E \ X \ A) _ ),
  {
    calc (dual (deletion M X hX)).r A hA = size A - (MdelX.r (E \ X) _ ) + (MdelX.r (E \ X \ A) _ )     : by trivial
                                  ...    = size A - (M.r (E \ X) _) + (M.r (E \ X \ A) _)               : by trivial,
  },
  linarith,
end


lemma dual_idempotent {E : finset α} (M: rank_matroid E) : dual (dual M) = M := 
begin
  apply same_ranks_same_matroid,
  intros X hX,
  let hE := subset.refl E,
  --let Xc := E \ X,
  let hXc := sdiff_subset E X,
  have Xcc : E \ (E \ X) = X, sorry,
  have EmEO : E \ {e} = ∅, exact sdiff_self E,
  have : size X + size (E \ X) = size E, sorry,

  calc (dual (dual M)).r X hX = size X - (size E - (M.r E hE) + (M.r (E \ {e}) _)) + (size (E \ X) - (M.r E hE) + (M.r (E \ (E \ X)) _) )   : by trivial 
                        ...   = - (M.r (E \ {e}) (sdiff_subset E E)) + (M.r (E \ (E \ X)) (sdiff_subset E (E \ X)))                         : by linarith
                        ...   = M.r X hX : sorry,
  
end

lemma basis_full_rank {E: finset α}(M: rank_matroid E) {B: finset α} {hB: B ⊆ E} : (is_basis M B hB) → size B = M.r E (subset.refl E) :=
begin
  intros Bbasis,
  cases Bbasis with Bind Bmax,
  --rw dep_or_indep at Bind,
  --unfold is_dep at Bind,
  unfold is_indep at Bind,
  
  by_contradiction hc,
  have rank_small: M.r B hB < rank M,
  {
    --have := (M.R1 hB).2,
    have hE := subset.refl E,
    unfold rank,
    
    have := M.R2 hB hE,
    by_contradiction hc',
    have := lt_or_gt_of_ne hc,
    cases this, linarith, linarith,
  },

  let N := contraction M B hB, 

  have : rank N > 0,
  {
    calc rank N = rank (contraction M B hB) : by trivial
          ...   = rank M - M.r B hB         : rank_con M hB
          ...   > 0                         : by linarith,
  },

  have N_loopy:  ∀ (e : α)( he : e ∈ E \ B), is_loop N e he,
  {
    intros e he,
    have he' := singleton_subset_iff.mpr he,
    have hsize: size (B ∪ {e}) = size B +1, sorry,
    specialize Bmax ((sorry):(B ⊂ B ∪ {e})) (sorry),
    rw dep_or_indep at Bmax,
    unfold is_dep at Bmax,
    unfold is_loop,
    suffices : N.r {e} (he') ≤ 0, linarith [(N.R1 he').1],
    calc N.r {e} he' = M.r ({e} ∪ B) _ - M.r B hB                         : by trivial
                ...  ≤ M.r (B ∪ {e}) sorry - M.r B hB                     : by linarith [eq_r M (sorry: {e} ∪ B ⊆ E) (sorry:({e} ∪ B = B ∪ {e}))]
                ...  ≤ (size (B ∪ {e}) -1) - size B                       : by linarith [Bind, hc]
                ...  ≤ 0 : by linarith [hsize, Bmax],
  },
  
  linarith [loopy_rank_zero N N_loopy],

end 

lemma basis_of_dual {E B : finset α} (M: rank_matroid E)(hB: B ⊆ E): is_basis M B hB ↔ is_basis (dual M) (E \ B) (sorry: E \ B ⊆ E) := 
begin
  -- Suffices to prove one direction by duality.
  suffices : ∀ (M': rank_matroid E){B' : finset α}(hB': B' ⊆ E), is_basis M' B' hB' → is_basis (dual M') (E \ B') (sorry), 
  {
    split,
    intros h,
    exact this M hB h,
    intros h,
    specialize this (dual M) (sorry: E \ B ⊆ E) h,
    rw dual_idempotent M at this,
    rw (sorry: E \ (E \ B) = B) at this,
    exact this,
  },
  clear M hB B,
  intros M B hB B_basis,
  have Bsize_r:= basis_full_rank M B_basis,
  rcases B_basis with ⟨B_ind,B_maximal⟩,
  unfold is_indep at B_ind,
  
  have hBC := sdiff_subset E B,
  
  split,
  {
    rw is_indep,
    have := eq_r M (sorry: E \ (E \ B) ⊆ E) (sorry: E \ (E \ B) = B),
    --have := size E = size B + size (E \ B), sorry,
    
    calc (dual M).r (E \ B) hBC = size (E \ B) - M.r E _  + M.r (E \ (E \ B)) _    : by trivial
                          ...   = size (E \ B)                                     : by linarith,
  },
  {
    intros X hBX hX,
    rw dep_or_indep,
    unfold is_dep,
    have : E \ X ⊂ B, sorry,
    have : size (B \ (E \ X )) ≥ 1, sorry,
    have XCind : is_indep M (E \ X) (sdiff_subset E X),
    { 
      have hEXB: (E \ X) ⊆ B, sorry,
      
      exact subset_of_indep_indep M hEXB B_ind,
      --unfold is_indep at XC_ind,
    },
    unfold is_indep at XCind,
    calc (dual M).r X hX = size X - M.r E sorry + M.r (E \ X) sorry             : by trivial
                    ...  = size X - M.r E sorry + size (E \ X)                  : by linarith
                    ...  ≤ size X - M.r E sorry + size B - size (B \ (E \ X))   : by linarith [(sorry: size B = size (E \ X) +  size (B \ (E \ X)) )]
                    ...  ≤ size X - 1                                           : by linarith,  
  },
end

lemma extends_to_basis_of_superset {E: finset α}(M: rank_matroid E)(I X: finset α){hI: I ⊆ E}(I_ind: is_indep M I hI)(hIX: I ⊆ X)(hX: X ⊆ E):
   ∃(B : finset α) (hB: B ⊆ E) (hBX: B ⊆ X), (I ⊆ B) ∧ is_basis (restriction M X hX) B hBX := 
begin
  let is_indep_prop := λ (U: finset α), (∃ (hU : U ⊆ E), is_indep M U hU),
  have I_indep: is_indep_prop I, use hI,exact I_ind,
  
  rcases (extends_to_maximal_property X I_indep) with ⟨B, ⟨hBX, ⟨B_superset, ⟨hB,B_indep⟩ , B_maximal⟩  ⟩ ⟩ ,
  use B,
  use hB,
  use hBX,
  --unfold is_basis,
  split,
  exact B_superset,
  split,
  {
    unfold is_indep,
    unfold is_indep at B_indep,
    have : (restriction M X hX).r B hBX = M.r B hB, trivial,
    linarith,
  },
  intros Y hBY hYX,
  have Y_dep := B_maximal Y hYX hBY, 
  push_neg at Y_dep,
  specialize Y_dep ((subset.trans hYX hX):(Y ⊆ E)),
  trivial,
end

lemma set_has_basis {E: finset α}(M: rank_matroid E)(X: finset α)(hX: X ⊆ E):
   ∃(B : finset α) (hB: B ⊆ E) (hBX: B ⊆ X), is_basis (restriction M X hX) B hBX :=  
begin
  have emp_ind : is_indep M ∅ em_ss, exact empty_rank_zero M, 
  rcases extends_to_basis_of_superset M ∅ X emp_ind em_ss hX with ⟨B, hB, hBX, ⟨_, win⟩ ⟩, 
  use B, use hB, use hBX, exact win,
end

   
lemma extends_to_basis {E: finset α}(M: rank_matroid E)(I: finset α){hI: I ⊆ E}(I_ind: is_indep M I hI): ∃(B : finset α) (hB: B ⊆ E), (I ⊆ B) ∧ is_basis M B hB := 
begin
  have hE := subset.refl E,
  have : M = restriction M E hE,
  {
    apply same_ranks_same_matroid M (restriction M E hE),
    intros X hX,
    trivial, 
  }, 
  have := extends_to_basis_of_superset M I E I_ind hI (subset.refl E),
  rcases this with ⟨ B, hB, hBX, ⟨ hIB, h_basis⟩ ⟩, 
  use B,
  use hB,
  tauto,
end

lemma ind_aug {E : finset α}   (M : rank_matroid E) {I I' : finset α} (hI : I ⊆ E) (hI' : I' ⊆ E)
    : is_indep M I hI → is_indep M I' hI' → (size I' > size I) → ∃ (J : finset α), I ⊂ J ∧ J ⊆ (I ∪ I') ∧ is_indep M J  (sorry) := 
begin
  intros hypI hypI' hypsize,
  by_contradiction hyp_con,
  push_neg at hyp_con,
  have hU := union_subset hI hI',
  
  unfold is_indep at hypI,
  unfold is_indep at hypI',
  
  let N := restriction M (I ∪ I') hU,
  have hIN: I ⊆ I ∪ I', exact subset_union_left I I',
  have hI'N: I' ⊆ I ∪ I', exact subset_union_right I I',

  have Ibasis : is_basis N I _,
  {
    unfold is_basis,
    split,
    {
      unfold is_indep,
      calc N.r I (hIN)   = M.r I _      : by trivial
                    ...  = I.size       : hypI,
    },
    by_contradiction hc,
    push_neg at hc,
    rcases hc with ⟨X, ⟨hIX, ⟨ hX⟩ ⟩ ⟩, 
    specialize hyp_con X hIX hX, 
    tauto,
  },

  have : size I ≥ size I',
  {
    calc size I = N.r (I ∪ I') _      : basis_full_rank N Ibasis
          ...   = M.r (I ∪ I') hU     : by trivial
          ...   ≥ M.r I' _            : by linarith [M.R2 hI'N hU]
          ...   = size I'             : hypI',
  },
  linarith,
end 

lemma rank_diff_aug {E X Y: finset α}   (M : rank_matroid E) (hX : X ⊆ E) (hY : Y ⊆ E)
    : M.r X hX < M.r Y hY → ∃ a ∈ Y \ X, M.r (X ∪ {a}) (sorry) > M.r X hX := 
begin
  --sorry,
  intros hypXY,
  by_contradiction hyp_con,
  push_neg at hyp_con,
  have hU := union_subset hX hY,
  
  have hXN: X ⊆ X ∪ Y, exact subset_union_left X Y,
  have hYN: Y ⊆ X ∪ Y, exact subset_union_right X Y,

  let R := restriction M (X ∪ Y) sorry,
  let N := (contraction (restriction M (X ∪ Y) hU) X (sorry) ), --(sorry: (X ∪ Y) \ X = Y  \ X),
  
  have hXN: X ⊆ X ∪ Y, exact subset_union_left X Y,
  have hYN: Y ⊆ X ∪ Y, exact subset_union_right X Y,
  
  have Nloopy: ∀ (a : α) (ha :a ∈ ((X ∪ Y) \ X)), N.r {a} sorry = 0,
  {
    intros a ha,
    have ha': {a} ⊆ Y \ X, tidy,
    suffices: N.r {a} sorry ≤ 0, linarith [(N.R1 (sorry: {a} ⊆ ((X ∪ Y) \ X))).1],
    --have hXa: X ∪ {a} ⊆ X ∪ Y, sorry,
    calc N.r {a} sorry = M.r ({a} ∪ X) sorry - M.r X sorry : by trivial
                  ...  = M.r (X ∪ {a}) sorry - M.r X sorry : by linarith [eq_r M (sorry: {a} ∪ X ⊆ E) (sorry: {a} ∪ X = X ∪ {a})]
                  ...  ≤ 0 : sorry,
  },

  have : rank N > 0,
  {
    calc rank N = M.r (((X ∪ Y) \ X) ∪ X) sorry - M.r X hX   :  by trivial
          ...   ≥ M.r Y hY - M.r X hX                        :  by linarith [M.R2 (sorry: Y ⊆ (((X ∪ Y) \ X) ∪ X)) (sorry : (((X ∪ Y) \ X) ∪ X) ⊆ E)]
          ...   > 0                                          :  by linarith, 
  },

  linarith [loopy_rank_zero N Nloopy],
end 
lemma coind_iff_comp_spanning {E X : finset α}(M: rank_matroid E)(hX: X ⊆ E): (is_indep (dual M) X hX) ↔ is_spanning M (E \ X) (sdiff_subset E X) := 
begin
  unfold is_indep is_spanning,
  have hE := subset.refl E,
  have hXC := sdiff_subset E X,
  have: (dual M).r X hX = size X - M.r E hE + M.r (E \ X) hXC, trivial,
  split,
  intros indep,
  linarith,
  intros is_spanning,
  linarith,
end

def rank_ub {E X: finset α}(M: rank_matroid E)(hX: X ⊆ E) := M.R2 hX (subset.refl E)




lemma hyperplane_iff_maximal_nonspanning {E H : finset α}(M: rank_matroid E)(hH: H ⊆ E): (is_hyperplane M H hH) ↔ (¬ is_spanning M H hH) ∧ (∀ (X : finset α)(hX : X ⊆ E), H ⊂ X → is_spanning M X hX) :=
begin
  sorry,
  /-unfold is_hyperplane,
  split,

  rintros ⟨Hflat, Hrank⟩,
  split, unfold is_spanning, linarith,
  intros X hX hHX,
  specialize Hflat hX hHX, 
  unfold is_spanning,
  linarith [rank_ub M hX],
  
  rintros ⟨H_nonspanning, H_maximal⟩,

  have Hdeficient := lt_of_le_of_ne (rank_ub M hH) H_nonspanning,
  split,
  intros X hX hHX,
  specialize H_maximal X hX hHX, 
  unfold is_spanning at H_nonspanning,
  unfold is_spanning at H_maximal,
  linarith,

  unfold is_spanning at H_nonspanning,
  have: H ⊂ E, 
  {
    rw ← coe_ssubset,
    rw set.ssubset_iff_subset_ne,
    rw ← coe_subset at hH, 
    split, exact hH,finish, 
  },

  have augment : ∃ (a : α), ({a} ⊆ E) ∧ (H ⊂ H ∪ {a}), 
  {
    sorry,
  },
  cases augment with a augment_a,

  suffices: M.r H hH ≥ M.r E sorry - 1, linarith,
  specialize H_maximal (H ∪ {a}) sorry augment_a.2, 
  unfold is_spanning at H_maximal,
  --have : M.r (H ∪ {a}) sorry 

  calc M.r H hH ≥ M.r (H ∪ {a}) sorry - M.r {a} hA : linarith [rank_superadditive M hH ((this a).left)] -/
end

lemma cocircuit_iff_complement_hyperplane {E K : finset α}(M: rank_matroid E)(hK: K ⊆ E): (is_circuit (dual M) K hK) ↔ is_hyperplane M (E \ K) (sdiff_subset E K) := 
begin
  split,
  intros K_cocircuit,
  unfold is_hyperplane is_flat,
  unfold is_circuit is_dep is_indep at K_cocircuit,
  cases K_cocircuit with K_codep K_minimal,
  split,
  intros X hX hEKX,

  sorry,
  sorry,
  sorry,

  --unfold is_flat,

end

def is_point {E : finset α}(M : rank_matroid E)(P : finset α)(hP: P ⊆ E) := is_flat M P hP ∧ M.r P hP = 1

lemma flats_intersection {E F F': finset α}(M: rank_matroid E){hF : F ⊆ E}{hF' : F' ⊆ E}(F_flat : is_flat M F hF)(F'_flat : is_flat M F' hF') : is_flat M (F ∩ F') sorry :=
begin
  unfold is_flat,
  intros X hX hFF'X,
  have : ∃ (x : α),(x ∈ X \ (F ∩ F')), sorry,
  cases this with x hx,
  wlog x_notin_F : x ∉ F using [F F', F' F], sorry,
  

  sorry,
  sorry,
  --specialize this F_flat F'_flat (sorry: X \ (F ∩ F') = X \ (F' ∩ F)),
  --specialize this F'_flat,
end


lemma points_skew {E P P': finset α}(M: rank_matroid E){hP: P ⊆ E}{hP': P' ⊆ E} (Ppoint: is_point M P hP) (P'point: is_point M P' hP')(hne: P ≠ P'): 
  (is_flat M (P ∩ P') sorry ) ∧ (M.r (P ∩ P') sorry = 0) :=
begin
  sorry,
end

--def ε : {E: finset α}(M : rank_matroid E) := size filter()



end matroid



/-/-- `indep E` is the type of matroids (encoded as systems of independent sets) with ground set `E` :
`finset α` -/
structure indep (E : finset α) :=
(indep : finset (finset α))
(indep_subset_powerset_ground : indep ⊆ powerset E)
-- (empty_indep)
(empty_mem_indep : ∅ ∈ indep)
-- (indep_of_subset_indep)
(indep_of_subset_indep {x y} (hx : x ∈ indep) (hyx : y ⊆ x) : y ∈ indep)
-- (I3)
(indep_exch {x y} (hx : x ∈ indep) (hy : y ∈ indep) (hcard : card x < card y)
    : ∃ e, e ∈ y \ x ∧ insert e x ∈ indep)
--attribute [class] indep

instance indep_repr [has_repr α] (E : finset α) : has_repr (indep E) :=
⟨λ m, has_repr.repr m.indep⟩

theorem eq_of_indep_eq : ∀ {M₁ M₂ : indep E}, M₁.1 = M₂.1 → M₁ = M₂
  | ⟨I₁, p₁, q₁, r₁, s₁⟩ ⟨I₂, p₂, q₂, r₂, s₂⟩ h :=
by simpa only []

/-- A circuit of a matroid is a minimal dependent subset of the ground set -/
def is_circuit (x : finset α) (m : indep E) : Prop :=
x ∉ m.indep ∧ ∀ y, y ⊂ x → y ∈ m.indep

/-- proof by Mario Carneiro https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/subject/finsets.2C.20decidable_mem.2C.20and.20filter/near/133708937 -/
instance decidable_circuit (x : finset α) (m : indep E) : decidable (is_circuit x m) :=
decidable_of_iff (x ∉ m.indep ∧ ∀ y ∈ (powerset x).erase x, y ∈ m.indep)
begin
  simp only [is_circuit, has_ssubset.ssubset, mem_powerset, and_imp, mem_erase],
  refine and_congr iff.rfl (forall_congr $ λ y, _),
  refine ⟨λ H h₁ h₂, H (mt _ h₂) h₁, λ H h₁ h₂, H h₂ $ mt _ h₁⟩,
  { rintro rfl, refl }, { exact subset.antisymm h₂ }
end

instance decidable_circuit_subset (x : finset α) (m : indep E) :
  decidable (∃ (y : finset α) (H : y ⊆ x), is_circuit y m) :=
decidable_of_iff (∃ (y : finset α) (H : y ∈ powerset x), is_circuit y m) $
  by simp only [exists_prop, mem_powerset]

/- should I make this definition reducible? I don't know when to use attributes... -/
def circuits_circ_of_indep (m : indep E) : finset (finset α) :=
(powerset E).filter (λ S, is_circuit S m)

lemma C2_of_indep (m : indep E) (x y : finset α) (hx : x ∈ circuits_circ_of_indep m)
  (hy : y ∈ circuits_circ_of_indep m) (hxy : x ⊆ y) : x = y :=
begin
  simp only [circuits_circ_of_indep, is_circuit, mem_filter] at *,
  have hnxy : ¬x ⊂ y := λ h, hx.2.1 $ hy.2.2 x h,
  rw ←lt_iff_ssubset at hnxy, rw [←le_iff_subset, le_iff_eq_or_lt] at hxy,
  exact or.elim hxy id (λ hxy2, false.elim $ hnxy hxy2)
end

theorem dep_iff_circuit_subset {x : finset α} (m : indep E) :
  x ⊆ E → (x ∉ m.indep ↔ ∃ y ⊆ x, is_circuit y m) :=
λ hxE, iff.intro (λ hxd, exists.elim (min_fun_of_ne_empty card (ne_empty_of_mem $
    mem_filter.mpr ⟨mem_powerset.mpr $ subset.refl x, hxd⟩)) $
  λ a ha, exists.elim ha $
    λ ha2 hamin, exists.intro a $ have hax : a ⊆ x := mem_powerset.mp (mem_filter.mp ha2).1,
      exists.intro hax $ by { unfold is_circuit,
        exact ⟨(mem_filter.mp ha2).2, by { intros y hy, by_contra h,
          exact not_le_of_lt (card_lt_card hy) (hamin y $ mem_filter.mpr ⟨mem_powerset.mpr $
            subset.trans (le_of_lt $ lt_iff_ssubset.mpr hy) hax, h⟩) }⟩ }) $
  λ H, exists.elim H $ λ a ha, exists.elim ha $
    by { intros hax hacirc hxi, unfold is_circuit at hacirc,
    exact hacirc.1 (m.indep_of_subset_indep hxi hax) }

/-- Lemma 1.1.3 -/
lemma C3_of_indep (m : indep E) (x y : finset α) (e : α) (hx : x ∈ circuits_circ_of_indep m)
  (hy : y ∈ circuits_circ_of_indep m) (hxny : x ≠ y) (he : e ∈ x ∩ y) :
  ∃ z, z ∈ circuits_circ_of_indep m ∧ z ⊆ erase (x ∪ y) e :=
have hxmy : x \ y ≠ ∅ := mt subset_iff_sdiff_eq_empty.mpr $ mt (C2_of_indep m x y hx hy) hxny,
  exists.elim (exists_mem_of_ne_empty hxmy) $
    by { clear hxny hxmy,
    intros a ha, simp only [circuits_circ_of_indep, mem_powerset, mem_filter, mem_sdiff, mem_inter]
      at ha hx hy he,
    have hxai : erase x a ∈ m.indep := by { unfold is_circuit at hx,
      exact hx.2.2 (erase x a) (erase_ssubset ha.1) },
    let F := (powerset (x ∪ y)).filter (λ S, erase x a ⊆ S ∧ S ∈ m.indep),
    have hxaF : erase x a ∈ F := mem_filter.2 ⟨mem_powerset.mpr $ subset.trans (erase_subset a x) $
      @subset_union_left _ _ x y, ⟨subset.refl _, hxai⟩⟩, clear hxai,
    exact exists.elim (max_fun_of_ne_empty card $ ne_empty_of_mem hxaF)
      (λ I hEindep_of_subset_indep, exists.elim hEindep_of_subset_indep $ by { clear hxaF hEindep_of_subset_indep,
        exact λ hIF hI,
          have hIFindep : I ∈ m.indep := (mem_filter.mp hIF).2.2,
          have hIdep : _ → I ∉ m.indep := (dep_iff_circuit_subset m $ mem_powerset.1 $
            m.indep_subset_powerset_ground hIFindep).2,
          have hIFxa : erase x a ⊆ I := (mem_filter.mp hIF).2.1,
          have hIxuy : I ⊆ x ∪ y := mem_powerset.mp (mem_filter.mp hIF).1,
          have haniI : a ∉ I :=
            λ H, have hxI : x ⊆ I := (insert_erase ha.1) ▸ insert_subset.mpr ⟨H, hIFxa⟩,
              have ∃ A ⊆ I, is_circuit A m := exists.intro x (exists.intro hxI hx.2),
              hIdep this hIFindep,
          have hEg : ∃ g ∈ y, g ∉ I :=
            by { have hIdep2 := mt hIdep, simp only [not_exists, exists_prop, not_and, not_not]
              at hIdep2,
            have hyI0 := mt (hIdep2 hIFindep y), simp only [not_not] at hyI0,
            have hYI : ¬y ⊆ I := hyI0 hy.2,
            have this := exists_mem_of_ne_empty (mt subset_iff_sdiff_eq_empty.mpr hYI),
            simp only [mem_sdiff] at this, simpa only [exists_prop] },
          exists.elim hEg $ λ g hEg2, exists.elim hEg2 $ by { clear hEg hEg2 hIdep,
            intros hgy hgnI,
            have hga : g ≠ a := λ H, ha.2 (H ▸ hgy),
            have hIag : I ⊆ erase (erase (x ∪ y) a) g :=
              subset_iff.mpr (λ xx hxx, mem_erase.mpr ⟨λ hgg, hgnI $ hgg ▸ hxx,
                mem_erase.mpr ⟨λ hgga, haniI $ hgga ▸ hxx, mem_of_subset hIxuy hxx⟩⟩),
            have haxuy : a ∈ x ∪ y := mem_union_left y ha.1,
            have hcardxye : card (erase (x ∪ y) a) = nat.pred (card (x ∪ y)) :=
              card_erase_of_mem haxuy,
            have hpcard : nat.pred (card (x ∪ y)) > 0 := by { rw ←hcardxye,
              exact card_pos.mpr (ne_empty_of_mem $ mem_erase.mpr ⟨hga, mem_union_right x hgy⟩) },
            have hcard : card I < card (erase (x ∪ y) e) :=
              calc card I ≤ card (erase (erase (x ∪ y) a) g) : card_le_of_subset hIag
              ... = nat.pred (nat.pred (card (x ∪ y))) : by rw [card_erase_of_mem
                (mem_erase.mpr ⟨hga, mem_union_right x hgy⟩), hcardxye]
              ... < card (erase (x ∪ y) e) :
                by { rw [card_erase_of_mem (mem_union_left y he.1),
                ←nat.succ_pred_eq_of_pos hpcard], exact nat.lt_succ_self _ },
            clear hga hIag haxuy hcardxye hpcard he,
            by_contra h, simp only [circuits_circ_of_indep, mem_powerset, not_exists, and_imp,
              mem_filter, not_and] at h,
            have hinE : erase (x ∪ y) e ⊆ E :=
              subset.trans (erase_subset e (x ∪ y)) (union_subset hx.1 hy.1),
            have : (∀ x_1 : finset α, x_1 ⊆ erase (x ∪ y) e → ¬is_circuit x_1 m) :=
              λ x1 hx1, (mt $ h x1 $ subset.trans hx1 hinE) $ not_not.mpr hx1,
            have hindep := mt (dep_iff_circuit_subset m hinE).mp,
              simp only [not_exists, exists_prop, not_and, not_not] at hindep,
            replace hindep : erase (x ∪ y) e ∈ m.indep := hindep this,
            have hfinal := m.indep_exch hIFindep hindep hcard,
            exact exists.elim hfinal (λ El ⟨hElxy, hElindep⟩,
              have hElF : insert El I ∈ F := mem_filter.mpr ⟨mem_powerset.mpr
                (insert_subset.mpr ⟨(mem_erase.mp (mem_sdiff.mp hElxy).1).2, hIxuy⟩),
                ⟨subset.trans hIFxa (subset_insert El I), hElindep⟩⟩,
              have hcardEl : card I < card (insert El I) :=
                by { rw card_insert_of_not_mem (mem_sdiff.mp hElxy).2,
                exact lt_add_one (card I) },
              not_lt.mpr (hI (insert El I) hElF) hcardEl) } }) }

structure circuits (E : finset α) :=
(circuits : finset (finset α))
(circuits_subset_powerset_ground : circuits ⊆ powerset E)
-- (C1)
(empty_not_mem_circuits : ∅ ∉ circuits)
-- (C2)
(circuits_eq_of_subset {x y} (hx : x ∈ circuits) (hy : y ∈ circuits) (hxy : x ⊆ y) : x = y)
-- (C3)
(circuit_elim {x y e} (hx : x ∈ circuits) (hy : y ∈ circuits) (hxy : x ≠ y) (he : e ∈ x ∩ y) :
  ∃ z, z ∈ circuits ∧ z ⊆ erase (x ∪ y) e)
--attribute [class] circuits

instance circuits_repr [has_repr α] (E : finset α) : has_repr (circuits E) :=
⟨λ c, has_repr.repr c.circuits⟩

theorem eq_of_circ_eq : ∀ {C₁ C₂ : circuits E}, C₁.1 = C₂.1 → C₁ = C₂
  | ⟨c₁, p₁, q₁, r₁, s₁⟩ ⟨c₂, p₂, q₂, r₂, s₂⟩ h :=
by simpa only []

def circuits_of_indep (m : indep E) : circuits E :=
{ circuits := circuits_circ_of_indep m,
  circuits_subset_powerset_ground := filter_subset _,
  empty_not_mem_circuits :=
    begin
      simp only [circuits_circ_of_indep, is_circuit, mem_filter, not_and],
      exact λ h h1, (h1 m.empty_mem_indep).elim
    end,
  circuits_eq_of_subset := C2_of_indep m,
  circuit_elim := C3_of_indep m }

/- make reducible? -/
def indep_indep_of_circuits (C : circuits E) : finset (finset α) :=
(powerset E).filter (λ S, ∀ c ∈ C.circuits, ¬c ⊆ S)

/-- first part of Theorem 1.1.4 -/
lemma indep_of_subset_indep_of_circuits (C : circuits E) (x y : finset α) : x ∈ indep_indep_of_circuits C → y ⊆ x →
  y ∈ indep_indep_of_circuits C :=
begin
  simp only [indep_indep_of_circuits, mem_powerset, and_imp, mem_filter],
  exact λ hxE hx hxy, ⟨subset.trans hxy hxE, λ c hc H, hx c hc $ subset.trans H hxy⟩
end

/-- second part of Theorem 1.1.4 -/
lemma I3_of_circuits (C : circuits E) (x y : finset α) (hx : x ∈ indep_indep_of_circuits C)
  (hy : y ∈ indep_indep_of_circuits C) (hcardxy : card x < card y)
  : ∃ e, e ∈ y \ x ∧ insert e x ∈ indep_indep_of_circuits C :=
begin
  unfold indep_indep_of_circuits at ⊢,
  simp only [indep_indep_of_circuits, mem_powerset, mem_filter] at hx hy,
  by_contra h,
  simp only [mem_powerset, not_exists, and_imp, mem_filter, not_and, mem_sdiff] at h,
  let F := (powerset $ x ∪ y).filter (λ S, (∀ c ∈ C.circuits, ¬c ⊆ S) ∧ card x < card S),
  have hyF : y ∈ F := mem_filter.mpr ⟨mem_powerset.mpr $ subset_union_right x y,
    ⟨hy.2, hcardxy⟩⟩,
  exact exists.elim (min_fun_of_ne_empty (λ f, card (x \ f)) $ ne_empty_of_mem hyF)
    (λ z Hz, exists.elim Hz $ by { clear hcardxy Hz hyF,
      intros hz hminz,
      have hzxuy : z ⊆ x ∪ y := mem_powerset.mp (mem_filter.mp hz).1,
      replace hz := (mem_filter.mp hz).2,
      exact exists.elim (exists_sdiff_of_card_lt hz.2)
        (by { intros a ha, rw mem_sdiff at ha,
        have hxsdiffz : x \ z ≠ ∅ :=
          by { intro H,
          have Hxsubz : x ⊆ z := subset_iff_sdiff_eq_empty.mpr H,
          have hay : a ∈ y := or.elim (mem_union.mp $ mem_of_subset hzxuy ha.1)
            (λ Hax, false.elim $ ha.2 Hax) id,
          have haindep : insert a x ∈ indep_indep_of_circuits C := indep_of_subset_indep_of_circuits C z (insert a x)
            (by { simp only [indep_indep_of_circuits, mem_powerset, mem_filter],
            exact ⟨subset.trans hzxuy $ union_subset hx.1 hy.1, hz.1⟩ })
            (insert_subset.mpr ⟨ha.1, Hxsubz⟩),
          simp only [indep_indep_of_circuits, mem_powerset, mem_filter] at haindep,
          exact h a hay ha.2 haindep.1 haindep.2 },
        exact exists.elim (exists_mem_of_ne_empty hxsdiffz)
          (by { clear h ha hxsdiffz,
          intros e he, rw mem_sdiff at he,
          let T : α → finset α := λ f, erase (insert e z) f,
          have hTf1 : ∀ f, f ∈ z \ x → T f ⊆ x ∪ y :=
            by { intros f hf, rw [mem_sdiff] at hf,
            rw [subset_iff],
            intros gg hgg, simp only [mem_insert, mem_erase, ne.def] at hgg,
            simp only [mem_union],
            exact or.elim hgg.2 (λ gge, or.inl $ gge.symm ▸ he.1)
              (λ ggz, mem_union.mp $ mem_of_subset hzxuy ggz) },
          have hTf2 : ∀ f, f ∈ z \ x → card (x \ T f) < card (x \ z) :=
            by { intros f hf, rw mem_sdiff at hf,
            suffices H : x \ T f ⊂ x \ z, exact card_lt_card H,
            by { simp only [ssubset_iff_subset_ne, exists_prop, mem_insert, not_forall_not, not_and,
                            mem_sdiff, mem_erase],
              exact exists.intro e
                ⟨λ h_, ⟨λ hef, hf.2 $ hef ▸ he.1, or.inl rfl⟩,
                by { rw [subset_iff],
                  intros gg hgg,
                  simp only [mem_insert, not_and, mem_sdiff, mem_erase, ne.def] at hgg,
                  have ggnef : gg ≠ f := λ ggef, or.elim hgg
                    (λ gge, (gge.symm ▸ he.2) $ ggef.substr hf.1) (λ H, (ggef.substr hf.2) H.1),
                  have he0 := mem_sdiff.mpr he,
                  exact or.elim hgg (λ gge, gge.symm ▸ he0)
                  (λ H, mem_sdiff.mpr ⟨H.1, λ ggz, (H.2 ggnef) $ or.inr ggz⟩) }⟩ } },
          have hTfindep : ∀ f, f ∈ z \ x → T f ∉ indep_indep_of_circuits C :=
            by { intros f hf,
            simp only [indep_indep_of_circuits, mem_powerset, mem_filter, not_and],
            intros hTfE H,
            have HTf1 : T f ⊆ x ∪ y := hTf1 f hf,
            have HTf2 : card (x \ T f) < card (x \ z) := hTf2 f hf,
            rw mem_sdiff at hf,
            have HTfcard : card z = card (T f) :=
              by { simp only [card_erase_of_mem (mem_insert.mpr $ or.inr hf.1),
              card_insert_of_not_mem he.2, mem_insert, card_insert_of_not_mem, nat.pred_succ] },
            replace HTfcard : card x < card (T f) := HTfcard ▸ hz.2,
            have : T f ∈ F := mem_filter.mpr ⟨mem_powerset.mpr HTf1, ⟨H, HTfcard⟩⟩,
            exact not_lt.mpr (hminz (T f) this) HTf2 },
          have hTfC : ∀ f, f ∈ z \ x → ∃ c ∈ C.circuits, c ⊆ T f :=
            by { intros f hf,
            have : T f ∉ indep_indep_of_circuits C := hTfindep f hf,
              simp only [indep_indep_of_circuits, mem_powerset, mem_filter, not_and] at this,
            have hfc := this (subset.trans (hTf1 f hf) $ union_subset hx.1 hy.1),
            by_contra H, simp only [not_exists, exists_prop, not_and] at H, contradiction },
          exact exists.elim (exists_sdiff_of_card_lt hz.2) (λ g hg, exists.elim (hTfC g hg) $
              λ Cg hCg, exists.elim hCg $
                by { clear hCg hTf1 hTf2 hTfindep hg,
                intros HCg1 HCg2,
                have hCgsub : Cg ⊆ insert e z := subset.trans HCg2 (erase_subset g $ insert e z),
                rw [subset_iff] at HCg2,
                have HCgzx : Cg ∩ (z \ x) ≠ ∅ :=
                  λ H, suffices Cg ⊆ x, from hx.2 Cg HCg1 this,
                    suffices H1 : Cg ⊆ erase (insert e (x ∩ z)) g, from
                    suffices H2 : erase (insert e (x ∩ z)) g ⊆ x, from
                    subset.trans H1 H2,
                    show erase (insert e (x ∩ z)) g ⊆ x, by
                      { rw [subset_iff],
                      intros gg hgg,
                      simp only [mem_insert, mem_erase, mem_inter] at hgg,
                      exact or.elim hgg.2 (λ gge, gge.symm ▸ he.1) (λ ggxggz, ggxggz.1) },
                    show Cg ⊆ erase (insert e (x ∩ z)) g, by
                      { rw [subset_iff],
                      intros gg hgg,
                      replace HCg2 : gg ∈ T g := HCg2 hgg,
                      simp only [mem_insert, mem_erase, mem_inter] at HCg2 ⊢,
                      split,
                        { exact HCg2.1 },
                        { rw eq_empty_iff_forall_not_mem at H,
                        replace H : gg ∉ Cg ∩ (z \ x) := H gg,
                        simp only [not_and, mem_sdiff, not_not, mem_inter] at H,
                      exact or.elim HCg2.2 (λ gge, or.inl gge) (λ ggz, or.inr ⟨H hgg ggz, ggz⟩) } },
                clear HCg2,
                exact exists.elim (exists_mem_of_ne_empty HCgzx)
                  (by { intros h0 hh0, rw [mem_inter] at hh0,
                  exact exists.elim (hTfC h0 hh0.2)
                    (λ Ch0 HCh0, exists.elim HCh0 $ λ hCh0circ hCh0T,
                      have hCgneCh0 : Cg ≠ Ch0 :=
                        λ H, have hh0Ch0 : h0 ∉ Ch0 := λ HH, (mem_erase.mp $
                          mem_of_subset hCh0T HH).1 rfl, (H.symm ▸ hh0Ch0) hh0.1,
                      have hCh0sub : Ch0 ⊆ insert e z :=
                        subset.trans hCh0T (erase_subset h0 $ insert e z),
                      have heCgCh0 : e ∈ Cg ∩ Ch0 :=
                        by { rw mem_inter, split,
                          { by_contra heCg, have hCgz : Cg ⊆ z :=
                              (erase_eq_of_not_mem heCg) ▸ (subset_insert_iff.mp hCgsub),
                            exact hz.1 Cg HCg1 hCgz },
                          { by_contra heCh0, have hCh0z : Ch0 ⊆ z :=
                              (erase_eq_of_not_mem heCh0) ▸ (subset_insert_iff.1 hCh0sub),
                            exact hz.1 Ch0 hCh0circ hCh0z } },
                      exists.elim (C.circuit_elim HCg1 hCh0circ hCgneCh0 heCgCh0) $
                        λ CC ⟨hCCcirc, hCCCguCh0⟩,
                          have hCCz : CC ⊆ z :=
                            by { rw [subset_iff],
                            intros t ht,
                            rw [subset_iff] at hCCCguCh0,
                            have htCguCh0 := hCCCguCh0 ht,
                              simp only [mem_union, mem_erase] at htCguCh0,
                            rw [subset_iff] at hCgsub hCh0sub,
                            have orCg : t ∈ Cg → t ∈ z :=
                              λ htCg, or.elim (mem_insert.mp $ hCgsub htCg)
                                (λ H, false.elim $ htCguCh0.1 H) id,
                            have orCh0 : t ∈ Ch0 → t ∈ z :=
                              λ htCh0, or.elim (mem_insert.mp $ hCh0sub htCh0)
                              (λ H, false.elim $ htCguCh0.1 H) id,
                            exact or.elim htCguCh0.2 orCg orCh0 },
                          hz.1 CC hCCcirc hCCz) }) }) }) }) })
end

def indep_of_circuits (C : circuits E) : indep E :=
⟨indep_indep_of_circuits C,
by simp only [indep_indep_of_circuits, filter_subset],
mem_filter.mpr
  ⟨empty_mem_powerset E, λ c hc H, C.empty_not_mem_circuits $ (subset_empty.mp H) ▸ hc⟩,
indep_of_subset_indep_of_circuits C,
I3_of_circuits C⟩

instance circ_indep : has_coe (circuits E) (indep E) := ⟨indep_of_circuits⟩
instance indep_circ : has_coe (indep E) (circuits E) := ⟨circuits_of_indep⟩

/-- third part of Theorem 1.1.4 -/
theorem circ_indep_circ : ∀ C : circuits E, C = circuits_of_indep (indep_of_circuits C)
  | ⟨c₁, p₁, q₁, r₁, s₁⟩ :=
by { simp only [indep_of_circuits, circuits_of_indep, indep_indep_of_circuits,
  circuits_circ_of_indep, is_circuit, ext, mem_filter, mem_powerset, and_imp, not_and],
exact λ c, iff.intro
  (λ hc : c ∈ c₁, have ce : c ⊆ E := mem_powerset.mp (mem_of_subset p₁ hc),
  ⟨ce, ⟨λ _ H, (H c hc) $ subset.refl c, λ f hf,
    ⟨subset.trans (le_of_lt $ lt_iff_ssubset.mpr hf) ce,
    λ g hg H, have Hc : g < c := lt_of_le_of_lt (le_iff_subset.mpr H) $ lt_iff_ssubset.mpr hf,
      have r : g = c := r₁ hg hc $ le_of_lt Hc, (not_le_of_lt Hc) $ le_of_eq r.symm⟩⟩⟩) $
  λ hc, have ∃ c_1 ∈ c₁, c_1 ⊆ c := by { have := not_forall.mp (hc.2.1 hc.1),
    simpa only [exists_prop, not_forall_not] },
  exists.elim this $ λ c' H, exists.elim H $ by { intros hc' hcc',
    by_cases h : c = c', { exact h.symm ▸ hc' },
      { have hc'lt : c' ⊂ c := lt_of_le_of_ne (le_iff_subset.mpr hcc') (ne.symm h),
        have : c' ∉ c₁ := mt ((hc.2.2 c' hc'lt).2 c') (not_not.mpr $ subset.refl c'),
        exact false.elim (this hc') } } }

theorem indep_circ_indep (M : indep E) : M = indep_of_circuits (circuits_of_indep M) :=
suffices M.indep = (indep_of_circuits $ circuits_of_indep M).indep, from eq_of_indep_eq this,
begin
  simp only [circuits_of_indep, indep_of_circuits, circuits_circ_of_indep, indep_indep_of_circuits,
    ext, mem_powerset, and_imp, mem_filter],
  intro I,
  have hI : I ∈ M.indep → I ⊆ E := λ H, mem_powerset.mp $
    mem_of_subset (M.indep_subset_powerset_ground) H,
  rw [←and_iff_right_of_imp hI, and_congr_right],
  intro hIE, have := not_iff_not_of_iff (dep_iff_circuit_subset M hIE),
  simp only [not_exists, exists_prop, not_and, not_not] at this,
  rw [this, forall_congr],
  exact λ a, ⟨λ h h₁ h₂ h₃, (h h₃) h₂, λ h h₁ h₂, h (subset.trans h₁ hIE) h₂ h₁⟩
end

/-- Proposition 1.1.6 -/
theorem existsu_circuit_of_dep_of_insert_indep {I : finset α} {e : α} {m : indep E}
  (hI : I ∈ m.indep) (he : e ∈ E) (hIe : insert e I ∉ m.indep) :
  ∃ c, c ∈ circuits_circ_of_indep m ∧ c ⊆ insert e I ∧ e ∈ c ∧
  ∀ c' ∈ circuits_circ_of_indep m, c' ⊆ insert e I ∧ e ∈ c → c' = c :=
by { simp only [circuits_circ_of_indep, mem_powerset, and_imp, mem_filter],
exact have hIE : I ⊆ E, from mem_powerset.mp (mem_of_subset m.indep_subset_powerset_ground hI),
have hIeE : insert e I ⊆ E, from insert_subset.mpr ⟨he, hIE⟩,
have hc : _, from (dep_iff_circuit_subset m hIeE).mp hIe,
exists.elim hc $ λ c hEc, exists.elim hEc $ λ hceI hccirc,
  have hcE : c ⊆ E := subset.trans hceI hIeE,
  have hecirc : ∀ c' ⊆ insert e I, is_circuit c' m → e ∈ c' :=
    by { intros c' hc'eI hc'circ,
    have h₁ := subset_insert_iff.mp hc'eI,
    by_contra h,
    have h₂ := (erase_eq_of_not_mem h).symm,
    have h₃ : c' ⊆ I := calc
    c' = erase c' e : h₂
    ... ⊆ I : h₁,
    exact (dep_iff_circuit_subset m hIE).mpr (exists.intro c' $ exists.intro h₃ $ hc'circ) hI },
  have hec : e ∈ c := hecirc c hceI hccirc,
  exists.intro c $ by { exact ⟨⟨hcE, hccirc⟩, ⟨hceI,⟨hec, by { intros c' hc'E hc'circ hc'eI _,
    have hec' : e ∈ c' := hecirc c' hc'eI hc'circ,
    have hcuc'eI : erase (c ∪ c') e ⊆ I := by {
      simp only [subset_iff, and_imp, mem_union, mem_insert, mem_erase, ne.def] at hceI hc'eI ⊢,
      exact λ a hane ha, or.elim ha (λ H, or.elim (hceI H) (λ H, false.elim $ hane H) id)
        (λ H, or.elim (hc'eI H) (λ H, false.elim $ hane H) id) },
    have : erase (c ∪ c') e ∈ m.indep := m.indep_of_subset_indep hI hcuc'eI,
    by_contra h,
    have C3 := C3_of_indep m c c' e,
      simp only [circuits_circ_of_indep, mem_powerset, and_imp,
        filter_congr_decidable, mem_filter, mem_inter] at C3,
    exact exists.elim (C3 hcE hccirc hc'E hc'circ (ne.symm h) hec hec')
      (λ c₀ hc₀, (dep_iff_circuit_subset m hIE).mpr (exists.intro c₀ $ exists.intro
        (subset.trans hc₀.2 hcuc'eI) hc₀.1.2) hI) }⟩⟩⟩ } }

section encodable
variable [encodable α]

def circuit_of_dep_of_insert_indep {I : finset α} {e : α} {m : indep E}
  (hI : I ∈ m.indep) (he : e ∈ E) (hIe : insert e I ∉ m.indep) : finset α :=
encodable.choose (existsu_circuit_of_dep_of_insert_indep hI he hIe)

local notation `cdii` := circuit_of_dep_of_insert_indep

def circuit_of_dep_of_insert_indep_spec {I : finset α} {e : α} {m : indep E}
  (hI : I ∈ m.indep) (he : e ∈ E) (hIe : insert e I ∉ m.indep) :
  cdii hI he hIe ∈ circuits_circ_of_indep m ∧ cdii hI he hIe ⊆ insert e I ∧
  e ∈ cdii hI he hIe ∧ ∀ (c' : finset α), c' ∈ circuits_circ_of_indep m →
  c' ⊆ insert e I ∧ e ∈ cdii hI he hIe → c' = cdii hI he hIe  :=
encodable.choose_spec (existsu_circuit_of_dep_of_insert_indep hI he hIe)

end encodable

-- § 1.2

def is_basis (x : finset α) (m : indep E) : Prop :=
x ∈ m.indep ∧ (∀ y ⊆ E, x ⊂ y → y ∉ m.indep)

instance decidable_basis (x : finset α) (m : indep E) : decidable (is_basis x m) :=
decidable_of_iff (x ∈ m.indep ∧ (∀ y ∈ powerset E, x ⊂ y → y ∉ m.indep)) $
  by simp only [is_basis, iff_self, finset.mem_powerset]

/-- Lemma 1.2.1 -/
theorem bases_of_indep_card_eq {x y : finset α} {m : indep E} : is_basis x m → is_basis y m →
  card x = card y :=
begin
  intros hx hy,
  by_contra heq,
  wlog h : card x < card y using [x y, y x],
  exact lt_or_gt_of_ne heq,
  unfold is_basis at hx hy,
  exact exists.elim (m.indep_exch hx.1 hy.1 h) (λ e ⟨he1, he2⟩,
    have hins : insert e x ⊆ E := mem_powerset.mp
      (mem_of_subset (m.indep_subset_powerset_ground) he2),
    have hememx : e ∉ x := (mem_sdiff.mp he1).2,
    (hx.2 (insert e x) hins $ ssubset_insert hememx) he2)
end

theorem exists_basis_containing_indep {I : finset α} {m : indep E} (h : I ∈ m.indep) :
  ∃ B : finset α, I ⊆ B ∧ is_basis B m :=
let F := (m.indep).filter (λ a, I ⊆ a) in
have FI : I ∈ F := mem_filter.mpr ⟨h, subset.refl I⟩,
exists.elim (max_fun_of_ne_empty card $ ne_empty_of_mem FI) $
  λ B HB, exists.elim HB $ by { clear HB, intros HBF Hg, rw mem_filter at HBF,
    have hBB : is_basis B m := ⟨HBF.1, λ y hy hBy hyI,
      have hxsy : I ⊆ y := le_of_lt $ lt_of_le_of_lt (le_iff_subset.mpr HBF.2) $
        lt_iff_ssubset.mpr hBy,
      have hyF : y ∈ F := mem_filter.mpr ⟨hyI, hxsy⟩,
      lt_irrefl (card B) $ lt_of_lt_of_le (card_lt_card hBy) $ Hg y hyF⟩,
    exact exists.intro B ⟨HBF.2, hBB⟩ }

section encodable

def basis_containing_indep [encodable α] {I : finset α} {m : indep E} (h : I ∈ m.indep) :
  finset α :=
encodable.choose $ exists_basis_containing_indep h

local notation `bci` := basis_containing_indep

def basis_containing_indep_spec [encodable α] {I : finset α} {m : indep E} (h : I ∈ m.indep) :
  I ⊆ bci h ∧ is_basis (bci h) m :=
encodable.choose_spec $ exists_basis_containing_indep h

end encodable

theorem dep_of_card_gt_card_basis {x B : finset α} {m : indep E} (hB : is_basis B m)
  (hcard : card B < card x) : x ∉ m.indep :=
λ hxI, exists.elim (exists_basis_containing_indep hxI) $ λ B' hB',
  ne_of_lt (lt_of_lt_of_le hcard $ card_le_of_subset hB'.1) $ bases_of_indep_card_eq hB hB'.2

theorem card_of_indep_le_card_basis {x B : finset α} {m : indep E} (hx : x ∈ m.indep)
  (hB : is_basis B m) : card x ≤ card B :=
by { by_contra h, exact dep_of_card_gt_card_basis hB (lt_of_not_ge h) hx }

structure bases (E : finset α) :=
(bases : finset (finset α))
(bases_subset_powerset_ground : bases ⊆ powerset E)
-- (B1)
(bases_not_empty : bases ≠ ∅)
-- (B2)
(basis_exch {x y e} (hx : x ∈ bases) (hy : y ∈ bases) (he : e ∈ x \ y)
    : ∃ a, a ∈ y \ x ∧ insert a (erase x e) ∈ bases)
--attribute [class] bases

instance bases_repr [has_repr α] (E : finset α) : has_repr (bases E) :=
⟨λ b, has_repr.repr b.bases⟩

theorem eq_of_base_eq : ∀ {B₁ B₂ : bases E}, B₁.1 = B₂.1 → B₁ = B₂
  | ⟨b₁, p₁, q₁, r₁⟩ ⟨b₂, p₂, q₂, r₂⟩ h :=
by simpa only []

def bases_bases_of_indep (m : indep E) : finset (finset α) :=
(powerset E).filter (λ S, is_basis S m)

lemma B1_of_indep (m : indep E) : bases_bases_of_indep m ≠ ∅ :=
by { simp only [is_basis, bases_bases_of_indep, ext, ne.def, mem_filter, mem_powerset,
    not_mem_empty, not_and, iff_false],
  exact λ h, exists.elim (max_fun_of_ne_empty card $ ne_empty_of_mem m.empty_mem_indep)
  (λ a ha, exists.elim ha $ λ ha1 hg, (h a (mem_powerset.mp $
    mem_of_subset m.indep_subset_powerset_ground ha1)
  ha1) $ λ F _ Fcontainsa Findep, not_le_of_lt (card_lt_card Fcontainsa) $ hg F Findep) }

/- Lemma 1.2.2 -/
lemma B2_of_indep (m : indep E) : ∀ (x y : finset α) (e : α), x ∈ bases_bases_of_indep m →
  y ∈ bases_bases_of_indep m → e ∈ x \ y →
  ∃ a, a ∈ y \ x ∧ insert a (erase x e) ∈ bases_bases_of_indep m :=
by { simp only [is_basis, bases_bases_of_indep, filter_and, mem_filter, mem_sdiff,
  mem_powerset, and_imp],
exact λ x y e hxE hxI hx hyE hyI hy hex hey,
  have hxr : erase x e ∈ m.indep := m.indep_of_subset_indep hxI $ erase_subset e x,
  have hxB : is_basis x m := ⟨hxI, hx⟩, have hyB : is_basis y m := ⟨hyI, hy⟩,
  have hcard : card (erase x e) < card y := calc
    card (erase x e) < card x : card_lt_card $ erase_ssubset hex
    ... = card y : bases_of_indep_card_eq hxB hyB,
  exists.elim (m.indep_exch hxr hyI hcard) $
    by { clear hxr hyI hcard hyB, intros a ha,
      have ha1 := mem_sdiff.mp ha.1,
      have hae : a ≠ e := λ hae, hey $ hae ▸ ha1.1,
      have hax : a ∉ x := by { simp only [not_and, mem_erase, ne.def] at ha1, exact ha1.2 hae },
      have hcx : card x > 0 := card_pos.mpr (ne_empty_of_mem hex),
      have hayycard : card (insert a $ erase x e) = card x := calc
        card (insert a $ erase x e) = nat.pred (card x) + 1 : by rw [card_insert_of_not_mem ha1.2,
            card_erase_of_mem hex]
        ... = card x : nat.succ_pred_eq_of_pos hcx,
      exact exists.intro a ⟨⟨ha1.1, hax⟩, mem_powerset.mp $
        mem_of_subset m.indep_subset_powerset_ground ha.2, ha.2,
        λ _ _ hayy, dep_of_card_gt_card_basis hxB $ hayycard ▸ (card_lt_card hayy)⟩ } }

def bases_of_indep (m : indep E) : bases E :=
⟨bases_bases_of_indep m,
filter_subset _,
B1_of_indep m,
B2_of_indep m⟩

/-- Lemma 1.2.4 -/
theorem bases_card_eq {x y : finset α} {b : bases E} (hx : x ∈ b.bases) (hy : y ∈ b.bases) :
  card x = card y :=
begin
  by_contra heq,
  wlog h : card y < card x using [x y, y x],
  exact lt_or_gt_of_ne (ne.symm heq), clear heq,
  let F : finset (finset α × finset α) := (finset.product b.bases b.bases).filter
    (λ e : finset α × finset α, card e.1 < card e.2),
  have hyx : (y, x) ∈ F := mem_filter.mpr ⟨mem_product.mpr ⟨hy, hx⟩, h⟩, clear hy hx,
  exact exists.elim (min_fun_of_ne_empty (λ f : finset α × finset α, card (f.2 \ f.1)) $
      ne_empty_of_mem hyx)
    (λ a ha, exists.elim ha $ by { clear hyx ha,
      intros haF Ha, replace haF := mem_filter.mp haF,
      have hab : a.1 ∈ b.bases ∧ a.2 ∈ b.bases := mem_product.mp haF.1,
      exact exists.elim (exists_sdiff_of_card_lt haF.2)
        (λ e he, exists.elim (b.basis_exch hab.2 hab.1 he) $ λ aa ⟨haa1, haa2⟩,
          by { rw mem_sdiff at haa1,
          let a2 : finset α := insert aa (erase a.2 e),
          have haani : aa ∉ erase a.2 e := λ h, haa1.2 (mem_erase.mp h).2,
          have hea2 : e ∈ a.2 := (mem_sdiff.mp he).1,
          have hpos : 0 < card a.2 := card_pos.mpr (ne_empty_of_mem hea2),
          have hcarda2 : card a.1 < card a2 := by { rw [card_insert_of_not_mem haani,
            card_erase_of_mem hea2, ←nat.succ_eq_add_one, nat.succ_pred_eq_of_pos hpos],
            exact haF.2 }, clear haani hpos,
          have : e ∉ a2 := λ hh, or.elim (mem_insert.mp hh)
            (λ h4, haa1.2 $ h4 ▸ hea2) $ λ h5, (mem_erase.mp h5).1 rfl,
          have hcard : card (a2 \ a.1) < card (a.2 \ a.1) :=
            suffices a2 \ a.1 ⊂ a.2 \ a.1, from card_lt_card this,
            by { rw ssubset_iff,
            exact exists.intro e ⟨λ h0, this (mem_sdiff.mp h0).1,
              by { rw subset_iff,
              intros A hA, rw mem_insert at hA,
              exact or.elim hA (λ hA1, hA1.symm ▸ he)
                (by { intro hA2, rw [mem_sdiff, mem_insert] at hA2,
                exact mem_sdiff.mpr ⟨or.elim hA2.1 (λ h6, false.elim $ hA2.2 $ h6.symm ▸ haa1.1) $
                  λ h7, (mem_erase.mp h7).2, hA2.2⟩ }) }⟩ },
          have ha2F : (a.1, a2) ∈ F := mem_filter.mpr ⟨mem_product.mpr ⟨hab.1, haa2⟩, hcarda2⟩,
          exact not_le_of_lt hcard (Ha (a.1, a2) ha2F) }) })
end

def indep_indep_of_bases (b : bases E) : finset (finset α) :=
(powerset E).filter (λ x, ∃ a ∈ b.bases, x ⊆ a)

/-- first part of Theorem 1.2.3 -/
def indep_of_bases (b : bases E) : indep E :=
⟨indep_indep_of_bases b,
filter_subset _,
mem_filter.mpr ⟨empty_mem_powerset E, exists.elim (exists_mem_of_ne_empty b.bases_not_empty) $
    λ a ha, exists.intro a $ exists.intro ha $ empty_subset a⟩,
begin
  intros x y hx hxy, simp only [indep_indep_of_bases, mem_powerset, filter_congr_decidable,
    exists_prop, mem_filter] at hx ⊢,
  exact ⟨subset.trans hxy hx.1,
    exists.elim hx.2 $ λ a ha, exists.intro a ⟨ha.1, subset.trans hxy ha.2⟩⟩
end,
begin
  intros x y hx hy hcard, unfold indep_indep_of_bases at *,
  let F := (b.bases).filter (λ S, S ⊆ y),
  by_contra h, simp only [mem_powerset, not_exists, and_imp, filter_congr_decidable,
    exists_prop, mem_filter, not_and, mem_sdiff] at hx hy h,
  exact exists.elim hx.2 (λ b1 hb1, exists.elim hy.2 $ λ b2 hb2, exists.elim
    (min_fun_of_ne_empty (λ f, card (f \ (y ∪ b1))) $ ne_empty_of_mem $ mem_filter.mpr hb2) $
    λ B2 hEB2, exists.elim hEB2 $ by { clear hb2 b2 hEB2,
      intros hB2filt hB2min, replace hB2filt : B2 ∈ b.bases ∧ y ⊆ B2 := mem_filter.mp hB2filt,
      have hysdiff : y \ b1 = y \ x := by { simp only [ext, mem_sdiff],
        exact λ gg, ⟨λ hgg, ⟨hgg.1, λ hggnx, hgg.2 $ mem_of_subset hb1.2 hggnx⟩,
          λ hgg, ⟨hgg.1, λ ggb1, h gg hgg.1 hgg.2 (insert_subset.mpr
          ⟨mem_of_subset hy.1 hgg.1, hx.1⟩) b1 hb1.1 $ insert_subset.mpr ⟨ggb1, hb1.2⟩⟩⟩ },
      have hB2yub1: B2 \ (y ∪ b1) = ∅ := by { by_contra H,
        exact exists.elim (exists_mem_of_ne_empty H) (by { clear H,
          intros X hX, simp only [not_or_distrib, mem_union, mem_sdiff] at hX,
          have hXB2b1 : X ∈ B2 \ b1 := by { rw mem_sdiff, exact ⟨hX.1, hX.2.2⟩ },
          exact exists.elim (b.basis_exch hB2filt.1 hb1.1 hXB2b1)
            (λ Y ⟨hYb1B2, hYbases⟩, by { rw mem_sdiff at hYb1B2 hXB2b1,
              have hssubY : insert Y (erase B2 X) \ (y ∪ b1) ⊂  B2 \ (y ∪ b1) :=
                by { rw [ssubset_iff],
                exact exists.intro X (by {
                  simp only [subset_iff, not_or_distrib, mem_union, mem_insert, not_and, mem_sdiff,
                    not_not, mem_erase, not_true, or_false, ne.def, false_and, or_false,
                    eq_self_iff_true],
                  exact ⟨λ hXY, false.elim $ hYb1B2.2 (hXY ▸ hXB2b1.1),
                  λ gg hgg, or.elim hgg (λ ggx, ggx.symm ▸ hX) $ λ ggor2, or.elim ggor2.1
                    (λ ggY, false.elim $ (ggY ▸ ggor2.2.2) hYb1B2.1) $
                      λ ggXB2, ⟨ggXB2.2, ggor2.2⟩⟩ }) },
              replace hssubY := card_lt_card hssubY,
              have hysubY : y ⊆ insert Y (erase B2 X) := by {
                simp only [subset_iff, mem_insert, mem_erase, ne.def],
                exact λ gg hgg, or.inr ⟨λ ggx, hX.2.1 $ ggx ▸ hgg, mem_of_subset hB2filt.2 hgg⟩ },
              exact not_lt_of_le (hB2min (insert Y $ erase B2 X) $ mem_filter.mpr
                  ⟨hYbases, hysubY⟩) hssubY }) }) }, clear hB2min,
      rw [←subset_iff_sdiff_eq_empty, subset_iff] at hB2yub1, simp only [mem_union] at hB2yub1,
      have hB2b1y : B2 \ b1 = y \ b1 := by { simp only [ext, mem_sdiff],
        exact λ gg, ⟨λ hgg, ⟨or.elim (hB2yub1 hgg.1) id $ λ hb1, false.elim $ hgg.2 hb1, hgg.2⟩,
            λ hgg, ⟨mem_of_subset hB2filt.2 hgg.1, hgg.2⟩⟩ },
      rw [hysdiff] at hB2b1y, clear hysdiff,
      have hb1xuB2 : b1 \ (x ∪ B2) = ∅ := by { by_contra H,
        exact exists.elim (exists_mem_of_ne_empty H)
          (by { intros X hX, simp only [not_or_distrib, mem_union, mem_sdiff] at hX,
          exact exists.elim (b.basis_exch hb1.1 hB2filt.1 $ mem_sdiff.mpr ⟨hX.1, hX.2.2⟩)
            (by { intros Y hY, rw mem_sdiff at hY,
            have hYyx : Y ∈ y ∧ Y ∉ x := mem_sdiff.mp (hB2b1y ▸ (mem_sdiff.mpr hY.1)),
            have hxYsub : insert Y x ⊆ insert Y (erase b1 X) := by {
              simp only [subset_iff, mem_insert, mem_erase, ne.def],
              exact λ gg hgg, or.elim hgg (λ ggY, or.inl ggY) $ λ ggx, or.inr ⟨λ ggX, hX.2.1 $
                ggX ▸ ggx, mem_of_subset hb1.2 ggx⟩ },
            have : insert Y x ⊆ E := insert_subset.mpr ⟨mem_of_subset hy.1 hYyx.1, hx.1⟩,
            exact h Y hYyx.1 hYyx.2 this (insert Y $ erase b1 X) hY.2 hxYsub }) }) },
      clear h hx hy,
      rw [←subset_iff_sdiff_eq_empty, subset_iff] at hb1xuB2, simp only [mem_union] at hb1xuB2,
      have hb1B2 : b1 \ B2 = x \ B2 := by { simp only [ext, mem_sdiff],
        exact λ gg, ⟨λ hgg, ⟨or.elim (hb1xuB2 hgg.1) id $ λ ggB2, false.elim $ hgg.2 ggB2, hgg.2⟩,
            λ hgg, ⟨mem_of_subset hb1.2 hgg.1, hgg.2⟩⟩ }, clear hb1xuB2,
      replace hb1B2 : b1 \ B2 ⊆ x \ y := hb1B2.symm ▸ (sdiff_subset_sdiff (subset.refl x)
          hB2filt.2),
      have hcardeq : card b1 = card B2 := bases_card_eq hb1.1 hB2filt.1,
      have hcardb1B2 : card (b1 \ B2) = card (B2 \ b1) := calc
        card (b1 \ B2) = card b1 - card (b1 ∩ B2) : card_sdiff_eq b1 B2
        ... = card B2 - card (B2 ∩ b1) : by rw [hcardeq, inter_comm]
        ... = card (B2 \ b1) : by rw ←card_sdiff_eq B2 b1,
      have hcardcontra0 : card (y \ x) ≤ card (x \ y) := calc
        card (y \ x) = card (B2 \ b1) : by rw hB2b1y
        ... = card (b1 \ B2) : by rw hcardb1B2
        ... ≤ card (x \ y) : card_le_of_subset hb1B2,
      rw [card_sdiff_eq y x, card_sdiff_eq x y, inter_comm] at hcardcontra0,
      have hcardcontra : card y ≤ card x := nat.le_of_le_of_sub_le_sub_right
          (card_le_of_subset $ @inter_subset_left _ _ x y) hcardcontra0,
      exact not_lt_of_le hcardcontra hcard })
end⟩

instance base_indep : has_coe (bases E) (indep E) := ⟨indep_of_bases⟩
instance indep_base : has_coe (indep E) (bases E) := ⟨bases_of_indep⟩

/-- second part of Theorem 1.2.3 -/
theorem base_indep_base (B : bases E) : B = bases_of_indep (indep_of_bases B) :=
suffices B.bases = (bases_of_indep $ indep_of_bases B).bases, from eq_of_base_eq this,
by { simp only [indep_of_bases, bases_of_indep, indep_indep_of_bases, is_basis,
  ext, bases_bases_of_indep, mem_filter, mem_powerset, not_and, not_exists, exists_prop],
exact λ b, iff.intro
  (λ hb, have hB : b ⊆ E := mem_powerset.mp (mem_of_subset B.bases_subset_powerset_ground hb),
    ⟨hB, ⟨⟨hB, exists.intro b ⟨hb, subset.refl b⟩⟩, λ b' _ hbb' _ _ hx H,
    (ne_of_lt $ lt_of_lt_of_le (card_lt_card hbb') $ card_le_of_subset H) $ bases_card_eq hb hx⟩⟩) $
  λ hb, exists.elim hb.2.1.2 $ λ a ha, have a ⊆ E := mem_powerset.mp $
    B.bases_subset_powerset_ground ha.1, by { by_cases h : a = b,
      { exact h ▸ ha.1 },
      { have hba : b ⊂ a := lt_iff_ssubset.mp (lt_of_le_of_ne (le_iff_subset.mpr ha.2) $ ne.symm h),
        exact false.elim (hb.2.2 a this hba this a ha.1 $ subset.refl a) } } }

theorem indep_base_indep (M : indep E) : M = indep_of_bases (bases_of_indep M) :=
suffices M.indep = (indep_of_bases $ bases_of_indep M).indep, from eq_of_indep_eq this,
by { simp only [indep_of_bases, bases_of_indep, indep_indep_of_bases, is_basis,
  ext, bases_bases_of_indep, mem_filter, mem_powerset, exists_prop],
  exact λ I, iff.intro (λ hI, ⟨mem_powerset.mp $ mem_of_subset M.indep_subset_powerset_ground hI,
  exists.elim (exists_basis_containing_indep hI) $ λ B hB, by { unfold is_basis at hB,
    exact exists.intro B ⟨⟨mem_powerset.1 $ mem_of_subset M.indep_subset_powerset_ground hB.2.1,
      hB.2⟩, hB.1⟩ }⟩) $ λ hI, exists.elim hI.2 $ λ B hB, M.indep_of_subset_indep hB.1.2.1 hB.2 }

/-- Corollary 1.2.6 -/
theorem existsu_fund_circ_of_basis {m : indep E} {B : finset α} (hB : is_basis B m) {e : α}
  (he : e ∈ E \ B) : ∃ C, C ∈ circuits_circ_of_indep m ∧ C ⊆ insert e B ∧
  ∀ C' ∈ circuits_circ_of_indep m, C' ⊆ insert e B → C' = C :=
begin
  unfold is_basis at hB, rw mem_sdiff at he,
  have : insert e B ∉ m.indep := hB.2 (insert e B) (insert_subset.mpr ⟨he.1,
    mem_powerset.mp $ mem_of_subset m.indep_subset_powerset_ground hB.1⟩) (ssubset_insert he.2),
  replace := existsu_circuit_of_dep_of_insert_indep hB.1 he.1 this,
  exact exists.elim this (λ C ⟨hCcirc, HC⟩, exists.intro C $
    ⟨hCcirc, ⟨HC.1, λ C' hC'circ hC', HC.2.2 C' hC'circ ⟨hC', HC.2.1⟩⟩⟩)
end

section encodable

def fund_circ_of_basis [encodable α] {m : indep E} {B : finset α} (hB : is_basis B m) {e : α}
  (he : e ∈ E \ B) : finset α :=
encodable.choose (existsu_fund_circ_of_basis hB he)

def fund_circ_of_basis_spec [encodable α] {m : indep E} {B : finset α} (hB : is_basis B m) {e : α}
  (he : e ∈ E \ B) : fund_circ_of_basis hB he ∈ circuits_circ_of_indep m ∧
  fund_circ_of_basis hB he  ⊆ insert e B ∧ ∀ C' ∈ circuits_circ_of_indep m, C' ⊆ insert e B →
  C' = fund_circ_of_basis hB he :=
encodable.choose_spec (existsu_fund_circ_of_basis hB he)

end encodable

-- § 1.3

def indep_of_restriction (m : indep E) {X : finset α} (hXE : X ⊆ E) : finset (finset α) :=
(m.indep).filter (λ I, I ⊆ X)

def restriction (m : indep E) {X : finset α} (hXE : X ⊆ E) : indep X :=
⟨indep_of_restriction m hXE,
by simp only [indep_of_restriction, subset_iff, and_imp, imp_self,
  mem_powerset, mem_filter, forall_true_iff],
by simp only [indep_of_restriction, m.empty_mem_indep, empty_subset, and_self, mem_filter],
by { unfold indep_of_restriction, exact λ x y hx hy, mem_filter.mpr
  ⟨m.indep_of_subset_indep (mem_filter.mp hx).1 hy, subset.trans hy (mem_filter.mp hx).2⟩ },
by { unfold indep_of_restriction, exact λ x y hx hy hcard,
  have hxm : x ∈ m.indep := (mem_filter.mp hx).1, have hym : y ∈ m.indep := (mem_filter.mp hy).1,
  have hxX : x ⊆ X := (mem_filter.mp hx).2, have hyX : y ⊆ X := (mem_filter.mp hy).2,
  have H : _ := m.indep_exch hxm hym hcard,
  let ⟨e, H, h₁⟩ := H in
    ⟨e, H, mem_filter.mpr ⟨h₁, insert_subset.mpr ⟨mem_of_subset hyX (mem_sdiff.mp H).1, hxX⟩⟩⟩ }⟩

def deletion (m : indep E) {X : finset α} (hXE : X ⊆ E) : indep (E \ X) :=
restriction m $ sdiff_subset E X

notation m `¦` hxe := restriction m hxe
notation m `\` hxe := deletion m hxe

lemma restriction_subset_restriction {X : finset α} (hX : X ⊆ E) (m : indep E) :
  (m ¦ hX).indep ⊆ m.indep :=
by { simp only [restriction, indep_of_restriction, subset_iff, and_imp,
  filter_congr_decidable, mem_filter],
  exact λ _ hX'I _, hX'I }

lemma restriction_trans {X Y : finset α} (hXY : X ⊆ Y) (hY : Y ⊆ E) (m : indep E) :
  (m ¦ subset.trans hXY hY) = ((m ¦ hY) ¦ hXY) :=
by { simp only [restriction, indep_of_restriction, ext, mem_filter],
  exact λ I, iff.intro (λ h, ⟨⟨h.1, subset.trans h.2 hXY⟩, h.2⟩) $ λ h, ⟨h.1.1, h.2⟩ }

lemma subset_restriction_indep {X Y : finset α} {m : indep E} (hX : X ∈ m.indep) (hXY : X ⊆ Y)
  (hY : Y ⊆ E) : X ∈ (m ¦ hY).indep :=
by { simp only [restriction, indep_of_restriction, mem_filter], exact ⟨hX, hXY⟩ }

/-def spans (X : finset α) {Y : finset α} (hY : Y ⊆ E) (m : indep E) : Prop :=
X ∈ bases_bases_of_indep (m ¦ hY)-/

lemma exists_basis_of_subset {X : finset α} (hXE : X ⊆ E) (m : indep E) :
  ∃ B, B ∈ bases_bases_of_indep (m ¦ hXE) :=
exists_mem_of_ne_empty $ B1_of_indep (m ¦ hXE)

/-lemma inter_of_span_of_subset_span {m : indep E} {X Y bX bY : finset α} {hXE : X ⊆ E}
  (hbX : spans bX hXE m) {hYE : Y ⊆ E} (hbY : spans bY hYE m) (hbXbY : bX ⊆ bY) : bY ∩ X = bX :=
sorry-/

section encodable
variable [encodable α]

def basis_of_subset {X : finset α} (hXE : X ⊆ E) (m : indep E) : finset α :=
encodable.choose $ exists_basis_of_subset hXE m

def basis_of_subset_spec {X : finset α} (hXE : X ⊆ E) (m : indep E) :
  basis_of_subset hXE m ∈ bases_bases_of_indep (m ¦ hXE) :=
encodable.choose_spec $ exists_basis_of_subset hXE m

notation `𝔹` := basis_of_subset
notation `𝔹ₛ` := basis_of_subset_spec

def rank_of_subset {X : finset α} (hXE : X ⊆ E) (m : indep E) : ℕ :=
card $ 𝔹 hXE m

notation `𝓇` := rank_of_subset

lemma R2_of_indep (m : indep E) {X Y : finset α} (hXY : X ⊆ Y) (hYE : Y ⊆ E) :
  𝓇 (subset.trans hXY hYE) m ≤ 𝓇 hYE m :=
let hXE : X ⊆ E := subset.trans hXY hYE in let bX := 𝔹 hXE m in let bY := 𝔹 hYE m in
have bXs : _ := 𝔹ₛ hXE m, have bYs : _ := 𝔹ₛ hYE m,
by { simp only [bases_bases_of_indep, mem_powerset, filter_congr_decidable, mem_filter] at bXs bYs,
  unfold rank_of_subset,
  have hBX : bX ∈ (m ¦ hYE).indep := mem_of_subset (restriction_subset_restriction hXY (m ¦ hYE))
    ((restriction_trans hXY hYE m) ▸ bXs.2.1),
  exact exists.elim (exists_basis_containing_indep hBX) (λ B hB, calc
    card bX ≤ card B : card_le_of_subset hB.1
    ... = card bY : bases_of_indep_card_eq hB.2 bYs.2) }

/-- Lemma 1.3.1 -/
lemma R3_of_indep (m : indep E) {X Y : finset α} (hX : X ⊆ E) (hY : Y ⊆ E) :
  𝓇 (union_subset hX hY) m +
  𝓇 (subset.trans (@inter_subset_left _ _ X Y) hX) m ≤
  𝓇 hX m + 𝓇 hY m :=
begin
  have hXXuY : X ⊆ X ∪ Y := @subset_union_left _ _ X Y,
  have hYXuY : Y ⊆ X ∪ Y := @subset_union_right _ _ X Y,
  have hXiYX : X ∩ Y ⊆ X := @inter_subset_left _ _ X Y,
  have hXuY : X ∪ Y ⊆ E := union_subset hX hY,
  have hXiY : X ∩ Y ⊆ E := subset.trans hXiYX hX,
  let bXuY := 𝔹 hXuY m, let bXiY := 𝔹 hXiY m,
  let bX := 𝔹 hX m, let bY := 𝔹 hY m,
  unfold rank_of_subset,
  have bXuYs := 𝔹ₛ hXuY m, have bXiYs := 𝔹ₛ hXiY m,
  have bXs := 𝔹ₛ hX m, have bYs := 𝔹ₛ hY m,
  simp only [bases_bases_of_indep, mem_powerset, filter_congr_decidable, mem_filter]
    at bXuYs bXiYs bXs bYs,
  have rXiY : 𝓇 hXiY m = card bXiY := by simp only [rank_of_subset],
  have hiu : X ∩ Y ⊆ X ∪ Y := subset.trans hXiYX hXXuY,
  have hbXiY : bXiY ∈ (m ¦ hXuY).indep := mem_of_subset
    (restriction_subset_restriction hiu (m ¦ hXuY)) ((restriction_trans hiu hXuY m) ▸ bXiYs.2.1),
  have HbbXiY := exists_basis_containing_indep hbXiY,
  exact exists.elim HbbXiY (by { intros B hB,
    have rXuY : 𝓇 hXuY m = card B := by { simp only [rank_of_subset],
      exact bases_of_indep_card_eq bXuYs.2 hB.2 },
    have hBXuY : B ⊆ X ∪ Y := mem_powerset.mp ((m ¦ hXuY).indep_subset_powerset_ground hB.2.1),
    have hBX : B ∩ X ∈ (m ¦ hX).indep := have hsub : _ := restriction_trans hXXuY hXuY m,
      have hBX : _ := ((m ¦ hXuY).indep_of_subset_indep hB.2.1 $ @inter_subset_left _ _ B X),
      hsub.symm ▸ (subset_restriction_indep hBX (@inter_subset_right _ _ B X) hXXuY),
    have hBY : B ∩ Y ∈ (m ¦ hY).indep := have hsub : _ := restriction_trans hYXuY hXuY m,
      have hBY : _ := ((m ¦ hXuY).indep_of_subset_indep hB.2.1 $ @inter_subset_left _ _ B Y),
      hsub.symm ▸ (subset_restriction_indep hBY (@inter_subset_right _ _ B Y) hYXuY),
    have hBXr : card (B ∩ X) ≤ 𝓇 hX m := by { unfold rank_of_subset,
      exact card_of_indep_le_card_basis hBX bXs.2 },
    have hBYr : card (B ∩ Y) ≤ 𝓇 hY m := by { unfold rank_of_subset,
      exact card_of_indep_le_card_basis hBY bYs.2 },
    have hinter : (B ∩ X) ∩ (B ∩ Y) = B ∩ X ∩ Y := by simp only [finset.inter_assoc,
      inter_right_comm, inter_self, inter_comm, inter_left_comm],
    have hBXiY : B ∩ X ∩ Y = bXiY :=
      by { have hsub : B ∩ X ∩ Y ⊆ bXiY :=
        by { by_contra h,
        exact exists.elim (exists_mem_of_ne_empty $ (mt subset_iff_sdiff_eq_empty.mpr) h)
          (by { intros a ha, rw [mem_sdiff, inter_assoc, mem_inter] at ha, unfold is_basis at bXiYs,
          have := ssubset_insert ha.2,
          have hbXiYsubXiY : insert a bXiY ⊆ X ∩ Y:= insert_subset.mpr ⟨ha.1.2, bXiYs.1⟩,
          have hrestrict : (m ¦ hXiY) = (m ¦ hXuY ¦ hiu) := restriction_trans hiu hXuY m,
          have hindep : insert a bXiY ∈ (m ¦ hXiY).indep := hrestrict.symm ▸
            (subset_restriction_indep ((m ¦ hXuY).indep_of_subset_indep hB.2.1
            $ insert_subset.mpr ⟨ha.1.1, hB.1⟩) hbXiYsubXiY hiu),
          exact bXiYs.2.2 (insert a bXiY) hbXiYsubXiY this hindep }) },
      have hsuper : bXiY ⊆ B ∩ X ∩ Y :=
        by { rw [inter_assoc],
        have := inter_subset_inter_right hB.1,
        have h : bXiY ∩ (X ∩ Y) = bXiY := inter_of_subset bXiYs.1,
        exact h ▸ this },
      exact subset.antisymm hsub hsuper },
    exact calc 𝓇 hX m + 𝓇 hY m ≥ card (B ∩ X) + card (B ∩ Y) : add_le_add hBXr hBYr
    ... = card ((B ∩ X) ∪ (B ∩ Y)) + card ((B ∩ X) ∩ (B ∩ Y)) : card_union_inter (B ∩ X) (B ∩ Y)
    ... = card (B ∩ (X ∪ Y)) + card (B ∩ X ∩ Y) : by rw [←inter_distrib_left, hinter]
    ... = card B + card bXiY : by rw [inter_of_subset hBXuY, hBXiY]
    ... = 𝓇 hXuY m + 𝓇 hXiY m : by rw [rXuY, rXiY] })
end

end encodable

structure rank (ground : finset α) :=
(r {X : finset α} (hX : X ⊆ ground) : ℕ)
-- (R1)
(bounded {X : finset α} (hX : X ⊆ ground) : 0 ≤ r hX ∧ r hX ≤ card X)
-- (R2)
(order_preserving {X Y : finset α} (hXY : X ⊆ Y) (hY : Y ⊆ ground) : r (subset.trans hXY hY) ≤ r hY)
-- (R3)
(submodular {X Y : finset α} (hX : X ⊆ ground) (hY : Y ⊆ ground) :
r (union_subset hX hY) + r (subset.trans (@inter_subset_left _ _ X Y) hX) ≤ r hX + r hY)

section encodable
variable [encodable α]

def rank_of_indep (m : indep E) : rank E :=
⟨λ X hX, rank_of_subset hX m,
λ X hX, ⟨dec_trivial, (by { have := basis_of_subset_spec hX m,
  simp only [bases_bases_of_indep, mem_powerset, filter_congr_decidable, mem_filter] at this,
  exact card_le_of_subset this.1 })⟩,
λ X Y hXY hY, R2_of_indep m hXY hY,
λ X Y hX hY, R3_of_indep m hX hY⟩

end encodable

structure rank_R2_R3 (ground : finset α) :=
(r {X : finset α} (hX : X ⊆ ground) : ℕ)
-- (R2)
(order_preserving {X Y : finset α} (hXY : X ⊆ Y) (hY : Y ⊆ ground) : r (subset.trans hXY hY) ≤ r hY)
-- (R3)
(submodular {X Y : finset α} (hX : X ⊆ ground) (hY : Y ⊆ ground) :
r (union_subset hX hY) + r (subset.trans (@inter_subset_left _ _ X Y) hX) ≤ r hX + r hY)

lemma congr_for_rank (rk : rank_R2_R3 E ) {X Y : finset α} (hX : X ⊆ E) (hY : Y ⊆ E) (h : X = Y) :
rk.r hX = rk.r hY :=
by { congr, exact h }

-- Lemma 1.3.3
lemma rank_union_lemma (rk : rank_R2_R3 E) {X Y : finset α} (hX : X ⊆ E) (hY : Y ⊆ E)
  (hy : ∀ y, ∀ (h : y ∈ Y \ X), rk.r (by { rw mem_sdiff at h,
    exact insert_subset.mpr ⟨mem_of_subset hY h.1, hX⟩ }) = rk.r hX) :
  rk.r (union_subset hX hY) = rk.r hX :=
begin
  have hXuY : X ∪ Y ⊆ E := union_subset hX hY,
  induction h : (Y \ X) using finset.induction with a S ha ih generalizing X Y,
  { congr, have H := congr_arg (λ x, X ∪ x) h,
    simp only [union_sdiff_self_eq_union, union_empty] at H, exact H },
  { have h₁ : rk.r hX + rk.r hX ≥ rk.r hXuY + rk.r hX :=
    by { have haa : a ∈ Y \ X := h.substr (mem_insert_self a S),
    have haX : insert a X ⊆ E := insert_subset.mpr ⟨mem_of_subset hY (mem_sdiff.mp haa).1, hX⟩,
    have hins : insert a S ⊆ E := h ▸ subset.trans (sdiff_subset Y X) hY,
    have hS : S ⊆ E := subset.trans (subset_insert a S) hins,
    have hXS : X ∪ S ⊆ E := union_subset hX hS,
    have hrins : rk.r haX = rk.r hX := hy a haa, rw mem_sdiff at haa,
    have hrS : rk.r hXS = rk.r hX := by {
      exact ih hX hS (by { intros y Hy, have : y ∈ Y \ X := by { rw mem_sdiff at Hy,
        simp only [ext, mem_insert, mem_sdiff] at h,
        exact mem_sdiff.mpr ((h y).mpr $ or.inr Hy.1) }, exact hy y this })
        hXS (by { simp only [ext, mem_insert, mem_sdiff] at h ⊢,
          exact λ y, iff.intro (λ Hy, Hy.1) $ λ Hy, ⟨Hy, ((h y).mpr $ or.inr Hy).2⟩ }) },
    have hXuSiaX : (X ∪ S) ∩ insert a X ⊆ E := (subset.trans (@inter_subset_right _ _ (X ∪ S)
      (insert a X)) haX),
    have hr₁ : rk.r (union_subset hXS haX) = rk.r hXuY :=
      by { exact congr_for_rank rk (union_subset hXS haX) hXuY (by {
        simp only [ext, mem_union, union_comm, mem_insert, mem_sdiff, union_insert,
          union_self, union_assoc] at h ⊢,
      exact λ x, iff.intro (λ hx, or.elim hx (λ hxa, or.inr $ hxa.substr haa.1) $
        λ H, or.elim H (by { intro hxS, exact or.inr ((h x).mpr $ or.inr hxS).1}) $
          by {exact (λ hxX, or.inl hxX) }) $
        λ hx, or.elim hx (by {intro hxX, exact or.inr (or.inr hxX)}) $
          by { intro hxY, by_cases hxX : x ∈ X,
            { exact or.inr (or.inr hxX) },
            { exact or.elim ((h x).mp ⟨hxY, hxX⟩) (λ H, or.inl H)
              (λ HS, or.inr $ or.inl HS) } } }) },
    have hr₂ : rk.r hXuSiaX = rk.r hX := by { congr,
      simp only [ext, mem_union, union_comm, mem_insert, mem_inter],
      exact λ x, iff.intro (λ hx, or.elim hx.1 (or.elim hx.2
        (λ H₁ H₂, false.elim $ ha $ H₁.subst H₂) $ λ h _, h) id) (λ hx, ⟨or.inr hx, or.inr hx⟩) },
    calc rk.r hX + rk.r hX = rk.r hXS + rk.r haX : by rw [hrS, hrins]
    ... ≥ rk.r (union_subset hXS haX) + rk.r hXuSiaX : rk.submodular (union_subset hX hS) haX
    ... = _ : by rw [hr₁, hr₂] },
  replace h₁ := le_of_add_le_add_right h₁,
  have h₂ : rk.r hX ≤ rk.r hXuY := rk.order_preserving (@subset_union_left _ _ X Y) hXuY,
  exact nat.le_antisymm h₁ h₂ }
end

def indep_of_rank (r : rank E) : indep E :=
⟨sorry,
sorry,
sorry,
sorry,
sorry⟩
end matroid

-/ 
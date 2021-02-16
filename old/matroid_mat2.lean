/-

Some goals:
  - Define matroid.
  - Define duality.
  - Define minors, deletion, contraction.
  - Prove that disjoint deletions and contractions commute.
  - Prove that dual of a minor is a minor of the dual.

Some things that are needed:
  - Finite sets, size.
  - Union, intersection, complement of finite subsets.

Paying special attention to:
  - When are things (propositionally) equal.

-/

import tactic.ext
import tactic.linarith

-- The API I would like to use for various basic objects.
section API

structure fin_bool_alg :=
  (subset : Type)
  (contained : subset → subset → Prop)
  (bot top : subset)
  (inter union : subset → subset → subset)
  (compl : subset → subset)
  (size : subset → ℤ)

  -- The structure axioms have a trailing underscore because they can't (yet) be written using the nice notation defined below.
  (refl_ (X : subset) : contained X X)
  (antisymm_ (X Y : subset) : (contained X Y) → (contained Y X) → X = Y)
  (trans_ (X Y Z : subset) : (contained X Y) → (contained Y Z) → (contained X Z))

  (bot_subset_ (X : subset) : contained bot X)
  (subset_top_ (X : subset) : contained X top)

  (inter_subset_left_ (X Y : subset) : contained (inter X Y) X)
  (inter_subset_right_ (X Y : subset) : contained (inter X Y) Y)
  (inter_maximal_ (X Y Z : subset) : (contained Z X) → (contained Z Y) → contained Z (inter X Y))

  (left_subset_union_ (X Y : subset) : contained X (union X Y))
  (right_subset_union_ (X Y : subset) : contained Y (union X Y))
  (union_minimal_ (X Y Z : subset) : (contained X Z) → (contained Y Z) → contained (union X Y) Z)

  (inter_distrib_union_ (X Y Z : subset) : (inter X (union Y Z)) = union (inter X Y) (inter X Z))
--  (union_distrib_inter_ (X Y Z : subset) : (union X (inter Y Z)) = inter (union X Y) (union X Z))

  (self_inter_compl_ (X : subset) : (inter X (compl X) = bot))
  (self_union_compl_ (X : subset) : (union X (compl X) = top))

  (size_bot_ : size bot = 0)
  (size_monotone_ (X Y : subset) : (contained X Y) → size X ≤ size Y)
  (size_antisymm_ (X Y : subset) : (contained X Y) → size X = size Y → X = Y)
  (size_atom_ (X : subset) : (forall (Y Z : subset), (contained X (union Y Z)) → (contained X Y) ∨ (contained X Z)) → size X = 1)
  (size_modular_ (X Y: subset) : size (union X Y) + size (inter X Y) = size X + size Y)

/-
Various instances to allow nice notations:
(X : A), ⊥, ⊤, (X ∩ Y), (X ∪ Y), Xᶜ, (X ⊆ Y)
-/
instance i1 : has_coe_to_sort fin_bool_alg := {S := Type, coe := fin_bool_alg.subset}
instance i2 {A : fin_bool_alg} : has_bot A := {bot := A.bot}
instance i3 {A : fin_bool_alg} : has_top A := {top := A.top}
instance i4 {A : fin_bool_alg} : has_inter A := {inter := A.inter}
instance i5 {A : fin_bool_alg} : has_union A := {union := A.union}
instance i6 {A : fin_bool_alg} : has_compl A := {compl := A.compl}
instance i7 {A : fin_bool_alg} : has_subset A := {subset := A.contained} 

abbreviation size {A : fin_bool_alg} (X : A) : ℤ := A.size X

def atom {A : fin_bool_alg} (X : A) : Prop :=
  ∀ (Y Z : A), (X ⊆ Y ∪ Z) → (X ⊆ Y) ∨ (X ⊆ Z)

/-
The axiom versions below, without a trailing underscore, are written using the notation instances above,
so that they can be used directly by the tactics rw and linarith.
-/
namespace fin_bool_alg
variables (A : fin_bool_alg) {X Y Z : A}
-- Note: inside the namespace, the structure field 'size' shadows the abbreviation 'size', so we have to write 'A.size'.

lemma refl : X ⊆ X := A.refl_ X
lemma antisymm : (X ⊆ Y) → (Y ⊆ X) → (X = Y) := A.antisymm_ X Y
lemma trans : (X ⊆ Y) → (Y ⊆ Z) → (X ⊆ Z) := A.trans_ X Y Z
lemma bot_subset : ⊥ ⊆ X := A.bot_subset_ X
lemma subset_top : X ⊆ ⊤ := A.subset_top_ X
lemma inter_subset_left : (X ∩ Y) ⊆ X := A.inter_subset_left_ X Y
lemma inter_subset_right : (X ∩ Y) ⊆ Y := A.inter_subset_right_ X Y
lemma inter_maximal : (Z ⊆ X) → (Z ⊆ Y) → (Z ⊆ X ∩ Y) := A.inter_maximal_ X Y Z
lemma left_subset_union : X ⊆ (X ∪ Y) := A.left_subset_union_ X Y
lemma right_subset_union : Y ⊆ (X ∪ Y) := A.right_subset_union_ X Y
lemma union_minimal : (X ⊆ Z) → (Y ⊆ Z) → ((X ∪ Y) ⊆ Z) := A.union_minimal_ X Y Z
lemma self_inter_compl_self : (X ∩ Xᶜ) = ⊥ := A.self_inter_compl_ X
lemma self_union_compl_self : (X ∪ Xᶜ) = ⊤ := A.self_union_compl_ X
lemma size_bot : A.size ⊥ = 0 := A.size_bot_
lemma size_monotone : (X ⊆ Y) → A.size X ≤ A.size Y := A.size_monotone_ X Y
lemma size_antisymm : (X ⊆ Y) → A.size X = A.size Y → X = Y := A.size_antisymm_ X Y
lemma size_atom : (atom X) → (A.size X = 1) := A.size_atom_ X
lemma size_modular : A.size (X ∪ Y) + A.size (X ∩ Y) = A.size X + A.size Y := A.size_modular_ X Y

/-
Because union and intersection are defined in terms of their universal property,
we can deduce associativity, commutativity, etc.
-/

lemma inter_comm : (X ∩ Y) = (Y ∩ X) :=
  by apply A.antisymm; { apply A.inter_maximal, apply A.inter_subset_right, apply A.inter_subset_left }

lemma inter_assoc : (X ∩ Y) ∩ Z = X ∩ (Y ∩ Z) := begin
  apply A.antisymm, repeat {apply A.inter_maximal},
  {apply A.trans, apply A.inter_subset_left, apply A.inter_subset_left},
  {apply A.trans, apply A.inter_subset_left, apply A.inter_subset_right},
  {apply A.inter_subset_right},
  {apply A.inter_subset_left},
  {apply A.trans, apply A.inter_subset_right, apply A.inter_subset_left},
  {apply A.trans, apply A.inter_subset_right, apply A.inter_subset_right},
end

lemma inter_left_comm : X ∩ (Y ∩ Z) = Y ∩ (X ∩ Z) := calc
  X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z : A.inter_assoc.symm
  ...         = (Y ∩ X) ∩ Z : by rw (@inter_comm A X Y)
  ...         = Y ∩ (X ∩ Z) : A.inter_assoc

lemma inter_bot : (X ∩ ⊥) = ⊥ := A.antisymm A.inter_subset_right A.bot_subset
lemma bot_inter : (⊥ ∩ X) = ⊥ := A.antisymm A.inter_subset_left A.bot_subset
lemma inter_top : (X ∩ ⊤) = X := A.antisymm A.inter_subset_left (A.inter_maximal A.refl A.subset_top)
lemma top_inter : (⊤ ∩ X) = X := A.antisymm A.inter_subset_right (A.inter_maximal A.subset_top A.refl)
lemma inter_self : (X ∩ X) = X := A.antisymm A.inter_subset_left (A.inter_maximal A.refl A.refl)

lemma inter_eq_left : (X ⊆ Y) → (X ∩ Y = X) := fun h, A.antisymm A.inter_subset_left (A.inter_maximal A.refl h)
lemma inter_eq_right : (X ⊆ Y) → (Y ∩ X = X) := fun h, A.antisymm A.inter_subset_right (A.inter_maximal h A.refl)

lemma union_comm : (X ∪ Y) = (Y ∪ X) :=
  by apply A.antisymm; { apply A.union_minimal, apply A.right_subset_union, apply A.left_subset_union }

lemma union_assoc : (X ∪ Y) ∪ Z = X ∪ (Y ∪ Z) := begin
  apply A.antisymm, repeat {apply A.union_minimal},
  {apply A.left_subset_union},
  {apply A.trans, apply A.left_subset_union, swap, apply A.right_subset_union},
  {apply A.trans, apply A.right_subset_union, swap, apply A.right_subset_union},
  {apply A.trans, apply A.left_subset_union, swap, apply A.left_subset_union},
  {apply A.trans, apply A.right_subset_union, swap, apply A.left_subset_union},
  {apply A.right_subset_union},
end

lemma union_left_comm : X ∪ (Y ∪ Z) = Y ∪ (X ∪ Z) := calc
  X ∪ (Y ∪ Z) = (X ∪ Y) ∪ Z : A.union_assoc.symm
  ...         = (Y ∪ X) ∪ Z : by rw (@union_comm A X Y)
  ...         = Y ∪ (X ∪ Z) : A.union_assoc

lemma union_bot : (X ∪ ⊥) = X := A.antisymm (A.union_minimal A.refl A.bot_subset) A.left_subset_union
lemma bot_union : (⊥ ∪ X) = X := A.antisymm (A.union_minimal A.bot_subset A.refl) A.right_subset_union
lemma union_top : (X ∪ ⊤) = ⊤ := A.antisymm A.subset_top A.right_subset_union
lemma top_union : (⊤ ∪ X) = ⊤ := A.antisymm A.subset_top A.left_subset_union
lemma union_self : (X ∪ X) = X := A.antisymm (A.union_minimal A.refl A.refl) A.left_subset_union

lemma union_eq_left : (X ⊆ Y) → (Y ∪ X = Y) := fun h, A.antisymm (A.union_minimal A.refl h) A.left_subset_union
lemma union_eq_right : (X ⊆ Y) → (X ∪ Y = Y) := fun h, A.antisymm (A.union_minimal h A.refl) A.right_subset_union

lemma inter_distrib_union_left : X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) := A.inter_distrib_union_ X Y Z
lemma inter_distrib_union_right : (X ∪ Y) ∩ Z = (X ∩ Z) ∪ (Y ∩ Z) := calc
  (X ∪ Y) ∩ Z = Z ∩ (X ∪ Y)       : A.inter_comm
  ...         = (Z ∩ X) ∪ (Z ∩ Y) : A.inter_distrib_union_left
  ...         = (X ∩ Z) ∪ (Y ∩ Z) : by rw [@inter_comm A X Z, @inter_comm A Y Z]
lemma union_distrib_inter_left : X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z) := A.antisymm
  (A.inter_maximal
    (A.union_minimal
      A.left_subset_union
      (A.trans A.inter_subset_left A.right_subset_union))
    (A.union_minimal
      A.left_subset_union
      (A.trans A.inter_subset_right A.right_subset_union)))
  (calc
    (X ∪ Y) ∩ (X ∪ Z) = ((X ∪ Y) ∩ X) ∪ ((X ∪ Y) ∩ Z)             : A.inter_distrib_union_left
    ...               = ((X ∩ X) ∪ (Y ∩ X)) ∪ ((X ∩ Z) ∪ (Y ∩ Z)) : by rw [@inter_distrib_union_right A X Y X, @inter_distrib_union_right A X Y Z]
    ...               ⊆ X ∪ (Y ∩ Z)                               : begin
      repeat {apply A.union_minimal},
      show (X ∩ X) ⊆ X ∪ (Y ∩ Z), {exact A.trans A.inter_subset_left A.left_subset_union},
      show (Y ∩ X) ⊆ X ∪ (Y ∩ Z), {exact A.trans A.inter_subset_right A.left_subset_union},
      show (X ∩ Z) ⊆ X ∪ (Y ∩ Z), {exact A.trans A.inter_subset_left A.left_subset_union},
      show (Y ∩ Z) ⊆ X ∪ (Y ∩ Z), {exact A.right_subset_union},
    end)
lemma union_distrib_inter_right : (X ∩ Y) ∪ Z = (X ∪ Z) ∩ (Y ∪ Z) := calc
  (X ∩ Y) ∪ Z = Z ∪ (X ∩ Y)       : A.union_comm
  ...         = (Z ∪ X) ∩ (Z ∪ Y) : A.union_distrib_inter_left
  ...         = (X ∪ Z) ∩ (Y ∪ Z) : by rw [@union_comm A X Z, @union_comm A Y Z]

-- TODO: complement
lemma compl_contained : (X ⊆ Y) → (Yᶜ ⊆ Xᶜ) := sorry
lemma compl_bot : (⊥ : A)ᶜ = ⊤ := sorry
lemma compl_top : (⊤ : A)ᶜ = ⊥ := sorry
lemma compl_inter : (X ∩ Y)ᶜ = (Xᶜ ∪ Yᶜ) := sorry
lemma compl_union : (X ∪ Y)ᶜ = (Xᶜ ∩ Yᶜ) := sorry
lemma compl_compl : Xᶜᶜ = X := sorry

end /- namespace -/ fin_bool_alg

lemma fin_bool_alg.size_diff (A : fin_bool_alg) {X Y : A} :
  (X ⊆ Y) → size (Xᶜ ∩ Y) = size Y - size X := sorry

-- Notionally, the boolean algebra of subsets of {1, 2, ..., n}.
def fin_bool_alg.canonical (size : ℤ) :
  (0 ≤ size) → fin_bool_alg := sorry

/-
The opposite poset of a fin_bool_alg is also a fin_bool_alg,
almost trivially, with various operations and arguments swapped around
(bot ↔ top, intersection ↔ union).
-/
def fin_bool_alg.opposite (A : fin_bool_alg) : fin_bool_alg := {
  subset := A.subset,
  contained := (fun X Y, A.contained Y X), -- swapped arguments
  bot := A.top,
  top := A.bot,
  inter := A.union,
  union := A.inter,
  compl := A.compl,
  size := (fun X, A.size A.top - A.size X),

  refl_ := A.refl_,
  antisymm_ := (fun X Y h₁ h₂, A.antisymm_ X Y h₂ h₁),
  trans_ := (fun X Y Z h₁ h₂, A.trans_ Z Y X h₂ h₁),
  bot_subset_ := A.subset_top_,
  subset_top_ := A.bot_subset_,
  inter_subset_left_ := A.left_subset_union_,
  inter_subset_right_ := A.right_subset_union_,
  inter_maximal_ := A.union_minimal_,
  left_subset_union_ := A.inter_subset_left_,
  right_subset_union_ := A.inter_subset_right_,
  union_minimal_ := A.inter_maximal_,
  inter_distrib_union_ := (fun X Y Z, A.union_distrib_inter_left), -- not completely trivial
  self_inter_compl_ := A.self_union_compl_,
  self_union_compl_ := A.self_inter_compl_,
  size_nonneg_ := (fun X, by linarith [A.size_monotone_ _ _ (A.subset_top_ X)]),
  size_monotone_ := (fun X Y h, by linarith [A.size_monotone_ Y X h]),
  size_modular_ := (fun X Y, by linarith [A.size_modular_ X Y]),
  size_bot_ := (by linarith),
}

def fin_bool_alg.interval (A : fin_bool_alg) (small big : A): (small ⊆ big) → fin_bool_alg := fun H, {
  subset := {X : A // (small ⊆ X) ∧ (X ⊆ big)}, -- there is unfortunately a coercion from this to A
  contained := (fun X Y, X.val ⊆ Y.val),
  bot := ⟨small, A.refl, H⟩,
  top := ⟨big, H, A.refl⟩,
  inter := (fun X Y, ⟨X.val ∩ Y.val, A.inter_maximal X.prop.left Y.prop.left, A.trans A.inter_subset_left X.prop.right⟩),
  union := (fun X Y, ⟨X.val ∪ Y.val, A.trans X.prop.left A.left_subset_union, A.union_minimal X.prop.right Y.prop.right⟩),
  compl := (fun X, ⟨(X.valᶜ ∪ small) ∩ big, A.inter_maximal A.right_subset_union H, A.inter_subset_right⟩),
  size := (fun X, A.size X.val - A.size small),

  refl_ := (fun X, A.refl),
  antisymm_ := (fun X Y h₁ h₂, subtype.ext (A.antisymm h₁ h₂)),
  trans_ := (fun X Y Z, A.trans),
  bot_subset_ := (fun X, X.prop.left),
  subset_top_ := (fun X, X.prop.right),
  inter_subset_left_ := (fun X Y, A.inter_subset_left),
  inter_subset_right_ := (fun X Y, A.inter_subset_right),
  inter_maximal_ := (fun X Y Z, A.inter_maximal),
  left_subset_union_ := (fun X Y, A.left_subset_union),
  right_subset_union_ := (fun X Y, A.right_subset_union),
  union_minimal_ := (fun X Y Z, A.union_minimal),
  inter_distrib_union_ := (fun X Y Z, subtype.ext A.inter_distrib_union_left),
  self_inter_compl_ := (fun X, subtype.ext (calc
      X.val ∩ ((X.valᶜ ∪ small) ∩ big)
    = (X.val ∩ X.valᶜ ∩ big) ∪ (X.val ∩ small ∩ big) : by simp only [fin_bool_alg.inter_distrib_union_left, fin_bool_alg.inter_distrib_union_right, fin_bool_alg.inter_assoc]
... =                          (X.val ∩ small ∩ big) : by rw [fin_bool_alg.self_inter_compl_self, fin_bool_alg.bot_inter, fin_bool_alg.bot_union]
... = small                                          : let h₁ : X.val ∩ small = small := A.inter_eq_right X.prop.left, h₂ : small ∩ big = small := A.inter_eq_left H in by rw [h₁, h₂]
  )),
  self_union_compl_ := (fun X, subtype.ext (calc
      X.val ∪ ((X.valᶜ ∪ small) ∩ big)
    = (X.val ∪ X.valᶜ ∪ small) ∩ (X.val ∪ big) : by simp only [fin_bool_alg.union_distrib_inter_left, fin_bool_alg.union_assoc]
... =                            (X.val ∪ big) : by rw [fin_bool_alg.self_union_compl_self, fin_bool_alg.top_union, fin_bool_alg.top_inter]
... = big                                      : A.union_eq_right X.prop.right
  )),
  size_nonneg_ := (fun X, by linarith [A.size_monotone_ small X.val X.prop.left]),
  size_monotone_ := (fun X Y h, by linarith [A.size_monotone h]),
  size_modular_ := (fun X Y, by linarith [@fin_bool_alg.size_modular A X.val Y.val]),
  size_bot_ := (by linarith),
}

-- TODO: isomorphisms of fin_bool_alg

example (A : fin_bool_alg) (small X big : A) :
  X ∩ ((Xᶜ ∪ small) ∩ big) = (X ∩ Xᶜ ∩ big) ∪ (X ∩ small ∩ big) :=
begin
  simp only [fin_bool_alg.inter_distrib_union_left, fin_bool_alg.inter_distrib_union_right, fin_bool_alg.inter_assoc],

end

end API

-- The rank-function definition of a matroid, as a packed structure.
@[ext] structure matroid :=
  (subset : fin_bool_alg)
  (rank : subset → ℤ)

  (R0 : forall (X : subset),
    0 ≤ rank X)
  (R1 : forall (X : subset),
    rank X ≤ size X)
  (R2 : forall {X Y : subset},
    X ⊆ Y → rank X ≤ rank Y)
  (R3 : forall (X Y : subset),
    rank (X ∩ Y) + rank (X ∪ Y) ≤ rank X + rank Y)

-- An example: uniform matroids, with rank `k` and size `n`.
def uniform_matroid (k n : ℤ) : (0 ≤ k) → (k ≤ n) → matroid :=
  fun (h0k : 0 ≤ k) (hkn : k ≤ n), let
    A : fin_bool_alg := fin_bool_alg.canonical n (le_trans h0k hkn)
  in {
    subset := A,
    rank := (fun (X : A), min k (size X)),

    R0 := (fun X, le_min h0k A.size_nonneg),
    R1 := (fun X, min_le_right _ _),
    R2 := (fun X Y (h : X ⊆ Y), le_min (min_le_left k _) (le_trans (min_le_right _ (size X)) (A.size_monotone h))),
    R3 := (fun X Y, or.elim (le_total k (size X))
      (fun (hkX : k ≤ size X), or.elim (le_total k (size Y))
        (fun (hkY : k ≤ (size Y)), let
          term1 : (min k (size (X ∩ Y)) ) ≤ k := min_le_left _ _,
          term2 : (min k (size (X ∪ Y)) ) ≤ k := min_le_left _ _,
          term3 : (min k (size X)) = k := min_eq_left hkX,
          term4 : (min k (size Y)) = k := min_eq_left hkY
          in by linarith)
        (fun (hYk : (size Y) ≤ k), let
          term1 : (min k (size (X ∩ Y))) ≤ (size Y) := le_trans (min_le_right _ _) (A.size_monotone A.inter_subset_right),
          term2 : (min k (size (X ∪ Y))) ≤ k := min_le_left _ _,
          term3 : (min k (size X)) = k := min_eq_left hkX,
          term4 : (min k (size Y)) = (size Y) := min_eq_right hYk
          in by linarith))
      (fun (hXk : (size X) ≤ k), or.elim (le_total k (size Y))
        (fun (hkY : k ≤ (size Y)), let
          term1 : (min k (size (X ∩ Y))) ≤ (size X) := le_trans (min_le_right _ _) (A.size_monotone A.inter_subset_left),
          term2 : (min k (size (X ∪ Y))) ≤ k := min_le_left _ _,
          term3 : (min k (size X)) = (size X) := min_eq_right hXk,
          term4 : (min k (size Y)) = k := min_eq_left hkY
          in by linarith)
        (fun (hYk : size Y ≤ k), let
          term1 : (min k (size (X ∩ Y))) ≤ size (X ∩ Y) := min_le_right _ _,
          term2 : (min k (size (X ∪ Y))) ≤ size (X ∪ Y) := min_le_right _ _,
          term3 : (min k (size X)) = size X := min_eq_right hXk,
          term4 : (min k (size Y)) = size Y := min_eq_right hYk
          in by linarith [@fin_bool_alg.size_modular A X Y]))),
  }

-- The empty set always has rank zero.
lemma matroid.rank_empty (M : matroid) :
  M.rank ⊥ = 0
    := le_antisymm (calc M.rank ⊥ ≤ size ⊥ : M.R1 ⊥ ... = 0 : M.subset.size_bot) (M.R0 ⊥)

-- The definition of the dual matroid. R2 is the trickier axiom to prove.
def matroid.dual : matroid → matroid := fun M, {
  subset := M.subset,
  rank := (fun (X : M.subset), M.rank Xᶜ + size X - M.rank ⊤),

  R0 := (fun X, calc
    0   ≤ M.rank Xᶜ + M.rank X - M.rank (X ∪ Xᶜ) - M.rank (X ∩ Xᶜ) : by linarith [M.R3 X Xᶜ]
    ... ≤ M.rank Xᶜ + M.rank X - M.rank ⊤        - M.rank ⊥        : by rw [@fin_bool_alg.self_inter_compl_self _ X, @fin_bool_alg.self_union_compl_self _ X]
    ... ≤ M.rank Xᶜ + size X   - M.rank ⊤                          : by linarith [M.R1 X, M.rank_empty]),
  R1 := (fun X, by linarith [M.R2 (@fin_bool_alg.subset_top _ Xᶜ)]),
  R2 := (fun X Y (hXY : X ⊆ Y), let
    h₁ : (Xᶜ ∩ Y) ∩ Yᶜ = ⊥ := calc
      (Xᶜ ∩ Y) ∩ Yᶜ = Xᶜ ∩ (Y ∩ Yᶜ) : M.subset.inter_assoc
      ...           = Xᶜ ∩ ⊥        : by rw [@fin_bool_alg.self_inter_compl_self _ Y]
      ...           = ⊥             : M.subset.inter_bot,
    h₂ : (Xᶜ ∪ Yᶜ) = Xᶜ := calc
      (Xᶜ ∪ Yᶜ) = (X ∩ Y)ᶜ : M.subset.compl_inter.symm
      ...       = Xᶜ       : by rw [M.subset.inter_eq_left hXY],
    h₃ : (Xᶜ ∩ Y) ∪ Yᶜ = Xᶜ := calc
      (Xᶜ ∩ Y) ∪ Yᶜ = (Xᶜ ∪ Yᶜ) ∩ (Y ∪ Yᶜ) : M.subset.union_distrib_inter_right
      ...           = Xᶜ ∩ ⊤               : by rw [h₂, @fin_bool_alg.self_union_compl_self _ Y]
      ...           = Xᶜ                   : M.subset.inter_top,
    h₄ : M.rank Xᶜ ≤ size Y - size X + M.rank Yᶜ := calc
      M.rank Xᶜ = M.rank ⊥ + M.rank Xᶜ                            : by linarith [M.rank_empty]
      ...       = M.rank ((Xᶜ ∩ Y) ∩ Yᶜ) + M.rank ((Xᶜ ∩ Y) ∪ Yᶜ) : by rw [h₁, h₃]
      ...       ≤ M.rank (Xᶜ ∩ Y) + M.rank Yᶜ                     : M.R3 _ _
      ...       ≤ size (Xᶜ ∩ Y) + M.rank Yᶜ                       : by linarith [M.R1 (Xᶜ ∩ Y)]
      ...       = size Y - size X + M.rank Yᶜ                     : by rw [M.subset.size_diff hXY]
    in by linarith),
  R3 := (fun X Y, calc
      (M.rank (X ∩ Y)ᶜ  + size (X ∩ Y) - M.rank ⊤) + (M.rank (X ∪ Y)ᶜ  + size (X ∪ Y) - M.rank ⊤)
    = (M.rank (Xᶜ ∪ Yᶜ) + size (X ∩ Y) - M.rank ⊤) + (M.rank (Xᶜ ∩ Yᶜ) + size (X ∪ Y) - M.rank ⊤) : by rw [@fin_bool_alg.compl_inter _ X Y, @fin_bool_alg.compl_union _ X Y]
... ≤ (M.rank Xᶜ        + size X       - M.rank ⊤) + (M.rank Yᶜ        + size Y       - M.rank ⊤) : by linarith [M.R3 Xᶜ Yᶜ, @fin_bool_alg.size_modular _ X Y]),
}

/-
-- The definition of a minor is weird-looking, but should correctly capture the notion of equality of minors.
@[ext] structure minor (major : matroid) :=
  (ground : major.ground.subset)
  (rank   : {X : major.ground.subset // X ⊆ ground} → ℤ)
  (kernel : exists (C : major.ground.subset),
    (ground ∩ C = ⊥) ∧
    (forall X, rank X = major.rank (X.val ∪ C) - major.rank C))

-- A matroid minor is a matroid in its own right.
def minor.as_matroid {M : matroid} (m : minor M) : matroid := {
  ground := m.ground.as_finite_set,
  rank := (fun (X : m.ground.as_finite_set.subset),
    m.rank (m.ground.embed X) (m.ground.embed_subset X)),

  R0 := (exists.elim m.kernel (fun C h mX, let
    X := m.ground.embed mX,
    h₁ : m.rank X _ = M.rank (X ∪ C) - M.rank C := h.2 _ (m.ground.embed_subset _),
    h₂ : M.rank C ≤ M.rank (X ∪ C) := M.R2 (X.right_subset_union C)
    in by linarith)),
  R1 := (exists.elim m.kernel (fun C h mX, let
    X := m.ground.embed mX,
    h₁ : m.rank X _ = M.rank (X ∪ C) - M.rank C := h.2 _ (m.ground.embed_subset _)
    in _)),
  R2 := sorry,
  R3 := sorry,
}

-- Is this possible to prove? Mathematically it should be.
lemma minor.as_matroid.injective {M : matroid} (m₁ m₂ : minor M) :
  (m₁.as_matroid = m₂.as_matroid) → m₁ = m₂ :=
    sorry

def minor.delete {M : matroid} (m : minor M) (D : M.ground.subset) :
  (D ⊆ m.ground) → (minor M) := fun h, {
    ground := (Dᶜ ∩ m.ground),
    rank := sorry,
    kernel := sorry,
  }

def minor.contract {M : matroid} (m : minor M) (C : M.ground.subset) :
  (C ⊆ m.ground) → (minor M) := fun h, {
    ground := (Cᶜ ∩ m.ground),
    rank := sorry,
    kernel := sorry,
  }
-/


/-

def finite_set : Type := sorry
def finite_set.subset : finite_set → Type := sorry
def finite_set.subset.size {γ : finite_set} : γ.subset → ℤ := sorry
instance has_subset_finite_set_subset {γ : finite_set} : has_subset γ.subset := sorry
instance has_inter_finite_set_subset {γ : finite_set} : has_inter γ.subset := sorry
instance has_union_finite_set_subset {γ : finite_set} : has_union γ.subset := sorry
instance has_compl_finite_set_subset {γ : finite_set} : has_compl γ.subset := sorry
instance has_top_finite_set_subset {γ : finite_set} : has_top γ.subset := sorry
instance has_bot_finite_set_subset {γ : finite_set} : has_bot γ.subset := sorry

@[trans] lemma finite_set.subset.trans {γ : finite_set} {X Y Z : γ.subset} :
  (X ⊆ Y) → (Y ⊆ Z) → (X ⊆ Z) := sorry

def finite_set.canonical (size : ℤ) :
  (0 ≤ size) → finite_set := sorry

def finite_set.subset.as_finite_set {γ : finite_set} :
  γ.subset → finite_set := sorry

def finite_set.subset.as_finite_set.injective {γ : finite_set} {X Y : γ.subset} :
  (X.as_finite_set = Y.as_finite_set) → (X = Y) := sorry

def finite_set.subset.embed {γ : finite_set} (X : γ.subset) :
  X.as_finite_set.subset → γ.subset := sorry

def finite_set.subset.restrict {γ : finite_set} (X Y : γ.subset) :
  (X ⊆ Y) → Y.as_finite_set.subset := sorry

lemma finite_set.subset.embed_subset {γ : finite_set} (X : γ.subset) (Y : X.as_finite_set.subset) :
  (X.embed Y) ⊆ X := sorry

lemma finite_set.subset.subset_embed {γ : finite_set} (X : γ.subset) (Y Z : X.as_finite_set.subset) :
  (Y ⊆ Z) → (X.embed Y) ⊆ (X.embed Z) := sorry

lemma finite_set.subset.inter_embed {γ : finite_set} (X : γ.subset) (Y Z : X.as_finite_set.subset) :
  (X.embed (Y ∩ Z)) = (X.embed Y) ∩ (X.embed Z) := sorry

lemma finite_set.subset.union_embed {γ : finite_set} (X : γ.subset) (Y Z : X.as_finite_set.subset) :
  (X.embed (Y ∪ Z)) = (X.embed Y) ∪ (X.embed Z) := sorry

lemma finite_set.subset.embed_size {γ : finite_set} (X : γ.subset) (Y : X.as_finite_set.subset) :
  (X.embed Y).size = Y.size := sorry

lemma finite_set.subset.size_empty {γ : finite_set} :
  (⊥ : γ.subset).size = 0 := sorry

lemma finite_set.subset.size_nonneg {γ : finite_set} (X : γ.subset) :
  0 ≤ X.size := sorry

lemma finite_set.subset.size_monotone {γ : finite_set} (X Y : γ.subset) :
  (X ⊆ Y) → X.size ≤ Y.size := sorry

lemma finite_set.subset.size_modular {γ : finite_set} (X Y : γ.subset) :
  (X ∩ Y).size + (X ∪ Y).size = X.size + Y.size := sorry

lemma finite_set.subset.inter_subset_left {γ : finite_set} (X Y : γ.subset) :
  (X ∩ Y) ⊆ X := sorry

lemma finite_set.subset.inter_subset_right {γ : finite_set} (X Y : γ.subset) :
  (X ∩ Y) ⊆ Y := sorry

lemma finite_set.subset.left_subset_union {γ : finite_set} (X Y : γ.subset) :
  X ⊆ (X ∪ Y) := sorry

lemma finite_set.subset.right_subset_union {γ : finite_set} (X Y : γ.subset) :
  Y ⊆ (X ∪ Y) := sorry

lemma finite_set.subset.inter_compl_self {γ : finite_set} (X : γ.subset) :
  (X ∩ Xᶜ) = ⊥ := sorry

lemma finite_set.subset.union_compl_self {γ : finite_set} (X : γ.subset) :
  (X ∪ Xᶜ) = ⊤ := sorry

lemma finite_set.subset.subset_top {γ : finite_set} (X : γ.subset) :
  X ⊆ ⊤ := calc X ⊆ (X ∪ Xᶜ) : X.left_subset_union Xᶜ ... = ⊤ : X.union_compl

lemma finite_set.subset.compl_inter {γ : finite_set} (X Y : γ.subset) :
  (X ∩ Y)ᶜ = Xᶜ ∪ Yᶜ := sorry

lemma finite_set.subset.compl_union {γ : finite_set} (X Y : γ.subset) :
  (X ∪ Y)ᶜ = Xᶜ ∩ Yᶜ := sorry

lemma finite_set.subset.inter_assoc {γ : finite_set} (X Y Z : γ.subset) :
  (X ∩ Y) ∩ Z = X ∩ (Y ∩ Z) := sorry

lemma finite_set.subset.inter_bot {γ : finite_set} (X : γ.subset) :
  (X ∩ ⊥) = ⊥ := sorry

lemma finite_set.subset.inter_top {γ : finite_set} (X : γ.subset) :
  (X ∩ ⊤) = X := sorry

lemma finite_set.subset.union_distrib_inter_left {γ : finite_set} (X Y Z : γ.subset) :
  (X ∩ Y) ∪ Z = (X ∪ Z) ∩ (Y ∪ Z) := sorry

lemma finite_set.subset.union_distrib_union_left {γ : finite_set} (X Y Z : γ.subset) :
  (X ∪ Y) ∪ Z = (X ∪ Z) ∪ (Y ∪ Z) := sorry

lemma finite_set.subset.inter_eq_left {γ : finite_set} (X Y : γ.subset) :
  (X ⊆ Y) → (X ∩ Y) = X := sorry

lemma finite_set.subset.diff_size {γ : finite_set} (X Y : γ.subset) :
  (X ⊆ Y) → (Xᶜ ∩ Y).size = Y.size - X.size := sorry

lemma finite_set.subset.subset_inter_subset_left {γ : finite_set} (X Y Z : γ.subset) :
  (X ⊆ Y) → (X ∩ Z) ⊆ (Y ∩ Z) := sorry

lemma finite_set.subset.subset_union_subset_left {γ : finite_set} (X Y Z : γ.subset) :
  (X ⊆ Y) → (X ∪ Z) ⊆ (Y ∪ Z) := sorry

lemma finite_set.subset.subset_bot {γ : finite_set} (X : γ.subset) :
  (X ⊆ ⊥) → (X = ⊥) := sorry
-/

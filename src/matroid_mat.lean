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

  (size_monotone {X Y : subset} : (contained X Y) → size X ≤ size Y)
  (size_nonneg (X: subset) : 0 ≤ size X) 
  (size_modular (X Y: subset) : size (union X Y) + size (inter X Y) = size X + size Y)
  (size_empty : size bot = 0)

  (inter_subset_left (X Y : subset) : contained (inter X Y) X)
  (inter_subset_right (X Y : subset) : contained (inter X Y) Y)
  (inter_is_lb (X Y Z : subset) : (contained Z X) → (contained Z Y) → contained (inter X Y) Z) 

  (union_compl (X: subset) : union X (compl X) = top)
  (inter_compl (X: subset) : inter X (compl X) = bot)


instance i1 : has_coe_to_sort fin_bool_alg := {S := Type, coe := fin_bool_alg.subset}
instance i2 {A : fin_bool_alg} : has_bot A := {bot := A.bot}
instance i3 {A : fin_bool_alg} : has_top A := {top := A.top}
instance i4 {A : fin_bool_alg} : has_inter A := {inter := A.inter}
instance i5 {A : fin_bool_alg} : has_union A := {union := A.union}
instance i6 {A : fin_bool_alg} : has_compl A := {compl := A.compl}
instance i7 {A : fin_bool_alg} : has_subset A := {subset := A.contained} 

def size {A : fin_bool_alg} (X : A) : ℤ := A.size X

def fin_bool_alg.canonical (size : ℤ) :
  (0 ≤ size) → fin_bool_alg := sorry

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

lemma finite_set.subset.inter_compl {γ : finite_set} (X : γ.subset) :
  (X ∩ Xᶜ) = ⊥ := sorry

lemma finite_set.subset.union_compl {γ : finite_set} (X : γ.subset) :
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

    R0 := (fun X, le_min h0k (A.size_nonneg X)),
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
          term1 : (min k (size (X ∩ Y))) ≤ (size Y) := le_trans (min_le_right _ _) (A.size_monotone (A.inter_subset_right X Y)),
          term2 : (min k (size (X ∪ Y))) ≤ k := min_le_left _ _,
          term3 : (min k (size X)) = k := min_eq_left hkX,
          term4 : (min k (size Y)) = (size Y) := min_eq_right hYk
          in by linarith))
      (fun (hXk : (size X) ≤ k), or.elim (le_total k (size Y))
        (fun (hkY : k ≤ (size Y)), let
          term1 : (min k (size (X ∩ Y))) ≤ (size X) := le_trans (min_le_right _ _) (A.size_monotone (A.inter_subset_left X Y)),
          term2 : (min k (size (X ∪ Y))) ≤ k := min_le_left _ _,
          term3 : (min k (size X)) = (size X) := min_eq_right hXk,
          term4 : (min k (size Y)) = k := min_eq_left hkY
          in by linarith)
        (fun (hYk : size Y ≤ k), let
          term1 : (min k (size (X ∩ Y))) ≤ size (X ∩ Y) := min_le_right _ _,
          term2 : (min k (size (X ∪ Y))) ≤ size (X ∪ Y) := min_le_right _ _,
          term3 : (min k (size X)) = size X := min_eq_right hXk,
          term4 : (min k (size Y)) = size Y := min_eq_right hYk,
          term5 : size (X ∪ Y) + size (X ∩ Y) = size X + size Y := A.size_modular X Y
          in by linarith))),
  }

-- The empty set always has rank zero.
lemma matroid.rank_empty (M : matroid) :
  M.rank ⊥ = 0
    := le_antisymm (calc M.rank ⊥ ≤ size (⊥ : M.subset) : M.R1 ⊥ ... = 0 : M.subset.size_empty) (M.R0 ⊥)

-- The definition of the dual matroid. R2 is the trickier axiom to prove.
def matroid.dual : matroid → matroid := fun M, {
  subset := M.subset,
  rank := (fun (X : M.subset), M.rank Xᶜ + (size X) - M.rank ⊤),

  R0 := (fun X, calc
    0   ≤ M.rank Xᶜ + M.rank X - M.rank (X ∪ Xᶜ) - M.rank (X ∩ Xᶜ) : by linarith [M.R3 X Xᶜ]
    ... ≤ M.rank Xᶜ + M.rank X - M.rank ⊤        - M.rank ⊥        : by rw [M.subset.union_compl X, M.subset.inter_compl X]
    ... ≤ M.rank Xᶜ + (size X)  - M.rank ⊤                         : by linarith [M.R1 X, M.rank_empty]),
  R1 := (fun X, by linarith [M.R2 Xᶜ.subset_top]),
  R2 := (fun X Y (hXY : X ⊆ Y), let
    h₁ : (Xᶜ ∩ Y) ∩ Yᶜ = ⊥ := calc
      (Xᶜ ∩ Y) ∩ Yᶜ = Xᶜ ∩ (Y ∩ Yᶜ) : Xᶜ.inter_assoc Y Yᶜ
      ...           = Xᶜ ∩ ⊥        : by rw [Y.inter_compl]
      ...           = ⊥             : Xᶜ.inter_bot,
    h₂ : (Xᶜ ∪ Yᶜ) = Xᶜ := calc
      (Xᶜ ∪ Yᶜ) = (X ∩ Y)ᶜ : (X.compl_inter Y).symm
      ...       = Xᶜ       : by rw [X.inter_eq_left Y hXY],
    h₃ : (Xᶜ ∩ Y) ∪ Yᶜ = Xᶜ := calc
      (Xᶜ ∩ Y) ∪ Yᶜ = (Xᶜ ∪ Yᶜ) ∩ (Y ∪ Yᶜ) : Xᶜ.union_distrib_inter_left Y Yᶜ
      ...           = Xᶜ ∩ ⊤               : by rw [h₂, Y.union_compl]
      ...           = Xᶜ                   : Xᶜ.inter_top,
    h₄ : M.rank Xᶜ ≤ Y.size - X.size + M.rank Yᶜ := calc
      M.rank Xᶜ = M.rank ⊥ + M.rank Xᶜ                            : by linarith [M.rank_empty]
      ...       = M.rank ((Xᶜ ∩ Y) ∩ Yᶜ) + M.rank ((Xᶜ ∩ Y) ∪ Yᶜ) : by rw [h₁, h₃]
      ...       ≤ M.rank (Xᶜ ∩ Y) + M.rank Yᶜ                     : M.R3 _ _
      ...       ≤ (Xᶜ ∩ Y).size + M.rank Yᶜ                       : by linarith [M.R1 (Xᶜ ∩ Y)]
      ...       = Y.size - X.size + M.rank Yᶜ                     : by rw [X.diff_size Y hXY]
    in by linarith),
  R3 := (fun X Y, calc
      (M.rank (X ∩ Y)ᶜ  + (X ∩ Y).size - M.rank ⊤) + (M.rank (X ∪ Y)ᶜ  + (X ∪ Y).size - M.rank ⊤)
    = (M.rank (Xᶜ ∪ Yᶜ) + (X ∩ Y).size - M.rank ⊤) + (M.rank (Xᶜ ∩ Yᶜ) + (X ∪ Y).size - M.rank ⊤) : by rw [X.compl_inter Y, X.compl_union Y]
... ≤ (M.rank Xᶜ        + X.size       - M.rank ⊤) + (M.rank Yᶜ        + Y.size       - M.rank ⊤) : by linarith [M.R3 Xᶜ Yᶜ, X.size_modular Y]),
}

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

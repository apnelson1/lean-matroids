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
import tactic.ring
import tactic.linarith

-- The API for finite boolean algebras (now moved)

import boolalg
import func_heq


/-


  --(inter_subset_right (X Y : subset) : contained (inter X Y) Y)


lemma boolalg.inter_subset_right {A: boolalg} (X Y : A) : (X ∩ Y) ⊆ Y := sorry
lemma boolalg.subset_inter {A: boolalg} (X Y Z : A) : (Z ⊆ X) → (Z ⊆ Y) → ((X ∩ Y) ⊆ Z) := sorry


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

end API

-/
namespace boolalg
-- The rank-function definition of a matroid, as a packed structure.
@[ext] structure matroid :=
  (A : boolalg)
  (rank : A → ℤ)

  (R0 : forall (X : A),
    0 ≤ rank X)
  (R1 : forall (X : A),
    rank X ≤ size X)
  (R2 : forall {X Y : A},
    X ⊆ Y → rank X ≤ rank Y)
  (R3 : forall (X Y : A),
    rank (X ∩ Y) + rank (X ∪ Y) ≤ rank X + rank Y)

-- An example: uniform matroids, with rank `k` and size `n`.
def uniform_matroid (k n : ℤ) : (0 ≤ k) → (k ≤ n) → matroid :=
  fun (h0k : 0 ≤ k) (hkn : k ≤ n), let
    A : boolalg := boolalg.canonical n (le_trans h0k hkn)
  in {
    A := A,
    rank := (fun (X : A), min k (size X)),

    R0 := (fun X, le_min h0k (size_nonneg X)),
    R1 := (fun X, min_le_right _ _),
    R2 := (fun X Y (h : X ⊆ Y), le_min (min_le_left k _) (le_trans (min_le_right _ (size X)) (size_monotone h))),
    R3 := (fun X Y, or.elim (le_total k (size X))
      (fun (hkX : k ≤ size X), or.elim (le_total k (size Y))
        (fun (hkY : k ≤ (size Y)), let
          term1 : (min k (size (X ∩ Y)) ) ≤ k := min_le_left _ _,
          term2 : (min k (size (X ∪ Y)) ) ≤ k := min_le_left _ _,
          term3 : (min k (size X)) = k := min_eq_left hkX,
          term4 : (min k (size Y)) = k := min_eq_left hkY
          in by linarith)
        (fun (hYk : (size Y) ≤ k), let
          term1 : (min k (size (X ∩ Y))) ≤ (size Y) := le_trans (min_le_right _ _) (size_monotone (inter_subset_right X Y)),
          term2 : (min k (size (X ∪ Y))) ≤ k := min_le_left _ _,
          term3 : (min k (size X)) = k := min_eq_left hkX,
          term4 : (min k (size Y)) = (size Y) := min_eq_right hYk
          in by linarith))
      (fun (hXk : (size X) ≤ k), or.elim (le_total k (size Y))
        (fun (hkY : k ≤ (size Y)), let
          term1 : (min k (size (X ∩ Y))) ≤ (size X) := le_trans (min_le_right _ _) (size_monotone (inter_subset_left X Y)),
          term2 : (min k (size (X ∪ Y))) ≤ k := min_le_left _ _,
          term3 : (min k (size X)) = (size X) := min_eq_right hXk,
          term4 : (min k (size Y)) = k := min_eq_left hkY
          in by linarith)
        (fun (hYk : size Y ≤ k), let
          term1 : (min k (size (X ∩ Y))) ≤ size (X ∩ Y) := min_le_right _ _,
          term2 : (min k (size (X ∪ Y))) ≤ size (X ∪ Y) := min_le_right _ _,
          term3 : (min k (size X)) = size X := min_eq_right hXk,
          term4 : (min k (size Y)) = size Y := min_eq_right hYk,
          term5 : size (X ∪ Y) + size (X ∩ Y) = size X + size Y := size_modular X Y
          in by linarith))),
  }

-- The empty set always has rank zero.
lemma matroid.rank_empty (M : matroid) :
  M.rank ⊥ = 0
    := le_antisymm (calc M.rank ⊥ ≤ size (⊥ : M.A) : M.R1 ⊥ ... = 0 : size_bot M.A) (M.R0 ⊥)

-- The definition of the dual matroid. R2 is the trickier axiom to prove.
def matroid.dual (M : matroid) : matroid :=
{
  A := M.A,
  rank := (fun (X : M.A), M.rank Xᶜ + (size X) - M.rank ⊤),

  R0 := (fun X, calc
    0   ≤ M.rank Xᶜ + M.rank X - M.rank (X ∪ Xᶜ) - M.rank (X ∩ Xᶜ) : by linarith [M.R3 X Xᶜ]
    ... ≤ M.rank Xᶜ + M.rank X - M.rank ⊤        - M.rank ⊥        : by rw [union_compl_self X, inter_compl_self X]
    ... ≤ M.rank Xᶜ + (size X)  - M.rank ⊤                         : by linarith [M.R1 X, M.rank_empty]),
  R1 := (fun X, by linarith [M.R2 (subset_top Xᶜ)]),
  R2 := (fun X Y (hXY : X ⊆ Y), let
    h₁ : (Xᶜ ∩ Y) ∩ Yᶜ = ⊥ := calc
      (Xᶜ ∩ Y) ∩ Yᶜ = Xᶜ ∩ (Y ∩ Yᶜ) : inter_assoc Xᶜ Y Yᶜ
      ...           = Xᶜ ∩ ⊥        : by rw [inter_compl_self Y]
      ...           = ⊥             : inter_bot Xᶜ,
    h₂ : (Xᶜ ∪ Yᶜ) = Xᶜ := calc
      (Xᶜ ∪ Yᶜ) = (X ∩ Y)ᶜ : (compl_inter X Y).symm
      ...       = Xᶜ       : by rw [inter_subset_mp hXY],
    h₃ : (Xᶜ ∩ Y) ∪ Yᶜ = Xᶜ := calc
      (Xᶜ ∩ Y) ∪ Yᶜ = (Xᶜ ∪ Yᶜ) ∩ (Y ∪ Yᶜ) : union_distrib_right Xᶜ Y Yᶜ --Xᶜ.union_distrib_inter_left Y Yᶜ
      ...           = Xᶜ ∩ ⊤               : by rw [h₂, union_compl_self Y]
      ...           = Xᶜ                   : inter_top Xᶜ,
    h₄ : M.rank Xᶜ ≤ size Y - size X + M.rank Yᶜ := calc
      M.rank Xᶜ = M.rank ⊥ + M.rank Xᶜ                            : by linarith [M.rank_empty]
      ...       = M.rank ((Xᶜ ∩ Y) ∩ Yᶜ) + M.rank ((Xᶜ ∩ Y) ∪ Yᶜ) : by rw [h₁, h₃]
      ...       ≤ M.rank (Xᶜ ∩ Y) + M.rank Yᶜ                     : M.R3 _ _
      ...       ≤ size (Xᶜ ∩ Y) + M.rank Yᶜ                       : by linarith [M.R1 (Xᶜ ∩ Y)]
      ...       = size Y - size X + M.rank Yᶜ                     : by rw [compl_inter_size_subset hXY]
    in by linarith),
  R3 := (fun X Y, calc
      (M.rank (X ∩ Y)ᶜ  + size (X ∩ Y) - M.rank ⊤) + (M.rank (X ∪ Y)ᶜ  + size (X ∪ Y) - M.rank ⊤)
    = (M.rank (Xᶜ ∪ Yᶜ) + size (X ∩ Y) - M.rank ⊤) + (M.rank (Xᶜ ∩ Yᶜ) + size (X ∪ Y) - M.rank ⊤) : by rw [compl_inter X Y, compl_union X Y]
... ≤ (M.rank Xᶜ        + size X       - M.rank ⊤) + (M.rank Yᶜ        + size Y       - M.rank ⊤) : by linarith [M.R3 Xᶜ Yᶜ, size_modular X Y]),
}

lemma rank_bot (M : matroid) :
  M.rank ⊥ = 0 :=
  by linarith[M.R0 ⊥, M.R1 ⊥, size_bot M.A]

lemma dual_dual (M : matroid) : M.dual.dual = M :=
begin
    ext, refl, refl,
    intros X X' hXX',
    apply heq_of_eq, rw ←(eq_of_heq hXX'),

    calc M.dual.dual.rank X = M.dual.rank Xᶜ + size X - M.dual.rank ⊤                                                 : rfl
    ...                     = (M.rank Xᶜᶜ + size Xᶜ - M.rank ⊤) + size X - (M.rank ⊤ᶜ + size (⊤ : M.A) - M.rank ⊤)   : rfl 
    ...                     = M.rank Xᶜᶜ + (size X + size Xᶜ - size (⊤ : M.A)) - (M.rank ⊤ᶜ)                          : by linarith
    ...                     = M.rank X + (size (⊤ : M.A) - size (⊤ : M.A)) - M.rank ⊥                                 : by rw [compl_compl, size_compl_sum, compl_top]
    ...                     = M.rank X                                                                                 : by linarith [rank_bot M]  
end




-- The definition of a minor is weird-looking, but should correctly capture the notion of equality of minors.

/- This definition works in the sense that proofs below are sorry-free, but the problem is now that
it doesn't capture equality correctly; it allows multiple 'versions' of the same minor of M to be
propositionally distinct, both before and after as_matroid is applied. Changing the data in the minor
back to just including ground set and rank function solves this problem, but causes ugliness elsewhere. I
want to be able to insist that the embedding is the inclusion map, but I don't see how to make the inclusion
map canonical in type theory -/

@[ext] structure minor (M : matroid) :=
  (m_A : boolalg)
  (m_rank   : m_A → ℤ)
  (kernel : exists (C : M.A) (emb : boolalg.embedding m_A M.A),
    (emb.func (⊥ : m_A) = ⊥) ∧
    (emb.func (⊤ : m_A) ∩ C = ⊥) ∧
    (forall X, m_rank X = M.rank (emb.func X ∪ C) - M.rank C))


-- A matroid minor is a matroid in its own right.
def minor.as_matroid {M : matroid} (m : minor M) : matroid :=
{
  A := m.m_A,
  rank := m.m_rank,

  R0 := by intros X; rcases m.kernel with ⟨C,emb,⟨h0,hC,hr⟩⟩; linarith [M.R2 (subset_union_right (emb.func X) C), hr X],

  R1 :=
  begin
    intros X, rcases m.kernel with ⟨C,emb,⟨h0,hC,hr⟩⟩,
    linarith [bot_to_bot_embedding_size emb h0 X, M.R0 (emb.func X ∩ C), M.R3 (emb.func X) C, M.R1 (emb.func X), hr X],
  end,
  R2 :=
  begin
    intros X Y hXY, rcases m.kernel with ⟨C,emb,⟨h0,hC,hCr⟩⟩,   
    linarith [M.R2 (subset_union_subset_left (emb.func X) (emb.func Y) C (embedding_on_subset emb hXY )), hCr X, hCr Y],
  end,
  R3 :=
  begin
    intros X Y, rcases m.kernel with ⟨C,emb,⟨h0,hC,hCr⟩⟩,
    let f := emb.func,
    have hu : (f X ∪ C) ∪ (f Y ∪ C) = f (X ∪ Y) ∪ C := by rw ←union_distrib_union_left; rw ←emb.on_union,
    have hi : (f X ∪ C) ∩ (f Y ∪ C) = f (X ∩ Y) ∪ C := by rw ←union_distrib_left; rw ←emb.on_inter,
    have hR3 := M.R3 (f X ∪ C) (f Y ∪ C),
    rw [hu, hi] at hR3,
    linarith [hCr X, hCr Y, hCr (X ∪ Y), hCr (X ∩ Y), hR3],
  end,
}


-- Is this possible to prove? Mathematically it should be.

-- Yes, it is! I'm not happy with the proof, though...
lemma minor.as_matroid.injective {M : matroid} (m₁ m₂ : minor M) :
  (m₁.as_matroid = m₂.as_matroid) → m₁ = m₂ :=
  begin
    intros hmm,

    have h : m₁.m_A = m₂.m_A :=
      by calc m₁.m_A = m₁.as_matroid.A : rfl
               ...   = m₂.as_matroid.A : by rw hmm
               ...   = m₂.m_A            : rfl,

    injections_and_clear,
    ext, exact h, rw h, intros a a' haa', apply heq_of_eq,
    apply congr_heq, exact h_2, exact haa',
  end

end boolalg


/-def minor.delete {M : matroid} (m : minor M) (D : M.ground.subset) :
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
  }-/

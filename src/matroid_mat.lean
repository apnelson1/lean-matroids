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
  --(contained : subset → subset → Prop)
  (bot top : subset)
  (inter union : subset → subset → subset)
  (compl : subset → subset)
  (size : subset → ℤ)

 -- (size_monotone {X Y : subset} : (contained X Y) → size X ≤ size Y)
  (size_bot_ax : size bot = 0)
  (size_nonneg_ax (X: subset) : 0 ≤ size X) 
  (size_modular_ax (X Y: subset) : size (union X Y) + size (inter X Y) = size X + size Y)
  (size_singleton_ax (X : subset) (hX : (∀ (Y: subset), (Y = inter Y X) → (Y ≠ X) → (Y = bot))) : size X = 1)

  (inter_comm_ax (X Y : subset) : inter X Y = inter Y X)
  (union_comm_ax (X Y : subset) : union X Y = union Y X)
  (inter_assoc_ax (X Y Z : subset) : inter (inter X Y) Z = inter X (inter Y Z))
  (union_assoc_ax (X Y Z : subset) : union (union X Y) Z = union X (union Y Z))

  (union_distrib_inter_left_ax (X Y Z : subset) : union (inter X Y) Z = inter (union X Z) (union Y Z))
  (inter_distrib_union_left_ax (X Y Z : subset) : inter (union X Y) Z = union (inter X Z) (inter Y Z))

  (absorb_union_inter_ax (X Y : subset) : union X (inter X Y) = X)
  (absorb_inter_union_ax (X Y : subset) : inter X (union X Y) = X)

  (inter_top_ax (X : subset) : inter X top = X)
  (union_top_ax (X : subset) : union X top = top)
  (inter_bot_ax (X : subset) : inter X bot = bot)
  (union_bot_ax (X : subset) : union X bot = X)

  (union_compl_ax (X: subset) : union X (compl X) = top)
  (inter_compl_ax (X: subset) : inter X (compl X) = bot)

  --(inter_is_lb (X Y Z : subset) : (contained Z X) → (contained Z Y) → contained (inter X Y) Z) 

-- Instances to enable ⊆ , ∩ , ∪ , ᶜ , ⊤, ⊥ , - (set diff)

instance i1 : has_coe_to_sort fin_bool_alg := {S := Type, coe := fin_bool_alg.subset}
instance i2 {A : fin_bool_alg} : has_bot A := {bot := A.bot}
instance i3 {A : fin_bool_alg} : has_top A := {top := A.top}
instance i4 {A : fin_bool_alg} : has_inter A := {inter := A.inter}
instance i5 {A : fin_bool_alg} : has_union A := {union := A.union}
instance i6 {A : fin_bool_alg} : has_compl A := {compl := A.compl}
instance i7 {A : fin_bool_alg} : has_subset A := {subset := λ (X Y), (X = X ∩ Y)} 
instance i8 {A : fin_bool_alg} : has_sub A := {sub := λ (X Y), X ∩ Yᶜ}

def size {A : fin_bool_alg} (X : A) : ℤ := A.size X

-- Below are just the axioms (some with right/left versions), written in terms of the shorthand to make linarith, calc etc behave more nicely. 

lemma inter_comm {A : fin_bool_alg} (X Y : A) : (X ∩ Y = Y ∩ X) := A.inter_comm_ax X Y
lemma union_comm {A : fin_bool_alg} (X Y : A) : (X ∪ Y = Y ∪ X) := A.union_comm_ax X Y

lemma inter_assoc {A : fin_bool_alg} (X Y Z : A) : (X ∩ Y) ∩ Z = X ∩ (Y ∩ Z) := A.inter_assoc_ax X Y Z 
lemma union_assoc {A : fin_bool_alg} (X Y Z : A) : (X ∪ Y) ∪ Z = X ∪ (Y ∪ Z) := A.union_assoc_ax X Y Z 

lemma union_distrib_inter_left {A : fin_bool_alg} (X Y Z : A) : (X ∩ Y) ∪ Z = (X ∪ Z) ∩ (Y ∪ Z) := A.union_distrib_inter_left_ax X Y Z
lemma union_distrib_inter_right {A : fin_bool_alg} (X Y Z : A) : X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z) := 
  by calc X ∪ (Y ∩ Z) = (Y ∩ Z) ∪ X       : union_comm X (Y ∩ Z) 
                  ... = (Y ∪ X) ∩ (Z ∪ X) : union_distrib_inter_left Y Z X  
                  ... = (X ∪ Y) ∩ (X ∪ Z) : by rw [union_comm X Y, union_comm X Z]

lemma inter_distrib_union_left {A : fin_bool_alg} (X Y Z : A) : (X ∪ Y) ∩ Z = (X ∩ Z) ∪ (Y ∩ Z) := A.inter_distrib_union_left_ax X Y Z
lemma inter_distrib_union_right {A : fin_bool_alg} (X Y Z : A) : X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) := 
  by calc X ∩ (Y ∪ Z) = (Y ∪ Z) ∩ X       : inter_comm X (Y ∪ Z) 
      ...             = (Y ∩ X) ∪ (Z ∩ X) : inter_distrib_union_left Y Z X
      ...             = (X ∩ Y) ∪ (X ∩ Z) : by rw [inter_comm X Y, inter_comm X Z]

lemma inter_top_left {A : fin_bool_alg} (X : A) : X ∩ ⊤ = X := A.inter_top_ax X
lemma inter_top_right {A : fin_bool_alg} (X : A) : ⊤ ∩ X = X := eq.trans (inter_comm ⊤ X) (inter_top_left X) 
lemma union_top_left {A : fin_bool_alg} (X : A) : X ∪ ⊤ = ⊤ := A.union_top_ax X
lemma union_top_right {A : fin_bool_alg} (X : A) : ⊤ ∪ X = ⊤ := eq.trans (union_comm ⊤ X) (union_top_left X)

lemma inter_bot_left {A : fin_bool_alg} (X : A) : X ∩ ⊥ = ⊥ := A.inter_bot_ax X
lemma inter_bot_right {A : fin_bool_alg} (X : A) : ⊥ ∩ X = ⊥ := eq.trans (inter_comm ⊥ X) (inter_bot_left X)
lemma union_bot_left {A : fin_bool_alg} (X : A) : X ∪ ⊥ = X := A.union_bot_ax X 
lemma union_bot_right {A : fin_bool_alg} (X : A) : ⊥ ∪ X = X := eq.trans (union_comm ⊥ X) (union_bot_left X)

lemma union_compl {A: fin_bool_alg} (X: A) : X ∪ Xᶜ = ⊤ := A.union_compl_ax X 
lemma inter_compl {A: fin_bool_alg} (X: A) : X ∩ Xᶜ = ⊥ := A.inter_compl_ax X 

lemma absorb_union_inter {A : fin_bool_alg} (X Y : A) : X ∪ (X ∩ Y) = X := A.absorb_union_inter_ax X Y 
lemma absorb_inter_union {A : fin_bool_alg} (X Y : A) : X ∩ (X ∪ Y) = X := A.absorb_inter_union_ax X Y 

lemma size_modular {A : fin_bool_alg} (X Y : A) : size (X ∪ Y) + size (X ∩ Y) = size (X) + size Y := A.size_modular_ax X Y
lemma size_bot (A : fin_bool_alg) : A.size ⊥ = 0 := A.size_bot_ax
lemma size_singleton {A : fin_bool_alg} (X : A) (hX : (∀ (Y : A), Y ⊆ X → Y ≠ X → Y = ⊥)) : size X = 1 := A.size_singleton_ax X hX 
lemma size_nonneg {A : fin_bool_alg} (X : A) : 0 ≤ A.size X := A.size_nonneg_ax X 

lemma inter_subset {A : fin_bool_alg} (X Y: A) : (X ⊆ Y) ↔ (X ∩ Y = X) := sorry 
-- These lemmas now follow from the axioms

lemma union_subset {A: fin_bool_alg} (X Y : A) : (X ⊆ Y) ↔ (X ∪ Y = Y) := 
begin
  split, 
  intros hXY,
  unfold has_subset.subset at hXY,
  calc X ∪ Y = (X ∩ Y) ∪ Y : by rw ← hXY
  ...        = Y ∪ (X ∩ Y) : union_comm _ _
  ...        = Y ∪ (Y ∩ X) : by rw (inter_comm X Y)
  ...        = Y           : absorb_union_inter _ _, 
  
  intros hXY2,
  calc X = X ∩ (X ∪ Y)  : eq.symm (absorb_inter_union X Y)
  ...    = X ∩ Y        : by rw hXY2,
end

lemma ss_antisymm {A : fin_bool_alg} {X Y : A} (hXY : X ⊆ Y) (hYX : Y ⊆ X) : X = Y := 
begin
  unfold has_subset.subset at hXY hYX, 
  calc X = X ∩ Y : hXY ... = Y ∩ X : inter_comm X Y ... = Y : by rw ← hYX, 
end 

lemma union_idem {A : fin_bool_alg} (X : A) : X ∪ X = X := 
  by calc X ∪ X = X ∪ (X ∩ ⊤) : by rw inter_top_left X ... = X : absorb_union_inter X ⊤ 

lemma inter_idem {A : fin_bool_alg} (X : A) : X ∩ X = X := 
  by calc X ∩ X = X ∩ (X ∪ ⊥) : by rw union_bot_left X ... = X : absorb_inter_union X ⊥ 

lemma inter_subset_left {A: fin_bool_alg} (X Y : A) : (X ∩ Y) ⊆ X := 
begin
  apply (union_subset (X ∩ Y) X).mpr, 
  rw union_comm (X ∩ Y) X, 
  apply absorb_union_inter, 
end

lemma inter_subset_right {A : fin_bool_alg} (X Y : A) : (X ∩ Y) ⊆ Y := 
begin
  apply (union_subset (X ∩ Y) Y).mpr,
  rw [union_comm,inter_comm X Y], 
  apply absorb_union_inter,
end

lemma subset_top {A : fin_bool_alg} (X : A) : X ⊆ ⊤ := 
begin
  unfold has_subset.subset, 
  exact eq.symm (inter_top_left X),
end


lemma bot_subset {A : fin_bool_alg} (X : A) : ⊥ ⊆ X := 
begin
  unfold has_subset.subset, 
  exact eq.symm (inter_bot_right X),
end

lemma compl_subset {A : fin_bool_alg} {X Y : A} (hXY : X ⊆ Y) : Yᶜ ⊆ Xᶜ := sorry 

lemma compl_uniq {A : fin_bool_alg} (X Y : A) (hU : X ∪ Y = ⊤) (hI : X ∩ Y = ⊥) : Y = Xᶜ := 
begin
  apply ss_antisymm,
  unfold has_subset.subset, 
  sorry, 
end 


lemma compl_inter {A : fin_bool_alg} (X Y : A) : (X ∩ Y)ᶜ = Xᶜ ∪ Yᶜ := 
begin

  sorry,
end 

lemma compl_union {A : fin_bool_alg} (X Y : A) : (X ∪ Y)ᶜ = Xᶜ ∩ Yᶜ := 
begin
  sorry, 
end

lemma inter_is_lb {A : fin_bool_alg} (X Y Z : A) : Z ⊆ X → Z ⊆ Y → Z ⊆ (X ∩ Y) := 
begin
  unfold has_subset.subset,
  intros hZX hZY, 
  calc Z = Z ∩ Y        : hZY
  ...    = (Z ∩ X) ∩ Y  : by rw ← hZX
  ...    = Z ∩ (X ∩ Y)  : inter_assoc Z X Y, 
end 

lemma union_is_ub {A : fin_bool_alg} (X Y Z : A) : X ⊆ Z → Y ⊆ Z → X ∪ Y ⊆ Z := 
begin
  unfold has_subset.subset, 
  intros hXZ hYZ, 
  calc X ∪ Y = (X ∩ Z) ∪ (Y ∩ Z)    : by rw [←hXZ, ←hYZ]
  ...        = (X ∪ Y) ∩ Z          : by rw (inter_distrib_union_left X Y Z), 
end

lemma subtract_subset {A : fin_bool_alg} (X Y : A) : X - Y ⊆ X := inter_subset_left X Yᶜ

lemma subtract_union {A : fin_bool_alg} (X Y : A): (X ∩ Y) ∪ (Y - X) = Y := 
begin
  unfold has_sub.sub, 
  rw ← inter_comm Y X, 
  rw ← inter_distrib_union_right, 
  rw union_compl, 
  exact inter_top_left Y,
end

lemma subtract_union_subset {A : fin_bool_alg} {X Y : A} (hXY : X ⊆ Y) : X ∪ (Y - X) = Y := 
begin
  unfold has_subset.subset at hXY, 
  have := subtract_union X Y, 
  rw ← hXY at this, 
  exact this, 
end

lemma subtract_inter {A : fin_bool_alg} (X Y : A) : X ∩ (Y - X) = ⊥ := 
begin
  unfold has_sub.sub, 
  rw [←inter_assoc, inter_comm X Y, inter_assoc, inter_compl ,inter_bot_left],
end


lemma size_monotone {A : fin_bool_alg} {X Y: A} (hXY : X ⊆ Y) : A.size X ≤ A.size Y := 
begin
  have := size_modular X (Y-X), 
  rw subtract_union_subset hXY at this, 
  rw subtract_inter at this, 
  linarith [size_bot A, size_nonneg (Y-X)],
end

lemma compl_int_size {A : fin_bool_alg} {X Y : A} (hXY : X ⊆ Y) : size (Xᶜ ∩ Y) = size Y - size X := sorry


def fin_bool_alg.canonical (size : ℤ) :
  (0 ≤ size) → fin_bool_alg := sorry




end API 

/-


  --(inter_subset_right (X Y : subset) : contained (inter X Y) Y)


lemma fin_bool_alg.inter_subset_right {A: fin_bool_alg} (X Y : A) : (X ∩ Y) ⊆ Y := sorry
lemma fin_bool_alg.inter_is_lb {A: fin_bool_alg} (X Y Z : A) : (Z ⊆ X) → (Z ⊆ Y) → ((X ∩ Y) ⊆ Z) := sorry


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

-/

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
          term1 : (min k (size (X ∩ Y))) ≤ (size Y) := le_trans (min_le_right _ _) (size_monotone (A.inter_subset_right X Y)),
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
    := le_antisymm (calc M.rank ⊥ ≤ size (⊥ : M.subset) : M.R1 ⊥ ... = 0 : size_bot M.subset) (M.R0 ⊥)

-- The definition of the dual matroid. R2 is the trickier axiom to prove.
def matroid.dual : matroid → matroid := fun M, {
  subset := M.subset,
  rank := (fun (X : M.subset), M.rank Xᶜ + (size X) - M.rank ⊤),

  R0 := (fun X, calc
    0   ≤ M.rank Xᶜ + M.rank X - M.rank (X ∪ Xᶜ) - M.rank (X ∩ Xᶜ) : by linarith [M.R3 X Xᶜ]
    ... ≤ M.rank Xᶜ + M.rank X - M.rank ⊤        - M.rank ⊥        : by rw [union_compl X, inter_compl X]
    ... ≤ M.rank Xᶜ + (size X)  - M.rank ⊤                         : by linarith [M.R1 X, M.rank_empty]),
  R1 := (fun X, by linarith [M.R2 (subset_top Xᶜ)]),
  R2 := (fun X Y (hXY : X ⊆ Y), let
    h₁ : (Xᶜ ∩ Y) ∩ Yᶜ = ⊥ := calc
      (Xᶜ ∩ Y) ∩ Yᶜ = Xᶜ ∩ (Y ∩ Yᶜ) : inter_assoc Xᶜ Y Yᶜ
      ...           = Xᶜ ∩ ⊥        : by rw [inter_compl Y]
      ...           = ⊥             : inter_bot_left Xᶜ,
    h₂ : (Xᶜ ∪ Yᶜ) = Xᶜ := calc
      (Xᶜ ∪ Yᶜ) = (X ∩ Y)ᶜ : (compl_inter X Y).symm
      ...       = Xᶜ       : by rw [(inter_subset X Y).mp hXY],
    h₃ : (Xᶜ ∩ Y) ∪ Yᶜ = Xᶜ := calc
      (Xᶜ ∩ Y) ∪ Yᶜ = (Xᶜ ∪ Yᶜ) ∩ (Y ∪ Yᶜ) : union_distrib_inter_left Xᶜ Y Yᶜ --Xᶜ.union_distrib_inter_left Y Yᶜ
      ...           = Xᶜ ∩ ⊤               : by rw [h₂, union_compl Y]
      ...           = Xᶜ                   : inter_top_left Xᶜ,
    h₄ : M.rank Xᶜ ≤ size Y - size X + M.rank Yᶜ := calc
      M.rank Xᶜ = M.rank ⊥ + M.rank Xᶜ                            : by linarith [M.rank_empty]
      ...       = M.rank ((Xᶜ ∩ Y) ∩ Yᶜ) + M.rank ((Xᶜ ∩ Y) ∪ Yᶜ) : by rw [h₁, h₃]
      ...       ≤ M.rank (Xᶜ ∩ Y) + M.rank Yᶜ                     : M.R3 _ _
      ...       ≤ size (Xᶜ ∩ Y) + M.rank Yᶜ                       : by linarith [M.R1 (Xᶜ ∩ Y)]
      ...       = size Y - size X + M.rank Yᶜ                     : by rw [compl_int_size hXY]
    in by linarith),
  R3 := (fun X Y, calc
      (M.rank (X ∩ Y)ᶜ  + size (X ∩ Y) - M.rank ⊤) + (M.rank (X ∪ Y)ᶜ  + size (X ∪ Y) - M.rank ⊤)
    = (M.rank (Xᶜ ∪ Yᶜ) + size (X ∩ Y) - M.rank ⊤) + (M.rank (Xᶜ ∩ Yᶜ) + size (X ∪ Y) - M.rank ⊤) : by rw [compl_inter X Y, compl_union X Y]
... ≤ (M.rank Xᶜ        + size X       - M.rank ⊤) + (M.rank Yᶜ        + size Y       - M.rank ⊤) : by linarith [M.R3 Xᶜ Yᶜ, size_modular X Y]),
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
-/

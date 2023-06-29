import Oneshot.Mathlib.Data.Set.Finite
import Oneshot.Mathlib.Data.Set.Basic
import Oneshot.Mathlib.Data.Set.Function
import Oneshot.Mathlib.Data.Set.Ncard
import Mathbin.Order.Minimal
import Oneshot.Mathlib.Order.Minimal
import Mathbin.Data.Set.Ncard
import Mathbin.Tactic.Default

-- import .ssfact 
-- import .ssfact
open scoped Classical

open scoped BigOperators

open Set

variable {α : Type _} {I D J B B' B₁ B₂ X Y : Set α} {e f : α}

section Prelim

/-- A predicate `P` on sets satisfies the exchange property if, for all `X` and `Y` satisfying `P`
  and all `a ∈ X \ Y`, there exists `b ∈ Y \ X` so that swapping `a` for `b` in `X` maintains `P`.-/
def ExchangeProperty (P : Set α → Prop) : Prop :=
  ∀ X Y, P X → P Y → ∀ a ∈ X \ Y, ∃ b ∈ Y \ X, P (insert b (X \ {a}))
#align exchange_property ExchangeProperty

-- def exists_maximal_subset_property (P : set α → Prop) : Prop := 
--   ∀ I X, P I → I ⊆ X → (maximals (⊆) {Y | P Y ∧ I ⊆ Y ∧ Y ⊆ X}).nonempty
/-- A predicate `P` on sets satisfies the maximal subset property if, for all `X` containing some 
  `I` satisfying `P`, there is a maximal subset of `X` satisfying `P`. -/
def ExistsMaximalSubsetProperty (P : Set α → Prop) (X : Set α) : Prop :=
  ∀ I, P I → I ⊆ X → (maximals (· ⊆ ·) {Y | P Y ∧ I ⊆ Y ∧ Y ⊆ X}).Nonempty
#align exists_maximal_subset_property ExistsMaximalSubsetProperty

theorem existsMaximalSubsetProperty_of_bounded {P : Set α → Prop}
    (h : ∃ n, ∀ I, P I → I.Finite ∧ I.ncard ≤ n) (X : Set α) : ExistsMaximalSubsetProperty P X :=
  by
  obtain ⟨n, h⟩ := h
  intro I₀ hI₀ hI₀X
  set S := {I | P I ∧ I₀ ⊆ I ∧ I ⊆ X} with hS
  have : Nonempty S := ⟨⟨I₀, hI₀, subset.rfl, hI₀X⟩⟩
  set f : {I | P I ∧ I₀ ⊆ I ∧ I ⊆ X} → Fin (n + 1) := fun I =>
    ⟨ncard (I : Set α), Nat.lt_succ_of_le (h I I.2.1).2⟩ with hf
  obtain ⟨m, ⟨⟨J, hJ⟩, rfl⟩, hJmax⟩ := Set.Finite.exists_maximal (range f) (range_nonempty _)
  refine' ⟨J, hJ, fun K hK hJK => (eq_of_subset_of_ncard_le hJK _ (h _ hK.1).1).symm.Subset⟩
  exact (hJmax _ ⟨⟨K, hK⟩, rfl⟩ (ncard_le_of_subset hJK (h _ hK.1).1)).symm.le
#align exists_maximal_subset_property_of_bounded existsMaximalSubsetProperty_of_bounded

private theorem antichain_of_exch {base : Set α → Prop} (exch : ExchangeProperty base) (hB : base B)
    (hB' : base B') (h : B ⊆ B') : B = B' :=
  by
  refine' h.antisymm (diff_eq_empty.mp (eq_empty_iff_forall_not_mem.mpr fun x hx => _))
  obtain ⟨e, he, -⟩ := exch _ _ hB' hB _ hx
  exact he.2 (h he.1)

private theorem diff_aux_of_exch {base : Set α → Prop} (exch : ExchangeProperty base)
    (hB₁ : base B₁) (hB₂ : base B₂) (hfin : (B₁ \ B₂).Finite) :
    (B₂ \ B₁).Finite ∧ (B₂ \ B₁).ncard = (B₁ \ B₂).ncard :=
  by
  suffices :
    ∀ {k B B'},
      base B → base B' → (B \ B').Finite → ncard (B \ B') = k → (B' \ B).Finite ∧ (B' \ B).ncard = k
  exact this hB₁ hB₂ hfin rfl
  intro k; induction' k with k IH
  · intro B B' hB hB' hfin h0
    rw [ncard_eq_zero hfin, diff_eq_empty] at h0 
    rw [antichain_of_exch exch hB hB' h0, diff_self]
    simp
  intro B B' hB hB' hfin hcard
  obtain ⟨e, he⟩ := nonempty_of_ncard_ne_zero (by rw [hcard]; simp : (B \ B').ncard ≠ 0)
  obtain ⟨f, hf, hB0⟩ := exch _ _ hB hB' _ he
  have hef : f ≠ e := by rintro rfl; exact hf.2 he.1
  obtain ⟨hfin', hcard'⟩ := IH hB0 hB' _ _
  · rw [insert_diff_singleton_comm hef, diff_diff_right, inter_singleton_eq_empty.mpr he.2,
      union_empty, ← union_singleton, ← diff_diff] at hfin' hcard' 
    have hfin'' := hfin'.insert f
    rw [insert_diff_singleton, insert_eq_of_mem hf] at hfin'' 
    apply_fun fun x => x + 1 at hcard' 
    rw [ncard_diff_singleton_add_one hf hfin'', ← Nat.succ_eq_add_one] at hcard' 
    exact ⟨hfin'', hcard'⟩
  · rw [insert_diff_of_mem _ hf.1, diff_diff_comm]
    exact hfin.diff _
  rw [insert_diff_of_mem _ hf.1, diff_diff_comm, ncard_diff_singleton_of_mem he hfin, hcard,
    Nat.succ_sub_one]

private theorem finite_of_finite_of_exch {base : Set α → Prop} (exch : ExchangeProperty base)
    (hB : base B) (hB' : base B') (h : B.Finite) : B'.Finite :=
  by
  rw [← inter_union_diff B' B]
  exact finite.union (h.subset (inter_subset_right _ _)) (diff_aux_of_exch exch hB hB' (h.diff _)).1

private theorem card_eq_card_of_exchange {base : Set α → Prop} (exch : ExchangeProperty base)
    (hB₁ : base B₁) (hB₂ : base B₂) : B₁.ncard = B₂.ncard :=
  by
  obtain hB₁' | hB₁' := B₁.finite_or_infinite.symm
  · rw [hB₁'.ncard, infinite.ncard fun h => hB₁' (finite_of_finite_of_exch exch hB₂ hB₁ h)]
  have hdcard := (diff_aux_of_exch exch hB₁ hB₂ (hB₁'.diff _)).2
  have hB₂' := finite_of_finite_of_exch exch hB₁ hB₂ hB₁'
  rw [← ncard_inter_add_ncard_diff_eq_ncard B₁ B₂ hB₁', ← hdcard, inter_comm,
    ncard_inter_add_ncard_diff_eq_ncard B₂ B₁ hB₂']

-- an `encard` version
private theorem encard_diff_eq_of_exch {base : Set α → Prop} (exch : ExchangeProperty base)
    (hB₁ : base B₁) (hB₂ : base B₂) : (B₁ \ B₂).encard = (B₂ \ B₁).encard :=
  by
  obtain hf | hi := (B₁ \ B₂).finite_or_infinite
  · obtain ⟨hf', he⟩ := diff_aux_of_exch exch hB₁ hB₂ hf
    rw [hf.encard_eq, hf'.encard_eq, he]
  obtain hf' | hi' := (B₂ \ B₁).finite_or_infinite
  · obtain ⟨h, _⟩ := diff_aux_of_exch exch hB₂ hB₁ hf'
    exact (hi h).elim
  rw [hi.encard_eq, hi'.encard_eq]

private theorem encard_eq_of_exch {base : Set α → Prop} (exch : ExchangeProperty base)
    (hB₁ : base B₁) (hB₂ : base B₂) : B₁.encard = B₂.encard := by
  rw [← encard_diff_add_encard_inter B₁ B₂, encard_diff_eq_of_exch exch hB₁ hB₂, inter_comm,
    encard_diff_add_encard_inter]

end Prelim

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (X «expr ⊆ » ground) -/
/-- A `matroid` is a nonempty collection of sets satisfying the exchange property and the maximal
  subset property. Each such set is called a `base` of the matroid. -/
@[ext]
structure MatroidIn (α : Type _) where
  ground : Set α
  base : Set α → Prop
  exists_base' : ∃ B, base B
  base_exchange' : ExchangeProperty base
  maximality : ∀ (X) (_ : X ⊆ ground), ExistsMaximalSubsetProperty (fun I => ∃ B, base B ∧ I ⊆ B) X
  subset_ground' : ∀ B, base B → B ⊆ ground
#align matroid_in MatroidIn

-- def exists_maximal_subset_property (P : set α → Prop) : Prop := 
--   ∀ I X, P I → I ⊆ X → (maximals (⊆) {Y | P Y ∧ I ⊆ Y ∧ Y ⊆ X}).nonempty 
/- This constructs a matroid using a slight weakening of the `exists_maximal_subset_property` 
  rule, that -/
-- def foo (α : Type*) (ground : set α) (base : set α → Prop) (exists_base' : ∃ B, base B) 
--   (base_exchange' : exchange_property base) 
--   -- (maximality' : ∀ I X, (∃ B, base B ∧ I ⊆ B) → I ⊆ X → X ⊆ ground → 
--   --   (maximals (⊆) {Y | (∃ B, base B ∧ Y ⊆ B) ∧ I ⊆ Y ∧ Y ⊆ X}).nonempty )
--   (maximality' : ∀ X, exists_maximal_subset_property' (λ I, ∃ B, base B ∧ I ⊆ B) X)
--   (subset_ground' : ∀ B, base B → B ⊆ ground) : matroid_in α := 
-- { ground := ground,
--   base := base,
--   exists_base' := exists_base',
--   base_exchange' := base_exchange',
--   maximality := 
--   begin 
--     rintro I X ⟨B, hB, hIB⟩ hIX, 
--     obtain ⟨J, hJ⟩ := maximality' I (X ∩ ground) ⟨B, hB, hIB⟩ 
--       (subset_inter hIX (hIB.trans (subset_ground' B hB))) (inter_subset_right _ _), 
--     use J, 
--     simp only [mem_maximals_set_of_iff', not_and, forall_exists_index, and_imp] at *, 
--     obtain ⟨⟨⟨B, hB, hJB⟩, hIJ, hJX⟩, h⟩ := hJ, 
--     rw subset_inter_iff at hJX, 
--     refine ⟨⟨⟨B, hB, hJB⟩,hIJ,hJX.1⟩,λ K hK B' hB' hKB' hIK hKX, h hK B' hB' hKB' hIK _⟩, 
--     exact subset_inter hKX (hKB'.trans (subset_ground' B' hB')), 
--   end,
--   subset_ground' := subset_ground' } 
-- instance {E : Type*} [finite E] : finite (matroid_in α) :=
-- finite.of_injective (λ M, M.base) (λ M₁ M₂ h, (by { ext, dsimp only at h, rw h }))
-- instance {E : Type*} : nonempty (matroid_in α) :=
--   ⟨⟨@eq _ ∅, ⟨_,rfl⟩, by { rintro _ _ rfl rfl a h, exfalso, exact not_mem_empty a h.1 }, 
--     exists_maximal_subset_property_of_bounded 
--     ⟨0, by { rintro I ⟨B, rfl, hIB⟩, rw subset_empty_iff.mp hIB, simp }⟩⟩⟩
namespace MatroidIn

def e (M : MatroidIn α) : Set α :=
  M.ground
#align matroid_in.E MatroidIn.e

@[simp]
theorem ground_eq_e (M : MatroidIn α) : M.ground = M.e :=
  rfl
#align matroid_in.ground_eq_E MatroidIn.ground_eq_e

section Tac

@[user_attribute]
unsafe def ssE_rules : user_attribute
    where
  Name := `ssE_rules
  descr := "lemmas usable to prove subset of ground set"
#align matroid_in.ssE_rules matroid_in.ssE_rules

@[user_attribute]
unsafe def ssE_finish_rules : user_attribute
    where
  Name := `ssE_finish_rules
  descr := "finishing lemmas usable to prove subset of ground set"
#align matroid_in.ssE_finish_rules matroid_in.ssE_finish_rules

/- ./././Mathport/Syntax/Translate/Expr.lean:336:4: warning: unsupported (TODO): `[tacs] -/
unsafe def ssE_finish : tactic Unit :=
  sorry
#align matroid_in.ssE_finish matroid_in.ssE_finish

/- ./././Mathport/Syntax/Translate/Expr.lean:336:4: warning: unsupported (TODO): `[tacs] -/
unsafe def ssE : tactic Unit :=
  sorry
#align matroid_in.ssE matroid_in.ssE

-- @[ssE_rules] private lemma empty_subset_ground {M : matroid_in α} : ∅ ⊆ M.E := empty_subset _
-- @[ssE_rules] private lemma ground_subset_ground {M : matroid_in α} : M.E ⊆ M.E := subset.rfl
-- @[ssE_rules] private lemma union_subset_ground {M : matroid_in α} {X Y : set α} 
--   (hX : X ⊆ M.E) (hY : Y ⊆ M.E) : X ∪ Y ⊆ M.E := union_subset hX hY
@[ssE_rules]
private theorem inter_right_subset_ground {X Y : Set α} {M : MatroidIn α} (hX : X ⊆ M.e) :
    X ∩ Y ⊆ M.e :=
  (inter_subset_left _ _).trans hX

@[ssE_rules]
private theorem inter_left_subset_ground {X Y : Set α} {M : MatroidIn α} (hX : X ⊆ M.e) :
    Y ∩ X ⊆ M.e :=
  (inter_subset_right _ _).trans hX

@[ssE_rules]
private theorem diff_subset_ground {X Y : Set α} {M : MatroidIn α} (hX : X ⊆ M.e) : X \ Y ⊆ M.e :=
  (diff_subset _ _).trans hX

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
-- @[ssE_rules] private lemma ground_diff_subset_ground {X : set α} {M : matroid_in α} : 
--   M.E \ X ⊆ M.E := diff_subset_ground subset.rfl
@[simp]
theorem ground_inter_right {M : MatroidIn α}
    (hXE : X ⊆ M.e := by
      run_tac
        ssE) :
    M.e ∩ X = X :=
  inter_eq_self_of_subset_right hXE
#align matroid_in.ground_inter_right MatroidIn.ground_inter_right

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
@[simp]
theorem ground_inter_left {M : MatroidIn α}
    (hXE : X ⊆ M.e := by
      run_tac
        ssE) :
    X ∩ M.e = X :=
  inter_eq_self_of_subset_left hXE
#align matroid_in.ground_inter_left MatroidIn.ground_inter_left

@[ssE_rules]
private theorem insert_subset_ground {e : α} {X : Set α} {M : MatroidIn α} (he : e ∈ M.e)
    (hX : X ⊆ M.e) : insert e X ⊆ M.e :=
  insert_subset_iff.mpr ⟨he, hX⟩

@[ssE_rules]
private theorem singleton_subset_ground {e : α} {M : MatroidIn α} (he : e ∈ M.e) : {e} ⊆ M.e :=
  singleton_subset_iff.mpr he

attribute [ssE_rules] mem_of_mem_of_subset empty_subset subset.rfl union_subset

end Tac

section Defs

/-- A set is independent if it is contained in a base.  -/
def Indep (M : MatroidIn α) (I : Set α) : Prop :=
  ∃ B, M.base B ∧ I ⊆ B
#align matroid_in.indep MatroidIn.Indep

/-- A subset of `M.E` is dependent if it is not independent . -/
def Dep (M : MatroidIn α) (D : Set α) : Prop :=
  ¬M.indep D ∧ D ⊆ M.e
#align matroid_in.dep MatroidIn.Dep

/-- A basis for a set `X ⊆ M.E` is a maximal independent subset of `X`
  (Often in the literature, the word 'basis' is used to refer to what we call a 'base'). -/
def Basis (M : MatroidIn α) (I X : Set α) : Prop :=
  I ∈ maximals (· ⊆ ·) {A | M.indep A ∧ A ⊆ X} ∧ X ⊆ M.e
#align matroid_in.basis MatroidIn.Basis

/-- A circuit is a minimal dependent set -/
def Circuit (M : MatroidIn α) (C : Set α) : Prop :=
  C ∈ minimals (· ⊆ ·) {X | M.Dep X}
#align matroid_in.circuit MatroidIn.Circuit

/-- A coindependent set is a subset of `M.E` that is disjoint from some base -/
def Coindep (M : MatroidIn α) (I : Set α) : Prop :=
  I ⊆ M.e ∧ ∃ B, M.base B ∧ Disjoint I B
#align matroid_in.coindep MatroidIn.Coindep

section Properties

/-- Typeclass for a matroid having finite ground set. This is just a wrapper for `[M.E.finite]`-/
class Finite (M : MatroidIn α) : Prop where
  ground_finite : M.e.Finite
#align matroid_in.finite MatroidIn.Finite

theorem ground_finite (M : MatroidIn α) [M.Finite] : M.e.Finite :=
  ‹M.Finite›.ground_finite
#align matroid_in.ground_finite MatroidIn.ground_finite

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem set_finite (M : MatroidIn α) [M.Finite] (X : Set α)
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    X.Finite :=
  M.ground_finite.Subset hX
#align matroid_in.set_finite MatroidIn.set_finite

instance finite_of_finite [@Finite α] {M : MatroidIn α} : Finite M :=
  ⟨Set.toFinite _⟩
#align matroid_in.finite_of_finite MatroidIn.finite_of_finite

class FiniteRk (M : MatroidIn α) : Prop where
  exists_finite_base : ∃ B, M.base B ∧ B.Finite
#align matroid_in.finite_rk MatroidIn.FiniteRk

-- instance finite_rk_of_finite (M : matroid_in α) [finite M] : finite_rk M := 
-- ⟨M.exists_base'.imp (λ B hB, ⟨hB, M.set_finite B (M.subset_ground' _ hB)⟩) ⟩
class InfiniteRk (M : MatroidIn α) : Prop where
  exists_infinite_base : ∃ B, M.base B ∧ B.Infinite
#align matroid_in.infinite_rk MatroidIn.InfiniteRk

class Finitary (M : MatroidIn α) : Prop where
  cct_finite : ∀ C : Set α, M.Circuit C → C.Finite
#align matroid_in.finitary MatroidIn.Finitary

class RkPos (M : MatroidIn α) : Prop where
  empty_not_base : ¬M.base ∅
#align matroid_in.rk_pos MatroidIn.RkPos

class DualRkPos (M : MatroidIn α) : Prop where
  univ_not_base : ¬M.base univ
#align matroid_in.dual_rk_pos MatroidIn.DualRkPos

end Properties

end Defs

variable {M : MatroidIn α}

section Base

@[ssE_finish_rules]
theorem Base.subset_ground (hB : M.base B) : B ⊆ M.e :=
  M.subset_ground' B hB
#align matroid_in.base.subset_ground MatroidIn.Base.subset_ground

theorem exists_base (M : MatroidIn α) : ∃ B, M.base B :=
  M.exists_base'
#align matroid_in.exists_base MatroidIn.exists_base

theorem Base.exchange (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hx : e ∈ B₁ \ B₂) :
    ∃ y ∈ B₂ \ B₁, M.base (insert y (B₁ \ {e})) :=
  M.base_exchange' B₁ B₂ hB₁ hB₂ _ hx
#align matroid_in.base.exchange MatroidIn.Base.exchange

theorem Base.exchange_mem (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hxB₁ : e ∈ B₁) (hxB₂ : e ∉ B₂) :
    ∃ y, (y ∈ B₂ ∧ y ∉ B₁) ∧ M.base (insert y (B₁ \ {e})) := by
  simpa using hB₁.exchange hB₂ ⟨hxB₁, hxB₂⟩
#align matroid_in.base.exchange_mem MatroidIn.Base.exchange_mem

theorem Base.eq_of_subset_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hB₁B₂ : B₁ ⊆ B₂) : B₁ = B₂ :=
  antichain_of_exch M.base_exchange' hB₁ hB₂ hB₁B₂
#align matroid_in.base.eq_of_subset_base MatroidIn.Base.eq_of_subset_base

theorem Base.finite_of_finite (hB : M.base B) (h : B.Finite) (hB' : M.base B') : B'.Finite :=
  finite_of_finite_of_exch M.base_exchange' hB hB' h
#align matroid_in.base.finite_of_finite MatroidIn.Base.finite_of_finite

theorem Base.infinite_of_infinite (hB : M.base B) (h : B.Infinite) (hB₁ : M.base B₁) :
    B₁.Infinite :=
  by_contra fun hB_inf => (hB₁.finite_of_finite (not_infinite.mp hB_inf) hB).not_infinite h
#align matroid_in.base.infinite_of_infinite MatroidIn.Base.infinite_of_infinite

theorem Base.finite [FiniteRk M] (hB : M.base B) : B.Finite :=
  let ⟨B₀, hB₀⟩ := ‹FiniteRk M›.exists_finite_base
  hB₀.1.finite_of_finite hB₀.2 hB
#align matroid_in.base.finite MatroidIn.Base.finite

theorem Base.infinite [InfiniteRk M] (hB : M.base B) : B.Infinite :=
  let ⟨B₀, hB₀⟩ := ‹InfiniteRk M›.exists_infinite_base
  hB₀.1.infinite_of_infinite hB₀.2 hB
#align matroid_in.base.infinite MatroidIn.Base.infinite

theorem Base.finiteRk_of_finite (hB : M.base B) (hfin : B.Finite) : FiniteRk M :=
  ⟨⟨B, hB, hfin⟩⟩
#align matroid_in.base.finite_rk_of_finite MatroidIn.Base.finiteRk_of_finite

theorem Base.infiniteRk_of_infinite (hB : M.base B) (h : B.Infinite) : InfiniteRk M :=
  ⟨⟨B, hB, h⟩⟩
#align matroid_in.base.infinite_rk_of_infinite MatroidIn.Base.infiniteRk_of_infinite

theorem not_finiteRk (M : MatroidIn α) [InfiniteRk M] : ¬FiniteRk M := by intro h;
  obtain ⟨B, hB⟩ := M.exists_base; exact hB.infinite hB.finite
#align matroid_in.not_finite_rk MatroidIn.not_finiteRk

theorem not_infiniteRk (M : MatroidIn α) [FiniteRk M] : ¬InfiniteRk M := by intro h;
  obtain ⟨B, hB⟩ := M.exists_base; exact hB.infinite hB.finite
#align matroid_in.not_infinite_rk MatroidIn.not_infiniteRk

theorem Base.encard_diff_comm (hB₁ : M.base B₁) (hB₂ : M.base B₂) :
    (B₁ \ B₂).encard = (B₂ \ B₁).encard :=
  encard_diff_eq_of_exch M.base_exchange' hB₁ hB₂
#align matroid_in.base.encard_diff_comm MatroidIn.Base.encard_diff_comm

theorem Base.card_diff_comm (hB₁ : M.base B₁) (hB₂ : M.base B₂) :
    (B₁ \ B₂).ncard = (B₂ \ B₁).ncard := by
  rw [← encard_to_nat_eq, hB₁.encard_diff_comm hB₂, encard_to_nat_eq]
#align matroid_in.base.card_diff_comm MatroidIn.Base.card_diff_comm

theorem Base.encard_eq_encard_of_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) : B₁.encard = B₂.encard :=
  by rw [encard_eq_of_exch M.base_exchange' hB₁ hB₂]
#align matroid_in.base.encard_eq_encard_of_base MatroidIn.Base.encard_eq_encard_of_base

theorem Base.card_eq_card_of_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) : B₁.ncard = B₂.ncard := by
  rw [← encard_to_nat_eq B₁, hB₁.encard_eq_encard_of_base hB₂, encard_to_nat_eq]
#align matroid_in.base.card_eq_card_of_base MatroidIn.Base.card_eq_card_of_base

theorem finite_or_infiniteRk (M : MatroidIn α) : FiniteRk M ∨ InfiniteRk M :=
  let ⟨B, hB⟩ := M.exists_base
  B.finite_or_infinite.elim (Or.inl ∘ hB.finiteRk_of_finite) (Or.inr ∘ hB.infiniteRk_of_infinite)
#align matroid_in.finite_or_infinite_rk MatroidIn.finite_or_infiniteRk

instance finiteRk_of_finite {M : MatroidIn α} [Finite M] : FiniteRk M :=
  let ⟨B, hB⟩ := M.exists_base
  ⟨⟨B, hB, M.ground_finite.Subset hB.subset_ground⟩⟩
#align matroid_in.finite_rk_of_finite MatroidIn.finiteRk_of_finite

instance finitary_of_finiteRk {M : MatroidIn α} [FiniteRk M] : Finitary M :=
  ⟨by
    intro C hC
    obtain rfl | ⟨e, heC⟩ := C.eq_empty_or_nonempty; exact finite_empty
    have hi : M.indep (C \ {e}) :=
      by_contra fun h => (hC.2 ⟨h, (diff_subset _ _).trans hC.1.2⟩ (diff_subset C {e}) heC).2 rfl
    obtain ⟨B, hB, hCB⟩ := hi
    convert (hB.finite.subset hCB).insert e
    rw [insert_diff_singleton, insert_eq_of_mem heC]⟩
#align matroid_in.finitary_of_finite_rk MatroidIn.finitary_of_finiteRk

theorem Base.diff_finite_comm (hB₁ : M.base B₁) (hB₂ : M.base B₂) :
    (B₁ \ B₂).Finite ↔ (B₂ \ B₁).Finite :=
  ⟨fun h => (diff_aux_of_exch M.base_exchange' hB₁ hB₂ h).1, fun h =>
    (diff_aux_of_exch M.base_exchange' hB₂ hB₁ h).1⟩
#align matroid_in.base.diff_finite_comm MatroidIn.Base.diff_finite_comm

theorem Base.diff_infinite_comm (hB₁ : M.base B₁) (hB₂ : M.base B₂) :
    (B₁ \ B₂).Infinite ↔ (B₂ \ B₁).Infinite :=
  not_iff_not.mpr (hB₁.diff_finite_comm hB₂)
#align matroid_in.base.diff_infinite_comm MatroidIn.Base.diff_infinite_comm

end Base

section DepIndep

theorem indep_iff_subset_base : M.indep I ↔ ∃ B, M.base B ∧ I ⊆ B :=
  Iff.rfl
#align matroid_in.indep_iff_subset_base MatroidIn.indep_iff_subset_base

theorem dep_iff : M.Dep D ↔ ¬M.indep D ∧ D ⊆ M.e :=
  Iff.rfl
#align matroid_in.dep_iff MatroidIn.dep_iff

@[ssE_finish_rules]
theorem Indep.subset_ground (hI : M.indep I) : I ⊆ M.e := by obtain ⟨B, hB, hIB⟩ := hI;
  exact hIB.trans hB.subset_ground
#align matroid_in.indep.subset_ground MatroidIn.Indep.subset_ground

@[ssE_finish_rules]
theorem Dep.subset_ground (hD : M.Dep D) : D ⊆ M.e :=
  hD.2
#align matroid_in.dep.subset_ground MatroidIn.Dep.subset_ground

@[ssE_finish_rules]
theorem Coindep.subset_ground (hX : M.Coindep X) : X ⊆ M.e :=
  hX.1
#align matroid_in.coindep.subset_ground MatroidIn.Coindep.subset_ground

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem indep_or_dep
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.indep X ∨ M.Dep X := by rw [dep, and_iff_left hX]; apply em
#align matroid_in.indep_or_dep MatroidIn.indep_or_dep

theorem Indep.not_dep (hI : M.indep I) : ¬M.Dep I := fun h => h.1 hI
#align matroid_in.indep.not_dep MatroidIn.Indep.not_dep

theorem Dep.not_indep (hD : M.Dep D) : ¬M.indep D :=
  hD.1
#align matroid_in.dep.not_indep MatroidIn.Dep.not_indep

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem dep_of_not_indep (hD : ¬M.indep D)
    (hDE : D ⊆ M.e := by
      run_tac
        ssE) :
    M.Dep D :=
  ⟨hD, hDE⟩
#align matroid_in.dep_of_not_indep MatroidIn.dep_of_not_indep

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem indep_of_not_dep (hI : ¬M.Dep I)
    (hIE : I ⊆ M.e := by
      run_tac
        ssE) :
    M.indep I :=
  by_contra fun h => hI ⟨h, hIE⟩
#align matroid_in.indep_of_not_dep MatroidIn.indep_of_not_dep

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
@[simp]
theorem not_dep_iff
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    ¬M.Dep X ↔ M.indep X := by rw [dep, and_iff_left hX, Classical.not_not]
#align matroid_in.not_dep_iff MatroidIn.not_dep_iff

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
@[simp]
theorem not_indep_iff
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    ¬M.indep X ↔ M.Dep X := by rw [dep, and_iff_left hX]
#align matroid_in.not_indep_iff MatroidIn.not_indep_iff

theorem Indep.exists_base_supset (hI : M.indep I) : ∃ B, M.base B ∧ I ⊆ B :=
  hI
#align matroid_in.indep.exists_base_supset MatroidIn.Indep.exists_base_supset

theorem Indep.subset (hJ : M.indep J) (hIJ : I ⊆ J) : M.indep I := by obtain ⟨B, hB, hJB⟩ := hJ;
  exact ⟨B, hB, hIJ.trans hJB⟩
#align matroid_in.indep.subset MatroidIn.Indep.subset

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Dep.supset (hD : M.Dep D) (hDX : D ⊆ X)
    (hXE : X ⊆ M.e := by
      run_tac
        ssE) :
    M.Dep X :=
  dep_of_not_indep fun hI => (hI.Subset hDX).not_dep hD
#align matroid_in.dep.supset MatroidIn.Dep.supset

@[simp]
theorem empty_indep (M : MatroidIn α) : M.indep ∅ :=
  Exists.elim M.exists_base fun B hB => ⟨_, hB, B.empty_subset⟩
#align matroid_in.empty_indep MatroidIn.empty_indep

theorem Indep.finite [FiniteRk M] (hI : M.indep I) : I.Finite :=
  let ⟨B, hB, hIB⟩ := hI
  hB.Finite.Subset hIB
#align matroid_in.indep.finite MatroidIn.Indep.finite

theorem Indep.inter_right (hI : M.indep I) (X : Set α) : M.indep (I ∩ X) :=
  hI.Subset (inter_subset_left _ _)
#align matroid_in.indep.inter_right MatroidIn.Indep.inter_right

theorem Indep.inter_left (hI : M.indep I) (X : Set α) : M.indep (X ∩ I) :=
  hI.Subset (inter_subset_right _ _)
#align matroid_in.indep.inter_left MatroidIn.Indep.inter_left

theorem Indep.diff (hI : M.indep I) (X : Set α) : M.indep (I \ X) :=
  hI.Subset (diff_subset _ _)
#align matroid_in.indep.diff MatroidIn.Indep.diff

theorem Base.indep (hB : M.base B) : M.indep B :=
  ⟨B, hB, subset_rfl⟩
#align matroid_in.base.indep MatroidIn.Base.indep

theorem Base.eq_of_subset_indep (hB : M.base B) (hI : M.indep I) (hBI : B ⊆ I) : B = I :=
  let ⟨B', hB', hB'I⟩ := hI
  hBI.antisymm (by rwa [hB.eq_of_subset_base hB' (hBI.trans hB'I)])
#align matroid_in.base.eq_of_subset_indep MatroidIn.Base.eq_of_subset_indep

theorem base_iff_maximal_indep : M.base B ↔ M.indep B ∧ ∀ I, M.indep I → B ⊆ I → B = I :=
  by
  refine' ⟨fun h => ⟨h.indep, fun _ => h.eq_of_subset_indep⟩, fun h => _⟩
  obtain ⟨⟨B', hB', hBB'⟩, h⟩ := h
  rwa [h _ hB'.indep hBB']
#align matroid_in.base_iff_maximal_indep MatroidIn.base_iff_maximal_indep

theorem base_iff_mem_maximals : M.base B ↔ B ∈ maximals (· ⊆ ·) {I | M.indep I} :=
  by
  rw [base_iff_maximal_indep, maximals]
  exact
    ⟨fun h => ⟨h.1, fun I hI hBI => (h.2 I hI hBI).symm.Subset⟩, fun h =>
      ⟨h.1, fun I hI hBI => hBI.antisymm (h.2 hI hBI)⟩⟩
#align matroid_in.base_iff_mem_maximals MatroidIn.base_iff_mem_maximals

theorem Indep.base_of_maximal (hI : M.indep I) (h : ∀ J, M.indep J → I ⊆ J → I = J) : M.base I :=
  base_iff_maximal_indep.mpr ⟨hI, h⟩
#align matroid_in.indep.base_of_maximal MatroidIn.Indep.base_of_maximal

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Base.dep_of_sSubset (hB : M.base B) (h : B ⊂ X)
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.Dep X :=
  ⟨fun hX => h.Ne (hB.eq_of_subset_indep hX h.Subset), hX⟩
#align matroid_in.base.dep_of_ssubset MatroidIn.Base.dep_of_sSubset

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Base.dep_of_insert (hB : M.base B) (heB : e ∉ B)
    (he : e ∈ M.e := by
      run_tac
        ssE) :
    M.Dep (insert e B) :=
  hB.dep_of_sSubset (ssubset_insert heB)
#align matroid_in.base.dep_of_insert MatroidIn.Base.dep_of_insert

theorem Base.exchange_base_of_indep (hB : M.base B) (he : e ∈ B) (hf : f ∉ B)
    (hI : M.indep (insert f (B \ {e}))) : M.base (insert f (B \ {e})) :=
  by
  obtain ⟨B', hB', hIB'⟩ := hI
  have hBeB' := (subset_insert _ _).trans hIB'
  have heB' : e ∉ B' := by
    intro heB'
    have hBB' : B ⊆ B' :=
      by
      refine' subset_trans _ (insert_subset.mpr ⟨heB', hIB'⟩)
      rw [insert_comm, insert_diff_singleton]
      refine' (subset_insert _ _).trans (subset_insert _ _)
    rw [← hB.eq_of_subset_indep hB'.indep hBB'] at hIB' 
    exact hf (hIB' (mem_insert _ _))
  obtain ⟨y, hy, hy'⟩ := hB.exchange hB' ⟨he, heB'⟩
  rw [← hy'.eq_of_subset_base hB' (insert_subset.mpr ⟨hy.1, hBeB'⟩)] at hIB' 
  have : f = y :=
    (mem_insert_iff.mp (hIB' (mem_insert _ _))).elim id fun h' => (hf (diff_subset _ _ h')).elim
  rwa [this]
#align matroid_in.base.exchange_base_of_indep MatroidIn.Base.exchange_base_of_indep

theorem Base.exchange_base_of_indep' (hB : M.base B) (he : e ∈ B) (hf : f ∉ B)
    (hI : M.indep (insert f B \ {e})) : M.base (insert f B \ {e}) :=
  by
  have hfe : f ≠ e := by rintro rfl; exact hf he
  rw [← insert_diff_singleton_comm hfe] at *
  exact hB.exchange_base_of_indep he hf hI
#align matroid_in.base.exchange_base_of_indep' MatroidIn.Base.exchange_base_of_indep'

/-- If the difference of two bases is a singleton, then they differ by an insertion/removal -/
theorem Base.eq_exchange_of_diff_eq_singleton (hB : M.base B) (hB' : M.base B') (h : B \ B' = {e}) :
    ∃ f ∈ B' \ B, B' = insert f B \ {e} :=
  by
  obtain ⟨f, hf, hb⟩ := hB.exchange hB' (h.symm.subset (mem_singleton e))
  have hne : f ≠ e := by rintro rfl; exact hf.2 (h.symm.subset (mem_singleton f)).1
  rw [insert_diff_singleton_comm hne] at hb 
  refine' ⟨f, hf, (hb.eq_of_subset_base hB' _).symm⟩
  rw [diff_subset_iff, insert_subset, union_comm, ← diff_subset_iff, h, and_iff_left subset.rfl]
  exact Or.inl hf.1
#align matroid_in.base.eq_exchange_of_diff_eq_singleton MatroidIn.Base.eq_exchange_of_diff_eq_singleton

theorem Basis.indep (hI : M.Basis I X) : M.indep I :=
  hI.1.1.1
#align matroid_in.basis.indep MatroidIn.Basis.indep

theorem Basis.subset (hI : M.Basis I X) : I ⊆ X :=
  hI.1.1.2
#align matroid_in.basis.subset MatroidIn.Basis.subset

@[ssE_finish_rules]
theorem Basis.subset_ground (hI : M.Basis I X) : X ⊆ M.e :=
  hI.2
#align matroid_in.basis.subset_ground MatroidIn.Basis.subset_ground

theorem Basis.basis_inter_ground (hI : M.Basis I X) : M.Basis I (X ∩ M.e) := by convert hI;
  rw [inter_eq_self_of_subset_left hI.subset_ground]
#align matroid_in.basis.basis_inter_ground MatroidIn.Basis.basis_inter_ground

@[ssE_finish_rules]
theorem Basis.subset_ground_left (hI : M.Basis I X) : I ⊆ M.e :=
  hI.indep.subset_ground
#align matroid_in.basis.subset_ground_left MatroidIn.Basis.subset_ground_left

theorem Basis.eq_of_subset_indep (hI : M.Basis I X) (hJ : M.indep J) (hIJ : I ⊆ J) (hJX : J ⊆ X) :
    I = J :=
  hIJ.antisymm (hI.1.2 ⟨hJ, hJX⟩ hIJ)
#align matroid_in.basis.eq_of_subset_indep MatroidIn.Basis.eq_of_subset_indep

theorem Basis.finite (hI : M.Basis I X) [FiniteRk M] : I.Finite :=
  hI.indep.Finite
#align matroid_in.basis.finite MatroidIn.Basis.finite

theorem basis_iff' :
    M.Basis I X ↔ (M.indep I ∧ I ⊆ X ∧ ∀ J, M.indep J → I ⊆ J → J ⊆ X → I = J) ∧ X ⊆ M.e :=
  by
  simp_rw [Basis, and_congr_left_iff, maximals, mem_set_of_eq, and_imp, sep_set_of, mem_set_of_eq,
    and_assoc', and_congr_right_iff]
  intro hXE hI hIX
  exact
    ⟨fun h J hJ hIJ hJX => hIJ.antisymm (h hJ hJX hIJ), fun h J hJ hIJ hJX =>
      (h J hJ hJX hIJ).symm.Subset⟩
#align matroid_in.basis_iff' MatroidIn.basis_iff'

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem basis_iff
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.Basis I X ↔ M.indep I ∧ I ⊆ X ∧ ∀ J, M.indep J → I ⊆ J → J ⊆ X → I = J := by
  rw [basis_iff', and_iff_left hX]
#align matroid_in.basis_iff MatroidIn.basis_iff

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem basis_iff_mem_maximals
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.Basis I X ↔ I ∈ maximals (· ⊆ ·) fun I : Set α => M.indep I ∧ I ⊆ X :=
  by
  simp_rw [basis_iff, mem_maximals_prop_iff, and_assoc', and_imp, and_congr_right_iff]
  exact fun hI hIX => ⟨fun h J hJ hJX hIJ => h J hJ hIJ hJX, fun h J hJ hJX hIJ => h hJ hIJ hJX⟩
#align matroid_in.basis_iff_mem_maximals MatroidIn.basis_iff_mem_maximals

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic matroid_in.ssE -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Indep.basis_of_maximal_subset (hI : M.indep I) (hIX : I ⊆ X)
    (hmax : ∀ ⦃J⦄, M.indep J → I ⊆ J → J ⊆ X → J ⊆ I)
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.Basis I X :=
  by
  rw [basis_iff
      (by
        run_tac
          ssE :
        X ⊆ M.E),
    and_iff_right hI, and_iff_right hIX]
  exact fun J hJ hIJ hJX => hIJ.antisymm (hmax hJ hIJ hJX)
#align matroid_in.indep.basis_of_maximal_subset MatroidIn.Indep.basis_of_maximal_subset

theorem Basis.basis_subset (hI : M.Basis I X) (hIY : I ⊆ Y) (hYX : Y ⊆ X) : M.Basis I Y :=
  by
  rw [basis_iff (hYX.trans hI.subset_ground), and_iff_right hI.indep, and_iff_right hIY]
  exact fun J hJ hIJ hJY => hI.eq_of_subset_indep hJ hIJ (hJY.trans hYX)
#align matroid_in.basis.basis_subset MatroidIn.Basis.basis_subset

@[simp]
theorem basis_empty_iff (M : MatroidIn α) : M.Basis I ∅ ↔ I = ∅ :=
  by
  refine' ⟨fun h => subset_empty_iff.mp h.Subset, _⟩
  rintro rfl
  rw [basis_iff, and_iff_right M.empty_indep, and_iff_right (empty_subset _)]
  exact fun _ _ => subset_antisymm
#align matroid_in.basis_empty_iff MatroidIn.basis_empty_iff

theorem Basis.dep_of_sSubset (hI : M.Basis I X) {Y : Set α} (hIY : I ⊂ Y) (hYX : Y ⊆ X) : M.Dep Y :=
  by
  rw [← not_indep_iff (hYX.trans hI.subset_ground)]
  exact fun hY => hIY.ne (hI.eq_of_subset_indep hY hIY.subset hYX)
#align matroid_in.basis.dep_of_ssubset MatroidIn.Basis.dep_of_sSubset

theorem Basis.insert_dep (hI : M.Basis I X) (he : e ∈ X \ I) : M.Dep (insert e I) :=
  hI.dep_of_sSubset (ssubset_insert he.2) (insert_subset_iff.mpr ⟨he.1, hI.Subset⟩)
#align matroid_in.basis.insert_dep MatroidIn.Basis.insert_dep

theorem Basis.mem_of_insert_indep (hI : M.Basis I X) (he : e ∈ X) (hIe : M.indep (insert e I)) :
    e ∈ I :=
  by_contra fun heI => (hI.insert_dep ⟨he, heI⟩).not_indep hIe
#align matroid_in.basis.mem_of_insert_indep MatroidIn.Basis.mem_of_insert_indep

theorem Basis.not_basis_of_sSubset (hI : M.Basis I X) (hJI : J ⊂ I) : ¬M.Basis J X := fun h =>
  hJI.Ne (h.eq_of_subset_indep hI.indep hJI.Subset hI.Subset)
#align matroid_in.basis.not_basis_of_ssubset MatroidIn.Basis.not_basis_of_sSubset

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Indep.subset_basis_of_subset (hI : M.indep I) (hIX : I ⊆ X)
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    ∃ J, M.Basis J X ∧ I ⊆ J :=
  by
  obtain ⟨J, ⟨hJ : M.indep J, hIJ, hJX⟩, hJmax⟩ := M.maximality X hX I hI hIX
  use J
  rw [and_iff_left hIJ, basis_iff, and_iff_right hJ, and_iff_right hJX]
  exact fun K hK hJK hKX => hJK.antisymm (hJmax ⟨hK, hIJ.trans hJK, hKX⟩ hJK)
#align matroid_in.indep.subset_basis_of_subset MatroidIn.Indep.subset_basis_of_subset

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem exists_basis (M : MatroidIn α) (X : Set α)
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    ∃ I, M.Basis I X :=
  let ⟨I, hI, _⟩ := M.empty_indep.subset_basis_of_subset (empty_subset X)
  ⟨_, hI⟩
#align matroid_in.exists_basis MatroidIn.exists_basis

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem exists_basis_subset_basis (M : MatroidIn α) (hXY : X ⊆ Y)
    (hY : Y ⊆ M.e := by
      run_tac
        ssE) :
    ∃ I J, M.Basis I X ∧ M.Basis J Y ∧ I ⊆ J :=
  by
  obtain ⟨I, hI⟩ := M.exists_basis X (hXY.trans hY)
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis_of_subset (hI.subset.trans hXY)
  exact ⟨_, _, hI, hJ, hIJ⟩
#align matroid_in.exists_basis_subset_basis MatroidIn.exists_basis_subset_basis

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Basis.exists_basis_inter_eq_of_supset (hI : M.Basis I X) (hXY : X ⊆ Y)
    (hY : Y ⊆ M.e := by
      run_tac
        ssE) :
    ∃ J, M.Basis J Y ∧ J ∩ X = I :=
  by
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis_of_subset (hI.subset.trans hXY)
  refine' ⟨J, hJ, subset_antisymm _ (subset_inter hIJ hI.subset)⟩
  exact fun e he => hI.mem_of_insert_indep he.2 (hJ.indep.subset (insert_subset.mpr ⟨he.1, hIJ⟩))
#align matroid_in.basis.exists_basis_inter_eq_of_supset MatroidIn.Basis.exists_basis_inter_eq_of_supset

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem exists_basis_union_inter_basis (M : MatroidIn α) (X Y : Set α)
    (hX : X ⊆ M.e := by
      run_tac
        ssE)
    (hY : Y ⊆ M.e := by
      run_tac
        ssE) :
    ∃ I, M.Basis I (X ∪ Y) ∧ M.Basis (I ∩ Y) Y :=
  by
  obtain ⟨J, hJ⟩ := M.exists_basis Y
  exact
    (hJ.exists_basis_inter_eq_of_supset (subset_union_right X Y)).imp fun I hI =>
      ⟨hI.1, by rwa [hI.2]⟩
#align matroid_in.exists_basis_union_inter_basis MatroidIn.exists_basis_union_inter_basis

theorem Indep.eq_of_basis (hI : M.indep I) (hJ : M.Basis J I) : J = I :=
  hJ.eq_of_subset_indep hI hJ.Subset Subset.rfl
#align matroid_in.indep.eq_of_basis MatroidIn.Indep.eq_of_basis

theorem Indep.basis_self (hI : M.indep I) : M.Basis I I :=
  by
  rw [basis_iff', and_iff_left hI.subset_ground, and_iff_right hI, and_iff_right subset.rfl]
  exact fun _ _ => subset_antisymm
#align matroid_in.indep.basis_self MatroidIn.Indep.basis_self

@[simp]
theorem basis_self_iff_indep : M.Basis I I ↔ M.indep I :=
  ⟨Basis.indep, Indep.basis_self⟩
#align matroid_in.basis_self_iff_indep MatroidIn.basis_self_iff_indep

-- lemma exists_basis (M : matroid_in α) (X : set α) (hX : X ⊆ M.E . ssE) : ∃ I, M.basis I X :=
-- let ⟨I, hI, _⟩ := M.empty_indep.subset_basis_of_subset (empty_subset X) in ⟨_,hI⟩
theorem Basis.exists_base (hI : M.Basis I X) : ∃ B, M.base B ∧ I = B ∩ X :=
  by
  obtain ⟨B, hB, hIB⟩ := hI.indep
  refine' ⟨B, hB, subset_antisymm (subset_inter hIB hI.subset) _⟩
  rw [hI.eq_of_subset_indep (hB.indep.inter_right X) (subset_inter hIB hI.subset)
      (inter_subset_right _ _)]
#align matroid_in.basis.exists_base MatroidIn.Basis.exists_base

theorem base_iff_basis_ground : M.base B ↔ M.Basis B M.e :=
  by
  rw [base_iff_maximal_indep, basis_iff, and_congr_right]
  intro hB
  rw [and_iff_right hB.subset_ground]
  exact ⟨fun h J hJ hBJ hJE => h _ hJ hBJ, fun h I hI hBI => h I hI hBI hI.subset_ground⟩
#align matroid_in.base_iff_basis_ground MatroidIn.base_iff_basis_ground

theorem Base.basis_ground (hB : M.base B) : M.Basis B M.e :=
  base_iff_basis_ground.mp hB
#align matroid_in.base.basis_ground MatroidIn.Base.basis_ground

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Indep.basis_of_forall_insert (hI : M.indep I) (hIX : I ⊆ X)
    (he : ∀ e ∈ X \ I, ¬M.indep (insert e I))
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.Basis I X := by
  rw [basis_iff, and_iff_right hI, and_iff_right hIX]
  refine' fun J hJ hIJ hJX => hIJ.antisymm fun e heJ => by_contra fun heI => he e ⟨hJX heJ, heI⟩ _
  exact hJ.subset (insert_subset.mpr ⟨heJ, hIJ⟩)
#align matroid_in.indep.basis_of_forall_insert MatroidIn.Indep.basis_of_forall_insert

theorem Basis.iUnion_basis_iUnion {ι : Type _} (X I : ι → Set α) (hI : ∀ i, M.Basis (I i) (X i))
    (h_ind : M.indep (⋃ i, I i)) : M.Basis (⋃ i, I i) (⋃ i, X i) :=
  by
  refine'
    h_ind.basis_of_forall_insert
      (Union_subset_iff.mpr fun i => (hI i).Subset.trans (subset_Union _ _)) (fun e he hi => _)
      (Union_subset fun i => (hI i).subset_ground)
  simp only [mem_diff, mem_Union, not_exists] at he 
  obtain ⟨i, heXi⟩ := he.1
  exact
    he.2 i ((hI i).mem_of_insert_indep heXi (hi.subset (insert_subset_insert (subset_Union _ _))))
#align matroid_in.basis.Union_basis_Union MatroidIn.Basis.iUnion_basis_iUnion

theorem Basis.basis_iUnion {ι : Type _} [Nonempty ι] (X : ι → Set α) (hI : ∀ i, M.Basis I (X i)) :
    M.Basis I (⋃ i, X i) :=
  by
  convert basis.Union_basis_Union X (fun _ => I) (fun i => hI i) _
  all_goals rw [Union_const]
  exact (hI ‹Nonempty ι›.some).indep
#align matroid_in.basis.basis_Union MatroidIn.Basis.basis_iUnion

theorem Basis.union_basis_union (hIX : M.Basis I X) (hJY : M.Basis J Y) (h : M.indep (I ∪ J)) :
    M.Basis (I ∪ J) (X ∪ Y) := by
  rw [union_eq_Union, union_eq_Union]
  refine' basis.Union_basis_Union _ _ _ _
  · simp only [Bool.forall_bool, Bool.cond_false, Bool.cond_true]; exact ⟨hJY, hIX⟩
  rwa [← union_eq_Union]
#align matroid_in.basis.union_basis_union MatroidIn.Basis.union_basis_union

theorem Basis.basis_union (hIX : M.Basis I X) (hIY : M.Basis I Y) : M.Basis I (X ∪ Y) := by
  convert hIX.union_basis_union hIY _ <;> rw [union_self]; exact hIX.indep
#align matroid_in.basis.basis_union MatroidIn.Basis.basis_union

theorem Basis.basis_union_of_subset (hI : M.Basis I X) (hJ : M.indep J) (hIJ : I ⊆ J) :
    M.Basis J (J ∪ X) :=
  by
  convert hJ.basis_self.union_basis_union hI (by rwa [union_eq_left_iff_subset.mpr hIJ])
  rw [union_eq_left_iff_subset.mpr hIJ]
#align matroid_in.basis.basis_union_of_subset MatroidIn.Basis.basis_union_of_subset

theorem Basis.insert_basis_insert (hI : M.Basis I X) (h : M.indep (insert e I)) :
    M.Basis (insert e I) (insert e X) :=
  by
  convert
    hI.union_basis_union (indep.basis_self (h.subset (singleton_subset_iff.mpr (mem_insert _ _)))) _
  simp; simp; simpa
#align matroid_in.basis.insert_basis_insert MatroidIn.Basis.insert_basis_insert

theorem Base.insert_dep (hB : M.base B) (h : e ∉ B) : ¬M.indep (insert e B) := fun h' =>
  (insert_ne_self.mpr h).symm ((base_iff_maximal_indep.mp hB).2 _ h' (subset_insert _ _))
#align matroid_in.base.insert_dep MatroidIn.Base.insert_dep

theorem Base.sSubset_dep (hB : M.base B) (h : B ⊂ X) : ¬M.indep X := fun h' =>
  h.Ne ((base_iff_maximal_indep.mp hB).2 _ h' h.Subset)
#align matroid_in.base.ssubset_dep MatroidIn.Base.sSubset_dep

theorem Indep.exists_insert_of_not_base (hI : M.indep I) (hI' : ¬M.base I) (hB : M.base B) :
    ∃ e ∈ B \ I, M.indep (insert e I) :=
  by
  obtain ⟨B', hB', hIB'⟩ := hI
  obtain ⟨x, hxB', hx⟩ := exists_of_ssubset (hIB'.ssubset_of_ne (by rintro rfl; exact hI' hB'))
  obtain hxB | hxB := em (x ∈ B)
  · exact ⟨x, ⟨hxB, hx⟩, ⟨B', hB', insert_subset.mpr ⟨hxB', hIB'⟩⟩⟩
  obtain ⟨e, he, hbase⟩ := hB'.exchange hB ⟨hxB', hxB⟩
  exact
    ⟨e, ⟨he.1, not_mem_subset hIB' he.2⟩,
      ⟨_, hbase, insert_subset_insert (subset_diff_singleton hIB' hx)⟩⟩
#align matroid_in.indep.exists_insert_of_not_base MatroidIn.Indep.exists_insert_of_not_base

theorem Basis.inter_eq_of_subset_indep (hIX : M.Basis I X) (hIJ : I ⊆ J) (hJ : M.indep J) :
    J ∩ X = I :=
  (subset_inter hIJ hIX.Subset).antisymm' fun e he =>
    hIX.mem_of_insert_indep he.2 (hJ.Subset (insert_subset_iff.mpr ⟨he.1, hIJ⟩))
#align matroid_in.basis.inter_eq_of_subset_indep MatroidIn.Basis.inter_eq_of_subset_indep

theorem Base.exists_insert_of_sSubset (hB : M.base B) (hIB : I ⊂ B) (hB' : M.base B') :
    ∃ e ∈ B' \ I, M.indep (insert e I) :=
  (hB.indep.Subset hIB.Subset).exists_insert_of_not_base
    (fun hI => hIB.Ne (hI.eq_of_subset_base hB hIB.Subset)) hB'
#align matroid_in.base.exists_insert_of_ssubset MatroidIn.Base.exists_insert_of_sSubset

theorem Base.base_of_basis_supset (hB : M.base B) (hBX : B ⊆ X) (hIX : M.Basis I X) : M.base I :=
  by
  by_contra h
  obtain ⟨e, heBI, he⟩ := hIX.indep.exists_insert_of_not_base h hB
  exact heBI.2 (hIX.mem_of_insert_indep (hBX heBI.1) he)
#align matroid_in.base.base_of_basis_supset MatroidIn.Base.base_of_basis_supset

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Base.basis_of_subset
    (hX : X ⊆ M.e := by
      run_tac
        ssE)
    (hB : M.base B) (hBX : B ⊆ X) : M.Basis B X :=
  by
  rw [basis_iff, and_iff_right hB.indep, and_iff_right hBX]
  exact fun J hJ hBJ hJX => hB.eq_of_subset_indep hJ hBJ
#align matroid_in.base.basis_of_subset MatroidIn.Base.basis_of_subset

theorem Indep.exists_base_subset_union_base (hI : M.indep I) (hB : M.base B) :
    ∃ B', M.base B' ∧ I ⊆ B' ∧ B' ⊆ I ∪ B :=
  by
  obtain ⟨B', hB', hIB'⟩ := hI.subset_basis_of_subset (subset_union_left I B)
  exact ⟨B', hB.base_of_basis_supset (subset_union_right _ _) hB', hIB', hB'.subset⟩
#align matroid_in.indep.exists_base_subset_union_base MatroidIn.Indep.exists_base_subset_union_base

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (B «expr ⊆ » M₁.E) -/
theorem eq_of_base_iff_base_forall {M₁ M₂ : MatroidIn α} (hE : M₁.e = M₂.e)
    (h : ∀ (B) (_ : B ⊆ M₁.e), M₁.base B ↔ M₂.base B) : M₁ = M₂ :=
  by
  apply MatroidIn.ext _ _ hE
  ext B
  refine'
    ⟨fun h' => (h _ h'.subset_ground).mp h', fun h' =>
      (h _ (h'.subset_ground.trans_eq hE.symm)).mpr h'⟩
#align matroid_in.eq_of_base_iff_base_forall MatroidIn.eq_of_base_iff_base_forall

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (I «expr ⊆ » M₁.E) -/
theorem eq_of_indep_iff_indep_forall {M₁ M₂ : MatroidIn α} (hE : M₁.e = M₂.e)
    (h : ∀ (I) (_ : I ⊆ M₁.e), M₁.indep I ↔ M₂.indep I) : M₁ = M₂ :=
  by
  refine' eq_of_base_iff_base_forall hE fun B hB => _
  rw [base_iff_maximal_indep, base_iff_maximal_indep]
  constructor
  · rintro ⟨hBi, hmax⟩
    rw [← h _ hB, and_iff_right hBi]
    refine' fun I hI hBI => hmax I _ hBI
    rwa [h]
    rw [hE]
    exact hI.subset_ground
  rintro ⟨hBi, hmax⟩
  rw [h _ hB, and_iff_right hBi]
  refine' fun I hI hBI => hmax I _ hBI
  rwa [← h]
  exact hI.subset_ground
#align matroid_in.eq_of_indep_iff_indep_forall MatroidIn.eq_of_indep_iff_indep_forall

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (I «expr ⊆ » M₁.E) -/
theorem eq_iff_indep_iff_indep_forall {M₁ M₂ : MatroidIn α} :
    M₁ = M₂ ↔ M₁.e = M₂.e ∧ ∀ (I) (_ : I ⊆ M₁.e), M₁.indep I ↔ M₂.indep I :=
  ⟨fun h => by subst h; simp, fun h => eq_of_indep_iff_indep_forall h.1 h.2⟩
#align matroid_in.eq_iff_indep_iff_indep_forall MatroidIn.eq_iff_indep_iff_indep_forall

-- lemma eq_iff_indep_iff_indep_forall {M₁ M₂ : matroid_in α} : M₁ = M₂ ↔ ∀ I, M₁.indep I ↔ M₂.indep I :=  
-- ⟨λ h I, by rw h, eq_of_indep_iff_indep_forall⟩  
-- lemma eq_iff_set_of_indep_eq_set_of_indep {M₁ M₂ : matroid_in α} : 
--   M₁ = M₂ ↔ {I | M₁.indep I} = {I | M₂.indep I} :=
-- by { rw [eq_iff_indep_iff_indep_forall, set.ext_iff], refl }
end DepIndep

section FromAxioms

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (X «expr ⊆ » E) -/
def matroidOfBase {α : Type _} (E : Set α) (base : Set α → Prop) (exists_base : ∃ B, base B)
    (base_exchange : ExchangeProperty base)
    (maximality : ∀ (X) (_ : X ⊆ E), ExistsMaximalSubsetProperty (fun I => ∃ B, base B ∧ I ⊆ B) X)
    (support : ∀ B, base B → B ⊆ E) : MatroidIn α :=
  ⟨E, base, exists_base, base_exchange, maximality, support⟩
#align matroid_in.matroid_of_base MatroidIn.matroidOfBase

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (X «expr ⊆ » E) -/
@[simp]
theorem matroidOfBase_apply {α : Type _} (E : Set α) (base : Set α → Prop)
    (exists_base : ∃ B, base B) (base_exchange : ExchangeProperty base)
    (maximality : ∀ (X) (_ : X ⊆ E), ExistsMaximalSubsetProperty (fun I => ∃ B, base B ∧ I ⊆ B) X)
    (support : ∀ B, base B → B ⊆ E) :
    (matroidOfBase E base exists_base base_exchange maximality support).base = base :=
  rfl
#align matroid_in.matroid_of_base_apply MatroidIn.matroidOfBase_apply

/-- A collection of bases with the exchange property and at least one finite member is a matroid -/
def matroidOfExistsFiniteBase {α : Type _} (E : Set α) (base : Set α → Prop)
    (exists_finite_base : ∃ B, base B ∧ B.Finite) (base_exchange : ExchangeProperty base)
    (support : ∀ B, base B → B ⊆ E) : MatroidIn α :=
  matroidOfBase E base
    (let ⟨B, h⟩ := exists_finite_base
    ⟨B, h.1⟩)
    base_exchange
    (by
      obtain ⟨B, hB, hfin⟩ := exists_finite_base
      intro X hXE
      apply existsMaximalSubsetProperty_of_bounded ⟨B.ncard, _⟩
      rintro I ⟨B', hB', hIB'⟩
      have hB'fin : B'.finite := finite_of_finite_of_exch base_exchange hB hB' hfin
      rw [card_eq_card_of_exchange base_exchange hB hB']
      exact ⟨hB'fin.subset hIB', ncard_le_of_subset hIB' hB'fin⟩)
    support
#align matroid_in.matroid_of_exists_finite_base MatroidIn.matroidOfExistsFiniteBase

@[simp]
theorem matroidOfExistsFiniteBase_apply {α : Type _} (E : Set α) (base : Set α → Prop)
    (exists_finite_base : ∃ B, base B ∧ B.Finite) (base_exchange : ExchangeProperty base)
    (support : ∀ B, base B → B ⊆ E) :
    (matroidOfExistsFiniteBase E base exists_finite_base base_exchange support).base = base :=
  rfl
#align matroid_in.matroid_of_exists_finite_base_apply MatroidIn.matroidOfExistsFiniteBase_apply

/-- A matroid constructed with a finite base is `finite_rk` -/
instance {E : Set α} {base : Set α → Prop} {exists_finite_base : ∃ B, base B ∧ B.Finite}
    {base_exchange : ExchangeProperty base} {support : ∀ B, base B → B ⊆ E} :
    MatroidIn.FiniteRk
      (matroidOfExistsFiniteBase E base exists_finite_base base_exchange support) :=
  ⟨exists_finite_base⟩

def matroidOfBaseOfFinite {E : Set α} (hE : E.Finite) (base : Set α → Prop)
    (exists_base : ∃ B, base B) (base_exchange : ExchangeProperty base)
    (support : ∀ B, base B → B ⊆ E) : MatroidIn α :=
  matroidOfExistsFiniteBase E base
    (let ⟨B, hB⟩ := exists_base
    ⟨B, hB, hE.Subset (support _ hB)⟩)
    base_exchange support
#align matroid_in.matroid_of_base_of_finite MatroidIn.matroidOfBaseOfFinite

@[simp]
theorem matroidOfBaseOfFinite_apply {E : Set α} (hE : E.Finite) (base : Set α → Prop)
    (exists_base : ∃ B, base B) (base_exchange : ExchangeProperty base)
    (support : ∀ B, base B → B ⊆ E) :
    (matroidOfBaseOfFinite hE base exists_base base_exchange support).base = base :=
  rfl
#align matroid_in.matroid_of_base_of_finite_apply MatroidIn.matroidOfBaseOfFinite_apply

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (X «expr ⊆ » E) -/
/-- A version of the independence axioms that avoids cardinality -/
def matroidOfIndep (E : Set α) (indep : Set α → Prop) (h_empty : indep ∅)
    (h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I)
    (h_aug :
      ∀ ⦃I B⦄,
        indep I →
          I ∉ maximals (· ⊆ ·) indep → B ∈ maximals (· ⊆ ·) indep → ∃ x ∈ B \ I, indep (insert x I))
    (h_maximal : ∀ (X) (_ : X ⊆ E), ExistsMaximalSubsetProperty indep X)
    (h_support : ∀ I, indep I → I ⊆ E) : MatroidIn α :=
  matroidOfBase E (fun B => B ∈ maximals (· ⊆ ·) indep)
    (by
      obtain ⟨B, ⟨hB, -, -⟩, hB₁⟩ := h_maximal E subset.rfl ∅ h_empty (empty_subset _)
      exact ⟨B, hB, fun B' hB' hBB' => hB₁ ⟨hB', empty_subset _, h_support B' hB'⟩ hBB'⟩)
    (by
      rintro B B' ⟨hB, hBmax⟩ ⟨hB', hB'max⟩ e he
      obtain ⟨f, hf, hfB⟩ := h_aug (h_subset hB (diff_subset B {e})) _ ⟨hB', hB'max⟩
      simp only [mem_diff, mem_singleton_iff, not_and, Classical.not_not] at hf 
      have hfB' : f ∉ B := by intro hfB; have := hf.2 hfB; subst this; exact he.2 hf.1
      · refine' ⟨f, ⟨hf.1, hfB'⟩, by_contra fun hnot => _⟩
        obtain ⟨x, hxB, hind⟩ := h_aug hfB hnot ⟨hB, hBmax⟩
        simp only [mem_diff, mem_insert_iff, mem_singleton_iff, not_or, not_and,
          Classical.not_not] at hxB 
        have := hxB.2.2 hxB.1; subst this
        rw [insert_comm, insert_diff_singleton, insert_eq_of_mem he.1] at hind 
        exact not_mem_subset (hBmax hind (subset_insert _ _)) hfB' (mem_insert _ _)
      simp only [maximals, mem_sep_iff, diff_singleton_subset_iff, not_and, not_forall, exists_prop]
      exact fun _ => ⟨B, hB, subset_insert _ _, fun hss => (hss he.1).2 rfl⟩)
    (by
      rintro X hXE I ⟨B, hB, hIB⟩ hIX
      -- rintro I X ⟨B, hB,  hIB⟩ hIX,
      obtain ⟨J, ⟨hJ, hIJ, hJX⟩, hJmax⟩ := h_maximal X hXE I (h_subset hB.1 hIB) hIX
      obtain ⟨BJ, hBJ⟩ := h_maximal E subset.rfl J hJ (h_support J hJ)
      refine' ⟨J, ⟨⟨BJ, _, hBJ.1.2.1⟩, hIJ, hJX⟩, _⟩
      ·
        exact
          ⟨hBJ.1.1, fun B' hB' hBJB' => hBJ.2 ⟨hB', hBJ.1.2.1.trans hBJB', h_support B' hB'⟩ hBJB'⟩
      simp only [mem_set_of_eq, and_imp, forall_exists_index]
      rintro A B' ⟨hB'i : indep _, hB'max⟩ hB'' hIA hAX hJA
      exact hJmax ⟨h_subset hB'i hB'', hIA, hAX⟩ hJA)
    fun B hB => h_support B hB.1
#align matroid_in.matroid_of_indep MatroidIn.matroidOfIndep

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (X «expr ⊆ » E) -/
@[simp]
theorem matroidOfIndep_apply (E : Set α) (indep : Set α → Prop) (h_empty : indep ∅)
    (h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I)
    (h_aug :
      ∀ ⦃I B⦄,
        indep I →
          I ∉ maximals (· ⊆ ·) indep → B ∈ maximals (· ⊆ ·) indep → ∃ x ∈ B \ I, indep (insert x I))
    (h_maximal : ∀ (X) (_ : X ⊆ E), ExistsMaximalSubsetProperty indep X)
    (h_support : ∀ I, indep I → I ⊆ E) :
    (matroidOfIndep E indep h_empty h_subset h_aug h_maximal h_support).indep = indep :=
  by
  ext I
  simp only [MatroidIn.Indep, matroid_of_indep]
  refine' ⟨fun ⟨B, hB, hIB⟩ => h_subset hB.1 hIB, fun hI => _⟩
  obtain ⟨B, ⟨hB, hIB, -⟩, hBmax⟩ := h_maximal E subset.rfl I hI (h_support _ hI)
  exact ⟨B, ⟨hB, fun B' hB' hBB' => hBmax ⟨hB', hIB.trans hBB', h_support _ hB'⟩ hBB'⟩, hIB⟩
#align matroid_in.matroid_of_indep_apply MatroidIn.matroidOfIndep_apply

/--
If there is an absolute upper bound on the size of an independent set, then the maximality axiom isn't needed to define a matroid by independent sets. -/
def matroidOfIndepOfBdd (E : Set α) (indep : Set α → Prop) (h_empty : indep ∅)
    (h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I)
    (h_aug :
      ∀ ⦃I B⦄,
        indep I →
          I ∉ maximals (· ⊆ ·) indep → B ∈ maximals (· ⊆ ·) indep → ∃ x ∈ B \ I, indep (insert x I))
    (h_bdd : ∃ n, ∀ I, indep I → I.Finite ∧ I.ncard ≤ n) (h_support : ∀ I, indep I → I ⊆ E) :
    MatroidIn α :=
  matroidOfIndep E indep h_empty h_subset h_aug
    (fun X h => existsMaximalSubsetProperty_of_bounded h_bdd X) h_support
#align matroid_in.matroid_of_indep_of_bdd MatroidIn.matroidOfIndepOfBdd

@[simp]
theorem matroidOfIndepOfBdd_apply (E : Set α) (indep : Set α → Prop) (h_empty : indep ∅)
    (h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I)
    (h_aug :
      ∀ ⦃I B⦄,
        indep I →
          I ∉ maximals (· ⊆ ·) indep → B ∈ maximals (· ⊆ ·) indep → ∃ x ∈ B \ I, indep (insert x I))
    (h_bdd : ∃ n, ∀ I, indep I → I.Finite ∧ I.ncard ≤ n) (h_support : ∀ I, indep I → I ⊆ E) :
    (matroidOfIndepOfBdd E indep h_empty h_subset h_aug h_bdd h_support).indep = indep := by
  simp [matroid_of_indep_of_bdd]
#align matroid_in.matroid_of_indep_of_bdd_apply MatroidIn.matroidOfIndepOfBdd_apply

instance (E : Set α) (indep : Set α → Prop) (h_empty : indep ∅)
    (h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I)
    (h_aug :
      ∀ ⦃I B⦄,
        indep I →
          I ∉ maximals (· ⊆ ·) indep → B ∈ maximals (· ⊆ ·) indep → ∃ x ∈ B \ I, indep (insert x I))
    (h_bdd : ∃ n, ∀ I, indep I → I.Finite ∧ I.ncard ≤ n) (h_support : ∀ I, indep I → I ⊆ E) :
    MatroidIn.FiniteRk (matroidOfIndepOfBdd E indep h_empty h_subset h_aug h_bdd h_support) :=
  by
  obtain ⟨B, hB⟩ :=
    (matroid_of_indep_of_bdd E indep h_empty h_subset h_aug h_bdd h_support).exists_base
  obtain ⟨h, h_bdd⟩ := h_bdd
  refine' hB.finite_rk_of_finite (h_bdd B _).1
  rw [← matroid_of_indep_of_bdd_apply E indep, MatroidIn.Indep]
  exact ⟨_, hB, subset.rfl⟩

def matroidOfIndepOfBdd' (E : Set α) (indep : Set α → Prop) (h_empty : indep ∅)
    (h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I)
    (ind_aug : ∀ ⦃I J⦄, indep I → indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ indep (insert e I))
    (h_bdd : ∃ n, ∀ I, indep I → I.Finite ∧ I.ncard ≤ n) (h_support : ∀ I, indep I → I ⊆ E) :
    MatroidIn α :=
  matroidOfIndepOfBdd E indep h_empty h_subset
    (by
      intro I J hI hIn hJ
      by_contra' h'
      obtain hlt | hle := lt_or_le I.ncard J.ncard
      · obtain ⟨e, heJ, heI, hi⟩ := ind_aug hI hJ.1 hlt
        exact h' e ⟨heJ, heI⟩ hi
      obtain h_eq | hlt := hle.eq_or_lt
      · refine'
          hIn
            ⟨hI, fun K (hK : indep K) hIK =>
              hIK.ssubset_or_eq.elim (fun hss => _) fun h => h.symm.subset⟩
        obtain ⟨f, hfK, hfJ, hi⟩ := ind_aug hJ.1 hK (h_eq.trans_lt (ncard_lt_ncard hss _))
        · exact (hfJ (hJ.2 hi (subset_insert _ _) (mem_insert f _))).elim
        obtain ⟨n, hn⟩ := h_bdd
        exact (hn K hK).1
      obtain ⟨e, heI, heJ, hi⟩ := ind_aug hJ.1 hI hlt
      exact heJ (hJ.2 hi (subset_insert _ _) (mem_insert e _)))
    h_bdd h_support
#align matroid_in.matroid_of_indep_of_bdd' MatroidIn.matroidOfIndepOfBdd'

@[simp]
theorem matroidOfIndepOfBdd'_apply (E : Set α) (indep : Set α → Prop) (h_empty : indep ∅)
    (h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I)
    (ind_aug : ∀ ⦃I J⦄, indep I → indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ indep (insert e I))
    (h_bdd : ∃ n, ∀ I, indep I → I.Finite ∧ I.ncard ≤ n) (h_support : ∀ I, indep I → I ⊆ E) :
    (matroidOfIndepOfBdd' E indep h_empty h_subset ind_aug h_bdd h_support).indep = indep := by
  simp [matroid_of_indep_of_bdd']
#align matroid_in.matroid_of_indep_of_bdd'_apply MatroidIn.matroidOfIndepOfBdd'_apply

/--
A collection of sets in a finite type satisfying the usual independence axioms determines a matroid -/
def matroidOfIndepOfFinite {E : Set α} (hE : E.Finite) (indep : Set α → Prop) (h_empty : indep ∅)
    (ind_mono : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I)
    (ind_aug : ∀ ⦃I J⦄, indep I → indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ indep (insert e I))
    (h_support : ∀ ⦃I⦄, indep I → I ⊆ E) : MatroidIn α :=
  matroidOfIndepOfBdd' E indep h_empty ind_mono ind_aug
    ⟨E.ncard, fun I hI => ⟨hE.Subset (h_support hI), ncard_le_of_subset (h_support hI) hE⟩⟩
    h_support
#align matroid_in.matroid_of_indep_of_finite MatroidIn.matroidOfIndepOfFinite

@[simp]
theorem matroidOfIndepOfFinite_apply {E : Set α} (hE : E.Finite) (indep : Set α → Prop)
    (h_empty : indep ∅) (ind_mono : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I)
    (ind_aug : ∀ ⦃I J⦄, indep I → indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ indep (insert e I))
    (h_support : ∀ ⦃I⦄, indep I → I ⊆ E) :
    (matroidOfIndepOfFinite hE indep h_empty ind_mono ind_aug h_support).indep = indep := by
  simp [matroid_of_indep_of_finite]
#align matroid_in.matroid_of_indep_of_finite_apply MatroidIn.matroidOfIndepOfFinite_apply

end FromAxioms

section Dual

/-- This is really an order-theory lemma. Not clear where to put it, though.  -/
theorem base_compl_iff_mem_maximals_disjoint_base :
    M.base (Bᶜ) ↔ B ∈ maximals (· ⊆ ·) {I | ∃ B, M.base B ∧ Disjoint I B} :=
  by
  simp_rw [← subset_compl_iff_disjoint_left]
  refine' ⟨fun h => ⟨⟨Bᶜ, h, subset.rfl⟩, _⟩, _⟩
  · rintro X ⟨B', hB', hXB'⟩ hBX
    rw [← compl_subset_compl] at hBX ⊢
    rwa [← hB'.eq_of_subset_base h (hXB'.trans hBX)]
  rintro ⟨⟨B', hB', hBB'⟩, h⟩
  rw [subset_compl_comm] at hBB' 
  rwa [hBB'.antisymm (h ⟨_, hB', _⟩ hBB'), compl_compl]
  rw [compl_compl]
#align matroid_in.base_compl_iff_mem_maximals_disjoint_base MatroidIn.base_compl_iff_mem_maximals_disjoint_base

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem base_compl_iff_mem_maximals_disjoint_base'
    (hB : B ⊆ M.e := by
      run_tac
        ssE) :
    M.base (M.e \ B) ↔ B ∈ maximals (· ⊆ ·) {I | I ⊆ M.e ∧ ∃ B, M.base B ∧ Disjoint I B} :=
  by
  refine' ⟨fun h => ⟨⟨hB, _, h, disjoint_sdiff_right⟩, _⟩, fun h => _⟩
  · rintro X ⟨hXE, B', hB', hXB'⟩ hBX
    rw [hB'.eq_of_subset_base h (subset_diff.mpr ⟨hB'.subset_ground, _⟩), ←
      subset_compl_iff_disjoint_right, diff_eq, compl_inter, compl_compl] at hXB' 
    · refine' (subset_inter hXE hXB').trans _
      rw [inter_distrib_left, inter_compl_self, empty_union]
      exact inter_subset_right _ _
    exact (disjoint_of_subset_left hBX hXB').symm
  obtain ⟨⟨-, B', hB', hIB'⟩, h⟩ := h
  suffices : B' = M.E \ B; rwa [← this]
  rw [subset_antisymm_iff, subset_diff, disjoint_comm, and_iff_left hIB',
    and_iff_right hB'.subset_ground, diff_subset_iff]
  intro e he
  rw [mem_union, or_iff_not_imp_right]
  intro heB'
  refine' h ⟨insert_subset.mpr ⟨he, hB⟩, ⟨B', hB', _⟩⟩ (subset_insert _ _) (mem_insert e B)
  rw [← union_singleton, disjoint_union_left, disjoint_singleton_left]
  exact ⟨hIB', heB'⟩
#align matroid_in.base_compl_iff_mem_maximals_disjoint_base' MatroidIn.base_compl_iff_mem_maximals_disjoint_base'

def dual (M : MatroidIn α) : MatroidIn α :=
  matroidOfIndep M.e (fun I => I ⊆ M.e ∧ ∃ B, M.base B ∧ Disjoint I B)
    ⟨empty_subset M.e, M.exists_base.imp fun B hB => ⟨hB, empty_disjoint _⟩⟩
    (by
      rintro I J ⟨hJE, B, hB, hJB⟩ hIJ
      exact ⟨hIJ.trans hJE, ⟨B, hB, disjoint_of_subset_left hIJ hJB⟩⟩)
    (by
      rintro I X ⟨hIE, B, hB, hIB⟩ hI_not_max hX_max
      have hXE := hX_max.1.1
      have hB' := (base_compl_iff_mem_maximals_disjoint_base' hXE).mpr hX_max
      set B' := M.E \ X with hX
      have hI := (not_iff_not.mpr base_compl_iff_mem_maximals_disjoint_base').mpr hI_not_max
      obtain ⟨B'', hB'', hB''₁, hB''₂⟩ := (hB'.indep.diff I).exists_base_subset_union_base hB
      rw [← compl_subset_compl, ← hIB.sdiff_eq_right, ← union_diff_distrib, diff_eq, compl_inter,
        compl_compl, union_subset_iff, compl_subset_compl] at hB''₂ 
      have hssu :=
        (subset_inter hB''₂.2 hIE).ssubset_of_ne (by rintro rfl; apply hI; convert hB''; simp)
      obtain ⟨e, ⟨heB'' : e ∉ _, heE⟩, heI⟩ := exists_of_ssubset hssu
      use e
      rw [mem_diff, insert_subset, and_iff_left heI, and_iff_right heE, and_iff_right hIE]
      refine' ⟨by_contra fun heX => heB'' (hB''₁ ⟨_, heI⟩), ⟨B'', hB'', _⟩⟩
      · rw [hX]; exact ⟨heE, heX⟩
      rw [← union_singleton, disjoint_union_left, disjoint_singleton_left, and_iff_left heB'']
      exact disjoint_of_subset_left hB''₂.2 disjoint_compl_left)
    (by
      rintro X hX I' ⟨hI'E, B, hB, hI'B⟩ hI'X
      obtain ⟨I, hI⟩ := M.exists_basis (M.E \ X)
      obtain ⟨B', hB', hIB', hB'IB⟩ := hI.indep.exists_base_subset_union_base hB
      refine'
        ⟨X \ B' ∩ M.E,
          ⟨_, subset_inter (subset_diff.mpr _) hI'E,
            (inter_subset_left _ _).trans (diff_subset _ _)⟩,
          _⟩
      · simp only [inter_subset_right, true_and_iff]
        exact ⟨B', hB', disjoint_of_subset_left (inter_subset_left _ _) disjoint_sdiff_left⟩
      · rw [and_iff_right hI'X]
        refine' disjoint_of_subset_right hB'IB _
        rw [disjoint_union_right, and_iff_left hI'B]
        exact disjoint_of_subset hI'X hI.subset disjoint_sdiff_right
      simp only [mem_set_of_eq, subset_inter_iff, and_imp, forall_exists_index]
      intro J hJE B'' hB'' hdj hI'J hJX hssJ
      rw [and_iff_left hJE]
      rw [diff_eq, inter_right_comm, ← diff_eq, diff_subset_iff] at hssJ 
      have hI' : B'' ∩ X ∪ B' \ X ⊆ B' :=
        by
        rw [union_subset_iff, and_iff_left (diff_subset _ _), ←
          inter_eq_self_of_subset_left hB''.subset_ground, inter_right_comm, inter_assoc]
        calc
          _ ⊆ _ := inter_subset_inter_right _ hssJ
          _ ⊆ _ := by rw [inter_distrib_left, hdj.symm.inter_eq, union_empty]
          _ ⊆ _ := inter_subset_right _ _
      obtain ⟨B₁, hB₁, hI'B₁, hB₁I⟩ := (hB'.indep.subset hI').exists_base_subset_union_base hB''
      rw [union_comm, ← union_assoc, union_eq_self_of_subset_right (inter_subset_left _ _)] at hB₁I 
      have : B₁ = B' := by
        refine' hB₁.eq_of_subset_indep hB'.indep fun e he => _
        refine' (hB₁I he).elim (fun heB'' => _) fun h => h.1
        refine' (em (e ∈ X)).elim (fun heX => hI' (Or.inl ⟨heB'', heX⟩)) fun heX => hIB' _
        refine'
          hI.mem_of_insert_indep ⟨hB₁.subset_ground he, heX⟩
            (hB₁.indep.subset (insert_subset.mpr ⟨he, _⟩))
        refine' (subset_union_of_subset_right (subset_diff.mpr ⟨hIB', _⟩) _).trans hI'B₁
        refine' disjoint_of_subset_left hI.subset disjoint_sdiff_left
      subst this
      refine' subset_diff.mpr ⟨hJX, by_contra fun hne => _⟩
      obtain ⟨e, heJ, heB'⟩ := not_disjoint_iff.mp hne
      obtain heB'' | ⟨heB₁, heX⟩ := hB₁I heB'
      · exact hdj.ne_of_mem heJ heB'' rfl
      exact heX (hJX heJ))
    (by tauto)
#align matroid_in.dual MatroidIn.dual

/-- A notation typeclass for matroid duality, denoted by the `﹡` symbol. -/
@[class]
structure HasMatroidDual (β : Type _) where
  dual : β → β
#align matroid_in.has_matroid_dual MatroidIn.HasMatroidDual

/- ./././Mathport/Syntax/Translate/Command.lean:476:9: unsupported: advanced prec syntax «expr + »(max[std.prec.max], 1) -/
postfix:999 "﹡" => HasMatroidDual.dual

instance matroidInDual {α : Type _} : HasMatroidDual (MatroidIn α) :=
  ⟨MatroidIn.dual⟩
#align matroid_in.matroid_in_dual MatroidIn.matroidInDual

theorem dual_indep_iff_exists' : M﹡.indep I ↔ I ⊆ M.e ∧ ∃ B, M.base B ∧ Disjoint I B := by
  simp [has_matroid_dual.dual, dual]
#align matroid_in.dual_indep_iff_exists' MatroidIn.dual_indep_iff_exists'

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem dual_indep_iff_exists
    (hI : I ⊆ M.e := by
      run_tac
        ssE) :
    M﹡.indep I ↔ ∃ B, M.base B ∧ Disjoint I B := by rw [dual_indep_iff_exists', and_iff_right hI]
#align matroid_in.dual_indep_iff_exists MatroidIn.dual_indep_iff_exists

@[simp]
theorem dual_ground : M﹡.e = M.e :=
  rfl
#align matroid_in.dual_ground MatroidIn.dual_ground

theorem dual_dep_iff_forall : M﹡.Dep I ↔ I ⊆ M.e ∧ ∀ B, M.base B → (I ∩ B).Nonempty :=
  by
  simp_rw [dep_iff, dual_indep_iff_exists', and_comm', dual_ground, and_congr_right_iff, not_and,
    not_exists, not_and, not_disjoint_iff_nonempty_inter]
  exact fun hIE => by rw [imp_iff_right hIE]
#align matroid_in.dual_dep_iff_forall MatroidIn.dual_dep_iff_forall

instance dual_finite [M.Finite] : M﹡.Finite :=
  ⟨M.ground_finite⟩
#align matroid_in.dual_finite MatroidIn.dual_finite

theorem Set.subset_ground_dual (hX : X ⊆ M.e) : X ⊆ M﹡.e :=
  hX
#align matroid_in.set.subset_ground_dual MatroidIn.Set.subset_ground_dual

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem dual_base_iff
    (hB : B ⊆ M.e := by
      run_tac
        ssE) :
    M﹡.base B ↔ M.base (M.e \ B) :=
  by
  rw [base_compl_iff_mem_maximals_disjoint_base', base_iff_maximal_indep, dual_indep_iff_exists',
    mem_maximals_setOf_iff]
  simp [dual_indep_iff_exists']
#align matroid_in.dual_base_iff MatroidIn.dual_base_iff

theorem dual_base_iff' : M﹡.base B ↔ M.base (M.e \ B) ∧ B ⊆ M.e :=
  by
  obtain h | h := em (B ⊆ M.E)
  · rw [dual_base_iff, and_iff_left h]
  rw [iff_false_intro h, and_false_iff, iff_false_iff]
  exact fun h' => h h'.subset_ground
#align matroid_in.dual_base_iff' MatroidIn.dual_base_iff'

theorem Base.compl_base_of_dual (h : M﹡.base B) : M.base (M.e \ B) :=
  (dual_base_iff h.subset_ground).mp h
#align matroid_in.base.compl_base_of_dual MatroidIn.Base.compl_base_of_dual

@[simp]
theorem dual_dual (M : MatroidIn α) : M﹡﹡ = M :=
  by
  refine' eq_of_base_iff_base_forall rfl fun B hB => _
  rw [dual_base_iff, dual_base_iff]
  rw [dual_ground] at *
  simp only [sdiff_sdiff_right_self, inf_eq_inter, ground_inter_right]
#align matroid_in.dual_dual MatroidIn.dual_dual

theorem dual_indep_iff_coindep : M﹡.indep X ↔ M.Coindep X :=
  dual_indep_iff_exists'
#align matroid_in.dual_indep_iff_coindep MatroidIn.dual_indep_iff_coindep

theorem Base.compl_base_dual (hB : M.base B) : M﹡.base (M.e \ B) := by
  haveI := Fact.mk hB.subset_ground; simpa [dual_base_iff]
#align matroid_in.base.compl_base_dual MatroidIn.Base.compl_base_dual

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic matroid_in.ssE -/
theorem Base.compl_inter_basis_of_inter_basis (hB : M.base B) (hBX : M.Basis (B ∩ X) X) :
    M﹡.Basis (M.e \ B ∩ (M.e \ X)) (M.e \ X) :=
  by
  rw [basis_iff]
  refine'
    ⟨hB.compl_base_dual.indep.subset (inter_subset_left _ _), inter_subset_right _ _,
      fun J hJ hBCJ hJX => hBCJ.antisymm (subset_inter _ hJX)⟩
  obtain ⟨-, B', hB', hJB'⟩ := dual_indep_iff_coindep.mp hJ
  obtain ⟨B'', hB'', hsB'', hB''s⟩ := hBX.indep.exists_base_subset_union_base hB'
  have hB'ss : B' ⊆ B ∪ X :=
    by
    rw [←
      diff_subset_diff_iff M.E
        (by
          run_tac
            ssE :
          B ∪ X ⊆ M.E)
        hB'.subset_ground,
      subset_diff, and_iff_right (diff_subset _ _)]
    rw [diff_inter_diff] at hBCJ 
    exact disjoint_of_subset_left hBCJ hJB'
  have hB''ss : B'' ⊆ B :=
    by
    refine' fun e he => (hB''s he).elim And.left fun heB' => (hB'ss heB').elim id fun heX => _
    exact (hBX.mem_of_insert_indep heX (hB''.indep.subset (insert_subset.mpr ⟨he, hsB''⟩))).1
  have := (hB''.eq_of_subset_indep hB.indep hB''ss).symm; subst this
  rw [subset_diff] at *
  exact
    ⟨hJX.1,
      disjoint_of_subset_right hB''s
        (disjoint_union_right.mpr ⟨disjoint_of_subset_right (inter_subset_right _ _) hJX.2, hJB'⟩)⟩
#align matroid_in.base.compl_inter_basis_of_inter_basis MatroidIn.Base.compl_inter_basis_of_inter_basis

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Base.inter_basis_iff_compl_inter_basis_dual (hB : M.base B)
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.Basis (B ∩ X) X ↔ M﹡.Basis (M.e \ B ∩ (M.e \ X)) (M.e \ X) :=
  by
  refine' ⟨hB.compl_inter_basis_of_inter_basis, fun h => _⟩
  simpa using hB.compl_base_dual.compl_inter_basis_of_inter_basis h
#align matroid_in.base.inter_basis_iff_compl_inter_basis_dual MatroidIn.Base.inter_basis_iff_compl_inter_basis_dual

theorem dual_inj {M₁ M₂ : MatroidIn α} (h : M₁﹡ = M₂﹡) : M₁ = M₂ := by
  rw [← dual_dual M₁, h, dual_dual]
#align matroid_in.dual_inj MatroidIn.dual_inj

@[simp]
theorem dual_inj_iff {M₁ M₂ : MatroidIn α} : M₁﹡ = M₂﹡ ↔ M₁ = M₂ :=
  ⟨dual_inj, congr_arg _⟩
#align matroid_in.dual_inj_iff MatroidIn.dual_inj_iff

theorem eq_dual_comm {M₁ M₂ : MatroidIn α} : M₁ = M₂﹡ ↔ M₂ = M₁﹡ := by
  rw [← dual_inj_iff, dual_dual, eq_comm]
#align matroid_in.eq_dual_comm MatroidIn.eq_dual_comm

theorem dual_eq_comm {M₁ M₂ : MatroidIn α} : M₁﹡ = M₂ ↔ M₂﹡ = M₁ := by
  rw [← dual_inj_iff, dual_dual, eq_comm]
#align matroid_in.dual_eq_comm MatroidIn.dual_eq_comm

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem coindep_iff_exists
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    M.Coindep X ↔ ∃ B, M.base B ∧ Disjoint X B := by rw [coindep, and_iff_right hX]
#align matroid_in.coindep_iff_exists MatroidIn.coindep_iff_exists

theorem Coindep.exists_disjoint_base (hX : M.Coindep X) : ∃ B, M.base B ∧ Disjoint X B :=
  hX.2
#align matroid_in.coindep.exists_disjoint_base MatroidIn.Coindep.exists_disjoint_base

theorem Coindep.base_of_basis_compl (hX : M.Coindep X) (hB : M.Basis B (Xᶜ)) : M.base B :=
  by
  obtain ⟨B', hB'⟩ := hX.exists_disjoint_base
  exact hB'.1.base_of_basis_supset (subset_compl_iff_disjoint_left.mpr hB'.2) hB
#align matroid_in.coindep.base_of_basis_compl MatroidIn.Coindep.base_of_basis_compl

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem base_iff_dual_base_compl
    (hB : B ⊆ M.e := by
      run_tac
        ssE) :
    M.base B ↔ M﹡.base (M.e \ B) := by simp [dual_base_iff]
#align matroid_in.base_iff_dual_base_compl MatroidIn.base_iff_dual_base_compl

end Dual

end MatroidIn


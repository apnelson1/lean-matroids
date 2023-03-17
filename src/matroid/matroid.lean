import .ncard
import .helpers 

-- noncomputable theory 
open_locale classical 
open_locale big_operators

open set 

variables {E : Type*}

/-- A predicate `P` on sets satisfies the exchange property if, for all `X` and `Y` satisfying `P`
  and all `a ∈ X \ Y`, there exists `b ∈ Y \ X` so that swapping `a` for `b` in `X` maintains `P`.-/
def exchange_property (P : set E → Prop) : Prop :=
  ∀ X Y, P X → P Y → ∀ a ∈ X \ Y, ∃ b ∈ Y \ X, P (insert b (X \ {a})) 

/-- A `matroid` is a nonempty collection of sets satisfying the exchange property. Each such set 
  is called a `base` of the matroid. -/
@[ext] structure matroid (E : Type*) :=
  (base : set E → Prop)
  (exists_base' : ∃ B, base B) 
  (base_exchange' : exchange_property base)

variables {B B' B₁ B₂ I I' J I₁ I₂ J' X Y Z : set E} {x y : E} {M : matroid E} 

namespace matroid 
/- None of these definitions require finiteness -/

section defs

/-- A set is independent if it is contained in a base.  -/
def indep (M : matroid E) (I : set E) : Prop := 
  ∃ B, M.base B ∧ I ⊆ B   

/-- A basis for a set `X` is a maximal independent subset of `X`
  (Often, the word 'basis' is used to refer to what we call a 'base')-/
def basis (M : matroid E) (I X : set E) : Prop := 
  M.indep I ∧ I ⊆ X ∧ ∀ J, M.indep J → I ⊆ J → J ⊆ X → I = J 

/-- A circuit is a minimal dependent set -/
def circuit (M : matroid E) (C : set E) : Prop := 
  ¬M.indep C ∧ ∀ I ⊂ C, M.indep I 

/-- A flat is a maximal set having a given basis  -/
def flat (M : matroid E) (F : set E) : Prop := 
  ∀ I X, M.basis I F → M.basis I X → X ⊆ F    

/-- The closure of a set is the intersection of the flats containing it -/
def cl (M : matroid E) (X : set E) : set E :=
  ⋂₀ {F | M.flat F ∧ X ⊆ F}

/-- A spanning set is one whose closure is the ground set -/
def spanning (M : matroid E) (X : set E) : Prop := 
  M.cl X = univ 

/-- A hyperplane is a maximal nonspanning set -/
def hyperplane (M : matroid E) (H : set E) : Prop :=
  ¬ M.spanning H ∧ ∀ X, X ⊂ H → M.spanning X      

/-- A cocircuit is the complement of a hyperplane -/
def cocircuit (M : matroid E) (K : set E) : Prop := 
  M.hyperplane Kᶜ  

/-- A loop is a singleton circuit -/
def loop (M : matroid E) (e : E) : Prop :=
  M.circuit {e}

/-- A coloop is an element contained in every basis -/
def coloop (M : matroid E) (e : E) : Prop :=
  ∀ B, M.base B → e ∈ B

  
end defs 

section base

lemma exists_base (M : matroid E) : ∃ B, M.base B := M.exists_base'

lemma base.exchange (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hx : x ∈ B₁ \ B₂) : 
  ∃ y ∈ B₂ \ B₁, M.base (insert y (B₁ \ {x}))  :=
M.base_exchange' B₁ B₂ hB₁ hB₂ _ hx

lemma base.exchange_mem (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hxB₁ : x ∈ B₁) (hxB₂ : x ∉ B₂) : 
  ∃ y, (y ∈ B₂ ∧ y ∉ B₁) ∧ M.base (insert y (B₁ \ {x})) := 
by simpa using hB₁.exchange hB₂ ⟨hxB₁, hxB₂⟩ 

variables [finite E]

lemma base.card_eq_card_of_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) :
  B₁.ncard = B₂.ncard := 
begin
  suffices h : ∀ i B B', M.base B → M.base B' → (B' \ B).ncard ≤ i → 
    B'.ncard ≤ B.ncard, from 
      (h _ _ _ hB₂ hB₁ rfl.le).antisymm (h _ _ _ hB₁ hB₂ rfl.le), 
  clear hB₁ B₁ hB₂ B₂, 
  intro i, 
  induction i with i IH, 
  { rintros B B' - - h, 
    rw [le_zero_iff, ncard_eq_zero, diff_eq_empty] at h, 
    exact ncard_le_of_subset h, },  
  refine λ B B' hB hB' hcard, le_of_not_lt (λ hlt, _ ) , 
  obtain ⟨x, hxB', hxB⟩ := exists_mem_not_mem_of_ncard_lt_ncard hlt,  
  have := hB'.exchange hB ⟨hxB',hxB⟩,
  obtain ⟨y, hy, hB''⟩ := hB'.exchange hB ⟨hxB',hxB⟩, 

  have hcard := IH B (insert y (B' \ {x}))  hB (by simpa using hB'') _, 
  { apply hlt.not_le, 
    rwa [ncard_insert_of_not_mem, ncard_diff_singleton_add_one hxB'] at hcard,
    simpa using hy.2},
  
  suffices hss : (insert y (B' \ {x})) \ B ⊂ B' \ B, 
  { exact nat.le_of_lt_succ ((ncard_lt_ncard hss).trans_le hcard)},

  refine (ssubset_iff_of_subset (λ a, _) ).mpr ⟨x,  _⟩, 
  { rw [mem_diff, mem_insert_iff, and_imp, mem_diff_singleton],
    rintro (rfl | ⟨haB',hax⟩) haB,
    { exact (haB hy.1).elim}, 
    exact ⟨haB',haB⟩},
  
  rw [exists_prop, mem_diff, mem_diff, not_and, not_not_mem, mem_insert_iff, mem_diff, 
    mem_singleton_iff, ne_self_iff_false, and_false, or_false], 
  exact ⟨⟨hxB', hxB⟩, by {rintro rfl, exact hy.1}⟩, 
end 

lemma base.eq_of_subset_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hB₁B₂ : B₁ ⊆ B₂) : 
  B₁ = B₂ :=
begin
  suffices : B₂ \ B₁ = ∅, from hB₁B₂.antisymm (diff_eq_empty.mp this),
  by_contra' h, 
  obtain ⟨e,he⟩ := set.nonempty_iff_ne_empty.mpr h, 
  obtain ⟨y,hy,-⟩:=  hB₂.exchange hB₁ he, 
  exact hy.2 (hB₁B₂ hy.1), 
end 

end base

end matroid 

section misc

lemma insert_diff_singleton_comm {α : Type*} {X : set α} {e f : α} (hef : e ≠ f) : 
  insert e (X \ {f}) = (insert e X) \ {f} :=
by rw [←union_singleton, ←union_singleton, union_diff_distrib, 
  diff_singleton_eq_self (by simpa using hef.symm : f ∉ {e})]

end misc 


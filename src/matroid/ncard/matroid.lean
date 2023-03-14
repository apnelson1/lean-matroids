import .ncard
import ..helpers 

-- noncomputable theory 
open_locale classical 

/-
 This is the same as basic.lean, but with noncomputable cardinality from ncard . Saves about 50 loc
-/

open set 

variables {E : Type*}

/-- A predicate `P` on sets satisfies the exchange property if, for all `X` and `Y` satisfying `P`
  and all `a ∈ X \ Y`, there exists `b ∈ Y \ X` so that swapping `a` for `b` in `X` maintains `P`.-/
def exchange_property (P : set E → Prop) : Prop :=
  ∀ X Y, P X → P Y → ∀ a, a ∈ X \ Y → ∃ b, b ∈ Y \ X ∧ P (X \ {a} ∪ {b}) 

/-- A `matroid` is a nonempty collection of sets satisfying the exchange property. Each such set 
  is called a `base` of the matroid. -/
@[ext] structure matroid (E : Type*) :=
  (base : set E → Prop)
  (exists_base' : ∃ B, base B) 
  (base_exchange' : exchange_property base)

namespace matroid 

variables [finite E] {B B' B₁ B₂ I I' J I₁ I₂ J' X Y Z : set E} {x y : E} {M : matroid E}

lemma exists_base (M : matroid E) : ∃ B, M.base B := M.exists_base'

lemma base.exchange (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hxB₁ : x ∈ B₁) (hxB₂ : x ∉ B₂) : 
  ∃ y, (y ∈ B₂ ∧ y ∉ B₁) ∧ M.base (B₁ \ {x} ∪ {y})   := 
M.base_exchange' B₁ B₂ hB₁ hB₂ x ⟨hxB₁,hxB₂⟩
  
lemma base.exchange_diff (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hx : x ∈ B₁ \ B₂) : 
  ∃ y ∈ B₂ \ B₁, M.base (insert y (B₁ \ {x}))  :=
by simpa using hB₁.exchange hB₂ hx.1 hx.2

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
  obtain ⟨y, ⟨(hyB : y ∈ B), (hyB' : y ∉ B')⟩, hB''⟩ := hB'.exchange hB hxB' hxB, 

  have hcard := IH B (B' \ {x} ∪ {y})  hB (by simpa using hB'') _, 
  { apply hlt.not_le, 
    rwa [union_singleton, ncard_insert_of_not_mem, ncard_diff_singleton_add_one hxB'] at hcard,
    simpa using hyB'},
  
  suffices hss : (B' \ {x} ∪ {y}) \ B ⊂ B' \ B, 
  { exact nat.le_of_lt_succ ((ncard_lt_ncard hss).trans_le hcard)},

  refine (ssubset_iff_of_subset (λ a, _) ).mpr ⟨x,  _⟩, 
  { simp only [mem_diff, mem_union, mem_singleton_iff, and_imp],  
    rintros (⟨haB',hax⟩ | rfl) haB;  
    tauto},
  
  simp only [mem_diff, mem_union, mem_singleton, not_true, and_false, mem_singleton_iff, false_or, 
    not_and, not_not_mem, exists_prop, and_false, false_or,eq_self_iff_true], 
  
  exact ⟨⟨hxB', hxB⟩, by {rintro rfl, exact hyB}⟩, 
end 

lemma base.eq_of_subset_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hB₁B₂ : B₁ ⊆ B₂) : 
  B₁ = B₂ :=
begin
  suffices : B₂ \ B₁ = ∅, from hB₁B₂.antisymm (diff_eq_empty.mp this),
  by_contra' h, 
  obtain ⟨e,he⟩ := set.nonempty_iff_ne_empty.mpr h, 
  obtain ⟨y,⟨hy,hy'⟩,-⟩:=  hB₂.exchange_diff hB₁ he, 
  exact hy' (hB₁B₂ hy), 
end 

end matroid 



section misc

lemma insert_diff_singleton_comm {α : Type*} {X : set α} {e f : α} (hef : e ≠ f) : 
  insert e (X \ {f}) = (insert e X) \ {f} :=
by rw [←union_singleton, ←union_singleton, union_diff_distrib, 
  diff_singleton_eq_self (by simpa using hef.symm : f ∉ {e})]
  
lemma ncard_exchange {α : Type*} {X : set α} {e f : α} (he : e ∉ X) (hf : f ∈ X) : 
  (insert e (X \ {f})).ncard = X.ncard :=
begin
  cases X.finite_or_infinite with h h,
  { haveI := h.to_subtype, 
    rw [ncard_insert_of_not_mem, ncard_diff_singleton_add_one hf],
    simpa only [mem_diff, not_and] using he},
  rw [((h.diff (set.to_finite {f})).mono (subset_insert e _)).ncard, h.ncard],  
end 

lemma ncard_exchange' {α : Type*} {X : set α} {e f : α} (he : e ∉ X) (hf : f ∈ X) : 
  ((insert e X) \ {f}).ncard = X.ncard :=
by rw [←insert_diff_singleton_comm (by {rintro rfl, exact he hf} : e ≠ f), ncard_exchange he hf]


end misc 
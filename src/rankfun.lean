

import boolalg

namespace boolalg

@[ext] structure rankfun (B : boolalg) :=
  (r : B → ℤ)
  (R0 : ∀ (X : B), 0 ≤ r X)
  (R1 : ∀ (X : B), r X ≤ size X)
  (R2 : ∀ (X Y : B), X ⊆ Y → r X ≤ r Y)
  (R3 : ∀ (X Y : B), r (X ∪ Y) + r (X ∩ Y) ≤ r X + r Y)

lemma rank_bot {B : boolalg} (M : rankfun B) :
  M.r ⊥ = 0 :=
le_antisymm (calc M.r ⊥ ≤ size (⊥ : B) : M.R1 ⊥ ... = 0 : size_bot B) (M.R0 ⊥)

instance rankfun.coe_to_fun {B : boolalg} : has_coe_to_fun (rankfun B) := ⟨_, rankfun.r⟩


structure matroid :=
  (E : Type)
  [E_finite : fintype E]
  [E_dec_eq : decidable_eq E]
  (r_fun : rankfun (powersetalg E))

-- simplifying interface with matroids 

def matroid.alg (M : matroid) := @powersetalg M.E M.E_finite M.E_dec_eq 

@[simp] def matroid.r (M : matroid) := M.r_fun.r 
def matroid.R0 (M : matroid) : ∀ X, 0 ≤ M.r X := M.r_fun.R0
def matroid.R1 (M : matroid) : ∀ X, M.r X ≤ size X := M.r_fun.R1
def matroid.R2 (M : matroid) : ∀ X Y, X ⊆ Y → M.r X ≤ M.r Y := M.r_fun.R2
def matroid.R3 (M : matroid) : ∀ X Y, M.r (X ∪ Y) + M.r (X ∩ Y) ≤ M.r X + M.r Y := M.r_fun.R3

-----



@[simp] def restrict_subset {B : boolalg} (R : B) (rfun : rankfun B)  : rankfun (subalg R) := 
let f := (embed.from_subset R).f in 
⟨λ X, rfun.r (f X), λ X, rfun.R0 (f X), λ X, rfun.R1 (f X), λ X Y, rfun.R2 (f X) (f Y), λ X Y, rfun.R3 (f X) (f Y)⟩ 

@[simp] def restrict_nested_pair {B : boolalg} {R₀ R : B} (h : R₀ ⊆ R) (rfun : rankfun (subalg R)) : rankfun (subalg R₀)  := 
let f := (embed.from_nested_pair h).f in 
⟨λ X, rfun.r (f X), λ X, rfun.R0 (f X), λ X, rfun.R1 (f X), λ X Y, rfun.R2 (f X) (f Y), λ X Y, rfun.R3 (f X) (f Y)⟩ 

@[simp] def corestrict_subset {B : boolalg} (R : B) (rfun : rankfun B)  : rankfun (subalg R) := 
let f := (embed.from_subset R).f in 
⟨ 
  λ X, rfun.r (f X ∪ Rᶜ),
  sorry, 
  sorry, 
  sorry, 
  sorry, 
⟩ 

@[simp] def corestrict_nested_pair {B : boolalg} {R₀ R : B} (h : R₀ ⊆ R) (rfun : rankfun (subalg R)) : rankfun (subalg R₀)  := 
let r := rfun.r, f := (embed.from_nested_pair h).f, C := (embed.to_subalg R₀ h)ᶜ in 
⟨
  λ X, r (f X ∪ C) - r C, 
  λ X, begin simp only [sub_nonneg], exact rfun.R2 C (f X ∪ C) (subset_union_right (f X) C) end, 
  λ X, sorry, 
  λ X Y, sorry, 
  λ X Y, sorry, 
⟩

--@[simp] lemma restrict_restrict {B : boolalg} (R₁ R₀ R : B)

structure preminor (M : matroid) :=
  (E : M.alg)
  (C : M.alg)
  (disjoint : C ∩ E = ⊥)

def preminor.r {M : matroid} (N : preminor M) : rankfun (subalg N.E) :=
let emb := @subalg.embed M.alg N.E, f := emb.f, C := N.C in 
{
  r := (fun (X : subalg N.E), M.r (f X ∪ N.C) - M.r N.C),
  R0 := λ X, by linarith [M.R2 C (f X ∪ C) (subset_union_right (f X) C)],
  R1 := λ X, by linarith [emb.on_size X, M.R0 (f X ∩ C), M.R3 (f X) C, M.R1 (f X)],
  R2 := λ X Y hXY, by linarith[M.R2 (f X ∪ C) (f Y ∪ C) (subset_union_subset_left (f X) (f Y) C (emb.on_subset hXY ))],
  R3 := λ X Y,
  begin
    have hu : (f X ∪ C) ∪ (f Y ∪ C) = f (X ∪ Y) ∪ C := by rw [←union_distrib_union_left,←emb.on_union],
    have hi : (f X ∪ C) ∩ (f Y ∪ C) = f (X ∩ Y) ∪ C := by rw [←union_distrib_right, ←emb.on_inter], 
    have hs := M.R3 (f X ∪ C) (f Y ∪ C), 
    rw [hu, hi] at hs,
    linarith [hs],      
  end,
}

end boolalg 
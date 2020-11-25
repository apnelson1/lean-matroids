

import boolalg

namespace boolalg

structure rankfun (B : boolalg) :=
  (r : B → ℤ)
  (R0 : ∀ (X : B), 0 ≤ r X)
  (R1 : ∀ (X : B), r X ≤ size X)
  (R2 : ∀ (X Y : B), X ⊆ Y → r X ≤ r Y)
  (R3 : ∀ (X Y : B), r (X ∪ Y) + r (X ∩ Y) ≤ r X + r Y)

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

-- Why doesn't this typecheck? I don't see why it's not isomorphic to submodular.lean. 

def minor (M : matroid) : Type* :=
  quot (fun (N₁ N₂ : preminor M), N₁.r = N₂.r)



--def minor.alg {M: matroid} (N : minor M) : 

structure protominor (M : matroid) :=
  (E : M.alg)
  (r : rankfun (subalg E))

def preminor_to_protominor {M : matroid} (N : preminor M) : protominor M := {
  E := N.E,
  r := N.r,
}

def preminor_to_protominor_respects_support {M : matroid} (N₁ N₂ : preminor M) (h : N₁.r = N₂.r) : preminor_to_protominor N₁ = preminor_to_protominor N₂
    := sorry
#check quot.lift 
-- power_set_alg {γ : Type} [decidable_eq γ] (S : finset γ) : boolalg

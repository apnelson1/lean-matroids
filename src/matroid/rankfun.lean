import boolalg.basic boolalg.examples

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
⟨λ X, rfun.r X, λ X, rfun.R0 X, λ X, rfun.R1 X, λ X Y, rfun.R2 X Y, λ X Y, rfun.R3 X Y⟩ 

@[simp] def restrict_nested_pair {B : boolalg} {R₀ R : B} (h : R₀ ⊆ R) (rfun : rankfun (subalg R)) : rankfun (subalg R₀)  := 
let f := (embed.from_nested_pair h).f in 
⟨λ X, rfun.r (f X), λ X, rfun.R0 (f X), λ X, rfun.R1 (f X), λ X Y, rfun.R2 (f X) (f Y), λ X Y, rfun.R3 (f X) (f Y)⟩ 

@[simp] def corestrict_subset {B : boolalg} (R : B) (M : rankfun B)  : rankfun (subalg R) := 
let C := Rᶜ in 
⟨ 
  λ X, M.r (X ∪ C) - M.r C,
  λ X, by {rw sub_nonneg, exact M.R2 C (X ∪ C) (subset_union_right X C)},
  λ X, by linarith [subalg_coe_size X, M.R0 (X ∩ C), M.R3 X C, M.R1 X],  
  λ X Y hXY, by linarith [M.R2 (X ∪ C) (Y ∪ C) (subset_union_subset_left X Y C (subalg_coe_subset hXY))] ,
  λ X Y, by
  {
    suffices : M.r (coe (X ∪ Y) ∪ C) + M.r (coe (X ∩ Y) ∪ C) ≤ M.r (X ∪ C) + M.r (Y ∪ C), by linarith, 
    have h := M.R3 (X ∪ C) (Y ∪ C), 
    rw [←union_distrib_right, ←union_distrib_union_left] at h, refine h,
  },
⟩ 

@[simp] def corestrict_nested_pair {B : boolalg} {R₀ R : B} (h : R₀ ⊆ R) (M : rankfun (subalg R)) : rankfun (subalg R₀)  := 
let r := M.r, emb := (embed.from_nested_pair h), f := emb.f, C := (embed.to_subalg R₀ R h)ᶜ in 
⟨
  λ X, r (f X ∪ C) - r C, 
  λ X, by {rw sub_nonneg, exact M.R2 C (f X ∪ C) (subset_union_right (f X) C)}, 
  λ X, by linarith [emb.on_size X, M.R0 ((f X) ∩ C), M.R3 (f X) C, M.R1 (f X)], 
  λ X Y hXY, by linarith [M.R2 ((f X) ∪ C) ((f Y) ∪ C) (subset_union_subset_left _ _ C (emb.on_subset hXY))], 
  λ X Y, by {
    suffices : M.r (f (X ∪ Y) ∪ C) + M.r (f (X ∩ Y) ∪ C) ≤ M.r ((f X) ∪ C) + M.r ((f Y) ∪ C), by linarith, 
    have h := M.R3 ((f X) ∪ C) ((f Y) ∪ C), 
    rw [←union_distrib_right, ←union_distrib_union_left] at h, refine h,
  },
⟩

end boolalg 
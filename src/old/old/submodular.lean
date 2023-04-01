/-

Idea:
A rank function is just a submodular function which is weakly increasing,
and sandwiched between 0 and size.

-/

import boolalg

structure submod (b : boolalg.boolalg) :=
  (f : b → ℤ)
  (s : forall (X Y : b), f (X ∪ Y) + f (X ∩ Y) ≤ f X + f Y)
instance submod.coe_to_fun {b : boolalg.boolalg} : has_coe_to_fun (submod b) := ⟨_, submod.f⟩

structure rankfun (b : boolalg.boolalg) extends submod b :=
  (pos : forall (X : b), 0 ≤ f X)
  (monotone : forall (X Y : b), X ⊆ Y → f(X) ≤ f(Y))
instance rankfun.coe_to_fun {b : boolalg.boolalg} : has_coe_to_fun (rankfun b) := ⟨_, fun (r : rankfun b), r.f⟩

structure boolalg.embed_ (b b' : boolalg.boolalg) :=
  (f : b → b')
  (on_bot : f ⊥ = ⊥)
  -- note : top is not respected by embedding
  (on_inter (X Y) : f (X ∩ Y) = (f X) ∩ (f Y))
  (on_union (X Y) : f (X ∪ Y) = (f X) ∪ (f Y))
  -- note : compl is not respected by embedding
  (on_size (X : b) : boolalg.size X = boolalg.size (f X))

lemma boolalg.embed.on_subset_ {b b' : boolalg.boolalg} (emb : boolalg.embed b b') {X Y : b} :
  (X ⊆ Y) → (emb.f X) ⊆ (emb.f Y) := sorry

def powersetalg_ : Type → boolalg.boolalg := sorry
def subalg_ {b : boolalg.boolalg} (E : b) : boolalg.boolalg := sorry
instance boolalg.embed.coe_to_fun_ {b b' : boolalg.boolalg} : has_coe_to_fun (boolalg.embed b b') := {
  F := (fun _, b → b'),
  coe := sorry,
}
def subalg_.embed_ {b : boolalg.boolalg} {E : b} : boolalg.embed (subalg_ E) b := sorry


structure matroid :=
  (E : Type)
  (r : rankfun (powersetalg_ E))
def matroid.alg_ (M : matroid) := powersetalg_ M.E

structure preminor (M : matroid) :=
  (E : M.alg_)
  (C : M.alg_)
  (disjoint : C ∩ {e} = ⊥)

def preminor.r {M : matroid} (N : preminor M) : rankfun (subalg_ N.E) :=
let emb := @subalg_.embed_ M.alg_ N.E, ef := emb.f, C := N.C in
{
  f := (fun (X : subalg_ N.E), M.r (ef X ∪ N.C) - M.r N.C),
  s :=
  begin
    intros X Y,
    have hu : (ef X ∪ C) ∪ (ef Y ∪ C) = ef (X ∪ Y) ∪ C := by rw ←boolalg.union_distrib_union_left; rw ←emb.on_union,
    have hi : (ef X ∪ C) ∩ (ef Y ∪ C) = ef (X ∩ Y) ∪ C := by sorry, --rw ←boolalg.union_distrib_left; rw ←emb.on_inter,
    have hs := M.r.s (ef X ∪ C) (ef Y ∪ C),
    rw [hu, hi] at hs, unfold_coes,
    linarith [hs],     
  end,
  pos := sorry,
  monotone := begin
    intros X Y hXY,
    have := M.r.monotone (ef X ∪ C) (ef Y ∪ C) (boolalg.subset_union_subset_left (ef X) (ef Y) C (emb.on_subset hXY )),
    show M.r (ef X ∪ N.C) - M.r N.C ≤ M.r (ef Y ∪ N.C) - M.r N.C,
    unfold_coes,
    linarith,
  end
}


/-
begin
    intros X Y, rcases m.kernel with ⟨C,emb,⟨h0,hC,hCr⟩⟩,
    let f := emb.func,
    have hu : (f X ∪ C) ∪ (f Y ∪ C) = f (X ∪ Y) ∪ C := by rw ←union_distrib_union_left; rw ←emb.on_union,
    have hi : (f X ∪ C) ∩ (f Y ∪ C) = f (X ∩ Y) ∪ C := by rw ←union_distrib_left; rw ←emb.on_inter,
    have hs := M.s (f X ∪ C) (f Y ∪ C),
    rw [hu, hi] at hs,
    linarith [hCr X, hCr Y, hCr (X ∪ Y), hCr (X ∩ Y), hR3],
  end,
-/

def minor (M : matroid) : Type* :=
  quot (fun (N₁ N₂ : preminor M), N₁.r = N₂.r)

--def minor.alg {M: matroid} (N : minor M) :

structure protominor (M : matroid) :=
  (E : M.alg_)
  (r : rankfun (subalg_ E))

def preminor_to_protominor {M : matroid} (N : preminor M) : protominor M := {
  E := N.E,
  r := N.r,
}

def preminor_to_protominor_respects_support {M : matroid} (N₁ N₂ : preminor M) (h : N₁.r = N₂.r) : preminor_to_protominor N₁ = preminor_to_protominor N₂
    := sorry
#check quot.lift
-- power_set_alg {γ : Type} [decidable_eq γ] (S : finset γ) : boolalg

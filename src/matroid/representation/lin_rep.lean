import analysis.inner_product_space.gram_schmidt_ortho
import data.zmod.basic
import linear_algebra.basis
import linear_algebra.linear_independent
import mathlib.ncard
import ..constructions.basic
import ..dual
import ..simple
import .field_stuff

namespace set
variables {α β : Type*} {f : α → β}

open function

lemma injective_iff_forall_inj_on_pair : injective f ↔ ∀ a b, inj_on f {a, b} :=
⟨λ h a b, h.inj_on _, λ h a b hab,
  h _ _ (mem_insert _ _) (mem_insert_of_mem _ $ mem_singleton _) hab⟩

end set

noncomputable theory

open function set submodule
open_locale classical

universe u
variables {E 𝔽 ι : Type*} [field 𝔽] [fintype E] {M : matroid E} {I B : set E} {x : E}
-- we should have semiring 𝔽 by default, idk why it doesn't see it
-- why did we have finite E and not fintype E?

namespace matroid

/-- A `𝔽`-matroid representation is a map from the base of the matroid to `ι → 𝔽` such that a set -/
structure rep (𝔽 : Type*) [field 𝔽] (M : matroid E) (ι : Type*) :=
(to_fun : E → ι → 𝔽)
(valid' : ∀ I : set E, linear_independent 𝔽 (λ e : I, to_fun e) ↔ M.indep I)

/-- `M` is `𝔽`-representable if it has an `𝔽`-representation. -/
def is_representable (𝔽 : Type*) [field 𝔽] (M : matroid E) : Prop := ∃ ι, nonempty (rep 𝔽 M ι)

namespace rep

def rep.mk (𝔽 : Type*) [field 𝔽] (M : matroid E) (ι : Type*) (f : E → ι → 𝔽 ) (valid : ∀ (I : set E), linear_independent 𝔽 (λ (e : ↥I), f ↑e) ↔ M.indep I) : 
  rep 𝔽 M ι := 
{ to_fun := f,
  valid' := valid }

instance fun_like : fun_like (rep 𝔽 M ι) E (λ _, ι → 𝔽) :=
{ coe := to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

instance : has_coe_to_fun (rep 𝔽 M ι) (λ _, E → ι → 𝔽) := fun_like.has_coe_to_fun

lemma valid (φ : rep 𝔽 M ι) : linear_independent 𝔽 (λ e : I, φ e) ↔ M.indep I := φ.valid' _

protected lemma is_representable {ι : Type u} (φ : rep 𝔽 M ι) : is_representable.{_ _ u} 𝔽 M :=
⟨ι, ⟨φ⟩⟩

lemma inj_on_of_indep (φ : rep 𝔽 M ι) (hI : M.indep I) : inj_on φ I :=
inj_on_iff_injective.2 (φ.valid.2 hI).injective

lemma linear_independent_iff_coe (φ : rep 𝔽 M ι) (hI : M.indep I) :
  linear_independent 𝔽 (λ e : I, φ e) ↔ linear_independent 𝔽 (coe : φ '' I → ι → 𝔽) :=
linear_independent_image $ inj_on_of_indep _ hI

-- want lemma that says if it's a simple matroid the cardinality of E
-- is leq that of the submodule

lemma ne_zero_of_nonloop (φ : rep 𝔽 M ι) (hx : M.nonloop x) : φ x ≠ 0 :=
(φ.valid.2 hx.indep).ne_zero (⟨x, mem_singleton _⟩ : ({x} : set E))

lemma ne_zero_of_loopless (φ : rep 𝔽 M ι) (hl : loopless M) (x : E) : φ x ≠ 0 :=
ne_zero_of_nonloop _ $ hl _

lemma injective_of_simple (φ : rep 𝔽 M ι) (hs : simple M) : injective φ :=
injective_iff_forall_inj_on_pair.2 $ λ a b, inj_on_of_indep _ $ hs _ _

lemma subset_nonzero_of_simple (φ : rep 𝔽 M ι) (hs : simple M) :
  range φ ⊆ span 𝔽 (range φ) \ {0} :=
begin
  refine subset_diff.2 ⟨subset_span, disjoint_left.2 _⟩,
  rintro _ ⟨x, rfl⟩,
  exact ne_zero_of_loopless _ hs.loopless _,
end

lemma of_base (φ : rep 𝔽 M ι) {B : set E} (hB : M.base B) (e : E) : φ e ∈ span 𝔽 (φ '' B) :=
begin
  by_cases e ∈ B,
  { exact subset_span (mem_image_of_mem _ h) },
  have h2 : ¬ linear_independent 𝔽 (λ x : insert e B, φ x) := φ.valid.not.2 (hB.dep_of_insert h),
  contrapose! h2,
  exact (linear_independent_insert' h).2 ⟨φ.valid.2 hB.indep, h2⟩,
end

lemma of_basis (φ : rep 𝔽 M ι) {X I : set E} (hI : M.basis I X) {e : E} (he : e ∈ X): φ e ∈ span 𝔽 (φ '' I) :=
begin
  by_cases e ∈ I, 
  { apply subset_span (mem_image_of_mem _ h) },
  have h2 : ¬ linear_independent 𝔽 (λ x : insert e I, φ x) := φ.valid.not.2 (hI.insert_dep (mem_diff_of_mem he h)),
  contrapose! h2,
  apply (linear_independent_insert' h).2 ⟨φ.valid.2 hI.indep, h2⟩,
end

lemma span_base (φ : rep 𝔽 M ι) (hB : M.base B) :
  span 𝔽 (φ '' B) = span 𝔽 (range φ) :=
begin
  refine (span_mono $ image_subset_range _ _).antisymm (span_le.2 _),
  rintro _ ⟨x, rfl⟩,
  exact of_base _ hB _,
end

lemma span_basis (φ : rep 𝔽 M ι) {X I : set E} (hI : M.basis I X) : 
  span 𝔽 (φ '' I) = span 𝔽 (φ '' X) :=
begin
  refine (span_mono $ image_subset _ (basis.subset hI)).antisymm (span_le.2 _),
  rintros x ⟨y, ⟨hy1, hy2⟩⟩,
  rw ← hy2, 
  apply of_basis φ hI hy1,
end

lemma basis_of_base (φ : rep 𝔽 M ι) {B : set E} (hB : M.base B) :
  _root_.basis B 𝔽 (span 𝔽 (range φ)) :=
by { rw [←span_base _ hB, image_eq_range], exact basis.span (φ.valid.2 hB.indep) }

lemma of_rank (φ : rep 𝔽 M ι) [fintype 𝔽] [fintype (span 𝔽 (set.range φ))] :
  finite_dimensional.finrank 𝔽 (span 𝔽 (range φ)) = M.rk :=
begin
  cases M.exists_base with B hB,
  -- need basis for this to work
  have h3 := finite_dimensional.fin_basis 𝔽 (span 𝔽 (set.range φ)),
  rw [←span_base φ hB, finrank_span_set_eq_card (φ '' B)],
  have h6 : (⇑φ '' B).to_finset.card = B.to_finset.card,
  { simp_rw to_finset_card,
    rw ← card_image_of_inj_on (inj_on_of_indep φ (base.indep hB)) },
  rw h6,
  simp only [← base.card hB, ncard_def, to_finset_card, nat.card_eq_fintype_card],
  have h8 : linear_independent 𝔽 (λ (x : B), φ (x : E)),
  rw rep.valid,
  apply hB.indep,
  apply linear_independent.image_of_comp B φ coe h8,
end

lemma of_rank_set (φ : rep 𝔽 M ι) [fintype 𝔽] (X : set E) [fintype (span 𝔽 (φ '' X))] :
  finite_dimensional.finrank 𝔽 (span 𝔽 (φ '' X)) = M.r X :=
begin
  cases M.exists_basis X with I hI,
  
  sorry,
end

lemma cl_subset_span_rep (φ : rep 𝔽 M ι) (X : set E): φ '' M.cl X ⊆ span 𝔽 (φ '' X) :=
begin
  cases M.exists_basis X with I hI,
  rw ← span_basis _ hI, 
  sorry,
end

end rep

section other_rep

variables {W W' : Type*} [add_comm_monoid W] [module 𝔽 W] [add_comm_monoid W'] [module 𝔽 W']

structure rep' (𝔽 W : Type*) [field 𝔽] [add_comm_monoid W] [module 𝔽 W] (M : matroid E) :=
(to_fun : E → W)
(valid : ∀ (I : set E), linear_independent 𝔽 (λ (e : I), to_fun (e : E)) ↔ M.indep I)

instance fun_like : fun_like (rep' 𝔽 W M) E (λ _, W) :=
{ coe := rep'.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

instance : has_coe_to_fun (rep' 𝔽 W M) (λ _, E → W) := fun_like.has_coe_to_fun

def rep'.to_submodule (φ : rep' 𝔽 W M) : submodule 𝔽 W := span 𝔽 (set.range φ)

-- def rep'.to_submodule_fun (φ : rep' 𝔽 W M) :

lemma rep'.mem_to_submodule (φ : rep' 𝔽 W M) (x : E) : φ x ∈ φ.to_submodule :=
by { rw [rep'.to_submodule], refine subset_span _, simp }

def rep'.compose (φ : rep' 𝔽 W M) (e : φ.to_submodule ≃ₗ[𝔽] W') : rep' 𝔽 W' M :=
{ to_fun := λ x, e ⟨φ x, φ.mem_to_submodule x⟩,
  valid :=
  begin
    intros I,
    rw [←φ.valid],
    rw linear_independent_image sorry,
    convert linear_map.linear_independent_iff e.to_linear_map sorry using 1,

    -- have := ((linear_equiv.refl 𝔽 W).to_linear_map.dom_restrict (φ.to_submodule)).linear_independent_iff sorry,
    rw ← iff_iff_eq,
    simp,
    
    
    --rw rep.valid φ,                      
    sorry,

    --rw linear_independent_equiv,
  end  }

end other_rep

-- lemma rep_equiv (𝔽 : Type*) [field 𝔽] (M : matroid E) (ι ι' : Type*) (φ : rep 𝔽 M ι)
-- (e : (ι → 𝔽))

-- i think we're doing something wrong, it can't be this complicated
lemma foo (φ : rep 𝔽 M ι) [fintype 𝔽] [fintype (span 𝔽 (set.range φ))] :
  nonempty (rep 𝔽 M (fin M.rk))  :=
begin
  have h1 := φ.of_rank,
  have h2 : finite_dimensional.finrank 𝔽 (fin M.rk → 𝔽) = M.rk, 
  simp,
  rw ← h2 at h1,
  rw ← finite_dimensional.nonempty_linear_equiv_iff_finrank_eq at h1,
  cases h1 with l,
  have h3 := λ (x : E), mem_of_subset_of_mem (@subset_span 𝔽 _ _ _ _ (range ⇑φ)) (mem_range_self x),
  use λ x, (l ⟨φ x, h3 x⟩),
  intros I,
  rw ← φ.valid,
  --rw linear_independent_equiv l.to_equiv,
  --refine ⟨λ h, _, λ h, _⟩,
  have h4 : linear_independent 𝔽 (λ (x : ↥I), φ x) ↔ linear_independent 𝔽 (λ (x : ↥I), (⟨φ x, h3 x⟩ : span 𝔽 (range ⇑φ))),
  have h8 : (λ (x : ↥I), φ x) = (λ (x : ↥I), ↑(⟨φ x, h3 x⟩ : (span 𝔽 (range ⇑φ)))),
  simp,
  rw h8,
  
  refine ⟨λ h, _, λ h, _⟩,
  /-have h5 := linear_independent_span h,
  simp at h5,
  simp_rw ← subtype_apply (span 𝔽 (range ⇑φ)) at h,
  have h7 := @linear_map.linear_independent_iff _ _ _ _ (λ (x : ↥I), (⟨φ x, h3 x⟩ : (span 𝔽 (range ⇑φ)))) _ _ _ _ _ (submodule.subtype (span 𝔽 (range ⇑φ))) sorry,
  simp at h7,-/
  sorry,
  
  
  
  --apply h5,  
  -- i think this is what i want but it gives me a deterministic timeout...
 -- have h5 := (linear_map.linear_independent_iff ((span 𝔽 (range φ)).subtype) _).2 h,
  --simp,
  --have h2 := linear_map.mem_submodule_image,
  --rw linear_map.linear_independent_iff l.to_linear_map,
  --convert linear_map.linear_independent_iff l.to_linear_map sorry using 1,
  --have h2 := gram_schmidt_linear_independent,
  sorry,
  sorry,
  --have h2 := @mem_range_self (ι → 𝔽) E φ x,
end

/- A matroid is binary if it has a `GF(2)`-representation -/
@[reducible, inline] def matroid.is_binary (M : matroid E) := M.is_representable (zmod 2)

lemma U24_simple : (canonical_unif 2 4).simple :=
begin
  sorry,
end

lemma U23_binary : (canonical_unif 2 3).is_binary :=
begin
  -- wait maybe i don't even need basis, maybe i could just map directly
  -- cardinality of U23 is 3
  -- cardinality of (fin 2 → zmod 2) \ {0} is 3
  -- just use any bijection between the two, show that it works
  have h1 := @fintype.card_fun (fin 2) (zmod 2) _ _ _,
  rw [zmod.card 2, fintype.card_fin] at h1,
  have h2 : fintype.card ((set.univ \ {0}) : set (fin 2 → zmod 2)) = 3, 
  --simp only [fintype.card_of_finset, mem_compl_iff, mem_singleton_iff, to_finset_univ],
  rw [← to_finset_card, to_finset_diff, finset.card_sdiff, to_finset_card univ],
  
  simp,
  sorry,
  simp only [to_finset_univ, to_finset_subset, finset.coe_univ, singleton_subset_iff],
  --rw ← fintype.card_fin 3 at h2,
  have f := equiv.symm (fintype.equiv_fin_of_card_eq h2),
  have φ := @rep.mk _ _ (zmod 2) _ (canonical_unif 2 3) (fin 2) (λ x, ↑(f.to_fun x)) _,
  rw [matroid.is_binary, is_representable],
  
  --use (fin 2) φ,
  sorry,
  intros I,
  refine ⟨λ h, _, λ h, _⟩,  
  -- now the possible sizes of vector families for h are 0, 1, 2.
  sorry,
  rw [canonical_unif, unif_indep_iff, le_iff_lt_or_eq] at h,
  cases h with h1 h2,
  have h4 := nat.le_of_lt_succ h1,
  rw le_iff_lt_or_eq at h4,
  cases h4 with h0 h1,
  have h5 := nat.lt_one_iff.1 h0,
  simp at h5,
  rw h5,
  simp,
  have h6 := (linear_independent_image sorry).2,
  --apply linear_independent_empty,
  sorry,
  -- want rep (zmod 2) M (fin M.rk)
  /-have B' := finite_dimensional.fin_basis (zmod 2) (fin 2 → zmod 2),
  cases (canonical_unif 2 3).exists_base with B h2,
  have h3 : 2 ≤ nat.card (fin 3) := by { simp only [nat.card_eq_fintype_card, fintype.card_fin, nat.bit0_le_bit1_iff] },
  rw [canonical_unif, unif_base_iff h3] at h2,
  have h4 := subset_univ B,
  have h5 := (fintype.card_fin 2),
  rw ← nat.card_eq_fintype_card at h5,
  -- plan is to map base elements to basis vectors and then third element
  -- to their linear combination
  have h6 : ∃ (a : fin 3), set.univ = B ∪ {a},
  sorry,
  have h7 : (finite_dimensional.finrank (zmod 2) (fin 2 → zmod 2)) = 2,
  simp,-/
  --have h2 := rep.mk,
  sorry,
end

-- this doesn't have sorry's but it relies on foo and U24_simple which do
lemma U24_nonbinary : ¬ (canonical_unif 2 4).is_binary :=
begin
  by_contra h2,
  rw [matroid.is_binary, is_representable] at h2,
  rcases h2 with ⟨ι, n⟩,
  cases n with φ,
  cases foo φ sorry sorry with φ,
  rw [canonical_unif, unif_rk] at φ,
  { have h8 := card_le_of_subset (φ.subset_nonzero_of_simple U24_simple),
    -- need basis
    have h9 := module.card_fintype (finite_dimensional.fin_basis (zmod 2)
      (span (zmod 2) (range φ))),
    rw [rep.of_rank, unif_rk] at h9,
    { -- there's probably a cleaner way to talk about the card of diff than going
      -- between fintype and finset cards
      simp_rw [← to_finset_card, to_finset_diff] at h8,
      rw finset.card_sdiff at h8,
      { simp only [set.to_finset_card, set_like.coe_sort_coe, card_singleton] at h8,
        simp only [fintype.card_of_finset, zmod.card, fintype.card_fin] at h9,
        rw h9 at h8,
        have h11 : fintype.card (range φ) = fintype.card (fin 4),
        rw card_range_of_injective (φ.injective_of_simple U24_simple),
        -- linarith doesn't see the contradiction unless I simplify the inequality
        simp only [h11, fintype.card_fin, pow_two, two_mul, nat.succ_add_sub_one] at h8,
        linarith },
      -- this comes from finset.card_sdiff, will make nicer later
      simp only [set.to_finset_subset, coe_to_finset, singleton_subset_iff,
        set_like.mem_coe, zero_mem] },
    -- this part comes from unif_rk needing 2 ≤ 4, will make nicer later
    simp only [nat.card_eq_fintype_card, fintype.card_fin, bit0_le_bit0,
      nat.one_le_bit0_iff, nat.lt_one_iff]},
  simp,
end

-- lemma foo (e f : E) (hne : e ≠ f) (h : M.r {e,f} = 1) :

end matroid

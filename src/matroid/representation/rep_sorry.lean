import analysis.inner_product_space.gram_schmidt_ortho
import data.zmod.basic
import linear_algebra.basis
import linear_algebra.linear_independent
import m_in.minor m_in.constructions
import m_in.erank
import m_in.equiv


universe u 
variables {α γ : Type} {β 𝔽 : Type*} {M : matroid_in α} {I B : set α} {x : α}
variables {W W' : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] [add_comm_group W'] [module 𝔽 W'] 

open function set submodule finite_dimensional

lemma set.injective_iff_forall_inj_on_pair {f : α → β} : injective f ↔ ∀ a b, inj_on f {a, b} :=
⟨λ h a b, h.inj_on _, λ h a b hab,
  h _ _ (mem_insert _ _) (mem_insert_of_mem _ $ mem_singleton _) hab⟩

noncomputable theory

 
open_locale classical


-- we should have semiring 𝔽 by default, idk why it doesn't see it
-- why did we have finite E and not fintype E?

namespace matroid_in

def loopless (M : matroid_in α) : Prop := ∀ S ⊆ M.E, S.ncard = 1 → M.indep S 

lemma simple.loopless (h : M.simple) : M.loopless := sorry

/- A `𝔽`-matroid_in representation is a map from the base of the matroid_in to `ι → 𝔽` such that a set -/
/-structure rep (𝔽 : Type*) [field 𝔽] (M : matroid_in α) (ι : Type) :=
(to_fun : α → ι → 𝔽)
(valid' : ∀ I : set α, linear_independent 𝔽 (λ e : I, to_fun e) ↔ M.indep I)

/-- `M` is `𝔽`-representable if it has an `𝔽`-representation. -/
def is_representable (𝔽 : Type*) [field 𝔽] (M : matroid_in α) : Prop := ∃ (ι : Type), nonempty (rep 𝔽 M ι)-/

-- this definition breaks injectivity of rep of simple matroids, i think we need
-- to restrict the domain
-- show that this is equivalent to the other definition
structure rep (𝔽 W : Type*) [field 𝔽] [add_comm_group W] [module 𝔽 W] (M : matroid_in α) :=
(to_fun : α → W)
(valid' : ∀ (I ⊆ M.E), linear_independent 𝔽 (to_fun ∘ coe : I → W) ↔ M.indep I)
(support : ∀ (e : α), e ∉ M.E → to_fun e = 0)

instance fun_like {𝔽 W : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] {M : matroid_in α } : 
  fun_like (rep 𝔽 W M) α (λ _, W) := 
{ coe := λ φ e, φ.to_fun e,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

instance : has_coe_to_fun (rep 𝔽 W M) (λ _, α → W) := fun_like.has_coe_to_fun

def is_representable (𝔽 : Type*) [field 𝔽] (M : matroid_in α) : Prop := 
  ∃ (B : set α) (hB : M.base B), nonempty (rep 𝔽 (B →₀ 𝔽) M)

def iso.rep (M : matroid_in α) (M' : matroid_in γ) (ψ : M' ≃i M) (φ : rep 𝔽 W M) : rep 𝔽 W M' := 
{ to_fun := λ a, if h : a ∈ M'.E then φ (ψ ⟨a, h⟩) else 0,
  valid' := λ I hI, 
    begin
      rw ψ.on_indep hI,
      sorry,
      /-have h2 : ((λ (a : α), dite (a ∈ M'.E) (λ (h : a ∈ M'.E), φ ↑(ψ ⟨a, h⟩)) 
        (λ (h : a ∉ M'.E), φ a)) ∘ coe) = 
        λ a : I, φ (ψ ⟨a, hI a.2⟩),  
        ext;
        simp only [comp_app],
        simp_rw [dite_eq_iff],
        left,
        simp only [exists_apply_eq_apply],
      rw h2,
      --simp only [← comp_app φ (λ e : I, ↑(ψ ⟨e, hI e.2⟩))],
      rw iso.image,
      sorry,
      -/
      /-have h4 := ψ.to_equiv,
      have h6 := λ a : I, (⟨a, hI a.2⟩ : M'.E),
        sorry, -/
     /- have h5 := @equiv.bij_on_image _ _ ψ.to_equiv (ψ.image I),-/
      /-have h5 := @equiv.mk M'.E M.E (λ A : set M'.E, 
        (⟨ψ.image (A : set α), ψ.image_subset_ground A⟩ : set M.E)) _ _ _,-/
      /-have h6 := ψ.to_equiv.image (λ e : M'.E, e.1 ∈ I),
      simp at h6,
      have h7 : ∀ e : I, e.1 ∈ ((λ (e : ↥(M'.E)), ↑e ∈ I) : set M'.E),-/
      /-
      simp only [left_inverse],
      refine λ x, ψ.preimage_image x,-/
      /-have h3 : ψ.image I ≃ I,
        
        --use ψ,
        sorry,
      --have h6 : inj_on ψ (I : set M.E),
      --rw φ.valid,-/
      /-rw ← φ.valid,
      --rw linear_independent_image,
      rw iso.image,
      have h4 : ∀ e : M'.E, e.1 ∈ I ↔ (ψ e).1 ∈ ψ.image I, 
        sorry,
      have h5 : ∀ e : I, (ψ ⟨e, hI e.2⟩).1 ∈ ψ.image I,
        sorry,
      /-have h6 : ψ.to_equiv '' I = ψ.image I,
        sorry,-/
      rw [← image_comp],
      simp only [← comp_app φ _],-/
      
      
      --rw [← @linear_independent_image _ _ _ _ _ _ _ (coe : M.E → α)],
     /- have h4 : (φ ∘ (λ e : I, ↑(ψ ⟨e, hI e.2⟩))) = λ (e : ↥(coe ∘ ψ '' (coe ⁻¹' I))), φ ↑e,
        ext;
        simp only [comp_app],
        have h5 : ((ψ ⟨↑(h3 x), hI (h3 x).2⟩) : α) = x,
          
          sorry,
        sorry,-/
     -- have h5 := @linear_independent_equiv M'.E M.E 𝔽 W _ _ _ ψ.to_equiv (M.E.restrict φ),
      
      /-have h3 : (λ (a : ↥I), φ ↑(ψ ⟨↑a, _⟩)) ∘ h3 = (λ (e : ↥(ψ.image I)), φ ↑e),
        intros,-/
      
      --have h3 : (λ (a : ↥I), φ (ψ ⟨a, hI a.2⟩)) = (λ (e : ↥(ψ.image I)), φ ↑e),
      --rw linear_independent_equiv ψ,
      --rw linear_map.linear_independent_iff,
      /-have h2 : ((λ (a : α), dite (a ∈ M'.E) (λ (h : a ∈ M'.E), φ ↑(ψ ⟨a, h⟩)) 
        (λ (h : a ∉ M'.E), φ a)) ∘ coe) = 
        λ a : I, φ (ψ ⟨a, hI a.2⟩),  
        ext;
        simp,
        simp_rw [dite_eq_iff],
        left,
        simp only [exists_apply_eq_apply],
      rw h2,
      rw ← φ.valid,
      have h3 : (λ (e : ↥(ψ.image I)), φ ↑e) = λ a : I, φ (ψ ⟨a, hI a.2⟩),  
        sorry,-/
    end,
  support := sorry } 

lemma vandermonde_rep [fintype 𝔽] (a n : ℕ) (hn : n ≤ nat.card 𝔽) : 
  is_representable 𝔽 (unif (a + 1) n) := 
begin
  -- Choose a matrix with rows (`fin a`) and columns of the form (x^0, x^1, ... x_i^{a-1}) for 
  -- distinct `x ∈ 𝔽`, and one extra column `(0,0,...,1)`. This is (pretty much) a Vandermonde 
  -- matrix, so all its a × a subdeterminants are nonsingular - see
  -- https://leanprover-community.github.io/mathlib_docs/linear_algebra/vandermonde.html#matrix.vandermonde. 
  -- it follows that the matroid it represents is uniform. 
  sorry,
end 

def add_coloop (M : matroid_in α) {f : α} (hf : f ∉ M.E) : matroid_in α := 
{ ground := M.E ∪ {f},
  base := λ B, M.base (B \ {f} : set α) ∧ f ∈ B,
  exists_base' := 
    begin
      obtain ⟨B, hB⟩ := M.exists_base,
      use B ∪ {f},
      simp only [union_singleton, insert_diff_of_mem, mem_singleton, mem_insert_iff, 
        eq_self_iff_true, true_or, and_true],
      rw diff_singleton_eq_self (not_mem_subset hB.subset_ground hf),
      apply hB,
    end,
  base_exchange' := sorry,
  maximality := sorry,
  subset_ground' := λ B hB, 
    begin
      rw ← diff_union_of_subset (singleton_subset_iff.2 hB.2),
      apply union_subset_union hB.1.subset_ground,
      simp only [subset_singleton_iff, mem_singleton_iff, imp_self, implies_true_iff],
    end }

lemma add_coloop_equal (M M' : matroid_in α) {f : α} (hf : f ∉ M.E) : 
  M' = add_coloop M hf ↔ M'.coloop f ∧ M' ⟍ f = M := sorry 

lemma add_coloop_del_equal (M : matroid_in α) {f : α} (hf : f ∉ M.E) :
  M = add_coloop M hf ⟍ f := sorry

def series_extend (M : matroid_in α) {e f : α} (he : e ∈ M.E) 
  (hf : f ∉ M.E) (hMe : ¬ M.coloop e) : matroid_in α := 
{ ground := insert f M.E,
  -- M.base B covers e ∈ B
  base := sorry,
  exists_base' := sorry,
  base_exchange' := sorry,
  maximality := sorry,
  subset_ground' := sorry }

-- don't need hf but keeping for convenience
lemma series_extend_eq (M M' : matroid_in α) {e f : α} (hM' : M'.cocircuit {e, f}) (he : e ∈ M.E) 
  (h : M = M' ⟋ f) (hf : f ∉ M.E) (hMe : ¬ M.coloop e) : M' = series_extend M he hf hMe := sorry

lemma cocircuit_contr_elem_eq_series_extend (M : matroid_in α) {e f : α} (hM : M.cocircuit {e, f}) 
  (he : e ∈ (M ⟋ f).E) (hf : f ∉ (M ⟋ f).E) (hMe : ¬ (M ⟋ f).coloop e) : 
  series_extend (M ⟋ f) he hf hMe = M :=
begin
  sorry,
end

lemma series_extend_cocircuit (M : matroid_in α) {e f : α} (he : e ∈ M.E) (hMe : ¬ M.coloop e)
  (hf : f ∉ M.E) : (series_extend M he hf hMe).cocircuit {e, f} := sorry

lemma series_extend_contr_eq (M : matroid_in α) {e f : α} (he : e ∈ M.E) (hf : f ∉ M.E) 
  (hMe : ¬ M.coloop e) : M = (series_extend M he hf hMe) ⟋ f := sorry

def parallel_extend (M : matroid_in α) {e f : α} (hMe : M.nonloop e) (hf : f ∉ M.E) :
  matroid_in α := 
{ ground := insert f M.E,
  -- M.base B covers e ∈ B
  base := sorry,
  exists_base' := sorry,
  base_exchange' := sorry,
  maximality := sorry,
  subset_ground' := sorry }

-- don't need hf but keeping for convenience
lemma parallel_extend_eq (M M' : matroid_in α) {e f : α} (hM' : M'.circuit {e, f}) 
  (h : M = M' ⟍ f) (hMe : M.nonloop e) (hf : f ∉ M.E) : M' = parallel_extend M hMe hf := sorry

lemma circuit_delete_elem_eq_parallel_extend (M : matroid_in α) {e f : α} (hM : M.circuit {e, f}) 
  (hMe : (M ⟍ f).nonloop e) (hf : f ∉ (M ⟍ f).E) : 
  parallel_extend (M ⟍ f) hMe hf = M :=
begin
  sorry,
end

lemma parallel_extend_circuit (M : matroid_in α) {e f : α} (hMe : M.nonloop e)
  (hf : f ∉ M.E) : (parallel_extend M hMe hf).circuit {e, f} := sorry

lemma parallel_extend_delete_eq (M : matroid_in α) {e f : α} (hMe : M.nonloop e) (hf : f ∉ M.E) 
  : M = (parallel_extend M hMe hf) ⟍ f := sorry

lemma series_pair_mem_circuit (x y : α) (C : set α) (hMC : M.circuit C) (hMxy : M.cocircuit {x, y}) 
  : x ∈ C ↔ y ∈ C :=
begin
  refine ⟨_, _⟩,
  sorry,
  sorry,
end

lemma U24_simple : (unif 2 4).simple := sorry

lemma unif_iso_minor {n m k : ℕ} (hjk : m ≤ n) : unif k m ≤i unif k n := sorry

end matroid_in
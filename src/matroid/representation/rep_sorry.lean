import analysis.inner_product_space.gram_schmidt_ortho
import data.zmod.basic
import linear_algebra.basis
import linear_algebra.linear_independent
import m_in.minor m_in.constructions
import m_in.erank
import m_in.equiv


universe u 
variables {α : Type} {β 𝔽 : Type*} {M : matroid_in α} {I B : set α} {x : α}
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

namespace rep 

def iso.rep (M M' : matroid_in α) (ψ : M' ≃i M) (φ : rep 𝔽 W M) : rep 𝔽 W M' := 
{ to_fun := λ a, if h : a ∈ M'.E then φ (ψ ⟨a, h⟩) else φ a,
  valid' := λ I hI, 
    begin
      rw ψ.on_indep hI,
      have h2 : ((λ (a : α), dite (a ∈ M'.E) (λ (h : a ∈ M'.E), φ ↑(ψ ⟨a, h⟩)) 
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
  support := _ } 

end rep

end matroid_in
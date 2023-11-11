import analysis.inner_product_space.gram_schmidt_ortho
import data.zmod.basic
import linear_algebra.basis
import linear_algebra.linear_independent
import m_in.minor m_in.constructions
import m_in.erank
import m_in.equiv
import m_in.preimage


universe u 
variables {α γ : Type} {β 𝔽 : Type*} {M : matroid_in α} {I B : set α} {x : α}
variables {W W' : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] [add_comm_group W'] [module 𝔽 W'] 

open function set submodule finite_dimensional

lemma set.injective_iff_forall_inj_on_pair {f : α → β} : injective f ↔ ∀ a b, inj_on f {a, b} :=
⟨λ h a b, h.inj_on _, λ h a b hab,
  h _ _ (mem_insert _ _) (mem_insert_of_mem _ $ mem_singleton _) hab⟩

noncomputable theory

 
open_locale classical

namespace matroid_in

def loopless (M : matroid_in α) : Prop := ∀ S ⊆ M.E, S.ncard = 1 → M.indep S 

lemma simple.loopless (h : M.simple) : M.loopless := sorry

structure rep (𝔽 W : Type*) [field 𝔽] [add_comm_group W] [module 𝔽 W] (M : matroid_in α) :=
(to_fun : α → W)
(valid' : ∀ (I ⊆ M.E), linear_independent 𝔽 (to_fun ∘ coe : I → W) ↔ M.indep I)
(support : ∀ (e : α), e ∉ M.E → to_fun e = 0)

instance fun_like {𝔽 W : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] {M : matroid_in α } : 
  fun_like (rep 𝔽 W M) α (λ _, W) := 
{ coe := λ φ e, φ.to_fun e,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

instance : has_coe_to_fun (rep 𝔽 W M) (λ _, α → W) := fun_like.has_coe_to_fun


lemma rep.valid (φ : rep 𝔽 W M) {I : set α} : linear_independent 𝔽 (λ e : I, φ e) ↔ M.indep I := 
begin
  refine (em (I ⊆ M.E)).elim (φ.valid' _) (fun hIE, _), 
  obtain ⟨e, heI, heE⟩ := not_subset.1 hIE,  
  exact iff_of_false (fun hli, hli.ne_zero ⟨e, heI⟩ (φ.support _ heE)) 
    (fun hI, hIE hI.subset_ground), 
end 

def is_representable (𝔽 : Type*) [field 𝔽] (M : matroid_in α) : Prop := 
  ∃ (B : set α) (hB : M.base B), nonempty (rep 𝔽 (B →₀ 𝔽) M)

def iso.rep (M : matroid_in α) (M' : matroid_in γ) (ψ : M' ≃i M) (v : rep 𝔽 W M) : rep 𝔽 W M' := 
{ to_fun := function.extend coe (fun (x : M'.E), v (ψ x)) 0,
  valid' := λ I hI, 
    begin
      set eI : I → ψ.image I := λ x, ⟨ψ ⟨x,hI x.2⟩, ⟨_,mem_image_of_mem _ (by simp), rfl⟩⟩ with heI,
      have hbij : bijective eI, 
      { refine ⟨fun x y hxy, _, fun x, _⟩, 
        { rwa [heI, subtype.mk_eq_mk, subtype.coe_inj, (equiv_like.injective ψ).eq_iff, 
            subtype.mk_eq_mk, subtype.coe_inj] at hxy },
        obtain ⟨_, ⟨_, ⟨z,hz,rfl⟩, rfl⟩⟩ := x,
        exact ⟨⟨z,hz⟩, by simp⟩ },
      rw [ψ.on_indep hI, ← v.valid ],
      refine linear_independent_equiv' (equiv.of_bijective _ hbij) _, 
      ext, 
      simp only [comp_app, equiv.of_bijective_apply, subtype.coe_mk], 
      exact ((@subtype.coe_injective _ M'.E).extend_apply (λ x, v (ψ x)) 0 (inclusion hI x)).symm,
    end,
  support := 
    begin
      rintro e he, 
      rw [extend_apply', pi.zero_apply], 
      rintro ⟨a,rfl⟩, 
      exact he a.2, 
    end } 

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
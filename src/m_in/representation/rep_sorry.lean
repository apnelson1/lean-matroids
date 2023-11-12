import analysis.inner_product_space.gram_schmidt_ortho
import data.zmod.basic
import linear_algebra.basis
import linear_algebra.linear_independent
import m_in.minor m_in.constructions
import m_in.erank
import m_in.equiv
-- import m_in.preimage
import m_in.simple 

universe u
variables {α γ : Type} {β 𝔽 : Type*} {M : matroid_in α} {I B : set α} {e x : α}
variables {W W' : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] [add_comm_group W'] [module 𝔽 W']

open function set submodule finite_dimensional

lemma set.injective_iff_forall_inj_on_pair {f : α → β} : injective f ↔ ∀ a b, inj_on f {a, b} :=
⟨λ h a b, h.inj_on _, λ h a b hab,
  h _ _ (mem_insert _ _) (mem_insert_of_mem _ $ mem_singleton _) hab⟩

noncomputable theory 

open_locale classical

namespace matroid_in

/- Alena : this stuff is now in `simple.lean` -/

-- def loopless (M : matroid_in α) : Prop := ∀ e, ¬ M.loop e 

-- def simple (M : matroid_in α) : Prop := ∀ (e ∈ M.E) (f ∈ M.E), M.indep {e, f}

-- lemma loopless.nonloop (h : M.loopless) (he : e ∈ M.E) : M.nonloop e := 
-- by { rw [← not_loop_iff], exact h e }

-- lemma simple.loopless (h : M.simple) : M.loopless :=
-- begin
--   refine fun e he, (loop_iff_dep.1 he).not_indep _, 
--   convert h e he.mem_ground e he.mem_ground, 
--   rw [pair_eq_singleton], 
-- end 

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

/- Alena : all the stuff you need for parallel/series extensions and adding loops/coloops is in 
  `single_extensions.lean`. I cleaned up the definitions and lemma statements in your sorrys to 
  remove extraneous assumptions, so I haven't filled them in exactly as you wrote them, but
  everything is substantially there. 
-/
 

-- -- don't need hf but keeping for convenience
-- lemma series_extend_eq (M M' : matroid_in α) {e f : α} (hM' : M'.cocircuit {e, f}) (he : e ∈ M.E)
--   (h : M = M' ⟋ f) (hf : f ∉ M.E) (hMe : ¬ M.coloop e) : M' = series_extend M he hf hMe := sorry

-- lemma cocircuit_contr_elem_eq_series_extend (M : matroid_in α) {e f : α} (hM : M.cocircuit {e, f})
--   (he : e ∈ (M ⟋ f).E) (hf : f ∉ (M ⟋ f).E) (hMe : ¬ (M ⟋ f).coloop e) :
--   series_extend (M ⟋ f) he hf hMe = M :=
-- begin
--   sorry,
-- end

-- lemma series_extend_cocircuit (M : matroid_in α) {e f : α} (he : e ∈ M.E) (hMe : ¬ M.coloop e)
--   (hf : f ∉ M.E) : (series_extend M he hf hMe).cocircuit {e, f} := sorry

-- lemma series_extend_contr_eq (M : matroid_in α) {e f : α} (he : e ∈ M.E) (hf : f ∉ M.E)
--   (hMe : ¬ M.coloop e) : M = (series_extend M he hf hMe) ⟋ f := sorry

-- def parallel_extend (M : matroid_in α) {e f : α} (hMe : M.nonloop e) (hf : f ∉ M.E) :
--   matroid_in α :=
-- { ground := insert f M.E,
--   -- M.base B covers e ∈ B
--   base := sorry,
--   exists_base' := sorry,
--   base_exchange' := sorry,
--   maximality := sorry,
--   subset_ground' := sorry }

-- -- don't need hf but keeping for convenience
-- lemma parallel_extend_eq (M M' : matroid_in α) {e f : α} (hM' : M'.circuit {e, f})
--   (h : M = M' ⟍ f) (hMe : M.nonloop e) (hf : f ∉ M.E) : M' = parallel_extend M hMe hf := sorry

-- lemma circuit_delete_elem_eq_parallel_extend (M : matroid_in α) {e f : α} (hM : M.circuit {e, f})
--   (hMe : (M ⟍ f).nonloop e) (hf : f ∉ (M ⟍ f).E) :
--   parallel_extend (M ⟍ f) hMe hf = M :=
-- begin
--   sorry,
-- end

-- lemma parallel_extend_circuit (M : matroid_in α) {e f : α} (hMe : M.nonloop e)
--   (hf : f ∉ M.E) : (parallel_extend M hMe hf).circuit {e, f} := sorry

-- lemma parallel_extend_delete_eq (M : matroid_in α) {e f : α} (hMe : M.nonloop e) (hf : f ∉ M.E)
--   : M = (parallel_extend M hMe hf) ⟍ f := sorry

lemma series_pair_mem_circuit (x y : α) (C : set α) (hMC : M.circuit C) 
  (hMxy : M.cocircuit {x, y}) : x ∈ C ↔ y ∈ C :=
begin
  suffices h : ∀ (M' : matroid_in α) {x' y' C'}, 
    M'.cocircuit C' → M'.circuit {x',y'} → x' ∈ C' → y' ∈ C', 
  { rw [← dual_circuit_iff_cocircuit] at hMxy, 
    rw [ ←dual_dual M, dual_circuit_iff_cocircuit] at hMC,  
    exact ⟨h M﹡ hMC hMxy, h M﹡ hMC (by rwa [pair_comm])⟩ },
  clear hMC C hMxy x y M, 
  refine fun M e f C hC hef heC, by_contra (fun hfC, _), 
  obtain (rfl | hne) := eq_or_ne e f, exact hfC heC, 
  rw [← compl_hyperplane_iff_cocircuit] at hC, 
  have hss : {e,f} \ {e} ⊆ M.E \ C, 
  { simp only [insert_diff_of_mem, mem_singleton, diff_singleton_subset_iff, singleton_subset_iff, 
      mem_insert_iff, mem_diff], 
    exact or.inr ⟨hef.subset_ground (or.inr rfl), hfC⟩ },
  
  have hcon := (hef.subset_cl_diff_singleton e).trans (M.cl_subset hss) (or.inl rfl), 
  rw [hC.flat.cl] at hcon, 
  exact hcon.2 heC,
end

lemma unif_simple (a b : ℕ) (ha : 2 ≤ a) : (unif a b).simple := 
begin
  rintro e - f -, 
  simp only [unif_indep_iff', nat.cast_bit0, enat.coe_one],
  have hfin : ({e,f} : set (fin b)).finite := ((finite_singleton _).insert _),
  rw [encard_le_coe_iff, and_iff_right hfin],
  refine le_trans _ ha, 
  obtain (rfl | hne) := eq_or_ne e f, simp, 
  rw [ncard_pair hne], 
end  

lemma U24_simple : (unif 2 4).simple := 
  unif_simple 2 4 rfl.le

lemma unif_iso_minor {n m k : ℕ} (hjk : m ≤ n) : unif k m ≤i unif k n :=
begin
  set D : set (fin n) := (range (fin.cast_le hjk))ᶜ with hD, 

  have hecard : (range (fin.cast_le hjk)).encard = m,
  { rw [←image_univ,  encard_image_of_injective], 
    { rw [encard_eq_coe_iff, ncard_univ, nat.card_eq_fintype_card, 
        and_iff_left (fintype.card_fin _)],
      exact univ.to_finite },
    exact rel_embedding.injective (fin.cast_le hjk) },
    
  refine ⟨(unif k n) ⟍  D, delete_minor _ _, ⟨iso.symm (nonempty.some _)⟩⟩, 
  rw [iso_unif_iff, delete_ground, unif_ground_eq, ← compl_eq_univ_diff, hD, compl_compl, 
    and_iff_left hecard, eq_iff_indep_iff_indep_forall], 
  simp [restrict_ground_eq', encard_le_coe_iff, and_assoc],
end 

end matroid_in

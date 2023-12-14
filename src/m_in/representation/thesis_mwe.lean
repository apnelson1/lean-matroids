import analysis.inner_product_space.gram_schmidt_ortho
import data.zmod.basic data.finsupp.fintype
import linear_algebra.basis
import linear_algebra.linear_independent
import m_in.minor m_in.constructions
import m_in.erank
import m_in.equiv
import m_in.single_extensions
import m_in.simple 

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

namespace rep

section matroid_lemmas

lemma contract_circuit_of_insert_circuit (e : α) (C : set α) (he : M.nonloop e) (heC : e ∉ C)
  (hMCe : M.circuit (insert e C)) : (M ⟋ e).circuit C :=
begin
  simp_rw [circuit_iff_forall_ssubset, contract_elem] at *,
  refine ⟨_, λ I hI, _⟩,
  rw [he.indep.contract_dep_iff, union_singleton],
  refine ⟨disjoint_singleton_right.2 heC, hMCe.1⟩,
  rw he.indep.contract_indep_iff,
  refine ⟨disjoint_singleton_right.2 (not_mem_subset (subset_of_ssubset hI) heC), _⟩,
  have h8 : insert e I ⊂ insert e C,
    obtain ⟨a, ⟨haI, haIC⟩⟩ := ssubset_iff_insert.1 hI,
    have ha : ¬(a = e ∨ a ∈ I),
    { push_neg,
      refine ⟨ne_of_mem_of_not_mem (mem_of_mem_of_subset (mem_insert _ I) haIC) heC, haI⟩ },
    apply ssubset_iff_insert.2 ⟨a, ⟨mem_insert_iff.1.mt ha, _⟩⟩,
    rw insert_comm,
    apply insert_subset_insert haIC,
  rw union_singleton,
  apply hMCe.2 _ h8,
end

lemma coindep.base_of_basis_del {X : set α} (hX : M.coindep X) (hB : M.basis B (M.E \ X)) : 
  M.base B :=
begin
  obtain ⟨B',hB'⟩ := hX.exists_disjoint_base, 
  apply hB'.1.base_of_basis_supset (subset_diff.2 ⟨hB'.1.subset_ground, disjoint.symm hB'.2⟩) hB, 
end 

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

end matroid_lemmas

section unif_lemmas 

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

lemma delete_elem_unif (k n : ℕ) (e : fin (n + 1)) : nonempty (unif k (n + 1) ⟍ e ≃i unif k n) := 
begin
  rw [iso_unif_iff, delete_elem, eq_iff_indep_iff_indep_forall, delete_ground, unif_ground_eq, 
    encard_eq_coe_iff, ncard_diff (singleton_subset_iff.2 (mem_univ e)), ncard_singleton, 
    ncard_univ, nat.card_eq_fintype_card, fintype.card_fin, nat.add_succ_sub_one, add_zero],
  refine ⟨⟨rfl, λ I hI, _⟩, ⟨finite.diff (@univ (fin (n + 1))).to_finite {e}, rfl⟩⟩,
  simp only [← compl_eq_univ_diff, delete_indep_iff, unif_indep_iff', disjoint_singleton_right, 
    set.unif_on_indep_iff, subset_compl_singleton_iff, encard_le_coe_iff, and_assoc],
end

lemma contract_elem_unif (k n : ℕ) (e : fin (n + 1)) : 
  nonempty (unif (k + 1) (n + 1) ⟋ e ≃i unif k n) :=
begin
  rw [iso_unif_iff, contract_elem, eq_iff_indep_iff_indep_forall, contract_ground, unif_ground_eq, 
    encard_eq_coe_iff, ncard_diff (singleton_subset_iff.2 (mem_univ e)), ncard_singleton, 
    ncard_univ, nat.card_eq_fintype_card, fintype.card_fin, nat.add_succ_sub_one, add_zero],
  refine ⟨⟨rfl, λ I hI, _⟩, ⟨finite.diff (@univ (fin (n + 1))).to_finite {e}, rfl⟩⟩,
  simp only [← compl_eq_univ_diff],
  rw [indep.contract_indep_iff, unif_indep_iff', disjoint_singleton_right, set.unif_on_indep_iff, 
    subset_compl_singleton_iff, encard_le_coe_iff, union_singleton, and_comm, ← and_assoc],
  refine ⟨λ h, ⟨_, h.2⟩, λ h, ⟨_, h.2⟩⟩,
  { refine ⟨h.1.1.subset (subset_insert _ _), _⟩,
    rw [← add_le_add_iff_right 1, ← ncard_insert_of_not_mem h.2],
    apply h.1.2 },
  { refine ⟨h.1.1.insert _, _⟩,
    rw [ncard_insert_of_not_mem h.2, add_le_add_iff_right],
    apply h.1.2 },
  simp only [unif_indep_iff, ncard_singleton, le_add_iff_nonneg_left, zero_le'],
end

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

end unif_lemmas

section linear_independent_lemmas

lemma linear_independent.map'' {ι : Type*} {v : ι → W} (hv : linear_independent 𝔽 v) (f : W →ₗ[𝔽] W')
   (hfv : linear_independent 𝔽 (f ∘ v)) : disjoint (span 𝔽 (range v)) f.ker :=
begin
  rw [disjoint_iff_inf_le, ← set.image_univ, finsupp.span_image_eq_map_total,
    map_inf_eq_map_inf_comap, map_le_iff_le_comap, comap_bot, finsupp.supported_univ, top_inf_eq],
  unfold linear_independent at hv hfv,
  rw [hv, le_bot_iff],
  haveI : inhabited W := ⟨0⟩,
  rw [finsupp.total_comp, @finsupp.lmap_domain_total _ _ 𝔽 _ _ _ _ _ _ _ _ _ _ f,
    linear_map.ker_comp (finsupp.total ι W 𝔽 v) f] at hfv,
  rw ← hfv, 
  exact λ _, rfl,
end

/-- If `f` is an injective linear map, then the family `f ∘ v` is linearly independent
if and only if the family `v` is linearly independent. -/
protected lemma linear_map.linear_independent_iff {ι : Type*} {v : ι → W} (f : W →ₗ[𝔽] W') :
  linear_independent 𝔽 (f ∘ v) ↔ linear_independent 𝔽 v ∧ disjoint (f.ker) (span 𝔽 (range v)) :=
⟨λ h, ⟨@linear_independent.of_comp _ _ _ W' _ _ _ 
  (@add_comm_group.to_add_comm_monoid W' _inst_4) _ _inst_5 f h, 
  disjoint.comm.1 (linear_independent.map'' (@linear_independent.of_comp _ _ _ W' _ _ _ 
  (@add_comm_group.to_add_comm_monoid W' _inst_4) _ _inst_5 f h) _ h)⟩, 
  λ h, linear_independent.map h.1 (disjoint.comm.1 h.2)⟩

lemma linear_independent.union' {s t : set W}
  (hs : linear_independent 𝔽 (λ x, x : s → W)) (ht : linear_independent 𝔽 (λ x, x : t → W))
  (hst : disjoint (span 𝔽 s) (span 𝔽 t)) (hst2 : linear_independent 𝔽 (λ x, x : (s ∪ t) → W))
    : disjoint s t := 
begin
  rw disjoint_def at hst,
  rw [set.disjoint_iff, subset_empty_iff, eq_empty_iff_forall_not_mem],
  intros x,
  by_contra,
  -- for some reason, it doesn't let me specialize directly here.
  have h20 := mem_of_subset_of_mem (subset_span) ((mem_inter_iff _ _ _).1 h).1,
  have h21 := mem_of_subset_of_mem (subset_span) ((mem_inter_iff _ _ _).1 h).2,
  specialize hst x h20 h21,
  apply @linear_independent.ne_zero _ 𝔽 W ((λ (x : (s ∪ t)), x)) _ _ _ _ 
    ⟨x, (mem_of_subset_of_mem (inter_subset_union s t) h)⟩ hst2,
  simp only [← hst, subtype.coe_mk],
end

lemma linear_independent.union'' {s t : set W}
  (hs : linear_independent 𝔽 (λ x, x : s → W)) (ht : linear_independent 𝔽 (λ x, x : t → W))
  (hst : disjoint s t) (hst2 : linear_independent 𝔽 (λ x, x : (s ∪ t) → W))
    :  disjoint (span 𝔽 s) (span 𝔽 t) := 
begin
  convert hst2.disjoint_span_image (show disjoint (coe ⁻¹' s) (coe ⁻¹' t), from _), 
  { rw [eq_comm, image_preimage_eq_iff, subtype.range_coe], apply subset_union_left },
  { rw [eq_comm, image_preimage_eq_iff, subtype.range_coe], apply subset_union_right },
  rw [set.disjoint_iff, subset_empty_iff] at ⊢ hst,
  rw [← preimage_inter, hst, preimage_empty],
end

end linear_independent_lemmas

section rep_lemmas

lemma inj_on_of_indep (φ : rep 𝔽 W M) (hI : M.indep I) : inj_on φ I :=
inj_on_iff_injective.2 ((φ.valid' I hI.subset_ground).2 hI).injective

@[simp] lemma to_fun_eq_coe (φ : rep 𝔽 W M) : φ.to_fun = (φ : α → W)  := by { ext, refl }

lemma support' {φ : rep 𝔽 W M} {e : α} (he : e ∉ M.E) : φ e = 0 := 
by { rw ← to_fun_eq_coe, apply φ.support _ he }

def rep_of_congr {M M' : matroid_in α} (φ : rep 𝔽 W M) (h : M = M') : rep 𝔽 W M' := 
{ to_fun := φ.to_fun,
  valid' := λ I hI, by { rw ← (eq_iff_indep_iff_indep_forall.1 h).1 at hI, 
    rw ← (eq_iff_indep_iff_indep_forall.1 h).2, apply φ.valid' I hI, apply hI },
  support := λ e he, by { rw ← (eq_iff_indep_iff_indep_forall.1 h).1 at he, apply φ.support e he } }

def rep_of_iso (M : matroid_in α) (M' : matroid_in γ) (ψ : M' ≃i M) (v : rep 𝔽 W M) : rep 𝔽 W M' :=
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

lemma ne_zero_of_nonloop (φ : rep 𝔽 W M) (hx : M.nonloop x) : φ x ≠ 0 :=
((φ.valid' {x} (indep_singleton.2 hx).subset_ground).2 hx.indep).ne_zero 
(⟨x, mem_singleton _⟩ : ({x} : set α))

lemma ne_zero_of_loopless (φ : rep 𝔽 W M) (hl : loopless M) (x : α) (hx : x ∈ M.E) : φ x ≠ 0 :=
 φ.ne_zero_of_nonloop (hl x hx)

lemma inj_on_ground_of_simple (φ : rep 𝔽 W M) (hs : simple M) : inj_on φ M.E :=
λ a ha b hb,
begin
  apply φ.inj_on_of_indep (hs a ha b hb),
  simp only [mem_insert_iff, eq_self_iff_true, true_or],
  simp only [mem_insert_iff, eq_self_iff_true, mem_singleton, or_true],
end

lemma subset_nonzero_of_simple (φ : rep 𝔽 W M) (hs : simple M) :
  φ '' M.E ⊆ span 𝔽 (φ '' M.E) \ {0} :=
begin
  refine subset_diff.2 ⟨subset_span, disjoint_left.2 _⟩,
  rintro x ⟨y, ⟨hy1, rfl⟩⟩,
  apply ne_zero_of_loopless _ hs.loopless _ hy1,
end

lemma of_basis (φ : rep 𝔽 W M) {X I : set α} (hI : M.basis I X) {e : α} (he : e ∈ X): 
  φ e ∈ span 𝔽 (φ '' I) :=
begin
  by_cases e ∈ I, 
  { apply subset_span (mem_image_of_mem _ h) },
  have h2 : ¬ linear_independent 𝔽 (λ x : insert e I, φ x) := (φ.valid' (insert e I) 
  (insert_subset.2 ⟨(mem_of_mem_of_subset he hI.subset_ground), hI.subset_ground_left⟩)).not.2 
  (dep_iff.1 (hI.insert_dep (mem_diff_of_mem he h))).1,
  contrapose! h2,
  apply (linear_independent_insert' h).2 ⟨(φ.valid' I hI.subset_ground_left).2 hI.indep, h2⟩,
end

lemma span_basis (φ : rep 𝔽 W M) {X I : set α} (hI : M.basis I X) : 
  span 𝔽 (φ '' I) = span 𝔽 (φ '' X) :=
begin
  refine (span_mono $ image_subset _ (basis.subset hI)).antisymm (span_le.2 _),
  rintros _ ⟨y, ⟨hy1, rfl⟩⟩,
  apply of_basis φ hI hy1,
end

lemma span_base (φ : rep 𝔽 W M) (hB : M.base B) : span 𝔽 (φ '' B) = span 𝔽 (φ '' M.E) := 
  by { rw [span_basis φ (base.basis_ground hB)] }

@[simp] lemma mem_span_rep_range (φ : rep 𝔽 W M) : ∀ (x : α), φ x ∈ (span 𝔽 (range ⇑φ)) := 
  λ x, by { apply mem_of_subset_of_mem (@subset_span 𝔽 _ _ _ _ (range ⇑φ)) (mem_range_self x) }

@[simp] lemma mem_span_rep (φ : rep 𝔽 W M) : ∀ (x : α) , φ x ∈ (span 𝔽 (φ '' M.E)) := 
  λ x, by { by_cases x ∈ M.E, 
apply mem_of_subset_of_mem (@subset_span 𝔽 _ _ _ _ (φ '' M.E)) (mem_image_of_mem φ h),
simp only [support' h, submodule.zero_mem] }

@[simp]
lemma span_range_eq_span_image (φ : rep 𝔽 W M) : span 𝔽 (φ '' M.E) = span 𝔽 (range ⇑φ) :=
span_eq_span (λ x ⟨y, ⟨hx1, hx2⟩⟩, by {rw ← hx2, apply mem_span_rep_range φ y}) 
  (λ x ⟨y, hx⟩, by {rw ← hx, apply mem_span_rep φ y })

lemma span_range_base (φ : rep 𝔽 W M) (hB: M.base B) : 
  span 𝔽 (range (λ (e : ↥B), φ ↑e)) = span 𝔽 (range φ)  := 
begin
  rw [← span_range_eq_span_image, ← φ.span_base hB],
  have h2 : range (λ (e : ↥B), φ ↑e) = (⇑φ '' B),
    ext;
    refine ⟨λ ⟨y, hy⟩, by { simp only at hy, rw ← hy, apply mem_image_of_mem φ y.2}, λ hx, _⟩, 
    obtain ⟨y, ⟨hy1, rfl⟩⟩ := hx,
    simp only [mem_range, set_coe.exists, subtype.coe_mk, exists_prop],
    refine ⟨y, ⟨hy1, rfl⟩⟩,
  rw h2,
end

lemma fund_circuit_inter_eq_diff_of_not_mem (e : α) (he : e ∈ M.cl I) (h2 : e ∉ I) : 
  (M.fund_circuit e I ∩ I) = (M.fund_circuit e I \ {e}) :=
begin
  apply eq_of_subset_of_subset,
  rw [diff_eq, compl_eq_univ_diff],
  apply inter_subset_inter (subset.refl _) (subset_diff_singleton (subset_univ I) h2),
  apply subset_inter (diff_subset _ _),
  apply (@insert_subset_insert_iff _ _ ((M.fund_circuit e I) \ {e}) I 
    (not_mem_diff_singleton e (M.fund_circuit e I))).1,
  rw [insert_diff_singleton, insert_eq_of_mem (mem_fund_circuit _ _ _)],
  apply fund_circuit_subset_insert he,
end

-- modify to disjoint union of circuits for iff?
lemma rep.circuit (φ : rep 𝔽 W M) {C : set α} (hMC : M.circuit C) : 
  ∃ f : α →₀ 𝔽, (f.support : set α) = C ∧ finsupp.total α W 𝔽 φ f = 0 ∧ f ≠ 0 :=
begin
  obtain ⟨f, ⟨hfssup, ⟨hftot, hfne0⟩⟩⟩ := 
    linear_dependent_comp_subtype'.1 (φ.valid.1.mt (not_indep_iff.2 hMC.dep)),
  refine ⟨f, ⟨_, ⟨hftot, hfne0⟩⟩⟩,
  apply subset.antisymm_iff.2 ⟨hfssup, λ x hx, _⟩,
  by_contra,
  apply φ.valid.2.mt 
    (linear_dependent_comp_subtype'.2 ⟨f, ⟨subset_diff_singleton hfssup h, ⟨hftot, hfne0⟩⟩⟩),
  apply hMC.diff_singleton_indep hx,
end

lemma mem_span_set_rep_of_not_mem (φ : rep 𝔽 W M) {I : set α} (hI : M.indep I) 
(e : α) (he : e ∈ M.cl I) (he2 : e ∉ I) :
 ∃ c : W →₀ 𝔽, (c.support : set W) = φ '' (M.fund_circuit e I \ {e}) ∧ 
  c.sum (λ mi r, r • mi) = φ e :=
begin
  obtain ⟨c, ⟨hc1, hc2⟩⟩ := mem_span_set.1 (of_basis φ (circuit.diff_singleton_basis 
    (indep.fund_circuit_circuit hI ((mem_diff e).2 ⟨he, he2⟩)) (M.mem_fund_circuit e I)) 
    (M.mem_fund_circuit e I)),
  refine ⟨c, ⟨subset.antisymm_iff.2 ⟨hc1, λ x hx, _⟩, hc2⟩⟩,
  obtain ⟨y, ⟨⟨hy1, hy2⟩, rfl⟩⟩ := hx,
  by_contra,
  have h5 : ∃ (c : W →₀ 𝔽), ↑(c.support) ⊆ ⇑φ '' (M.fund_circuit e I \ {e}) \ {φ y} ∧ 
    c.sum (λ (mi : W) (r : 𝔽), r • mi) = φ e,
  refine ⟨c, ⟨subset_diff_singleton hc1 h, hc2⟩⟩,
  have h8 : e ∈ ((M.fund_circuit e I) \ {y}),  
  { simp only [mem_diff, mem_singleton_iff],
    refine ⟨(M.mem_fund_circuit e I), ne.symm hy2⟩ },
  have h7 := (linear_independent_iff_not_mem_span.1 ((φ.valid' (M.fund_circuit e I \ {y}) 
    (subset.trans (diff_subset _ _) (fund_circuit_subset_ground he))).2 
    (circuit.diff_singleton_indep 
    (indep.fund_circuit_circuit hI ((mem_diff e).2 ⟨he, he2⟩)) hy1))) ⟨e, h8⟩,
  simp only [subtype.coe_mk, to_fun_eq_coe] at h7,
  rw [set.image_eta] at h7,
  have h9 : ((λ (a : ↥(M.fund_circuit e I \ {y})), φ ↑a) '' (univ \ {⟨e, h8⟩})) = 
    (⇑φ '' (M.fund_circuit e I \ {e}) \ {φ y}),
  { ext;
    refine ⟨λ h, _, λ h20, _⟩,  
    { simp only [mem_image, mem_diff, mem_univ, mem_singleton_iff, true_and, set_coe.exists, 
        subtype.mk_eq_mk, subtype.coe_mk, exists_prop] at h,
      obtain ⟨a, ⟨⟨ha1, ha2⟩, ⟨ha3, rfl⟩⟩⟩ := h,
      simp only [mem_diff, mem_image, mem_singleton_iff],
      use ⟨a, ⟨⟨ha1, ha3⟩, rfl⟩⟩,
      have h11 : (insert y {a}) ⊂ M.fund_circuit e I,
      rw ssubset_iff_subset_diff_singleton,
      refine ⟨e, ⟨(M.mem_fund_circuit e I), λ x hx, _⟩⟩,
      obtain ⟨rfl, rfl⟩ := hx,
      rw mem_diff_singleton,
      simp only [mem_singleton_iff] at hy2,
      refine ⟨hy1, hy2⟩,
      rw mem_diff_singleton,
      simp only [mem_singleton_iff] at hx,
      rw hx, 
      refine ⟨ha1, ha3⟩,
      have h10 := inj_on_of_indep φ 
        (circuit.ssubset_indep (indep.fund_circuit_circuit hI ((mem_diff e).2 ⟨he, he2⟩)) h11),
      apply (inj_on.ne_iff h10 _ _).2 ha2,
      simp only [mem_insert_iff, mem_singleton, or_true],
      simp only [mem_insert_iff, eq_self_iff_true, true_or]},
    { obtain ⟨⟨a, ⟨⟨ha1, ha2⟩, rfl⟩⟩, ha3⟩ := h20,
      use a,
      apply mem_diff_singleton.2 ⟨ha1, _⟩,
      simp only [mem_singleton_iff] at ha3,
      by_contra,
      rw h at ha3,
      apply ha3,
      refl,
      refine ⟨(mem_diff _).2 ⟨mem_univ _, mem_singleton_iff.1.mt (subtype.mk_eq_mk.1.mt ha2)⟩, _⟩,
      simp only [subtype.coe_mk]} },
  rw h9 at h7, 
  apply h7,
  exact mem_span_set.2 h5,
end

end rep_lemmas

section standard_rep_lemmas

/-- The representation for `M` whose rows are indexed by a base `B` -/
def standard_rep (φ' : rep 𝔽 W M) {B : set α} (hB : M.base B) : 
  rep 𝔽 (B →₀ 𝔽) M := 
{ to_fun := λ e : α, ((valid φ').2 hB.indep).repr ⟨φ' e, by
    { have h4 := φ'.mem_span_rep_range, rw ← span_range_base φ' hB at h4, exact h4 e}⟩,
  valid' := by 
  { intros I hI,
    rw [← @valid _ _ _ _ _ _ _ φ' I, 
      linear_map.linear_independent_iff ((valid φ').2 hB.indep).repr, 
      ←(submodule.subtype (span 𝔽 (range (λ (e : B), φ' ↑e)))).linear_independent_iff, 
         submodule.coe_subtype, and_iff_left],
    { refl }, 
    { simp only [linear_independent.repr_ker, disjoint_bot_left] },
    simp only [ker_subtype] },
  support := by
  { intros e he, simp_rw [support' he], convert _root_.map_zero _} }

@[simp]
lemma id_matrix_of_base (φ : rep 𝔽 W M) {B : set α} (e : B) (hB : M.base B) : 
  standard_rep φ hB e e = 1 :=
begin
  rw ← to_fun_eq_coe,
  simp [standard_rep],
  rw [((valid φ).2 hB.indep).repr_eq_single e ⟨φ e, by
    { have h4 := φ.mem_span_rep_range, rw ← span_range_base φ hB at h4, exact h4 e}⟩ rfl],
  simp only [finsupp.single_eq_same],
end 

lemma id_matrix_of_base' (φ : rep 𝔽 W M) {B : set α} (e f : B) (hB : M.base B) (hne : e ≠ f) : 
  standard_rep φ hB e f = 0 :=
begin
  rw ← to_fun_eq_coe,
  simp [standard_rep],
  rw [(φ.valid.2 hB.indep).repr_eq_single e ⟨φ e, by
    { have h4 := φ.mem_span_rep_range, rw ← span_range_base φ hB at h4, exact h4 e}⟩ rfl],
  apply finsupp.single_eq_of_ne hne,
end

lemma standard_rep_base_eq {M' : matroid_in α} (φ : rep 𝔽 W M) (φ' : rep 𝔽 W' M') {B : set α} 
(hB : M.base B) (hB' : M'.base B) (e : B) : standard_rep φ hB e = standard_rep φ' hB' e :=
begin
  ext;
  by_cases e = a, 
  simp_rw [h, id_matrix_of_base],
  simp_rw [id_matrix_of_base' φ e a hB h, id_matrix_of_base' φ' e a hB' h],
end

lemma standard_rep_eq_of_congr {M M' : matroid_in α} (φ : rep 𝔽 W M) (h : M = M') {B : set α} 
  (hMB : M.base B) (hMB' : M'.base B) : 
  ((standard_rep φ hMB) : α → B →₀ 𝔽) = (standard_rep (rep_of_congr φ h) hMB' :  α → B →₀ 𝔽) := rfl

/-- A representation over *any* module certifies representability-/
lemma is_representable_of_rep {W : Type*} [add_comm_group W] [module 𝔽 W] (φ : rep 𝔽 W M) : 
    is_representable 𝔽 M := 
  begin
    obtain ⟨B, hB⟩ := M.exists_base, 
    exact ⟨B, hB, ⟨standard_rep φ hB⟩⟩, 
  end

end standard_rep_lemmas

section matroid_of_module_fun

def matroid_of_module_fun (𝔽 W : Type*) {ι : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] 
  [finite_dimensional 𝔽 W] (v : ι → W) (ground : set ι) : 
  matroid_in ι := matroid_of_indep_of_bdd' ground 
  (λ (I : set ι), (linear_independent 𝔽 (λ x : I, v x)) ∧ I ⊆ ground)  
  begin
    rw [linear_independent_image (inj_on_empty _), image_empty],
    refine ⟨linear_independent_empty 𝔽 W, empty_subset ground⟩,
  end 
  begin
    intros I J hJ hIJ,
    have hIJ3 := linear_independent.injective hJ.1, 
    rw [← set.restrict, ← inj_on_iff_injective] at hIJ3,
    rw linear_independent_image hIJ3 at hJ,
    rw linear_independent_image (inj_on.mono hIJ hIJ3),
    refine ⟨linear_independent.mono (image_subset v hIJ) hJ.1, subset_trans hIJ hJ.2⟩,
  end 
  begin
    intros I J hI hJ hIJ,
    have h3 : ∃ x ∈ J, v x ∉ span 𝔽 (v '' I),
    { have hJ2 := linear_independent.injective hJ.1, 
      rw [← set.restrict, ← inj_on_iff_injective] at hJ2,
      rw linear_independent_image hJ2 at hJ,
      have hI2 := linear_independent.injective hI.1, 
      rw [← set.restrict, ← inj_on_iff_injective] at hI2,
      rw linear_independent_image hI2 at hI,
      haveI := finite.fintype (_root_.linear_independent.finite hI.1),
      haveI := finite.fintype (_root_.linear_independent.finite hJ.1),
      by_contra,
      push_neg at h,
      have h8 : ((v '' J).to_finite.to_finset) = (v '' J).to_finset,
        ext,
        simp only [finite.mem_to_finset, mem_to_finset],
      have h9 : ((v '' I).to_finite.to_finset) = (v '' I).to_finset,
        ext,
        simp only [finite.mem_to_finset, mem_to_finset],
      have h5 : (v '' I).ncard < (v '' J).ncard,
      { rwa [ncard_image_of_inj_on hJ2, ncard_image_of_inj_on hI2] },
      apply not_le_of_lt h5,
      rw [ncard_eq_to_finset_card, ncard_eq_to_finset_card, h8, h9, 
      ← finrank_span_set_eq_card (v '' I) hI.1, ← finrank_span_set_eq_card (v '' J) hJ.1],
      have h2 := (@span_le 𝔽 W _ _ _ (v '' J) (span 𝔽 (v '' I))).2 (λ j hj, _),
      swap,
      { obtain ⟨x, ⟨hx, rfl⟩⟩ := hj,
        apply h x hx },
      apply submodule.finrank_le_finrank_of_le h2 },
    obtain ⟨x, ⟨hx1, hx2⟩⟩ := h3,
    refine ⟨x, ⟨hx1, ⟨(mem_image_of_mem v).mt (not_mem_subset (subset_span) hx2), _⟩⟩⟩, 
    refine ⟨(linear_independent_insert' ((mem_image_of_mem v).mt 
      (not_mem_subset (subset_span) hx2))).2 ⟨hI.1, hx2⟩, insert_subset.2 
        ⟨(mem_of_subset_of_mem hJ.2 hx1), hI.2⟩⟩,
  end 
  begin
    refine ⟨finite_dimensional.finrank 𝔽 W, λ I hI, _⟩,
    have hI2 := linear_independent.injective hI.1, 
      rw [← set.restrict, ← inj_on_iff_injective] at hI2,
      rw linear_independent_image hI2 at hI,
    haveI := finite.fintype (_root_.linear_independent.finite hI.1),
    rw ← linear_independent_image hI2 at hI, 
    haveI := ((v '' I).to_finite.of_finite_image hI2).fintype,
    
    rw [ncard, nat.card_eq_fintype_card],
    refine ⟨to_finite I, fintype_card_le_finrank_of_linear_independent hI.1⟩,

  end
  (by { tauto })

lemma matroid_of_module_fun.ground (𝔽 W : Type*) {ι : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] 
  [finite_dimensional 𝔽 W] (v : ι → W) (ground : set ι) : 
    (matroid_of_module_fun 𝔽 W v ground).E = ground := 
begin
  rw [matroid_of_module_fun, matroid_of_indep_of_bdd', matroid_of_indep_of_bdd, 
    matroid_of_indep, matroid_of_base, ← ground_eq_E],
end

lemma matroid_of_module_fun_congr (𝔽 W : Type*) {ι : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] 
  [finite_dimensional 𝔽 W] (v w : ι → W) (ground : set ι) (hvw : ∀ (e : ι), e ∈ ground → v e = w e) :
  matroid_of_module_fun 𝔽 W v ground = matroid_of_module_fun 𝔽 W w ground :=
begin
  apply eq_of_indep_iff_indep_forall,
  simp only [matroid_of_module_fun.ground],
  intros I hI,
  simp only [matroid_of_module_fun, matroid_of_indep_of_bdd', matroid_of_indep_of_bdd_apply,
    λ e : I, hvw e (mem_of_mem_of_subset e.2 hI)],
end

lemma delete_matroid_of_module_fun (𝔽 W : Type*) {ι : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] 
  [finite_dimensional 𝔽 W] (v : ι → W) (ground : set ι) (D : set ι) : 
    matroid_of_module_fun 𝔽 W v (ground \ D) = (matroid_of_module_fun 𝔽 W v ground) ⟍ D :=
begin
  apply eq_of_indep_iff_indep_forall,
  simp only [delete_ground, matroid_of_module_fun.ground],
  intros I hI,
  simp only [delete_indep_iff, matroid_of_module_fun, matroid_of_indep_of_bdd', subset_diff, 
    matroid_of_indep_of_bdd_apply, and_assoc],
end

lemma matroid_of_module_fun_rep_eq (M : matroid_in α) (𝔽 W : Type*) [field 𝔽] [add_comm_group W] 
  [module 𝔽 W] [finite_dimensional 𝔽 W] (φ : rep 𝔽 W M) : 
  M = matroid_of_module_fun 𝔽 W φ M.E :=
begin
  apply eq_of_indep_iff_indep_forall _ (λ I hI, _),
  refl,
  have hset : (λ (x : ↥I), φ x) = (φ.to_fun ∘ coe),
  { ext, 
    simp only [comp_app],
    refl },
  rw [matroid_of_module_fun, matroid_of_indep_of_bdd'_apply, hset, φ.valid'], 
  refine ⟨λ h, ⟨h, hI⟩, λ h, h.1⟩, 
  apply hI,
end

def rep_of_matroid_of_module_fun (𝔽 W : Type*) {ι : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] 
  [finite_dimensional 𝔽 W] (v : ι → W) (ground : set ι) : rep 𝔽 W (matroid_of_module_fun 𝔽 W v ground) := 
{ to_fun := λ x, if x ∈ ground then v x else 0,
  valid' := λ I hI, by {simp only [matroid_of_module_fun, matroid_of_indep_of_bdd'_apply],
    rw matroid_of_module_fun.ground at hI, 
    have h2 : (λ (x : ι), if (x ∈ ground) then (v x) else 0) ∘ (coe : I → ι) = λ x : I, v x,
      ext;
      simp only [ite_eq_left_iff],
      contrapose,
      intros h,
      push_neg,
      apply mem_of_subset_of_mem hI x.2,
    rw h2,
    simp,
    intros h, 
    apply hI },
  support := λ e he, 
    begin
      simp only [ite_eq_iff],
      right,
      refine ⟨he, rfl⟩,
    end }

end matroid_of_module_fun

section binary_lemmas

/- A matroid_in is binary if it has a `GF(2)`-representation -/
@[reducible, inline] def matroid_in.is_binary (M : matroid_in α) := M.is_representable (zmod 2)

open_locale big_operators

lemma mem_sum_basis_zmod2_of_not_mem [fintype α] [module (zmod 2) W] (φ : rep (zmod 2) W M) 
{I : set α} (hI : M.indep I) (e : α) (he : e ∈ M.cl I) (heI : e ∉ I) :
  ∑ i in (M.fund_circuit e I \ {e}).to_finset, φ i = φ e :=
begin
  have h3 := subset_insert e (M.fund_circuit e I),
  obtain ⟨c, ⟨hc1, hc2⟩⟩ := mem_span_set_rep_of_not_mem φ hI e he heI,
  rw ← hc2, 
  have h4 : c.support = (φ '' (M.fund_circuit e I \ {e})).to_finset := 
    by { simp_rw [← hc1, finset.to_finset_coe] },
  have h7 : (∀ (i : W), i ∈ (⇑φ '' (M.fund_circuit e I \ {e})).to_finset → 
    (λ (mi : W) (r : zmod 2), r • mi) i 0 = 0),
  intros x hx,
  simp only [zero_smul],
  rw [finsupp.sum_of_support_subset c (finset.subset_of_eq h4) (λ mi r, r • mi) h7, 
    to_finset_image, to_finset_diff, finset.sum_image, finset.sum_congr],
  simp only [eq_self_iff_true],
  { intros x hx,
    simp only,
    haveI := (@add_comm_group.to_add_comm_monoid W _inst_2),
    -- for some reason i have to do this roundabout way of using one_smul because
    -- i can't figure out how to make my monoid instance work for it
    have hc : c (φ x) = 1,
    cases le_iff_lt_or_eq.1 (nat.le_of_lt_succ (zmod.val_lt (c (φ x)))) with h0 h1,
    { by_contra,
      simp only [nat.lt_one_iff, zmod.val_eq_zero] at h0,
      rw ← to_finset_diff at hx,
      have hφ := finset.mem_image_of_mem φ hx,
      rw [← to_finset_image, ← h4, finsupp.mem_support_iff, ne.def] at hφ,
      apply hφ,
      exact h0 },
    { rw [← zmod.nat_cast_zmod_val (c (φ x)), h1, algebra_map.coe_one] },
    rw hc,
    simp only [one_smul] },
  { simp_rw [←set.to_finset_diff, mem_to_finset],
    apply inj_on_of_indep φ (circuit.diff_singleton_indep 
      (indep.fund_circuit_circuit hI ((mem_diff e).2 ⟨he, heI⟩)) (M.mem_fund_circuit e I)) },
end

lemma mem_sum_basis_zmod2 [fintype α] [module (zmod 2) W] (φ : rep (zmod 2) W M) {I : set α} 
(hI : M.indep I) (e : α) (he : e ∈ M.cl I) :
  φ e = ∑ i in (M.fund_circuit e I ∩ I).to_finset, φ i :=
begin
  by_cases e ∈ I,
  rw [hI.fund_circuit_eq_of_mem h, @to_finset_congr _ ({e}∩I) {e} _ _ (singleton_inter_eq_of_mem h),
     to_finset_singleton, finset.sum_singleton],
  rw to_finset_congr (fund_circuit_inter_eq_diff_of_not_mem _ he h),
  apply eq.symm (mem_sum_basis_zmod2_of_not_mem φ hI e he h),
end

lemma eq_of_forall_fund_circuit_eq [fintype α] {M M' : matroid_in α} [module (zmod 2) W] 
[module (zmod 2) W'] (φM : rep (zmod 2) W M) (φM' : rep (zmod 2) W' M')
(hE : M.E = M'.E) (hB : M.base B) (hB' : M'.base B) 
(he : ∀ e ∈ M.E, M.fund_circuit e B = M'.fund_circuit e B) :
  M = M' :=
begin
  have φM := standard_rep φM hB,
  have φM' := standard_rep φM' hB',
  apply eq_of_indep_iff_indep_forall hE,
  intros I hI,
  have hI' := hI,
  rw hE at hI',
  rw [← (standard_rep φM hB).valid' _ hI, ← (standard_rep φM' hB').valid' _ hI'],
  have h2 : (standard_rep φM hB).to_fun ∘ coe = λ i : I, (standard_rep φM hB).to_fun i,
    simp only [eq_self_iff_true], 
  have h3 : (standard_rep φM' hB').to_fun ∘ coe = λ i : I, (standard_rep φM' hB').to_fun i,
    simp only [eq_self_iff_true],
  rw [h2, h3],
  simp only [to_fun_eq_coe],
  simp_rw [λ (e : I), (standard_rep φM hB).mem_sum_basis_zmod2 hB.indep _ (@base.mem_cl _ M B hB e (hI e.2)),
    λ (e : I), (standard_rep φM' hB').mem_sum_basis_zmod2 hB'.indep _ (@base.mem_cl _ M' B hB' e (hI' e.2))],
  simp_rw λ (e : I), he e (hI e.2),
  have h6 : (λ (i : ↥I), ∑ (x : α) in (M'.fund_circuit ↑i B ∩ B).to_finset, (standard_rep φM hB) x) 
    = (λ (i : ↥I), ∑ (x : α) in (M'.fund_circuit ↑i B ∩ B).to_finset, (standard_rep φM' hB') x),
    simp only,
    have h10 :=  λ (i : ↥I), @finset.sum_congr _ _ (M'.fund_circuit i B ∩ B).to_finset 
      (M'.fund_circuit i B ∩ B).to_finset (standard_rep φM hB) (standard_rep φM' hB') _ rfl _,
    simp_rw  [λ (i : I), h10 i],
    intros x hx,
    rw mem_to_finset at hx,
    have h12 := standard_rep_base_eq φM φM' hB hB' ⟨x, (mem_of_mem_inter_right hx)⟩,
    simp at h12,
    rw h12,
  simp_rw h6,
end 

-- part (iii) in the proof of theorem 6.5.4
lemma indep_eq_doubleton_of_subset [fintype α] (MI MC : matroid_in α) [finite_rk MI] [finite_rk MC] 
  (hrk : MI.rk = MC.rk) (hIC : MI.E = MC.E) (x y : α) (hxy : x ≠ y) 
  (hiIC : MI.coindep {x,y} ∨ MC.coindep {x,y}) (hMx : MI ⟍ x = MC ⟍ x) (hMy : MI ⟍ y = MC ⟍ y)
  {Z J : set α} (hxZ : x ∈ Z) (hyZ : y ∈ Z) (hMIZ : MI.indep Z) (hMCZ : ¬ MC.indep Z) 
  (hZJ : Z ⊆ J) (hMIJ : MI.indep J) [module (zmod 2) W] [module (zmod 2) W'] 
  (φI : rep (zmod 2) W (MI ⟋ (J \ {x, y})))
  (φC : rep (zmod 2) W' (MC ⟋ (J \ {x, y}))) : J = {x, y} :=
begin
  apply subset_antisymm _ (insert_subset.2 ⟨hZJ hxZ, singleton_subset_iff.2 (hZJ hyZ)⟩),
  rw ← diff_eq_empty,
  by_contra,
  --have hMIxy : (MI ⟍ {x, y}).indep (J \ {x, y}),
  rw [MI.delete_elem x, MC.delete_elem x] at hMx, --← delete_delete,
  rw [MI.delete_elem y, MC.delete_elem y] at hMy,
  have hMIxyJ := delete_indep_iff.2 ⟨hMIJ.subset (diff_subset J {x, y}), 
    @disjoint_sdiff_left _ {x, y} J⟩,
  have hMIxyJ2 := hMIxyJ,
  rw [← union_singleton, ← delete_delete, hMy, 
    delete_delete, union_singleton] at hMIxyJ2,
  -- i need something that tells me the rank of a matroid when you contract an independent set
  have hNIC : (MI ⟋ (J \ {x, y})).rk = (MC ⟋ (J \ {x, y})).rk,
    { -- this is due to M and M' having the same rank
      have h2 := MI.er_contract_add_er_eq_er_union (J \ {x, y}) (MI.E \ (J \ {x, y})),
      have h3 := MC.er_contract_add_er_eq_er_union (J \ {x, y}) (MC.E \ (J \ {x, y})),
      rw [union_comm, union_diff_cancel (subset_trans (diff_subset _ _) (hMIJ.subset_ground))] at h2,
      rw [union_comm, union_diff_cancel] at h3,
      have h4 : MI.er (J \ {x, y}) = MC.er (J \ {x, y}),
      { rw [← union_singleton, ← diff_diff, ← MI.delete_er_eq', ← MC.delete_er_eq', hMx] },
      rw [rk_def, rk_def, ← er_eq_coe_iff, eq_comm] at hrk,
      simp only [contract_ground, coe_r_eq_er] at hrk,
      rw [hrk, ← h2, h4] at h3,
      simp only [← coe_r_eq_er] at h3,
      simp only [← enat.coe_add] at h3,
      have h7 : ((MC ⟋ (J \ {x, y})).r (MC.E \ (J \ {x, y})) + MC.r (J \ {x, y})) = 
        ((MI ⟋ (J \ {x, y})).r (MI.E \ (J \ {x, y})) + MC.r (J \ {x, y})),
      { rwa [enat.coe_inj] at h3 },
      simp only [rk_def],
      rw eq_comm,
      simp only [contract_ground],
      apply nat.add_right_cancel h7,
      rw ← hIC,
      apply subset_trans (diff_subset _ _) (hMIJ.subset_ground) },
  have hNIneNC : (MI ⟋ (J \ {x, y})) ≠ (MC ⟋ (J \ {x, y})),
  { simp only [ne.def, eq_iff_indep_iff_indep_forall, contract_ground, hIC, eq_self_iff_true, 
      true_and, not_forall, exists_prop],
    refine ⟨{x, y}, ⟨_, _⟩⟩,
    { rw subset_diff,
      refine ⟨_, @disjoint_sdiff_right _ {x, y} J⟩,
      rw ← hIC, 
      apply (insert_subset.2 ⟨(hMIZ.subset_ground) hxZ, singleton_subset_iff.2 
        ((hMIZ.subset_ground) hyZ)⟩) },
    { rw [iff_def, not_and_distrib],
      left,
      push_neg,
      refine ⟨(indep.contract_indep_iff (hMIJ.subset (diff_subset J {x, y}))).2 
        ⟨@disjoint_sdiff_right _ {x, y} J, _⟩, _⟩,
      rw union_diff_cancel (insert_subset.2 ⟨hZJ hxZ, singleton_subset_iff.2 (hZJ hyZ)⟩),
      apply hMIJ,
      rw [indep.contract_indep_iff (hMIxyJ2.of_delete), not_and_distrib],
      right,
      rw union_diff_cancel (insert_subset.2 ⟨hZJ hxZ, singleton_subset_iff.2 (hZJ hyZ)⟩),
      apply indep.subset.mt (not_imp.2 ⟨hZJ, hMCZ⟩) } }, 
  obtain ⟨B, hNIxyB⟩ := (MI ⟋ (J \ {x, y}) ⟍ ({x, y} : set α)).exists_base,
    have hNCxyB := hNIxyB,
    rw [contract_delete_comm _ (@disjoint_sdiff_left _ {x, y} J), ← union_singleton, 
      ← delete_delete, hMy, delete_delete, union_singleton, 
      ← contract_delete_comm _ (@disjoint_sdiff_left _ {x, y} J)] at hNCxyB,
  have hB : (MI ⟋ (J \ {x, y})).base B ↔ (MC ⟋ (J \ {x, y})).base B,
  { refine ⟨λ hI, _, λ hC, _⟩,
    -- duplicate code, turn into lemma
    { by_contra h2,
      have hCB := hNCxyB.indep.of_delete,
      obtain ⟨B', hB'⟩ := (MC ⟋ (J \ ({x, y} : set α))).exists_base,
      rw [← hI.card] at hNIC,
      apply h2,
      apply hCB.base_of_rk_le_card,
      rw hNIC },
    { by_contra h2, 
      have hIB := hNIxyB.indep.of_delete,
      obtain ⟨B', hB'⟩ := (MI ⟋ (J \ ({x, y} : set α))).exists_base,
      rw [← hC.card] at hNIC,
      apply h2,
      apply hIB.base_of_rk_le_card,
      rw hNIC } },
  by_cases (MI ⟋ (J \ {x, y})).base B,
  { apply hNIneNC,
    have hfund : ∀ e ∈ (MI ⟋ (J \ {x, y})).E, (MI ⟋ (J \ {x, y})).fund_circuit e B 
      = (MC ⟋ (J \ {x, y})).fund_circuit e B, 
      intros e he,
      by_cases h2 : e = y,
      { rw h2 at *,
        have h3 : disjoint (insert y B) {x},
          apply disjoint_singleton_right.2 (mem_insert_iff.1.mt _),
          push_neg,
          refine ⟨hxy, _⟩,
          have h10 := hNIxyB.subset_ground,
          rw [delete_ground, ← union_singleton, ← diff_diff] at h10,
          apply not_mem_subset h10 (not_mem_diff_of_mem (mem_singleton x)),
        have h5 : disjoint (J \ {x, y}) {x},
          rw [← union_singleton, ← diff_diff],
          apply disjoint_sdiff_left,
        rw [← fund_circuit_delete h.indep (h.mem_cl y) h3, MI.contract_delete_comm h5, hMx,
            ← MC.contract_delete_comm h5], 
        rw [contract_ground, hIC, ← contract_ground] at he,
        rw fund_circuit_delete (hB.1 h).indep ((hB.1 h).mem_cl y) h3 },
      { have h3 : disjoint (insert e B) {y},
          apply disjoint_singleton_right.2 (mem_insert_iff.1.mt _),
          push_neg,
          refine ⟨ne.symm h2, _⟩,
          have h10 := hNIxyB.subset_ground,
          rw [delete_ground, ← union_singleton, union_comm, ← diff_diff] at h10,
          apply not_mem_subset h10 (not_mem_diff_of_mem (mem_singleton y)),
        have h5 : disjoint (J \ {x, y}) {y},
          rw [← union_singleton, union_comm, ← diff_diff],
          apply disjoint_sdiff_left,
        rw [← fund_circuit_delete h.indep (h.mem_cl e) h3, MI.contract_delete_comm h5, hMy,
            ← MC.contract_delete_comm h5], 
        rw [contract_ground, hIC, ← contract_ground] at he,
        rw fund_circuit_delete (hB.1 h).indep ((hB.1 h).mem_cl e) h3 },
      apply eq_of_forall_fund_circuit_eq φI φC _ h (hB.1 h) hfund,
      simp_rw [contract_ground, hIC] },
  { apply h,
    rw delete_base_iff at hNIxyB hNCxyB,
    cases hiIC with hIc hCc,
    { have h3 := (coindep_contract_iff.2 ⟨hIc, @disjoint_sdiff_right _ {x, y} J⟩).cl_compl,
      rw ← hNIxyB.cl at h3,
      apply hNIxyB.indep.base_of_cl_eq_ground h3 },
    { have h3 := (coindep_contract_iff.2 ⟨hCc, @disjoint_sdiff_right _ {x, y} J⟩).cl_compl,
      rw ← hNCxyB.cl at h3,
      apply hB.2,
      apply hNCxyB.indep.base_of_cl_eq_ground h3 } },
end

lemma delete_elem_eq_of_binary {B : set α} {x y : α} (hBxy : (M ⟍ ({x, y} : set α)).base B)
  (hBx : (M ⟍ x).base B) (hB : M.base B) [fintype α]
  [module (zmod 2) W] (φ : rep (zmod 2) W (M ⟍ ({x, y} : set α))) {Wx : Type*} [add_comm_group Wx]
  [module (zmod 2) Wx]
  (φx : rep (zmod 2) Wx (M ⟍ x)) : (M ⟍ x) = 
  (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
    (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E) ⟍ x :=
begin
  apply eq_of_indep_iff_indep_forall,
    simp_rw [delete_elem, delete_ground],
    rw matroid_of_module_fun.ground,
    intros I hI,
    rw [(matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E).delete_elem x, 
      delete_indep_iff, ← (standard_rep φx hBx).valid' I hI],
    rw ← (rep_of_matroid_of_module_fun (zmod 2) (B →₀ zmod 2) 
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E).valid' I _,
    simp [rep_of_matroid_of_module_fun],
    have h12 : (λ (x_1 : α), ite (x_1 ∈ M.E) (∑ (x_1 : α) in (M.fund_circuit x_1 B).to_finset 
      ∩ B.to_finset, (φ.standard_rep hBxy) x_1) 0) ∘ (coe : I → α) = 
      (λ (x_1 : I), ite (x_1.1 ∈ M.E) (∑ (x_1 : α) in (M.fund_circuit x_1 B).to_finset 
      ∩ B.to_finset, (φ.standard_rep hBxy) x_1) 0),
      simp only [eq_self_iff_true, subtype.val_eq_coe],
    have h10 : ∀ (x_1 : I), ite (x_1.1 ∈ M.E) (∑ (x_1 : α) in (M.fund_circuit x_1 B).to_finset 
      ∩ B.to_finset, (φ.standard_rep hBxy) x_1) 0 = (∑ (x_1 : α) in 
      (M.fund_circuit x_1 B).to_finset ∩ B.to_finset, (φ.standard_rep hBxy) x_1),
      { simp only [subtype.val_eq_coe],
        intros e,
        simp_rw [ite_eq_iff],
        left,
        rw delete_elem at hI,
        refine ⟨(M.delete_ground_subset_ground {x}) (hI e.2), rfl⟩ },
    simp_rw [h12, h10],
    have h3 : ((φx.standard_rep hBx) ∘ (coe : I → α)) = λ (e : I), ((φx.standard_rep hBx) e),
      simp only [eq_self_iff_true],
    rw [h3],
    simp_rw λ (e : I), (standard_rep φx hBx).mem_sum_basis_zmod2 hBx.indep _ 
      (@base.mem_cl _ (M ⟍ x) B hBx e (hI e.2)),
    have hBxs := hBx.subset_ground,
    simp_rw [delete_elem, delete_ground] at *,
    have h5 := diff_subset M.E {x},
    simp_rw λ (e : I), fund_circuit_delete hB.indep (@base.mem_cl _ M B hB e ((diff_subset M.E {x}) 
      (hI e.2))) (disjoint_singleton_right.2 (mem_insert_iff.1.mt (not_or (ne.symm 
      (mem_diff_singleton.1 (hI e.2)).2) (not_mem_subset hBxs 
      (not_mem_diff_of_mem (mem_singleton x)))))),
    have h6 : (λ (e : ↥I), ∑ (x : α) in (M.fund_circuit ↑e B ∩ B).to_finset, (standard_rep φx hBx) x) = 
      (λ (e : ↥I), ∑ (x : α) in (M.fund_circuit ↑e B ∩ B).to_finset, (standard_rep φ hBxy) x),
      simp only,
      have h10 :=  λ (i : ↥I), @finset.sum_congr _ _ (M.fund_circuit i B ∩ B).to_finset 
        (M.fund_circuit i B ∩ B).to_finset (standard_rep φx hBx) (standard_rep φ hBxy) _ rfl _,
      simp_rw  [λ (i : I), h10 i],
      intros x hx,
      rw mem_to_finset at hx,
      have h12 := standard_rep_base_eq φx φ hBx hBxy ⟨x, (mem_of_mem_inter_right hx)⟩,
      simp at h12,
      rw h12,
    simp_rw [h6, to_finset_inter, iff_self_and],
    apply λ h, not_mem_subset hI (not_mem_diff_singleton x M.E),
    rw [delete_elem, delete_ground] at hI,
    rw matroid_of_module_fun.ground,
    apply subset_trans hI (diff_subset M.E {x}),
end

end binary_lemmas

section rep_constructions

def rep_empty (𝔽 : Type*) [field 𝔽] (M : matroid_in α) 
  (hM : M.E = ∅) : rep 𝔽 𝔽 M := 
{ to_fun := λ e, 0,
  valid' := λ I hI, 
    begin
      rw [hM, subset_empty_iff] at hI,
      rw [hI, @linear_independent_image _ _ _ _ _ _ (∅ : set α) _ (inj_on_empty _),
          image_empty],
        simp only [empty_indep, linear_independent_empty 𝔽 𝔽, iff_true]
    end,
  support := λ e he, rfl }

def rep_singleton (𝔽 : Type*) [field 𝔽] (M : matroid_in α) {x : α} (hMx : M.E = {x}) : 
  rep 𝔽 𝔽 M := 
{ to_fun := λ e, if hMx : M.nonloop x ∧ e = x then (1 : 𝔽) else (0 : 𝔽),
  valid' := λ I hI, 
    begin 
      rw hMx at *,
      cases ssubset_or_eq_of_subset hI with hIempty hIsing,
      { rw ssubset_singleton_iff.1 hIempty,
        rw [@linear_independent_image _ _ _ _ _ _ (∅ : set α) _ (inj_on_empty _),
          image_empty],
        simp only [empty_indep, linear_independent_empty 𝔽 𝔽, iff_true] },
      rw hIsing,
      by_cases M.loop x,
      { have hd : (λ (e : α), dite (M.nonloop x ∧ e = x) (λ (hMx : M.nonloop x ∧ e = x), (1 : 𝔽)) 
        (λ (hMx : ¬(M.nonloop x ∧ e = x)), (0 : 𝔽))) ∘ (coe : ({x} : set α) → α)
        = λ x : ({x} : set α), (0 : 𝔽),
          ext;
          simp only [dite_eq_iff],
          right,
          simp_rw not_and_distrib,
          refine ⟨(or.intro_left (¬↑x_1 = x)) h.not_nonloop, rfl⟩,
        rw [hd, ← not_iff_not],
        refine ⟨λ h2, h.dep.not_indep, λ h2, _⟩,
        by_contra,
        apply @linear_independent.ne_zero _ 𝔽 _ ((λ (e : α), (0 : 𝔽)) ∘ (coe : ({x} : set α) → α)) 
          _ _ _ _ ⟨x, mem_singleton x⟩ h,
        simp only },
      { have hd : (λ (e : α), dite (M.nonloop x ∧ e = x) (λ (hMx : M.nonloop x ∧ e = x), (1 : 𝔽)) 
        (λ (hMx : ¬(M.nonloop x ∧ e = x)), (0 : 𝔽))) ∘ (coe : ({x} : set α) → α)
        = λ x : ({x} : set α), (1 : 𝔽),
          ext;
          simp only [dite_eq_iff],
          left,
          have h2 := mem_singleton_iff.1 x_1.2,
          simp only [subtype.val_eq_coe] at h2,
          refine ⟨⟨(not_loop_iff (by {rw hMx, apply mem_singleton _})).1 h, h2⟩, rfl⟩,
        rw hd,
        refine ⟨λ h2, indep_singleton.2 ((not_loop_iff (by {rw hMx, apply mem_singleton _})).1 h), 
          λ h2, _⟩,
        rw [@linear_independent_image _ _ _ _ _ _ ({x} : set α) (λ e : α, (1 : 𝔽)) 
          (inj_on_singleton _ _), image_singleton],
        apply linear_independent_singleton,
        simp only [ne.def, one_ne_zero, not_false_iff] },
    end,
  support := λ e he, 
    begin
      simp only [dite_eq_iff],
      right,
      simp_rw not_and_distrib,
      rw [hMx, mem_singleton_iff] at he,
      refine ⟨(or.intro_right (¬ M.nonloop x)) he, rfl⟩,
    end }

def rep_of_loop (M : matroid_in α) [finite_rk M] {f : α} (hf : M.loop f) 
  (φ : rep 𝔽 W (M ⟍ f)) : rep 𝔽 W M := 
{ to_fun := φ,
  valid' := λ I hI, 
    begin
      by_cases f ∈ I,
      { rw ← not_iff_not,
        refine ⟨λ h2, _, λ h2, _⟩,
        { apply indep.nonloop_of_mem.mt,
          simp only [not_forall, exists_prop],
          refine ⟨h, not_nonloop_iff.2 hf⟩ },
        have hfφ := φ.support f,
        by_contra h3,
        have h4 : linear_independent 𝔽 (φ ∘ coe) = linear_independent 𝔽 (λ (i : I), φ i),
          simp only [eq_iff_iff],
        rw h4 at h3,
        apply @linear_independent.ne_zero _ 𝔽 W ((λ (i : I), φ i.1)) _ _ _ _ ⟨f, h⟩ h3,
        simp only,
        apply hfφ,
        rw [delete_elem, delete_ground],
        apply not_mem_diff_singleton },
      have hIf := subset_diff_singleton hI h,
      rw φ.valid,
      simp only [delete_elem, delete_indep_iff, disjoint_singleton_right, and_iff_left_iff_imp],
      intros hf2,
      apply h,
    end,
  support := λ e he, 
    begin
      by_cases e = f,
      rw h,
      apply φ.support,
      simp only [delete_elem, delete_ground, not_mem_diff_singleton, not_false_iff],
      apply φ.support,
      simp only [delete_elem, delete_ground, mem_diff, mem_singleton_iff, not_and, not_not],
      contrapose,
      intros,
      apply he
    end } 

def add_coloop_rep (φ : rep 𝔽 W M) {f : α} (hf : f ∉ M.E) : 
  rep 𝔽 (W × 𝔽) (add_coloop M f) := 
{ to_fun := λ (e : α), if e ∈ ({f} : set α) then linear_map.inr 𝔽 W 𝔽 ((λ e : α, 1) e) else 
    linear_map.inl 𝔽 W 𝔽 (φ e),
  valid' := λ I hI, 
    begin
      by_cases f ∈ I,
      { rw [← union_diff_cancel (singleton_subset_iff.2 h), union_comm],
        simp only [← ite_apply _ (linear_map.inr 𝔽 W 𝔽 ∘ (λ e : α, 1)) (linear_map.inl 𝔽 W 𝔽 ∘ φ)],
        refine ⟨λ h2, _, λ h2, _⟩,
        { have h11 := linear_independent.image h2,
          rw image_union at h11,
          have hM : M.indep (I \ {f} : set α),
            { have h10 := linear_independent.mono (subset_union_left _ _) h11,
                rw ← linear_independent_image at h10,
                have h12 : ∀ e : ((I \ {f}) : set α), (ite ((e : α) ∈ ({f} : set α)) 
                  ((linear_map.inr 𝔽 W 𝔽) ↑1) ((linear_map.inl 𝔽 W 𝔽) (φ e)) 
                  = ((linear_map.inl 𝔽 W 𝔽) ∘ φ) e),
                { intros e,
                  rw ite_eq_iff,
                  right,
                  refine ⟨not_mem_of_mem_diff e.2, rfl⟩ },
              simp_rw [λ (e : (I \ {f} : set α)), h12 e, 
                @_root_.linear_map.linear_independent_iff _ _ _ _ _ _ _ _ _ _ (linear_map.inl 𝔽 W 𝔽) 
                (linear_map.ker_eq_bot_of_injective linear_map.inl_injective)] at h10,
              rw φ.valid at h10, 
              apply h10,
             { intros a ha b hb hab,
                have h13 := h2.injective,
                rw [← restrict_eq, ← inj_on_iff_injective] at h13,
                apply h13 (mem_union_left {f} ha) (mem_union_left {f} hb) hab } },
            obtain ⟨B2, hB2⟩ := hM,
            rw [← add_coloop_del_eq M hf, delete_elem, delete_base_iff, add_coloop_ground] at hB2,
            refine ⟨B2 ∪ {f}, ⟨_, 
              union_subset_union hB2.2 (subset_refl _)⟩⟩,
            simp only [insert_diff_of_mem, mem_singleton] at hB2,
            rw base_iff_basis_ground,
            have h3 := basis.insert_basis_insert hB2.1 (((add_coloop_eq M (add_coloop M f) hf).1 
              rfl).1.insert_indep_of_indep hB2.1.indep),
            simp only [insert_diff_singleton] at h3,
            rw [add_coloop_ground, union_singleton],
            apply h3 },  
        { rw [linear_independent_image, image_union],
          have h12 : (λ (e : α), ite (e ∈ ({f} : set α)) ((linear_map.inr 𝔽 W 𝔽) ↑1) 
            ((linear_map.inl 𝔽 W 𝔽) (φ e))) '' (I \ {f}) = 
            (linear_map.inl 𝔽 W 𝔽) '' (φ '' (I \ {f})),
            { ext;
              simp only [mem_image, mem_diff, mem_singleton_iff, comp_app],
              refine ⟨λ h, _, λ h, _⟩,  
              { obtain ⟨x, ⟨⟨hx1, hx3⟩, hx2⟩⟩ := h,
                refine ⟨φ x, ⟨⟨x, ⟨⟨hx1, hx3⟩, rfl⟩⟩, _⟩⟩,
                rw [← hx2, eq_comm, ite_eq_iff],
                right,
                refine ⟨hx3, rfl⟩ },
              { obtain ⟨x, ⟨⟨x2, ⟨⟨hx3, hx4⟩, rfl⟩⟩, hx2⟩⟩ := h,
                refine ⟨x2, ⟨⟨hx3, hx4⟩, _⟩⟩,
                rw [← hx2, ite_eq_iff],
                right,
                refine ⟨hx4, rfl⟩ } },
          have h13 : (λ (e : α), ite (e ∈ ({f} : set α)) ((linear_map.inr 𝔽 W 𝔽) ↑1) 
            ((linear_map.inl 𝔽 W 𝔽) (φ e))) '' {f} = (linear_map.inr 𝔽 W 𝔽) '' (↑1 '' ({f} : set α)),
            { simp_rw [image_singleton, singleton_eq_singleton_iff, ite_eq_iff],
              left,
              refine ⟨mem_singleton _, rfl⟩ },
          rw [h12, h13],
          apply linear_independent.inl_union_inr,
          { have h6 := (h2.subset (subset_union_left _ _)).indep_delete_of_disjoint 
              (disjoint_sdiff_left),
            rw [← delete_elem, add_coloop_del_eq M hf, ← φ.valid] at h6,
            apply h6.image },
          { rw image_singleton,
            apply linear_independent_singleton,
            simp only [algebra_map.coe_one, pi.one_apply, ne.def, one_ne_zero, not_false_iff] },
          rw inj_on_union (disjoint_sdiff_left),
          refine ⟨_, ⟨inj_on_singleton _ _, _⟩⟩,
          { intros a ha b hb hab,
            simp only [if_neg (not_mem_of_mem_diff ha), if_neg (not_mem_of_mem_diff hb)] at hab,
            have hab2 := linear_map.inl_injective hab,
            have h4 := (h2.subset (subset_union_left _ _)).indep_delete_of_disjoint 
              (disjoint_sdiff_left),
            rw [← delete_elem, add_coloop_del_eq M hf] at h4,
            apply (inj_on_of_indep φ h4) ha hb (linear_map.inl_injective hab) },
          intros a ha b hb,
          simp only [if_pos hb, if_neg (not_mem_of_mem_diff ha)],
          simp only [linear_map.coe_inl, linear_map.coe_inr, ne.def, prod.mk.inj_iff, not_and],
          intros hc,
          by_contra,
          have h6 := (h2.subset (subset_union_left _ _)).indep_delete_of_disjoint 
              (disjoint_sdiff_left),
          rw [← delete_elem, add_coloop_del_eq M hf] at h6,
          apply φ.ne_zero_of_nonloop (h6.nonloop_of_mem ha),
          rw hc } },
      { have h8 : ((λ (e : α), ite (e ∈ ({f} : set α)) ((linear_map.inr 𝔽 W 𝔽) ↑((λ (e : α), 1) e)) 
          ((linear_map.inl 𝔽 W 𝔽) (φ e))) ∘ coe) = 
          (λ (e : I), ite ((e : α) ∈ ({f} : set α)) ((linear_map.inr 𝔽 W 𝔽) ↑((λ (e : α), 1) e))
          ((linear_map.inl 𝔽 W 𝔽) (φ e))),
          simp only [eq_self_iff_true],
        rw h8,
        have h3 : ∀ (e : I), (ite ((e : α) ∈ ({f} : set α)) 
          ((linear_map.inr 𝔽 W 𝔽) ↑((λ (e : α), 1) e)) ((linear_map.inl 𝔽 W 𝔽) (φ e))) = 
              ((linear_map.inl 𝔽 W 𝔽) ∘ φ) e,
        { intros,
          simp_rw [ite_eq_iff],
          right,
          refine ⟨mem_singleton_iff.1.mt (ne_of_mem_of_not_mem e.2 h), rfl⟩ },
        simp_rw [λ (e : I), h3 e],
        rw [@_root_.linear_map.linear_independent_iff _ _ _ _ _ _ _ _ _ _ 
          (linear_map.inl 𝔽 W 𝔽) 
          (linear_map.ker_eq_bot_of_injective linear_map.inl_injective), φ.valid],
        refine ⟨λ h2, _, λ h2, _⟩,
        { rw [← add_coloop_del_eq M hf, delete_elem, delete_indep_iff] at h2,
          apply h2.1 },
        { rw [← add_coloop_del_eq M hf, delete_elem, delete_indep_iff],
          refine ⟨h2, disjoint_singleton_right.2 h⟩ } },
    end,
  support := λ e he, 
    begin
      by_cases e ∈ {f},
      { by_contra h2,
        apply he,
        rw [add_coloop_ground, mem_singleton_iff.1 h],
        apply mem_insert },
      { have he2 := not_mem_subset (subset_union_left _ _) he,
        rw ite_eq_iff,
        right,
        refine ⟨h, _⟩,
        simp only [linear_map.coe_inl, prod.mk_eq_zero, eq_self_iff_true, 
          and_true],
        rw [add_coloop_ground, mem_insert_iff, not_or_distrib] at he,
        apply φ.support e he.2 },
    end }

def rep_of_del (N : matroid_in α) (φ : rep 𝔽 W N) (D : set α) : 
rep 𝔽 W (N ⟍ D) := 
{ to_fun := λ x, if x ∈ D then 0 else φ.to_fun x,
  valid' := λ I hI, by { rw delete_ground at hI, 
    have h2 : ∀ x : I, ite ((x : α) ∈ D) 0 (φ.to_fun x) = φ.to_fun x,
      intros x,
      rw ite_eq_iff,
      right,
      refine ⟨((mem_diff x.1).1 (mem_of_subset_of_mem hI x.2)).2, rfl⟩,
    have h8 : ((λ (e : α), ite ((e : α) ∈ D) 0 (φ.to_fun e)) ∘ coe) = 
          (λ (e : I), ite ((e : α) ∈ D) 0 (φ.to_fun e)),
      simp only [eq_self_iff_true],
    rw h8,
    simp_rw [λ (e : I), h2 e],
    refine ⟨λ h, delete_indep_iff.2 ⟨((φ.valid' I (subset_trans hI (diff_subset N.E D))).1 h), 
    (subset_diff.1 hI).2⟩, λ h, (φ.valid' I (subset_trans hI (diff_subset N.E D))).2 
      (matroid_in.delete_indep_iff.1 h).1⟩ },
  support := λ e he,
    begin
      simp only [ite_eq_iff],
      by_cases e ∈ D,
      left,
      refine ⟨h, rfl⟩,
      right,
      have h2 : e ∉ N.E,
        rw delete_ground at he,
        have h3 : N.E ⊆ (N.E \ D) ∪ D, 
          simp only [diff_union_self, subset_union_left],
        apply not_mem_subset h3,
        rw mem_union,
        push_neg,
        refine ⟨he, h⟩,
      refine ⟨h, φ.support e h2⟩,
    end  }

def rep_of_contr (N : matroid_in α) (φ : rep 𝔽 W N) (C : set α) (hC : C ⊆ N.E):
  rep 𝔽 (W ⧸ span 𝔽 (φ.to_fun '' C)) (N ⟋ C) := 
{ to_fun := λ x, submodule.quotient.mk (φ.to_fun x),
  valid' := λ I hI,
    begin
      rw contract_ground at hI,
      have h21 : (λ (x : ↥I), φ.to_fun ↑x) '' univ = φ.to_fun '' I,
        { simp only [to_fun_eq_coe, image_univ],
          ext;
          simp only [mem_range, set_coe.exists, subtype.coe_mk, exists_prop, mem_image] },
      obtain ⟨J, hJ⟩ := exists_basis N C hC,
      rw [basis.contract_eq_contract_delete hJ, delete_indep_iff, 
        indep.contract_indep_iff hJ.indep],
      have h10 := span_basis φ hJ,
      refine ⟨λ h, _, λ h, _⟩,  
      simp only at h,
      simp_rw [← mkq_apply _] at h,
      rw ← φ.valid' _ (union_subset (subset_trans hI (diff_subset _ _)) hJ.subset_ground_left),
      have h30 : disjoint (span 𝔽 (φ.to_fun '' I)) (span 𝔽 (φ.to_fun '' J)),
      { simp_rw [← to_fun_eq_coe] at h10,
        rw h10,
        simp_rw [← to_fun_eq_coe],
        rw ← ker_mkq (span 𝔽 (φ.to_fun '' C)),
        rw [linear_map.linear_independent_iff, ← image_univ, h21, disjoint.comm] at h,
        exact h.2 },
      have h7 := linear_independent.image 
        (linear_independent.of_comp ((span 𝔽 (φ '' C)).mkq) h),
      have h8 := linear_independent.image ((φ.valid' J hJ.subset_ground_left).2 (hJ.indep)),
      have h6 := linear_independent.union h7 h8 h30,
      rw [linear_independent_image, image_union],
      refine ⟨⟨_root_.disjoint.of_image (linear_independent.union' h7 h8 h30 h6), h6⟩, _⟩,
      apply @_root_.disjoint.of_image _ _ φ,
      rw disjoint_iff_forall_ne,
      intros x hxI y hyC, 
      by_contra h2,
      rw ← h2 at *,
      rw [submodule.disjoint_def, to_fun_eq_coe, h10] at h30,
      specialize h30 x (set_like.mem_coe.1 (mem_of_subset_of_mem subset_span hxI))
        (set_like.mem_coe.1 (mem_of_subset_of_mem 
        (subset_trans (image_subset _ (diff_subset _ _)) subset_span) hyC)),
      have h31 := mem_of_subset_of_mem 
        (image_subset _ (diff_subset _ _)) hyC,
      obtain ⟨e, ⟨he, rfl⟩⟩ := (mem_image φ I x).1 hxI,
      rw to_fun_eq_coe at h7,
      apply @linear_independent.ne_zero _ 𝔽 W _ _ _ _ _ (⟨φ e, hxI⟩ : φ '' I) h7,
      simp_rw h30,
      simp only [subtype.coe_mk],
      rw inj_on_union (_root_.disjoint.of_image (linear_independent.union' h7 h8 h30 h6)),
      refine ⟨φ.inj_on_of_indep ((φ.valid' I (subset_trans hI (diff_subset _ _))).1 
        (linear_independent.of_comp ((span 𝔽 (φ '' C)).mkq) h)), 
        ⟨φ.inj_on_of_indep (hJ.indep), λ x hx y hy, set.disjoint_iff_forall_ne.1 
        (linear_independent.union' h7 h8 h30 h6) (φ x) (mem_image_of_mem φ hx) 
        (φ y) (mem_image_of_mem φ hy)⟩⟩,
      simp_rw [← mkq_apply _],
      rw linear_map.linear_independent_iff,
      refine ⟨(φ.valid' I (indep.subset h.1.2 (subset_union_left I J)).subset_ground).2 
        (indep.subset h.1.2 (subset_union_left I J)), _⟩,
      rw ker_mkq (span 𝔽 (φ.to_fun '' C)),
      have h60 := linear_independent.image ((φ.valid' _ h.1.2.subset_ground).2 h.1.2),
      rw image_union at h60,
      rw [← image_univ, h21],
      simp_rw [to_fun_eq_coe],
      simp only [← h10],
      apply linear_independent.union'',
      { apply linear_independent.image 
          ((φ.valid' J (indep.subset h.1.2 (subset_union_right I J)).subset_ground).2 
            (indep.subset h.1.2 (subset_union_right I J))) },
      { apply linear_independent.image 
          ((φ.valid' I (indep.subset h.1.2 (subset_union_left I J)).subset_ground).2 
          (indep.subset h.1.2 (subset_union_left I J))) },
      { rw disjoint.comm,
        apply disjoint_image_image,
        have h200 := inj_on_of_indep φ h.1.2,
        rw inj_on at h200,
        intros x hx y hy,
        specialize h200 (mem_of_subset_of_mem (subset_union_left I J) hx) 
          (mem_of_subset_of_mem (subset_union_right I J) hy),
        apply mt h200,
        apply disjoint_iff_forall_ne.1 h.1.1 x hx y hy },
      rw [to_fun_eq_coe, union_comm _ _] at h60,
      apply h60,
    end,
  support := λ e he, 
    begin
      rw contract_ground at he,
      by_cases e ∈ C,
      rw quotient.mk_eq_zero,
      apply mem_of_subset_of_mem subset_span (mem_image_of_mem _ h),
      rw [φ.support, quotient.mk_zero],
      rw ← union_diff_cancel hC,
      apply (mem_union _ _ _).1.mt (not_or_distrib.2 ⟨h, he⟩),
    end }

def is_rep_of_minor_of_is_rep (N : matroid_in α) (hNM : N ≤m M) (hM : M.is_representable 𝔽) : 
  N.is_representable 𝔽 := 
begin
  obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := hM,
  obtain ⟨C, ⟨D, ⟨hC, ⟨hD, ⟨hCD, rfl⟩⟩⟩⟩⟩ := minor.exists_contract_indep_delete_coindep hNM,
  apply is_representable_of_rep (rep_of_del (M ⟋ C) (rep_of_contr M φ C hC.subset_ground) D),
end

lemma minor_closed_rep : minor_closed (matroid_in.is_representable 𝔽 : matroid_in α → Prop) := 
  λ M N hNM hM, is_rep_of_minor_of_is_rep N hNM hM

def is_rep_of_iso_minor_of_is_rep (N : matroid_in γ) (hNM : N ≤i M) (hM : M.is_representable 𝔽) : 
  N.is_representable 𝔽 := 
begin
  obtain ⟨M', ⟨hM'M, ⟨ψ⟩⟩⟩ := hNM,
  obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := is_rep_of_minor_of_is_rep M' hM'M hM,
  apply is_representable_of_rep (rep_of_iso M' N ψ φ),
end

variables [fintype α]

open_locale big_operators

lemma parallel_extend_rep (φ : rep 𝔽 W M) {x y : α} (hMx : M.nonloop x) (hy : y ∉ M.E) 
[finite_dimensional 𝔽 W] :
  matroid_of_module_fun 𝔽 W (λ (e : α), if e = y then - φ x else φ e) (insert y M.E) = 
  parallel_extend M x y := 
begin
  rw ← (eq_parallel_extend_iff hMx hy).2,
  rw circuit_iff_dep_forall_diff_singleton_indep,
    refine ⟨⟨_, λ e he, _⟩, _⟩,
    rw dep,
    refine ⟨_, _⟩,
    { simp only [matroid_of_module_fun, matroid_of_indep_of_bdd'_apply, not_and_distrib],
      left,
      --simp_rw [← ite_apply],
      rw not_linear_independent_iff,
      refine ⟨finset.univ, ⟨λ e, 1, _⟩⟩,
      simp only [one_smul, finset.mem_univ, ne.def, one_ne_zero, not_false_iff, set_coe.exists, 
        mem_insert_iff, mem_singleton_iff, exists_prop, and_true, exists_or_eq_right],
      convert_to (∑ (x_1 : α) in {x, y}, ite (x_1 = y) (-φ x) (φ x_1) = 0), 
      rw @finset.sum_subtype _ _ _ ({x, y} : set α) _ {x, y},
      refl,
      intros e,
      rw [← finset.mem_coe, finset.coe_insert, finset.coe_singleton],
      refl,
      rw [finset.sum_insert (finset.mem_singleton.1.mt (ne_of_mem_of_not_mem hMx.mem_ground hy)), 
        finset.sum_singleton, if_pos rfl, if_neg (ne_of_mem_of_not_mem hMx.mem_ground hy)],
      simp only [add_right_neg] },
    rw [insert_eq, union_comm, ← insert_eq],
    apply insert_subset_insert (singleton_subset_iff.2 hMx.mem_ground),
    obtain ⟨rfl | _⟩ := mem_insert_iff.1 he,
    { simp only [insert_diff_of_mem, mem_singleton, 
        diff_singleton_eq_self (mem_singleton_iff.1.mt (ne_of_mem_of_not_mem hMx.mem_ground hy)), 
        matroid_of_module_fun, matroid_of_indep_of_bdd'_apply, not_and_distrib],
      refine ⟨_, singleton_subset_iff.2 (mem_insert y _)⟩,
      have h2 : ∀ e : ({y} : set α), ↑e = y,
        intros e,
        apply mem_singleton_iff.1 e.2,
      simp_rw [h2, eq_self_iff_true, if_true],
      rw [@linear_independent_image _ _ _ _ _ _ _ (λ (e : α), - φ x) (inj_on_singleton _ _), 
        image_singleton],
      apply @linear_independent_singleton 𝔽 _ _ _ _ _ _ _ 
        (neg_ne_zero.2 (φ.ne_zero_of_nonloop hMx)) },
    rw [mem_singleton_iff.1 h, insert_eq x {y}, union_comm, ← insert_eq],
    simp only [insert_diff_of_mem, mem_singleton, 
      diff_singleton_eq_self (mem_singleton_iff.1.mt (ne.symm 
      (ne_of_mem_of_not_mem hMx.mem_ground hy))), matroid_of_module_fun, 
      matroid_of_indep_of_bdd'_apply, not_and_distrib],
    refine ⟨_, singleton_subset_iff.2 (mem_of_mem_of_subset hMx.mem_ground (subset_insert y _))⟩,
    have h2 : ∀ e : ({x} : set α), ↑e ≠ y,
      intros e,
      have h3 := (ne_of_mem_of_not_mem hMx.mem_ground hy),
      rw ← mem_singleton_iff.1 e.2 at h3,
      apply h3,
    simp_rw [h2, if_false],
    rw [linear_independent_image (inj_on_singleton _ _), image_singleton],
    exact linear_independent_singleton (φ.ne_zero_of_nonloop hMx),
  simp only [delete_elem, ← delete_matroid_of_module_fun, insert_diff_of_mem, mem_singleton,
    diff_singleton_eq_self hy],
  have h10 : ∀ e : α, e ∈ M.E → ite (e = y) (-φ x) (φ e) = φ e,
    intros e he,
    rw if_neg (ne_of_mem_of_not_mem he hy),
  simp_rw [matroid_of_module_fun_congr 𝔽 W _ _ _ h10],
  rw ← matroid_of_module_fun_rep_eq,
end

def series_extend_rep (φ : rep 𝔽 W M) {x y : α} (hx : x ∈ M.E)
  (hy : y ∉ M.E) (hMx : ¬ M.coloop x) : rep 𝔽 (W × 𝔽) (series_extend M x y) := 
{ to_fun := λ (e : α), 
    if e = x
    then 
      (linear_map.inl 𝔽 W 𝔽 ∘ φ + linear_map.inr 𝔽 W 𝔽 ∘ (λ e : α, 1)) e
    else 
      if e = y then linear_map.inr 𝔽 W 𝔽 1 else (linear_map.inl 𝔽 W 𝔽 ∘ φ) e,
  valid' := λ I hI, 
    begin
      refine ⟨_, λ h2, _⟩,
      { contrapose,
      intros h2,
      rw linear_dependent_comp_subtype',
      rw not_indep_iff at h2,
      obtain ⟨C, ⟨hCI, hCcct⟩⟩ := exists_circuit_subset_of_dep h2,
      by_cases hxC : x ∈ C, 
      { have hyC := (series_pair_mem_circuit _ _ _ hCcct 
          (series_extend_cocircuit hx hMx hy)).1 hxC,
        rw [← @union_diff_cancel _ {y} C (singleton_subset_iff.2 hyC), union_comm, 
          union_singleton] at hCcct,
        have hMcct := contract_circuit_of_insert_circuit y (C \ {y}) 
          ((series_extend_cocircuit hx hMx hy).nonloop_of_mem 
          (mem_insert_of_mem x (mem_singleton _))) (not_mem_diff_singleton _ _) hCcct,
        rw [series_extend_contract_eq M x y hy] at hMcct,
        obtain ⟨f, ⟨hC, ⟨hftot, hfne0⟩⟩⟩ := rep.circuit φ hMcct,
        rw ← hC at hCcct hMcct,
        refine ⟨(⟨(insert y f.support), (λ e : α, if e = y then - f x else f e), λ a, 
          ⟨λ ha, _, λ ha, _⟩⟩ : α →₀ 𝔽), _⟩,
        { obtain ⟨rfl | ha⟩ := finset.mem_insert.1 ha,
          { simp only [eq_self_iff_true, if_true, ne.def, neg_eq_zero],
            rw [← ne.def, ← finsupp.mem_support_iff, ← finset.mem_coe, hC],
            apply mem_diff_of_mem hxC (mem_singleton_iff.1.mt (ne_of_mem_of_not_mem hx hy)) },
          { rw if_neg (ne_of_mem_of_not_mem (finset.mem_coe.2 h) 
              (not_mem_subset (subset_of_eq hC) (not_mem_diff_singleton _ _))),
            apply finsupp.mem_support_iff.1 h } },
        { apply finset.mem_insert.2,
          by_cases hay : a = y,
          { apply or.intro_left _ hay },
          { rw if_neg hay at ha,
            apply or.intro_right _ (finsupp.mem_support_iff.2 ha) } },
        refine ⟨_, ⟨_, _⟩⟩,
        { rw finsupp.mem_supported,
          simp only [finset.coe_insert, hC],
          apply insert_subset.2 ⟨mem_of_subset_of_mem hCI hyC, subset_trans (diff_subset _ _) hCI⟩},
        { simp_rw finset.insert_eq y f.support,
          dsimp [finsupp.total_apply, finsupp.sum],
          dsimp [finsupp.total_apply, finsupp.sum] at hftot,
          simp_rw [ite_smul, smul_ite],
          simp only [prod.ext_iff, prod.smul_mk, zero_add, add_zero, algebra.id.smul_eq_mul, 
            mul_one, smul_zero],
          rw [finset.sum_union, ← @finset.sdiff_union_of_subset _ _ ({x} : finset α) f.support _, 
            finset.sum_union, finset.sum_singleton],
          simp only [if_pos rfl, if_neg (ne_of_mem_of_not_mem hx hy), 
            if_neg (ne.symm (ne_of_mem_of_not_mem hx hy)), ← prod_mk_sum],
          have hx2 : ∀ (e : α), e ∈ ({x} : finset α) → e ≠ y,
            intros e he,
            rw [finset.mem_singleton.1 he],
            apply ne_of_mem_of_not_mem hx hy,
          have hx3 : ∀ (e : α), e ∈ ({x} : finset α) → e = x,
            intros e he,
            rw [finset.mem_singleton.1 he],
          
          rw [finset.sum_ite_of_false _ _ hx2, finset.sum_ite_of_true _ _ hx3],
          simp only [neg_smul, eq_self_iff_true, if_true, pi.add_apply, 
            prod.mk_add_mk, add_zero, zero_add, prod.smul_mk, algebra.id.smul_eq_mul, mul_one, 
            prod.neg_mk],
          
          simp only [prod.fst_add, zero_add, prod.fst_zero, prod.snd_add, prod.snd_zero],
          rw [finset.sum_ite_of_false _ _ (λ e he, _), finset.sum_ite_of_false _ _ (λ e he, _)],
          simp only [finset.sum_ite_of_false _ _ (λ e he, _), ← prod_mk_sum], 
          rw finset.sum_ite_of_false _ _ (λ e he, _),
          rw [← prod_mk_sum, finset.sum_const_zero, zero_add],
          simp only,
          rw ← finset.sum_union, --(finset.sdiff_disjoint), 
          simp only [finset.sdiff_union_self_eq_union, finset.sum_singleton, add_left_neg, 
            eq_self_iff_true, and_true],
          rw [finset.union_comm, ← finset.insert_eq, finset.insert_eq_of_mem],
          apply hftot,
          rw [← finset.mem_coe, hC],
          apply mem_diff_singleton.2 ⟨hxC, ne_of_mem_of_not_mem hx hy⟩,
          simp only [finset.disjoint_singleton_right, finset.mem_sdiff, finset.mem_singleton, 
            eq_self_iff_true, not_true, and_false, not_false_iff], -- avoiding decidable_eq instance
          rw [← finset.mem_coe, finset.coe_sdiff, hC, mem_diff, mem_diff] at he,
          apply mem_singleton_iff.2.mt he.1.2,
          rw [finset.mem_sdiff, finset.mem_singleton] at he,
          apply he.2,
          rw [← finset.mem_coe, finset.coe_sdiff, hC, mem_diff, mem_diff] at he,
          apply mem_singleton_iff.2.mt he.1.2,
          simp only [finset.disjoint_singleton_right, finset.mem_sdiff, finset.mem_singleton, 
            eq_self_iff_true, not_true, and_false, not_false_iff],
          rw [finset.singleton_subset_iff, ← finset.mem_coe, hC],
          apply mem_diff_singleton.2 ⟨hxC, ne_of_mem_of_not_mem hx hy⟩,
          rw [← finset.disjoint_coe, hC],
          simp only [finset.coe_singleton, disjoint_singleton_left, not_mem_diff_singleton, 
            not_false_iff] },
        rw ne.def,
        rw finsupp.ext_iff,
        push_neg,
        use x,
        simp only [ne.def, finsupp.coe_mk, finsupp.coe_zero, pi.zero_apply],
        rw if_neg (ne_of_mem_of_not_mem hx hy),
        apply finsupp.mem_support_iff.1,
        rw [← finset.mem_coe, hC],
        apply mem_diff_singleton.2 ⟨hxC, ne_of_mem_of_not_mem hx hy⟩ },
      { have hyC := (series_pair_mem_circuit _ _ _ hCcct 
          (series_extend_cocircuit hx hMx hy)).2.mt hxC,
        have h4 := (@indep.of_contract _ _ {y} _).mt (not_indep_iff.2 hCcct.dep),
        rw [← contract_elem, series_extend_contract_eq M x y hy, ← φ.valid, 
          linear_dependent_comp_subtype'] at h4, 
        obtain ⟨f, ⟨hC, ⟨hftot, hfne0⟩⟩⟩ := h4,
        refine ⟨f, ⟨subset_trans hC hCI, ⟨_, hfne0⟩⟩⟩,
        dsimp [finsupp.total_apply, finsupp.sum],
        dsimp [finsupp.total_apply, finsupp.sum] at hftot,
        simp_rw smul_ite,
        rw [finset.sum_ite_of_false _ _ (λ e he, _), 
          finset.sum_ite_of_false _ _ (λ e he, _)],
        simp only [prod.smul_mk, algebra.id.smul_eq_mul, mul_zero, ← prod_mk_sum, hftot, 
          finset.sum_const_zero, prod.mk_eq_zero, eq_self_iff_true, and_self],
        { apply ne_of_mem_of_not_mem (finset.mem_coe.2 he) 
            (not_mem_subset ((f.mem_supported _).1 hC) hyC) },
        { apply ne_of_mem_of_not_mem (finset.mem_coe.2 he) 
            (not_mem_subset ((f.mem_supported _).1 hC) hxC) } } },
      { simp_rw [linear_independent_comp_subtype, finsupp.total_apply, smul_ite],
        dsimp [finsupp.sum],
        simp only [add_zero, zero_add, mul_one, smul_zero, mul_zero, finset.sum_ite, prod.ext_iff,
          finset.filter_congr_decidable, prod.fst_add, prod.fst_zero, prod.snd_add, 
          prod.snd_zero, finset.filter_eq', finset.filter_ne', ← prod_mk_sum, 
          finset.sum_const_zero, zero_add, add_zero],
        intros l hl hl0,
        by_cases hyI : (series_extend M x y).indep ({y} ∪ I : set α),
        { have hyI2 := (hyI.subset (subset_union_left _ _)).union_indep_iff_contract_indep.1 hyI,
          rw [← contract_elem, series_extend_contract_eq M x y hy, ← φ.valid, 
            linear_independent_comp_subtype] at hyI2,
          simp_rw [finsupp.total_apply] at hyI2,
          have hxl : x ∉ l.support,
          { by_contra hxl,
            rw [if_pos hxl] at hl0,
            specialize hyI2 (l.filter (≠ y)) _ _,
            { rw [finsupp.mem_supported, finsupp.support_filter, finset.filter_ne', 
                finset.coe_erase],
              apply diff_subset_diff_left ((l.mem_supported _).1 hl) },
            { rw [finsupp.sum_filter_index, finsupp.support_filter, finset.filter_ne',
                finset.sum_eq_add_sum_diff_singleton (finset.mem_erase.2 
                ⟨ne_of_mem_of_not_mem hx hy, hxl⟩), ← finset.erase_eq],
              rw [finset.erase_right_comm, finset.sum_singleton] at hl0,
              apply hl0.1 },
            apply finsupp.mem_support_iff.1 hxl,
            rw [← l.filter_apply_pos (≠ y) (ne_of_mem_of_not_mem hx hy), hyI2], 
            simp only [finsupp.coe_zero, pi.zero_apply] },
          simp only [if_neg hxl, finset.sum_empty, zero_add] at hl0,
          have hyl : y ∉ l.support,
          { by_contra hyl,
            rw [if_pos (finset.mem_erase.2 ⟨ne.symm (ne_of_mem_of_not_mem hx hy), hyl⟩), 
              finset.sum_singleton] at hl0,
             apply finsupp.mem_support_iff.1 hyl,
             apply hl0.2 },
          specialize hyI2 l _ _,
          { rw [finsupp.mem_supported],
            apply subset_diff_singleton ((l.mem_supported 𝔽).2 hl) hyl },
          { dsimp [finsupp.sum],
            rw [finset.erase_eq_of_not_mem hxl, finset.erase_eq_of_not_mem hyl] at hl0,
            apply hl0.1 },
          apply hyI2 },
      { have hyl : y ∉ l.support,
        { by_contra,
          rw [singleton_union, insert_eq_of_mem (mem_of_subset_of_mem 
            ((l.mem_supported _).1 hl) h)] at hyI,
          apply hyI h2 },
        rw [if_neg (finset.mem_erase.1.mt (not_and_distrib.2 (or.intro_right _ hyl))), 
          finset.sum_empty, add_zero] at hl0,
        have hxl : x ∉ l.support,
        { by_contra hxl,
          simp only [if_pos hxl, finset.sum_singleton] at hl0,
          apply finsupp.mem_support_iff.1 hxl,
          apply hl0.2 },
        rw [if_neg hxl, finset.sum_empty, zero_add] at hl0,
        rw not_indep_iff _ at hyI,
        have hIxy : (series_extend M x y).indep ({y} ∪ (I \ {x}) : set α),  
        { by_contra hIyxn, 
          obtain ⟨C, ⟨hC, hC2⟩⟩ := exists_circuit_subset_of_dep ((not_indep_iff _).1 hIyxn),
          have hyC : y ∈ C,
          { by_contra hyC,
            rw [singleton_union, subset_insert_iff_of_not_mem hyC] at hC,
            apply hC2.dep.not_indep (h2.subset (subset_trans hC (diff_subset _ _))) },
          rw ← series_pair_mem_circuit _ _ _ hC2 (series_extend_cocircuit hx hMx hy) at hyC,
          apply (not_mem_subset hC ((mem_union _ _ _).1.mt 
            (not_or_distrib.2 ⟨mem_singleton_iff.1.mt (ne_of_mem_of_not_mem hx hy), 
            not_mem_diff_singleton _ _⟩))) hyC,
          apply subset_trans (union_subset_union_right _ (diff_subset I {x})) hyI.subset_ground },
        have hyx := (hIxy.subset (subset_union_left _ _)).union_indep_iff_contract_indep.1 hIxy,
        rw [← contract_elem, series_extend_contract_eq M x y hy, ← φ.valid, 
          linear_independent_comp_subtype] at hyx,
        rw [finset.erase_eq_of_not_mem hxl, finset.erase_eq_of_not_mem hyl] at hl0,
        apply hyx l ((l.mem_supported _).2 
          (subset_diff_singleton (subset_diff_singleton ((l.mem_supported _).1 hl) hxl) hyl)) hl0.1,
      --apply hyx.subset_ground,
      rw series_extend_ground hx at hI ⊢,
      simp only [singleton_union, auto_param_eq],
      apply insert_subset.2 ⟨mem_insert _ _, hI⟩ } }, 
    end,
  support := λ e he, 
    begin
      rw series_extend_ground hx at he,
      rw [if_neg, if_neg],
      simp only [linear_map.coe_inl, prod.mk_eq_zero, eq_self_iff_true, and_true],
      apply φ.support _ (not_mem_subset (subset_insert _ _) he),
      apply ne.symm (ne_of_mem_of_not_mem (mem_insert y _) he),
      apply ne.symm (ne_of_mem_of_not_mem (mem_insert_of_mem _ hx) he),
    end }

end rep_constructions

section unif_rep

lemma U1k_representable (k : ℕ) (hk : 1 ≤ k) [nontrivial 𝔽] : (unif 1 k).is_representable 𝔽 :=
begin
  have φ := @rep.mk _ 𝔽 _ _ _ _ (unif 1 k) (λ x, (1 : 𝔽)) (λ I hI, _) 
    (by { intros e he,
          by_contra,
          apply he,
          simp only [unif_ground_eq, mem_univ] }),
  { apply is_representable_of_rep φ },
  rw [unif_indep_iff],
  refine ⟨λ h, _, λ h, _⟩,  
  { rw [ncard, nat.card_eq_fintype_card, ← finrank_self 𝔽],
    apply fintype_card_le_finrank_of_linear_independent h },
  { cases le_iff_lt_or_eq.1 h with h0 h1,
    { rw [ncard_eq_zero.1 (nat.lt_one_iff.1 h0), linear_independent_image (λ x hx y hy hxy, 
        (inj_on_empty (λ x, (1 : 𝔽))) hx hy rfl), image_empty],
      apply linear_independent_empty 𝔽 _ },
    { obtain ⟨a, rfl⟩ := ncard_eq_one.1 h1,
      rw [linear_independent_image (λ x hx y hy hxy, (inj_on_singleton (λ x, (1 : 𝔽)) a) hx hy rfl), 
        image_singleton],
      apply linear_independent_singleton,
      simp only [ne.def, one_ne_zero, not_false_iff] } },
end

lemma U23_binary : matroid_in.is_binary (unif 2 3) :=
begin
  have hcard3 : fintype.card ((set.univ \ {0}) : set (fin 2 → zmod 2)) = 3, 
  { rw [← to_finset_card, to_finset_diff, finset.card_sdiff, to_finset_univ, finset.card_univ, 
      to_finset_card, card_singleton, @fintype.card_fun (fin 2) (zmod 2) _ _ _, zmod.card 2, 
      fintype.card_fin, pow_two, nat.sub_one, nat.pred_eq_succ_iff, two_mul],
    simp only [to_finset_univ, to_finset_subset, finset.coe_univ, singleton_subset_iff] },
  have f := equiv.symm (fintype.equiv_fin_of_card_eq hcard3),
  have φ := @rep.mk _ (zmod 2) (fin 2 → zmod 2) _ _ _ (unif 2 3) (λ x, (f x)) (λ I hI, _) 
    (by { simp only [unif_ground_eq, mem_univ, not_true, is_empty.forall_iff, forall_const]}),
  { rw [matroid_in.is_binary, is_representable],
    apply is_representable_of_rep φ },
  rw [unif_indep_iff],
  refine ⟨λ h, _, λ h, _⟩,  
  -- now the possible sizes of vector families for h are 0, 1, 2.
  { rw [ncard, nat.card_eq_fintype_card, ← @finrank_fin_fun (zmod 2) _ _ 2],
    apply fintype_card_le_finrank_of_linear_independent h },
  rw [linear_independent_image (λ x hx y hy hxy, 
    (f.injective.inj_on I) hx hy (subtype.coe_inj.1 hxy))],
  cases le_iff_lt_or_eq.1 h with h1 h2,
  cases le_iff_lt_or_eq.1 (nat.le_of_lt_succ h1) with h0 h1,
  { rw [ncard_eq_zero.1 (nat.lt_one_iff.1 h0), image_empty],
    apply linear_independent_empty (zmod 2) _ },
  
  { obtain ⟨a, rfl⟩ := ncard_eq_one.1 h1,
    rw [image_singleton],
    apply linear_independent_singleton,
    -- if i plug this in directly it wants me to provide a nontrivial (zmod 2) instance
    apply (mem_diff_singleton.1 (f a).2).2 },

  { obtain ⟨x, ⟨y, ⟨hxy, rfl⟩⟩⟩ := ncard_eq_two.1 h2,
    rw [image_insert_eq, image_singleton, linear_independent_insert, mem_span_singleton, not_exists],
    refine ⟨linear_independent_singleton ((mem_diff_singleton.1 (f y).2).2), λ a, _⟩,
    cases le_iff_lt_or_eq.1 (nat.le_of_lt_succ (zmod.val_lt a)) with h0 h1,
    { rw [(zmod.val_eq_zero a).1 (nat.lt_one_iff.1 h0), zero_smul],
      apply ne.symm (mem_diff_singleton.1 (f x).2).2 },
      rw [← zmod.nat_cast_zmod_val a, h1, algebra_map.coe_one, one_smul], 
      by_contra,
      apply hxy (f.injective (subtype.coe_inj.1 (eq.symm h))),
      by_contra,
      apply hxy (mem_singleton_iff.2 (f.injective (subtype.coe_inj.1 (h)))) },
end

lemma U22_binary : matroid_in.is_binary (unif 2 2) := 
begin
  have h23 : 2 ≤ 3,
    simp only [nat.bit0_le_bit1_iff],
  apply is_rep_of_iso_minor_of_is_rep (unif 2 2) (unif_iso_minor h23) U23_binary,
end

lemma U24_nonbinary : ¬ matroid_in.is_binary (unif 2 4) :=
begin
  by_contra h2,
  rw [matroid_in.is_binary, is_representable] at h2,
  obtain ⟨B, ⟨hB, ⟨φ'⟩⟩⟩ := h2,
  { have h8 := (φ'.subset_nonzero_of_simple (unif_simple 2 4 rfl.le)),
    have h50 := @span_mono (zmod 2) _ _ _ _ _ _ (subset_univ (φ' '' (unif 2 4).E)),
    rw ← span_span at h50,
    have h70 := subset_trans h8 (@diff_subset_diff_left _ _ _ 
      ({0} : set (B →₀ zmod 2)) (span_le.1 h50)),
    -- need basis
    have h11 := ((φ'.valid' _ hB.subset_ground).2 hB.indep),
    have h20 : (finrank (zmod 2) (B →₀ zmod 2)) = 2,
      simp only [finrank_finsupp, fintype.card_of_finset, finset.filter_congr_decidable],
      rw unif_base_iff at hB,
      rw filter_mem_univ_eq_to_finset,
      simp_rw ← hB, 
      rw [ncard_def, nat.card_eq_fintype_card, to_finset_card],
      simp only [bit0_le_bit0, nat.one_le_bit0_iff, nat.lt_one_iff],
    have h10 := finite_dimensional.fin_basis (zmod 2) (B →₀ zmod 2),
    rw h20 at h10,
    haveI : fintype (B →₀ zmod 2),
      apply finsupp.fintype,
    have h9 := @module.card_fintype _ (zmod 2) (B →₀ zmod 2) _ _ _ _ h10 _ _,
    simp only [zmod.card, fintype.card_fin] at h9,
    have h12 := fintype.card_le_of_embedding (embedding_of_subset _ _ h70),
    simp_rw [← to_finset_card, to_finset_diff] at h12,
    rw [finset.card_sdiff, span_univ, top_coe, to_finset_univ, finset.card_univ, h9,
      to_finset_card, to_finset_singleton, finset.card_singleton] at h12,
    have h80 : fintype.card (φ' '' (unif 2 4).E) = fintype.card (fin 4),
    { rw card_image_of_inj_on (φ'.inj_on_ground_of_simple (unif_simple 2 4 rfl.le)),
      simp only [unif_ground_eq, ← to_finset_card, to_finset_univ, finset.card_univ] },
    rw [h80, fintype.card_fin, pow_two, two_mul, nat.succ_add_sub_one] at h12,
    linarith,
    simp only [span_univ, top_coe, to_finset_univ, to_finset_subset, 
      finset.coe_univ, singleton_subset_iff], },
end

end unif_rep

variables [fintype α]

open_locale big_operators

-- should be an instance but i can't figure it out rn
lemma nontrivial_excluded_minor (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor matroid_in.is_binary M) : nontrivial M.E := 
begin
  by_contra,
  simp only [nontrivial_coe_sort, not_nontrivial_iff] at h,
  cases h.eq_empty_or_singleton with hempty hsing,
  { apply hM.1 (is_representable_of_rep (rep_empty (zmod 2) M hempty)) },
  { obtain ⟨x, hx⟩ := hsing,
    apply hM.1 (is_representable_of_rep (rep_singleton (zmod 2) M hx)) },
end

-- can remove hxy
lemma excluded_minor_noncoloop (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor {N : matroid_in α | N.is_representable 𝔽} M) {y : α} (hf : y ∈ M.E) : 
  ¬ M.cocircuit {y} :=
begin
  by_contra hcy,
  have h2 := (dual_circuit_iff_cocircuit.2 hcy).nonempty,
  rw [← ground_inter_left (hcy.subset_ground)] at h2,
  obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := hM.delete_mem h2,
  have hyMy : y ∉ (M ⟋ y).E,
      rw [contract_elem, contract_ground],
      apply not_mem_diff_of_mem (mem_singleton _),
    have φM := add_coloop_rep φ hyMy,
    simp only [excluded_minor, mem_minimals_prop_iff] at hM,
  apply hM.1,
  rw [contract_elem, contract_ground, ← delete_ground ] at hyMy,
  rw (add_coloop_eq (M ⟍ {y}) M hyMy).2 ⟨coloop_iff_cocircuit.2 hcy, 
    delete_elem M y⟩,
  apply is_representable_of_rep φM,
end
-- can remove hxy
lemma coindep_excluded_minor (M : matroid_in α) 
(hM : excluded_minor {N : matroid_in α | N.is_representable 𝔽} M) (x y : α) (hxy : x ≠ y) 
(hx : {x, y} ⊆ M.E) 
  : M.coindep {x, y} :=
begin
  by_contra,
  rw coindep_iff_forall_subset_not_cocircuit at h,
  push_neg at h,
  obtain ⟨K, hK1, hK2⟩ := h,
  have h2 := (dual_circuit_iff_cocircuit.2 hK2).nonempty,
  cases ssubset_or_eq_of_subset hK1 with hKs hKeq,
  obtain ⟨a, ⟨ha1, ha2⟩⟩ := ssubset_iff_subset_diff_singleton.1 hKs,
  obtain ⟨rfl | h2⟩ := (mem_insert_iff.1 ha1),
  -- duplicate code
  -- use add_coloop_rep,
  { simp only [insert_diff_of_mem, mem_singleton, diff_singleton_eq_self 
      (mem_singleton_iff.1.mt hxy), subset_singleton_iff_eq] at ha2,
    cases ha2 with hempty hs,
    { apply (nonempty_iff_ne_empty.1 h2) hempty },
    rw hs at *,
    apply excluded_minor_noncoloop M hM (singleton_subset_iff.1 hK2.subset_ground) hK2 },
  { rw mem_singleton_iff.1 h at *,
    rw [← union_singleton, union_comm, union_singleton] at *,
    simp only [insert_diff_of_mem, mem_singleton, diff_singleton_eq_self 
      (mem_singleton_iff.1.mt (ne.symm hxy)), subset_singleton_iff_eq] at ha2,
    cases ha2 with hempty hs,
    { apply (nonempty_iff_ne_empty.1 h2) hempty },
    rw hs at *,
    apply excluded_minor_noncoloop M hM (singleton_subset_iff.1 hK2.subset_ground) hK2 },
  rw hKeq at *,
  have hyy := singleton_nonempty y,
  rw ← ground_inter_left (insert_subset.1 hx).2 at hyy,
  --rw [ground_inter_left _] at hyy,
  have h3 := hM.contract_mem hyy,
  obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := h3,
  rw ← M.contract_elem y at φ, 
  have hxMy : x ∈ (M ⟋ y).E,
    rw [contract_elem, contract_ground],
    apply (mem_diff x).2,
    refine ⟨_, mem_singleton_iff.1.mt hxy⟩,
    apply mem_of_subset_of_mem hx,
    simp only [mem_insert_iff, eq_self_iff_true, true_or],
  have hyMy : y ∉ (M ⟋ y).E,
    rw [contract_elem, contract_ground],
    apply not_mem_diff_of_mem (mem_singleton _),
 --have hf := series_extend_eq (M ⟋ y) M hK2 hxMy rfl hyMy,
  simp only [excluded_minor, mem_minimals_prop_iff] at hM,
  apply hM.1,
  have hMx : ¬(M ⟋ y).coloop x,
    rw [contract_elem, coloop, contract_dual_eq_dual_delete, not_loop_iff, delete_nonloop_iff],
    rw [cocircuit, circuit_iff_dep_forall_diff_singleton_indep] at hK2,
    cases hK2 with hxy2 hin,
    specialize hin y (mem_insert_of_mem _ (mem_singleton y)),
    rw [insert_eq, union_comm, ← insert_eq, insert_diff_of_mem _ (mem_singleton _),
      diff_singleton_eq_self (mem_singleton_iff.1.mt (ne.symm hxy))] at hin,
    refine ⟨indep_singleton.1 hin, mem_singleton_iff.1.mt hxy⟩,
  rw [(eq_series_extend_iff hxMy hMx hyMy).2 ⟨hK2, rfl⟩, mem_set_of],
  obtain φM := series_extend_rep φ hxMy hyMy hMx,
  exact is_representable_of_rep φM, 
end

lemma excluded_minor_nonloop (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor matroid_in.is_binary M) {f : α} (hf : f ∈ M.E) : M.nonloop f :=
begin
  by_contra,
  have hfM : ({f} ∩ M.E).nonempty,
    simp only [ground_inter_left, singleton_nonempty],
  obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := hM.delete_mem hfM,
  simp only [not_nonloop_iff] at h,
  apply hM.1 (is_representable_of_rep (rep_of_loop M h φ)),
end

lemma excluded_minor_nonpara (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor matroid_in.is_binary M) {x y : α} (hxy : x ≠ y) :
  ¬ M.circuit {x, y}  :=
begin
  by_contra,
  obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := hM.delete_mem (singleton_inter_nonempty.2 (mem_of_subset_of_mem 
    h.subset_ground (mem_insert_iff.2 (or.intro_right (y = x) (mem_singleton y))))),
  have hx : (M ⟍ y).nonloop x,
    rw [delete_elem, delete_nonloop_iff],
    cases circuit_iff_dep_forall_diff_singleton_indep.1 h with hxy2 hin,
    { specialize hin y (mem_insert_of_mem _ (mem_singleton y)),
      rw [insert_eq, union_comm, ← insert_eq, insert_diff_of_mem _ (mem_singleton _),
        diff_singleton_eq_self (mem_singleton_iff.1.mt (ne.symm hxy))] at hin,
      refine ⟨indep_singleton.1 hin, mem_singleton_iff.1.mt hxy⟩ },
    { have hy : y ∉ (M ⟍ y).E,
        rw [delete_elem, delete_ground],
        apply not_mem_diff_singleton,
      obtain φM := parallel_extend_rep φ hx hy,
      simp_rw ← delete_elem at φM,
      rw ← (eq_parallel_extend_iff hx hy).2 ⟨h, rfl⟩ at φM,
      apply hM.1 (is_representable_of_rep (rep_of_congr (rep_of_matroid_of_module_fun (zmod 2) 
        (B →₀ zmod 2) (λ (e : α), ite (e = y) (-φ x) (φ e)) (insert y (M ⟍ y).E)) φM)) },
end

lemma excluded_minor_simple (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor matroid_in.is_binary M) : simple M :=
begin
  apply λ e he f hf, (indep_iff_forall_subset_not_circuit (insert_subset.2 
    ⟨he, singleton_subset_iff.2 hf⟩)).2 (λ C hC, _),
  by_cases hef : e = f,
  { rw hef at *,
    rw insert_eq_of_mem (mem_singleton f) at hC,
    cases ssubset_or_eq_of_subset hC with hempty heq,
    { rw ssubset_singleton_iff.1 hempty,
      apply empty_not_circuit },
    { rw [heq, ← loop_iff_circuit],
      apply (excluded_minor_nonloop M hM hf).1 } },
  { cases ssubset_or_eq_of_subset hC with hC2 heq,
    { obtain ⟨x, ⟨hx1, hx2⟩⟩ := ssubset_iff_subset_diff_singleton.1 hC2,
      simp only [mem_insert_iff, mem_singleton_iff] at hx1,
      obtain ⟨rfl | rfl⟩ := hx1,
      { simp only [insert_diff_of_mem, mem_singleton, subset_diff] at hx2,
        cases (subset_iff_ssubset_or_eq.1 hx2.1) with hempty heq,
        { rw ssubset_singleton_iff.1 hempty,
          apply empty_not_circuit },
        { rw [heq, ← loop_iff_circuit],
          apply (excluded_minor_nonloop M hM hf).1 } }, 
      { rw hx1 at *,
        rw [← union_singleton, union_comm, union_singleton] at hx2,
        simp only [insert_diff_of_mem, mem_singleton, 
          subset_diff] at hx2,
        cases (subset_iff_ssubset_or_eq.1 hx2.1) with hempty heq,
        { rw ssubset_singleton_iff.1 hempty,
          apply empty_not_circuit },
        { rw [heq, ← loop_iff_circuit],
          apply (excluded_minor_nonloop M hM he).1 } } },
    rw heq,
    apply excluded_minor_nonpara M hM hef },
end

lemma excluded_minor_binary_rk2 (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor (set_of matroid_in.is_binary) M) : M.rk = 2 :=
begin
  haveI hME := nontrivial_excluded_minor M hM,
  rw [nontrivial_coe_sort, nontrivial_iff_pair_subset] at hME,
  obtain ⟨x, ⟨y, ⟨hxy1, hxy2⟩⟩⟩ := hME,
  have h2 := coindep_excluded_minor M hM x y hxy1 hxy2,

  have hxyr : matroid_in.is_binary (M ⟍ ({x, y} : set α)),
    apply excluded_minor.delete_mem hM,
    rw ground_inter_left,
    apply insert_nonempty,

  obtain ⟨B, ⟨hBxy, ⟨φ⟩⟩⟩ := hxyr,

  obtain ⟨Bx, ⟨hBx, ⟨φx⟩⟩⟩ := (((excluded_minor_iff _ (@minor_closed_rep _ (zmod 2) _)).1 hM).2 x 
    (hxy2 (mem_union_left {y} (mem_singleton x)))).2,

  obtain ⟨By, ⟨hBy, ⟨φy⟩⟩⟩ := (((excluded_minor_iff _ (@minor_closed_rep _ (zmod 2) _)).1 hM).2 y 
    (hxy2 (mem_union_right {x} (mem_singleton y)))).2,
  
  have hB := coindep.base_of_basis_del h2 (delete_base_iff.1 hBxy),

  have hBy : (M ⟍ y).base B,
    rw [delete_elem, delete_base_iff],
    apply hB.basis_of_subset _,
    apply subset.trans,
    apply hBxy.subset_ground,
    rw [delete_ground, ← union_singleton, union_comm, ← diff_diff],
    apply diff_subset_diff_left (diff_subset _ _),
    apply diff_subset M.E ({y} : set α),
  
  have hBx : (M ⟍ x).base B,
    rw [delete_elem, delete_base_iff],
    apply hB.basis_of_subset _,
    apply subset.trans,
    apply hBxy.subset_ground,
    rw [delete_ground, ← union_singleton, ← diff_diff],
    apply diff_subset_diff_left (diff_subset _ _),
    apply diff_subset M.E ({x} : set α),
  
  have hMM'E : M.E = (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E).E,
    rw matroid_of_module_fun.ground,
  have hMM'x := delete_elem_eq_of_binary hBxy hBx hB φ φx,
  have hByx := hBxy,
  have hxyyx : M ⟍ {x, y} = M ⟍ {y, x},
    rw [← union_singleton, union_comm, union_singleton],
  rw [← union_singleton, union_comm, union_singleton] at hByx,
  have hMM'y := delete_elem_eq_of_binary hByx hBy hB (rep_of_congr φ hxyyx) φy,
  have hφ : ∀ (a : α), ((rep_of_congr φ hxyyx).standard_rep hByx) a = (φ.standard_rep hBxy) a,
  { intros a,
    rw φ.standard_rep_eq_of_congr hxyyx },
  simp_rw [λ (a : α), hφ a] at hMM'y,
  have hB' : (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E).base B,
  { rw hMM'x at hBx,
    rw hMM'y at hBy,
    rw [base_iff_basis_ground, ← @diff_empty _ (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E).E, 
      ← singleton_inter_eq_empty.2 (mem_singleton_iff.1.mt hxy1), diff_inter], 
    rw [delete_elem, delete_base_iff] at hBx hBy,
    apply basis.basis_union hBx hBy },
  have hMM'r : M.rk = (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E).rk,
  { rw [← hB'.card, hB.card] },
  have hnxy : ({x, y} : set α).ncard = 2,
    { rw ncard_eq_to_finset_card,
      simp only [finite.to_finset_insert, finite.to_finset_singleton],
      apply finset.card_insert_of_not_mem (finset.not_mem_singleton.2 hxy1) },
  have hMM' : M ≠ (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
    (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E),
    { by_contra,
      rw [excluded_minor, mem_minimals_prop_iff] at hM,
      apply hM.1,
      rw [h, mem_def],
      apply is_representable_of_rep (rep_of_matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
        (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E) },
    rw [ne.def, eq_iff_indep_iff_indep_forall, matroid_of_module_fun.ground] at hMM', 
    simp only [eq_self_iff_true, true_and, not_forall, exists_prop] at hMM',
    obtain ⟨Z, ⟨hZM, hZ⟩⟩ := hMM',
    rw [iff_def, not_and_distrib] at hZ,
    push_neg at hZ,
    cases hZ with hMZ hM'Z,
    { have hJZ : ∀ (J : set α), M.indep J → Z ⊆ J → J = {x, y}, 
      { intros J hMJ hZJ,
        -- duplicate code
        have hZx : x ∈ Z,
          { by_contra,
            have hZs : (M ⟍ x).indep Z,
            { rw [delete_elem, delete_indep_iff],
              refine ⟨hMZ.1, disjoint_singleton_right.2 h⟩ },
            rw [hMM'x, delete_elem] at hZs,
            apply hMZ.2 hZs.of_delete },
        have hZy : y ∈ Z,
          { by_contra,
            have hZs : (M ⟍ y).indep Z,
            { rw [delete_elem, delete_indep_iff],
              refine ⟨hMZ.1, disjoint_singleton_right.2 h⟩ },
            rw [hMM'y, delete_elem] at hZs,
            apply hMZ.2 hZs.of_delete },
        have hZxy := union_subset (singleton_subset_iff.2 hZy) (singleton_subset_iff.2 hZx),
        rw union_singleton at hZxy,
        by_contra,
        have hJxyM : ((J \ {x, y}) ∩ M.E).nonempty,
        { simp only [ground_inter_left],
          apply nonempty_iff_ne_empty.2,
          apply diff_eq_empty.1.mt, 
          by_contra h2,
          apply h (eq_of_subset_of_subset h2 (subset_trans hZxy hZJ)) },
        obtain ⟨BN, ⟨hBN, ⟨φN⟩⟩⟩ := hM.contract_mem hJxyM,
        have φN' := rep_of_contr _ (rep_of_matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
          (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E) (J \ {x, y})
          (by { rw matroid_of_module_fun.ground, apply subset_trans (diff_subset _ _) 
          hMJ.subset_ground }),
        apply h (indep_eq_doubleton_of_subset M (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
          (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E) hMM'r hMM'E 
          x y hxy1 (by { left, apply h2 }) hMM'x hMM'y hZx hZy hMZ.1 hMZ.2 hZJ hMJ φN φN') },
      obtain ⟨BZ, hBZ⟩ := hMZ.1,
      specialize hJZ BZ hBZ.1.indep hBZ.2,
      rw hJZ at *,
      rw [← hBZ.1.card, hnxy] },
  { have hJZ : ∀ (J : set α), (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E).indep J 
      → Z ⊆ J → J = {x, y}, 
    { intros J hMJ hZJ,
      have hZx : x ∈ Z,
        { by_contra,
        have hZs : ((matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
          (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, 
          (standard_rep φ hBxy) i) M.E) ⟍ x).indep Z,
        { rw [delete_elem, delete_indep_iff],
          refine ⟨hM'Z.1, disjoint_singleton_right.2 h⟩ },
        rw [← hMM'x, delete_elem] at hZs,
        apply hM'Z.2 hZs.of_delete },
      have hZy : y ∈ Z,
        { by_contra,
          have hZs : ((matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
            (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, 
            (standard_rep φ hBxy) i) M.E) ⟍ y).indep Z,
          { rw [delete_elem, delete_indep_iff],
            refine ⟨hM'Z.1, disjoint_singleton_right.2 h⟩ },
          rw [← hMM'y, delete_elem] at hZs,
          apply hM'Z.2 hZs.of_delete },
      have hZxy := union_subset (singleton_subset_iff.2 hZy) (singleton_subset_iff.2 hZx),
      rw union_singleton at hZxy,
      by_contra,
      have hJxyM' : ((J \ {x, y}) ∩ (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
            (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, 
            (standard_rep φ hBxy) i) M.E).E).nonempty,
      { simp only [ground_inter_left],
        apply nonempty_iff_ne_empty.2,
        apply diff_eq_empty.1.mt, 
        by_contra h2,
        apply h (eq_of_subset_of_subset h2 (subset_trans hZxy hZJ)) },
      obtain ⟨BN, ⟨hBN, ⟨φN⟩⟩⟩ := hM.contract_mem hJxyM',
      have φN' := rep_of_contr _ (rep_of_matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
        (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E) (J \ {x, y})
        (by { rw matroid_of_module_fun.ground, apply subset_trans (diff_subset _ _) 
        hMJ.subset_ground }),
      apply h (indep_eq_doubleton_of_subset (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
        (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E) M 
        (eq.symm hMM'r) (eq.symm hMM'E) x y hxy1 (by { right, apply h2 }) (eq.symm hMM'x)
        (eq.symm hMM'y) hZx hZy hM'Z.1 hM'Z.2 hZJ hMJ φN' φN) },
    obtain ⟨BZ, hBZ⟩ := hM'Z.1,
    specialize hJZ BZ hBZ.1.indep hBZ.2,
    rw hJZ at *,
    rw [hMM'r, ← hBZ.1.card, hnxy] },
end

lemma excluded_minor_binary_ncard (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor (set_of matroid_in.is_binary) M) : 2 ≤ M.E.ncard :=
by { rw [← excluded_minor_binary_rk2 M hM, rk_def], apply r_le_card }

lemma excluded_minor_binary_unif (hM : excluded_minor matroid_in.is_binary M) 
  (ψ : M ≃i unif 2 M.E.ncard) (h2 : 2 ≤ M.E.ncard) : 4 ≤ M.E.ncard :=
begin
  cases le_iff_eq_or_lt.1 (excluded_minor_binary_ncard M hM) with h2 h3,
  { by_contra,
    rw ← h2 at ψ, 
    obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := U22_binary,
    apply hM.1 (is_representable_of_rep (rep_of_iso _ _ ψ φ)) },
  { cases le_iff_eq_or_lt.1 (nat.add_one_le_iff.2 h3) with h2 h3,
    { by_contra, 
      rw ← h2 at ψ, 
      obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := U23_binary,
      apply hM.1 (is_representable_of_rep (rep_of_iso _ _ ψ φ)) },
    { apply nat.add_one_le_iff.2 h3 } },
end

lemma excluded_minor_binary (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor (set_of matroid_in.is_binary) M) : unif 2 4 ≤i M := 
begin
  obtain ⟨ψ⟩ := (iso_line_iff (excluded_minor_binary_ncard M hM)).2 ⟨excluded_minor_simple M hM,
    ⟨excluded_minor_binary_rk2 M hM, ⟨to_finite M.E, rfl⟩⟩⟩,
  apply iso_minor.trans (unif_iso_minor (excluded_minor_binary_unif hM ψ 
    (excluded_minor_binary_ncard M hM))) (ψ.symm.trans_iso_minor (minor.refl.iso_minor)),
end

lemma excluded_minor_binary_iso_unif (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor (set_of matroid_in.is_binary) M) : nonempty (M ≃i (unif 2 M.E.ncard)) := 
(iso_line_iff (excluded_minor_binary_ncard M hM)).2 ⟨excluded_minor_simple M hM,
⟨excluded_minor_binary_rk2 M hM, ⟨to_finite M.E, rfl⟩⟩⟩

lemma excluded_minor_binary_ncard4 (hM : excluded_minor matroid_in.is_binary M) : 4 = M.E.ncard :=
begin
  obtain ⟨ψ⟩ := excluded_minor_binary_iso_unif M hM,
  cases le_iff_eq_or_lt.1 (excluded_minor_binary_unif hM ψ (excluded_minor_binary_ncard M hM)) 
    with h3 h4,
  { apply h3 },
  { by_contra,
    obtain ⟨ψ2⟩ := (iso_line_iff (excluded_minor_binary_ncard M hM)).2 ⟨excluded_minor_simple M hM, ⟨excluded_minor_binary_rk2 M hM, 
      ⟨to_finite M.E, rfl⟩⟩⟩,
    have h4 := (excluded_minor_iff matroid_in.is_binary (@minor_closed_rep _ (zmod 2) _)).1 hM,
    obtain ⟨M', ⟨hM'M, ⟨g⟩⟩⟩ := iso_minor.trans (@unif_iso_minor _ _ 2 
      (excluded_minor_binary_unif hM ψ2 (excluded_minor_binary_ncard M hM))) (ψ2.symm.iso_minor),
    cases le_iff_eq_or_lt.1 (ncard_le_of_subset hM'M.ground_subset) with hcontra hlt,
    { apply h,
      rw [ncard_eq_to_finset_card M.E, finite.to_finset_eq_to_finset, to_finset_card, 
        ((fintype.bijective_iff_injective_and_card ψ2).1 ψ2.bijective).2, ← hcontra, 
        ncard_eq_to_finset_card M'.E, finite.to_finset_eq_to_finset, to_finset_card M'.E,
        ← ((fintype.bijective_iff_injective_and_card g).1 g.bijective).2, unif_ground_eq, 
        ← to_finset_card univ, to_finset_univ, finset.card_univ, fintype.card_fin, unif_ground_eq, 
        ← to_finset_card univ, to_finset_univ, finset.card_univ, fintype.card_fin] },
    { obtain ⟨e, ⟨heM, heM'⟩⟩ := exists_mem_not_mem_of_ncard_lt_ncard hlt, 
      apply U24_nonbinary,
      cases hM'M.minor_contract_or_minor_delete ((mem_diff e).2 ⟨heM, heM'⟩) with hMe hMe,
      { obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := is_rep_of_minor_of_is_rep _ hMe (h4.2 e heM).1,
        apply is_representable_of_rep (rep_of_iso _ _ g φ) },
      { obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := is_rep_of_minor_of_is_rep _ hMe (h4.2 e heM).2,
        apply is_representable_of_rep (rep_of_iso _ _ g φ) } } },
end

lemma excluded_minor_binary_iso_unif24 (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor (set_of matroid_in.is_binary) M) : nonempty (M ≃i (unif 2 4)) := 
by { rw excluded_minor_binary_ncard4 hM, apply excluded_minor_binary_iso_unif M hM }  

lemma U24_excluded_minor : excluded_minor (set_of matroid_in.is_binary) (unif 2 4) :=
begin
  apply (excluded_minor_iff (set_of matroid_in.is_binary) (@minor_closed_rep _ (zmod 2) _)).2 
    ⟨U24_nonbinary, λ e he, ⟨_, _⟩⟩,
  { obtain ⟨B, ⟨hB, ⟨φc⟩⟩⟩ := @U1k_representable (zmod 2) _ 3 _ _,
    obtain ⟨ψc⟩ := (contract_elem_unif 1 3 e),
    apply is_representable_of_rep (rep_of_iso _ _ ψc φc),
    simp only [one_le_bit1, zero_le'] },
  { obtain ⟨B, ⟨hB, ⟨φc⟩⟩⟩ := @U23_binary,
    obtain ⟨ψc⟩ := (delete_elem_unif 2 3 e),
    apply is_representable_of_rep (rep_of_iso _ _ ψc φc) },
end

lemma excluded_minor_binary_iff_iso_unif24 (M : matroid_in α) [finite_rk M] :
  excluded_minor (set_of matroid_in.is_binary) M ↔ nonempty (M ≃i (unif 2 4)) := 
begin
  refine ⟨λ hM, excluded_minor_binary_iso_unif24 M hM, λ hφ, _⟩,
  obtain ⟨φ2⟩ := hφ,
  apply (excluded_minor_iff (set_of matroid_in.is_binary) (@minor_closed_rep _ (zmod 2) _)).2 
    ⟨_, λ e he, _⟩,
  { by_contra,
    obtain ⟨B, ⟨hB, ⟨φ24⟩⟩⟩ := h,
    obtain φ := rep_of_iso _ _ φ2.symm φ24,
    apply U24_nonbinary (is_representable_of_rep (rep_of_iso _ _ φ2.symm φ24)) },
  have hcoe : (coe : M.E → α)⁻¹' {e} = {(⟨e, he⟩ : M.E)},
  { ext;
    simp only [mem_preimage, mem_singleton_iff],
    refine ⟨λ h, subtype.coe_eq_of_eq_mk h, λ h, by { rw h,
      apply subtype.coe_mk e he }⟩ },
  refine ⟨_, _⟩,
  obtain ⟨B, ⟨hB, ⟨φc⟩⟩⟩ := @U1k_representable (zmod 2) _ 3 _ _,
  obtain ⟨ψc⟩ := (contract_elem_unif 1 3 (φ2 ⟨e, he⟩)),
  rw [contract_elem, ← image_singleton, ← image_singleton, ← hcoe, ← iso.image] at ψc,
  apply is_representable_of_rep (rep_of_iso _ _ (iso.trans (contract_iso φ2 {e}) ψc) φc),
  simp only [one_le_bit1, zero_le'],

  obtain ⟨B, ⟨hB, ⟨φd⟩⟩⟩ := U23_binary,
  obtain ⟨ψd⟩ := (delete_elem_unif 2 3 (φ2 ⟨e, he⟩)),
  rw [delete_elem, ← image_singleton, ← image_singleton, ← hcoe, ← iso.image] at ψd,
  apply is_representable_of_rep (rep_of_iso _ _ (iso.trans (delete_iso φ2 {e}) ψd) φd),
end

lemma binary_iff_no_u24_minor (M : matroid_in α) [finite_rk M] : 
  matroid_in.is_binary M ↔ ¬ unif 2 4 ≤i M :=
begin
  refine ⟨λ hfM, _, λ h3, (@mem_iff_no_excluded_minor_minor _ M _ (matroid_in.is_binary) 
    (@minor_closed_rep _ (zmod 2) _)).2 (λ M' hM', _)⟩,
  { by_contra,
    obtain ⟨M', ⟨hM', ⟨ψ⟩⟩⟩ := h,
    apply ((excluded_minor_iff (set_of matroid_in.is_binary) (@minor_closed_rep _ (zmod 2) _)).1 
      ((excluded_minor_binary_iff_iso_unif24 M').2 ⟨ψ.symm⟩)).1 
      (is_rep_of_minor_of_is_rep _ hM' hfM) },
  { by_contra,
    obtain ⟨ψ⟩ := excluded_minor_binary_iso_unif24 M' hM',
    refine h3 ⟨M', ⟨h, ⟨ψ.symm⟩⟩⟩ },
end

end rep

end matroid_in
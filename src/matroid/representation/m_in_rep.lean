import analysis.inner_product_space.gram_schmidt_ortho
import data.zmod.basic
import linear_algebra.basis
import linear_algebra.linear_independent
import m_in.minor
import m_in.rank
import m_in.equiv


namespace set
variables {α β : Type*} {f : α → β}

open function

lemma injective_iff_forall_inj_on_pair : injective f ↔ ∀ a b, inj_on f {a, b} :=
⟨λ h a b, h.inj_on _, λ h a b hab,
  h _ _ (mem_insert _ _) (mem_insert_of_mem _ $ mem_singleton _) hab⟩

end set

noncomputable theory

open function set submodule finite_dimensional 
open_locale classical

universe u 
variables {α 𝔽 : Type*} [fintype α] {M : matroid_in α} {I B : set α} {x : α}
variables {W W' : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] [add_comm_group W'] [module 𝔽 W'] 
-- we should have semiring 𝔽 by default, idk why it doesn't see it
-- why did we have finite E and not fintype E?

namespace matroid_in

/- A `𝔽`-matroid_in representation is a map from the base of the matroid_in to `ι → 𝔽` such that a set -/
/-structure rep (𝔽 : Type*) [field 𝔽] (M : matroid_in α) (ι : Type) :=
(to_fun : α → ι → 𝔽)
(valid' : ∀ I : set α, linear_independent 𝔽 (λ e : I, to_fun e) ↔ M.indep I)

/-- `M` is `𝔽`-representable if it has an `𝔽`-representation. -/
def is_representable (𝔽 : Type*) [field 𝔽] (M : matroid_in α) : Prop := ∃ (ι : Type), nonempty (rep 𝔽 M ι)-/

structure rep (𝔽 W : Type*) [field 𝔽] [add_comm_group W] [module 𝔽 W] (M : matroid_in α) :=
(to_fun : α → W)
(valid' : ∀ (I : set α), linear_independent 𝔽 (to_fun ∘ coe : I → W) ↔ M.indep I)

/-- `M` is `𝔽`-representable if it has an `𝔽`-representation. -/
def is_representable (𝔽 : Type*) [field 𝔽] (M : matroid_in α) : Prop := 
  ∃ (W : Type) (hW : add_comm_group W) 
    (hFW : 
      @module 𝔽 W _ (@add_comm_group.to_add_comm_monoid W hW)), nonempty (@rep _ _ 𝔽 W _ hW hFW M)

-- shouldn't maximality be a consequence of exchange property?
def matroid_of_module_set (𝔽 W : Type*) [field 𝔽] [add_comm_group W] [module 𝔽 W] 
  [finite_dimensional 𝔽 W] (s : set W) : 
  matroid_in W := 
{ ground := s,
  base := λ v, v ⊆ s ∧ span 𝔽 v = span 𝔽 s ∧ linear_independent 𝔽 (coe : v → W),--(λ (e : v), e.1),
  exists_base' := 
    begin
      obtain ⟨B, ⟨hB1, hB2⟩⟩ := exists_linear_independent 𝔽 s,
      use ⟨B, ⟨hB1, hB2⟩⟩,
    end,
  base_exchange' := λ X Y hX hY a ha, 
    begin
      simp only at *,
      have h2 := linear_independent_iff_not_mem_span.1 hX.2.2 ⟨a, mem_of_mem_diff ha⟩, 
      simp only [subtype.coe_mk] at h2,
      have h3 : a ∈ span 𝔽 ((X \ {a}) ∪ Y),
      { have h7 := mem_of_subset_of_mem (@subset_span 𝔽 _ _ _ _ s) 
          (mem_of_subset_of_mem hX.1 (mem_of_mem_diff ha)),
        have h4 := span_mono (subset_union_right (X \ {a}) Y),
        rw ← hY.2.1 at h7,
        apply h4 h7 },
      have h4 : a ∉ ((X \ {a}) ∪ Y),
        { simp only [mem_union, not_mem_diff_singleton, false_or],
          apply not_mem_of_mem_diff ha },
      have h5 := (subset_union_left (X \ {a}) Y),
      have h7 := span_mono (union_subset (subset_trans (diff_subset X {a}) hX.1) hY.1),
      have h6 : span 𝔽 s = span 𝔽 (X \ {a} ∪ Y),
      { apply span_eq_of_le _ _ h7,
        have h10 := @subset_span 𝔽 _ _ _ _ s,  
        rw ← hY.2.1 at h10, 
        apply subset_span_trans h10 
          ((@span_le 𝔽 _ _ _ _ _ _).1 (span_mono (subset_union_right (X \ {a}) Y))) },
      rw ← hX.2.1 at h6,
      have h8 := linear_independent.mono (diff_subset X {a}) hX.2.2,
      have S := h8.extend (subset_union_left (X \ {a}) Y),
      have hS1 := h8.extend_subset (subset_union_left (X \ {a}) Y),
      have hS2 := h8.subset_extend (subset_union_left (X \ {a}) Y),
      have hS3 := h8.subset_span_extend (subset_union_left (X \ {a}) Y),
      have hS4 := h8.linear_independent_extend (subset_union_left (X \ {a}) Y),
      have h50 : ∃ b ∈ Y \ X, (X \ {a}) ∪ {b} = (h8.extend (subset_union_left (X \ {a}) Y)),
      { have h100 : ↥(h8.extend (subset_union_left (X \ {a}) Y)) ≃ X,
        { have h60 := basis.span hS4,
          have h61 := basis.span hX.2.2,
          rw [subtype.range_coe_subtype, set_of_mem_eq] at h60 h61,
          rw h6 at h61,
          rw ← span_eq_span hS3 ((@span_le 𝔽 _ _ _ _ _ _).1 (span_mono hS1)) at h60,
          apply basis.index_equiv h60 h61 },
        have h200 : ∃ b ∈ (h8.extend (subset_union_left (X \ {a}) Y)), b ∉ X,
        { sorry },
        obtain ⟨b, ⟨hb1, hb2⟩⟩ := h200,
        use b,
        have hb3 := mem_of_subset_of_mem hS1 hb1,
        refine ⟨(mem_diff _).2 ⟨or.resolve_left hb3 (not_mem_subset (diff_subset X {a}) hb2), hb2⟩, 
          _⟩,
        have h200 : X ≃ ↥(X \ {a} ∪ {b}),
        { have h61 := basis.span hX.2.2,
          have h63 := (linear_independent.mono (union_subset hS2 (singleton_subset_iff.2 hb1)) hS4),
          simp at h63,
          have h64 := basis.span h63,
          rw [subtype.range_coe_subtype, set_of_mem_eq] at h61 h64,
           
          apply basis.index_equiv h61,
          -- apply basis.index_equiv,
          sorry, },
        have f := equiv.trans h100 h200,
        
        ext;
        refine ⟨λ h, (union_subset hS2 (singleton_subset_iff.2 hb1)) h, λ hx, _⟩,
        have y := f.to_fun ⟨x, hx⟩,

        sorry },
      obtain ⟨b, ⟨hb1, hb2⟩⟩ := h50,
      use b,
      rw [← union_singleton, hb2],
      refine ⟨hb1, ⟨_, ⟨_, hS4⟩⟩⟩,
      have h2 : X \ {a} ∪ Y ⊆ s,
      { sorry }, 
      apply subset_trans hS1 h2,
      sorry,
    end,
  maximality := λ I X hI hIX, 
    begin
      simp only at *,
      obtain ⟨B, ⟨hBs, hBe⟩⟩ := hI,
      have h2 := linear_independent.mono hBe hBs.2.2,
      use (h2.extend hIX), 
      simp only [mem_maximals_iff'],
      refine ⟨⟨_, ⟨h2.subset_extend hIX, h2.extend_subset hIX⟩⟩, λ y hy hI'y, _⟩,
      -- i think X ⊆ s has to be stated in maximality.
      have h10 := exists_linear_independent_extension (h2.linear_independent_extend hIX),
      sorry,
      sorry,
      obtain ⟨⟨By, ⟨hB1, hB2, hBy⟩, hyBy⟩, hIy, hyX⟩ := hy,
      rw ← eq_of_linear_independent_of_span_subtype 
        (linear_independent.mono hyBy hBy) hI'y (subset_trans hyX (h2.subset_span_extend hIX)),
    end,
  subset_ground' := by tauto }

-- if M has rank 2, has at least 4 elements, and is simple, then M is deletion of U_{2, 4}
lemma unif24_of_rank_2_simple_le_4 (M : matroid_in α) (h2 : M.rk = 2) (hs : M.is_simple) : 
  ∃ (D : set α), (M ⟍ D) ≃i unif 2 4 :=
begin
  sorry,

end

namespace rep

instance fun_like : fun_like (rep 𝔽 W M) α (λ _, W) :=
{ coe := to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

instance : has_coe_to_fun (rep 𝔽 W M) (λ _, α → W) := fun_like.has_coe_to_fun

lemma valid (φ : rep 𝔽 W M) : linear_independent 𝔽 (λ e : I, φ e) ↔ M.indep I := φ.valid' _

protected lemma is_representable {W : Type} [add_comm_group W] [module 𝔽 W] (φ : rep 𝔽 W M) : 
  is_representable 𝔽 M := ⟨W, ⟨_, ⟨_, ⟨φ⟩⟩⟩⟩

lemma inj_on_of_indep (φ : rep 𝔽 W M) (hI : M.indep I) : inj_on φ I :=
inj_on_iff_injective.2 ((φ.valid' I).2 hI).injective

lemma eq_zero_of_not_mem_ground (φ : rep 𝔽 W M) {e : α} (he : e ∉ M.E) : φ e = 0 :=
begin
  sorry 
end  

@[simp] lemma to_fun_eq_coe (φ : rep 𝔽 W M) : φ.to_fun = (φ : α → W)  := by { ext, refl }

lemma linear_independent_iff_coe (φ : rep 𝔽 W M) (hI : M.indep I) :
  linear_independent 𝔽 (λ e : I, φ e) ↔ linear_independent 𝔽 (coe : φ '' I → W) :=
linear_independent_image $ inj_on_of_indep _ hI

def to_submodule (φ : rep 𝔽 W M) : submodule 𝔽 W := span 𝔽 (φ '' M.E)

lemma mem_to_submodule (φ : rep 𝔽 W M) (hx : x ∈ M.E) : φ x ∈ rep.to_submodule φ :=
by { rw [rep.to_submodule], refine subset_span _, simp, sorry }

def rep_submodule (φ : rep 𝔽 W M) : rep 𝔽 (rep.to_submodule φ) M := 
{ to_fun := λ a, --⟨φ x, _⟩,
    begin
      refine ⟨φ a, _⟩,
      /-have h2 := (rep.mem_to_submodule φ),
      apply h2,-/
      sorry,
    end,
  valid' := λ I, 
    begin
      have h8 : (λ (x : ↥I), φ x) = (λ (x : ↥I), ↑(⟨φ x, rep.mem_to_submodule φ x⟩ : (span 𝔽 (range ⇑φ)))),
        { simp only [subtype.coe_mk] },
      have h4 : linear_independent 𝔽 (λ (x : ↥I), φ x) ↔ linear_independent 𝔽 (λ (x : ↥I), (⟨φ x, rep.mem_to_submodule φ x⟩ : span 𝔽 (range ⇑φ))),
        { simp_rw [h8, ← submodule.coe_subtype],
          apply linear_map.linear_independent_iff ((span 𝔽 (range ⇑φ)).subtype) (ker_subtype (span 𝔽 (range ⇑φ))) },
      simp_rw [← h4], 
      apply φ.valid,
    end } 

def rep.compose (φ : rep 𝔽 W M) (e : rep.to_submodule φ ≃ₗ[𝔽] W') : rep 𝔽 W' M :=
{ to_fun := λ x, sorry,--e ⟨φ x, rep.mem_to_submodule φ x⟩,
  valid' :=
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

lemma ne_zero_of_nonloop (φ : rep 𝔽 W M) (hx : M.nonloop x) : φ x ≠ 0 :=
((φ.valid' {x}).2 hx.indep).ne_zero (⟨x, mem_singleton _⟩ : ({x} : set α))

lemma ne_zero_of_loopless (φ : rep 𝔽 W M) (hl : loopless M) (x : α) : φ x ≠ 0 :=
ne_zero_of_nonloop _ $ hl _

lemma injective_of_simple (φ : rep 𝔽 W M) (hs : simple M) : injective φ :=
injective_iff_forall_inj_on_pair.2 $ λ a b, inj_on_of_indep _ $ hs _ _

lemma subset_nonzero_of_simple (φ : rep 𝔽 W M) (hs : simple M) :
  φ '' M.E ⊆ span 𝔽 (φ '' M.E) \ {0} :=
begin
  refine subset_diff.2 ⟨subset_span, disjoint_left.2 _⟩,
  /-rintro _ ⟨x, rfl⟩,
  exact ne_zero_of_loopless _ hs.loopless _,-/
  sorry
end

lemma of_basis (φ : rep 𝔽 W M) {X I : set α} (hI : M.basis I X) {e : α} (he : e ∈ X): 
  φ e ∈ span 𝔽 (φ '' I) :=
begin
  by_cases e ∈ I, 
  { apply subset_span (mem_image_of_mem _ h) },
  /-have h2 : ¬ linear_independent 𝔽 (λ x : insert e I, φ x) := 
    (φ.valid' (insert e I)).not.2 (hI.insert_dep (mem_diff_of_mem he h)),
  contrapose! h2,
  apply (linear_independent_insert' h).2 ⟨(φ.valid' I).2 hI.indep, h2⟩,-/
  sorry,
end

lemma of_base (φ : rep 𝔽 W M) {B : set α} (hB : M.base B) (e : α) (he : e ∈ M.E) : 
  φ e ∈ span 𝔽 (φ '' B) :=
of_basis φ (base.basis_univ hB) he

lemma span_basis (φ : rep 𝔽 W M) {X I : set α} (hI : M.basis I X) : 
  span 𝔽 (φ '' I) = span 𝔽 (φ '' X) :=
begin
  refine (span_mono $ image_subset _ (basis.subset hI)).antisymm (span_le.2 _),
  rintros _ ⟨y, ⟨hy1, rfl⟩⟩,
  apply of_basis φ hI hy1,
end

lemma span_base (φ : rep 𝔽 W M) (hB : M.base B) : span 𝔽 (φ '' B) = span 𝔽 (φ '' M.E) := 
  by { rw [span_basis φ (base.basis_univ hB)] }

-- use span
/-lemma span_base' (φ : rep 𝔽 W M) (hB : _root_.basis B 𝔽 (span 𝔽 (φ '' M.E))) : 
  span 𝔽 (φ '' B) = span 𝔽 (φ '' M.E) :=
begin
  rw ← image_univ,
  refine (span_mono $ image_subset _ (subset_univ B)).antisymm (span_le.2 _),
  rintros _ ⟨y, ⟨hy1, rfl⟩⟩,
  
  sorry,
end-/

lemma basis_of_base (φ : rep 𝔽 W M) {B : set α} (hB : M.base B) :
  _root_.basis B 𝔽 (span 𝔽 (φ '' M.E)) :=
by { rw [←span_base _ hB, image_eq_range], exact basis.span 
  ((φ.valid' B (base.subset_ground hB)).2 hB.indep) }


/-lemma base_of_basis (φ : rep 𝔽 W M) {B : set α} (hB : linear_independent 𝔽 (φ '' B)) : --(hB : _root_.basis B 𝔽 (span 𝔽 (φ '' M.E))) : 
  M.base B :=
begin
  --rw ← image_eq_range at hB, 
  have h2 := (basis.linear_independent hB),
  rw ← span_base' φ hB at hB,

  sorry,
end-/

instance fin_dim_rep (φ : rep 𝔽 W M) [M.finite_rk] [fintype 𝔽] : 
  finite_dimensional 𝔽 (span 𝔽 (φ '' M.E)) :=
begin
  cases M.exists_base with B hB,
  apply finite_dimensional.of_finite_basis (basis_of_base φ hB) (base.finite hB),
end

@[simp] lemma mem_span_rep_range (φ : rep 𝔽 W M) : ∀ (x : α), φ x ∈ (span 𝔽 (range ⇑φ)) := 
  λ x, by { apply mem_of_subset_of_mem (@subset_span 𝔽 _ _ _ _ (range ⇑φ)) (mem_range_self x) }

@[simp] lemma mem_span_rep (φ : rep 𝔽 W M) : ∀ (x ∈ M.E), φ x ∈ (span 𝔽 (φ '' M.E)) := 
  λ x hx, by { apply mem_of_subset_of_mem (@subset_span 𝔽 _ _ _ _ (φ '' M.E)) 
  (mem_image_of_mem φ hx) }

lemma mem_span_cl (φ : rep 𝔽 W M) {x : α} {X : set α} (hX : X ⊆ M.E) (hx : x ∈ M.cl X) : 
  φ x ∈ span 𝔽 (φ '' X) :=
begin
  by_cases x ∈ X, 
  { apply mem_of_subset_of_mem (@subset_span 𝔽 _ _ _ _ (φ '' X)) (mem_image_of_mem φ h) },
  obtain ⟨I, hI⟩ := M.exists_basis X,
  rw [← span_basis φ hI, span_basis φ (indep.basis_cl (basis.indep hI)), basis.cl hI],
  apply mem_of_subset_of_mem (@subset_span 𝔽 _ _ _ _ (φ '' M.cl X)) (mem_image_of_mem φ hx),
end

/-lemma dual_rep_of_rep (φ : rep 𝔽 W M) [fintype 𝔽] : rep 𝔽 (module.dual 𝔽 W) M﹡ := 
{ to_fun := λ (e : α), subspace.dual_lift (span 𝔽 (range ⇑φ)) 
  (basis.to_dual (finite_dimensional.fin_basis 𝔽 (span 𝔽 (φ '' M.E))) 
  ⟨φ e, mem_span_rep _ e⟩),
  valid' := λ I, 
    begin
      refine ⟨λ h, _, λ h, _⟩,
      sorry,  
      sorry,
    end }-/


def rep_of_del (N : matroid_in α) (φ : rep 𝔽 W N) (D : set α) : 
rep 𝔽 W (N ⟍ D) := 
{ to_fun := λ x, if x ∈ D then (0 : W) else φ x,
  valid' := λ I,
    begin
      rw delete_indep_iff,
      refine ⟨λ h, _, λ h, _⟩,
      -- deterministic timeout if i plug this in directly
      have h5 := linear_independent.restrict_of_comp_subtype h,
      have h4 : ∀ x : I, (I.restrict (λ (x : α), ite (x ∈ D) 0 (φ x))) x ≠ 0 :=
      by { intros x, apply linear_independent.ne_zero x h5 },
      simp only [restrict_apply, ne.def, ite_eq_left_iff, not_forall, 
        exists_prop, set_coe.forall, subtype.coe_mk] at h4,
      refine ⟨_, disjoint_left.2 (λ a ha, (h4 a ha).1)⟩,
      have h10 : (λ (x : α), ite (x ∈ D) 0 (φ x)) ∘ (coe : I → α) = φ ∘ (coe : I → α),
      { ext;
        simp only [ite_eq_right_iff],
        specialize h4 x.1 x.2,
        rw imp_iff_not_or,
        left,
        apply h4.1 },
      rw h10 at h,
      rw ← φ.valid',
      apply h,
      have h10 : (λ (x : α), ite (x ∈ D) 0 (φ x)) ∘ (coe : I → α) = φ ∘ (coe : I → α),
      { ext;
        simp only [ite_eq_right_iff],
        rw imp_iff_not_or,
        left,
        rw disjoint_left at h,
        apply h.2 x.2 },
      rw h10,
      apply (φ.valid' I).2 h.1,
    end }
   --by { rw delete_ground at hI, 
    /-refine ⟨λ h, delete_indep_iff.2 ⟨((φ.valid' I (subset_trans hI (diff_subset N.E D))).1 h), 
    (subset_diff.1 hI).2⟩, λ h, (φ.valid' I (subset_trans hI (diff_subset N.E D))).2 
    (matroid_in.delete_indep_iff.1 h).1⟩, } }-/

lemma linear_independent.map'' {ι : Type*} {v : ι → W} (hv : linear_independent 𝔽 v) (f : W →ₗ[𝔽] W')
   (hfv : linear_independent 𝔽 (f ∘ v)) : disjoint (span 𝔽 (range v)) f.ker :=
begin
  rw [disjoint_iff_inf_le, ← set.image_univ, finsupp.span_image_eq_map_total,
    map_inf_eq_map_inf_comap,
    map_le_iff_le_comap, comap_bot, finsupp.supported_univ, top_inf_eq],
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
  (@add_comm_group.to_add_comm_monoid W' _inst_5) _ _inst_6 f h, 
  disjoint.comm.1 (linear_independent.map'' (@linear_independent.of_comp _ _ _ W' _ _ _ 
  (@add_comm_group.to_add_comm_monoid W' _inst_5) _ _inst_6 f h) _ h)⟩, 
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
  --rw disjoint_def,
  rw [set.disjoint_iff, subset_empty_iff, eq_empty_iff_forall_not_mem] at hst,
  have h20 := λ (x : W) (h : x ∈ s), mem_union_left t h,
  --have h21 := (coe : s ∪ t → set W) ⁻¹' s,
  --have h10 := @linear_independent.disjoint_span_image _ 𝔽 W ((λ (x : (s ∪ t)), x)) _ _ _ hst2,
  sorry
end

def rep_of_contr (N : matroid_in α) (φ : matroid_in.rep 𝔽 W N) (C : set α) (hC : C ⊆ N.E):
  matroid_in.rep 𝔽 (W ⧸ span 𝔽 (φ.to_fun '' C)) (N ⟋ C) := 
{ to_fun := λ x, submodule.quotient.mk (φ.to_fun x),
  valid' := λ I,
    begin
      have h21 : (λ (x : ↥I), φ.to_fun ↑x) '' univ = φ.to_fun '' I,
        { simp,
          ext;
          simp only [mem_range, set_coe.exists, subtype.coe_mk, exists_prop, mem_image] },
      obtain ⟨J, hJ⟩ := exists_basis N C hC,
      rw [basis.contract_eq_contract_delete hJ, delete_indep_iff, 
        indep.contract_indep_iff hJ.indep],
      have h10 := span_basis φ hJ,
      refine ⟨λ h, _, λ h, _⟩,  
      simp at h,
      simp_rw [← mkq_apply _] at h,
      rw ← φ.valid' _,
      have h30 : disjoint (span 𝔽 (φ.to_fun '' I)) (span 𝔽 (φ.to_fun '' J)),
      { simp_rw [← to_fun_eq_coe] at h10,
        rw h10,
        simp at h10,
        simp_rw [← to_fun_eq_coe],
        rw ← ker_mkq (span 𝔽 (φ.to_fun '' C)),
        rw [linear_map.linear_independent_iff, ← image_univ, h21, disjoint.comm] at h,
        exact h.2 },
      have h7 := linear_independent.image 
        (linear_independent.of_comp ((span 𝔽 (φ '' C)).mkq) h),
      have h8 := linear_independent.image ((φ.valid' J).2 (hJ.indep)),
      have h6 := linear_independent.union h7 h8 h30,
      rw [linear_independent_image, image_union],
      refine ⟨⟨_root_.disjoint.of_image (linear_independent.union' h7 h8 h30 h6), h6⟩, _⟩,
      sorry,
      rw inj_on_union (_root_.disjoint.of_image (linear_independent.union' h7 h8 h30 h6)),
      refine ⟨φ.inj_on_of_indep ((φ.valid' I).1 
        (linear_independent.of_comp ((span 𝔽 (φ '' C)).mkq) h)), 
        ⟨φ.inj_on_of_indep (hJ.indep), λ x hx y hy, set.disjoint_iff_forall_ne.1 
        (linear_independent.union' h7 h8 h30 h6) (φ x) (mem_image_of_mem φ hx) 
        (φ y) (mem_image_of_mem φ hy)⟩⟩,
      simp_rw [← mkq_apply _],
      rw linear_map.linear_independent_iff,
      refine ⟨(φ.valid' I).2 (indep.subset h.1.2 (subset_union_left I J)), _⟩,
      rw ker_mkq (span 𝔽 (φ.to_fun '' C)),
      have h60 := linear_independent.image ((φ.valid' _).2 h.1.2),
      rw image_union at h60,
      rw [← image_univ, h21],
      simp_rw [to_fun_eq_coe],
      rw [← h10],
      simp only,
      apply linear_independent.union'',
      { apply linear_independent.image 
          ((φ.valid' J).2 (indep.subset h.1.2 (subset_union_right I J))) },
      { apply linear_independent.image 
          ((φ.valid' I).2 
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
    end }

theorem finrank_span_set_eq_ncard {K V : Type*} [division_ring K] [add_comm_group V] 
  [module K V] (s : set V) (hs : linear_independent K (coe : s → V)) :
finite_dimensional.finrank K (submodule.span K s) = s.ncard :=
begin
  by_cases s.finite,
  { haveI := (finite.fintype h),
    rw [finrank_span_set_eq_card s hs, to_finset_card, 
      ncard_eq_to_finset_card, finite.card_to_finset] },
  { -- i'm doing this in a roundabout way because the finrank lemmas that talk
    -- about something not being finite dimensional require all bases to not be
    -- finite, which is true but this feels easier
    rw infinite.ncard h,
    apply finrank_of_infinite_dimensional,
    by_contra h3,
    apply h,
    have h8 : span K (range (coe : s → V)) = span K s,
    simp only [subtype.range_coe_subtype, set_of_mem_eq],
    apply basis.finite_index_of_dim_lt_aleph_0 (basis.span hs),
    rw [← is_noetherian.iff_dim_lt_aleph_0, is_noetherian.iff_fg, h8],
    apply h3 },
end 


lemma of_r (φ : rep 𝔽 W M) (X : set α) : finite_dimensional.finrank 𝔽 (span 𝔽 (φ '' X)) = M.r X :=
begin
  obtain ⟨I, hI⟩ := M.exists_basis X, 
  rw [←hI.card, ←φ.span_basis hI, finrank_span_set_eq_ncard, 
    ncard_image_of_inj_on (inj_on_of_indep _ hI.indep) ], 
  exact linear_independent.image (φ.valid.mpr hI.indep), 
end

lemma of_rank (φ : rep 𝔽 W M) : finite_dimensional.finrank 𝔽 (span 𝔽 (φ '' M.E)) = M.rk :=
by { convert of_r φ univ; simp }

lemma cl_subset_span_range (φ : rep 𝔽 W M) (X : set α) : φ '' M.cl X ⊆ span 𝔽 (φ '' M.E) :=
by { rintros _ ⟨x, ⟨hx, rfl⟩⟩, apply mem_span_rep φ x hx.2 }

lemma cl_subset_span_set (φ : rep 𝔽 W M) {X : set α} (hX : X ⊆ M.E) : 
  φ '' M.cl X ⊆ span 𝔽 (φ '' X) :=
by { rintros _ ⟨x, ⟨hx, rfl⟩⟩, apply mem_span_cl φ hX hx }

--lemma rep_of_minor (φ : rep 𝔽 W M) (N : matroid_in α) (hNM : N ≤ matroid_in.to_matroid_in M) : 

end rep

variables {ι : Type}

structure rep' (𝔽 : Type*) [field 𝔽] (M : matroid_in α) (ι : Type) :=
(to_fun : α → ι → 𝔽)
(valid' : ∀ I : set α, linear_independent 𝔽 (λ e : I, to_fun e) ↔ M.indep I)

namespace rep'

lemma valid (φ : rep' 𝔽 M ι) : linear_independent 𝔽 (λ e : I, φ.to_fun e) ↔ M.indep I := φ.valid' _

instance fun_like : fun_like (rep' 𝔽 M ι) E (λ _, ι → 𝔽) :=
{ coe := rep'.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

instance : has_coe_to_fun (rep' 𝔽 M ι) (λ _, E → ι → 𝔽) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe' (φ : rep' 𝔽 M ι) : φ.to_fun = (φ : α → ι → 𝔽)  := by { ext, refl }

lemma inj_on_of_indep' (φ : rep' 𝔽 M ι) (hI : M.indep I) : inj_on φ I :=
inj_on_iff_injective.2 ((rep'.valid' φ I).2 hI).injective

def rep_of_rep' (φ : rep' 𝔽 M ι) : rep 𝔽 (ι → 𝔽) M := ⟨φ, λ I, φ.valid' I⟩    

noncomputable def rep'_of_rep [finite_dimensional 𝔽 W] (φ : rep 𝔽 W M) {n : ℕ} (h : finrank 𝔽 W = n) : 
  rep' 𝔽 M (fin n)  := 
{ to_fun := λ v, (linear_equiv.of_finrank_eq W (fin n → 𝔽) (by simpa) :  W ≃ₗ[𝔽] (fin n → 𝔽)) (φ v), 
  valid' := λ I, 
  begin
    rw [←φ.valid', rep.to_fun_eq_coe], 
    exact (linear_equiv.of_finrank_eq _ _ (by simpa) : 
    W ≃ₗ[𝔽] (fin n → 𝔽)).to_linear_map.linear_independent_iff (linear_equiv.ker _), 
  end }

lemma of_base' (φ : rep' 𝔽 M ι) {B : set α} (hB : M.base B) (e : α) : φ e ∈ span 𝔽 (φ '' B) :=
begin
  by_cases e ∈ B,
  { exact subset_span (mem_image_of_mem _ h) },
  have h2 : ¬ linear_independent 𝔽 (λ x : insert e B, φ x) := φ.valid.not.2 (hB.dep_of_insert h),
  contrapose! h2,
  exact (linear_independent_insert' h).2 ⟨φ.valid.2 hB.indep, h2⟩,
end

lemma span_base' (φ : rep' 𝔽 M ι) (hB : M.base B) :
  span 𝔽 (φ '' B) = span 𝔽 (φ '' M.E) :=
begin
  --refine (span_mono $ image_subset_range _ _).antisymm (span_le.2 _),
  ext;
  exact of_base' _ hB _,
end

lemma basis_of_base' (φ : rep' 𝔽 M ι) {B : set α} (hB : M.base B) :
  _root_.basis B 𝔽 (span 𝔽 (φ '' M.E)) :=
by { rw [←span_base' _ hB, image_eq_range], exact basis.span ((rep'.valid' φ B).2 hB.indep) }

instance fin_dim_rep' (φ : rep' 𝔽 M ι) [finite E] [fintype 𝔽] : 
  finite_dimensional 𝔽 (span 𝔽 (φ '' M.E)) :=
begin
  cases M.exists_base with B hB,
  apply finite_dimensional.of_finite_basis (basis_of_base' φ hB) (base.finite hB),
end

lemma of_rank' (φ : rep' 𝔽 M ι) [fintype 𝔽] :
  finite_dimensional.finrank 𝔽 (span 𝔽 (φ '' M.E)) = M.rk :=
begin
  cases M.exists_base with B hB,
  -- need basis for this to work
  have h3 := finite_dimensional.fin_basis 𝔽 (span 𝔽 (set.φ '' M.E)),
  rw [←span_base' φ hB, finrank_span_set_eq_card (φ '' B)],
  have h6 : (⇑φ '' B).to_finset.card = B.to_finset.card,
  { simp_rw to_finset_card,
    rw ← card_image_of_inj_on (inj_on_of_indep' φ (base.indep hB)) },
  rw h6,
  simp only [← base.card hB, ncard_def, to_finset_card, nat.card_eq_fintype_card],
  have h8 : linear_independent 𝔽 (λ (x : B), φ (x : α)),
  rw [← to_fun_eq_coe', rep'.valid φ],
  apply hB.indep,
  apply linear_independent.image_of_comp B φ coe h8,
end

end rep'

namespace rep

-- we have fin_dim_vectorspace_equiv
lemma foo (φ' : rep 𝔽 W M) [fintype 𝔽] [finite_dimensional 𝔽 W] :
  nonempty (rep' 𝔽 M (fin M.rk))  :=
begin
  have φ := rep'.rep'_of_rep (φ'.rep_submodule) (of_rank φ'),
  have h1 := eq.symm (@finite_dimensional.finrank_fin_fun 𝔽 _ sorry (M.rk)),
  rw [← rep'.of_rank' φ, ← finite_dimensional.nonempty_linear_equiv_iff_finrank_eq] at h1, 
  cases h1 with l,
  have h3 := λ (x : α), mem_of_subset_of_mem (@subset_span 𝔽 _ _ _ _ (range ⇑φ)) (mem_range_self x),
  use φ,
end

lemma foo' (φ : rep 𝔽 W M) [fintype 𝔽] [finite_dimensional 𝔽 W] :
  nonempty (rep 𝔽 (fin M.rk → 𝔽) M) :=
begin
  cases foo φ with φ,
  use rep'.rep_of_rep' φ,
end

def std_rep' (φ' : rep 𝔽 W M) {B : set α} (hB : M.base B) : 
  rep 𝔽 (B → 𝔽) M := sorry

@[simp]
lemma id_matrix_of_base (φ : rep 𝔽 W M) {B : set α} (e : B) (hB : M.base B) : 
  std_rep' φ hB e.1 e = 1 :=
sorry

lemma id_matrix_of_base' (φ : rep 𝔽 W M) {B : set α} (e f : B) (hB : M.base B) (hne : e ≠ f) : 
  std_rep' φ hB e.1 f = 0 :=
sorry

-- ∃ (c : ι →₀ R), x = finsupp.sum c (λ i x, x • b i)
lemma mem_sum_basis' (φ : rep 𝔽 W M) {B : set α} (e : α) (hB : M.base B) :
  ∃ (I : B →₀ 𝔽) , finsupp.sum I (λ i x, std_rep' φ hB i) = std_rep' φ hB e :=
begin

  sorry,
end

open_locale big_operators

--lemma mem_span_of_mem_cl 

lemma mem_span_set_rep (φ : rep 𝔽 W M) {I : set α} (hI : M.indep I) 
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
  have h7 := (linear_independent_iff_not_mem_span.1 ((φ.valid' (M.fund_circuit e I \ {y})).2 
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
      rw mem_diff_singleton,
      refine ⟨ha1, _⟩,
      by_contra,
      rw h at ha3,
      apply ha3,
      simp only [mem_singleton],
      refine ⟨_, _⟩,
      simp only [mem_diff, mem_univ, mem_singleton_iff, subtype.mk_eq_mk, true_and],
      apply ha2,
      simp only [subtype.coe_mk]} },
  rw h9 at h7, 
  apply h7,
  exact mem_span_set.2 h5,
end

-- use finsum instead of finset.sum
lemma mem_sum_basis_zmod2 [module (zmod 2) W] (φ : rep (zmod 2) W M) {I : set α} (hI : M.indep I) 
(e : α) (he : e ∈ M.cl I) (heI : e ∉ I) :
  ∑ i in (M.fund_circuit e I \ {e}).to_finset, φ i = φ e :=
begin
  have h3 := subset_insert e (M.fund_circuit e I),
  obtain ⟨c, ⟨hc1, hc2⟩⟩ := mem_span_set_rep φ hI e he heI,
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
    haveI := (@add_comm_group.to_add_comm_monoid W _inst_3),
    --rw ← @one_smul W (zmod 2) (@add_comm_group.to_add_comm_monoid W _inst_3) _ (φ x),
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

structure std_rep (𝔽 W : Type*) [field 𝔽] [add_comm_group W] [module 𝔽 W] (M : matroid_in α) 
{B : set α} (hB : M.base B) extends rep 𝔽 W M :=
(basis : true)

/- A matroid_in is binary if it has a `GF(2)`-representation -/
@[reducible, inline] def matroid_in.is_binary (M : matroid_in α) := M.is_representable (zmod 2)

-- part (iii) in the proof of theorem 6.5.4
lemma indep_eq_doubleton_of_nonbinary (M : matroid_in α) (hM : ¬ M.is_binary) (hI : M.indep I)
  {Z : set α} {x y : α} (hxy : M.rk = M.r (univ \ {x, y})) (hxy2 : {x, y} ⊆ Z) : I = {x, y} :=
begin
  sorry,
end


lemma U24_simple : (unif 2 4).simple :=
begin
  have h2 := (unif_on_simple_iff (fin 4)),
  simp only [nat.card_eq_fintype_card, fintype.card_fin, nat.one_lt_bit0_iff, nat.one_le_bit0_iff, nat.lt_one_iff,
  eq_self_iff_true, forall_true_left] at h2,
  rw h2,
  simp only [nat.one_lt_bit0_iff],
end

lemma U23_binary : (unif 2 3).is_binary :=
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
  
  simp only [to_finset_card, card_singleton],
  sorry,
  simp only [to_finset_univ, to_finset_subset, finset.coe_univ, singleton_subset_iff],
  --rw ← fintype.card_fin 3 at h2,
  have f := equiv.symm (fintype.equiv_fin_of_card_eq h2),
  have φ := @rep.mk _ _ (zmod 2) (fin 2 → zmod 2) _ _ _ (unif 2 3) (λ x, ↑(f.to_fun x)) _,
  rw [matroid_in.is_binary, is_representable],
  { refine ⟨(fin 2 → zmod 2), ⟨_, ⟨_, ⟨φ⟩⟩⟩⟩ },
  intros I,
  have h3 := @finrank_fin_fun (zmod 2) _ sorry 2,
  refine ⟨λ h, _, λ h, _⟩,  
  -- now the possible sizes of vector families for h are 0, 1, 2.
  have h4 := fintype_card_le_finrank_of_linear_independent h,
  rw h3 at h4,
  apply unif.indep_iff.2,
  { rw [ncard, nat.card_eq_fintype_card],
    apply h4 },
  { sorry },
  have h5 := inj_on_of_injective (equiv.injective f),
  rw [unif.indep_iff, le_iff_lt_or_eq] at h,
  cases h with h1 h2,
  have h4 := nat.le_of_lt_succ h1,
  rw le_iff_lt_or_eq at h4,
  cases h4 with h0 h1,
  have h5 := nat.lt_one_iff.1 h0,
  simp only [ncard_eq_zero] at h5,
  rw h5,
  simp only [equiv.to_fun_as_coe],
  --have h6 := (linear_independent_image sorry).2,
  --apply linear_independent_empty,
  sorry,
  rw ncard_eq_one at h1,
  cases h1 with a ha,
  --rw ha,
  simp,
  --have h7 := linear_independent_image,
  --have h6 := linear_independent_image (inj_on_of_injective ↑(equiv.injective f) I),
  sorry,
  --have h2 := linear_independent_singleton,
  sorry,
end

-- i think we need something that says if a matroid_in is finite it has 
-- a finite dimensional representation

-- this doesn't have sorry's but it relies on foo and U24_simple which do
lemma U24_nonbinary : ¬ (unif 2 4).is_binary :=
begin
  by_contra h2,
  rw [matroid_in.is_binary, is_representable] at h2,
  rcases h2 with ⟨W, ⟨hW, ⟨hM, ⟨φ'⟩⟩⟩⟩,
  haveI := zmod.fintype 2,
  have φ := rep.rep_submodule φ',
  rw rep.to_submodule at φ,
  cases foo' φ with φ,
  rw [unif_on_rk] at φ,
  { have h8 := card_le_of_subset (φ.subset_nonzero_of_simple U24_simple),
    -- need basis
    have h9 := module.card_fintype (finite_dimensional.fin_basis (zmod 2)
      (span (zmod 2) (φ '' M.E))),
    rw [rep.of_rank, unif_on_rk] at h9,
    { -- there's probably a cleaner way to talk about the card of diff than going
      -- between fintype and finset cards
      simp_rw [← to_finset_card, to_finset_diff] at h8,
      rw finset.card_sdiff at h8,
      { simp only [set.to_finset_card, set_like.coe_sort_coe, card_singleton] at h8,
        simp only [fintype.card_of_finset, zmod.card, fintype.card_fin] at h9,
        rw h9 at h8,
        have h11 : fintype.card (φ '' M.E) = fintype.card (fin 4),
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

-- need the one-dimensional subspaces lemma for this
lemma card_of_unif_rep (k : ℕ) (hk : 1 < k) (h2 : is_representable 𝔽 (unif 2 k)) [fintype 𝔽]: 
  k - 1 ≤ ncard (@univ 𝔽) :=
begin
  rcases h2 with ⟨W, ⟨hW, ⟨hM, ⟨φ'⟩⟩⟩⟩,
  have φ'' := @rep.rep_submodule _ _ _ _ _ _ hW hM φ',
  rw rep.to_submodule at φ'',
  cases foo' φ'' with φ,
  rw [unif_on_rk] at φ,
  { have hs : (unif 2 k).simple,
    rw [← fintype.card_fin k, ← nat.card_eq_fintype_card] at hk,
    apply (@unif_on_simple_iff (fin k) hk 2).2,
    simp only [nat.one_lt_bit0_iff, le_refl, forall_true_left],
    have h8 := card_le_of_subset (φ.subset_nonzero_of_simple hs),
    have h9 := module.card_fintype (finite_dimensional.fin_basis 𝔽
      (span 𝔽 (φ '' M.E))),
    rw [rep.of_rank, unif_on_rk] at h9,
    { simp_rw [← to_finset_card, to_finset_diff] at h8,
      rw finset.card_sdiff at h8,
    { simp only [set.to_finset_card, set_like.coe_sort_coe, card_singleton] at h8,
      simp only [fintype.card_of_finset, zmod.card, fintype.card_fin] at h9,
      rw h9 at h8,
      simp_rw card_range_of_injective (φ.injective_of_simple hs) at *,
      simp only [fintype.card_fin, ← nat.card_eq_fintype_card] at h8,
      by_contra hle,
      push_neg at hle,
      have hsubs : ∀ (x y : (fin k)), φ y ∈ (𝔽 ∙ φ x) → x = y, 
      intros x y hxy,
      sorry },
    { simp only [set.to_finset_subset, coe_to_finset, singleton_subset_iff,
        set_like.mem_coe, zero_mem] } },
    simp only [nat.card_eq_fintype_card, fintype.card_fin],
    apply hk, },
  simp only [nat.card_eq_fintype_card, fintype.card_fin],
  apply hk,
end

end rep

-- lemma foo (e f : α) (hne : e ≠ f) (h : M.r {e,f} = 1) :

end matroid_in


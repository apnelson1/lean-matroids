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

instance fun_like {𝔽 W : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] {M : matroid_in α } : 
  fun_like (rep 𝔽 W M) α (λ _, W) := 
{ coe := λ φ e, φ.to_fun e,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

instance : has_coe_to_fun (rep 𝔽 W M) (λ _, α → W) := fun_like.has_coe_to_fun

/-- `M` is `𝔽`-representable if it has an `𝔽`-representation. -/
def is_representable (𝔽 : Type*) [field 𝔽] (M : matroid_in α) : Prop := 
  ∃ (W : Type) (hW : add_comm_group W) 
  (hFW : @module 𝔽 W _ (@add_comm_group.to_add_comm_monoid W hW)), nonempty (@rep _ 𝔽 W _ hW hFW M)

def matroid_of_module_set (𝔽 W : Type*) [field 𝔽] [add_comm_group W] [module 𝔽 W] 
  [finite_dimensional 𝔽 W] (s : set W) : 
  matroid_in W := matroid_of_indep_of_bdd' s 
  (λ (I : set W), (linear_independent 𝔽 (coe : I → W)) ∧ I ⊆ s) 
  ⟨linear_independent_empty 𝔽 W, empty_subset s⟩ 
  (λ I J hI hIJ, ⟨linear_independent.mono hIJ hI.1, 
    subset.trans hIJ hI.2⟩) 
  begin
    intros I J hI hJ hIJ,
    haveI := finite.fintype (_root_.linear_independent.finite hI.1),
    haveI := finite.fintype (_root_.linear_independent.finite hJ.1),
    have h3 : ∃ x ∈ J, x ∉ span 𝔽 I,
      by_contra,
      push_neg at h,
      have h8 : (J.to_finite.to_finset) = J.to_finset,
        ext,
        simp only [finite.mem_to_finset, mem_to_finset],
      have h9 : (I.to_finite.to_finset) = I.to_finset,
        ext,
        --simp only [finite.mem_to_finset, mem_to_finset],
        simp only [finite.mem_to_finset, mem_to_finset],
      apply not_le_of_lt hIJ,
      rw [ncard_eq_to_finset_card, ncard_eq_to_finset_card, h8, h9, 
        ← finrank_span_set_eq_card I hI.1, ← finrank_span_set_eq_card J hJ.1],
      apply submodule.finrank_le_finrank_of_le (span_le.2 (λ x hx, h x hx)),
    obtain ⟨x, ⟨hx1, hx2⟩⟩ := h3,
    refine ⟨x, ⟨hx1, ⟨_, ⟨linear_independent.insert hI.1 hx2, 
      insert_subset.2 ⟨mem_of_subset_of_mem hJ.2 hx1, hI.2⟩⟩⟩⟩⟩,  
    by_contra,
    apply hx2,
    apply mem_of_subset_of_mem subset_span h
  end
  begin
    refine ⟨finite_dimensional.finrank 𝔽 W, λ I hI, _⟩,
    haveI := finite.fintype (_root_.linear_independent.finite hI.1),
    rw [ncard, nat.card_eq_fintype_card],
    refine ⟨_root_.linear_independent.finite hI.1, 
      fintype_card_le_finrank_of_linear_independent hI.1⟩,
  end
  (by {tauto})

lemma ground_matroid_of_module_set (𝔽 W : Type*) [field 𝔽] [add_comm_group W] [module 𝔽 W] 
  [finite_dimensional 𝔽 W] (s : set W) : (matroid_of_module_set 𝔽 W s).E = s := 
begin
  rw [matroid_of_module_set, matroid_of_indep_of_bdd', matroid_of_indep_of_bdd, 
    matroid_of_indep, matroid_of_base, ← ground_eq_E],
end

-- to do : matroid_of_module_fun.base ↔ module.basis 
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

lemma matroid_of_module_fun.base (𝔽 W : Type*) {ι : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] 
  [finite_dimensional 𝔽 W] (v : ι → W) (ground : set ι) {B : set ι} 
  (hMB : (matroid_of_module_fun 𝔽 W v ground).base B) : 
    linear_independent 𝔽 (λ x : B, v x) ∧ span 𝔽 (v '' B) = span 𝔽 (v '' ground) :=
begin
  have hMBi := hMB.indep,
  rw [matroid_of_module_fun, matroid_of_indep_of_bdd', matroid_of_indep_of_bdd, 
    matroid_of_indep_apply] at hMBi,
  refine ⟨hMBi.1, _⟩,
  sorry,
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

lemma equiv_matroid_of_module_fun_iff_rep (𝔽 W : Type*) {ι : Type*} [field 𝔽] [add_comm_group W] 
  [module 𝔽 W] [finite_dimensional 𝔽 W] (v : ι → W) (ground : set ι) (M : matroid_in ι) 
  (ψ : ((matroid_of_module_fun 𝔽 W v ground) ≃i M)): 
  rep 𝔽 W M :=
begin
  sorry,
end

lemma matroid_of_module_fun_rep_eq (M : matroid_in α) (𝔽 W : Type*) [field 𝔽] [add_comm_group W] 
  [module 𝔽 W] [finite_dimensional 𝔽 W] (φ : rep 𝔽 W M) : 
  M = matroid_of_module_fun 𝔽 W φ M.E :=
begin
  apply eq_of_indep_iff_indep_forall _ (λ I hI, _),
  refl,
  have hsigh : (λ (x : ↥I), φ x) = (φ.to_fun ∘ coe),
  { ext, 
    simp only [comp_app],
    refl },
  rw [matroid_of_module_fun, matroid_of_indep_of_bdd'_apply, hsigh, φ.valid'], 
  refine ⟨λ h, ⟨h, hI⟩, λ h, h.1⟩, 
  apply hI,
end

namespace rep

variables


lemma valid (φ : rep 𝔽 W M) {I : set α} {hI : I ⊆ M.E}: linear_independent 𝔽 (λ e : I, φ e) ↔ 
  M.indep I := φ.valid' _ hI

lemma valid'' (φ : rep 𝔽 W M) {I : set α} (hI : I ⊆ M.E): linear_independent 𝔽 (λ e : I, φ e) ↔ 
  M.indep I := φ.valid' _ hI

protected lemma is_representable {W : Type} [add_comm_group W] [module 𝔽 W] (φ : rep 𝔽 W M) : 
  is_representable 𝔽 M := ⟨W, ⟨_, ⟨_, ⟨φ⟩⟩⟩⟩

lemma inj_on_of_indep (φ : rep 𝔽 W M) (hI : M.indep I) : inj_on φ I :=
inj_on_iff_injective.2 ((φ.valid' I hI.subset_ground).2 hI).injective

@[simp] lemma to_fun_eq_coe (φ : rep 𝔽 W M) : φ.to_fun = (φ : α → W)  := by { ext, refl }

lemma support' {φ : rep 𝔽 W M} {e : α} (he : e ∉ M.E) : φ e = 0 := 
by { rw ← to_fun_eq_coe, apply φ.support _ he }

lemma linear_independent_iff_coe (φ : rep 𝔽 W M) (hI : M.indep I) :
  linear_independent 𝔽 (λ e : I, φ e) ↔ linear_independent 𝔽 (coe : φ '' I → W) :=
linear_independent_image $ inj_on_of_indep _ hI

def to_submodule (φ : rep 𝔽 W M) : submodule 𝔽 W := span 𝔽 (range φ)

def to_submodule' (φ : rep 𝔽 W M) : submodule 𝔽 W := span 𝔽 (φ '' M.E)

lemma mem_to_submodule (φ : rep 𝔽 W M) (x : α) : φ x ∈ φ.to_submodule :=
by { rw [rep.to_submodule], refine subset_span _, rw mem_range, use x }

lemma mem_to_submodule' (φ : rep 𝔽 W M) (x : α) (hx : x ∈ M.E) : φ x ∈ φ.to_submodule' :=
by { rw [rep.to_submodule'], refine subset_span _, rw mem_image, use ⟨x, ⟨hx, rfl⟩⟩ }

def rep_submodule (φ : rep 𝔽 W M) : rep 𝔽 (φ.to_submodule') M := 
{ to_fun := λ a, if h : a ∈ M.E then ⟨φ a, φ.mem_to_submodule' a h⟩ else 0,
  valid' := λ I hI, 
    begin
       have h2 : ((λ (a : α), dite (a ∈ M.E) (λ (h : a ∈ M.E), 
        (⟨φ a, φ.mem_to_submodule' a h⟩ : φ.to_submodule')) (λ (h : a ∉ M.E), 0)) ∘
           coe : I → φ.to_submodule') = λ a : I, (⟨φ a, φ.mem_to_submodule' a (mem_of_subset_of_mem 
           hI (by { simp only [subtype.val_eq_coe, subtype.coe_prop]}))⟩ : φ.to_submodule'), 
        ext;
        simp only [comp_app],
        have h3 : ↑x ∈ I, 
          simp only [subtype.val_eq_coe, subtype.coe_prop],
        rw (@dite_eq_iff _ (↑x ∈ M.E) _ (⟨φ x, φ.mem_to_submodule' x (mem_of_subset_of_mem hI h3)⟩ : 
          φ.to_submodule') _ _).2 _,
        left,
        use (mem_of_subset_of_mem hI h3),
      rw h2,
      have h8 : (λ (x : ↥I), φ x) = 
        (λ (x : ↥I), ↑(⟨φ x, φ.mem_to_submodule' x 
        (mem_of_subset_of_mem hI (by { simp only [subtype.val_eq_coe, subtype.coe_prop]}))⟩ : 
          φ.to_submodule')),
      { simp only [subtype.coe_mk] },
      have h4 : linear_independent 𝔽 (λ (x : ↥I), (⟨φ x, φ.mem_to_submodule' x 
        (mem_of_subset_of_mem hI (by { simp only [subtype.val_eq_coe, subtype.coe_prop]}))⟩ : 
          φ.to_submodule')) = linear_independent 𝔽 (λ (a : I), φ a),
        simp_rw [h8, ← submodule.coe_subtype],
        rw linear_map.linear_independent_iff 
          (φ.to_submodule'.subtype) (ker_subtype φ.to_submodule'),
      rw h4,
      apply φ.valid' I hI,
    end,
    support := λ e he, 
    begin
      simp only [dite_eq_iff],
      right,
      use he,
    end } 

def rep.compose (φ : rep 𝔽 W M) (e : W ≃ₗ[𝔽] W') : rep 𝔽 W' M := 
{ to_fun := e ∘ φ.to_fun,
  valid' := λ I,
    begin
      rw comp.assoc,
      have h2 := linear_map.linear_independent_iff e.to_linear_map e.ker,
      simp only [linear_equiv.coe_to_linear_map] at h2,
      rw h2,
      apply φ.valid',
    end,
  support := λ x hx, by { rw [comp_app, φ.support x hx, _root_.map_zero] } }

def rep.compose' (φ : rep 𝔽 W M) (e : φ.to_submodule' ≃ₗ[𝔽] W') : rep 𝔽 W' M := 
  (rep.compose (φ.rep_submodule) e)

/-def iso.rep (M M' : matroid_in α) (ψ : M' ≃i M) (φ : rep 𝔽 W M) : rep 𝔽 W M' := 
{ to_fun := λ a, if h : a ∈ M'.E then φ (ψ ⟨a, h⟩) else φ a,
  valid' := λ I hI, 
    begin
      rw ψ.on_indep hI,
      have h2 : ((λ (a : α), dite (a ∈ M'.E) (λ (h : a ∈ M'.E), φ ↑(ψ ⟨a, h⟩)) 
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
        sorry,
      sorry,
    end,
  support := _ } -/

lemma ne_zero_of_nonloop (φ : rep 𝔽 W M) (hx : M.nonloop x) : φ x ≠ 0 :=
((φ.valid' {x} (indep_singleton.2 hx).subset_ground).2 hx.indep).ne_zero 
(⟨x, mem_singleton _⟩ : ({x} : set α))

lemma ne_zero_of_loopless (φ : rep 𝔽 W M) (hl : loopless M) (x : α) (hx : x ∈ M.E) : φ x ≠ 0 :=
φ.ne_zero_of_nonloop $ indep_singleton.1 (hl {x} (singleton_subset_iff.2 hx) (ncard_singleton x))

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

lemma of_base (φ : rep 𝔽 W M) {B : set α} (hB : M.base B) (e : α) (he : e ∈ M.E) : 
  φ e ∈ span 𝔽 (φ '' B) :=
of_basis φ (base.basis_ground hB) he

lemma span_basis (φ : rep 𝔽 W M) {X I : set α} (hI : M.basis I X) : 
  span 𝔽 (φ '' I) = span 𝔽 (φ '' X) :=
begin
  refine (span_mono $ image_subset _ (basis.subset hI)).antisymm (span_le.2 _),
  rintros _ ⟨y, ⟨hy1, rfl⟩⟩,
  apply of_basis φ hI hy1,
end

lemma span_base (φ : rep 𝔽 W M) (hB : M.base B) : span 𝔽 (φ '' B) = span 𝔽 (φ '' M.E) := 
  by { rw [span_basis φ (base.basis_ground hB)] }

/-lemma matroid_of_module_fun.base (𝔽 W : Type*) {ι : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] 
  [finite_dimensional 𝔽 W] (v : ι → W) (ground : set ι) {B : set ι} 
  (hMB : (matroid_of_module_fun 𝔽 W v ground).base B) : 
    linear_independent 𝔽 (λ x : B, v x) ∧ span 𝔽 (v '' B) = span 𝔽 (v '' ground) :=
begin
  have hMBi := hMB.indep,
  rw [matroid_of_module_fun, matroid_of_indep_of_bdd', matroid_of_indep_of_bdd, 
    matroid_of_indep_apply] at hMBi,
  refine ⟨hMBi.1, _⟩,
  have φ := rep_of_matroid_of_module_fun 𝔽 W v ground,
  have hφ := φ.span_base hMB,
  sorry,
end-/

lemma basis_of_base (φ : rep 𝔽 W M) {B : set α} (hB : M.base B) :
  _root_.basis B 𝔽 (span 𝔽 (φ '' M.E)) := by {
rw [←span_base _ hB, image_eq_range], exact basis.span ((φ.valid' B hB.subset_ground).2 hB.indep) }

instance fin_dim_rep (φ : rep 𝔽 W M) [M.finite_rk] [fintype 𝔽] : 
  finite_dimensional 𝔽 (span 𝔽 (φ '' M.E)) :=
begin
  cases M.exists_base with B hB,
  apply finite_dimensional.of_finite_basis (basis_of_base φ hB) (base.finite hB),
end

instance fin_dim_rep' (φ : rep 𝔽 W M) [M.finite_rk] [fintype 𝔽] : 
  finite_dimensional 𝔽 φ.to_submodule' :=
begin
  cases M.exists_base with B hB,
  apply finite_dimensional.of_finite_basis (basis_of_base φ hB) (base.finite hB),
end

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

lemma mem_span_cl (φ : rep 𝔽 W M) {x : α} {X : set α} (hX : X ⊆ M.E) (hx : x ∈ M.cl X) : 
  φ x ∈ span 𝔽 (φ '' X) :=
begin
  by_cases x ∈ X, 
  { apply mem_of_subset_of_mem (@subset_span 𝔽 _ _ _ _ (φ '' X)) (mem_image_of_mem φ h) },
  obtain ⟨I, hI⟩ := M.exists_basis X,
  rw [← span_basis φ hI, span_basis φ (indep.basis_cl (basis.indep hI)), basis.cl hI],
  apply mem_of_subset_of_mem (@subset_span 𝔽 _ _ _ _ (φ '' M.cl X)) (mem_image_of_mem φ hx),
end

/-def rep_of_del (N : matroid_in α) (φ : rep 𝔽 W N) (D : set α) : 
rep 𝔽 W (N ⟍ D) := 
{ to_fun := λ x, if x ∈ D then 0 else φ.to_fun x,
  valid' := λ I hI, by { rw delete_ground at hI, 
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
    end  }-/

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
  valid' := λ I hI,
    begin
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
      have h8 := linear_independent.image ((φ.valid' J hJ.subset_ground_left).2 (hJ.indep)),
      have h6 := linear_independent.union h7 h8 h30,
      rw [linear_independent_image, image_union],
      refine ⟨⟨_root_.disjoint.of_image (linear_independent.union' h7 h8 h30 h6), h6⟩, _⟩,
      apply @_root_.disjoint.of_image _ _ φ,
      simp only [to_fun_eq_coe] at h30,
      rw h10 at h30,
      simp only [← to_fun_eq_coe] at h30,
      sorry,
      rw inj_on_union (_root_.disjoint.of_image (linear_independent.union' h7 h8 h30 h6)),
      refine ⟨φ.inj_on_of_indep ((φ.valid' I _).1 
        (linear_independent.of_comp ((span 𝔽 (φ '' C)).mkq) h)), 
        ⟨φ.inj_on_of_indep (hJ.indep), λ x hx y hy, set.disjoint_iff_forall_ne.1 
        (linear_independent.union' h7 h8 h30 h6) (φ x) (mem_image_of_mem φ hx) 
        (φ y) (mem_image_of_mem φ hy)⟩⟩,
      /-simp_rw [← mkq_apply _],
      rw linear_map.linear_independent_iff,
      refine ⟨(φ.valid' I).2 (indep.subset h.1.2 (subset_union_left I J)), _⟩,
      rw ker_mkq (span 𝔽 (φ.to_fun '' C)),
      have h60 := linear_independent.image ((φ.valid' _).2 h.1.2),
      rw image_union at h60,
      rw [← image_univ, h21],
      simp_rw [to_fun_eq_coe],
      rw [← h10],
      simp only,
      apply linear_independent.union'',-/
      sorry,
      /-{ apply linear_independent.image 
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
      apply h60,-/
      sorry,
      sorry,
    end,
  support := sorry }

/-def rep_of_dual {𝔽 W : Type*} [is_R_or_C 𝔽] [normed_add_comm_group W] [inner_product_space 𝔽 W] 
  (M : matroid_in α) (φ : rep 𝔽 W M) : rep 𝔽 (φ.to_submodule)ᗮ M﹡ := 
{ to_fun := λ e, _,
  valid' := _,
  support := _ }-/

/-def is_rep_of_minor_of_is_rep (N : matroid_in α) (hNM : N ≤m M) (hM : M.is_representable 𝔽) : 
  N.is_representable 𝔽 := 
begin
  obtain ⟨W, ⟨_, ⟨_, ⟨φ⟩⟩⟩⟩ := hM,
  obtain ⟨C, ⟨D, ⟨hC, ⟨hD, ⟨hCD, rfl⟩⟩⟩⟩⟩ := minor.exists_contract_indep_delete_coindep hNM,
  refine ⟨_, ⟨_, ⟨_, ⟨rep_of_del (M ⟋ C) 
    (@rep_of_contr _ 𝔽 W _ hM_h_w hM_h_h_w _ M φ C hC.subset_ground) D⟩⟩⟩⟩,
end-/

theorem finrank_span_set_eq_ncard {K V : Type*} [division_ring K] [add_comm_group V] 
  [module K V] (s : set V) (hs : linear_independent K (coe : s → V)) :
finite_dimensional.finrank K (submodule.span K s) = s.ncard :=
begin
  by_cases s.finite,
  { haveI := (finite.fintype h),
    rw [finrank_span_set_eq_card s hs, to_finset_card, 
      ncard_eq_to_finset_card, finite.card_to_finset] },
  { rw infinite.ncard h,
    apply finrank_of_infinite_dimensional,
    by_contra h3,
    apply h,
    have h8 : span K (range (coe : s → V)) = span K s,
    simp only [subtype.range_coe_subtype, set_of_mem_eq],
    apply _root_.basis.finite_index_of_rank_lt_aleph_0 (basis.span hs),
    rw [← is_noetherian.iff_rank_lt_aleph_0, is_noetherian.iff_fg, h8],
    apply h3 },
end 


lemma of_r (φ : rep 𝔽 W M) (X : set α) (hX : X ⊆ M.E . ssE) : 
  finite_dimensional.finrank 𝔽 (span 𝔽 (φ '' X)) = M.r X :=
begin
  obtain ⟨I, hI⟩ := M.exists_basis X, 
  rw [←hI.card, ←φ.span_basis hI, finrank_span_set_eq_ncard, 
    ncard_image_of_inj_on (inj_on_of_indep _ hI.indep) ], 
  exact linear_independent.image ((φ.valid' I hI.subset_ground_left).mpr hI.indep), 
end

lemma of_rank (φ : rep 𝔽 W M) : finite_dimensional.finrank 𝔽 (span 𝔽 (φ '' M.E)) = M.rk :=
by { convert of_r φ M.E; simp }

lemma cl_subset_span_range (φ : rep 𝔽 W M) (X : set α) (hX : X ⊆ M.E . ssE) : 
  φ '' M.cl X ⊆ span 𝔽 (φ '' M.E) := by { rintros _ ⟨x, ⟨hx, rfl⟩⟩, 
  apply mem_span_rep φ x }

/-lemma cl_subset_span_set (φ : rep 𝔽 W M) {X : set α} (hX : X ⊆ M.E) : 
  φ '' M.cl X ⊆ span 𝔽 (φ '' X) :=
by { rintros _ ⟨x, ⟨hx, rfl⟩⟩, apply mem_span_cl φ hX hx, }-/

--lemma rep_of_minor (φ : rep 𝔽 W M) (N : matroid_in α) (hNM : N ≤ matroid_in.to_matroid_in M) : 

end rep

variables {ι : Type} [fintype α]

structure rep' (𝔽 : Type*) [field 𝔽] (M : matroid_in α) (ι : Type) :=
(to_fun : α → ι → 𝔽)
(valid' : ∀ (I ⊆ M.E), linear_independent 𝔽 (λ e : I, to_fun e) ↔ M.indep I)

namespace rep'

lemma valid (φ : rep' 𝔽 M ι) {I : set α} {hI : I ⊆ M.E} : linear_independent 𝔽 (λ e : I, φ.to_fun e) 
  ↔ M.indep I := φ.valid' _ hI

instance fun_like : fun_like (rep' 𝔽 M ι) α (λ _, ι → 𝔽) :=
{ coe := rep'.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

instance : has_coe_to_fun (rep' 𝔽 M ι) (λ _, α → ι → 𝔽) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe' (φ : rep' 𝔽 M ι) : φ.to_fun = (φ : α → ι → 𝔽)  := by { ext, refl }

lemma inj_on_of_indep' (φ : rep' 𝔽 M ι) (hI : M.indep I) : inj_on φ I :=
inj_on_iff_injective.2 ((φ.valid' I hI.subset_ground).2 hI).injective

/- def rep_of_rep' (φ : rep' 𝔽 M ι) : rep 𝔽 (ι → 𝔽) M := ⟨φ, λ I hI, φ.valid' I hI⟩    -/

noncomputable def rep'_of_rep [finite_dimensional 𝔽 W] (φ : rep 𝔽 W M) {n : ℕ} (h : finrank 𝔽 W = n) : 
  rep' 𝔽 M (fin n)  := 
{ to_fun := λ v, (linear_equiv.of_finrank_eq W (fin n → 𝔽) 
  (by simpa only [finrank_fin_fun]) :  W ≃ₗ[𝔽] (fin n → 𝔽)) (φ v), 
  valid' := λ I hI, 
  begin
    rw [←φ.valid' I hI, rep.to_fun_eq_coe], 
    exact (linear_equiv.of_finrank_eq _ _ (by simpa only [finrank_fin_fun]) : 
    W ≃ₗ[𝔽] (fin n → 𝔽)).to_linear_map.linear_independent_iff (linear_equiv.ker _), 
  end }

lemma of_basis' (φ : rep' 𝔽 M ι) {X I : set α} (hI : M.basis I X) {e : α} (he : e ∈ X): 
  φ e ∈ span 𝔽 (φ '' I) :=
begin
  by_cases e ∈ I, 
  { apply subset_span (mem_image_of_mem _ h) },
  have h2 : ¬ linear_independent 𝔽 (λ x : insert e I, φ x) := 
    (φ.valid' (insert e I) _).not.2 (dep_iff.1 (hI.insert_dep (mem_diff_of_mem he h))).1,
  contrapose! h2,
  apply (linear_independent_insert' h).2 ⟨(φ.valid' I hI.subset_ground_left).2 hI.indep, h2⟩,
  apply insert_subset.2 ⟨mem_of_subset_of_mem hI.subset_ground he, hI.subset_ground_left⟩,
end

lemma of_base' (φ : rep' 𝔽 M ι) {B : set α} (hB : M.base B) (e : α) (he : e ∈ M.E) : 
  φ e ∈ span 𝔽 (φ '' B) := of_basis' φ (base.basis_ground hB) he

lemma span_basis' (φ : rep' 𝔽 M ι) {X I : set α} (hI : M.basis I X) : 
  span 𝔽 (φ '' I) = span 𝔽 (φ '' X) :=
begin
  refine (span_mono $ image_subset _ (basis.subset hI)).antisymm (span_le.2 _),
  rintros _ ⟨y, ⟨hy1, rfl⟩⟩,
  apply of_basis' φ hI hy1,
end

lemma span_base' (φ : rep' 𝔽 M ι) (hB : M.base B) : span 𝔽 (φ '' B) = span 𝔽 (φ '' M.E) := 
  by { rw [span_basis' φ (base.basis_ground hB)] }

@[simp] lemma mem_span_rep' (φ : rep' 𝔽 M ι) : ∀ (x ∈ M.E), φ x ∈ (span 𝔽 (φ '' M.E)) := 
  λ x h, by { 
  apply mem_of_subset_of_mem (@subset_span 𝔽 _ _ _ _ (φ '' M.E)) (mem_image_of_mem φ h) }

@[simp] lemma mem_span_rep_range' (φ : rep' 𝔽 M ι) : ∀ (x : α), φ x ∈ (span 𝔽 (range ⇑φ)) := 
  λ x, by { apply mem_of_subset_of_mem (@subset_span 𝔽 _ _ _ _ (range ⇑φ)) (mem_range_self x) }

lemma basis_of_base' (φ : rep' 𝔽 M ι) {B : set α} (hB : M.base B) :
  _root_.basis B 𝔽 (span 𝔽 (φ '' M.E)) := by { rw [←span_base' _ hB, image_eq_range], 
  exact basis.span ((φ.valid' B hB.subset_ground).2 hB.indep) }

instance fin_dim_rep' (φ : rep' 𝔽 M ι) [fintype 𝔽] : 
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
  have h3 := finite_dimensional.fin_basis 𝔽 (span 𝔽 (φ '' M.E)),
  rw [←span_base' φ hB, finrank_span_set_eq_card (φ '' B)],
  have h6 : (⇑φ '' B).to_finset.card = B.to_finset.card,
  { simp_rw to_finset_card,
    rw ← card_image_of_inj_on (inj_on_of_indep' φ (base.indep hB)) },
  rw h6,
  simp only [← base.card hB, ncard_def, to_finset_card, nat.card_eq_fintype_card],
  have h8 : linear_independent 𝔽 (λ (x : B), φ (x : α)),
  rw [← to_fun_eq_coe', rep'.valid' φ _ hB.subset_ground],
  apply hB.indep,
  apply linear_independent.image_of_comp B φ coe h8,
end

end rep'

namespace rep

-- make version of std_rep that uses is_representable instead of explicit φ
-- to avoid using casesI a lot
/-- The representation for `M` whose rows are indexed by a base `B` -/
def std_rep (φ' : rep 𝔽 W M) {B : set α} (hB : M.base B) : 
  rep 𝔽 (B →₀ 𝔽) M := 
{ to_fun := λ e : α, ((valid'' φ' hB.subset_ground).2 hB.indep).repr ⟨φ' e, by
    { have h4 := φ'.mem_span_rep_range, rw ← span_range_base φ' hB at h4, exact h4 e}⟩,
  valid' := by 
  { intros I hI,
    rw [← @valid _ _ _ _ _ _ _ φ' _ hI, 
      linear_map.linear_independent_iff ((valid'' φ' hB.subset_ground).2 hB.indep).repr, 
      ←(submodule.subtype (span 𝔽 (range (λ (e : B), φ' ↑e)))).linear_independent_iff, 
         submodule.coe_subtype, and_iff_left],
    { refl }, 
    { simp only [linear_independent.repr_ker, disjoint_bot_left] },
    simp only [ker_subtype] },
  support := by
  { intros e he, simp_rw [support' he], convert _root_.map_zero _} }

def foo (φ' : rep 𝔽 W M) [M.finite_rk] :
  rep' 𝔽 M (fin M.rk)  := 
begin
  have h2 := M.exists_base,
  -- why isn't this working???
  /-obtain ⟨B, hB⟩ := M.exists_base,
  obtain φ := std_rep φ',
  use φ,
  rw [← (of_rank φ'), to_submodule'],-/
  sorry,
end

/-lemma foo' (φ : rep 𝔽 W M) [fintype 𝔽] [finite_dimensional 𝔽 W] :
  nonempty (rep 𝔽 (fin M.rk → 𝔽) M) :=
begin
  have φ := foo φ,
  use rep'.rep_of_rep' φ,
end-/

@[simp]
lemma id_matrix_of_base (φ : rep 𝔽 W M) {B : set α} (e : B) (hB : M.base B) : 
  std_rep φ hB e e = 1 :=
begin
  rw ← to_fun_eq_coe,
  simp [std_rep],
  rw [((valid'' φ hB.subset_ground).2 hB.indep).repr_eq_single e ⟨φ e, by
    { have h4 := φ.mem_span_rep_range, rw ← span_range_base φ hB at h4, exact h4 e}⟩ rfl],
  simp only [finsupp.single_eq_same],
end 

lemma id_matrix_of_base' (φ : rep 𝔽 W M) {B : set α} (e f : B) (hB : M.base B) (hne : e ≠ f) : 
  std_rep φ hB e f = 0 :=
begin
  rw ← to_fun_eq_coe,
  simp [std_rep],
  rw [((valid'' φ hB.subset_ground).2 hB.indep).repr_eq_single e ⟨φ e, by
    { have h4 := φ.mem_span_rep_range, rw ← span_range_base φ hB at h4, exact h4 e}⟩ rfl],
  apply finsupp.single_eq_of_ne hne,
end

lemma std_rep_base_eq {M' : matroid_in α} (φ : rep 𝔽 W M) (φ' : rep 𝔽 W' M') {B : set α} (hB : M.base B)
(hB' : M'.base B) (e : B) : std_rep φ hB e = std_rep φ' hB' e :=
begin
  ext;
  by_cases e = a, 
  simp_rw [h, id_matrix_of_base],
  simp_rw [id_matrix_of_base' φ e a hB h, id_matrix_of_base' φ' e a hB' h],
end

open_locale big_operators

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

--lemma mem_span_of_mem_cl 
-- we need he2 because we are deleting {e} from the funamental circuit for this
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

lemma mem_span_set_rep (φ : rep 𝔽 W M) {I : set α} (hI : M.indep I) (e : α) (he : e ∈ M.cl I) :
 ∃ c : W →₀ 𝔽, (c.support : set W) = φ '' (M.fund_circuit e I ∩ I) ∧ 
  c.sum (λ mi r, r • mi) = φ e :=
begin
  by_cases e ∈ I,
  rw [hI.fund_circuit_eq_of_mem h, singleton_inter_eq_of_mem h],
  simp only [image_singleton, finset.coe_eq_singleton],
  use finsupp.single (φ e) (1 : 𝔽),
  simp only [finsupp.sum_single_index, smul_eq_zero, eq_self_iff_true, true_or, one_smul, and_true],
  apply finsupp.support_single_ne_zero,
  simp only [ne.def, one_ne_zero, not_false_iff],
  rw fund_circuit_inter_eq_diff_of_not_mem _ he h,
  apply mem_span_set_rep_of_not_mem φ hI e he h,
end

-- use finsum instead of finset.sum
lemma mem_sum_basis_zmod2_of_not_mem [module (zmod 2) W] (φ : rep (zmod 2) W M) {I : set α} (hI : M.indep I) 
(e : α) (he : e ∈ M.cl I) (heI : e ∉ I) :
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

lemma mem_sum_basis_zmod2 [module (zmod 2) W] (φ : rep (zmod 2) W M) {I : set α} (hI : M.indep I) 
(e : α) (he : e ∈ M.cl I) :
  φ e = ∑ i in (M.fund_circuit e I ∩ I).to_finset, φ i :=
begin
  by_cases e ∈ I,
  rw [hI.fund_circuit_eq_of_mem h, @to_finset_congr _ ({e}∩I) {e} _ _ (singleton_inter_eq_of_mem h),
     to_finset_singleton, finset.sum_singleton],
  rw to_finset_congr (fund_circuit_inter_eq_diff_of_not_mem _ he h),
  apply eq.symm (mem_sum_basis_zmod2_of_not_mem φ hI e he h),
end

lemma circuit_sum_zero [module (zmod 2) W] (φ : rep (zmod 2) W M) {C : set α} (hI : M.circuit C) :
  ∑ i in C.to_finset, φ i = 0 :=
begin
  obtain ⟨e, he⟩ := hI.nonempty,
  sorry,
end

/-lemma circuit_sum [module (zmod 2) W] (φ : rep (zmod 2) W M) {C X : set α} (hI : M.circuit C) 
  (hXC : X ⊆ C) : ∑ i in X.to_finset, φ i = ∑ i in (C \ X).to_finset, φ i :=
begin
  sorry,
end-/
 
/- A matroid_in is binary if it has a `GF(2)`-representation -/
@[reducible, inline] def matroid_in.is_binary (M : matroid_in α) := M.is_representable (zmod 2)

-- change to is_binary instead of having reps
lemma eq_of_forall_fund_circuit_eq {M M' : matroid_in α} [module (zmod 2) W] [module (zmod 2) W'] 
(φM : rep (zmod 2) W M) (φM' : rep (zmod 2) W' M')
(hE : M.E = M'.E) (hB : M.base B) (hB' : M'.base B) 
(he : ∀ e ∈ M.E, M.fund_circuit e B = M'.fund_circuit e B) :
  M = M' :=
begin
  have φM := std_rep φM hB,
  have φM' := std_rep φM' hB',
  apply eq_of_indep_iff_indep_forall hE,
  intros I hI,
  have hI' := hI,
  rw hE at hI',
  rw [← (std_rep φM hB).valid' _ hI, ← (std_rep φM' hB').valid' _ hI'],
  have h2 : (std_rep φM hB).to_fun ∘ coe = λ i : I, (std_rep φM hB).to_fun i,
    simp only [eq_self_iff_true], 
  have h3 : (std_rep φM' hB').to_fun ∘ coe = λ i : I, (std_rep φM' hB').to_fun i,
    simp only [eq_self_iff_true],
  rw [h2, h3],
  simp only [to_fun_eq_coe],
  simp_rw [λ (e : I), (std_rep φM hB).mem_sum_basis_zmod2 hB.indep _ (@base.mem_cl _ M B hB e (hI e.2)),
    λ (e : I), (std_rep φM' hB').mem_sum_basis_zmod2 hB'.indep _ (@base.mem_cl _ M' B hB' e (hI' e.2))],
  simp_rw λ (e : I), he e (hI e.2),
  have h6 : (λ (i : ↥I), ∑ (x : α) in (M'.fund_circuit ↑i B ∩ B).to_finset, (std_rep φM hB) x) 
    = (λ (i : ↥I), ∑ (x : α) in (M'.fund_circuit ↑i B ∩ B).to_finset, (std_rep φM' hB') x),
    simp only,
    have h10 :=  λ (i : ↥I), @finset.sum_congr _ _ (M'.fund_circuit i B ∩ B).to_finset 
      (M'.fund_circuit i B ∩ B).to_finset (std_rep φM hB) (std_rep φM' hB') _ rfl _,
    simp_rw  [λ (i : I), h10 i],
    intros x hx,
    rw mem_to_finset at hx,
    have h12 := std_rep_base_eq φM φM' hB hB' ⟨x, (mem_of_mem_inter_right hx)⟩,
    simp at h12,
    rw h12,
  simp_rw h6,
end 

def rep_cocircuit_singleton (x : α) (B : set α) (φ : rep 𝔽 W (M ⟍ x)) 
(φx : rep 𝔽 W' (M ‖ ({x} : set α))) (hx : M.cocircuit {x}) (hB : (M ⟍ x).base B) : 
  rep 𝔽 (W × W') M := 
{ to_fun := λ (e : α), 
    if e ∈ ({x} : set α)
    then 
        linear_map.inr 𝔽 W W' (φx e)
    else 
      linear_map.inl 𝔽 W W' (φ e),
  valid' := λ I hI, 
    begin
      by_cases x ∈ I,
      { rw [← union_diff_cancel (singleton_subset_iff.2 h), union_comm],
        simp only [← ite_apply _ (linear_map.inr 𝔽 W W' ∘ φx) (linear_map.inl 𝔽 W W' ∘ φ)],
        refine ⟨λ h2, _, λ h2, _⟩,
        { have h11 := linear_independent.image h2,
          rw image_union at h11,
          have hM : M.indep (I \ {x} : set α),
            { have h10 := linear_independent.mono (subset_union_left _ _) h11,
                rw ← linear_independent_image at h10,
                have h12 : ∀ e : ((I \ {x}) : set α), (ite ((e : α) ∈ ({x} : set α)) 
                  ((linear_map.inr 𝔽 W W') ∘ φx) ((linear_map.inl 𝔽 W W') ∘ φ) e 
                  = ((linear_map.inl 𝔽 W W') ∘ φ) e),
                { intros e,
                  rw [ite_apply, ite_eq_iff],
                  right,
                  refine ⟨not_mem_of_mem_diff e.2, rfl⟩ },
              simp_rw [λ (e : (I \ {x} : set α)), h12 e,  
                @_root_.linear_map.linear_independent_iff _ _ _ _ _ _ _ _ _ _ (linear_map.inl 𝔽 W W') 
                  (linear_map.ker_eq_bot_of_injective linear_map.inl_injective)] at h10,
              rw φ.valid at h10, 
              apply h10.of_delete,
              rw [delete_elem, delete_ground],
              apply diff_subset_diff hI (subset.refl _),
              { intros a ha b hb hab,
                have h13 := h2.injective,
                rw [← restrict_eq, ← inj_on_iff_injective] at h13,
                apply h13 (mem_union_left {x} ha) (mem_union_left {x} hb) hab } },
            obtain ⟨B2, hB2⟩ := hM, 
            simp only [cocircuit_iff_mem_minimals, mem_minimals_iff', mem_set_of_eq, 
              singleton_inter_nonempty] at hx,
            refine ⟨B2, ⟨hB2.1, union_subset hB2.2 (singleton_subset_iff.2 (hx.1 B2 hB2.1))⟩⟩ },  
        { rw [linear_independent_image, image_union],
          have h12 : (λ (e : α), ite (e ∈ ({x} : set α)) ((linear_map.inr 𝔽 W W') ∘ φx) 
            ((linear_map.inl 𝔽 W W') ∘ φ) e) '' (I \ {x}) = 
            (linear_map.inl 𝔽 W W') '' (φ '' (I \ {x})),
            { simp_rw ite_apply,
              ext;
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
          have h13 : (λ (e : α), ite (e ∈ ({x} : set α)) ((linear_map.inr 𝔽 W W') ∘ φx) 
            ((linear_map.inl 𝔽 W W') ∘ φ) e) '' {x} = 
            (linear_map.inr 𝔽 W W') '' (φx '' {x}),
            { simp_rw [ite_apply, image_singleton, singleton_eq_singleton_iff, ite_eq_iff],
              left,
              refine ⟨mem_singleton _, rfl⟩ },
          rw [h12, h13],
          apply linear_independent.inl_union_inr,
          { have h6 := (h2.subset (subset_union_left _ _)).indep_delete_of_disjoint 
              (disjoint_sdiff_left),
            rw [← delete_elem, ← φ.valid] at h6,
            apply h6.image,
            rw [delete_elem, delete_ground],
            apply diff_subset_diff hI (subset_refl _) },
          { apply linear_independent.image,
            rw [φx.valid, restrict_indep_iff],
            refine ⟨h2.subset (subset_union_right _ _), subset_refl _⟩,
            rw restrict_ground_eq },
          simp_rw ite_apply,
          rw inj_on_union (disjoint_sdiff_left),
          refine ⟨_, ⟨inj_on_singleton _ _, _⟩⟩,
          { intros a ha b hb hab,
            simp only [if_neg (not_mem_of_mem_diff ha), if_neg (not_mem_of_mem_diff hb)] at hab,
            have hab2 := linear_map.inl_injective hab,
            have h4 := (h2.subset (subset_union_left _ _)).indep_delete_of_disjoint 
              (disjoint_sdiff_left),
            apply (inj_on_of_indep φ h4) ha hb (linear_map.inl_injective hab) },
          intros a ha b hb,
          simp only [if_pos hb, if_neg (not_mem_of_mem_diff ha)],
          simp only [linear_map.coe_inl, linear_map.coe_inr, ne.def, prod.mk.inj_iff, not_and],
          intros hc,
          by_contra,
          have h6 := (h2.subset (subset_union_left _ _)).indep_delete_of_disjoint 
              (disjoint_sdiff_left),
          rw [← delete_elem] at h6,
          apply φ.ne_zero_of_nonloop (h6.nonloop_of_mem ha),
          rw hc } },
      { -- this is infuriating
        have h8 : ((λ (e : α), ite (e ∈ ({x} : set α)) ((linear_map.inr 𝔽 W W') (φx e)) 
          ((linear_map.inl 𝔽 W W') (φ e))) ∘ coe) = 
          (λ (e : I), ite ((e : α) ∈ ({x} : set α)) ((linear_map.inr 𝔽 W W') (φx e)) 
          ((linear_map.inl 𝔽 W W') (φ e))),
          simp only [eq_self_iff_true],
        rw h8,
        have h3 : ∀ (e : I), (ite ((e : α) ∈ ({x} : set α)) ((linear_map.inr 𝔽 W W') (φx e)) 
          ((linear_map.inl 𝔽 W W') (φ e))) = 
              ((linear_map.inl 𝔽 W W') ∘ φ) e,
        { intros,
          simp_rw [ite_eq_iff],
          right,
          refine ⟨mem_singleton_iff.1.mt (ne_of_mem_of_not_mem e.2 h), rfl⟩ },
        simp_rw [λ (e : I), h3 e],
        rw [@_root_.linear_map.linear_independent_iff _ _ _ _ _ _ _ _ _ _ 
          (linear_map.inl 𝔽 W W') 
          (linear_map.ker_eq_bot_of_injective linear_map.inl_injective), φ.valid, delete_elem],
        refine ⟨λ h2, h2.of_delete, 
          λ h2, h2.indep_delete_of_disjoint (disjoint_singleton_right.2 h)⟩,
        rw [delete_elem, delete_ground],
        apply subset_diff_singleton hI h },
    end,
  support := λ e he, 
    begin
      by_cases e ∈ {x},
      { by_contra h2,
        apply he,
        rw mem_singleton_iff.1 h,
        apply hx.subset_ground,
        simp only [mem_singleton] },
      { have he2 := not_mem_subset (diff_subset M.E {x}) he,
        rw [← delete_ground, ← delete_elem] at he2,
        rw ite_eq_iff,
        right,
        refine ⟨h, _⟩,
        simp only [linear_map.coe_inl, prod.mk_eq_zero, eq_self_iff_true, 
          and_true],
        apply φ.support e he2 },
    end  } 

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
  base_exchange' := _,
  maximality := _,
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

lemma add_coloop_ground (M : matroid_in α) {f : α} (hf : f ∉ M.E) : 
  (add_coloop M hf).E = M.E ∪ {f} := by refl

def add_coloop_rep (φ : rep 𝔽 W M) {f : α} (hf : f ∉ M.E) : 
  rep 𝔽 (W × 𝔽) (add_coloop M hf) := 
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
              rw [diff_subset_iff, union_comm],
              apply hI,
              { intros a ha b hb hab,
                have h13 := h2.injective,
                rw [← restrict_eq, ← inj_on_iff_injective] at h13,
                apply h13 (mem_union_left {f} ha) (mem_union_left {f} hb) hab } },
            obtain ⟨B2, hB2⟩ := hM, 
            refine ⟨B2 ∪ {f}, ⟨⟨_, mem_union_right _ (mem_singleton f)⟩, 
              union_subset_union hB2.2 (subset_refl _)⟩⟩,
            simp only [union_singleton, insert_diff_of_mem, mem_singleton],
            rw diff_singleton_eq_self (not_mem_subset hB2.1.subset_ground hf),
            apply hB2.1 },  
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
            rw [← delete_elem, ← add_coloop_del_equal, ← φ.valid] at h6,
            apply h6.image,
            apply h6.subset_ground },
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
            rw [← delete_elem, ← add_coloop_del_equal] at h4,
            apply (inj_on_of_indep φ h4) ha hb (linear_map.inl_injective hab) },
          intros a ha b hb,
          simp only [if_pos hb, if_neg (not_mem_of_mem_diff ha)],
          simp only [linear_map.coe_inl, linear_map.coe_inr, ne.def, prod.mk.inj_iff, not_and],
          intros hc,
          by_contra,
          have h6 := (h2.subset (subset_union_left _ _)).indep_delete_of_disjoint 
              (disjoint_sdiff_left),
          rw [← delete_elem, ← add_coloop_del_equal] at h6,
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
        { obtain ⟨B, hB⟩ := h2,
          refine ⟨(B ∪ {f} : set α), ⟨⟨_, _⟩, _⟩⟩,
          rw union_diff_cancel_right,
          apply hB.1,
          rw inter_comm,
          rw subset_empty_iff,
          apply singleton_inter_eq_empty.2,
          apply not_mem_subset hB.1.subset_ground hf,
          apply mem_union_right _ (mem_singleton _), 
          apply subset_union_of_subset_left hB.2 },
        { obtain ⟨B, ⟨⟨hB1, hB2⟩, hB3⟩⟩ := h2,
          refine ⟨(B \ {f} : set α), ⟨hB1, subset_diff_singleton hB3 h⟩⟩ },
        rw ← union_diff_cancel_right (subset_empty_iff.2 (inter_singleton_eq_empty.2 hf)),
        apply subset_diff_singleton hI h },
    end,
  support := λ e he, 
    begin
      by_cases e ∈ {f},
      { by_contra h2,
        apply he,
        rw mem_singleton_iff.1 h,
        rw ← singleton_subset_iff,
        apply subset_union_right },
      { have he2 := not_mem_subset (subset_union_left _ _) he,
        rw ite_eq_iff,
        right,
        refine ⟨h, _⟩,
        simp only [linear_map.coe_inl, prod.mk_eq_zero, eq_self_iff_true, 
          and_true],
        apply φ.support e he2 },
    end }

-- i think we need e to be a cocircuit of M
def series_extend (M : matroid_in α) {e f : α} (he : e ∈ M.E) 
  (hf : f ∉ M.E) : matroid_in α := 
{ ground := insert f M.E,
  -- M.base B covers e ∈ B
  base := sorry,
  exists_base' := _,
  base_exchange' := _,
  maximality := _,
  subset_ground' := _ }

-- don't need hf but keeping for convenience
lemma series_extend_eq (M M' : matroid_in α) {e f : α} (hM' : M'.cocircuit {e, f}) (he : e ∈ M.E) 
  (h : M = M' ⟋ f) (hf : f ∉ M.E) : M' = series_extend M he hf := sorry

-- e can't be coloop
lemma series_extend_cocircuit (M : matroid_in α) {e f : α} (he : e ∈ M.E) (hMe : ¬ M.coloop e)
  (hf : f ∉ M.E) : (series_extend M he hf).cocircuit {e, f} := sorry

lemma series_extend_contr_eq (M : matroid_in α) {e f : α} (he : e ∈ M.E) (hf : f ∉ M.E) : 
    M = (series_extend M he hf) ⟋ f := sorry

-- switch e ∈ {x} out for e = x
def series_extend_rep (φ : rep 𝔽 W M) {x y : α} (hx : x ∈ M.E)
  (hy : y ∉ M.E) : rep 𝔽 (W × 𝔽) (series_extend M hx hy) := 
{ to_fun := λ (e : α), 
    if e ∈ ({x} : set α)
    then 
      (linear_map.inl 𝔽 W 𝔽 ∘ φ + linear_map.inr 𝔽 W 𝔽 ∘ (λ e : α, 1)) e
    else 
      if e ∈ ({y} : set α) then linear_map.inr 𝔽 W 𝔽 1 else (linear_map.inl 𝔽 W 𝔽 ∘ φ) e,
  valid' := λ I hI, 
    begin
    /-have h6 : ((λ (e : α), ite (e ∈ ({x} : set α)) ((linear_map.inl 𝔽 W 𝔽 ∘ φ + 
      linear_map.inr 𝔽 W 𝔽 ∘ (λ e : α, 1)) e) (ite (e ∈ ({y} : set α)) ((linear_map.inr 𝔽 W 𝔽) 1) 
          ((linear_map.inl 𝔽 W 𝔽 ∘ φ) e))) ∘ coe) = 
          (λ (e : I), ite ((e : α) ∈ ({x} : set α)) 
          ((linear_map.inl 𝔽 W 𝔽 ∘ φ + linear_map.inr 𝔽 W 𝔽 ∘ (λ e : α, 1)) e) 
          (ite ((e : α) ∈ ({y} : set α)) ((linear_map.inr 𝔽 W 𝔽) 1) ((linear_map.inl 𝔽 W 𝔽 ∘ φ) e))),
            --simp only [eq_self_iff_true],
            sorry,
    rw h6,-/
    by_cases hyI : y ∈ I,
      { 
        --rw ← [linear_map.add_apply],
        --rw linear_map.add_comp,
         -- ← ite_apply ((linear_map.inl 𝔽 W 𝔽) ∘ φ + (linear_map.inr 𝔽 W 𝔽) 1) _ ],
        by_cases hxI : x ∈ I,
        simp only [← ite_apply _ (linear_map.inr 𝔽 W 𝔽 ∘ (λ e : α, 1)) (linear_map.inl 𝔽 W 𝔽 ∘ φ)],
        simp only [← ite_apply _ _ _],
        { -- maybe by_cases M.indep I \ {x, y}?
          by_cases (series_extend M hx hy).indep (I \ {x, y} : set α),
          { have h2 : (series_extend M hx hy).indep (I \ {y} : set α),
              -- comes from x ∈ cocircuit
              sorry,
            rw ← not_iff_not,
            sorry },
          -- this gives us that M.indep (I \ {y}) 
          have hxyI : {x, y} ⊆ I,
            sorry,
          rw [← union_diff_cancel hxyI, union_comm],
          rw ← not_iff_not,
          refine ⟨λ h2, _, λ h2, _⟩,
          sorry, 
          sorry },
        { rw [← union_diff_cancel (singleton_subset_iff.2 hyI), union_comm],
          --simp only [← ite_apply _ (linear_map.inr 𝔽 W 𝔽 ∘ (λ e : α, 1)) (linear_map.inl 𝔽 W 𝔽 ∘ φ)],
          --simp only [← ite_apply _ _ _],
          refine ⟨λ h2, _, λ h2, _⟩,
          have h11 := linear_independent.image h2,  
          rw image_union at h11,
          have hM : M.indep (I \ {y} : set α),
            { have h10 := linear_independent.mono (subset_union_left _ _) h11,
                rw ← linear_independent_image at h10,
                have h12 : ∀ e : ((I \ {y}) : set α), ite ((e : α) ∈ ({x} : set α)) 
                  (((linear_map.inl 𝔽 W 𝔽) ∘ φ + (linear_map.inr 𝔽 W 𝔽) ∘ λ (e : α), 1) e) 
                  (ite ((e : α) ∈ ({y} : set α)) ((linear_map.inr 𝔽 W 𝔽) 1) 
                  (((linear_map.inl 𝔽 W 𝔽) ∘ φ) e)) 
                  = ((linear_map.inl 𝔽 W 𝔽) ∘ φ) e,
                { intros e,
                  rw ite_eq_iff,
                  right,
                  refine ⟨mem_singleton_iff.1.mt (ne_of_mem_of_not_mem e.2 (not_mem_subset 
                      (diff_subset I {y}) hxI)), _⟩,
                  rw ite_eq_iff,
                  right,
                  refine ⟨not_mem_of_mem_diff e.2, rfl⟩, },
              simp_rw [λ (e : (I \ {y} : set α)), h12 e, 
                @_root_.linear_map.linear_independent_iff _ _ _ _ _ _ _ _ _ _ (linear_map.inl 𝔽 W 𝔽) 
                (linear_map.ker_eq_bot_of_injective linear_map.inl_injective)] at h10,
              rw φ.valid at h10, 
              apply h10,
              rw [diff_subset_iff, union_comm],
              apply hI,
              { intros a ha b hb hab,
                have h13 := h2.injective,
                rw [← restrict_eq, ← inj_on_iff_injective] at h13,
                apply h13 (mem_union_left {y} ha) (mem_union_left {y} hb) hab } },
          rw [union_comm, indep.union_indep_iff_contract_indep],
          simp only [diff_singleton_eq_self, not_mem_diff_singleton, not_false_iff],
          rw [← contract_elem, ← series_extend_contr_eq M hx hy], 
          apply hM,
          have h5 : y ∈ ({x, y} : set α),
            simp only [mem_insert_iff, mem_singleton, or_true],
          apply ((series_extend_cocircuit M hx hy).nonloop_of_mem h5).indep,
          { rw [linear_independent_image, image_union],
            have h7 : (λ (e : α), ite (e ∈ ({x} : set α)) (((linear_map.inl 𝔽 W 𝔽) ∘ φ + 
              (linear_map.inr 𝔽 W 𝔽) ∘ λ (e : α), 1) e) (ite (e ∈ ({y} : set α)) 
              ((linear_map.inr 𝔽 W 𝔽) 1) (((linear_map.inl 𝔽 W 𝔽) ∘ φ) e))) '' (I \ {y}) = 
              (linear_map.inl 𝔽 W 𝔽) '' (φ '' (I \ {y})),
            sorry,
            have h8 : (λ (e : α), ite (e ∈ ({x} : set α)) (((linear_map.inl 𝔽 W 𝔽) ∘ φ + 
              (linear_map.inr 𝔽 W 𝔽) ∘ λ (e : α), 1) e) (ite (e ∈ ({y} : set α)) 
              ((linear_map.inr 𝔽 W 𝔽) 1) (((linear_map.inl 𝔽 W 𝔽) ∘ φ) e))) '' {y} = 
              (linear_map.inr 𝔽 W 𝔽) '' (1 '' {y}),
              sorry,
            rw [h7, h8],
            apply linear_independent.inl_union_inr,
            apply linear_independent.image,
            rw φ.valid, 
            --rw union_comm at h2,
            have h3 := h2.subset(subset_union_right _ _),
            rw union_comm at h2,
            rw indep.union_indep_iff_contract_indep h3 at h2,
            simp only [diff_singleton_eq_self, not_mem_diff_singleton, not_false_iff] at h2,
            simp_rw ← contract_elem at h2,
            rw ← series_extend_contr_eq at h2,
            apply h2,
            sorry,
            rw image_singleton,
            apply linear_independent_singleton,
            simp only [pi.one_apply, ne.def, one_ne_zero, not_false_iff],
            sorry, } } },
      { by_cases hxI : x ∈ I,
        { rw [← union_diff_cancel (singleton_subset_iff.2 hxI), union_comm],
          rw union_singleton,
          rw linear_independent_insert',
          --rw [linear_independent_image, image_union],
          have h7 : (λ (e : α), ite (e ∈ ({x} : set α)) (((linear_map.inl 𝔽 W 𝔽) ∘ φ + 
            (linear_map.inr 𝔽 W 𝔽) ∘ λ (e : α), 1) e) (ite (e ∈ ({y} : set α)) 
            ((linear_map.inr 𝔽 W 𝔽) 1) (((linear_map.inl 𝔽 W 𝔽) ∘ φ) e))) '' (I \ {x}) = 
            (linear_map.inl 𝔽 W 𝔽) '' (φ '' (I \ {x})),
            sorry,
          have h8 : (λ (e : α), ite (e ∈ ({x} : set α)) (((linear_map.inl 𝔽 W 𝔽) ∘ φ + 
            (linear_map.inr 𝔽 W 𝔽) ∘ λ (e : α), 1) e) (ite (e ∈ ({y} : set α)) 
            ((linear_map.inr 𝔽 W 𝔽) 1) (((linear_map.inl 𝔽 W 𝔽) ∘ φ) e))) '' {x} = 
            (((linear_map.inl 𝔽 W 𝔽) ∘ φ + 
            (linear_map.inr 𝔽 W 𝔽) ∘ λ (e : α), 1)) '' {x},
            sorry,
          have h9 : ∀ (x_1 : (I \ {x})), ite ((x_1 : α) ∈ ({x} : set α)) 
            (((linear_map.inl 𝔽 W 𝔽) ∘ φ + (linear_map.inr 𝔽 W 𝔽) ∘ λ (e : α), 1) x_1) 
            (ite ((x_1 : α) ∈ ({y} : set α)) ((linear_map.inr 𝔽 W 𝔽) 1) (((linear_map.inl 𝔽 W 𝔽) ∘ φ) x_1))
            = (((linear_map.inl 𝔽 W 𝔽) ∘ φ) x_1),
            sorry,
          have h10 : ite (x ∈ ({x} : set α)) 
            (((linear_map.inl 𝔽 W 𝔽) ∘ φ + (linear_map.inr 𝔽 W 𝔽) ∘ λ (e : α), 1) x) 
            (ite (x ∈ ({y} : set α)) ((linear_map.inr 𝔽 W 𝔽) 1) (((linear_map.inl 𝔽 W 𝔽) ∘ φ) x)) =
            ((linear_map.inl 𝔽 W 𝔽) ∘ φ + (linear_map.inr 𝔽 W 𝔽) ∘ λ (e : α), 1) x,
            sorry,
          rw [h7, h10], --h8],
          simp_rw [λ (e : (I \ {x})), h9 e],
          { refine ⟨λ h2, _, λ h2, _⟩, 
            { rw indep.insert_indep_iff_of_not_mem',
              refine ⟨mem_union_left {y} hx, _⟩,
              have h5 : I \ {x} ⊆ ((series_extend M hx hy).E \ {x, y} : set α),
              { sorry
                /-rw [← diff_singleton_eq_self hyI, diff_diff, union_comm, 
                  union_singleton],
                apply diff_subset_diff_left hI-/ },
              apply not_mem_subset (cl_subset (series_extend M hx hy) h5),
              rw (series_extend_cocircuit M hx hy).compl_hyperplane.flat.cl,
              simp only [mem_diff, mem_insert_iff, eq_self_iff_true, true_or, 
                not_true, and_false, not_false_iff],
              rw [@_root_.linear_map.linear_independent_iff _ _ _ _ _ _ _ _ _ _ (linear_map.inl 𝔽 W 𝔽) 
                (linear_map.ker_eq_bot_of_injective linear_map.inl_injective), φ.valid] at h2,
              rw (eq_iff_indep_iff_indep_forall.1 (series_extend_contr_eq M hx hy)).2 (I \ {x}) at h2,
              rw contract_elem at h2,
              apply h2.1.of_contract,
              /-apply diff_subset (series_extend M hx hy).E {x, y},
              simp,
              apply mem_union_right M.E (mem_singleton _),-/
              /-have h5 : x ∈ ({x, y} : set α),
                sorry,-/
                --simp only [mem_insert_iff, mem_singleton, or_true],
              --apply ((series_extend_cocircuit M hx hy).nonloop_of_mem h5).indep,
              sorry,
              sorry,
              sorry },
            { have h3 := (h2.subset (subset_insert x (I \ {x}))).insert_indep_iff_of_not_mem' 
                (not_mem_diff_singleton x I),
              refine ⟨_, _⟩,
              rw [@_root_.linear_map.linear_independent_iff _ _ _ _ _ _ _ _ _ _ (linear_map.inl 𝔽 W 𝔽) 
                (linear_map.ker_eq_bot_of_injective linear_map.inl_injective), φ.valid],
              rw (eq_iff_indep_iff_indep_forall.1 (series_extend_contr_eq M hx hy)).2 (I \ {x}),
              rw contract_elem,
              have h5 := h2.subset (subset_insert x (I \ {x})),
              have h4 := (h2.subset (subset_insert x (I \ {x}))).insert_indep_iff_of_not_mem' 
                (not_mem_subset (diff_subset _ _) hyI),
              rw indep.contract_indep_iff,
              { refine ⟨disjoint_singleton_right.2 (not_mem_subset (diff_subset _ _) hyI), _⟩,
                rw union_singleton,
                rw (h2.subset (subset_insert x (I \ {x}))).insert_indep_iff_of_not_mem' 
                  (not_mem_subset (diff_subset _ _) hyI),
                refine ⟨mem_union_right M.E (mem_singleton _), _⟩,
                have h5 : I \ {x} ⊆ ((series_extend M hx hy).E \ {x, y} : set α),
                { sorry },
                apply not_mem_subset (cl_subset (series_extend M hx hy) h5),
                rw (series_extend_cocircuit M hx hy).compl_hyperplane.flat.cl,
                simp only [mem_diff, mem_insert_iff, mem_singleton, or_true, not_true, and_false, 
                  not_false_iff] },
              have h5 : y ∈ ({x, y} : set α),
                simp only [mem_insert_iff, mem_singleton, or_true],
              apply ((series_extend_cocircuit M hx hy).nonloop_of_mem h5).indep,
              sorry,
              sorry,
              rw ← image_comp,
              
              sorry } },
          sorry },
        { have h6 : ((λ (e : α), ite (e ∈ ({x} : set α)) ((linear_map.inl 𝔽 W 𝔽 ∘ φ + 
            linear_map.inr 𝔽 W 𝔽 ∘ (λ e : α, 1)) e) (ite (e ∈ ({y} : set α)) ((linear_map.inr 𝔽 W 𝔽) 1) 
                ((linear_map.inl 𝔽 W 𝔽 ∘ φ) e))) ∘ coe) = 
                (λ (e : I), ite ((e : α) ∈ ({x} : set α)) 
                ((linear_map.inl 𝔽 W 𝔽 ∘ φ + linear_map.inr 𝔽 W 𝔽 ∘ (λ e : α, 1)) e) 
                (ite ((e : α) ∈ ({y} : set α)) ((linear_map.inr 𝔽 W 𝔽) 1) ((linear_map.inl 𝔽 W 𝔽 ∘ φ) e))),
                  --simp only [eq_self_iff_true],
                  sorry,
          rw h6,
          have h7 : ∀ (e : I), ite ((e : α) ∈ ({x} : set α)) (((linear_map.inl 𝔽 W 𝔽) ∘ φ + 
            (linear_map.inr 𝔽 W 𝔽) ∘ λ (e : α), 1) (e : α)) (ite ((e : α) ∈ ({y} : set α)) 
            ((linear_map.inr 𝔽 W 𝔽) 1) (((linear_map.inl 𝔽 W 𝔽) ∘ φ) (e : α))) 
          = ((linear_map.inl 𝔽 W 𝔽) (φ e)),
          { intros e,
            rw ite_eq_iff,
            right,
            refine ⟨mem_singleton_iff.1.mt (ne_of_mem_of_not_mem e.2 hxI), _⟩,
            apply ite_eq_iff.2,
            apply or.intro_right,
            refine ⟨mem_singleton_iff.1.mt (ne_of_mem_of_not_mem e.2 hyI), rfl⟩ },
          simp_rw [λ (e : I), h7 e],
          rw [@_root_.linear_map.linear_independent_iff _ _ _ _ _ _ _ _ _ _ (linear_map.inl 𝔽 W 𝔽) 
            (linear_map.ker_eq_bot_of_injective linear_map.inl_injective), φ.valid],
          rw (eq_iff_indep_iff_indep_forall.1 (series_extend_contr_eq M hx hy)).2 I,
          rw contract_elem,
          rw indep.contract_indep_iff,
          refine ⟨λ h2, h2.2.subset (subset_union_left _ _), λ h2, 
            ⟨disjoint_singleton_right.2 hyI, _⟩⟩,
          simp,
          rw @indep.insert_indep_iff_of_not_mem _ _ _ _ h2 hyI _,
          --have h5 := (series_extend_cocircuit M hx hy).compl_hyperplane.flat.cl,
          have h3 := cocircuit_iff_mem_minimals_compl_nonspanning.1 (series_extend_cocircuit M hx hy),
          rw mem_minimals_prop_iff at h3,
          have h31 := h3.1,
          have h4 : ¬(series_extend M hx hy).spanning ((series_extend M hx hy).E \ ({x, y} : set α)),
            apply h31,
          rw not_spanning_iff_cl _ at h4,
          have h5 : I ⊆ ((series_extend M hx hy).E \ {x, y} : set α),
          { rw [← diff_singleton_eq_self hyI, ← diff_singleton_eq_self hxI, diff_diff, union_comm, 
              union_singleton],
            apply diff_subset_diff_left hI },
          apply not_mem_subset (cl_subset (series_extend M hx hy) h5),
          rw (series_extend_cocircuit M hx hy).compl_hyperplane.flat.cl,
          simp only [mem_diff, mem_insert_iff, mem_singleton, or_true, not_true, and_false, 
            not_false_iff],
          apply diff_subset (series_extend M hx hy).E {x, y},
          simp,
          apply mem_union_right M.E (mem_singleton _),
          have h5 : y ∈ ({x, y} : set α),
            simp only [mem_insert_iff, mem_singleton, or_true],
          apply ((series_extend_cocircuit M hx hy).nonloop_of_mem h5).indep,
          { rw [← diff_singleton_eq_self hyI, ← @union_diff_cancel_right _ M.E {y} 
              (subset_empty_iff.2 (inter_singleton_eq_empty.2 hy))],
            apply @diff_subset_diff_left _ _ _ {y} hI },
          { rw [← diff_singleton_eq_self hyI, ← @union_diff_cancel_right _ M.E {y} 
            (subset_empty_iff.2 (inter_singleton_eq_empty.2 hy))],
            apply @diff_subset_diff_left _ _ _ {y} hI } } },
      end,
  support := _ }

lemma rep_cocircuit_doubleton' (x y : α) (hxy : x ≠ y) [module 𝔽 W] 
  (φ : rep 𝔽 W (M ⟍ y)) (hx : M.cocircuit {x, y}) : 
  rep 𝔽 (W × 𝔽) M := 
{ to_fun := λ (e : α), 
    if e ∈ ({x} : set α)
    then 
      linear_map.inl 𝔽 W 𝔽 (φ e) + linear_map.inr 𝔽 W 𝔽 1
    else 
      if e ∈ ({y} : set α) then linear_map.inr 𝔽 W 𝔽 1 else linear_map.inl 𝔽 W 𝔽 (φ e),
  valid' := λ I hI, 
    begin
      by_cases hyI : y ∈ I,
      { by_cases hxI : x ∈ I,
        { 
          sorry },
        { sorry } },
      { by_cases hxI : x ∈ I,
        { 
          sorry },
        { have h6 : ((λ (e : α), ite (e ∈ ({x} : set α)) 
          ((linear_map.inl 𝔽 W 𝔽) (φ e) + (linear_map.inr 𝔽 W 𝔽) 1) 
          (ite (e ∈ ({y} : set α)) ((linear_map.inr 𝔽 W 𝔽) 1) ((linear_map.inl 𝔽 W 𝔽) (φ e)))) ∘ coe) = 
          (λ (e : I), ite ((e : α) ∈ ({x} : set α)) 
          ((linear_map.inl 𝔽 W 𝔽) (φ e) + (linear_map.inr 𝔽 W 𝔽) 1) 
          (ite ((e : α) ∈ ({y} : set α)) ((linear_map.inr 𝔽 W 𝔽) 1) ((linear_map.inl 𝔽 W 𝔽) (φ e)))),
            simp only [eq_self_iff_true],
          have h7 : ∀ (e : I), ite (↑e ∈ ({x} : set α)) 
          ((linear_map.inl 𝔽 W 𝔽) (φ e) + (linear_map.inr 𝔽 W 𝔽) 1) 
          (ite (↑e ∈ ({y} : set α)) ((linear_map.inr 𝔽 W 𝔽) 1) ((linear_map.inl 𝔽 W 𝔽) (φ e))) 
          = ((linear_map.inl 𝔽 W 𝔽) (φ e)),
          { intros e,
            rw ite_eq_iff,
            right,
            refine ⟨mem_singleton_iff.1.mt (ne_of_mem_of_not_mem e.2 hxI), _⟩,
            apply ite_eq_iff.2,
            apply or.intro_right,
            refine ⟨mem_singleton_iff.1.mt (ne_of_mem_of_not_mem e.2 hyI), rfl⟩ },
          rw h6,
          simp_rw [λ (e : I), h7 e],
          rw [@_root_.linear_map.linear_independent_iff _ _ _ _ _ _ _ _ _ _ (linear_map.inl 𝔽 W 𝔽) 
            (linear_map.ker_eq_bot_of_injective linear_map.inl_injective), φ.valid, delete_elem],
          refine ⟨λ h2, h2.of_delete, λ h2, h2.indep_delete_of_disjoint 
            (disjoint_singleton_right.2 hyI)⟩,
          rw [delete_elem, delete_ground],
          apply subset_diff_singleton hI hyI } },
    end,
  support := _ }
 
-- i think this works for any field but i want to do it for zmod 2 for now
lemma rep_cocircuit_doubleton (x y : α) (hxy : x ≠ y) (B : set α) [module (zmod 2) W] 
  (φ : rep (zmod 2) W (M ⟍ y)) (hx : M.cocircuit {x, y}) (hB : (M ⟍ y).base B) : 
  rep (zmod 2) W M := 
{ to_fun := λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, φ i,
  valid' := λ I hI, 
    begin
      have h8 : linear_independent (zmod 2) ((λ (e : α), ∑ (i : α) in 
        (M.fund_circuit e B ∩ B).to_finset, φ i) ∘ coe) = 
        linear_independent (zmod 2) (λ (e : I), 
          ∑ (i : α) in (M.fund_circuit e B ∩ B).to_finset, φ i),
          { simp only },
      rw h8,
      by_cases y ∈ I, 
      { refine ⟨λ h2, _, λ h2, _⟩,
        { by_contra h3,
          rw ← @not_not (linear_independent (zmod 2) (λ (e : I), ∑ (i : α) in 
            (M.fund_circuit e B ∩ B).to_finset, φ i)) at h2,
          apply h2,
          by_cases hIy : (M ⟍ y).indep (I \ {y}), 
          { rw delete_elem at hIy,
            have h6 := (hIy.of_delete).mem_cl_iff_of_not_mem (not_mem_diff_singleton _ _),
            rw [insert_diff_singleton, insert_eq_of_mem h] at h6,
            rw [not_indep_iff, ← h6] at h3, 
            rw ← delete_elem at hIy, 
            by_cases M.fund_circuit y B = M.fund_circuit y (I \ {y}),
            { sorry },
            have hyB : y ∈ (M.cl B) \ B,
              { sorry },
              have hyI : y ∈ (M.cl (I \ {y})) \ (I \ {y}),
              { sorry },
              have hCB := hB.indep.of_delete.fund_circuit_circuit hyB,
              have hCY := hIy.of_delete.fund_circuit_circuit hyI,
              obtain ⟨C, ⟨hCs, hMC⟩⟩ := circuit.elimination hCB hCY h x, 
              apply fintype.not_linear_independent_iff.2,
              use (λ (e : I), if (e.1 ∈ C) then (1 : zmod 2) else (0 : zmod 2)),
              refine ⟨_, _⟩,
              sorry, -- fintype I, whatever
              have hss : ∑ (i : I), ite (i.val ∈ C) 1 0 • ∑ (i : α) in 
                (M.fund_circuit i B ∩ B).to_finset, φ i = 
                ∑ (e : C), ∑ (i : α) in 
                (M.fund_circuit e B ∩ B).to_finset, φ i,
              simp,
            /- have hs : ∑ (i : α) in (M.fund_circuit y B ∩ B).to_finset, φ i = 
              ∑ (i : α) in (M.fund_circuit y (I \ {y}) ∩ (I \ {y})).to_finset, φ i,
            by_cases M.fund_circuit y B = M.fund_circuit y (I \ {y}),
            { rw h,
              sorry },
            { have hyB : y ∈ (M.cl B) \ B,
              { sorry },
              have hyI : y ∈ (M.cl (I \ {y})) \ (I \ {y}),
              { sorry },
              have hCB := hB.indep.of_delete.fund_circuit_circuit hyB,
              have hCY := hIy.of_delete.fund_circuit_circuit hyI,
              have hC := circuit.elimination hCB hCY h y, 
              apply fintype.not_linear_independent_iff.2,
              --have hs := set.symm_diff_def,
              sorry },-/
            sorry,
            sorry,
            sorry },
          { rw ← (std_rep φ hB).valid at hIy,
            --apply hIy,
           -- have h3 := linear_independent.image h2,
            sorry,
            rw [delete_elem, delete_ground],
            apply diff_subset_diff_left hI } },
        { sorry } },
      { have h9 : ∀ (e : I), 
          ∑ (i : α) in (M.fund_circuit e B ∩ B).to_finset, φ i = φ e,
          { intros e,
            rw φ.mem_sum_basis_zmod2 hB.indep e (hB.mem_cl e _),
            simp_rw delete_elem,
            have h7 : y ∉ B,
              rw [delete_elem] at hB,
              have h11 := hB.subset_ground,
              rw [delete_ground, subset_diff, disjoint_singleton_right] at h11,
              apply h11.2,
            rw fund_circuit_delete (hB.indep).of_delete,
            { rw ← diff_singleton_eq_self h7,
              apply ((@mem_diff_singleton _ e.1 y _).1 _).1,
              rw [← delete_cl_eq, ← delete_elem], 
              apply hB.mem_cl _ _,
              simp only [delete_elem, delete_ground, mem_diff, mem_singleton_iff, auto_param_eq],
              refine ⟨hI e.2, has_mem.mem.ne_of_not_mem e.2 h⟩ },
            { apply disjoint_singleton_right.2 (mem_insert_iff.1.mt (not_or 
              (ne.symm (has_mem.mem.ne_of_not_mem e.2 h)) h7)) },
            simp only [delete_elem, delete_ground, mem_diff, mem_singleton_iff, auto_param_eq],
            refine ⟨hI e.2, has_mem.mem.ne_of_not_mem e.2 h⟩ },
        simp_rw [λ (e : I), h9 e],
        rw φ.valid,
        simp only [delete_elem, delete_indep_iff, disjoint_singleton_right, and_iff_left_iff_imp],
        intros,
        apply h,
        { rw [delete_elem, delete_ground],
          apply subset_diff_singleton hI h } },
    end,
  support := _ }

lemma coindep_singleton_excluded_minor (M : matroid_in α) 
(hM : excluded_minor (λ (N : matroid_in α), N.is_representable 𝔽) M) (x y : α) (hx : {x} ⊆ M.E) 
  : M.coindep {x} :=
begin
  by_contra,
  rw coindep_iff_forall_subset_not_cocircuit at h,
  push_neg at h,
  obtain ⟨K, hK1, hK2⟩ := h,
  have h2 := (dual_circuit_iff_cocircuit.2 hK2).nonempty,
  rw [← ground_inter_left (subset_trans hK1 hx)] at h2,
  --have h3 := hM.delete_mem h2,
  obtain ⟨W, _⟩ := hM.delete_mem h2,
  casesI h with hW ha,
  casesI ha with hFW hb,
  casesI hb with φ,
  obtain ⟨B, hB⟩ := (M ⟍ K).exists_base,
  obtain hK0 | rfl := subset_singleton_iff_eq.1 hK1,
  { apply (nonempty_iff_ne_empty.1 (dual_circuit_iff_cocircuit.2 hK2).nonempty) hK0 },
  have h4 : rep 𝔽 (W × 𝔽) M,
  use λ a : α, if a = x then (⟨0, 1⟩ : W × 𝔽) else ⟨φ a, 0⟩,
  { intros I hI,
    by_cases x ∈ I, 
    { refine ⟨λ h, _, λ h, _⟩,
      { sorry },  
      { --have h4 := linear_independent.inl_union_inr,
        sorry } },
    { 
      sorry } },
  { sorry },
  { sorry },
end

lemma coindep_excluded_minor (M : matroid_in α) 
(hM : excluded_minor (λ (N : matroid_in α), N.is_representable 𝔽) M) (x y : α) (hxy : x ≠ y) 
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
  { simp only [insert_diff_of_mem, mem_singleton, diff_singleton_eq_self 
      (mem_singleton_iff.1.mt hxy), subset_singleton_iff_eq] at ha2,
    cases ha2 with hempty hs,
    { apply (nonempty_iff_ne_empty.1 h2) hempty },
    rw hs at *,
    rw [← ground_inter_left (subset_trans hK1 hx)] at h2,
    obtain ⟨W, h3⟩ := hM.delete_mem h2,
    casesI h3 with hW ha,
    casesI ha with hFW hb,
    casesI hb with φ,
    obtain ⟨B, hB⟩ := (M ⟍ ({y} : set α)).exists_base,
    rw ← delete_elem at *, 
    have hmem := (mem_diff x).2 ⟨(mem_of_subset_of_mem hx ha1), mem_singleton_iff.1.mt hxy⟩,
    rw [← @ground_inter_left _ (M.E \ {y}) _ (diff_subset _ _)] at hmem,
    obtain ⟨W', h3'⟩ := hM.delete_mem (nonempty_of_mem hmem),
    casesI h3' with hW' ha',
    casesI ha' with hFW' hb',
    casesI hb' with φy,
    rw ← restrict_ground_diff at φy,
    simp only [sdiff_sdiff_right_self, inf_eq_inter, ground_inter_right] at φy,
    have φM := rep_cocircuit_singleton y B φ φy hK2 hB,
    simp only [excluded_minor, mem_minimals_prop_iff] at hM,
    apply hM.1,
    refine ⟨W × W', ⟨by {apply_instance}, ⟨_, ⟨φM⟩⟩⟩⟩ },
  { rw mem_singleton_iff.1 h at *,
    rw [← union_singleton, union_comm, union_singleton] at *,
    simp only [insert_diff_of_mem, mem_singleton, diff_singleton_eq_self 
      (mem_singleton_iff.1.mt (ne.symm hxy)), subset_singleton_iff_eq] at ha2,
    cases ha2 with hempty hs,
    { apply (nonempty_iff_ne_empty.1 h2) hempty },
    rw hs at *,
    rw [← ground_inter_left (subset_trans hK1 hx)] at h2,
    obtain ⟨W, h3⟩ := hM.delete_mem h2,
    casesI h3 with hW ha,
    casesI ha with hFW hb,
    casesI hb with φ,
    obtain ⟨B, hB⟩ := (M ⟍ ({x} : set α)).exists_base,
    rw ← delete_elem at *, 
    have hmem := (mem_diff y).2 ⟨(mem_of_subset_of_mem hx ha1), mem_singleton_iff.1.mt 
      (ne.symm hxy)⟩,
    rw [← @ground_inter_left _ (M.E \ {x}) _ (diff_subset _ _)] at hmem,
    obtain ⟨W', h3'⟩ := hM.delete_mem (nonempty_of_mem hmem),
    casesI h3' with hW' ha',
    casesI ha' with hFW' hb',
    casesI hb' with φx,
    rw ← restrict_ground_diff at φx,
    simp only [sdiff_sdiff_right_self, inf_eq_inter, ground_inter_right] at φx,
    have φM := rep_cocircuit_singleton x B φ φx hK2 hB,
    simp only [excluded_minor, mem_minimals_prop_iff] at hM,
    apply hM.1,
    refine ⟨W × W', ⟨by {apply_instance}, ⟨_, ⟨φM⟩⟩⟩⟩ },
  have hyy : ({y} ∩ M.E).nonempty,
  rw [← ground_inter_left (subset_trans hK1 hx)] at h2,
  --have h3 := hM.delete_mem h2,
  obtain ⟨W, _⟩ := hM.delete_mem h2,
  casesI h with hW ha,
  casesI ha with hFW hb,
  casesI hb with φ,
  obtain ⟨B, hB⟩ := (M ⟍ K).exists_base,
  have hrep := rep_cocircuit_doubleton x y hxy,
  /-
  have f := λ a : α, if a = x then (⟨0, 1⟩ : W × 𝔽) else ⟨φ a, 0⟩,
  have h1 : add_comm_group W × 𝔽,
    sorry,  
  have h2 : module 𝔽 (W × 𝔽), 
    sorry,
  have h3 : M.is_representable 𝔽,
  rw is_representable,
  have h4 : rep 𝔽 (W × 𝔽) M,
  -/
  sorry,
end

-- might need something that says if two matroids are rep. over the same field, then we can put them
-- in the same module

-- part (iii) in the proof of theorem 6.5.4
lemma indep_eq_doubleton_of_subset (MI MC : matroid_in α) [finite_rk MI] [finite_rk MC] (hrk : MI.rk = MC.rk)
  (hIC : MI.E = MC.E) (x y : α) (hxy : x ≠ y) (hiIC : MI.coindep {x,y} ∨ MC.coindep {x,y})
  (hMx : MI ⟍ x = MC ⟍ x) (hMy : MI ⟍ y = MC ⟍ y)
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

lemma U23_binary : (unif 2 3).is_binary :=
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
    refine ⟨(fin 2 → zmod 2), ⟨_, ⟨_, ⟨φ⟩⟩⟩⟩ },
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

-- this doesn't have sorry's but it relied on the unif_simple_iff lemma which isn't
-- available right now
lemma U24_nonbinary : ¬ (unif 2 4).is_binary :=
begin
  have U24_simple : (unif 2 4).simple,
    sorry,
  by_contra h2,
  rw [matroid_in.is_binary, is_representable] at h2,
  rcases h2 with ⟨W, ⟨hW, ⟨hM, ⟨φ'⟩⟩⟩⟩,
  haveI := zmod.fintype 2,
  obtain ⟨B, hB⟩ := (unif 2 4).exists_base,
  have φ := φ'.std_rep hB,
  /-rw rep.to_submodule' at φ,
  cases foo φ with φ,
  rw [rk_def, unif_r_eq] at φ,-/
  { --have h8 := card_le_of_subset (φ.subset_nonzero_of_simple U24_simple),
    -- need basis
    have h11 := ((valid'' φ' hB.subset_ground).2 hB.indep),
    have h11 : (finrank (zmod 2) (B →₀ zmod 2)) = 2,
      simp,
      sorry,
    have h10 := finite_dimensional.fin_basis (zmod 2) (B →₀ zmod 2),
    rw h11 at h10,
    have h9 := @module.card_fintype _ (zmod 2) (B →₀ zmod 2) _ _ _ _ h10 _ _,
    /-have h9 := module.card_fintype (finite_dimensional.fin_basis (zmod 2)
      (span (zmod 2) (φ '' (unif 2 4).E))),-/
    rw [rep.of_rank, rk_def, unif_r_eq] at h9,
    { -- there's probably a cleaner way to talk about the card of diff than going
      -- between fintype and finset cards
      simp_rw [← to_finset_card, to_finset_diff] at h8,
      rw finset.card_sdiff at h8,
      { simp only [set.to_finset_card, set_like.coe_sort_coe, card_singleton] at h8,
        simp only [fintype.card_of_finset, zmod.card, fintype.card_fin] at h9,
        rw h9 at h8,
        have h11 : fintype.card (φ '' (unif 2 4).E) = fintype.card (fin 4),
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

lemma coindep.base_of_basis_del {X : set α} (hX : M.coindep X) (hB : M.basis B (M.E \ X)) : 
  M.base B :=
begin
  obtain ⟨B',hB'⟩ := hX.exists_disjoint_base, 
  apply hB'.1.base_of_basis_supset (subset_diff.2 ⟨hB'.1.subset_ground, disjoint.symm hB'.2⟩) hB, 
end 

lemma delete_elem_eq_of_binary {B : set α} {x y : α} (hBxy : (M ⟍ ({x, y} : set α)).base B)
  (hBx : (M ⟍ x).base B) (hB : M.base B)
  [module (zmod 2) W] (φ : rep (zmod 2) W (M ⟍ ({x, y} : set α))) {Wx : Type*} [add_comm_group Wx]
  [module (zmod 2) Wx]
  (φx : rep (zmod 2) Wx (M ⟍ x)) : (M ⟍ x) = 
  (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
    (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (std_rep φ hBxy) i) M.E) ⟍ x :=
begin
  apply eq_of_indep_iff_indep_forall,
    simp_rw [delete_elem, delete_ground],
    rw matroid_of_module_fun.ground,
    intros I hI,
    rw [(matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (std_rep φ hBxy) i) M.E).delete_elem x, 
      delete_indep_iff, ← (std_rep φx hBx).valid' I hI],
    rw ← (rep_of_matroid_of_module_fun (zmod 2) (B →₀ zmod 2) 
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (std_rep φ hBxy) i) M.E).valid' I _,
    simp [rep_of_matroid_of_module_fun],
    have h12 : (λ (x_1 : α), ite (x_1 ∈ M.E) (∑ (x_1 : α) in (M.fund_circuit x_1 B).to_finset 
      ∩ B.to_finset, (φ.std_rep hBxy) x_1) 0) ∘ (coe : I → α) = 
      (λ (x_1 : I), ite (x_1.1 ∈ M.E) (∑ (x_1 : α) in (M.fund_circuit x_1 B).to_finset 
      ∩ B.to_finset, (φ.std_rep hBxy) x_1) 0),
      simp only [eq_self_iff_true],
      simp only [subtype.val_eq_coe],
    have h10 : ∀ (x_1 : I), ite (x_1.1 ∈ M.E) (∑ (x_1 : α) in (M.fund_circuit x_1 B).to_finset 
      ∩ B.to_finset, (φ.std_rep hBxy) x_1) 0 = (∑ (x_1 : α) in 
      (M.fund_circuit x_1 B).to_finset ∩ B.to_finset, (φ.std_rep hBxy) x_1),
      { simp only,
        simp only [subtype.val_eq_coe],
        intros e,
        simp_rw [ite_eq_iff],
        left,
        rw delete_elem at hI,
        refine ⟨(M.delete_ground_subset_ground {x}) (hI e.2), rfl⟩ },
    simp_rw [h12, h10],
    have h3 : ((φx.std_rep hBx) ∘ (coe : I → α)) = λ (e : I), ((φx.std_rep hBx) e),
      simp only [eq_self_iff_true],
    rw [h3],
    simp_rw λ (e : I), (std_rep φx hBx).mem_sum_basis_zmod2 hBx.indep _ 
      (@base.mem_cl _ (M ⟍ x) B hBx e (hI e.2)),
    have hBxs := hBx.subset_ground,
    simp_rw [delete_elem, delete_ground] at *,
    have h5 := diff_subset M.E {x},
    simp_rw λ (e : I), fund_circuit_delete hB.indep (@base.mem_cl _ M B hB e ((diff_subset M.E {x}) 
      (hI e.2))) (disjoint_singleton_right.2 (mem_insert_iff.1.mt (not_or (ne.symm 
      (mem_diff_singleton.1 (hI e.2)).2) (not_mem_subset hBxs 
      (not_mem_diff_of_mem (mem_singleton x)))))),
    have h6 : (λ (e : ↥I), ∑ (x : α) in (M.fund_circuit ↑e B ∩ B).to_finset, (std_rep φx hBx) x) = 
      (λ (e : ↥I), ∑ (x : α) in (M.fund_circuit ↑e B ∩ B).to_finset, (std_rep φ hBxy) x),
      simp only,
      have h10 :=  λ (i : ↥I), @finset.sum_congr _ _ (M.fund_circuit i B ∩ B).to_finset 
        (M.fund_circuit i B ∩ B).to_finset (std_rep φx hBx) (std_rep φ hBxy) _ rfl _,
      simp_rw  [λ (i : I), h10 i],
      intros x hx,
      rw mem_to_finset at hx,
      have h12 := std_rep_base_eq φx φ hBx hBxy ⟨x, (mem_of_mem_inter_right hx)⟩,
      simp at h12,
      rw h12,
    simp_rw [h6, to_finset_inter, iff_self_and],
    apply λ h, not_mem_subset hI (not_mem_diff_singleton x M.E),
    rw [delete_elem, delete_ground] at hI,
    rw matroid_of_module_fun.ground,
    apply subset_trans hI (diff_subset M.E {x}),
end

lemma delete_elem_eq_of_binary_right {B : set α} {x y : α} (hBxy : (M ⟍ ({x, y} : set α)).base B)
  (hBx : (M ⟍ y).base B) (hB : M.base B)
  [module (zmod 2) W] (φ : rep (zmod 2) W (M ⟍ ({x, y} : set α))) {Wy : Type*} [add_comm_group Wy]
  [module (zmod 2) Wy]
  (φx : rep (zmod 2) Wy (M ⟍ y)) : (M ⟍ y) = 
  (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
    (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (std_rep φ hBxy) i) M.E) ⟍ y :=
begin
  sorry
end

lemma eq_iff_indep_iff_minimals_empty {M₁ M₂ : matroid_in α} : 
  M₁ = M₂ ↔ (M₁.E = M₂.E) ∧ minimals (⊆) {A | ¬(M₁.indep A ↔ M₂.indep A)} = ∅ :=
begin
  refine ⟨λ hM12, _, λ hmin, _⟩,
  { refine ⟨_, _⟩,
    rw hM12,
    rw minimals,
    simp only [mem_set_of_eq, sep_set_of],
    rw hM12,
    simp only [iff_self, not_true, false_and, set_of_false] },
  { rw eq_iff_indep_iff_indep_forall,
    refine ⟨hmin.1, λ I hI, _⟩,
    sorry },
end

lemma rep_of_loop (M : matroid_in α) [finite_rk M] {f : α} (hf : M.loop f) 
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
      rw [delete_elem, delete_ground],
      apply hIf,
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

lemma rep_of_parallel (M : matroid_in α) [finite_rk M] {x y : α} (hxy : x ≠ y) 
  (hf : M.circuit {x, y}) (φ : rep 𝔽 W (M ⟍ ({y} : set α))) : rep 𝔽 W M := 
{ to_fun := λ (e : α), if e = y then φ x else φ e,
  valid' := λ I hI, 
    begin
      by_cases y ∈ I,
      { sorry },
      { sorry },
    end,
  support := _ }

lemma excluded_minor_nonloop (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor matroid_in.is_binary M) {f : α} (hf : f ∈ M.E) : M.nonloop f :=
begin
  by_contra,
  have hfM : ({f} ∩ M.E).nonempty,
    simp only [ground_inter_left, singleton_nonempty],
  obtain ⟨W, hW⟩ := hM.delete_mem hfM,
  casesI hW with hW hFW,
  casesI hFW with hFW h,
  casesI h with φ,
  rw [excluded_minor, mem_minimals_prop_iff] at hM,
  simp only [not_nonloop_iff] at h,
  apply hM.1,
  refine ⟨W, ⟨by { apply_instance }, ⟨by { apply_instance }, ⟨rep_of_loop M h φ⟩⟩⟩⟩,
end

lemma excluded_minor_nonpara (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor matroid_in.is_binary M) {x y : α} (hxy : x ≠ y) :
  ¬ M.circuit {x, y}  :=
begin
  by_contra,
  have hfM : ({y} ∩ M.E).nonempty,
    simp only [singleton_inter_nonempty],
    apply mem_of_subset_of_mem h.subset_ground,
    simp only [mem_insert_iff, mem_singleton, or_true],
  obtain ⟨W, hW⟩ := hM.delete_mem hfM,
  casesI hW with hW hFW,
  casesI hFW with hFW h,
  casesI h with φ,
  rw [excluded_minor, mem_minimals_prop_iff] at hM,
  apply hM.1,
  refine ⟨W, ⟨by { apply_instance }, ⟨by { apply_instance }, ⟨rep_of_parallel M hxy h φ⟩⟩⟩⟩,
end

lemma excluded_minor_simple (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor matroid_in.is_binary M) : simple M :=
begin
  intros e he f hf,
  rw indep_iff_forall_subset_not_circuit,
  intros C hC,
  { cases ssubset_or_eq_of_subset hC with hC heq,
    { rw ssubset_iff_subset_diff_singleton at hC,
      obtain ⟨x, ⟨hx1, hx2⟩⟩ := hC,
      simp at hx1,
      obtain ⟨rfl | rfl⟩ := hx1,
      simp at hx2,
      sorry,
      sorry },
    { rw heq,
      sorry } },
  /-by_cases e = f,
  { rw h,
    simp only [pair_eq_singleton, indep_singleton],
    apply excluded_minor_nonloop M hM hf },
  { rw indep_iff_forall_subset_not_circuit,
    intros C hC,
    cases ssubset_or_eq_of_subset hC with heq hC,
    
    sorry },-/
  sorry,
end

/-lemma unif_restr {a b : ℕ} (M : matroid_in α) {k : ℕ} (hcard : M.E.ncard = k) (hs : M.simple) 
  (hr : M.rk = 2) : (unif 2 k) ≃i M :=
begin
  rw unif,
  apply iso_of_bij_on,
  sorry,
  sorry,
  sorry,
end-/

-- write congr lemma
def rep_of_congr {M M' : matroid_in α} (φ : rep 𝔽 W M) (h : M = M') : rep 𝔽 W M' := 
{ to_fun := φ.to_fun,
  valid' := λ I hI, by { rw ← (eq_iff_indep_iff_indep_forall.1 h).1 at hI, 
    rw ← (eq_iff_indep_iff_indep_forall.1 h).2, apply φ.valid' I hI, apply hI },
  support := λ e he, by { rw ← (eq_iff_indep_iff_indep_forall.1 h).1 at he, apply φ.support e he } }

-- write refl lemma for the above
lemma rep_eq_of_congr {M M' : matroid_in α} (φ : rep 𝔽 W M) (h : M = M') : 
  (φ : α → W) = (rep_of_congr φ h) := rfl

lemma excluded_minor_binary_unif24 (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor matroid_in.is_binary M) : iso_minor (unif 2 4) M :=
begin
  -- this comes from hM
  have hME : nontrivial M.E,
    by_contra,
    sorry,
  rw [nontrivial_coe_sort, nontrivial_iff_pair_subset] at hME,
  obtain ⟨x, ⟨y, ⟨hxy1, hxy2⟩⟩⟩ := hME,
  have h2 := coindep_excluded_minor M hM x y hxy1 hxy2,
  have hxyr : (M ⟍ ({x, y} : set α)).is_binary,
    sorry,
  obtain ⟨W, _⟩ := hxyr,
  casesI hxyr_h with hW ha,
  casesI ha with hFW hb,
  casesI hb with φ,
  obtain ⟨B, hBxy⟩ := (M ⟍ ({x, y} : set α)).exists_base,

  obtain ⟨Wx, _⟩ := (((excluded_minor_iff _).1 hM).2 x (hxy2 (mem_union_left {y} (mem_singleton x)))).2,
  casesI h with hWx ha,
  casesI ha with hFWx hb,
  casesI hb with φx,

  obtain ⟨Wy, _⟩ := (((excluded_minor_iff _).1 hM).2 y (hxy2 (mem_union_right {x} (mem_singleton y)))).2,
  casesI h with hWy ha,
  casesI ha with hFWy hb,
  casesI hb with φy,
  
  have hB := coindep.base_of_basis_del h2 (delete_base_iff.1 hBxy),

  have hBy : (M ⟍ y).base B,
    rw delete_elem,
    sorry,
  
  have hBx : (M ⟍ x).base B,
    sorry,
  
  have hMM'E : M.E = (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (std_rep φ hBxy) i) M.E).E,
    rw matroid_of_module_fun.ground,
  have hMM'x := delete_elem_eq_of_binary hBxy hBx hB φ φx,
  have hByx := hBxy,
  have φyx := φ,
  rw [← union_singleton, union_comm, union_singleton] at hByx,
  rw [← union_singleton, union_comm, union_singleton] at φyx,
  have hMM'y := delete_elem_eq_of_binary hByx hBy hB φyx φy,
  have hφ : ∀ (a : α), (φyx.std_rep hByx) a = (φ.std_rep hBxy) a,
  { intros a,
    -- use rep_eq_of_congr
    /-rw [← union_singleton, union_comm, union_singleton] at *,
    rw [← union_singleton, union_comm, union_singleton] at φyx,-/
    sorry },
  simp_rw [λ (a : α), hφ a] at hMM'y,
  have hB' : (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (std_rep φ hBxy) i) M.E).base B,
    { rw hMM'x at hBx,
      rw hMM'y at hBy,
      rw [base_iff_basis_ground, ← @diff_empty _ (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
        (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (std_rep φ hBxy) i) M.E).E, 
        ← singleton_inter_eq_empty.2 (mem_singleton_iff.1.mt hxy1), diff_inter], 
      rw [delete_elem, delete_base_iff] at hBx hBy,
      apply basis.basis_union hBx hBy },
  have hMM'r : M.rk = (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (std_rep φ hBxy) i) M.E).rk,
    { rw [← hB'.card, hB.card] },
    have hMM' : M ≠ (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (std_rep φ hBxy) i) M.E),
    { by_contra,
      rw [excluded_minor, mem_minimals_prop_iff] at hM,
      apply hM.1,
      rw [h, mem_def, matroid_in.is_binary, is_representable],
      -- changed (α : Type *) to (α : Type) to make this work
      refine ⟨B →₀ zmod 2, ⟨_, ⟨_, ⟨(rep_of_matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
        (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (std_rep φ hBxy) i) M.E)⟩⟩⟩⟩ },
    simp at hMM',
    rw [eq_iff_indep_iff_indep_forall, matroid_of_module_fun.ground] at hMM', 
    simp only [eq_self_iff_true, true_and, not_forall, exists_prop] at hMM',

    have hZ : ∃ (Z : set α), Z ∈ minimals (⊆) {A | ¬(M.indep A ↔ 
      (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (std_rep φ hBxy) i) M.E).indep A) },  
    { -- has to exist since the matroids aren't equal
      sorry },
    obtain ⟨Z, hZ⟩ := hZ,
    simp_rw [iff_def, not_and_distrib, not_imp] at hZ,
    rw mem_minimals_prop_iff at hZ,
    cases hZ.1 with hMZ hM'Z,
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
        casesI hM.contract_mem hJxyM with W hW,
        casesI hW with hW hFW,
        casesI hFW with hFW hN,
        casesI hN with φN,
        have φN' := rep_of_contr _ (rep_of_matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
          (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (std_rep φ hBxy) i) M.E) (J \ {x, y})
          (by { rw matroid_of_module_fun.ground, apply subset_trans (diff_subset _ _) hMJ.subset_ground }),
        apply h (indep_eq_doubleton_of_subset M (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
          (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (std_rep φ hBxy) i) M.E) hMM'r hMM'E 
          x y hxy1 (by { left, apply h2 }) hMM'x hMM'y hZx hZy hMZ.1 hMZ.2 hZJ hMJ φN φN') },
        { obtain ⟨BZ, hBZ⟩ := hMZ.1,
          specialize hJZ BZ hBZ.1.indep hBZ.2,
          have hsimp := excluded_minor_simple M hM,
          have hcard : 2 ≤ M.E.ncard,
            sorry, 
          have hunif := (iso_line_iff hcard).2 ⟨hsimp, _⟩,
          have hcard4 : 4 ≤ M.E.ncard,
            sorry, 
          sorry } },
      { sorry },
end

-- need the one-dimensional subspaces lemma for this
/--lemma card_of_unif_rep (k : ℕ) (hk : 1 < k) (h2 : is_representable 𝔽 (unif 2 k)) [fintype 𝔽]: 
  k - 1 ≤ nat.card (@univ 𝔽) :=
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
end-/

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

end rep

end matroid_in
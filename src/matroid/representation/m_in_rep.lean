import analysis.inner_product_space.gram_schmidt_ortho
import data.zmod.basic
import linear_algebra.basis
import linear_algebra.linear_independent
import m_in.minor m_in.constructions
import m_in.erank
import m_in.equiv




universe u 
variables {α β 𝔽 : Type*} {M : matroid_in α} {I B : set α} {x : α}
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
structure rep (𝔽 W : Type*) [field 𝔽] [add_comm_group W] [module 𝔽 W] (M : matroid_in α) :=
(to_fun : α → W)
(valid' : ∀ (I ⊆ M.E), linear_independent 𝔽 (to_fun ∘ coe : I → W) ↔ M.indep I)
(support : ∀ (e : α), e ∉ M.E → to_fun e = 0)

instance fun_like {𝔽 W : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] {M : matroid_in α } : 
  fun_like (rep 𝔽 W M) α (λ _, W) := 
{ coe := λ φ e, φ.to_fun e,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

instance : has_coe_to_fun (rep 𝔽 W M) (λ _, α → W) := fun_like.has_coe_to_fun

lemma valid {φ : rep 𝔽 W M} {I : set α} : linear_independent 𝔽 (φ ∘ coe : I → W) ↔ M.indep I := 
begin
  sorry
end 

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

-- i think we need this because it accounts for things like repeated columns
-- this also allows us to compare matroids on the same type in the U24 proof, 
-- as opposed to comparing matroid_in α and matroid_in W. 
def matroid_of_module_func (𝔽 W : Type*) {ι : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] 
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
        sorry,
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
    haveI : fintype I,
      sorry,
    rw [ncard, nat.card_eq_fintype_card],
    refine ⟨sorry, fintype_card_le_finrank_of_linear_independent hI.1⟩,
  end
  (by { tauto })

lemma ground_matroid_of_module_func (𝔽 W : Type*) {ι : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] 
  [finite_dimensional 𝔽 W] (v : ι → W) (ground : set ι) : 
    (matroid_of_module_func 𝔽 W v ground).E = ground := 
begin
  rw [matroid_of_module_func, matroid_of_indep_of_bdd', matroid_of_indep_of_bdd, 
    matroid_of_indep, matroid_of_base, ← ground_eq_E],
end

def rep_of_matroid_of_module_func (𝔽 W : Type*) {ι : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] 
  [finite_dimensional 𝔽 W] (v : ι → W) (ground : set ι) : rep 𝔽 W (matroid_of_module_func 𝔽 W v ground) := 
{ to_fun := v,
  valid' := λ I hI, by {simp only [matroid_of_module_func, matroid_of_indep_of_bdd'_apply], 
    simp only [iff_self_and], intros h, rw ground_matroid_of_module_func at hI, apply hI } }

def rep_of_matroid_of_module_set (𝔽 W : Type*) [field 𝔽] [add_comm_group W] [module 𝔽 W] 
  [finite_dimensional 𝔽 W] (s : set W) : rep 𝔽 W (matroid_of_module_set 𝔽 W s) := 
{ to_fun := id,
  valid' := λ I hI, 
    begin
      simp only [comp.left_id, matroid_of_module_set, matroid_of_indep_of_bdd'_apply, iff_self_and],
      intros hI2,
      rw ground_matroid_of_module_set at hI,
      apply hI,
    end }

/-def rep_union (𝔽 W : Type*) [field 𝔽] [add_comm_group W] [module 𝔽 W] (N N' : matroid_in α) 
(hN : N ≤m M) (hN' : N' ≤m M) (hNN' : disjoint N.E N'.E) (hNN'2 : N.E ∪ N'.E = M.E) 
(φ : rep 𝔽 W N) (φ2 : rep 𝔽 W N') 
(hI : ∀ s ⊆ N.E, ∀ t ⊆ N'.E, linear_independent 𝔽 ((φ.to_fun ∘ coe : s → W) ∪ (φ2.to_fun ∘ coe : t → W))) ↔ M.indep (s ∪ t) 
  : rep 𝔽 W M := -/

-- use finite_rank stuff
-- if M has rank 2, has at least 4 elements, and is simple, then M is deletion of U_{2, 4}
lemma unif24_of_rank_2_simple_le_4 (M : matroid_in α) (h2 : M.rk = 2) (h4 : 4 ≤ M.E.ncard) 
(hs : M.simple) : iso_minor (unif 2 4) M :=
begin
  rw iso_minor,
  rw simple at hs,
  have h5 : 4 = (unif 2 4).E.ncard,
    { simp only [unif_ground_eq],
      rw ncard_eq_to_finset_card,
      simp only [finite.to_finset_univ, finset.card_fin] },
  rw h5 at h4,
  have h6 : ∃ D ⊆ M.E, (M ⟍ D).E.ncard = 4,  
    simp,
    sorry,
  obtain ⟨D, ⟨hD1, hD2⟩⟩ := h6,
  use (M ⟍ D),
  have f : (unif 2 4).E ≃ (M ⟍ D).E,
    sorry,
  have h11 : (∀ (I : set ↥((unif 2 4).E)), 
    (unif 2 4).indep (coe '' I) ↔ (M ⟍ D).indep (coe '' (⇑f '' I))),
  { intros I,
    rw unif_indep_iff,
    refine ⟨λ h, _, λ h, _⟩,
    rw delete_indep_iff,
    sorry,
    -- need finite_rk instance for minors
    haveI : M.finite_rk,
    sorry,
    /-haveI : (M ⟍ D).finite_rk,
    sorry,-/
    --have h2 := h.card_le_rk,
    have h3 : (coe '' I).ncard = ((coe '' (⇑f '' I)) : set α).ncard,
    apply nat.card_congr,
    apply equiv.trans 
      (equiv.trans (equiv.symm (equiv.set.image (coe : ↥((unif 2 4).E) → (fin 4)) I _)) 
      (equiv.image f I)) (equiv.set.image (coe : ↥((M ⟍ D).E) → α) (⇑f '' I) _),
    --rw has_lift.coe_eq_coe_fn,
    intros x y h,
    sorry,
    intros x y h,
    sorry,
    rw h3,
    have h80 : (M ⟍ D).rk ≤ M.rk,
      sorry,
    have h90 := le_trans (h.card_le_rk) h80, 
    rw h2 at h90, 
    apply h90 },
  refine ⟨delete_minor M D, _⟩,
  use iso_of_indep f h11,
end

namespace rep

variables [fintype α]



lemma valid (φ : rep 𝔽 W M) {I : set α} {hI : I ⊆ M.E}: linear_independent 𝔽 (λ e : I, φ e) ↔ 
  M.indep I := φ.valid' _ hI

protected lemma is_representable {W : Type} [add_comm_group W] [module 𝔽 W] (φ : rep 𝔽 W M) : 
  is_representable 𝔽 M := ⟨W, ⟨_, ⟨_, ⟨φ⟩⟩⟩⟩

lemma inj_on_of_indep (φ : rep 𝔽 W M) (hI : M.indep I) : inj_on φ I :=
inj_on_iff_injective.2 ((φ.valid' I hI.subset_ground).2 hI).injective

/-lemma eq_zero_of_not_mem_ground (φ : rep 𝔽 W M) {e : α} (he : e ∉ M.E) : φ e = 0 :=
begin
  by_contra,
  apply he,
  rw ← singleton_subset_iff,
  apply indep.subset_ground,
  rw ← φ.valid',
  have h2 := @linear_independent_singleton 𝔽 W _ _ _ _ _ _ h,
  rw [← image_singleton, ← linear_independent_image (inj_on_singleton φ e)] at h2,
  apply h2,
end  -/

@[simp] lemma to_fun_eq_coe (φ : rep 𝔽 W M) : φ.to_fun = (φ : α → W)  := by { ext, refl }

lemma linear_independent_iff_coe (φ : rep 𝔽 W M) (hI : M.indep I) :
  linear_independent 𝔽 (λ e : I, φ e) ↔ linear_independent 𝔽 (coe : φ '' I → W) :=
linear_independent_image $ inj_on_of_indep _ hI

def to_submodule (φ : rep 𝔽 W M) : submodule 𝔽 W := span 𝔽 (range φ)

def to_submodule' (φ : rep 𝔽 W M) : submodule 𝔽 W := span 𝔽 (φ '' M.E)

lemma mem_to_submodule (φ : rep 𝔽 W M) (x : α) {hx : x ∈ M.E} : φ x ∈ φ.to_submodule :=
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
    end } 

def rep.compose (φ : rep 𝔽 W M) (e : W ≃ₗ[𝔽] W') : rep 𝔽 W' M := 
{ to_fun := e ∘ φ,
  valid' := λ I,
    begin
      rw comp.assoc,
      have h2 := linear_map.linear_independent_iff e.to_linear_map e.ker,
      simp only [linear_equiv.coe_to_linear_map] at h2,
      rw h2,
      apply φ.valid',
    end }

def rep.compose' (φ : rep 𝔽 W M) (e : φ.to_submodule' ≃ₗ[𝔽] W') : rep 𝔽 W' M := 
  (rep.compose (φ.rep_submodule) e)

def rep.of_base' (φ : rep 𝔽 W M) (B : set α) (hB : M.base B) (φ' : B → W') 
  (hφ' : linear_independent 𝔽 φ') : rep 𝔽 W' M := sorry 

lemma ne_zero_of_nonloop (φ : rep 𝔽 W M) (hx : M.nonloop x) : φ x ≠ 0 :=
((φ.valid' {x} (indep_singleton.2 hx).subset_ground).2 hx.indep).ne_zero 
(⟨x, mem_singleton _⟩ : ({x} : set α))

lemma ne_zero_of_loopless (φ : rep 𝔽 W M) (hl : loopless M) (x : α) (hx : x ∈ M.E) : φ x ≠ 0 :=
φ.ne_zero_of_nonloop $ indep_singleton.1 (hl {x} (singleton_subset_iff.2 hx) (ncard_singleton x))

lemma inj_on_ground_of_simple (φ : rep 𝔽 W M) (hs : simple M) : inj_on φ M.E :=
λ a ha b hb, --inj_on_of_indep _ $ hs a ha b hb
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
  _root_.basis B 𝔽 (span 𝔽 (φ '' M.E)) := by {
rw [←span_base _ hB, image_eq_range], exact basis.span ((φ.valid' B hB.subset_ground).2 hB.indep) }


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

instance fin_dim_rep' (φ : rep 𝔽 W M) [M.finite_rk] [fintype 𝔽] : 
  finite_dimensional 𝔽 φ.to_submodule' :=
begin
  cases M.exists_base with B hB,
  apply finite_dimensional.of_finite_basis (basis_of_base φ hB) (base.finite hB),
end

@[simp] lemma mem_span_rep_range (φ : rep 𝔽 W M) : ∀ (x : α), φ x ∈ (span 𝔽 (range ⇑φ)) := 
  λ x, by { apply mem_of_subset_of_mem (@subset_span 𝔽 _ _ _ _ (range ⇑φ)) (mem_range_self x) }

@[simp] lemma mem_span_rep (φ : rep 𝔽 W M) : ∀ (x ∈ M.E) , φ x ∈ (span 𝔽 (φ '' M.E)) := 
  λ x h, by { apply mem_of_subset_of_mem (@subset_span 𝔽 _ _ _ _ (φ '' M.E)) (mem_image_of_mem φ h) }

-- it's not true that (φ '' M.E) = (range ⇑φ) because we can have φ x = 0 for some x ∉ M.E,
-- but if M.E is loopless, there are no y ∈ M.E such that φ x = 0.  
@[simp]
lemma span_range_eq_span_image (φ : rep 𝔽 W M) : span 𝔽 (φ '' M.E) ≤ span 𝔽 (range ⇑φ) :=
sorry

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
{ to_fun := φ.to_fun,
  valid' := λ I hI, by { rw delete_ground at hI, 
    refine ⟨λ h, delete_indep_iff.2 ⟨((φ.valid' I (subset_trans hI (diff_subset N.E D))).1 h), 
    (subset_diff.1 hI).2⟩, λ h, (φ.valid' I (subset_trans hI (diff_subset N.E D))).2 
    (matroid_in.delete_indep_iff.1 h).1⟩ } }

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

def is_rep_of_minor_of_is_rep (N : matroid_in α) (hNM : N ≤m M) (hM : M.is_representable 𝔽) : 
  N.is_representable 𝔽 := 
begin
  obtain ⟨W, ⟨_, ⟨_, ⟨φ⟩⟩⟩⟩ := hM,
  obtain ⟨C, ⟨D, ⟨hC, ⟨hD, ⟨hCD, rfl⟩⟩⟩⟩⟩ := minor.exists_contract_indep_delete_coindep hNM,
  refine ⟨_, ⟨_, ⟨_, ⟨rep_of_del (M ⟋ C) 
    (@rep_of_contr _ 𝔽 W _ hM_h_w hM_h_h_w _ M φ C hC.subset_ground) D⟩⟩⟩⟩,
end

lemma indep.union (M : matroid_in α) (I J : set α) : 
  M.indep (I ∪ J) ↔ (∀ x ∈ M.cl I ∩ M.cl J, M.loop x) ∧ M.indep I ∧ M.indep J :=
begin
  sorry,
end

lemma span_equiv_of_rep [M.finite_rk] [fintype 𝔽] (φ : rep 𝔽 W (M ⟍ x)) (φ2 : rep 𝔽 W' M) (hx : x ∈ M.cl (M.E \ {x})) :
  (φ.to_submodule') ≃ₗ[𝔽] (φ2.to_submodule')  :=
begin
  rw [to_submodule', to_submodule'],
  apply linear_map.linear_equiv_of_injective,
  sorry,
  sorry,
  sorry,
end

def extend_rep (M : matroid_in α) [M.finite_rk] [fintype 𝔽] (J : set α) (hJ : M.base J) (x : α) 
  (hx : x ∈ M.E) (hx : x ∈ M.cl (M.E \ {x})) (φ' : rep 𝔽 W' (M ⟍ x)) (φ : rep 𝔽 W M) : rep 𝔽 W' M := 
begin
  have h2 := rep.compose' φ (linear_equiv.symm (span_equiv_of_rep φ' φ hx)),
  sorry,
end

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
  apply mem_span_rep φ x (mem_of_subset_of_mem (M.cl_subset_ground X) hx) }

lemma cl_subset_span_set (φ : rep 𝔽 W M) {X : set α} (hX : X ⊆ M.E) : 
  φ '' M.cl X ⊆ span 𝔽 (φ '' X) :=
by { rintros _ ⟨x, ⟨hx, rfl⟩⟩, apply mem_span_cl φ hX hx }

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

def rep_of_rep' (φ : rep' 𝔽 M ι) : rep 𝔽 (ι → 𝔽) M := ⟨φ, λ I hI, φ.valid' I hI⟩    

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

lemma span_range_eq_span_image' (φ : rep' 𝔽 M ι) : span 𝔽 (φ '' M.E) ≤ span 𝔽 (range ⇑φ) :=
sorry
/-span_eq_span (λ x ⟨y, ⟨hx1, hx2⟩⟩, by {rw ← hx2, apply mem_span_rep_range' φ y}) 
  (λ x ⟨y, hx⟩, by {rw ← hx, apply mem_span_rep' φ y })-/

lemma basis_of_base' (φ : rep' 𝔽 M ι) {B : set α} (hB : M.base B) :
  _root_.basis B 𝔽 (span 𝔽 (φ '' M.E)) := by { rw [←span_base' _ hB, image_eq_range], 
  exact basis.span ((φ.valid' B hB.subset_ground).2 hB.indep) }

instance fin_dim_rep' (φ : rep' 𝔽 M ι) [fintype 𝔽] : 
  finite_dimensional 𝔽 (span 𝔽 (φ '' M.E)) :=
begin
  cases M.exists_base with B hB,
  apply finite_dimensional.of_finite_basis (basis_of_base' φ hB) (base.finite hB),
end

instance fin_dim_rep (φ : rep' 𝔽 M ι) [fintype 𝔽] : 
  finite_dimensional 𝔽 (span 𝔽 (range φ)) :=
begin
  cases M.exists_base with B hB,
  have h2 := finite_dimensional.of_finite_basis (basis_of_base' φ hB) (base.finite hB),
  -- application of fintype α and fintype 𝔽
  sorry,
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

-- we have fin_dim_vectorspace_equiv
def foo (φ' : rep 𝔽 W M) [fintype 𝔽] [finite_dimensional 𝔽 W] :
  rep' 𝔽 M (fin M.rk)  := 
begin
  obtain φ := rep'.rep'_of_rep (φ'.rep_submodule) _,
  use φ,
  rw [← (of_rank φ'), to_submodule'],
end

lemma foo' (φ : rep 𝔽 W M) [fintype 𝔽] [finite_dimensional 𝔽 W] :
  nonempty (rep 𝔽 (fin M.rk → 𝔽) M) :=
begin
  have φ := foo φ,
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

lemma fund_circuit_inter_eq_diff_of_not_mem (e : α) (he : e ∈ M.cl I) (h2 : e ∉ I) : 
  (M.fund_circuit e I ∩ I) = (M.fund_circuit e I \ {e}) :=
begin
  apply eq_of_subset_of_subset,
  rw [diff_eq, compl_eq_univ_diff],
  apply inter_subset_inter (subset.refl _) (subset_diff_singleton (subset_univ I) h),
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
  ∑ i in (M.fund_circuit e I ∩ I).to_finset, φ i = φ e :=
begin
  by_cases e ∈ I,
  rw [hI.fund_circuit_eq_of_mem h, @to_finset_congr _ ({e}∩I) {e} _ _ (singleton_inter_eq_of_mem h),
     to_finset_singleton, finset.sum_singleton],
  rw to_finset_congr (fund_circuit_inter_eq_diff_of_not_mem _ he h),
  apply mem_sum_basis_zmod2_of_not_mem φ hI e he h,
end


noncomputable def std_rep {𝔽 W : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] 
{M : matroid_in α} (φ : rep 𝔽 W M) (hB : M.base B) : rep 𝔽 (B → 𝔽) M := sorry  


/- A matroid_in is binary if it has a `GF(2)`-representation -/
@[reducible, inline] def matroid_in.is_binary (M : matroid_in α) := M.is_representable (zmod 2)


lemma eq_of_forall_fund_circuit_eq {M M' : matroid_in α} (hMb : M.is_binary) (hM'b : M'.is_binary) 
(hE : M.E = M'.E) (hB : M.base B) (hB' : M'.base B) 
(he : ∀ e ∈ M.E \ B, M.fund_circuit e B = M'.fund_circuit e B) :
  M = M' :=
begin
  sorry 
end 
  

-- I think we might actually need 3-connectedness for this?
lemma cocircuits_nonbinary_minor (M : matroid_in α) (hM : ¬ M.is_binary) {x : α} (hx : x ∈ M.E) : -- M.E \ {x}  not hyperplane?
  x ∈ M.cl (M.E \ {x}) :=
begin
  sorry,
end   

lemma cocircuits_excluded_minor (M : matroid_in α)
(hM : excluded_minor (λ (N : matroid_in α), N.is_representable 𝔽) M) {x : α} (hx : x ∈ M.E) : 
  ¬ M.cocircuit {x} :=
begin
  by_contra,
  rw excluded_minor_iff at hM,
  obtain ⟨W, ⟨_, ⟨_, ⟨φ⟩⟩⟩⟩ := (hM.2 x hx).2,
  haveI : has_zero W,
    sorry,
  rw [cocircuit_iff_mem_minimals_compl_nonspanning, mem_minimals_iff'] at h,
  simp only [mem_set_of_eq, subset_singleton_iff] at h,
  apply hM.1,
  simp only,
  --use ⟨W × 𝔽, ⟨_, ⟨_, ⟨_⟩⟩⟩⟩,
  have f := λ a : α, if a = x then (⟨0, 1⟩ : W × 𝔽) else ⟨φ a, 0⟩,
  have h1 : add_comm_group W × 𝔽,
    sorry,  
  have h2 : module 𝔽 (W × 𝔽), 
    sorry,
  have h3 : M.is_representable 𝔽,
  rw is_representable,
  have h4 : rep 𝔽 (W × 𝔽) M,
  use f,
  intros I hI,
  by_cases x ∈ I,
  { refine ⟨λ h, _, λ h, _⟩,  
    sorry,
    --have h2 := linear_independent.inl_union_inr,
    sorry, },  
  { 
    refine ⟨λ h, _, λ h, _⟩, 
    sorry },

  -- for some reason this isn't working but i think it should be
  --use ⟨W × 𝔽, ⟨h1, ⟨h2, ⟨h4⟩⟩⟩⟩,
  sorry,
  sorry,
end

lemma cocircuits_excluded_minor' (M : matroid_in α) 
(hM : excluded_minor (λ (N : matroid_in α), N.is_representable 𝔽) M) (x y : α) (hx : x ∈ M.E) 
(hy : y ∈ M.E) : ¬ M.cocircuit {x, y} :=
begin
  sorry,
end

-- might need something that says if two matroids are rep. over the same field, then we can put them
-- in the same module

-- part (iii) in the proof of theorem 6.5.4
lemma indep_eq_doubleton_of_nonbinary (M : matroid_in α) (hM : ¬ M.is_binary) (hI : M.indep I)
  {Z : set α} {x y : α} (hx : x ∈ M.E) (hy : y ∈ M.E) (hxb : (M ⟍ ({x} : set α)).is_binary) 
  (φy : (M ⟍ ({y} : set α)).is_binary) (hxy : M.rk = M.r (univ \ {x, y})) 
  (hxy2 : {x, y} ⊆ I) : {x, y} = I :=
begin
  by_contra,
  have h5 := indep.subset hI (diff_subset I {x, y}),
  have h4 := nonempty_of_ssubset (ssubset_of_ne_of_subset h hxy2),
  rw nonempty_iff_ne_empty at h4,
  
  have M' := matroid_of_module_set,
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
  rw rep.to_submodule' at φ,
  cases foo' φ with φ,
  rw [rk_def, unif_r_eq] at φ,
  { have h8 := card_le_of_subset (φ.subset_nonzero_of_simple U24_simple),
    -- need basis
    have h9 := module.card_fintype (finite_dimensional.fin_basis (zmod 2)
      (span (zmod 2) (φ '' (unif 2 4).E))),
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

lemma excluded_minor_binary_unif24 (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor matroid_in.is_binary M) : iso_minor (unif 2 4) M :=
begin
  -- this comes from hM
  have hME : nontrivial M.E,
    sorry,
  rw nontrivial_coe_sort at hME,
  rw nontrivial_iff_pair_subset at hME,
  obtain ⟨x, ⟨y, ⟨hxy1, hxy2⟩⟩⟩ := hME,
  have h2 := cocircuits_excluded_minor' M hM x y _ _,
  swap,
  apply singleton_subset_iff.1,
  sorry,
  swap,
  apply singleton_subset_iff.1,
  sorry,
  rw excluded_minor_iff at hM,
  have hxyr : (M ⟍ ({x, y} : set α)).is_binary,
    sorry,
  obtain ⟨W, _⟩ := hxyr,
  casesI hxyr_h with a ha,
  casesI ha with b hb,
  casesI hb with φ2,
  have φ := φ2.rep_submodule,
  haveI := φ2.fin_dim_rep,
  --haveI := hxyr_h_w,
  obtain ⟨B, hB⟩ := (M ⟍ ({x, y} : set α)).exists_base,
  /-have hB2 : M.base B,
    rw delete_base_iff at hB,
    rw cocircuit_iff_mem_minimals_compl_nonspanning at h2,
    rw mem_minimals_iff' at h2,
    push_neg at h2,
    simp at h2,
    
    sorry,-/
  let φ' := λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, φ i,
  -- the sorries are for module and finite_dimensional instances,
  -- i think i need to show that we have a finite dimensional rep of M \ {x, y} somehow
  -- but i'm worried about making assumptions 
  have φy : rep (zmod 2) ↥(φ2.to_submodule') (M ⟍ x),
    use (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, φ i),
    intros I hI,
    rw delete_elem at hI,
    have hfundcirc : ∀ (a ∈ (M ⟍ ({x, y} : set α)).E), (M.fund_circuit a B) = 
      ((M ⟍ ({x, y} : set α)).fund_circuit a B),
        sorry,
    by_cases y ∈ I, 
    refine ⟨λ h5, _, λ h5, _⟩,  
    have h4 : ((λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, φ i) ∘ (coe : I → α)) = 
      (λ e : I, (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, φ i) e),
        simp only [eq_self_iff_true],
    rw h4 at h5,
    have h6 : I = insert y ((I \ {y}) : set α),
      sorry,
    rw [h6, indep.insert_indep_iff_of_not_mem],
    sorry,
    have h7 : disjoint (I \ {y}) {y},
      simp only [disjoint_singleton_right, not_mem_diff_singleton, not_false_iff],
    have hIM : (I \ {y}) ⊆ (M ⟍ ({x, y} : set α)).E,
      rw [← union_singleton, union_comm, ← delete_delete, delete_ground],
      apply diff_subset_diff hI (subset.refl _), 
    have h8 : (M ⟍ ({x, y} : set α)).indep (I \ {y}),
      rw ← φ.valid',
      have h4 : (φ.to_fun ∘ (coe : (I \ {y}) → α)) = (λ e : (I \ {y}), φ.to_fun e),
        simp only [eq_self_iff_true],
      rw h4,
      have h10 := linear_independent.injective h5,
      have h11 := linear_independent.image h5,
      have h9 := linear_independent.mono (image_subset 
        (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, φ i) (diff_subset I {y})) h11,
      rw ← linear_independent_image at h9, 
      have h12 : (λ (x_1 : ↥(I \ {y})), ∑ (i : α) in (M.fund_circuit ↑x_1 B ∩ B).to_finset, φ i) = 
        (λ (e : ↥(I \ {y})), φ.to_fun ↑e),
        ext;
        simp only [to_finset_inter, coe_sum, to_fun_eq_coe],
        rw ← mem_sum_basis_zmod2 φ hB.indep _ (hB.mem_cl _ (mem_of_subset_of_mem hIM _)),
        simp only [to_finset_inter, coe_sum], 
        rw hfundcirc x_1 (mem_of_subset_of_mem hIM x_1.2),
        apply x_1.2,
      rw ← h12,
      apply h9,
      apply inj_on.mono (diff_subset I {y}) _,
      have h20 := inj_on_of_injective h10 univ,
      sorry,
      rw [← union_singleton, union_comm, ← delete_delete, delete_ground],
      apply diff_subset_diff hI (subset.refl _),
    rw [← union_singleton, union_comm, ← delete_delete, delete_indep_iff] at h8,
    apply h8.1,
    apply not_mem_diff_singleton,
    sorry,
    have hIM : I ⊆ (M ⟍ ({x, y} : set α)).E, 
      rw [← union_singleton, union_comm, ← delete_delete, delete_ground],
      apply subset_diff_singleton hI h,
    have h4 : (λ (e : α), ∑ (i : α) in (M.fund_circuit e B ∩ B).to_finset, φ i) ∘ (coe : I → α) = 
        (λ (e : I), φ e),
        have h5 : (λ (e : α), ∑ (i : α) in (M.fund_circuit e B ∩ B).to_finset, φ i) ∘ (coe : I → α) =
          (λ (e : I), ∑ (i : α) in (M.fund_circuit e B ∩ B).to_finset, φ i),
          simp only,
        rw h5,
        ext;
        rw ← mem_sum_basis_zmod2 φ hB.indep _ (hB.mem_cl _ (mem_of_subset_of_mem hIM _)),
        rw hfundcirc x_1 (mem_of_subset_of_mem hIM x_1.2),
        apply x_1.2,
    have h7 : (φ.to_fun ∘ (coe : I → α)) = (λ e : I, φ e),
      simp only [to_fun_eq_coe],
    rw [h4, ← h7, φ.valid' _ hIM, ← union_singleton, union_comm, ← delete_delete],
    refine ⟨λ hI2, hI2.of_delete, λ hI2, delete_indep_iff.2 ⟨hI2, disjoint_singleton_right.2 h⟩⟩,

    have φy' := rep_of_matroid_of_module_func (zmod 2) (φ2.to_submodule') 
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, φ i) (M.E \ {x}),
    have hMM'x : (M ⟍ x) = (matroid_of_module_func (zmod 2) (φ2.to_submodule')
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, φ i) (M.E \ {x})),
    apply eq_of_indep_iff_indep_forall,
    simp_rw [delete_elem, delete_ground],
    rw ground_matroid_of_module_func,
    intros I hI,
    rw [← φy.valid' I hI, ← φy'.valid' I _],
    have hφ : φy.to_fun = (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, φ i),
      simp,
      funext,
    /-refine ⟨λ hI2, _, λ hI2, _⟩,
    refine ⟨⟨_, sorry⟩, sorry,⟩,
    by_cases y ∈ I,
      sorry,
      have h3 : (M ⟍ ({x, y} : set α)).indep I,
      have h4 : disjoint I {y},
        sorry,
      have h2 := delete_indep_iff.2 ⟨hI2, h4⟩,
      rw [delete_elem, delete_delete, union_comm, union_singleton] at h2,
      apply h2,
      have h5 := mem_sum_basis_zmod2 φ hB.indep,
      rw ← φ.valid' I at h3,
      simp at h3,
      have h4 : (φ ∘ (coe : I → α)) = (λ e : I, φ e),
        simp only [eq_self_iff_true],
      rw h4 at h3,
      have h6 : (λ (e : ↥I), φ ↑e) = (λ (x_1 : ↥I), ((M ⟍ ({x, y} : set α)).fund_circuit ↑x_1 B ∩ B).to_finset.sum φ),
        ext;
        rw ← h5,
        simp, 
        refine ⟨_, _⟩,
        sorry,
        push_neg,
        sorry,
      rw ← h6,
      apply h3, 
    sorry,
  have hMM'y : (M ⟍ y) = (M' ⟍ y),
    sorry,
  have hMM' : M ≠ M',
    -- M nonbinary, M' binary
    sorry,
  have hMM'3 : M.E = M'.E,  
    -- this will be annoying to prove
    sorry,
  have hMM'2 := (eq_of_indep_iff_indep_forall hMM'3).mt hMM',
  push_neg at hMM'2,
  obtain ⟨I, ⟨hI1, hI2⟩⟩ := hMM'2,
  rw not_iff at hI2,
  -- have to think about how to set up minimal and WLOG arguments here
  let Z := set α,

  sorry,-/
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


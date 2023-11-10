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
-- def is_representable (𝔽 : Type*) [field 𝔽] (M : matroid_in α) : Prop := 
--   ∃ (W : Type) (hW : add_comm_group W) 
--   (hFW : @module 𝔽 W _ (@add_comm_group.to_add_comm_monoid W hW)), nonempty (@rep _ 𝔽 W _ hW hFW M)

def is_representable (𝔽 : Type*) [field 𝔽] (M : matroid_in α) : Prop := 
  ∃ (B : set α) (hB : M.base B), nonempty (rep 𝔽 (B →₀ 𝔽) M)

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
  convert hst2.disjoint_span_image (show disjoint (coe ⁻¹' s) (coe ⁻¹' t), from _), 
  { rw [eq_comm, image_preimage_eq_iff, subtype.range_coe], apply subset_union_left },
  { rw [eq_comm, image_preimage_eq_iff, subtype.range_coe], apply subset_union_right },
  rw [set.disjoint_iff, subset_empty_iff] at ⊢ hst,
  rw [← preimage_inter, hst, preimage_empty],
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
  apply mem_span_rep φ x }

/-lemma cl_subset_span_set (φ : rep 𝔽 W M) {X : set α} (hX : X ⊆ M.E) : 
  φ '' M.cl X ⊆ span 𝔽 (φ '' X) :=
by { rintros _ ⟨x, ⟨hx, rfl⟩⟩, apply mem_span_cl φ hX hx, }-/

--lemma rep_of_minor (φ : rep 𝔽 W M) (N : matroid_in α) (hNM : N ≤ matroid_in.to_matroid_in M) : 

end rep


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

/-- A representation over *any* module certifies representability-/
lemma is_representable_of_rep {W : Type*} [add_comm_group W] [module 𝔽 W] (φ : rep 𝔽 W M) : 
    is_representable 𝔽 M := 
  begin
    obtain ⟨B, hB⟩ := M.exists_base, 
    exact ⟨B, hB, ⟨std_rep φ hB⟩⟩, 
  end

variables [fintype α]

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

-- modify to disjoint union of circuits for iff?
lemma rep.circuit (φ : rep 𝔽 W M) {C : set α} (hMC : M.circuit C) : 
  ∃ f : α →₀ 𝔽, (f.support : set α) = C ∧ finsupp.total α W 𝔽 φ f = 0 ∧ f ≠ 0 :=
begin
  obtain ⟨f, ⟨hfssup, ⟨hftot, hfne0⟩⟩⟩ := 
    linear_dependent_comp_subtype'.1 ((φ.valid'' hMC.subset_ground).1.mt (not_indep_iff.2 hMC.dep)),
  refine ⟨f, ⟨_, ⟨hftot, hfne0⟩⟩⟩,
  apply subset.antisymm_iff.2 ⟨hfssup, λ x hx, _⟩,
  by_contra,
  apply (φ.valid'' (subset.trans (diff_subset _ _) hMC.subset_ground)).2.mt 
    (linear_dependent_comp_subtype'.2 ⟨f, ⟨subset_diff_singleton hfssup h, ⟨hftot, hfne0⟩⟩⟩),
  apply hMC.diff_singleton_indep hx,
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

lemma add_coloop_ground (M : matroid_in α) {f : α} (hf : f ∉ M.E) : 
  (add_coloop M hf).E = M.E ∪ {f} := by refl

-- i think we need e to be a cocircuit of M
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

lemma series_pair_mem_circuit (x y : α) (C : set α) (hMC : M.circuit C) (hMxy : M.cocircuit {x, y}) 
  : x ∈ C ↔ y ∈ C :=
begin
  refine ⟨_, _⟩,
  sorry,
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

-- write congr lemma
def rep_of_congr {M M' : matroid_in α} (φ : rep 𝔽 W M) (h : M = M') : rep 𝔽 W M' := 
{ to_fun := φ.to_fun,
  valid' := λ I hI, by { rw ← (eq_iff_indep_iff_indep_forall.1 h).1 at hI, 
    rw ← (eq_iff_indep_iff_indep_forall.1 h).2, apply φ.valid' I hI, apply hI },
  support := λ e he, by { rw ← (eq_iff_indep_iff_indep_forall.1 h).1 at he, apply φ.support e he } }

-- write refl lemma for the above
lemma rep_eq_of_congr {M M' : matroid_in α} (φ : rep 𝔽 W M) (h : M = M') : 
  (φ : α → W) = (rep_of_congr φ h) := rfl

lemma std_rep_eq_of_congr {M M' : matroid_in α} (φ : rep 𝔽 W M) (h : M = M') {B : set α} 
  (hMB : M.base B) (hMB' : M'.base B) : 
  ((std_rep φ hMB) : α → B →₀ 𝔽) = (std_rep (rep_of_congr φ h) hMB' :  α → B →₀ 𝔽)  := rfl

lemma delete_elem_eq_of_binary_right {B : set α} {x y : α} (hBxy : (M ⟍ ({x, y} : set α)).base B)
  (hBx : (M ⟍ y).base B) (hB : M.base B)
  [module (zmod 2) W] (φ : rep (zmod 2) W (M ⟍ ({x, y} : set α))) {Wy : Type*} [add_comm_group Wy]
  [module (zmod 2) Wy]
  (φx : rep (zmod 2) Wy (M ⟍ y)) : (M ⟍ y) = 
  (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
    (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (std_rep φ hBxy) i) M.E) ⟍ y :=
begin
  have hMxyyx : M ⟍ ({x, y} : set α) = M ⟍ ({y, x} : set α),
    rw [← union_singleton, union_comm, union_singleton],
  have hByx := hBxy,
  rw [← union_singleton, union_comm, union_singleton] at hByx,
  rw std_rep_eq_of_congr φ hMxyyx hBxy hByx,
  apply delete_elem_eq_of_binary hByx hBx hB (rep_of_congr φ hMxyyx) φx,
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
import analysis.inner_product_space.gram_schmidt_ortho
import data.zmod.basic
import linear_algebra.basis
import linear_algebra.linear_independent
import mathlib.ncard
import ..constructions.basic
import matroid.matroid_in.minor
import ..simple

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
variables {E 𝔽 : Type*} [fintype E] {M : matroid E} {I B : set E} {x : E}
variables {W W' : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] [add_comm_group W'] [module 𝔽 W'] 
-- we should have semiring 𝔽 by default, idk why it doesn't see it
-- why did we have finite E and not fintype E?

namespace matroid

/-- A `𝔽`-matroid representation is a map from the base of the matroid to `ι → 𝔽` such that a set -/
/-structure rep (𝔽 : Type*) [field 𝔽] (M : matroid E) (ι : Type) :=
(to_fun : E → ι → 𝔽)
(valid' : ∀ I : set E, linear_independent 𝔽 (λ e : I, to_fun e) ↔ M.indep I)

/-- `M` is `𝔽`-representable if it has an `𝔽`-representation. -/
def is_representable (𝔽 : Type*) [field 𝔽] (M : matroid E) : Prop := ∃ (ι : Type), nonempty (rep 𝔽 M ι)-/

structure rep (𝔽 W : Type*) [field 𝔽] [add_comm_group W] [module 𝔽 W] (M : matroid E) :=
(to_fun : E → W)
(valid' : ∀ (I : set E), linear_independent 𝔽 (λ (e : I), to_fun e) ↔ M.indep I)

/-- `M` is `𝔽`-representable if it has an `𝔽`-representation. -/
def is_representable (𝔽 : Type*) [field 𝔽] (M : matroid E) : Prop := 
  ∃ (W : Type) (hW : add_comm_group W) (hFW : @module 𝔽 W _ (@add_comm_group.to_add_comm_monoid W hW)), nonempty (@rep _ _ 𝔽 W _ hW hFW M)

namespace rep

instance fun_like : fun_like (rep 𝔽 W M) E (λ _, W) :=
{ coe := to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

instance : has_coe_to_fun (rep 𝔽 W M) (λ _, E → W) := fun_like.has_coe_to_fun

lemma valid (φ : rep 𝔽 W M) : linear_independent 𝔽 (λ e : I, φ e) ↔ M.indep I := φ.valid' _

protected lemma is_representable {W : Type} [add_comm_group W] [module 𝔽 W] (φ : rep 𝔽 W M) : 
  is_representable 𝔽 M := ⟨W, ⟨_, ⟨_, ⟨φ⟩⟩⟩⟩

lemma inj_on_of_indep (φ : rep 𝔽 W M) (hI : M.indep I) : inj_on φ I :=
inj_on_iff_injective.2 ((φ.valid' I).2 hI).injective

@[simp] lemma to_fun_eq_coe (φ : rep 𝔽 W M) : φ.to_fun = (φ : E → W)  := by { ext, refl }

lemma linear_independent_iff_coe (φ : rep 𝔽 W M) (hI : M.indep I) :
  linear_independent 𝔽 (λ e : I, φ e) ↔ linear_independent 𝔽 (coe : φ '' I → W) :=
linear_independent_image $ inj_on_of_indep _ hI

def to_submodule (φ : rep 𝔽 W M) : submodule 𝔽 W := span 𝔽 (set.range φ)

lemma mem_to_submodule (φ : rep 𝔽 W M) (x : E) : φ x ∈ rep.to_submodule φ :=
by { rw [rep.to_submodule], refine subset_span _, simp }

def rep_submodule (φ : rep 𝔽 W M) : rep 𝔽 (rep.to_submodule φ) M := 
{ to_fun := λ x, ⟨φ x, rep.mem_to_submodule φ x⟩,
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
{ to_fun := λ x, e ⟨φ x, rep.mem_to_submodule φ x⟩,
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
((φ.valid' {x}).2 hx.indep).ne_zero (⟨x, mem_singleton _⟩ : ({x} : set E))

lemma ne_zero_of_loopless (φ : rep 𝔽 W M) (hl : loopless M) (x : E) : φ x ≠ 0 :=
ne_zero_of_nonloop _ $ hl _

lemma injective_of_simple (φ : rep 𝔽 W M) (hs : simple M) : injective φ :=
injective_iff_forall_inj_on_pair.2 $ λ a b, inj_on_of_indep _ $ hs _ _

lemma subset_nonzero_of_simple (φ : rep 𝔽 W M) (hs : simple M) :
  range φ ⊆ span 𝔽 (range φ) \ {0} :=
begin
  refine subset_diff.2 ⟨subset_span, disjoint_left.2 _⟩,
  rintro _ ⟨x, rfl⟩,
  exact ne_zero_of_loopless _ hs.loopless _,
end

lemma of_base (φ : rep 𝔽 W M) {B : set E} (hB : M.base B) (e : E) : φ e ∈ span 𝔽 (φ '' B) :=
begin
  by_cases e ∈ B,
  { exact subset_span (mem_image_of_mem _ h) },
  have h2 : ¬ linear_independent 𝔽 (λ x : insert e B, φ x) := (φ.valid' (insert e B)).not.2 (hB.dep_of_insert h),
  contrapose! h2,
  exact (linear_independent_insert' h).2 ⟨(φ.valid' B).2 hB.indep, h2⟩,
end

lemma of_basis (φ : rep 𝔽 W M) {X I : set E} (hI : M.basis I X) {e : E} (he : e ∈ X): φ e ∈ span 𝔽 (φ '' I) :=
begin
  by_cases e ∈ I, 
  { apply subset_span (mem_image_of_mem _ h) },
  have h2 : ¬ linear_independent 𝔽 (λ x : insert e I, φ x) := (φ.valid' (insert e I)).not.2 (hI.insert_dep (mem_diff_of_mem he h)),
  contrapose! h2,
  apply (linear_independent_insert' h).2 ⟨(φ.valid' I).2 hI.indep, h2⟩,
end

lemma span_base (φ : rep 𝔽 W M) (hB : M.base B) :
  span 𝔽 (φ '' B) = span 𝔽 (range φ) :=
begin
  refine (span_mono $ image_subset_range _ _).antisymm (span_le.2 _),
  rintro _ ⟨x, rfl⟩,
  exact of_base _ hB _,
end

lemma span_basis (φ : rep 𝔽 W M) {X I : set E} (hI : M.basis I X) : 
  span 𝔽 (φ '' I) = span 𝔽 (φ '' X) :=
begin
  refine (span_mono $ image_subset _ (basis.subset hI)).antisymm (span_le.2 _),
  rintros x ⟨y, ⟨hy1, hy2⟩⟩,
  rw ← hy2, 
  apply of_basis φ hI hy1,
end

lemma basis_of_base (φ : rep 𝔽 W M) {B : set E} (hB : M.base B) :
  _root_.basis B 𝔽 (span 𝔽 (range φ)) :=
by { rw [←span_base _ hB, image_eq_range], exact basis.span ((φ.valid' B).2 hB.indep) }

lemma base_of_basis (φ : rep 𝔽 W M) {B : set E} (hB : _root_.basis B 𝔽 (span 𝔽 (range φ))) : 
  M.base B :=
begin
  sorry,
end

instance fin_dim_rep (φ : rep 𝔽 W M) [finite E] [fintype 𝔽] : finite_dimensional 𝔽 (span 𝔽 (set.range φ)) :=
begin
  cases M.exists_base with B hB,
  apply finite_dimensional.of_finite_basis (basis_of_base φ hB) (base.finite hB),
end

@[simp] lemma mem_span_rep (φ : rep 𝔽 W M) : ∀ (x : E), φ x ∈ (span 𝔽 (range ⇑φ)) := 
  λ x, by { apply mem_of_subset_of_mem (@subset_span 𝔽 _ _ _ _ (range ⇑φ)) (mem_range_self x) }

lemma dual_rep_of_rep (φ : rep 𝔽 W M) [fintype 𝔽] : rep 𝔽 (module.dual 𝔽 W) M﹡ := 
{ to_fun := λ (e : E), subspace.dual_lift (span 𝔽 (range ⇑φ)) 
  (basis.to_dual (finite_dimensional.fin_basis 𝔽 (span 𝔽 (set.range φ))) 
  ⟨φ e, mem_span_rep _ e⟩),
  valid' := λ I, 
    begin
      refine ⟨λ h, _, λ h, _⟩,
      sorry,  
      sorry,
    end }

namespace matroid_in

structure rep (𝔽 W : Type*) [field 𝔽] [add_comm_group W] [module 𝔽 W] (M : matroid_in E) :=
(to_fun : E → W)
(valid' : ∀ (I ⊆ M.ground), linear_independent 𝔽 (λ (e : I), to_fun e) ↔ M.indep I)

/-- `M` is `𝔽`-representable if it has an `𝔽`-representation. -/
def is_representable (𝔽 : Type*) [field 𝔽] (M : matroid_in E) : Prop := 
  ∃ (W : Type) (hW : add_comm_group W) (hFW : @module 𝔽 W _ (@add_comm_group.to_add_comm_monoid W hW)), nonempty (@rep _ _ 𝔽 W _ hW hFW M)
end matroid_in

def rep_of_del (N : matroid_in E) (φ : matroid_in.rep 𝔽 W N) (D : set E) : matroid_in.rep 𝔽 W (N ⟍ D) := 
{ to_fun := φ.to_fun,
  valid' := λ I hI, ⟨λ h, matroid_in.indep.delete_indep 
  ((φ.valid' I (subset_trans hI (diff_subset N.E D))).1 h) ((subset_diff.1 hI).2), 
  λ h, (φ.valid' I (subset_trans hI (diff_subset N.E D))).2 (matroid_in.delete_indep_iff.1 h).1⟩ }

theorem finrank_span_set_eq_ncard {K V : Type*} [division_ring K] [add_comm_group V] 
  [module K V] (s : set V) (hs : linear_independent K (coe : s → V)) :
finite_dimensional.finrank K (submodule.span K s) = s.ncard :=
begin
  sorry, 
end 

lemma of_r (φ : rep 𝔽 W M) (X : set E) : finite_dimensional.finrank 𝔽 (span 𝔽 (φ '' X)) = M.r X :=
begin
  obtain ⟨I, hI⟩ := M.exists_basis X, 
  rw [←hI.card, ←φ.span_basis hI, finrank_span_set_eq_ncard, 
    ncard_image_of_inj_on (inj_on_of_indep _ hI.indep) ], 
  exact linear_independent.image (φ.valid.mpr hI.indep), 
end

lemma of_rank (φ : rep 𝔽 W M) : finite_dimensional.finrank 𝔽 (span 𝔽 (range φ)) = M.rk :=
by { convert of_r φ univ; simp }

lemma cl_subset_span_rep (φ : rep 𝔽 W M) (X : set E): φ '' M.cl X ⊆ span 𝔽 (φ '' X) :=
begin
  cases M.exists_basis X with I hI,
  rw ← span_basis _ hI, 
  sorry,
end

end rep

variables {ι : Type}

structure rep' (𝔽 : Type*) [field 𝔽] (M : matroid E) (ι : Type) :=
(to_fun : E → ι → 𝔽)
(valid' : ∀ I : set E, linear_independent 𝔽 (λ e : I, to_fun e) ↔ M.indep I)

namespace rep'

lemma valid (φ : rep' 𝔽 M ι) : linear_independent 𝔽 (λ e : I, φ.to_fun e) ↔ M.indep I := φ.valid' _

instance fun_like : fun_like (rep' 𝔽 M ι) E (λ _, ι → 𝔽) :=
{ coe := rep'.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

instance : has_coe_to_fun (rep' 𝔽 M ι) (λ _, E → ι → 𝔽) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe' (φ : rep' 𝔽 M ι) : φ.to_fun = (φ : E → ι → 𝔽)  := by { ext, refl }

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

lemma of_base' (φ : rep' 𝔽 M ι) {B : set E} (hB : M.base B) (e : E) : φ e ∈ span 𝔽 (φ '' B) :=
begin
  by_cases e ∈ B,
  { exact subset_span (mem_image_of_mem _ h) },
  have h2 : ¬ linear_independent 𝔽 (λ x : insert e B, φ x) := φ.valid.not.2 (hB.dep_of_insert h),
  contrapose! h2,
  exact (linear_independent_insert' h).2 ⟨φ.valid.2 hB.indep, h2⟩,
end

lemma span_base' (φ : rep' 𝔽 M ι) (hB : M.base B) :
  span 𝔽 (φ '' B) = span 𝔽 (range φ) :=
begin
  refine (span_mono $ image_subset_range _ _).antisymm (span_le.2 _),
  rintro _ ⟨x, rfl⟩,
  exact of_base' _ hB _,
end

lemma basis_of_base' (φ : rep' 𝔽 M ι) {B : set E} (hB : M.base B) :
  _root_.basis B 𝔽 (span 𝔽 (range φ)) :=
by { rw [←span_base' _ hB, image_eq_range], exact basis.span ((rep'.valid' φ B).2 hB.indep) }

instance fin_dim_rep' (φ : rep' 𝔽 M ι) [finite E] [fintype 𝔽] : finite_dimensional 𝔽 (span 𝔽 (set.range φ)) :=
begin
  cases M.exists_base with B hB,
  apply finite_dimensional.of_finite_basis (basis_of_base' φ hB) (base.finite hB),
end

lemma of_rank' (φ : rep' 𝔽 M ι) [fintype 𝔽] :
  finite_dimensional.finrank 𝔽 (span 𝔽 (range φ)) = M.rk :=
begin
  cases M.exists_base with B hB,
  -- need basis for this to work
  have h3 := finite_dimensional.fin_basis 𝔽 (span 𝔽 (set.range φ)),
  rw [←span_base' φ hB, finrank_span_set_eq_card (φ '' B)],
  have h6 : (⇑φ '' B).to_finset.card = B.to_finset.card,
  { simp_rw to_finset_card,
    rw ← card_image_of_inj_on (inj_on_of_indep' φ (base.indep hB)) },
  rw h6,
  simp only [← base.card hB, ncard_def, to_finset_card, nat.card_eq_fintype_card],
  have h8 : linear_independent 𝔽 (λ (x : B), φ (x : E)),
  rw [← to_fun_eq_coe', rep'.valid φ],
  apply hB.indep,
  apply linear_independent.image_of_comp B φ coe h8,
end

end rep'

namespace rep

lemma foo (φ' : rep 𝔽 W M) [fintype 𝔽] [finite_dimensional 𝔽 W] :
  nonempty (rep' 𝔽 M (fin M.rk))  :=
begin
  have φ := rep'.rep'_of_rep (φ'.rep_submodule) (of_rank φ'),
  have h1 := eq.symm (@finite_dimensional.finrank_fin_fun 𝔽 _ (M.rk)),
  rw [← rep'.of_rank' φ, ← finite_dimensional.nonempty_linear_equiv_iff_finrank_eq] at h1, 
  cases h1 with l,
  have h3 := λ (x : E), mem_of_subset_of_mem (@subset_span 𝔽 _ _ _ _ (range ⇑φ)) (mem_range_self x),
  use φ,
end

lemma foo' (φ : rep 𝔽 W M) [fintype 𝔽] [finite_dimensional 𝔽 W] :
  nonempty (rep 𝔽 (fin M.rk → 𝔽) M) :=
begin
  have h := foo φ,
  cases h with φ,
  have φ' := rep'.rep_of_rep' φ,
  use φ',
end

/- A matroid is binary if it has a `GF(2)`-representation -/
@[reducible, inline] def matroid.is_binary (M : matroid E) := M.is_representable (zmod 2)

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
  rw [matroid.is_binary, is_representable],
  { refine ⟨(fin 2 → zmod 2), ⟨_, ⟨_, ⟨φ⟩⟩⟩⟩ },
  intros I,
  have h3 := @finrank_fin_fun (zmod 2) _ 2,
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

-- i think we need something that says if a matroid is finite it has 
-- a finite dimensional representation

-- this doesn't have sorry's but it relies on foo and U24_simple which do
lemma U24_nonbinary : ¬ (unif 2 4).is_binary :=
begin
  by_contra h2,
  rw [matroid.is_binary, is_representable] at h2,
  rcases h2 with ⟨W, ⟨hW, ⟨hM, ⟨φ'⟩⟩⟩⟩,
  haveI := zmod.fintype 2,
  have φ := rep.rep_submodule φ',
  rw rep.to_submodule at φ,
  cases foo' φ with φ,
  rw [unif_on_rk] at φ,
  { have h8 := card_le_of_subset (φ.subset_nonzero_of_simple U24_simple),
    -- need basis
    have h9 := module.card_fintype (finite_dimensional.fin_basis (zmod 2)
      (span (zmod 2) (range φ))),
    rw [rep.of_rank, unif_on_rk] at h9,
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

end rep

-- lemma foo (e f : E) (hne : e ≠ f) (h : M.r {e,f} = 1) :

end matroid

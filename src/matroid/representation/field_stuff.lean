import data.finset.basic
import combinatorics.simple_graph.basic
import algebra.module.submodule.basic
import linear_algebra.finite_dimensional
import linear_algebra.finrank
import linear_algebra.finsupp
import data.setoid.partition
import linear_algebra.projective_space.basic
import linear_algebra.span

universes u v w

open finset

variables {α : Type u} [decidable_eq α]



variables [fintype α]


-- any d-dimensional vector space over GF(q) has exactly (q^d-1) / (q - 1) 1-dimensional subspaces
-- do i count it as fintype.card or do i try to do set of subspaces?
-- fintype.card {x : subspace α V | findim x = 1} = (q^d-1) / (q - 1)
variables (K : Type u) (V : Type v) [field K] [add_comm_group V] [module K V] [fintype K]
variables [finite_dimensional K V] (q d : ℕ)
--variables [fintype (module K V)]
variables [fintype {S : submodule K V | finite_dimensional.finrank K S = 1}]
-- size of K should be q
-- we get [fintype V] from finite_dimensional K V and fintype K

/-instance fintype_submodules [fintype V] : fintype (submodule K V) :=
begin
  rw submodule,
  sorry,
end-/

/-instance fintype_subspaces [fintype V] : fintype {S : submodule K V | finite_dimensional.finrank K S = 1} :=
begin
  simp,
  --have h : subtype ↑(powerset (@finset.univ V _)),
  apply subtype,
  sorry,
end-/



-- lemma num_basis_vectors :

-- use basis_unique, basis_singleton

-- some kind of lemma stating that if c ⬝ x = d ⬝ y then their respective subspaces are the same
-- do we have some kind of map from basis to subspace?
-- i think the notation here is K ∙ x = K ∙ y
-- this is just span_singleton_eq_span_singleton
lemma subspace_eq_of_basis_scalar (x y : V) (b : K) (h2 : b ≠ 0) :
  x = (b • y) → (K ∙ x) = (K ∙ y) :=
begin
  intros h,
  ext v;
  simp_rw [submodule.mem_span_singleton],
  --refine ⟨λ ⟨n, hn⟩, _, λ n, _⟩,
  split,
  rintros ⟨n, hn⟩,
  rw [← hn, h, smul_smul],
  use (n * b),
  rintros ⟨n, hn⟩,
  use (n * b⁻¹),
  rw [← hn, h, smul_smul, mul_assoc, inv_mul_cancel h2, mul_one],
end

lemma mem_span_singleton_smul (a : K) (x : V) : a • x ∈ K ∙ x :=
begin
  apply submodule.mem_span_singleton.2,
  use a,
end

open_locale classical

-- only true if V & K nontrivial
-- use this for principal of inclusion-exclusion?
lemma sUnion_dimone_univ (hV : nontrivial V) :
  set.sUnion {x : set V | ∃ (m : submodule K V), x = m.carrier ∧ finite_dimensional.finrank K m = 1} = set.univ :=
begin
  ext;
  split,
  { intros h,
    simp at h },
  simp,
  by_cases h : x ≠ 0,
  { use (K ∙ x).carrier,
    refine ⟨_, submodule.mem_span_singleton_self x⟩,
    use (K ∙ x),
    refine ⟨rfl, finrank_span_singleton h⟩ },
  push_neg at h,
  cases ((nontrivial_iff_exists_ne 0).1 hV) with v hv,
  use (K ∙ v).carrier,
  rw h,
  refine ⟨_, (submodule.mem_carrier (K ∙ v)).2 (submodule.zero_mem (K ∙ v))⟩,
  use (K ∙ v),
  refine ⟨rfl, finrank_span_singleton hv⟩,
end

variables {ι : Type*}
lemma nonzero_elems [fintype ι] (b : basis ι K V) [fintype V] :
 ({0}ᶜ : finset V).card = fintype.card K ^ fintype.card ι - 1 :=
begin
  rw [← module.card_fintype b, ← card_singleton (0 : V), card_compl],
end

variables {K V}
def subspace_rem_zero (S : submodule K V) : set V := S \ {0}

noncomputable def subspace_rem_zero_finset [fintype V] (S : submodule K V) : finset V := (subspace_rem_zero S).to_finset

-- i don't know why the lemma doesn't see the instances
variables [nontrivial K] (p : submodule K V) [no_zero_smul_divisors K p]
lemma span_singleton_eq_iff_mem_dim_one (m : V) (hk : m ≠ 0) : (K ∙ m) = p ↔ m ∈ p ∧ finite_dimensional.finrank K p = 1 :=
begin
  refine ⟨λ h2, _, λ h2, _⟩,
  { rw ← h2,
    refine ⟨submodule.mem_span_singleton_self m, finrank_span_singleton hk⟩ },
  ext;
  refine ⟨λ h3, _, λ h4, _⟩,
  { simp only [submodule.mem_span, set.singleton_subset_iff, set_like.mem_coe] at h3,
    apply h3 p h2.1 },
  have h6 : (⟨m, h2.1⟩ : p) ≠ 0,
  { simp only [ne.def, submodule.mk_eq_zero],
    exact hk },
  have hbas : nonempty (basis (fin 1) K p),
  { use (finite_dimensional.basis_singleton (fin 1) h2.2) ⟨m, h2.1⟩ h6 },
  rcases (basis.basis_singleton_iff (fin 1)).1 hbas with ⟨a, ⟨ha, hb⟩⟩,
  cases hb ⟨x, h4⟩ with r hr,
  cases hb ⟨m, h2.1⟩ with s hs,
  by_cases x = 0,
  simp only [h, submodule.zero_mem],
  have h16 : s ≠ 0,
  { rw ← hs at h6,
    exact (smul_ne_zero_iff.1 h6).1 },
  have h17 : m = s • ↑a,
  { rw [← submodule.coe_smul, hs, submodule.coe_mk] },
  rw [subspace_eq_of_basis_scalar K V m a s h16 h17, submodule.mem_span_singleton],
  use r,
  rw [← submodule.coe_mk x h4, ← hr, submodule.coe_smul],
end

noncomputable def of_span [fintype V] : finpartition ({0}ᶜ : finset V) :=
{ parts := finset.image subspace_rem_zero_finset ({S : submodule K V | finite_dimensional.finrank K S = 1}.to_finset),
  sup_indep := λ S h a ha hna,
    begin
      simp only [mem_image, set.mem_to_finset, set.mem_set_of_eq, exists_prop] at ha,
      rcases ha with ⟨H, ⟨hH1, hH2⟩⟩,
      simp_rw [disjoint_iff_ne, mem_sup],
      rintros x hx y ⟨Y, ⟨hY1, hY2⟩⟩,
      have h2 := mem_of_subset h hY1,
      simp only [mem_image, set.mem_to_finset, set.mem_set_of_eq, exists_prop] at h2,
      rcases h2 with ⟨P, ⟨hP1, hP2⟩⟩,
      have hxH : x ∈ H,
      { simp only [← hH2, subspace_rem_zero_finset, subspace_rem_zero, set.to_finset_diff,
          id.def, mem_sdiff, set.mem_to_finset, set_like.mem_coe, set.mem_singleton_iff] at hx,
        exact hx.1 },
      have hyP : y ∈ P,
      { simp only [id.def, ← hP2, subspace_rem_zero_finset, subspace_rem_zero,
          set.to_finset_diff, mem_sdiff, set.mem_to_finset, set_like.mem_coe, set.mem_singleton_iff] at hY2,
        exact hY2.1 },
      have hx0 : x ≠ 0,
      { simp only [← hH2, subspace_rem_zero_finset, subspace_rem_zero,
          set.to_finset_diff, id.def, mem_sdiff, set.mem_to_finset,
          set_like.mem_coe, set.mem_singleton_iff] at hx,
        exact hx.2 },
      by_contra hxy,
      rw ← hxy at hyP,
      have hHP : H = P,
      { rw [← (span_singleton_eq_iff_mem_dim_one H x hx0).2 ⟨hxH, hH1⟩, ← (span_singleton_eq_iff_mem_dim_one P x hx0).2 ⟨hyP, hP1⟩] },
      have haY : a = Y,
      { rw [← hP2, ← hHP, ← hH2] },
      rw ← haY at hY1,
      apply hna hY1,
    end,
  sup_parts :=
    begin
      ext a;
      simp only [mem_sup, mem_compl, mem_singleton],
      refine ⟨λ h, _, λ h, _⟩,
      { rcases h with ⟨f, ⟨h1, h2⟩⟩,
        rw mem_image at h1,
        rcases h1 with ⟨S, ⟨h4, h5⟩⟩,
        rw [subspace_rem_zero_finset, subspace_rem_zero] at h5,
        simp only [← h5, set.to_finset_diff, id.def, mem_sdiff, set.mem_to_finset,
          set_like.mem_coe, set.mem_singleton_iff] at h2,
        exact h2.2 },
      { use subspace_rem_zero_finset (K ∙ a),
        simp only [mem_image, set.mem_to_finset, set.mem_set_of_eq, exists_prop, id.def],
        refine ⟨_, _⟩,
        { use (K ∙ a),
          refine ⟨_, rfl⟩,
          rw ← finrank_span_singleton h },
        rw [subspace_rem_zero_finset, subspace_rem_zero, set.mem_to_finset,
          set.mem_diff, set_like.mem_coe, set.mem_singleton_iff],
        exact ⟨submodule.mem_span_singleton_self a, h⟩ },
    end,
  not_bot_mem :=
    begin
      by_contra,
      simp at h,
      rcases h with ⟨a, ⟨ha1, ha2⟩⟩,
      simp only [subspace_rem_zero_finset, subspace_rem_zero, set.to_finset_diff,
        sdiff_eq_empty_iff_subset, set.to_finset_subset, set.coe_to_finset,
        set.subset_singleton_iff, set_like.mem_coe] at ha2,
      have h2 : finite_dimensional.finrank K a = 0,
      { rw finrank_zero_iff_forall_zero,
        intros x,
        specialize ha2 x x.2,
        simp only [submodule.coe_eq_zero] at ha2,
        apply ha2 },
      apply nat.one_ne_zero,
      rw [← ha1, ← h2],
    end }

lemma card_subspace_rem_zero [fintype V] [nontrivial V] :
  (∀ (x : finset V), x ∈ finset.image subspace_rem_zero_finset ({S : submodule K V | finite_dimensional.finrank K S = 1}.to_finset) → finset.card x = (fintype.card K) - 1) :=
begin
  simp_rw [mem_image, set.mem_to_finset, set.mem_set_of_eq,
    subspace_rem_zero_finset, subspace_rem_zero],
  rintros x ⟨h, ⟨ha, hb⟩⟩,
  have h6 : 0 < finite_dimensional.finrank K ↥h,
  { simp only [ha, nat.lt_one_iff] },
  haveI := finite_dimensional.finrank_pos_iff.1 h6,
  cases (exists_ne (0 : h)) with y hy,
  have hy' : y.1 ≠ 0,
  { simp only [subtype.val_eq_coe, ne.def, submodule.coe_eq_zero],
    exact hy },
  have h9 := linear_equiv.to_span_nonzero_singleton K V y.1 hy',
  have h13 : nonempty (K ≃ (submodule.span K {y.1})),
  { use (equiv.of_bijective h9.to_equiv h9.to_equiv.bijective) },
  rw [← hb, ← (span_singleton_eq_iff_mem_dim_one h y.1 hy').2 ⟨y.2, ha⟩,
    set.to_finset_diff, card_sdiff, set.to_finset_card],
  simp only [set_like.coe_sort_coe, ← fintype.card_eq.2 h13,
    set.to_finset_card, set.card_singleton],
  simp only [set.to_finset_subset, set.coe_to_finset,
    set.singleton_subset_iff, set_like.mem_coe, submodule.zero_mem],
end

lemma num_subspaces_dim_one [nontrivial V] :
  fintype.card {S : subspace K V | finite_dimensional.finrank K S = 1} * ((fintype.card K) - 1) = (fintype.card K) ^ (finite_dimensional.finrank K V) - 1 :=
begin
  haveI := module.fintype_of_fintype (finite_dimensional.fin_basis K V), -- this part is necessary for fintype V instance

  have h5 := @finpartition.sum_card_parts V _ ({0}ᶜ : finset V) (@of_span K V _ _ _ _ _ _ _ _),
  have h6 : (@of_span K V _ _ _ _ _ _ _ _).parts.sum (λ (i : finset V), i.card) = (@of_span K V _ _ _ _ _ _ _ _).parts.sum (λ (i : finset V), ((fintype.card K) - 1)),
  apply sum_congr rfl,
  { exact λ a ha, card_subspace_rem_zero a ha },

  rw @sum_const _ (finset V) of_span.parts _ ((fintype.card K) - 1) at h6,
  simp at h6,
  rw nonzero_elems K V (finite_dimensional.fin_basis K V) at h5,
  simp at h5,
  rw [← h5, h6],
  simp,
  left,
  rw of_span,
  simp only,
  rw [finset.card_image_of_injective, set.to_finset_card],
  intros a b hg,
  rw [subspace_rem_zero_finset, subspace_rem_zero_finset, subspace_rem_zero,
    subspace_rem_zero, set.to_finset_inj] at hg,
  ext;
  by_cases x ∈ ({0} : set V),
  { simp only [set.mem_singleton_iff] at h,
    rw h,
    refine ⟨λ ha, submodule.zero_mem _, λ hb, submodule.zero_mem _⟩ },
  refine ⟨λ ha, _, λ hb, _⟩,
  { have ha' : x ∈ ↑a,
    apply ha,
    have hm := (set.mem_diff x).2 ⟨ha', h⟩,
    rw [hg, set.mem_diff] at hm,
    apply hm.1 },
  { have hb' : x ∈ ↑b,
    apply hb,
    have hm := (set.mem_diff x).2 ⟨hb', h⟩,
    rw [← hg, set.mem_diff] at hm,
    apply hm.1 },
end

variables [fintype (subspace K V)]
-- for general dimension of the subspace we might be able to set up an induction argument
-- need to show that if S is k-dimensional subspace, there are k (unique?) 1-dimensional subspaces whose closure is S
lemma dim_unique_subspaces [nontrivial V] (S : subspace K V) (h : 0 < finite_dimensional.finrank K S) :
  ∃ (X : set (submodule K V)),
    ∀ (y : submodule K V), y ∈ X → finite_dimensional.finrank K y = 1 ∧
    fintype.card X = finite_dimensional.finrank K S ∧ (Sup X) = S :=
begin
  have B := (finite_dimensional.fin_basis K V),
  /-have M := λ x : (fin (finite_dimensional.finrank K ↥S)), K ∙ B ↑x,
  --have M2 := λ (y : subspace K V), ∃ x : fin (finite_dimensional.finrank K ↥S), (M x) = y.to_submodule,
  have M2 := set.image M (@univ (fin (finite_dimensional.finrank K ↥S)) _),
  use M2,-/
  sorry,
end

import algebra.module.submodule.basic
import combinatorics.simple_graph.basic
import data.finset.basic
import data.setoid.partition
import linear_algebra.finite_dimensional
import linear_algebra.finrank
import linear_algebra.finsupp
import linear_algebra.projective_space.basic
import linear_algebra.span

open finset

universes u v w
variables {α : Type u} [decidable_eq α] [fintype α]

-- any d-dimensional vector space over GF(q) has exactly (q^d-1) / (q - 1) 1-dimensional subspaces
-- do i count it as fintype.card or do i try to do set of subspaces?
-- fintype.card {x : subspace α V | findim x = 1} = (q^d-1) / (q - 1)
variables (K : Type u) (V : Type v) [field K] [add_comm_group V] [module K V] [fintype K]
variables [finite_dimensional K V] (q d : ℕ)
--variables [fintype (module K V)]
-- size of K should be q
-- we get [fintype V] from finite_dimensional K V and fintype K

open_locale classical

variables (K V)

noncomputable def of_span [fintype V] : finpartition ({0}ᶜ : finset V) := 
{ parts := finset.image (λ (x : ({0}ᶜ : finset V)), (K ∙ x.1).carrier.to_finset.erase (0 : V)) 
    (@univ ({0}ᶜ : finset V) _),
  sup_indep := λ S hS X hX hXS, 
    begin
      obtain ⟨a, ⟨ha1, rfl⟩⟩ := mem_image.1 hX,
      simp_rw [disjoint_iff_ne, mem_sup],
      rintros x hxX y ⟨Y, ⟨hy1, hyY⟩⟩,
      obtain ⟨b, ⟨hb1, rfl⟩⟩ := mem_image.1 (mem_of_subset hS hy1),
      simp only [subtype.val_eq_coe] at *,
      simp only [id.def, mem_erase, ne.def, set.mem_to_finset, 
        submodule.mem_carrier, set_like.mem_coe] at hxX hyY,
      by_contra hxy,
      obtain ⟨c, rfl⟩ := submodule.mem_span_singleton.1 hxX.2,
      obtain ⟨d, rfl⟩ := submodule.mem_span_singleton.1 hyY.2,
      have h3 := submodule.span_smul_eq_of_is_unit ({a} : set V) c 
        (units.exists_iff_ne_zero.2 (smul_ne_zero_iff.1 hxX.1).1),
      simp only [set.smul_set_singleton] at h3,
      simp only [← h3, hxy, ← set.smul_set_singleton, submodule.span_smul_eq_of_is_unit 
        ({b} : set V) d (units.exists_iff_ne_zero.2 (smul_ne_zero_iff.1 hyY.1).1)] at hXS,
      apply hXS hy1,
    end,
  sup_parts := 
    begin
      ext b;
      simp only [mem_sup, mem_compl, mem_singleton, mem_image],
      refine ⟨λ h, _, λ h, ⟨(K ∙ b).carrier.to_finset.erase (0 : V), 
          ⟨⟨⟨b, finset.mem_compl.2 (finset.not_mem_singleton.2 h)⟩, ⟨mem_univ ⟨b, 
          finset.mem_compl.2 (finset.not_mem_singleton.2 h)⟩, rfl⟩⟩, mem_erase.2 
          ⟨h, set.mem_to_finset.2 ((submodule.mem_carrier 
          (submodule.span K {b})).2 (set_like.mem_coe.2 (submodule.mem_span_singleton_self b)))⟩⟩⟩⟩,
      { obtain ⟨X, ⟨hXim, hX2⟩⟩ := h,
        obtain ⟨a, ⟨ha, rfl⟩⟩ := hXim,
        simp only [subtype.val_eq_coe, id.def, mem_erase, ne.def, set.mem_to_finset, 
          submodule.mem_carrier, set_like.mem_coe] at hX2,
        apply hX2.1 },
    end,
  not_bot_mem := 
    begin
      by_contra hbot,
      obtain ⟨a, ⟨hauniv, ha2⟩⟩ := mem_image.1 hbot,
      simp only [subtype.val_eq_coe, bot_eq_empty] at ha2,
      rw erase_eq_empty_iff at ha2,
      cases ha2 with hempty hzero,
      { apply set.nonempty_iff_ne_empty.1 (set.nonempty_coe_sort.1 (@nontrivial.to_nonempty _ 
          (@submodule.nontrivial_span_singleton K V _ _ _ _ (finset.not_mem_singleton.1 
          (finset.mem_compl.1 a.2))))),
        simp only [subtype.val_eq_coe, set_like.mem_coe, ← set.to_finset_eq_empty, ← hempty],
        refl },
      { obtain ⟨x, ⟨y, hxy⟩⟩ := (@submodule.nontrivial_span_singleton K V _ _ _ _ 
          (finset.not_mem_singleton.1 (finset.mem_compl.1 a.2))),
        have h2 := (submodule.mem_carrier _).2 x.2,
        have h3 := (submodule.mem_carrier _).2 y.2,
        simp only [subtype.val_eq_coe, ← set.mem_to_finset, hzero, mem_singleton, 
          submodule.coe_eq_zero] at h2 h3,
        apply hxy,
        rw [h2, h3] },
    end }

lemma card_subspace_rem_zero [fintype V] [nontrivial V] (x : ({0}ᶜ : finset V)) : 
  ((K ∙ x.1).carrier.to_finset.erase (0 : V)).card = (fintype.card K) - 1 :=
begin
  rw [finset.card_erase_of_mem (set.mem_to_finset.2 ((submodule.mem_carrier 
    (submodule.span K {x.val})).2 (set_like.mem_coe.1 (submodule.zero_mem 
    (submodule.span K {x.val}))))), fintype.card_eq.2 (by { use (equiv.of_bijective 
    (linear_equiv.to_span_nonzero_singleton K V x.1 (finset.not_mem_singleton.1 
    (finset.mem_compl.1 x.2))).to_equiv (linear_equiv.to_span_nonzero_singleton K V x.1 
    (finset.not_mem_singleton.1 (finset.mem_compl.1 x.2))).to_equiv.bijective) })],
  simp only [set.to_finset_card, ← set_like.coe_sort_coe],
  refl,
end

lemma num_subspaces_dim_one [fintype V] [nontrivial V] :
  (of_span K V).parts.card * ((fintype.card K) - 1) 
  = (fintype.card K) ^ (finite_dimensional.finrank K V) - 1 :=
begin
  have h6 : (of_span K V).parts.sum (λ (i : finset V), i.card) = 
    (of_span K V).parts.sum (λ (i : finset V), ((fintype.card K) - 1)),
  apply sum_congr rfl,
  { intros x hx,
    unfold of_span at hx,
    simp at hx,
    obtain ⟨v, hv⟩ := hx,
    rw [← card_subspace_rem_zero K V ⟨v, (finset.mem_compl.2 
      (finset.not_mem_singleton.2 hv.1))⟩, hv.2] },
  rw @sum_const _ (finset V) (of_span K V).parts _ ((fintype.card K) - 1) at h6,
  --simp only [algebra.id.smul_eq_mul] at h6,
  rw [← fintype.card_fin (finite_dimensional.finrank K V), ← module.card_fintype 
    (finite_dimensional.fin_basis K V), ← algebra.id.smul_eq_mul, ← h6, ← card_singleton (0 : V), 
    ← card_compl, ← @finpartition.sum_card_parts V _ ({0}ᶜ : finset V) (of_span K V)],
end

-- check out projectivization?

--variables [fintype (subspace K V)]
-- for general dimension of the subspace we might be able to set up an induction argument
-- need to show that if S is k-dimensional subspace, there are k (unique?) 1-dimensional subspaces whose closure is S
/-lemma dim_unique_subspaces [nontrivial V] (S : subspace K V) (h : 0 < finite_dimensional.finrank K S) :
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
end-/

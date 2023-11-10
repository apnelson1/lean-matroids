import analysis.inner_product_space.gram_schmidt_ortho
import data.zmod.basic data.finsupp.fintype
import linear_algebra.basis
import linear_algebra.linear_independent
import m_in.minor m_in.constructions
import m_in.erank
import m_in.equiv
import .m_in_rep .rep_m_constructions


universe u 
variables {α : Type} {β 𝔽 : Type*} {M : matroid_in α} {I B : set α} {x : α}
variables {W W' : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] [finite_dimensional 𝔽 W] 
  [add_comm_group W'] [module 𝔽 W'] 

open function set submodule finite_dimensional

noncomputable theory

 
open_locale classical


-- we should have semiring 𝔽 by default, idk why it doesn't see it
-- why did we have finite E and not fintype E?

namespace matroid_in

namespace rep

variables

variables [fintype α]


open_locale big_operators

lemma parallel_extend_rep (φ : rep 𝔽 W M) {x y : α} (hMx : M.nonloop x) (hy : y ∉ M.E) :
  matroid_of_module_fun 𝔽 W (λ (e : α), if e = y then - φ x else φ e) (insert y M.E) = 
  parallel_extend M hMx hy := 
begin
  apply parallel_extend_eq _ _ _ _ hMx hy,
  { rw circuit_iff_dep_forall_diff_singleton_indep,
    refine ⟨_, λ e he, _⟩,
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
    exact linear_independent_singleton (φ.ne_zero_of_nonloop hMx) },
  simp only [delete_elem, ← delete_matroid_of_module_fun, insert_diff_of_mem, mem_singleton,
    diff_singleton_eq_self hy],
  have h10 : ∀ e : α, e ∈ M.E → ite (e = y) (-φ x) (φ e) = φ e,
    intros e he,
    rw if_neg (ne_of_mem_of_not_mem he hy),
  simp_rw [matroid_of_module_fun_congr 𝔽 W _ _ _ h10],
  apply matroid_of_module_fun_rep_eq,
end

-- change x ∈ M.E and ¬ M.loop x to M.nonloop x
/-def parallel_extend_rep (φ : rep 𝔽 W M) {x y : α} (hx : x ∈ M.E)
  (hy : y ∉ M.E) (hMx : M.nonloop x) : rep 𝔽 W (parallel_extend M hMx hy) := 
{ to_fun := λ (e : α), 
    if e = y then φ x else φ e,
  valid' := λ I hI, 
    begin
      refine ⟨_, λ h2, _⟩,
      { contrapose,
      intros h2,
      rw linear_dependent_comp_subtype',
      rw not_indep_iff at h2,
      obtain ⟨C, ⟨hCI, hCcct⟩⟩ := exists_circuit_subset_of_dep h2,
      by_cases hyC : y ∈ C, 
      { by_cases hxC : x ∈ C,
        { have h4 := parallel_extend_circuit M hx hMx hy,
          have h5 := hCcct.eq_of_dep_subset (parallel_extend_circuit M hx hMx hy).dep 
            (insert_subset.2 ⟨hxC, singleton_subset_iff.2 hyC⟩),
          refine ⟨(⟨{x, y}, (λ e : α, if e = y then - 1 else (if e = x then 1 else 0)), λ a, 
            ⟨λ ha, _, λ ha, _⟩⟩ : α →₀ 𝔽), _⟩,
          sorry,
          sorry,
          sorry },
        { obtain ⟨C2, ⟨hC2, ⟨hC3, hC4⟩⟩⟩ := (parallel_extend_circuit M hx hMx hy).strong_elimination hCcct 
            (mem_inter (mem_insert_of_mem x (mem_singleton y)) hyC) 
            (mem_diff_of_mem (mem_insert x {y}) hxC),
          have hC2y : disjoint C2 {y},
            sorry,
          have h2 := delete_circuit_iff.2 ⟨hC3, hC2y⟩,
          rw ← delete_elem at h2,
          rw [← parallel_extend_delete_eq] at h2,
          obtain ⟨f, ⟨rfl, ⟨hftot, hfne0⟩⟩⟩ := rep.circuit φ h2,
          refine ⟨(⟨(insert y (f.support \ {x})), (λ e : α, if e = x then 0 else 
            (if e = y then f x else f e)), λ a, ⟨λ ha, _, λ ha, _⟩⟩ : α →₀ 𝔽), _⟩,
          rw if_neg,
          rw finset.mem_insert at ha,
          cases ha with hay ha,
          { rw if_pos hay,
            apply finsupp.mem_support_iff.1 hC4 },
          { rw if_neg,
            apply finsupp.mem_support_iff.1 (finset.mem_sdiff.1 ha).1,
            apply ne_of_mem_of_not_mem (finset.mem_sdiff.1 ha).1,
            apply not_mem_subset hC2 (not_mem_diff_of_mem (mem_singleton y)) },
          --have hf := finsupp.mem_support_iff,
          --obtain ⟨f, ⟨hC, ⟨hftot, hfne0⟩⟩⟩ := rep.circuit φ hC3.1,
          sorry,
          sorry,
          refine ⟨_, ⟨_, _⟩⟩,
          { rw finsupp.mem_supported,
            simp only [finset.coe_insert],
            apply insert_subset.2 ⟨mem_of_subset_of_mem hCI hyC, _⟩,
            simp only [finset.coe_sdiff, finset.coe_singleton, diff_singleton_subset_iff],
            sorry },
          { dsimp [finsupp.total_apply, finsupp.sum],
            dsimp [finsupp.total_apply, finsupp.sum] at hftot,
            simp_rw [ite_smul, zero_smul, smul_ite],
            /-rw ite_ite_comm,
            rw [finset.sum_ite_of_false _ _ (λ e he, _)],
            rw finset.sum_insert,
            simp only [if_pos],
            rw [finset.sum_ite_of_false _ _ (λ e he, _)],
            sorry,
            sorry,
            obtain ⟨he | he⟩ := finset.mem_insert.1 he,
            apply ne_of_mem_of_not_mem hyC hxC,
            apply finset.not_mem_singleton.1 (finset.mem_sdiff.1 h).2-/
            sorry },
          sorry } },
          sorry }, 
      { 
        sorry },
    end,
  support := λ e he, sorry }-/

end rep

end matroid_in
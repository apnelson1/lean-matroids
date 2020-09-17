/-
Examples of matroids.
-/
import matroid data.equiv.list

open finset

variables {α : Type*} [decidable_eq α] {E : finset α}
namespace matroid

/-- the loopy matroid on `E : finset α` is the matroid where every
element of `E` is a loop; equivalently, every subset of `E` is
dependent -/
def loopy (E : finset α) : indep E :=
⟨{∅},
powerset_mono.mpr $ empty_subset _,
mem_singleton_self _,
λ x y h1 h2, mem_singleton.mpr $ subset_empty.mp $ (mem_singleton.mp h1) ▸ h2,
λ x y hx hy hcard, false.elim $ (nat.not_lt_zero $ card x) $
  card_empty.subst $ (mem_singleton.mp hy).subst hcard⟩

/-- the free matroid is the matroid where every subset
of the ground set is independent; sometimes called the trivial matroid -/
def free (E : finset α) : indep E :=
⟨powerset E,
subset.refl _,
empty_mem_powerset _,
λ x y h1 h2, mem_powerset.mpr $ subset.trans h2 $ mem_powerset.mp h1,
λ x y hx hy hcard, exists.elim (exists_sdiff_of_card_lt hcard) $
  λ e exy, ⟨e, exy, mem_powerset.mpr $ insert_subset.mpr
    ⟨mem_of_subset (mem_powerset.mp hy) (mem_sdiff.mp exy).1, mem_powerset.mp hx⟩⟩⟩

/-- the uniform matroid U_k on `E : finset α` is the matroid whose
independent sets are all subsets of `E` of size `k` or less; Example 1.2.7 in Oxley -/
def uniform (k : ℕ) (E : finset α) : indep E :=
⟨(powerset E).filter (λ x, card x ≤ k),
filter_subset (powerset E),
mem_filter.mpr ⟨empty_mem_powerset E, (@card_empty $ finset α).symm ▸ nat.zero_le k⟩,
by { simp only [mem_powerset, and_imp, mem_filter],
  exact λ x y hx hcardx hy, ⟨subset.trans hy hx, le_trans (card_le_of_subset hy) hcardx⟩ },
by { simp only [mem_powerset, and_imp, mem_filter, mem_sdiff],
  exact λ x y hx hcardx hy hcardy hcard, exists.elim (exists_sdiff_of_card_lt hcard) $
  λ e exy, ⟨e, ⟨mem_sdiff.mp exy, ⟨insert_subset.mpr ⟨mem_of_subset hy (mem_sdiff.mp exy).1, hx⟩,
    (card_insert_of_not_mem (mem_sdiff.mp exy).2).symm ▸
      nat.succ_le_of_lt $ nat.lt_of_lt_of_le hcard hcardy⟩⟩⟩ }⟩

theorem loopy_eq_uniform_zero (E : finset α) : loopy E = uniform 0 E :=
suffices (loopy E).indep = (uniform 0 E).indep, from eq_of_indep_eq this,
by { simp only [loopy, uniform, ext, mem_powerset, mem_filter, card_eq_zero, le_zero_iff_eq,
    iff_false, insert_empty_eq_singleton, mem_singleton, not_mem_empty],
  intro a, rw ←eq_empty_iff_forall_not_mem,
  exact ⟨λ ha, ⟨ha.symm ▸ empty_subset E, ha⟩, λ ha, ha.2⟩ }

theorem free_eq_uniform_card (E : finset α) : free E = uniform (card E) E :=
suffices (free E).indep = (uniform (card E) E).indep, from eq_of_indep_eq this,
  by { simp only [free, uniform, ext, mem_powerset, mem_filter, empty_mem_powerset],
    exact λ a, ⟨λ ha, ⟨ha, card_le_of_subset ha⟩, λ ha, ha.1⟩ }

#eval uniform 2 $ range 4

#eval (is_basis {1,3} $ uniform 2 $ range 4 : bool)
#eval (is_basis {1,0,3} $ uniform 2 $ range 4 : bool)

#eval bases_of_indep $ loopy $ range 5
#eval bases_of_indep $ uniform 3 $ range 5
#eval bases_of_indep $ free $ range 5

#eval (is_circuit {1,2} $ uniform 2 $ range 4 : bool)
#eval (is_circuit {1,2,4} $ uniform 2 $ range 4 : bool)
#eval (is_circuit {1,2,3,4} $ uniform 2 $ range 4 : bool)

#eval circuits_of_indep $ loopy $ range 5
#eval circuits_of_indep $ uniform 3 $ range 5
#eval circuits_of_indep $ free $ range 5

#eval uniform 3 $ range 5
#eval indep_of_bases $ bases_of_indep $ uniform 3 $ range 5
#eval indep_of_circuits $ circuits_of_indep $ uniform 3 $ range 5

/- /- slow -/
#eval circuit_of_dep_of_insert_indep (dec_trivial : {0,2,3} ∈ (uniform 3 $ range 5).indep)
    (dec_trivial : 1 ∈ range 5) (dec_trivial : _ /-insert 3 {1,2} ∉ (uniform 2 $ range 4).indep -/)
#eval fund_circ_of_basis (dec_trivial : is_basis {0,1,2} (uniform 3 $ range 5))
    (dec_trivial : 4 ∈ range 5 \ {0,1,2}) -/
#eval fund_circ_of_basis (dec_trivial : is_basis ∅ (loopy $ range 5))
    (dec_trivial : 4 ∈ range 5 \ ∅)

#eval basis_containing_indep (dec_trivial : {0,2} ∈ (uniform 3 $ range 5).indep)

#eval basis_of_subset (dec_trivial : {0,4,1,2,3} ⊆ range 5) (uniform 3 $ range 5)

#eval rank_of_subset (dec_trivial : {0,4,1} ⊆ range 5) (uniform 3 $ range 5)
#eval rank_of_subset (dec_trivial : {0,4,2,1} ⊆ range 5) (uniform 3 $ range 5)
#eval rank_of_subset (dec_trivial : {0,4} ⊆ range 5) (loopy $ range 5)
#eval rank_of_subset (dec_trivial : {0,4} ⊆ range 5) (free $ range 5)

end matroid

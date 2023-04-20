import ..dual
import ..quotients
import ..simple

/-
Basic matroid constructions; free/loopy matroids, truncation, dual, etc.
-/
open_locale classical

open set
namespace matroid

noncomputable theory

section free_loopy

variables {E : Type*} {X I B : set E} {r s t : ℕ} {M : matroid E}

/-- The matroid whose only basis is empty -/
def loopy_on (E : Type*) : matroid E := 
matroid_of_exists_finite_base
(λ B, B = ∅) (⟨_,rfl, finite_empty⟩) 
(λ B B' hB hB' a ha, by {rw hB at ha, exact (not_mem_empty _ ha.1).elim })

instance : finite_rk (loopy_on E) := by { rw [loopy_on], apply_instance }

/-- The matroid whose only basis is the whole ground set -/
def free_on (E : Type*) : matroid E := (loopy_on E)﹡

@[simp] lemma free_on.dual (E : Type*) : (free_on E)﹡ = loopy_on E := by rw [free_on, dual_dual]

@[simp] lemma loopy_on.dual (E : Type*) : (loopy_on E)﹡ = free_on E := 
by rw [←free_on.dual, dual_dual]

@[simp] lemma loopy_on.base_iff_empty : (loopy_on E).base B ↔ B = ∅ := iff.rfl 

@[simp] lemma loopy_on.indep_iff_empty : (loopy_on E).indep I ↔ I = ∅ :=
by simp_rw [indep_iff_subset_base, loopy_on.base_iff_empty, exists_eq_left, subset_empty_iff]

@[simp] lemma free_on.base_iff_univ : (free_on E).base B ↔ B = univ :=
by rw [free_on, dual_base_iff, loopy_on.base_iff_empty, compl_empty_iff]

@[simp] lemma free_on.univ_base (E : Type*) : (free_on E).base univ := free_on.base_iff_univ.mpr rfl 

@[simp] lemma loopy_on.empty_base (E : Type*) : (loopy_on E).base ∅ := 
loopy_on.base_iff_empty.mpr rfl 

@[simp] lemma free_on.indep (I : set E) : (free_on E).indep I := 
(free_on.univ_base E).indep.subset (subset_univ _)

lemma univ_indep_iff_eq_free_on : M.indep univ ↔ M = free_on E :=
⟨λ h, eq_of_indep_iff_indep_forall (λ I, by simp [h.subset (subset_univ _)]), 
  by { rintro rfl, exact free_on.indep _} ⟩

lemma univ_base_iff_free_on : M.base univ ↔ M = free_on E :=
⟨λ h, univ_indep_iff_eq_free_on.mp h.indep, by { rintro rfl, simp }⟩ 

@[simp] lemma free_on.r_eq (X : set E) : (free_on E).r X = X.ncard :=
by rw ←(free_on.indep X).basis_self.card

@[simp] lemma free_on.rk_eq (E : Type*) : (free_on E).rk = nat.card E := 
by rw [rk_def, free_on.r_eq, ncard_univ]

@[simp] lemma empty_base_iff_loopy_on : M.base ∅ ↔ M = loopy_on E :=
by rw [←compl_compl (∅ : set E), ←dual_base_iff, compl_empty, univ_base_iff_free_on, 
  ←loopy_on.dual, dual_inj_iff]

@[simp] lemma free_on.cl (X : set E) : (free_on E).cl X = X :=
(subset_cl _ _).antisymm' (λ e he, (free_on.indep _).mem_cl_iff.mp he (free_on.indep _))
  
@[simp] lemma loopy_on.loop (e : E) : (loopy_on E).loop e := 
by simp_rw [loop_iff_dep, loopy_on.indep_iff_empty, singleton_ne_empty, not_false_iff]

@[simp] lemma loopy_on.cl (X : set E) : (loopy_on E).cl X = univ := 
begin
  refine eq_univ_of_subset (cl_subset_cl_of_subset _ (empty_subset X)) (eq_univ_of_forall _), 
  simp_rw [←loop_iff_mem_cl_empty], 
  exact loopy_on.loop, 
end 

lemma univ_loops_iff_loopy_on :
  M.cl ∅ = univ ↔ M = loopy_on E :=
begin
  refine ⟨λ h, eq_of_indep_iff_indep_forall (λ I, _), by { rintro rfl, simp }⟩,
  simp only [loopy_on.indep_iff_empty], 
  refine ⟨λ hI, _, by { rintro rfl, simp }⟩,
  have hdj := hI.disjoint_loops, 
  rwa [h, disjoint_univ] at hdj, 
end

lemma loopy_iff_univ_r_zero [finite E] :
  M = loopy_on E ↔ M.r univ = 0 :=
begin
  rw ←univ_loops_iff_loopy_on,
  refine ⟨λ h, by {rw ← h, simp}, λ h, _⟩,
  rwa [r_eq_zero_iff_subset_loops, univ_subset_iff] at h,
end

end free_loopy

section truncation

variables {E : Type*} {s t : ℕ} {I X : set E} {M : matroid E}

/-- Truncate a matroid to rank `t`. Every rank above `t` drops to `t`. -/
def tr {E : Type*} (M : matroid E) (t : ℕ) : matroid E := 
matroid_of_indep_of_bdd
(λ I, M.indep I ∧ I.finite ∧ I.ncard ≤ t) 
(by simp) 
(λ I J hJ hIJ, ⟨hJ.1.subset hIJ, hJ.2.1.subset hIJ, (ncard_le_of_subset hIJ hJ.2.1).trans hJ.2.2⟩) 
(begin
  rintro I B ⟨hI,hIfin,hIc⟩ hInb hB,
  obtain (hle | hlt) := le_or_lt B.ncard I.ncard, 
  { refine false.elim (hInb ⟨⟨hI,hIfin,hIc⟩,λ K hK hIK, hIK.ssubset_or_eq.elim (λ hss, false.elim _) 
    (λ h, h.symm.subset)⟩), 
    obtain ⟨e, heK, heB, hei⟩ := 
     hB.1.1.augment_of_finite hK.1 hB.1.2.1 (hle.trans_lt (ncard_lt_ncard hss hK.2.1)), 
    refine heB (hB.2 ⟨hei,hB.1.2.1.insert e,_⟩ (subset_insert _ _) (mem_insert _ _)),   
    rw [ncard_insert_of_not_mem heB hB.1.2.1, nat.add_one_le_iff], 
    exact hle.trans_lt ((ncard_lt_ncard hss hK.2.1).trans_le hK.2.2) },
  
  obtain ⟨e,heB,heI,hi⟩ := hI.augment_of_finite hB.1.1 hIfin hlt, 
  refine ⟨e, ⟨heB,heI⟩, hi, hIfin.insert e, (ncard_insert_le _ _).trans _⟩,
  rw nat.add_one_le_iff, 
  exact hlt.trans_le hB.1.2.2, 
end) 
t (λ I, and.right)

instance {E : Type*} {M : matroid E} {t : ℕ} : finite_rk (M.tr t) := by { rw tr, apply_instance }

lemma tr.indep_iff' : (M.tr t).indep I ↔ M.indep I ∧ I.finite ∧ I.ncard ≤ t := by simp [tr]

@[simp] lemma tr.indep_iff [finite_rk M] : (M.tr t).indep I ↔ M.indep I ∧ I.ncard ≤ t :=
by { rw [tr.indep_iff'], exact ⟨λ h, ⟨h.1, h.2.2⟩ , λ h, ⟨h.1, h.1.finite, h.2⟩⟩ }

@[simp] lemma tr.r_eq (M : matroid E) [finite_rk M] (t : ℕ) (X : set E) : 
  (M.tr t).r X = min t (M.r X) :=
begin
  refine le_antisymm (r_le_iff.mpr (λ I hIX hI, _)) (le_r_iff.mpr _),
  { rw tr.indep_iff at hI,
    refine le_min hI.2 _, 
    rw [←hI.1.r], 
    exact M.r_mono hIX },
  obtain ⟨J, hJ⟩ := M.exists_basis X, 
  obtain (hle | hlt) := le_or_lt J.ncard t, 
  { refine ⟨J, hJ.subset, tr.indep_iff.mpr ⟨hJ.indep, hle⟩, _⟩,
    rw [hJ.card, eq_comm, min_eq_right], rwa ←hJ.card },
  obtain ⟨I, hIJ, rfl⟩ := exists_smaller_set _ _ hlt.le, 
  refine ⟨I, hIJ.trans hJ.subset, tr.indep_iff.mpr ⟨hJ.indep.subset hIJ, rfl.le⟩, _⟩, 
  rw [eq_comm, min_eq_left], 
  rw [←hJ.card],
  exact hlt.le, 
end 

lemma tr.base_iff' (h_rk : t ≤ M.rk ∨ M.infinite_rk) {B : set E}  :
   (M.tr t).base B ↔ M.indep B ∧ B.finite ∧ B.ncard = t :=
begin
  simp_rw [base_iff_maximal_indep, tr.indep_iff', and_imp], 
  refine ⟨λ h, ⟨h.1.1, h.1.2.1, h.1.2.2.antisymm (le_of_not_lt (λ hlt, _))⟩, _⟩,
  { obtain ⟨B', hB', hBB'⟩ := h.1.1.exists_base_supset, 
    have : ∃ I, B ⊆ I ∧ I ⊆ B' ∧ I.ncard = t, 
    { obtain (hfin | hinf) := M.finite_or_infinite_rk, 
      { haveI := hfin, 
        rw [iff_false_intro M.not_infinite_rk, or_false] at h_rk,
        exact exists_intermediate_set' hlt.le (h_rk.trans_eq hB'.card.symm) hBB' },
      haveI := hinf, 
      exact hB'.infinite.exists_supset_ncard_eq hBB' h.1.2.1 hlt.le }, 
  
    obtain ⟨I, hBI, hIB', rfl⟩ := this, 
    have hIfin : I.finite, from finite_of_ncard_pos ((nat.zero_le _).trans_lt hlt), 
    have := h.2 I (hB'.indep.subset hIB') hIfin rfl.le hBI, subst this, 
    exact hlt.ne rfl },
  rintro ⟨hB, hBfin, rfl⟩, 
  exact ⟨⟨hB,hBfin,rfl.le⟩, λ I hI hIfin hIB hBI, eq_of_subset_of_ncard_le hBI hIB hIfin⟩,  
end 

lemma tr.base_iff [finite_rk M] (h_rk : t ≤ M.rk) {B : set E} : 
   (M.tr t).base B ↔ M.indep B ∧ B.ncard = t :=
by { rw tr.base_iff' (or.inl h_rk), exact ⟨λ h, ⟨h.1, h.2.2⟩, λ h, ⟨h.1, h.1.finite, h.2⟩⟩ }

lemma tr.cl_eq_univ_of_le_r {X : set E} (h : t ≤ M.r X) : (M.tr t).cl X = univ :=
begin
  have h_rk : t ≤ M.rk ∨ M.infinite_rk,
  { refine M.finite_or_infinite_rk.elim _ or.inr, 
    introI _, exact or.inl (h.trans (M.r_le_rk _)) },
  simp_rw [←base_subset_iff_cl_eq_univ, tr.base_iff' h_rk], 
  obtain ⟨J, hJ⟩ := M.exists_basis X, 
  obtain (hf | hi) := J.finite_or_infinite,
  { obtain ⟨I, hIJ, rfl⟩ := exists_smaller_set J t (by rwa [hJ.card]), 
    exact ⟨I, hIJ.trans hJ.subset, hJ.indep.subset hIJ, hf.subset hIJ, rfl⟩ },
  obtain ⟨I, hIJ, hIfin, rfl⟩ := hi.exists_subset_ncard_eq t, 
  exact ⟨I, hIJ.trans hJ.subset, hJ.indep.subset hIJ, hIfin, rfl⟩,  
end 

lemma basis.tr_basis_of_r_le [finite_rk M] (hI : M.basis I X) (hX : M.r X ≤ t) : 
  (M.tr t).basis I X :=
indep.basis_of_forall_insert (tr.indep_iff.mpr ⟨hI.indep, (by rwa [hI.card])⟩) 
  hI.subset (λ e he hi, he.2 (hI.mem_of_insert_indep he.1 (tr.indep_iff.mp hi).1)) 

lemma tr.cl_eq_cl_of_r_lt [finite_rk M] (h : M.r X < t) : (M.tr t).cl X = M.cl X :=
begin
  obtain ⟨J, hJ⟩ := M.exists_basis X, 
  have hJ' := hJ.tr_basis_of_r_le h.le, 
  rw [←hJ'.cl, ←hJ.cl], 
  ext e, 
  refine (em (e ∈ J)).elim (λ heJ, iff_of_true (mem_cl_of_mem _ heJ) (mem_cl_of_mem _ heJ)) 
    (λ heJ, _), 
  rw [hJ.indep.mem_cl_iff_of_not_mem heJ, hJ'.indep.mem_cl_iff_of_not_mem heJ, not_iff_not, 
    tr.indep_iff, and_iff_left_iff_imp, ncard_insert_of_not_mem heJ hJ.finite, nat.add_one_le_iff, 
    hJ.card],  
  exact λ _, h, 
end 

/-- This doesn't need `finite_rk M` to be true, but it's a bit of a pain to prove all the previous stuff at the right generality. TODO. -/
lemma tr.is_quotient (M : matroid E) [finite_rk M] (t : ℕ) : M.tr t ≼ M := 
λ X, (lt_or_le (M.r X) t).elim (λ h, (tr.cl_eq_cl_of_r_lt h).symm.subset) 
    (λ h, (subset_univ _).trans_eq (tr.cl_eq_univ_of_le_r h).symm)

end truncation

section uniform

variables {E : Type*} {s t r : ℕ} {I B X : set E} {M : matroid E}

/-- The matroid whose bases are the `r`-sets. If `E` is smaller than `r`, then this is the free
  matroid. -/
def unif (E : Type*) (r : ℕ) : matroid E := tr (free_on E) r

instance {E : Type*} {r : ℕ} : finite_rk (unif E r) := 
begin
  obtain ⟨B, hB⟩ := (unif E r).exists_base,
  refine hB.finite_rk_of_finite _, 
  have hi := hB.indep, 
  rw [unif, tr.indep_iff'] at hi, 
  exact hi.2.1, 
end 

/-- the rank-`a` uniform matroid on b elements with ground set `fin b`. Free if `b ≤ a`. -/
@[reducible] def canonical_unif (a b : ℕ) : matroid (fin b) := unif (fin b) a

lemma unif_eq_tr (E : Type*) (r : ℕ) : unif E r = tr (free_on E) r := rfl 

@[simp] lemma unif_r [finite E] (X : set E) : (unif E r).r X = min r (X.ncard) :=
by { rw [unif, tr.r_eq _ r, free_on.r_eq], apply_instance  }

lemma unif_rk [finite E] (hr : r ≤ nat.card E) : (unif E r).rk = r :=
by { rw [rk, unif_r univ, ncard_univ, min_eq_left hr], apply_instance,  }

lemma unif.indep_iff' : (unif E r).indep I ↔ I.finite ∧ I.ncard ≤ r :=
by rw [unif, tr.indep_iff', iff_true_intro (free_on.indep _), true_and]

@[simp] lemma unif.indep_iff [finite E] {I : set E}: (unif E r).indep I ↔ I.ncard ≤ r :=
by rw [indep_iff_r_eq_card, unif_r, min_eq_right_iff]

lemma unif_free_iff_card_le_r [finite E] : nat.card E ≤ r ↔ unif E r = free_on E :=
by rw [←univ_indep_iff_eq_free_on, unif.indep_iff, ncard_univ]

lemma unif_base_iff [finite E] (hr : r ≤ nat.card E) : (unif E r).base B ↔ B.ncard = r :=
begin
  rw [unif_eq_tr, tr.base_iff, iff_true_intro (free_on.indep _), true_and], 
  rwa free_on.rk_eq, 
end

@[simp] lemma unif_circuit_iff {C : set E} : (unif E r).circuit C ↔ C.ncard = r + 1 :=
begin
  obtain (rfl | ⟨e, heC⟩) := C.eq_empty_or_nonempty, 
  { exact iff_of_false (empty_not_circuit _) (by { rw ncard_empty, apply ne_zero.ne' }) },
  obtain (hinf | hfin) := C.finite_or_infinite.symm, 
  { refine iff_of_false (λ hC, hinf hC.finite) (by { rw hinf.ncard, apply ne_zero.ne' }) },
  simp_rw [circuit_iff_dep_forall_diff_singleton_indep, unif.indep_iff', not_and, not_le, 
    nat.lt_iff_add_one_le, iff_true_intro hfin, true_implies_iff], 
  refine ⟨λ h, h.1.antisymm' _, λ h, ⟨h.symm.le, λ f hf, ⟨ hfin.diff _, _⟩  ⟩⟩,
  { rw [←ncard_diff_singleton_add_one heC hfin, add_le_add_iff_right], exact (h.2 e heC).2 },
  rw [ncard_diff_singleton_of_mem hf hfin, h, add_tsub_cancel_right], 
end

@[simp] lemma unif_flat_iff [finite E] {F : set E} : (unif E r).flat F ↔ F = univ ∨ F.ncard < r :=
begin
  simp_rw [flat_iff_forall_circuit, unif_circuit_iff],
  refine ⟨λ h, (lt_or_le F.ncard r).elim or.inr (λ hle, or.inl _),_⟩,
  { obtain ⟨X,hXF,rfl⟩ := exists_smaller_set F r hle,
    refine eq_univ_of_forall (λ x, (em (x ∈ X)).elim (λ h', hXF h') (λ hxF, _)),
    refine h (insert x X) x (by rw [ncard_insert_of_not_mem hxF]) (mem_insert _ _) _,
    simp only [insert_diff_of_mem, mem_singleton, diff_singleton_subset_iff],
    exact hXF.trans (subset_insert _ _)},
  rintro (rfl | hlt),
  { exact λ _ _ _ _ _, mem_univ _},
  refine λ C e hcard heC hCF, _,
  have hlt' := (ncard_le_of_subset hCF).trans_lt hlt,
  rw [nat.lt_iff_add_one_le, ncard_diff_singleton_add_one heC, hcard] at hlt',
  simpa using hlt',
end

lemma unif_dual (E : Type*) [finite E] {r₁ r₂ : ℕ} (h : r₁ + r₂ = nat.card E) :
  (unif E r₁)﹡ = unif E r₂ :=
begin
  ext X,
  rw [unif_base_iff (le_of_add_le_right h.le), dual_base_iff,
    unif_base_iff (le_of_add_le_left h.le)],
  zify at *, split;
  { intro h, linarith [ncard_add_ncard_compl X]},
end

lemma unif_loopless_iff (E : Type*) (hE : nonempty E) : (unif E r).loopless ↔ 0 < r :=
by simp [loopless, loopless_on, ←indep_singleton, ←nat.add_one_le_iff]

lemma unif_simple_iff (E : Type*) (hE : 1 < nat.card E) {r : ℕ} :
  (unif E r).simple ↔ 1 < r :=
begin
  haveI : finite E, 
  { rw [←finite_univ_iff], refine finite_of_ncard_pos _, rw ncard_univ, linarith  },
  rw [←ncard_univ, one_lt_ncard_iff] at hE, 
  obtain ⟨a,b,-,-,hab⟩ := hE, 
  simp_rw [simple, unif.indep_iff], 
  obtain (hle | hlt) := le_or_lt r 1, 
  { refine iff_of_false _ hle.not_lt,
    push_neg, 
    refine ⟨a,b, hle.trans_lt (by { rw [ncard_eq_two.mpr ⟨a,b,hab,rfl⟩], exact one_lt_two }) ⟩ },
  refine iff_of_true (λ e f, le_trans _ hlt) hlt, 
  rw [←union_singleton], 
  exact (ncard_union_le _ _).trans (by simp), 
end

end uniform

end matroid

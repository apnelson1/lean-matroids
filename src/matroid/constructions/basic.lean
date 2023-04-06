import ..dual
import ..simple

/-
Basic matroid constructions; free/loopy matroids, truncation, dual, etc.
-/
open_locale classical

open set
namespace matroid

noncomputable theory

section free_loopy

variables {E : Type*} [finite E] {X I B : set E} {r s t : ℕ} [finite E] {M : matroid E}

/-- The matroid whose only basis is the whole ground set -/
def free_on (E : Type*) [finite E] : matroid E :=
matroid_of_base_of_finite
(λ B, B = univ) (⟨_,rfl⟩) (λ B B' hB hB' a ha, (ha.2 (by convert mem_univ a)).elim)

/-- The matroid whose only basis is empty -/
def loopy_on (E : Type*) [finite E] : matroid E := 
matroid_of_base_of_finite
(λ B, B = ∅) ⟨_,rfl⟩ (λ B B' hB hB' a ha, by {rw hB at ha, exact (not_mem_empty _ ha.1).elim })

lemma free_indep (I : set E) :
  (free_on E).indep I  :=
⟨univ, rfl, subset_univ _⟩

lemma univ_indep_iff_free {M : matroid E} :
   indep M univ ↔ M = free_on E :=
begin
  simp_rw [matroid.ext_iff, free_on, indep, univ_subset_iff, exists_eq_right],
  rw [function.funext_iff],
  simp_rw [eq_iff_iff, matroid_of_base_of_finite_apply],
  exact ⟨λ h a, ⟨λ ha, ha.eq_of_subset_base h (subset_univ _), λ ha, by rwa ha⟩, λ h, by rw h⟩,
end

@[simp] lemma free_r (X : set E) :
  (free_on E).r X = X.ncard :=
by {rw ← indep_iff_r_eq_card, apply free_indep}

@[simp] lemma loopy_on_base_iff_empty :
  (loopy_on E).base X ↔ X = ∅ :=
iff.rfl

lemma loopy_on.empty_base (E : Type*) [finite E] :
  (loopy_on E).base ∅ :=
@rfl _ ∅

@[simp] lemma loopy_on_indep_iff_empty :
  (loopy_on E).indep X ↔ X = ∅ :=
by simp only [indep_iff_subset_base, loopy_on_base_iff_empty, exists_eq_left, subset_empty_iff]

@[simp] lemma loopy_matroid_indep_iff_empty :
  (loopy_on E).indep X ↔ X = ∅ :=
by simp only [loopy_on, matroid_of_base_of_finite_apply, indep, exists_eq_left, subset_empty_iff]

@[simp] lemma empty_base_iff_loopy_on :
  M.base ∅ ↔ M = loopy_on E :=
begin
  refine ⟨λ h, _, by {rintro rfl, rw loopy_on_base_iff_empty}⟩,
  ext B,
  refine ⟨λ hB, (h.eq_of_subset_base hB (empty_subset _)).symm, λ hB, _⟩,
  rwa ←(loopy_on.empty_base E).eq_of_subset_base hB (empty_subset _),
end

lemma univ_loops_iff_loopy_on :
  M = loopy_on E ↔ M.cl ∅ = univ :=
begin
  simp_rw [←empty_base_iff_loopy_on, set.ext_iff, ←loop_iff_mem_cl_empty, mem_univ, iff_true,
    loop_iff_dep],
  refine ⟨λ hB x hx, singleton_ne_empty x (hB.eq_of_subset_indep hx (empty_subset _)).symm, λ h, _⟩,
  obtain ⟨B, hB⟩ := M.exists_base,
  convert hB,
  rw [eq_comm, eq_empty_iff_forall_not_mem],
  exact λ x hxB, h x (hB.indep.subset (singleton_subset_iff.mpr hxB)),
end

lemma loopy_iff_univ_r_zero :
  M = loopy_on E ↔ M.r univ = 0 :=
begin
  rw univ_loops_iff_loopy_on,
  refine ⟨λ h, by {rw ← h, simp}, λ h, _⟩,
  rwa [r_eq_zero_iff_subset_loops, univ_subset_iff] at h,
end

end free_loopy

section truncation

variables {E : Type*} [finite E] {s t : ℕ} {I : set E} {M : matroid E}

/-- Truncate a matroid to rank `t`. Every rank above `t` drops to `t`. -/
def tr (M : matroid E) (t : ℕ) :=
  matroid_of_r (λ X, min t (M.r X))
  (λ X, (min_le_right _ _).trans (M.r_le_card _))
  (λ X Y hXY, le_min (min_le_left _ _) ((min_le_right _ _).trans (M.r_mono hXY)))
  (λ X Y,
  (begin
    wlog hXY : M.r X ≤ M.r Y generalizing X Y,
    { obtain (h | h) := le_or_lt (M.r X) (M.r Y),
      { exact this _ _ h},
      rw [add_comm (min t (M.r X)), inter_comm, union_comm],
      exact this _ _ h.le},
    cases le_or_lt t (M.r Y) with ht ht,
    { rw [min_eq_left ht, min_eq_left (ht.trans (M.r_le_r_union_right _ _))],
      linarith [min_le_min (rfl.le : t ≤ t) (M.r_inter_left_le_r X Y)]},
    rw [min_eq_right_of_lt ht, min_eq_right (hXY.trans ht.le)],
    linarith [min_le_right t (M.r (X ∩ Y)), min_le_right t (M.r (X ∪ Y)), M.r_submod X Y],
  end))

@[simp] lemma tr_r (t : ℕ) (X : set E) :
  (M.tr t).r X = min t (M.r X) :=
by simp only [tr, matroid_of_r_apply]

@[simp] lemma tr_indep_iff :
  (M.tr t).indep I ↔ M.indep I ∧ I.ncard ≤ t :=
begin
  simp_rw [indep_iff_r_eq_card, tr_r],
  obtain (hle | hlt) := le_or_lt t (M.r I),
  { rw [min_eq_left hle],
    exact ⟨by {rintro rfl, exact ⟨hle.antisymm' (M.r_le_card _), rfl.le⟩},
      λ h, (hle.trans_eq h.1).antisymm h.2⟩},
  rw [min_eq_right hlt.le],
  simp only [iff_self_and],
  exact λ h, h.symm.trans_le hlt.le,
end

end truncation

section uniform

variables {E : Type*} [finite E] {s t r : ℕ} {M : matroid E}

/-- The matroid whose bases are the `r`-sets. If `E` is smaller than `r`, then this is the free
  matroid. TODO : define without rank  -/
def unif (E : Type*) [finite E] (r : ℕ) : matroid E := tr (free_on E) r

/-- the rank-a uniform matroid on b elements with ground set `fin' b`. Free if `b ≤ a`. -/
def canonical_unif (a b : ℕ) : matroid (fin b) := unif (fin b) a

@[simp] lemma unif_r (X : set E) :
  (unif E r).r X = min r (X.ncard) :=
by rw [unif, tr_r r, free_r]

lemma unif_rk (hr : r ≤ nat.card E) :
  (unif E r).rk = r :=
by rw [rk, unif_r univ, ncard_univ, min_eq_left hr]

@[simp] lemma unif_indep_iff {I : set E}:
  (unif E r).indep I ↔ I.ncard ≤ r :=
by rw [indep_iff_r_eq_card, unif_r, min_eq_right_iff]

lemma unif_free_iff_card_le_r :
  nat.card E ≤ r ↔ unif E r = free_on E :=
by rw [←univ_indep_iff_free, unif_indep_iff, ncard_univ]

lemma unif_base_iff {B : set E} (hr : r ≤ nat.card E):
  (unif E r).base B ↔ B.ncard = r :=
begin
  simp_rw [base_iff_maximal_indep, unif_indep_iff],
  rw [←ncard_univ] at hr,
  refine ⟨λ h, h.1.antisymm _, _⟩,
  { obtain ⟨Y, hXY, - ,rfl⟩ := exists_intermediate_set' h.1 hr (subset_univ _),
    rw h.2 Y rfl.le hXY},
  rintro rfl,
  exact ⟨rfl.le, λ I hIX hXI, eq_of_subset_of_ncard_le hXI hIX⟩,
end

@[simp] lemma unif_circuit_iff {C : set E}:
  (unif E r).circuit C ↔ C.ncard = r + 1 :=
begin
  simp_rw [circuit_def, unif_indep_iff, not_le],
  refine ⟨λ h, _,λ h, _⟩,
  { obtain ⟨e,he⟩ := nonempty_of_ncard_ne_zero (ne_zero_of_lt h.1),
    have hCe := h.2 (C \ {e}) (diff_singleton_ssubset.2 he),
    rw [←add_le_add_iff_right 1, ncard_diff_singleton_add_one he] at hCe,
    exact hCe.antisymm (nat.add_one_le_iff.mpr h.1)},
  refine ⟨by linarith, λ I hIC, (add_le_add_iff_right 1).mp _⟩,
  rw [←h, ←nat.lt_iff_add_one_le],
  exact ncard_lt_ncard hIC,
end

@[simp] lemma unif_flat_iff {F : set E} :
  (unif E r).flat F ↔ F = univ ∨ F.ncard < r :=
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
  (unif E r₁).dual = unif E r₂ :=
begin
  ext X,
  rw [unif_base_iff (le_of_add_le_right h.le), dual_base_iff,
    unif_base_iff (le_of_add_le_left h.le)],
  zify at *, split;
  { intro h, linarith [ncard_add_ncard_compl X]},
end

lemma unif_loopless_iff (E : Type*) (hE : nonempty E) [finite E] : (unif E r).loopless ↔ 0 < r :=
by simp [loopless, loopless_set, nonloop_iff_indep, ←nat.add_one_le_iff]

lemma unif_simple_iff (E : Type*) [finite E] (hE : 1 < nat.card E) {r : ℕ} :
  (unif E r).simple ↔ 1 < r :=
begin
  rw [←ncard_univ, one_lt_ncard_iff] at hE, 
  obtain ⟨a,b,-,-,hab⟩ := hE, 
  simp_rw [simple_iff_forall_pair_indep, unif_indep_iff], 
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

/-def dual (M : matroid E) : matroid E :=
{ base := λ X, M.base (univ \ X) ,
  exists_base' :=
    begin
      cases M.exists_base' with B hB,
      use (univ \ B),
      simp,
      exact hB,
    end,
  base_exchange' := λ X Y hX hY a ha,
    begin
      have h3 : a ∈ univ \ Y \ (univ \ X),
      { simp only [mem_diff, mem_univ, true_and, not_not_mem],
        refine ⟨ha.2, ha.1⟩ },
      have h2 := M.base_exchange' (univ \ Y) (univ \ X) hY hX a h3,
      simp at *,
      rcases h2 with ⟨b, ⟨hb1, hb2⟩⟩,
      use b,
      refine ⟨⟨hb1.2, hb1.1⟩, _⟩,
      have h4 := M.base_exchange' (univ \ X) (univ \ Y) hX hY b,
      have h5 : b ∈ univ \ X \ (univ \ Y),
      { simp,
        exact hb1 },
      specialize h4 h5,
      rcases h4 with ⟨x, ⟨hx1, hx2⟩⟩,
      simp at hx1,

      sorry,
    end }

lemma unif_dual {r : ℕ} (hr : 0 ≤ r) (hrn : r ≤ nat.card (univ : set E)) :
  dual (unif E r)
  = unif E (nat.card (univ : set E) - r) :=
begin
  ext X,
  rw [dual_r, unif_r hr, unif_r hr,
      unif_r (_ : 0 ≤ nat.card univ - r), min_eq_left hrn,
      compl_size, ← min_add_add_left, ← min_sub_sub_right, min_comm],
  congr,
  all_goals {linarith},
end

def circuit_matroid_on (E : Type*) [fintype E]: matroid E :=
  unif E (type_size E - 1)

@[simp] lemma circuit_matroid_r (hE : nonempty E) (X : set E) :
  (circuit_matroid_on E).r X = min (nat.card (univ : set E) - 1) (nat.card X) :=
by {convert unif_r  _ X, linarith [one_le_type_size_of_nonempty hE]}

lemma circuit_matroid_iff_univ_circuit (hE : nonempty E){M : matroid E} :
  M = circuit_matroid_on E ↔ is_circuit M univ :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  rw [circuit_iff_r, h],
  simp_rw circuit_matroid_r hE,
  from ⟨min_eq_left (by linarith), λ Y hY, min_eq_right (by linarith [size_strict_monotone hY])⟩,
  ext X, rw circuit_matroid_r hE,
  rw circuit_iff_r at h,
  have h' : X ⊂ univ ∨ X = univ := _ ,
  rcases h' with (h' | rfl ),
  { rw [h.2 X h', eq_comm], from min_eq_right (by linarith [size_strict_monotone h'])},
  { rw [h.1, eq_comm], from min_eq_left (by linarith)},
  from subset_ssubset_or_eq (subset_univ _),
end

lemma unif_simple_iff (E : Type*)[fintype E] (hE : 2 ≤ type_size E){r : ℕ} (hr : 0 ≤ r) :
  (unif.unif E r).is_simple ↔ 2 ≤ r :=
begin
  rw type_size_eq at hE,
  refine ⟨λ h, by_contra (λ hn, _), λ h, _⟩,
  { push_neg at hn,
    obtain ⟨X,hX⟩ := has_set_of_size  (by norm_num : (0 : ℤ) ≤ 2) hE,
    have h' := (h X (subset_univ X) (le_of_eq hX)),
    rw [indep_iff_r, hX] at h',
    have h'' := rank_le_univ (unif E r) X,

    rw [h', unif_r hr, min_eq_left] at h'';
    linarith},
  rintros X - hX,
  rw [indep_iff_r, unif_r hr, min_eq_right],
  -- linarith fails here - why???
  exact le_trans hX h,
end


lemma unif_loopless_iff (E : Type*) [fintype E] {r : ℕ} (hr : 0 ≤ r)
(hE : 1 ≤ type_size E):
  (unif.unif E r).is_loopless ↔ 1 ≤ r :=
begin
  simp_rw [loopless_iff_all_nonloops, nonloop_iff_r],
  by_cases (r ≤ 0),
  { rw [le_antisymm h hr],
    norm_num,
    obtain ⟨e⟩ :=  nonempty_of_type_size_pos hE,
    exact ⟨e, by {rw [unif_r, min_eq_left (size_nonneg _)]; norm_num,  }⟩},
  have : 1 ≤ r, rwa not_le at h,
  convert (iff_true _).mpr _, simpa only [iff_true, eq_iff_iff],
  intro e,
  rw unif_r hr,
  rw [size_singleton, min_eq_right this],
end

lemma unif_simple_of_two_le_r (E : Type*)[fintype E] {r : ℕ} (hr : 2 ≤ r) :
  (unif.unif E r).is_simple :=
begin
  rintros X - hX,
  rw [indep_iff_r, unif_r (by linarith : 0 ≤ r), min_eq_right],
  exact le_trans hX hr,
end
-/


/-!
  The canonical uniform matroid is defined to have a fixed ground set.
-/


/-lemma canonical_unif_simple_iff (ha : 0 ≤ a) (hb : 2 ≤ b) :
  (canonical_unif a b).is_simple ↔ 2 ≤ a :=
begin
 convert unif.unif_simple_iff (fin' b) _ ha,
 rwa size_fin' b (by linarith : 0 ≤ b),
end

lemma canonical_unif_loopless_iff (ha : 0 ≤ a) (hb : 1 ≤ b):
  (canonical_unif a b).loopless ↔ 1 ≤ a :=
begin
  convert unif.unif_loopless_iff (fin' b) _ _,
  assumption,
  convert hb, rw size_fin' b (by linarith : 0 ≤ b),
end
lemma canonical_unif_simple_of_two_le_r (ha : 2 ≤ a) :
  (canonical_unif a b).is_simple :=
unif.unif_simple_of_two_le_r _ ha-/

-- @[simp] lemma canonical_unif_r (ha : 0 ≤ a) (X : set (fin b)) :
--   (canonical_unif a b).r X = min a (X.ncard) :=
-- unif.unif_r ha _

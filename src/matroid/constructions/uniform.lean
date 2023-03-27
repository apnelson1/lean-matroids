import .truncation 

open matroid set 
open_locale classical

noncomputable theory 

variables {E : Type*} {X I B : set E} {r s t : ℕ} [finite E] {M : matroid E}

lemma free_indep (I : set E) :
  (free_matroid_on E).indep I  := 
⟨univ, rfl, subset_univ _⟩

lemma univ_indep_iff_free {M : matroid E} : 
   indep M univ ↔ M = free_matroid_on E := 
begin
  simp_rw [matroid.ext_iff, free_matroid_on, indep, univ_subset_iff, exists_eq_right], 
  rw [function.funext_iff],  
  simp_rw [eq_iff_iff], 
  exact ⟨λ h a, ⟨λ ha, ha.eq_of_subset_base h (subset_univ _), λ ha, by rwa ha⟩, λ h, by rw h⟩,
end 
  
@[simp] lemma free_r (X : set E) :
  (free_matroid_on E).r X = X.ncard :=
by {rw ← indep_iff_r_eq_card, apply free_indep}

@[simp] lemma loopy_on_base_iff_empty :
  (loopy_on E).base X ↔ X = ∅ := 
iff.rfl 

lemma loopy_on.empty_base (E : Type*) :
  (loopy_on E).base ∅ := 
@rfl _ ∅ 

@[simp] lemma loopy_on_indep_iff_empty :
  (loopy_on E).indep X ↔ X = ∅ := 
by simp only [indep_iff_subset_base, loopy_on_base_iff_empty, exists_eq_left, subset_empty_iff]

@[simp] lemma loopy_matroid_indep_iff_empty :
  (loopy_on E).indep X ↔ X = ∅ := 
by simp only [loopy_on, indep, exists_eq_left, subset_empty_iff]

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
  rwa [r_zero_iff_subset_loops, univ_subset_iff] at h, 
end

/-- The matroid whose bases are the `r`-sets. If `E` is smaller than `r`, then this is the free 
  matroid. TODO : define without rank  -/
def unif (E : Type*) [finite E] (r : ℕ) : matroid E := 
  tr (free_matroid_on E) r 

/-- the rank-a uniform matroid on b elements with ground set `fin' b`. Free if `b ≤ a`. -/
def canonical_unif (a b : ℕ) : 
  matroid (fin b) := 
unif (fin b) a


@[simp] lemma unif_r (X : set E) :
  (unif E r).r X = min r (X.ncard) := 
by rw [unif, tr_r r, free_r]

@[simp] lemma unif_rk (hr : r ≤ nat.card E) : 
  (unif E r).rk = r :=
by rw [rk, unif_r univ, ncard_univ, min_eq_left hr]
 
@[simp] lemma unif_indep_iff : 
  indep (unif E r) X ↔ X.ncard ≤ r := 
by rw [indep_iff_r_eq_card, unif_r, min_eq_right_iff]

lemma unif_base_iff (hr : r ≤ nat.card E): 
  base (unif E r) X ↔ X.ncard = r := 
begin
  simp_rw [base_iff_maximal_indep, unif_indep_iff], 
  rw [←ncard_univ] at hr, 
  refine ⟨λ h, h.1.antisymm _, _⟩,
  { obtain ⟨Y, hXY, - ,rfl⟩ := exists_intermediate_set' r h.1 hr (subset_univ _), 
    rw h.2 Y rfl.le hXY},
  rintro rfl, 
  exact ⟨rfl.le, λ I hIX hXI, eq_of_subset_of_ncard_le hXI hIX⟩, 
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

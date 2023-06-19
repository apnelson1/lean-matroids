import .minor
import .rank
import ..mathlib.data.set.ncard

variables {α : Type*} {M : matroid_in α} {k a b c : ℕ} {I J X C B E : set α}

open set 

namespace matroid_in 

section trivial 

/-- Given `I ⊆ E`, the matroid on `E` whose unique base is the set `I`. 
  (If `I` is not a subset of `E`, the base is `I ∩ E` )-/
def trivial_on (I E : set α) : matroid_in α := 
matroid_of_base E (λ X, X = I ∩ E) ⟨_, rfl⟩ 
(by { rintro B₁ B₂ rfl rfl x h, simpa using h })
(begin 
  rintro J Y ⟨B, rfl, hJB⟩ hJY, 
  use I ∩ Y ∩ E,
  simp only [mem_maximals_set_of_iff, exists_eq_left, subset_inter_iff, inter_subset_right, 
    and_true, and_imp], 
  rw [inter_right_comm, and_iff_left (inter_subset_right _ _), inter_assoc, 
    and_iff_right (inter_subset_left _ _), and_iff_left hJY, 
    and_iff_right (subset_inter_iff.mp hJB)], 
  exact λ X hXI hXE hJX hXY hss, hss.antisymm (subset_inter hXI (subset_inter hXE hXY)), 
end)
(by { rintro B rfl, apply inter_subset_right })

@[simp] lemma trivial_on_ground (hIE : I ⊆ E) : (trivial_on I E).E = E := 
by { simp only [trivial_on], refl }

lemma trivial_on_base_iff (hIE : I ⊆ E) : (trivial_on I E).base B ↔ B = I := 
by simp only [trivial_on, matroid_of_base_apply, inter_eq_self_of_subset_left hIE]

lemma trivial_on_eq_trivial_on_inter_ground (I E : set α) : trivial_on I E = trivial_on (I ∩ E) E :=
begin
  refine eq_of_base_iff_base_forall rfl (λ B hB, _), 
  simp_rw [trivial_on, matroid_of_base_apply, inter_assoc, inter_self], 
end 

lemma trivial_on_indep_iff (hIE : I ⊆ E) : (trivial_on I E).indep J ↔ J ⊆ I := 
by { simp_rw [indep_iff_subset_base, trivial_on_base_iff hIE], simp }

lemma trivial_on_inter_basis (hI : I ⊆ E) (hX : X ⊆ E) : (trivial_on I E).basis (X ∩ I) X := 
begin
  simp_rw [basis_iff, trivial_on_indep_iff hI, and_iff_right (inter_subset_left _ _), 
    and_iff_right (inter_subset_right _ _) ], 
  exact λ J hJ hXIJ hJX, hXIJ.antisymm (subset_inter hJX hJ), 
end 

lemma trivial_on_basis_iff (hIE : I ⊆ E) (hX : X ⊆ E) : (trivial_on I E).basis J X ↔ J = X ∩ I := 
begin
  have hb := trivial_on_inter_basis hIE hX, 
  refine ⟨λ h, _, λ h, by rwa h⟩,
  have hss := subset_inter h.subset ((trivial_on_indep_iff hIE).mp h.indep),
  exact h.eq_of_subset_indep hb.indep hss (inter_subset_left _ _), 
end 

@[simp] lemma trivial_on_dual_eq (I E : set α) : (trivial_on I E)﹡ = trivial_on (E \ I) E :=
begin
  rw [trivial_on_eq_trivial_on_inter_ground], 
  refine eq_of_base_iff_base_forall rfl (λ B (hB : B ⊆ E), _), 
  have hIE := inter_subset_right I E, 
  rw [dual_base_iff, trivial_on_ground hIE, trivial_on_base_iff hIE, 
    trivial_on_base_iff (diff_subset _ _), subset_antisymm_iff, diff_subset_comm, 
    subset_diff_comm hIE hB, ←subset_antisymm_iff, eq_comm, diff_inter_self_eq_diff], 
end 

/-- The matroid on `E` whose only basis is empty -/
def loopy_on (E : set α) : matroid_in α := trivial_on ∅ E

@[simp] lemma loopy_on_ground (E : set α) : (loopy_on E).E = E := rfl 

@[simp] lemma loopy_on_base_iff (E : set α) : (loopy_on E).base B ↔ B = ∅ :=
by rw [loopy_on, trivial_on_base_iff (empty_subset E)]

@[simp] lemma loopy_on_indep_iff (E : set α) : (loopy_on E).indep I ↔ I = ∅ :=
by rw [loopy_on, trivial_on_indep_iff (empty_subset E), subset_empty_iff]

/-- The matroid on `E` whose only basis is `E` -/
def free_on (E : set α) : matroid_in α := trivial_on E E

@[simp] lemma free_on_ground (E : set α) : (free_on E).E = E := rfl 

lemma free_on_finite {E : set α} (hE : E.finite) : finite (free_on E) :=
by { constructor, simpa }

@[simp] lemma free_on_base_iff (E : set α) : (free_on E).base B ↔ B = E := 
by rw [free_on, trivial_on_base_iff subset.rfl]

@[simp] lemma free_on_indep_iff (E : set α) : (free_on E).indep I ↔ I ⊆ E := 
by rw [free_on, trivial_on_indep_iff subset.rfl]

@[simp] lemma free_on_rk_eq (E : set α) : (free_on E).rk = E.ncard :=
by { obtain ⟨B, hB⟩ := (free_on E).exists_base, rw [←hB.card, (free_on_base_iff _).mp hB] }

@[simp] lemma free_on_basis_iff (hXE : X ⊆ E) : (free_on E).basis I X ↔ I = X :=
by rw [free_on, trivial_on_basis_iff subset.rfl hXE, inter_eq_self_of_subset_left hXE]

lemma free_on_r_eq (hXE : X ⊆ E) : (free_on E).r X = X.ncard := 
((free_on_indep_iff E).mpr hXE).r

lemma free_on_r_eq' {E X : set α} : (free_on E).r X = (X ∩ E).ncard := 
by rw [r_eq_r_inter_ground, free_on_ground, free_on_r_eq (inter_subset_right _ _)]

@[simp] lemma loopy_on_dual_eq (E : set α) : (loopy_on E)﹡ = free_on E := 
by simp [loopy_on, free_on]

@[simp] lemma free_on_dual_eq (E : set α) : (free_on E)﹡ = loopy_on E := 
by rw [←dual_dual (loopy_on E), loopy_on_dual_eq]

lemma ground_indep_iff_eq_free_on : M.indep M.E ↔ M = free_on M.E := 
begin
  refine ⟨λ hi, eq_of_indep_iff_indep_forall rfl (λ I hI, _), λ hM, _⟩, 
  { rw [free_on_indep_iff, iff_true_intro hI, iff_true],
    exact hi.subset hI }, 
  rw hM, 
  simp, 
end 

@[simp] lemma girth_eq_zero_iff_free_on [finitary M] : M.girth = 0 ↔ M = free_on M.E :=
begin
  rw [←ground_indep_iff_eq_free_on, girth_eq_zero_iff, indep_iff_forall_subset_not_circuit], 
  exact ⟨λ h C hCE hC, h C hC hC.finite, λ h C hC hi, h C hC.subset_ground hC⟩,
end 

/-- The matroid on `α` with empty ground set -/
def empty (α : Type*) : matroid_in α := matroid_in.loopy_on ∅ 

lemma ground_eq_empty_iff_eq_empty : M.E = ∅ ↔ M = empty α := 
begin
  simp_rw [eq_iff_indep_iff_indep_forall, empty, loopy_on_ground, loopy_on_indep_iff, iff_self_and], 
  rintro he I hI, 
  rw [he, subset_empty_iff] at hI, 
  simp [hI], 
end 

@[simp] lemma empty_ground : (empty α).E = ∅ := rfl  

@[simp] lemma empty_base_iff : (empty α).base B ↔ B = ∅ := 
by simp [empty]

/-- Any two empty matroids are isomorphic -/
def iso.of_empty (α β : Type*) : (empty α) ≃i (empty β) :=
{ to_equiv := by {convert equiv.equiv_of_is_empty (∅ : set α) (∅ : set β)},
  on_base' := by simp }

@[simp] lemma restrict_empty (M : matroid_in α) : M ‖ (∅ : set α) = empty α :=
by simp [←ground_eq_empty_iff_eq_empty]

@[simp] lemma dual_empty : (empty α)﹡ = empty α := 
by simp [←ground_eq_empty_iff_eq_empty]

@[simp] lemma delete_ground_eq_empty (M : matroid_in α) : M ⟍ M.E = empty α :=
by simp [←ground_eq_empty_iff_eq_empty]

@[simp] lemma contract_ground_eq_empty (M : matroid_in α) : M ⟋ M.E = empty α :=
by simp [←ground_eq_empty_iff_eq_empty]

end trivial 

/-- The truncation of a matroid to finite rank `k`. The independent sets of the truncation
  are the independent sets of the matroid of size at most `k`. -/
def truncate (M : matroid_in α) (k : ℕ) : matroid_in α := 
matroid_of_indep_of_bdd' M.E (λ I, M.indep I ∧ I.finite ∧ I.ncard ≤ k) 
(by simp)
(λ I J h hIJ, ⟨h.1.subset hIJ, h.2.1.subset hIJ, (ncard_le_of_subset hIJ h.2.1).trans h.2.2⟩ )
(begin
  rintro I J ⟨hI, hIfin, hIc⟩ ⟨hJ, hJfin, hJc⟩ hIJ, 
  obtain ⟨e, heJ, heI, hi⟩ := hI.augment_of_finite hJ hIfin hIJ, 
  refine ⟨e, heJ, heI, hi, hIfin.insert e, (ncard_insert_le _ _).trans _⟩, 
  rw [nat.add_one_le_iff], 
  exact hIJ.trans_le hJc, 
end) 
(⟨k, λ I, and.right⟩)
(λ I hI, hI.1.subset_ground)

@[simp] lemma truncate_indep_iff : (M.truncate k).indep I ↔ (M.indep I ∧ I.finite ∧ I.ncard ≤ k) := 
by simp [truncate]

@[simp] lemma truncate_ground_eq : (M.truncate k).E = M.E := rfl 

lemma truncate_base_iff [finite_rk M] (h : k ≤ M.rk) :
  (M.truncate k).base B ↔ M.indep B ∧ B.ncard = k :=
begin
  simp_rw [base_iff_maximal_indep, truncate_indep_iff, and_imp], 
  split, 
  { rintro ⟨⟨hBi, hBin, hBc⟩, hBmax⟩, 
    refine ⟨hBi, hBc.antisymm _⟩, 
    obtain ⟨B', hB', hBB'⟩ := hBi.exists_base_supset, 
    rw ←hB'.card at h, 
    obtain ⟨J, hBJ, hJB', rfl⟩ := exists_intermediate_set' hBc h hBB', 
    rw hBmax J (hB'.indep.subset hJB') (hB'.finite.subset hJB') rfl.le hBJ },
  rintro ⟨hB, rfl⟩, 
  exact ⟨⟨hB, hB.finite, rfl.le⟩, λ I hI hIfin hIc hBI, eq_of_subset_of_ncard_le hBI hIc hIfin⟩, 
end 

lemma truncate_base_iff_of_infinite_rk [infinite_rk M] :
  (M.truncate k).base B ↔ M.indep B ∧ B.finite ∧ B.ncard = k :=
begin
  simp_rw [base_iff_maximal_indep, truncate_indep_iff, and_imp], 
  split, 
  { rintro ⟨⟨hBi, hBfin, hBc⟩, hBmax⟩, 
    refine ⟨hBi, hBfin, hBc.antisymm _⟩, 
    obtain ⟨B', hB', hBB'⟩ := hBi.exists_base_supset, 
    obtain ⟨J, hBJ, hJB', hJfin, rfl⟩ := hB'.infinite.exists_supset_ncard_eq' hBB' hBfin hBc, 
    rw hBmax J (hB'.indep.subset hJB') hJfin rfl.le hBJ, },
  rintro ⟨hB, hBfin, rfl⟩, 
  exact ⟨⟨hB, hBfin, rfl.le⟩, λ I hI hIfin hIc hBI, eq_of_subset_of_ncard_le hBI hIc hIfin⟩, 
end 

instance truncate.finite [finite M] : finite (M.truncate k) := 
⟨ by simp [ground_finite M] ⟩ 

instance truncate.finite_rk : finite_rk (M.truncate k) := 
⟨ let ⟨B, hB⟩ := (M.truncate k).exists_base in ⟨B, hB, (truncate_indep_iff.mp hB.indep).2.1⟩ ⟩ 

lemma indep.of_truncate (h : (M.truncate k).indep I) : M.indep I := 
by { rw [truncate_indep_iff] at h, exact h.1 }

lemma indep.ncard_le_of_truncate (h : (M.truncate k).indep I) : I.ncard ≤ k := 
(truncate_indep_iff.mp h).2.2

lemma r_fin.truncate_r_eq (hX : M.r_fin X) (k : ℕ) : (M.truncate k).r X = min (M.r X) k := 
begin
  obtain ⟨I, hI⟩ := (M.truncate k).exists_basis X hX.subset_ground, 
  have hi := truncate_indep_iff.mp hI.indep, 
  obtain ⟨J, hJ, hIJ⟩ := hi.1.subset_basis_of_subset hI.subset, 
  rw [←hI.card, le_antisymm_iff, le_min_iff, and_iff_left hi.2.2, min_le_iff, ←hi.1.r, 
    and_iff_right (hX.r_mono hI.subset), ←hJ.card, hi.1.r], 
  by_contra' h, 
  obtain ⟨e, heJ, heI⟩ := exists_mem_not_mem_of_ncard_lt_ncard h.1 hI.indep.finite, 
  rw hI.eq_of_subset_indep _ (subset_insert e I) (insert_subset.mpr ⟨hJ.subset heJ,hI.subset⟩) 
    at heI, 
  { exact heI (mem_insert _ _) },
  rw truncate_indep_iff, 
  refine ⟨hJ.indep.subset (insert_subset.mpr ⟨heJ, hIJ⟩), hI.finite.insert e, _⟩, 
  refine (ncard_insert_le _ _).trans (nat.add_one_le_iff.mpr h.2), 
end 

lemma truncate_r_eq [finite_rk M] (k : ℕ) (X : set α) : (M.truncate k).r X = min (M.r X) k := 
begin
  rw [r_eq_r_inter_ground, M.r_eq_r_inter_ground, truncate_ground_eq], 
  exact (M.to_r_fin (X ∩ M.E)).truncate_r_eq _, 
end 

lemma truncate_r_eq_of_not_r_fin (hX : ¬M.r_fin X) (k : ℕ) (hXE : X ⊆ M.E . ssE) :
  (M.truncate k).r X = k :=
begin
  obtain ⟨I, hI⟩ := M.exists_basis X, 
  obtain ⟨J, hJI, hJfin, rfl⟩ := (hI.infinite_of_not_r_fin hX).exists_subset_ncard_eq k, 
  have hJfin' := M.r_fin_of_finite hJfin (hJI.trans hI.subset_ground_left), 
  have hJi : (M.truncate J.ncard).indep J, by simp [hI.indep.subset hJI, hJfin],
  obtain ⟨J', hJJ', hJ'⟩ := hJi.subset_basis_of_subset (hJI.trans hI.subset), 
  rw [←hJJ'.card, eq_of_subset_of_ncard_le hJ' _ hJJ'.indep.finite], 
  exact hJJ'.indep.ncard_le_of_truncate, 
end 

/-- A uniform matroid with a given rank and ground set -/
def set.unif_on (E : set α) (k : ℕ) := (free_on E).truncate k 

@[simp] lemma set.unif_on_indep_iff : (E.unif_on k).indep I ↔ I.finite ∧ I.ncard ≤ k ∧ I ⊆ E :=
by simp [set.unif_on, and_comm (I ⊆ E), and_assoc]

lemma set.unif_on_base_iff_of_finite (hE : E.finite) (hk : k ≤ E.ncard) (hBE : B ⊆ E) : 
  (E.unif_on k).base B ↔ B.ncard = k :=
by { haveI := free_on_finite hE, rw [set.unif_on, truncate_base_iff], simp [hBE], simpa }

lemma set.unif_on_r_eq_of_finite (E : set α) (k : ℕ) {X : set α} (hX : X ⊆ E) (hXfin : X.finite) : 
  (E.unif_on k).r X = min X.ncard k := 
begin
  rw [set.unif_on, r_fin.truncate_r_eq, free_on_r_eq hX], 
  apply r_fin_of_finite _ hXfin _, 
  ssE, 
end 

lemma set.unif_on_r_eq_of_infinite (E : set α) (k : ℕ) (hXinf : X.infinite) (hXE : X ⊆ E):
  (E.unif_on k).r X = k :=
begin
  rw [set.unif_on, truncate_r_eq_of_not_r_fin], 
  simp_rw [r_fin, not_exists, not_and, free_on_basis_iff hXE], 
  simpa, 
end 

/-- A uniform matroid of a given rank whose ground set is the universe of a type -/
def unif_on (α : Type*) (k : ℕ) := (univ : set α).unif_on k 

@[simp] lemma unif_on_ground_eq : (unif_on α k).E = (univ : set α) := rfl 

@[simp] lemma unif_on_indep_iff [_root_.finite α] : (unif_on α k).indep I ↔ I.ncard ≤ k := 
by simp only [unif_on, set.unif_on_indep_iff, subset_univ, and_true, and_iff_right_iff_imp, 
    iff_true_intro (to_finite I), imp_true_iff]
  
/-- A canonical uniform matroid, with rank `a` and ground type `fin b`. -/
def unif (a b : ℕ) := unif_on (fin b) a 

@[simp] lemma unif_ground_eq (a b : ℕ) : (unif a b).E = univ := rfl 

@[simp] lemma unif_indep_iff (I : set (fin b)) : (unif a b).indep I ↔ I.ncard ≤ a :=
by rw [unif, unif_on_indep_iff]

@[simp] lemma unif_r_eq (X : set (fin b)) : (unif a b).r X = min X.ncard a := 
by { rw [unif, unif_on, set.unif_on_r_eq_of_finite _ _ (subset_univ _)], exact to_finite X } 

@[simp] lemma unif_base_iff (hab : a ≤ b) {B : set (fin b)} : 
  (unif a b).base B ↔ B.ncard = a := 
begin
  simp only [unif, unif_on, set.unif_on], 
  rw [truncate_base_iff, free_on_indep_iff, and_iff_right (subset_univ _)], 
  rwa [free_on_rk_eq, ncard_eq_to_finset_card, finite.to_finset_univ, finset.card_fin], 
end 

lemma unif_dual' (h : a + b = c) : (unif a c)﹡ = unif b c := 
begin
  subst h, 
  refine eq_of_base_iff_base_forall rfl (λ B hB, _), 
  rw [unif_base_iff le_add_self, dual_base_iff, unif_base_iff le_self_add, unif_ground_eq, 
    ←compl_eq_univ_diff], 
  have hc := ncard_add_ncard_compl B, 
  rw [nat.card_eq_fintype_card, fintype.card_fin] at hc,
  exact ⟨λ h, by rwa [h, add_comm, add_right_inj] at hc, 
    λ h, by rwa [h, add_comm, add_left_inj] at hc⟩ 
end 

lemma unif_dual (hab : a ≤ b) : (unif a b)﹡ = unif (b - a) b := 
unif_dual' (nat.add_sub_of_le hab)

lemma unif_self_dual (a : ℕ) : (unif a (2*a))﹡ = unif a (2*a) := 
unif_dual' (two_mul a).symm 

section relax

def relax_set (M : matroid_in α) (Hs : set (set α)) := 
matroid_of_base M.E (λ B, M.base B ∨ (B ∈ Hs ∧ M.circuit B ∧ M.cocircuit (M.E \ B))) 
(M.exists_base.imp (λ _, or.inl)) 
(begin
  intros B B' hB hB' e he, 
  have hBE : B ⊆ M.E := hB.elim base.subset_ground (λ h', h'.2.1.subset_ground), 
  by_cases hel : M.coloop e, sorry,
  have h1 : M.indep (B \ {e}), sorry, 
  obtain ⟨B₁, hB₁⟩ := h1.subset_basis_of_subset (diff_subset_diff_left hBE) (diff_subset _ _), 
  have h2 : ¬M.base (B \ {e}), sorry, 
  rw coloop_iff_forall_mem_base at hel, push_neg at hel, 
  obtain ⟨B₁, hB₁, heB₁⟩ := hel, 
  

  -- have h2 : ∃ B₂, M.base B₂ ∧ B \ {e} ⊆ B₂ ∧ B₂ ⊆ (B \ {e}) ∪ B', sorry, 
  -- obtain ⟨B₂, hB₂, hssB₂, hB₂ss⟩ := h2, 
  -- obtain ⟨B₃, hB₃, hB₃ss⟩ := h1.exists_base_supset, 
  -- have := hB₃.exchange hB₂,  
  -- have := hB₁.exchange hB₂, 
  -- have h2 : ∃ x ∈ B' \ (B \ {e}), M.base (insert x (B \ {e})), 
  -- {   },

  -- obtain ⟨B1, hB1, hBeB1⟩ := h1.exists_base_supset,  
  -- { have := hB1.exchange, },

  
  -- obtain ⟨x, hx, hxB⟩ := h₁,  
  -- have h' : ∃ B₁ ⊆ (B \ {e}) ∪ B', B \ {e} ⊆ B₁ ∧ M.base B₁, sorry, 

  -- have heB : M.indep (B \ {e}), sorry, 
  -- rintro B B' (hB | ⟨hB, hBc, hBk⟩) (hB' | ⟨hB', hBc', hBk'⟩) e ⟨heB, heB'⟩, 
  
  -- { exact (hB.exchange hB' ⟨heB, heB'⟩).imp (λ f, Exists.imp (λ hf, or.inl)) },
  -- { have h' : ∃ B₁ ⊆ (B \ {e}) ∪ B', M.base B₁, sorry, 
  -- obtain ⟨B₁, hB₁ss, hB₁⟩ := h',  
  -- obtain ⟨B₂, hB₂, hBB₂⟩ := heB.exists_base_supset, 
  -- have := hB₂.exchange hB₁, 
  -- have := hB₂.exchange hB₁ ⟨, 
  --
  --  have := hB.exchange hB₁, 
  -- obtain ⟨f, hf, hBf⟩  := 
  --   hB.exchange hB₁ ⟨heB, λ heB₁, (hB₁ss heB₁).elim (not_mem_diff_singleton _ _) _⟩, 
  --   exact ⟨f, ⟨(hB₁ss hf.1).elim (λ h', (hf.2 h'.1).elim) id, hf.2⟩, or.inl hBf⟩ },
  
end) sorry sorry 

end relax

end matroid_in 
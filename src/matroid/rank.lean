import .loop
import tactic.linarith

/- The rank of a set in a matroid `M` is the size of one of its bases. When `M` is infinite, 
  this quantity is not defined in general, so rank is not very useful when building API for 
  general matroids, even though it is often the easiest way to do things for finite matroids. 

  A good number of rank lemmas have both `r_fin` versions, for sets of finite rank in a matroid
  of potentially infinite rank, and `[finite_rk M]` version, which apply in the more commonly 
  considered case where the entire matroid has finite rank, and are implied by the `r_fin` version. 
   -/

noncomputable theory
open_locale classical

open set

namespace matroid

variables {E : Type*} {M : matroid E}  {B X Y X' Y' Z I J : set E} {e f x y z : E} {k n : ℕ}

section basic 
/-- The rank `r X` of a set `X` is the cardinality of one of its bases, or zero if its bases are 
  infinite -/
def r {E : Type*} (M : matroid E) (X : set E) : ℕ := ⨅ (I : {I | M.basis I X}), ncard (I : set E)

/-- The rank `M.rk` of a matroid is the rank of its ground set -/
def rk {E : Type*} (M : matroid E) : ℕ := M.r univ

lemma rk_def {E : Type*} (M : matroid E) : M.rk = M.r univ := rfl 

/-- The rank of a set is the size of a basis -/
lemma basis.card (hI : M.basis I X) : I.ncard = M.r X :=
begin
  have hrw : ∀ J : {J : set E | M.basis J X}, (J : set E).ncard = I.ncard,
  { rintro ⟨J, (hJ : M.basis J X)⟩, rw [subtype.coe_mk, hI.card_eq_card_of_basis hJ] },
  haveI : nonempty {J : set E | M.basis J X}, from let ⟨I,hI⟩ := M.exists_basis X in ⟨⟨I,hI⟩⟩,
  simp_rw [r, hrw, cinfi_const],
end

lemma eq_r_iff {n : ℕ} : M.r X = n ↔ ∃ I, M.basis I X ∧ I.ncard = n :=
begin
  split,
  { rintro rfl, obtain ⟨I,hI⟩ := M.exists_basis X, exact ⟨I, hI, hI.card⟩ },
  rintro ⟨I,hI,rfl⟩, rw hI.card,
end

lemma indep.r (hI : M.indep I) : M.r I = I.ncard := eq_r_iff.mpr ⟨I, hI.basis_self, rfl⟩

lemma basis.r (hIX : M.basis I X) : M.r I = M.r X := by rw [←hIX.card, hIX.indep.r]

lemma basis.r_eq_card (hIX : M.basis I X) : M.r X = I.ncard := by rw [←hIX.r, ←hIX.indep.r]

lemma base.r (hB : M.base B) : M.r B = M.rk := by { rw base_iff_basis_univ at hB, rw hB.r, refl }

lemma base.card (hB : M.base B) : B.ncard = M.rk := by { rw (base_iff_basis_univ.mp hB).card, refl }

@[simp] lemma r_empty (M : matroid E) : M.r ∅ = 0 := 
by rw [←M.empty_indep.basis_self.card, ncard_empty]

@[simp] lemma r_cl (M : matroid E) (X : set E) : M.r (M.cl X) = M.r X :=
let ⟨I, hI⟩ := M.exists_basis X in by rw [←hI.r, ←hI.cl, hI.indep.basis_cl.r]

@[simp] lemma r_union_cl_right_eq_r_union (M : matroid E) (X Y : set E) :
  M.r (X ∪ M.cl Y) = M.r (X ∪ Y) :=
by rw [←r_cl, cl_union_cl_right_eq, r_cl]

@[simp] lemma r_union_cl_left_eq_r_union (M : matroid E) (X Y : set E) :
  M.r (M.cl X ∪ Y) = M.r (X ∪ Y) :=
by rw [←r_cl, cl_union_cl_left_eq, r_cl]

@[simp] lemma r_insert_cl_eq_r_insert (M : matroid E) (e : E) (X : set E) : 
  M.r (insert e (M.cl X)) = M.r (insert e X) :=
by rw [← union_singleton, r_union_cl_left_eq_r_union, union_singleton]

lemma basis.r_eq_r_union (hIX : M.basis I X) (Y : set E) :
  M.r (I ∪ Y) = M.r (X ∪ Y) :=
begin
  obtain ⟨I', hI', hII'⟩ :=
    hIX.indep.subset_basis_of_subset (hIX.subset.trans (subset_union_left _ Y)), 
  rw [←hI'.r, ← (hI'.basis_subset _ (union_subset_union_left Y hIX.subset)).r],   
  refine λ e he, (hI'.subset he).elim (λ heX, or.inl _) (λ heY, subset_union_right _ _ heY), 
  exact hIX.mem_of_insert_indep heX (hI'.indep.subset (insert_subset.mpr ⟨he, hII'⟩)), 
end

section finite

lemma r_le_card_of_finite (M : matroid E) {X : set E} (h : X.finite) : 
  M.r X ≤ X.ncard := 
let ⟨I,hI⟩ := M.exists_basis X in hI.card.symm.le.trans (ncard_le_of_subset hI.subset h)

lemma r_le_card [finite E] (M : matroid E) (X : set E) : M.r X ≤ X.ncard :=
M.r_le_card_of_finite (to_finite X)

lemma indep_iff_r_eq_card_of_finite {M : matroid E} (hI : I.finite) : M.indep I ↔ M.r I = I.ncard :=
begin
  obtain ⟨J,hJ⟩ := M.exists_basis I, 
  rw [←hJ.card], 
  refine ⟨λ h, by rw h.eq_of_basis hJ, λ h, _⟩, 
  rw ←eq_of_subset_of_ncard_le hJ.subset h.symm.le hI, 
  exact hJ.indep, 
end

lemma indep_iff_r_eq_card [finite E] : M.indep I ↔ M.r I = I.ncard :=
indep_iff_r_eq_card_of_finite (to_finite _)

lemma rk_le_card [finite E] (M : matroid E) : M.rk ≤ nat.card E :=
(M.r_le_card univ).trans (ncard_univ _).le
  
lemma r_lt_card_of_dep_of_finite (h : X.finite) (hX : ¬ M.indep X) : M.r X < X.ncard :=
lt_of_le_of_ne (M.r_le_card_of_finite h) 
  (by { rwa indep_iff_r_eq_card_of_finite h at hX })

lemma r_lt_card_of_dep [finite E] (hX : ¬ M.indep X) : M.r X < X.ncard :=
r_lt_card_of_dep_of_finite (to_finite _) hX 

lemma r_lt_card_iff_dep_of_finite (hX : X.finite) : M.r X < X.ncard ↔ ¬M.indep X := 
⟨λ h hI, (h.ne hI.r), r_lt_card_of_dep_of_finite hX⟩

lemma r_lt_card_iff_dep [finite E] : M.r X < X.ncard ↔ ¬M.indep X :=
⟨λ h hI, (h.ne hI.r),r_lt_card_of_dep⟩

end finite

section r_fin

/-- `M.r_fin X` means that `X` has a finite basis in `M`-/
def r_fin (M : matroid E) (X : set E) : Prop := ∃ I, M.basis I X ∧ I.finite  

lemma r_fin.exists_finite_basis (h : M.r_fin X) : ∃ I, M.basis I X ∧ I.finite := h 

lemma basis.finite_of_r_fin (h : M.basis I X) (hX : M.r_fin X) : I.finite :=
by { obtain ⟨J, hJ, hJfin⟩ := hX, exact hJ.finite_of_finite hJfin h }

lemma basis.r_fin_of_finite (hIX : M.basis I X) (h : I.finite) : M.r_fin X := ⟨I, hIX, h⟩ 

lemma basis.r_fin_iff_finite (hIX : M.basis I X) : M.r_fin X ↔ I.finite := 
⟨hIX.finite_of_r_fin, hIX.r_fin_of_finite⟩

lemma indep.r_fin_iff_finite (hI : M.indep I) : M.r_fin I ↔ I.finite := 
hI.basis_self.r_fin_iff_finite 

lemma indep.finite_of_r_fin (hI : M.indep I) (hfin : M.r_fin I) : I.finite := 
hI.basis_self.finite_of_r_fin hfin   

lemma indep.subset_finite_basis_of_subset_of_r_fin (hI : M.indep I) (hIX : I ⊆ X) (hX : M.r_fin X) :
∃ J, M.basis J X ∧ I ⊆ J ∧ J.finite :=
(hI.subset_basis_of_subset hIX).imp (λ J hJ, ⟨hJ.1, hJ.2, hJ.1.finite_of_r_fin hX⟩)

lemma to_r_fin (M : matroid E) [finite_rk M] (X : set E) : M.r_fin X :=  
by { obtain ⟨I,hI⟩ := M.exists_basis X, exact ⟨I, hI, hI.finite⟩ }

lemma r_fin_of_finite (M : matroid E) (hX : X.finite) : M.r_fin X := 
exists.elim (M.exists_basis X) (λ I hI, hI.r_fin_of_finite (hX.subset hI.subset))

lemma r_fin_singleton (M : matroid E) (e : E) : M.r_fin {e} := 
M.r_fin_of_finite (finite_singleton e)
 
@[simp] lemma r_fin_empty (M : matroid E) : M.r_fin ∅ := M.r_fin_of_finite finite_empty

lemma r_fin.subset (h : M.r_fin Y) (hXY : X ⊆ Y) : M.r_fin X := 
begin
  obtain ⟨I, hI⟩ := M.exists_basis X, 
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis_of_subset (hI.subset.trans hXY),    
  exact hI.r_fin_of_finite ((hJ.finite_of_r_fin h).subset hIJ), 
end 

lemma r_fin.finite_of_indep_subset (hX : M.r_fin X) (hI : M.indep I) (hIX : I ⊆ X) : I.finite := 
exists.elim (hI.subset_finite_basis_of_subset_of_r_fin hIX hX) (λ J hJ, hJ.2.2.subset hJ.2.1)

lemma indep.finite_of_subset_r_fin (hI : M.indep I) (hIX : I ⊆ X) (hX : M.r_fin X) : I.finite :=
hX.finite_of_indep_subset hI hIX 

lemma r_fin.to_cl (h : M.r_fin X) : M.r_fin (M.cl X) := 
begin
  obtain ⟨I, hI⟩ := M.exists_basis X, 
  rwa [←hI.cl, hI.indep.basis_cl.r_fin_iff_finite, ←hI.r_fin_iff_finite],     
end 

@[simp] lemma r_fin_cl_iff : M.r_fin (M.cl X) ↔ M.r_fin X := 
⟨λ h, h.subset (M.subset_cl _), r_fin.to_cl⟩

/-- A set with no finite basis has the junk rank value of zero -/
lemma r_eq_zero_of_not_r_fin (h : ¬M.r_fin X) : M.r X = 0 :=
begin
  simp_rw [r_fin, not_exists, not_and] at h, 
  obtain ⟨I, hI⟩ := M.exists_basis X, 
  rw [←hI.card, infinite.ncard (h _ hI)], 
end

lemma r_fin_of_r_ne_zero (h : M.r X ≠ 0) : M.r_fin X := 
begin
  obtain ⟨I, hI⟩ := M.exists_basis X, 
  rw [←hI.card] at h, 
  exact hI.r_fin_of_finite (finite_of_ncard_ne_zero h),  
end 

lemma r_fin.union (hX : M.r_fin X) (hY : M.r_fin Y) : M.r_fin (X ∪ Y) :=
begin
  obtain ⟨I, hI⟩ := M.exists_basis X, 
  obtain ⟨J, hJ⟩ := M.exists_basis Y, 
  rw [←r_fin_cl_iff, ←cl_union_cl_left_eq, ←hI.cl, cl_union_cl_left_eq, 
    ←cl_union_cl_right_eq, ←hJ.cl, cl_union_cl_right_eq, r_fin_cl_iff], 
  exact M.r_fin_of_finite ((hI.finite_of_r_fin hX).union (hJ.finite_of_r_fin hY)), 
end 

lemma r_fin.insert (hX : M.r_fin X) (e : E) : M.r_fin (insert e X) := (M.r_fin_singleton e).union hX 

lemma indep.le_card_basis_of_r_fin (hI : M.indep I) (hIX : I ⊆ X) (hX : M.r_fin X) 
(hXJ : M.basis J X) : I.ncard ≤ J.ncard :=
begin
  obtain ⟨I', hI, h⟩ := hI.subset_finite_basis_of_subset_of_r_fin hIX hX, 
  rw hXJ.card_eq_card_of_basis hI, 
  exact ncard_le_of_subset h.1 (hI.finite_of_r_fin hX), 
end 

lemma r_fin.le_r_iff (h : M.r_fin X) {n : ℕ} : n ≤ M.r X ↔ ∃ I ⊆ X, M.indep I ∧ I.ncard = n :=
begin
  obtain ⟨J, hJ⟩ := eq_r_iff.mp (@rfl _ (M.r X)),
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨I', hI', rfl⟩ := exists_smaller_set _ _ (h.trans_eq hJ.2.symm),
    exact ⟨I', hI'.trans hJ.1.subset, hJ.1.indep.subset hI', by simp⟩ },
  obtain ⟨I, hIX, hI, rfl⟩ := h,
  rw ←hJ.2,
  exact hI.le_card_basis_of_r_fin hIX h hJ.1, 
end 

lemma r_fin.r_le_iff (h : M.r_fin X) {n : ℕ} : M.r X ≤ n ↔ (∀ I ⊆ X, M.indep I → I.ncard ≤ n) :=
begin
  obtain ⟨I, hIX, hI⟩ := eq_r_iff.mp (@rfl _ (M.r X)),
  exact ⟨λ h' J hJX hJ, (hJ.le_card_basis_of_r_fin hJX h hIX).trans (hI.trans_le h'),
    λ h, hI.symm.trans_le (h I hIX.subset hIX.indep)⟩,
end 

lemma r_fin.r_mono (hY : M.r_fin Y) (hXY : X ⊆ Y) : M.r X ≤ M.r Y :=
by { simp_rw [(hY.subset hXY).r_le_iff, hY.le_r_iff], exact λ I hIX hI, ⟨I,hIX.trans hXY,hI,rfl⟩ }

lemma r_fin.r_eq_r_of_subset_le (h : M.r_fin Y) (hXY : X ⊆ Y) (hYX : M.r Y ≤ M.r X) : 
  M.r X = M.r Y :=
(h.r_mono hXY).antisymm hYX

lemma indep.card_le_r_of_subset_of_r_fin (hI : M.indep I) (h : I ⊆ X) (hX : M.r_fin X) : 
  I.ncard ≤ M.r X :=
by { rw [←hI.r], exact hX.r_mono h }

lemma indep.basis_of_subset_of_r_le_of_r_fin (hI : M.indep I) (hIX : I ⊆ X) (h : M.r X ≤ M.r I) 
(hX : M.r_fin X) :
  M.basis I X :=
begin
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset hIX,   
  rwa eq_of_subset_of_ncard_le hIJ _ (hJ.finite_of_r_fin hX), 
  rwa [hJ.card, ←hI.r], 
end

/-- The submodularity axiom for the rank function -/
lemma r_fin.r_inter_add_r_union_le_r_add_r (hX : M.r_fin X) (hY : M.r_fin Y) :
  M.r (X ∩ Y) + M.r (X ∪ Y) ≤ M.r X + M.r Y :=
begin
  obtain ⟨Ii, hIi⟩ := M.exists_basis (X ∩ Y),
  obtain ⟨IX, hIX, hIX', hIXfin⟩ :=
    hIi.indep.subset_finite_basis_of_subset_of_r_fin (hIi.subset.trans (inter_subset_left _ _)) hX,
  obtain ⟨IY, hIY, hIY', hIYfin⟩ :=
    hIi.indep.subset_finite_basis_of_subset_of_r_fin (hIi.subset.trans (inter_subset_right _ _)) hY,
  
  rw [←hIX.r_eq_r_union, union_comm, ←hIY.r_eq_r_union, ←hIi.card, ←hIX.card, ←hIY.card, 
   union_comm, ← ncard_union_add_ncard_inter _ _ hIXfin hIYfin, add_comm], 
  refine add_le_add (M.r_le_card_of_finite (hIXfin.union hIYfin)) _, 
  refine (ncard_le_of_subset (subset_inter hIX' hIY') (hIXfin.subset (inter_subset_left _ _))),
end

alias r_fin.r_inter_add_r_union_le_r_add_r ← r_fin.submod 

lemma r_fin.r_union_le_add_r (hX : M.r_fin X) (hY : M.r_fin Y) : M.r (X ∪ Y) ≤ M.r X + M.r Y :=
by linarith [hX.submod hY]

lemma r_fin.basis_iff_finite_indep_card (hX : M.r_fin X) :
  M.basis I X ↔ M.indep I ∧ I ⊆ X ∧ I.finite ∧ I.ncard = M.r X :=
begin
  refine (I.finite_or_infinite.symm.elim _ (λ hI, ⟨λ hb, ⟨hb.indep,hb.subset,hI,hb.card⟩, λ h, _⟩)), 
  { exact λ hI, iff_of_false (λ hb, hI (hb.finite_of_r_fin hX)) (by simp [iff_false_intro hI]) },
  
  refine h.1.basis_of_maximal_subset h.2.1 (λ J hJ hIJ hJX, _), 
  rw [←eq_of_subset_of_ncard_le hIJ _ (hJ.finite_of_subset_r_fin hJX hX)], 
  rw [h.2.2.2, hX.le_r_iff], 
  exact ⟨J, hJX, hJ, rfl⟩, 
end 

lemma indep.basis_of_r_fin_of_subset_of_r_ge (hI : M.indep I) (hIX : I ⊆ X) (hX : M.r_fin X) 
(hr : M.r X ≤ I.ncard) : 
  M.basis I X  :=
hX.basis_iff_finite_indep_card.mpr ⟨hI, hIX, hI.finite_of_subset_r_fin hIX hX, 
    hr.antisymm' (hX.le_r_iff.mpr ⟨I, hIX, hI,rfl⟩)⟩

lemma r_fin.r_eq_zero_iff_subset_loops (hX : M.r_fin X) : M.r X = 0 ↔ X ⊆ M.cl ∅ :=
begin
  obtain ⟨I, hI⟩ := M.exists_basis X,
  rw [←cl_subset_cl_iff_subset_cl, ←hI.cl], 
  rw hX.basis_iff_finite_indep_card at hI, 
  rw [←hI.2.2.2, ncard_eq_zero hI.2.2.1], 
  exact ⟨by { rintro rfl, exact subset.rfl }, 
    λ h, hI.1.eq_empty_of_subset_loops ((M.subset_cl I).trans h)⟩,
end 

lemma r_fin.r_eq_r_diff_r_le_zero (hY : M.r_fin Y) (X) (hr : M.r Y ≤ 0) : M.r (X \ Y) = M.r X :=
by rw [←r_cl, cl_diff_eq_cl_of_subset_loops (hY.r_eq_zero_iff_subset_loops.mp (le_zero_iff.mp hr)), 
  r_cl]

lemma r_fin.r_eq_r_union_r_le_zero (hY : M.r_fin Y) (X) (hr : M.r Y ≤ 0) : M.r (X ∪ Y) = M.r X :=
by rw [←r_cl, cl_union_eq_cl_of_subset_loops (hY.r_eq_zero_iff_subset_loops.mp (le_zero_iff.mp hr)), 
  r_cl]

lemma r_fin.r_le_r_inter_add_r_diff (hX : M.r_fin X) (Y : set E) : 
  M.r X ≤ M.r (X ∩ Y) + M.r (X \ Y) :=
begin
  convert r_fin.r_union_le_add_r (hX.subset (inter_subset_left _ _)) (hX.subset (diff_subset _ _)), 
  rw (inter_union_diff X Y), 
end 

lemma r_fin.r_le_r_add_r_diff (hX : M.r_fin X) (hYX : Y ⊆ X) : M.r X ≤ M.r Y + M.r (X \ Y) :=
begin
  convert hX.r_le_r_inter_add_r_diff _, 
  rw [inter_eq_self_of_subset_right hYX], 
end 

lemma r_fin.cl_eq_cl_of_subset_of_r_ge_r (hY : M.r_fin Y) (hXY : X ⊆ Y) (hr : M.r Y ≤ M.r X) : 
  M.cl X = M.cl Y :=
begin
  obtain ⟨I, hI⟩ := M.exists_basis X, 
  obtain ⟨J, hJ, hIJ, hJfin⟩ := hI.indep.subset_finite_basis_of_subset_of_r_fin 
    (hI.subset.trans hXY) hY, 
  rw [←hI.cl, ←hJ.cl, eq_of_subset_of_ncard_le hIJ _ hJfin], 
  rwa [hI.card, hJ.card],
end 

end r_fin

lemma le_r_iff [finite_rk M] : n ≤ M.r X ↔ ∃ I ⊆ X, M.indep I ∧ I.ncard = n := 
(M.to_r_fin X).le_r_iff

lemma r_le_iff [finite_rk M] : M.r X ≤ n ↔ (∀ I ⊆ X, M.indep I → I.ncard ≤ n) :=
(M.to_r_fin X).r_le_iff

lemma r_mono (M : matroid E) [finite_rk M] {X Y : set E} (hXY : X ⊆ Y) : M.r X ≤ M.r Y :=
(M.to_r_fin _).r_mono hXY 

lemma basis_iff_indep_card [finite_rk M] : M.basis I X ↔ M.indep I ∧ I ⊆ X ∧ I.ncard = M.r X :=
begin
  rw [(M.to_r_fin X).basis_iff_finite_indep_card], 
  exact ⟨λ h, ⟨h.1, h.2.1, h.2.2.2⟩, λ h, ⟨h.1, h.2.1, h.1.finite, h.2.2⟩⟩, 
end 

lemma r_le_rk (M : matroid E) [finite_rk M] (X : set E) : M.r X ≤ M.rk := M.r_mono (subset_univ _)

lemma lt_rk_iff_ne_rk [finite_rk M] : M.r X < M.rk ↔ M.r X ≠ M.rk := (M.r_le_rk X).lt_iff_ne

lemma indep.card_le_r_of_subset [finite_rk M] (hI : M.indep I) (h : I ⊆ X) : 
  I.ncard ≤ M.r X :=
by { rw [←hI.r], exact M.r_mono h }

lemma indep.card_le_rk [finite_rk M] (hI : M.indep I) : I.ncard ≤ M.rk :=
hI.r.symm.trans_le (M.r_mono (subset_univ I))

lemma base_iff_indep_r [finite_rk M] : M.base B ↔ M.indep B ∧ M.r B = M.rk :=
begin
  refine ⟨λ h, ⟨h.indep, h.r⟩, λ h, base_iff_maximal_indep.mpr ⟨h.1, λ I hI hBI, _⟩⟩,
  refine eq_of_le_of_not_lt hBI (λ hBI' : B ⊂ I, _),
  cases h with hB hB',
  rw [hB.r] at hB',
  have := ncard_lt_ncard hBI' hI.finite,
  rw [←hI.r, hB'] at this,
  exact (M.r_mono (subset_univ _)).not_lt this,
end

lemma base_iff_indep_card [finite_rk M] : M.base B ↔ M.indep B ∧ B.ncard = M.rk :=
⟨λ h, ⟨h.indep, by rw ←h.card⟩, λ h, base_iff_indep_r.mpr ⟨h.1, by rw [←h.2, ←h.1.r]⟩⟩

lemma indep.base_of_rk_le_card [finite_rk M] (hI : M.indep I) (h : M.rk ≤ I.ncard) : M.base I :=
base_iff_indep_card.mpr ⟨hI, h.antisymm' (by {rw ←hI.r, apply r_le_rk})⟩

lemma basis.r_eq_r_insert (hIX : M.basis I X) (e : E) : M.r (insert e I) = M.r (insert e X) :=
by simp_rw [←union_singleton, hIX.r_eq_r_union]

lemma indep.basis_of_subset_of_r_le [finite_rk M] (hI : M.indep I) (hIX : I ⊆ X) 
(h : M.r X ≤ M.r I) :
  M.basis I X := hI.basis_of_subset_of_r_le_of_r_fin hIX h (M.to_r_fin X)

/-- The submodularity axiom for the rank function -/
lemma r_inter_add_r_union_le_r_add_r (M : matroid E) [finite_rk M] (X Y : set E) :
  M.r (X ∩ Y) + M.r (X ∪ Y) ≤ M.r X + M.r Y :=
(M.to_r_fin X).r_inter_add_r_union_le_r_add_r (M.to_r_fin Y)

alias r_inter_add_r_union_le_r_add_r ← r_submod 

lemma eq_of_r_eq_r_forall {M₁ M₂ : matroid E} [finite_rk M₁] (h : ∀ X, M₁.r X = M₂.r X) : M₁ = M₂ :=
begin
  have h2 : ∀ I, M₂.indep I → I.finite, 
  { refine λ I hI, by_contra (λ (hinf : I.infinite), _),  
    obtain ⟨B₁,hB₁⟩ := M₁.exists_base, 
    obtain ⟨I₁,hI₁I, hI₁fin, hI₁card⟩ := hinf.exists_subset_ncard_eq (M₁.rk + 1), 
    rw [←(hI.subset hI₁I).r, ←h ] at hI₁card, 
    linarith [M₁.r_le_rk I₁] },
    
  refine eq_of_indep_iff_indep_forall (λ I, (I.finite_or_infinite.symm.elim 
    (λ hI, iff_of_false (λ h', hI h'.finite) (λ h', hI (h2 _ h') ) ) (λ hI, _))),  
  
  rw [indep_iff_r_eq_card_of_finite hI, h, indep_iff_r_eq_card_of_finite hI], 
end 

lemma r_le_r_of_subset (M : matroid E) [finite_rk M] (hXY : X ⊆ Y) : M.r X ≤ M.r Y :=
M.r_mono hXY

lemma r_inter_left_le_r (M : matroid E) [finite_rk M] (X Y : set E) : M.r (X ∩ Y) ≤ M.r X :=
M.r_mono (inter_subset_left X Y)

lemma r_inter_right_le_r (M : matroid E) [finite_rk M] (X Y : set E) : M.r (X ∩ Y) ≤ M.r Y :=
M.r_mono (inter_subset_right X Y)

lemma r_le_r_union_left (M : matroid E) [finite_rk M] (X Y : set E) : M.r X ≤ M.r (X ∪ Y) :=
M.r_mono (subset_union_left X Y)

lemma r_le_r_union_right (M : matroid E) [finite_rk M] (X Y : set E) : M.r Y ≤ M.r (X ∪ Y) :=
M.r_mono (subset_union_right X Y)

lemma r_diff_le_r (M : matroid E) [finite_rk M] (X Y : set E) : M.r (X \ Y) ≤ M.r X :=
by { rw diff_eq, apply r_inter_left_le_r }

lemma r_lt_card_iff_not_indep [finite E] : (M.r X < X.ncard) ↔ ¬M.indep X :=
begin
  rw [lt_iff_not_le, not_iff_not, indep_iff_r_eq_card],
  exact ⟨(M.r_le_card X).antisymm, λ h, by rw h⟩,
end

lemma nonempty_of_r_nonzero (hX : M.r X ≠ 0): X.nonempty :=
by {rw nonempty_iff_ne_empty, rintro rfl, exact hX M.r_empty}

lemma r_single_ub (M : matroid E) [finite_rk M] (e : E) : M.r {e} ≤ 1 :=
by { convert M.r_le_card_of_finite _; simp [ncard_singleton] }

lemma r_eq_r_of_subset_le [finite_rk M] (hXY : X ⊆ Y) (hYX : M.r Y ≤ M.r X) : M.r X = M.r Y :=
(M.r_mono hXY).antisymm hYX

lemma r_eq_r_diff_r_le_zero [finite_rk M] (X : set E) (hY : M.r Y ≤ 0) : M.r (X \ Y) = M.r X :=
(M.to_r_fin Y).r_eq_r_diff_r_le_zero _ hY 

lemma r_eq_r_union_r_le_zero [finite_rk M] (X : set E) (hY : M.r Y ≤ 0) : M.r (X ∪ Y) = M.r X :=
(M.to_r_fin Y).r_eq_r_union_r_le_zero _ hY 

lemma cl_eq_cl_of_subset_of_r_ge_r [finite_rk M] (hXY : X ⊆ Y) (hr : M.r Y ≤ M.r X) : 
  M.cl X = M.cl Y :=
(M.to_r_fin Y).cl_eq_cl_of_subset_of_r_ge_r hXY hr 

lemma r_union_eq_of_subset_of_r_le_r [finite_rk M] (Z : set E) (hXY : X ⊆ Y) (hr : M.r Y ≤ M.r X) :
  M.r (X ∪ Z) = M.r (Y ∪ Z) :=
by rw [←r_cl, ←cl_union_cl_left_eq, cl_eq_cl_of_subset_of_r_ge_r hXY hr, 
    cl_union_cl_left_eq, r_cl]

-- lemma r_union_eq_of_subset_of_r_eqs (hX : X ⊆ X') (hY : Y ⊆ Y')
-- (hXX' : M.r X = M.r X') (hYY' : M.r Y = M.r Y') :
--   M.r (X ∪ Y) = M.r (X' ∪ Y') :=
-- by rw [r_union_eq_of_subset_of_r_eq Y hX hXX', union_comm, union_comm _ Y',
--        r_union_eq_of_subset_of_r_eq _ hY hYY']

-- lemma r_eq_of_inter_union (X Y A : set E) :
--   M.r (X ∩ A) = M.r X → M.r ((X ∩ A) ∪ Y) = M.r (X ∪ Y) :=
-- λ h, r_union_eq_of_subset_of_r_eq _ (inter_subset_left _ _) h

-- lemma r_eq_of_union_r_diff_eq (Z : set E) (hX : M.r (X \ Y) = M.r X) :
--   M.r (Z ∪ (X \ Y)) = M.r (Z ∪ X) :=
-- by {rw diff_eq at *, rw [union_comm _ X, ← r_eq_of_inter_union _ Z _ hX, union_comm Z]}

lemma r_union_le_add_r (M : matroid E) [finite_rk M] (X Y : set E) : M.r (X ∪ Y) ≤ M.r X + M.r Y :=
by linarith [M.r_submod X Y]

lemma r_union_le_card_add_r [finite E] (M : matroid E) (X Y : set E) : 
  M.r (X ∪ Y) ≤ X.ncard + M.r Y :=
(M.r_union_le_add_r X Y).trans (add_le_add_right (M.r_le_card _) _)

lemma r_union_le_r_add_card [finite E] (M : matroid E) (X Y : set E) : 
  M.r (X ∪ Y) ≤ M.r X + Y.ncard :=
(M.r_union_le_add_r X Y).trans (add_le_add_left (M.r_le_card _) _)

lemma rk_le_card_add_r_compl [finite E] (M : matroid E) (X : set E) : M.rk ≤ X.ncard + M.r Xᶜ :=
begin
  rw [rk, ←union_compl_self X],
  exact (M.r_union_le_add_r _ _).trans (add_le_add_right (M.r_le_card _) _),
end

lemma rank_eq_of_le_supset [finite_rk M] (h : X ⊆ Y) (hr : M.r Y ≤ M.r X) : M.r X = M.r Y :=
hr.antisymm' (M.r_mono h)

lemma r_le_r_insert (M : matroid E) (e : E) (X : set E) : M.r X ≤ M.r (insert e X) :=
(em (M.r_fin X)).symm.elim (λ hX, by simp [r_eq_zero_of_not_r_fin hX]) 
  (λ hX, (hX.insert e).r_mono (subset_insert _ _)) 
  
lemma r_insert_le_add_one (M : matroid E) (e : E) (X : set E) : 
  M.r (insert e X) ≤ M.r X + 1 :=
begin
  refine (em (M.r_fin X)).symm.elim (λ hX, _) (λ hX, _), 
  { convert nat.zero_le _, 
    rw r_eq_zero_of_not_r_fin, 
    exact λ h, hX (h.subset (subset_insert _ _)) },
  refine ((M.r_fin_singleton e).r_union_le_add_r hX).trans _,
  rw [add_comm, add_le_add_iff_left, ←ncard_singleton e],  
  exact M.r_le_card_of_finite (finite_singleton e), 
end 

lemma r_eq_of_le_insert (h : M.r (insert e X) ≤ M.r X) : M.r (insert e X) = M.r X :=
h.antisymm (M.r_le_r_insert e X)

lemma r_insert_eq_add_one_of_r_ne (h : M.r (insert e X) ≠ M.r X) : M.r (insert e X) = M.r X + 1 :=
(nat.lt_iff_add_one_le.mp ((M.r_le_r_insert e X).lt_of_ne h.symm)).antisymm' 
  (M.r_insert_le_add_one e X)

lemma r_insert_eq_add_one_iff_r_ne : M.r (insert e X) = M.r X + 1 ↔ M.r (insert e X) ≠ M.r X :=
⟨by { intro h, rw h, exact (r M X).succ_ne_self } , r_insert_eq_add_one_of_r_ne⟩ 

lemma r_le_r_add_r_diff (M : matroid E) [finite_rk M] (X Y : set E) : M.r Y ≤ M.r X + M.r (Y \ X) :=
le_trans (M.r_mono (by simp)) (r_union_le_add_r M X (Y \ X))

lemma r_le_r_diff_singleton_add_one (M : matroid E) (e : E) (X : set E) :
  M.r X ≤ M.r (X \ {e}) + 1 :=
begin
  refine le_trans _ (M.r_insert_le_add_one e (X \ {e})),
  rw [insert_diff_singleton], 
  apply r_le_r_insert, 
end 

lemma r_diff_singleton_add_one_eq_r_of_ne (h_ne : M.r X ≠ M.r (X \ {e})) :
  M.r X = M.r (X \ {e}) + 1 :=
begin
  refine (em (e ∈ X)).symm.elim (λ h, (h_ne (by rw [diff_singleton_eq_self h])).elim) (λ he, _),
  convert (@r_insert_eq_add_one_of_r_ne _ _ _ e _);
  rwa [insert_diff_singleton, insert_eq_of_mem he],
end 

lemma r_le_r_add_card_diff_of_subset [finite E] (M : matroid E) (hXY : X ⊆ Y) : 
  M.r Y ≤ M.r X + (Y \ X).ncard :=
(M.r_le_r_add_r_diff X Y).trans (add_le_add_left (by convert M.r_le_card (Y \ X)) _)

lemma r_add_card_le_r_add_card_of_subset [finite E] (M : matroid E) (hXY : X ⊆ Y) :
  M.r Y + X.ncard ≤ M.r X + Y.ncard :=
begin
  have := M.r_le_r_add_card_diff_of_subset hXY,
  linarith [ncard_diff_add_ncard_eq_ncard hXY],
end

lemma submod_three (M : matroid E) [finite_rk M] (X Y Y' : set E) :
  M.r (X ∪ (Y ∪ Y')) + M.r (X ∪ (Y ∩ Y')) ≤ M.r (X ∪ Y) + M.r (X ∪ Y') :=
begin
  have := M.r_submod (X ∪ Y) (X ∪ Y'),
  rwa [←union_distrib_left, ←union_union_distrib_left, add_comm] at this,
end

lemma submod_three_right (M : matroid E) [finite_rk M] (X Y Y' : set E) :
  M.r ((Y ∪ Y') ∪ X) + M.r ((Y ∩ Y') ∪ X) ≤ M.r (Y ∪ X) + M.r (Y' ∪ X) :=
by {simp_rw ←(union_comm X), apply submod_three}

lemma submod_three_disj (M : matroid E) [finite_rk M] (X Y Y' : set E) (hYY' : Y ∩ Y' = ∅) :
  M.r (X ∪ (Y ∪ Y')) + M.r X ≤ M.r (X ∪ Y) + M.r (X ∪ Y') :=
by {have := submod_three M X Y Y', rwa [hYY', union_empty] at this}

lemma r_union_add_r_le_r_union_add_r_of_subset (M : matroid E) [finite_rk M] (hXY : X ⊆ Y) 
(Z : set E) : 
  M.r (Y ∪ Z) + M.r X ≤ M.r (X ∪ Z) + M.r Y :=
begin
  have hsm := M.r_submod (X ∪ Z) Y,
  rw [union_right_comm, union_eq_right_iff_subset.mpr hXY, inter_distrib_right,
    inter_eq_left_iff_subset.mpr hXY, add_comm] at hsm,
  exact le_trans (add_le_add_left (M.r_le_r_union_left _ _) _) hsm,
end

lemma r_fin.r_augment (hX : M.r_fin X) (hZ : M.r_fin Z) (h : M.r X < M.r Z) : 
  ∃ z ∈ Z \ X, M.r (insert z X) = M.r X + 1 :=
begin
  obtain ⟨I, hI, hIfin⟩ := hX.exists_finite_basis, 
  obtain ⟨J, hJ⟩ := M.exists_basis Z, 
  refine (hI.indep.augment_of_finite hJ.indep hIfin (by rwa [hI.card, hJ.card])).imp (λ e, _), 
  rintro ⟨he, heI, hi⟩, 
  refine ⟨⟨hJ.subset he, λ heX, heI (hI.mem_of_insert_indep heX hi)⟩, _⟩, 
  rw [←hI.r, hI.indep.r, ←ncard_insert_of_not_mem heI hIfin, ←hi.r, ←r_insert_cl_eq_r_insert, 
    ←hI.cl, r_insert_cl_eq_r_insert], 
end 

lemma r_fin.augment_of_not_r_fin (hX : M.r_fin X) (hZ : ¬M.r_fin Z) : 
  ∃ z ∈ Z \ X, M.r (insert z X) = M.r X + 1 := 
begin
  obtain ⟨J, hJ⟩ := M.exists_basis Z, 
  have hJinf : J.infinite, by rwa [set.infinite, ←hJ.r_fin_iff_finite], 
  obtain ⟨J', hJ'J, hJfin, hJcard⟩ := hJinf.exists_subset_ncard_eq (M.r X + 1), 
  obtain ⟨z, ⟨hzJ',hzX⟩, h⟩ := hX.r_augment (M.r_fin_of_finite hJfin) 
    (((lt_add_one _).trans_eq hJcard.symm).trans_eq (hJ.indep.subset hJ'J).r.symm), 
  exact ⟨z, ⟨hJ.subset (hJ'J hzJ'),hzX⟩, h⟩, 
end 

-- (M.to_r_fin X).r_augment (M.to_r_fin Z) h 

lemma r_union_eq_of_r_union_subset_le [finite_rk M] (hXY : X ⊆ Y) (h : M.r (X ∪ Z) ≤ M.r X) :
  M.r (Y ∪ Z) = M.r Y :=
begin
  have hsm := M.r_submod Y (X ∪ Z),
  rw [←union_assoc, union_eq_left_iff_subset.mpr hXY, inter_distrib_left,
    inter_eq_right_iff_subset.mpr hXY] at hsm,
  linarith [M.r_le_r_union_left X (Y ∩ Z), M.r_le_r_union_left Y Z],
end

lemma r_insert_eq_of_r_insert_subset_le [finite_rk M] (hXY : X ⊆ Y) (h : M.r (insert e X) ≤ M.r X) :
  M.r (insert e Y) = M.r Y :=
by {rw [←union_singleton] at *, rw [r_union_eq_of_r_union_subset_le hXY h],}

lemma r_eq_of_r_all_insert_le (hXY : X ⊆ Y) (hY : ∀ e ∈ Y, M.r (insert e X) ≤ M.r X) :
   M.r X = M.r Y :=
begin
  refine (em (M.r_fin Y)).symm.elim (λ hYinf, _) 
    (λ hYfin, (hYfin.r_mono hXY).antisymm (le_of_not_lt (λ hlt, _))),
  { refine (em (M.r_fin X)).symm.elim (λ hX, _) (λ hX, _), 
    { rw [r_eq_zero_of_not_r_fin hX, r_eq_zero_of_not_r_fin hYinf] }, 
    obtain ⟨e, ⟨heY, -⟩, hr'⟩ := hX.augment_of_not_r_fin hYinf, 
    linarith [hY e heY] },
  obtain ⟨e, he, hre⟩ := (hYfin.subset hXY).r_augment hYfin hlt,   
  linarith [hY e he.1], 
end

lemma r_union_eq_of_r_all_insert_le (hY : ∀ e ∈ Y, M.r (insert e X) ≤ M.r X) : 
  M.r (X ∪ Y) = M.r X :=
begin
  refine (r_eq_of_r_all_insert_le (subset_union_left X Y) _).symm,
  rintro e (heX | heY),
  { rw [insert_eq_of_mem heX]},
  exact hY _ heY,
end

lemma r_eq_of_r_all_insert_eq (hXY : X ⊆ Y) (hY : ∀ e ∈ Y, M.r X = M.r (insert e X)) :
   M.r X = M.r Y :=
r_eq_of_r_all_insert_le hXY (λ e h, (hY e h).symm.le)

lemma indep_inter_r_zero_eq_empty [finite_rk M] (hI : M.indep I) (hX : M.r X = 0) : I ∩ X = ∅ :=
begin
  have h := hI.subset (inter_subset_left _ X),
  rw [←ncard_eq_zero (hI.finite.subset (inter_subset_left _ _)), ←le_zero_iff], 
  rw indep_iff_r_eq_card_of_finite (hI.finite.subset (inter_subset_left _ _)) at h, 
  rw ←h, exact (M.r_mono (inter_subset_right I X)).trans_eq hX, 
end

lemma base_iff_indep_card_eq_r [finite_rk M] : M.base B ↔ M.indep B ∧ B.ncard = M.rk :=
begin
  refine ⟨λ hB, ⟨hB.indep, hB.card⟩, 
    λ h, base_iff_maximal_indep.mpr ⟨h.1, λ I hI hBI, eq_of_subset_of_ncard_le hBI _ hI.finite⟩⟩,
  rw [h.2], exact hI.card_le_rk,
end

end basic 

section circuit 

variables {C : set E}

lemma circuit.finite_of_r_fin (hC : M.circuit C) (hCfin : M.r_fin C) : C.finite :=
begin
  obtain ⟨e,he⟩ := hC.nonempty,
  convert ((hC.diff_singleton_indep he).finite_of_r_fin (hCfin.subset (diff_subset _ _))).insert e, 
  rw [insert_diff_singleton, insert_eq_of_mem he],  
end 

lemma circuit.r_fin_iff_finite (hC : M.circuit C) : M.r_fin C ↔ C.finite :=
⟨hC.finite_of_r_fin, M.r_fin_of_finite⟩ 

lemma circuit.card_of_finite (hC : M.circuit C) (hfin : C.finite) : C.ncard = M.r C + 1 :=
begin
  obtain ⟨e,he⟩ := hC.nonempty,
  have hss : C \ {e} ⊂ C, by {refine ssubset_of_ne_of_subset _ (diff_subset _ _),
    simpa only [ne.def, sdiff_eq_left, disjoint_singleton_right, not_not_mem]},
  have hlb := (M.r_fin_of_finite hfin).r_mono hss.subset,
  rw [(hC.ssubset_indep hss).r] at hlb,
  linarith [ncard_diff_singleton_add_one he hfin, r_lt_card_of_dep_of_finite hfin hC.dep],
end 

lemma circuit.card [finitary M] (hC : M.circuit C) : C.ncard = M.r C + 1 :=
hC.card_of_finite hC.finite

/-- This lemma is phrased in terms of `nat` subtraction; it never underflows but is probably still
  best avoided -/
lemma circuit.nat_r_eq [finitary M] (hC : M.circuit C) : M.r C = C.ncard - 1 :=
by rw [hC.card, nat.add_succ_sub_one, add_zero]

lemma circuit.cast_r_eq [finitary M] (hC : M.circuit C) : (M.r C : ℤ) = C.ncard - 1 :=
by rw [hC.card, nat.cast_add, nat.cast_one, add_tsub_cancel_right]

lemma exists_circuit_iff_card_lt_rk [finite E] : M.rk < (univ : set E).ncard ↔ ∃ C, M.circuit C :=
by simp_rw [matroid.rk, r_lt_card_iff_dep, dep_iff_supset_circuit, exists_prop, 
  and_iff_right (subset_univ _)]

end circuit 

section cl_flat

variables {F F' F₁ F₂ H H₁ H₂ : set E}

lemma flat.r_insert_of_not_mem_of_r_fin (hF : M.flat F) (he : e ∉ F) (hfin : M.r_fin F):
  M.r (insert e F) = M.r F + 1 :=
begin
  obtain ⟨I, hI⟩ := M.exists_basis F, 
  rw [←hF.cl, ←hI.cl, hI.indep.not_mem_cl_iff] at he, 
  rw [←(hI.insert_basis_insert he.2).card, ←hI.card, 
    ncard_insert_of_not_mem he.1 (hI.finite_of_r_fin hfin)],
end

lemma flat.r_insert_of_not_mem [finite_rk M] (hF : M.flat F) (he : e ∉ F) :
  M.r (insert e F) = M.r F + 1 :=
hF.r_insert_of_not_mem_of_r_fin he (M.to_r_fin F)

lemma flat_iff_r_lt_r_insert [finite_rk M] : M.flat F ↔ ∀ e ∉ F, M.r F < M.r (insert e F) :=
begin
  refine ⟨λ hF e heF, nat.lt_iff_add_one_le.mpr (hF.r_insert_of_not_mem heF).symm.le,
    λ h, flat_def.mpr (λ I X hIF hIX, _)⟩,
  by_contra' hXF,
  obtain ⟨e,heX,heF⟩ := not_subset.mp hXF,
  apply (h _ heF).ne,
  rw [←hIF.r_eq_r_insert, hIX.r_eq_r_insert, insert_eq_of_mem heX, ←hIF.r, ←hIX.r],
end

lemma flat.not_mem_iff_r_insert_of_r_fin (hF : M.flat F) (hfin : M.r_fin F) : 
  e ∉ F ↔ M.r (insert e F) = M.r F + 1 :=
begin
  refine ⟨λ he, hF.r_insert_of_not_mem_of_r_fin he hfin, λ h he, _⟩,
  rw [insert_eq_of_mem he, self_eq_add_right] at h,
  simpa only using h,
end

lemma flat.not_mem_iff_r_insert [finite_rk M] (hF : M.flat F) : 
  e ∉ F ↔ M.r (insert e F) = M.r F + 1 :=
hF.not_mem_iff_r_insert_of_r_fin (M.to_r_fin F)

lemma flat.r_lt_r_of_ssubset_of_r_fin (hF : M.flat F) (hFX : F ⊂ X) (hX : M.r_fin X) : 
  M.r F < M.r X :=
begin
  obtain ⟨e, heX, heF⟩ := exists_of_ssubset hFX, 
  rw [nat.lt_iff_add_one_le, ←hF.r_insert_of_not_mem_of_r_fin heF (hX.subset hFX.subset)], 
  exact hX.r_mono (insert_subset.mpr ⟨heX, hFX.subset⟩), 
end 

lemma flat.eq_of_r_le_r_subset_of_r_fin (hF : M.flat F) (hFfin : M.r_fin X) (hFX : F ⊆ X) 
(hr : M.r X ≤ M.r F) : 
  F = X :=
by_contra (λ hne, (hF.r_lt_r_of_ssubset_of_r_fin (hFX.ssubset_of_ne hne) hFfin).not_le hr)

lemma flat.r_lt_r_of_ssubset [finite_rk M] (hF : M.flat F) (hFX : F ⊂ X) : M.r F < M.r X :=
hF.r_lt_r_of_ssubset_of_r_fin hFX (M.to_r_fin X)

lemma flat.eq_of_le_r_subset [finite_rk M] (hF : M.flat F) (hFX : F ⊆ X) (hr : M.r X ≤ M.r F) : 
  F = X := 
hF.eq_of_r_le_r_subset_of_r_fin (M.to_r_fin X) hFX hr  

lemma flat.eq_univ_of_rk_le_r [finite_rk M] (hF : M.flat F) (hr : M.rk ≤ M.r F) : F = univ :=
hF.eq_of_le_r_subset (subset_univ _) hr

lemma r_fin.mem_cl_iff_r_insert (hX : M.r_fin X) : e ∈ M.cl X ↔ M.r (insert e X) = M.r X :=
by rw [←not_iff_not, ←ne.def, ←r_insert_eq_add_one_iff_r_ne, ←singleton_union, 
    ←r_union_cl_right_eq_r_union, singleton_union, 
    (M.flat_of_cl X).not_mem_iff_r_insert_of_r_fin hX.to_cl, r_cl]

lemma r_fin.not_mem_cl_iff_r_insert (hX : M.r_fin X) : e ∉ M.cl X ↔ M.r (insert e X) = M.r X + 1 :=
begin
  rw [hX.mem_cl_iff_r_insert, ←ne.def],
  refine ⟨r_insert_eq_add_one_of_r_ne, λ h,
    by simp only [h, ne.def, nat.succ_ne_self, not_false_iff]⟩,
end

lemma mem_cl_iff_r_insert [finite_rk M] : e ∈ M.cl X ↔ M.r (insert e X) = M.r X :=
(M.to_r_fin X).mem_cl_iff_r_insert 

lemma not_mem_cl_iff_r_insert [finite_rk M] : e ∉ M.cl X ↔ M.r (insert e X) = M.r X + 1 :=
(M.to_r_fin X).not_mem_cl_iff_r_insert 

lemma subset_cl_iff_r_union_eq_r [finite_rk M] : X ⊆ M.cl Y ↔ M.r (Y ∪ X) = M.r Y :=
begin
  refine ⟨λ h, r_union_eq_of_r_all_insert_le (λ e he, by rw mem_cl_iff_r_insert.mp (h he)),
    λ hu e heX, mem_cl_iff_r_insert.mpr ((M.r_mono (subset_insert _ _)).antisymm' _)⟩,
  rw ←hu,
  apply r_mono,
  rw insert_subset,
  simp only [mem_union, subset_union_left, and_true],
  exact or.inr heX,
end

lemma r_insert_eq_add_one_of_not_mem_cl [finite_rk M] (h : e ∉ M.cl X) :
  M.r (insert e X) = M.r X + 1 :=
r_insert_eq_add_one_of_r_ne (h ∘ mem_cl_iff_r_insert.mpr)

lemma not_mem_cl_of_r_insert_gt [finite_rk M] (h : M.r X < M.r (insert e X)) : e ∉ M.cl X :=
h.ne.symm ∘ mem_cl_iff_r_insert.mp

lemma mem_cl_of_r_insert_le [finite_rk M] (h : M.r (insert e X) ≤ M.r X) : e ∈ M.cl X :=
mem_cl_iff_r_insert.mpr (h.antisymm (M.r_le_r_insert e X))

lemma r_eq_rk_iff_cl_eq_univ [finite_rk M] : M.r X = M.rk ↔ M.cl X = univ :=
⟨λ h, eq_univ_iff_forall.mpr (λ e, mem_cl_of_r_insert_le ((M.r_le_rk _).trans_eq h.symm)), 
    λ h, by rw [←M.r_cl, h, rk]⟩

lemma not_mem_cl_iff_r_insert_eq_add_one [finite_rk M] :
  e ∉ M.cl X ↔ M.r (insert e X) = M.r X + 1 :=
⟨r_insert_eq_add_one_of_not_mem_cl, λ h, not_mem_cl_of_r_insert_gt (by {rw h, apply lt_add_one})⟩

lemma r_le_iff_cl {n : ℕ} [finite_rk M] : M.r X ≤ n ↔ ∃ I, X ⊆ M.cl I ∧ I.ncard ≤ n ∧ I.finite :=
begin
  refine ⟨λ h, _, _⟩,
  { obtain ⟨I,hI⟩ := M.exists_basis X,
    exact ⟨I, hI.subset_cl, by rwa hI.card, hI.finite⟩ },
  rintro ⟨I, hXI, hIn⟩,
  refine (M.r_mono hXI).trans _, 
  rw [r_cl],
  exact (M.r_le_card_of_finite hIn.2).trans hIn.1,
end

lemma le_r_iff_cl {n : ℕ} [finite_rk M] : n ≤ M.r X ↔ ∀ I, X ⊆ M.cl I → I.finite → n ≤ I.ncard :=
begin
  cases n, simp,
  rw [←not_lt, ←not_iff_not, not_not, not_forall],
  simp_rw [not_imp, not_le, nat.lt_succ_iff],
  rw r_le_iff_cl,
  tauto, 
end

lemma flat.covby_iff_r_of_r_fin (hF : M.flat F) (hFfin : M.r_fin F) (hF' : M.flat F') :
  M.covby F F' ↔ F ⊆ F' ∧ M.r F' = M.r F + 1 :=
begin
  rw hF.covby_iff_eq_cl_insert, 
  refine ⟨_, λ h, _⟩,
  { rintro ⟨e, he, rfl⟩, 
    rw [and_iff_right (M.subset_cl_of_subset (subset_insert _ _)), r_cl, 
      (hF.not_mem_iff_r_insert_of_r_fin hFfin).mp he] },
  have hss : F ⊂ F', from h.1.ssubset_of_ne (by { rintro rfl, simpa using h.2 }), 
  obtain ⟨e, heF', heF⟩ := exists_of_ssubset hss, 
  refine ⟨e, heF, ((M.flat_of_cl _).eq_of_r_le_r_subset_of_r_fin _ _ _).symm⟩, 
  { refine r_fin_of_r_ne_zero _, rw h.2, exact nat.succ_ne_zero _ },
  { exact hF'.cl_subset_of_subset (insert_subset.mpr ⟨heF', h.1⟩) },
  rw [h.2, r_cl, hF.r_insert_of_not_mem_of_r_fin heF hFfin], 
end 

lemma flat.covby_iff_r [finite_rk M] (hF : M.flat F) (hF' : M.flat F') : 
  M.covby F F' ↔ F ⊆ F' ∧ M.r F' = M.r F + 1 :=
hF.covby_iff_r_of_r_fin (M.to_r_fin F) hF'  

lemma hyperplane_iff_maximal_r [finite_rk M] : 
  M.hyperplane H ↔ M.r H < M.rk ∧ ∀ X, H ⊂ X → M.r X = M.rk :=
by simp_rw [hyperplane_iff_maximal_cl_ne_univ, lt_rk_iff_ne_rk, ne.def, ←r_eq_rk_iff_cl_eq_univ]

lemma hyperplane.r_add_one [finite_rk M] (hH : M.hyperplane H) : M.r H + 1 = M.rk :=
begin
  rw [hyperplane_iff_maximal_r] at hH,
  obtain (rfl | hne) := eq_or_ne H univ, 
  { exact (hH.1.ne rfl).elim },
  obtain ⟨e, he⟩ := (ne_univ_iff_exists_not_mem _).mp hne,
  refine (nat.lt_iff_add_one_le.mp hH.1).antisymm _,
  rw [←hH.2 (insert e H) (ssubset_insert he)],
  exact M.r_insert_le_add_one e H,  
end

lemma hyperplane.cast_r [finite_rk M] (hH : M.hyperplane H) : (M.r H : ℤ) = M.rk - 1 := 
by simp [←hH.r_add_one]

lemma flat.hyperplane_of_r_add_one_eq_rk [finite_rk M] (hF : M.flat F) (h : M.r F + 1 = M.rk) :
  M.hyperplane F :=
begin
  rw [hyperplane_iff_maximal_r, ←h, iff_true_intro (lt_add_one (M.r F)), true_and],
  refine λ X hFX, ((M.r_le_rk X).trans_eq h.symm).antisymm 
    (nat.add_one_le_iff.mpr (hF.r_lt_r_of_ssubset hFX)),  
end 

lemma hyperplane_iff_flat_r_add_one_eq_r [finite_rk M] : 
  M.hyperplane H ↔ M.flat H ∧ M.r H + 1 = M.rk :=
⟨λ h, ⟨h.flat, h.r_add_one⟩, λ h, h.1.hyperplane_of_r_add_one_eq_rk h.2⟩

end cl_flat

section loop

lemma loop_iff_r : M.loop e ↔ M.r {e} = 0 :=
begin
  rw [loop_iff_dep, indep_iff_r_eq_card_of_finite (finite_singleton e), ncard_singleton],
  refine ⟨λ h, nat.eq_zero_of_le_zero (nat.lt_succ_iff.mp _), 
    λ h h', (nat.zero_ne_one (h.symm.trans h'))⟩, 
  convert (M.r_le_card_of_finite (finite_singleton e)).lt_of_ne _,
  { rw ncard_singleton }, 
  rwa ncard_singleton,  
end 

lemma loop.r (he : M.loop e) : M.r {e} = 0 := loop_iff_r.mp he 

lemma r_eq_zero_iff_subset_loops [finite_rk M] : M.r X = 0 ↔ X ⊆ M.cl ∅ :=
(M.to_r_fin X).r_eq_zero_iff_subset_loops

lemma r_eq_zero_iff_forall_loop [finite_rk M] : M.r X = 0 ↔ ∀ e ∈ X, M.loop e :=
r_eq_zero_iff_subset_loops

lemma r_eq_zero_of_subset_loops (h : X ⊆ M.cl ∅) : M.r X = 0 := 
by rw [←r_cl, cl_eq_loops_of_subset h, r_cl, r_empty]

lemma nonloop_iff_r : M.nonloop e ↔ M.r {e} = 1 :=
by rw [←indep_singleton, indep_iff_r_eq_card_of_finite (finite_singleton e), ncard_singleton]

lemma nonloop.r (he : M.nonloop e) : M.r {e} = 1 := nonloop_iff_r.mp he 

lemma coloop.r_compl_add_one [finite_rk M] (he : M.coloop e) : M.r {e}ᶜ + 1 = M.rk :=
begin
  rw coloop_iff_forall_mem_base at he, 
  obtain ⟨I,hI⟩ := M.exists_basis {e}ᶜ,
  obtain ⟨B, hB, hIB⟩ := hI.indep.subset_basis_of_subset (subset_univ I),
  rw [←base_iff_basis_univ] at hB,
  have heI : e ∉ I, from λ heI, by simpa using hI.subset heI,
  have hIB' : B = insert e I,
  { refine subset_antisymm _ _,
    { rw [←union_singleton, ←inter_union_diff B {e}, union_subset_iff],
      refine ⟨(inter_subset_right _ _).trans (subset_union_right _ _),
        subset_union_of_subset_left _ _⟩,
      rw hI.eq_of_subset_indep (hB.indep.diff {e}) (subset_diff_singleton hIB heI) _,
      rw [compl_eq_univ_diff],
      exact diff_subset_diff_left (subset_univ _) },
    exact insert_subset.mpr ⟨he hB, hIB⟩},
  subst hIB',
  rw [←hI.r, hI.indep.r, ←hB.r, hB.indep.r, ncard_insert_of_not_mem heI hI.finite],
end

lemma coloop_iff_r_compl_add_one_eq [finite_rk M] : M.coloop e ↔ M.r {e}ᶜ + 1 = M.rk :=
begin
  refine ⟨coloop.r_compl_add_one, 
    (λ h, coloop_iff_forall_mem_base.mpr (λ B hB, by_contra (λ h', _)))⟩,
  rw ←subset_compl_singleton_iff at h',
  have hB' := M.r_mono h',
  rw [hB.r, ←h] at hB',
  simpa only [add_le_iff_nonpos_right, le_zero_iff, nat.one_ne_zero] using hB',
end

lemma coloop_iff_r_compl_lt [finite_rk M] : M.coloop e ↔ M.r {e}ᶜ < M.rk :=
begin
  refine ⟨λ h, _,λ h, _⟩,
  { rw ←h.r_compl_add_one, apply lt_add_one, },
  have he :insert e ({e}ᶜ : set E) = univ,
  {ext, simp [em]},
  rw [rk, ←he] at h,
  rw [coloop_iff_r_compl_add_one_eq, eq_comm, rk, ←he, r_insert_eq_add_one_of_r_ne h.ne.symm],
end

lemma coloop.coe_r_compl [finite_rk M] (he : M.coloop e) : (M.r {e}ᶜ : ℤ) = M.rk - 1 :=
by simp [←he.r_compl_add_one]

end loop 

section flat_of_r

variables {F F' P L : set E}

/-- `M.flat_of_r k F` means that `F` is a flat in `r` with finite rank `k`. -/
def flat_of_r (M : matroid E) (k : ℕ) (F : set E) := M.flat F ∧ M.r F = k ∧ M.r_fin F  

lemma flat_of_r.flat (h : M.flat_of_r k F) : M.flat F := h.1 

lemma flat_of_r.r (h : M.flat_of_r k F) : M.r F = k := h.2.1 

lemma flat_of_r.r_fin (h : M.flat_of_r k F) : M.r_fin F := h.2.2 

lemma flat.flat_of_r_of_ne_zero (hF : M.flat F) (hk : M.r F ≠ 0) : M.flat_of_r (M.r F) F :=
⟨hF, rfl, r_fin_of_r_ne_zero hk⟩  

lemma flat.flat_of_r_of_ne_zero' (hF : M.flat F) (hr : M.r F = k) (hk : k ≠ 0) : 
  M.flat_of_r (M.r F) F :=
hF.flat_of_r_of_ne_zero (by { subst hr, assumption } )   

lemma flat_of_r.nonempty (hF : M.flat_of_r k F) (hk : k ≠ 0) : F.nonempty := 
nonempty_of_r_nonzero (ne_of_eq_of_ne hF.r hk)

@[simp] lemma flat_of_r_zero_iff_loops : M.flat_of_r 0 F ↔ F = M.cl ∅ :=
begin
  refine ⟨λ h,_, _⟩,
  { obtain ⟨I, hI⟩ := M.exists_basis F, 
    have hc := hI.card, 
    rw [h.r, ncard_eq_zero (hI.finite_of_r_fin h.r_fin)] at hc, subst hc, 
    rw [←h.flat.cl, hI.cl] },
  rintro rfl, 
  exact ⟨M.flat_of_cl _, by simp, M.r_fin_empty.to_cl⟩,   
end

lemma loops_flat_of_r_zero (M : matroid E) : M.flat_of_r 0 (M.cl ∅) :=
by rw flat_of_r_zero_iff_loops

lemma flat_of_r.covby_iff (hF : M.flat_of_r k F) : M.covby F F' ↔ M.flat_of_r (k+1) F' ∧ F ⊆ F' :=
begin
  refine (em (M.flat F')).symm.elim (λ hF', iff_of_false (mt covby.flat_right hF') _) (λ hF', _), 
  { exact mt (λ h, h.1.flat) hF' },
  have hr := hF.r, subst hr, 
  simp_rw [hF.flat.covby_iff_r_of_r_fin hF.r_fin hF', flat_of_r, and_comm, and.congr_right_iff, 
    ← and_assoc, iff_and_self, and_iff_right hF'], 
  refine λ h hF', r_fin_of_r_ne_zero _, 
  rw hF', 
  simp,  
end 

lemma flat_of_r.flat_of_r_add_one_of_covby (hF : M.flat_of_r k F) (hFF' : M.covby F F') : 
  M.flat_of_r (k+1) F' := 
by { rw [hF.covby_iff] at hFF', exact hFF'.1 }

/-- A `point` is a rank-one flat -/
def point (M : matroid E) (P : set E) := M.flat_of_r 1 P 

/-- A `line` is a rank-two flat -/
def line (M : matroid E) (L : set E) := M.flat_of_r 2 L

/-- A `plane` is a rank-three flat -/
def plane (M : matroid E) (P : set E) := M.flat_of_r 3 P

lemma point.nonempty (hP : M.point P) : P.nonempty := flat_of_r.nonempty hP one_ne_zero

lemma line.nonempty (hL : M.line L) : L.nonempty := flat_of_r.nonempty hL two_ne_zero

lemma plane.nonempty (hP : M.plane P) : P.nonempty := flat_of_r.nonempty hP three_pos.ne.symm 

lemma nonloop.cl_point (he : M.nonloop e) : M.point (M.cl {e}) := 
begin
  rw [point, ←ncard_singleton e, ←he.indep.r, ←r_cl ],
  exact (M.flat_of_cl _).flat_of_r_of_ne_zero (by { rw [r_cl, he.indep.r], simp }), 
end

lemma point.diff_loops_nonempty (hP : M.point P) : (P \ M.cl ∅).nonempty := 
nonempty_of_r_nonzero (by { rw [←r_cl, cl_diff_loops_eq_cl, r_cl, hP.r], exact one_ne_zero })

lemma point.exists_eq_cl_nonloop (hP : M.point P) : ∃ e, M.nonloop e ∧ P = M.cl {e} := 
begin
  obtain ⟨I, hI⟩ := M.exists_basis P,
  have hc := hI.card, 
  rw [hP.r, ncard_eq_one] at hc, 
  obtain ⟨e, rfl⟩ := hc, 
  use e, 
  rw [hI.cl, hP.flat.cl, and_iff_left rfl, nonloop_iff_r, hI.r, hP.r], 
end 

lemma point.eq_cl_nonloop (hP : M.point P) (heP : e ∈ P) (he : M.nonloop e) : P = M.cl {e} := 
begin
  obtain ⟨I, hI, heI⟩ := he.indep.subset_basis_of_subset (singleton_subset_iff.mpr heP), 
  have hc := hI.card, 
  rw [hP.r, ncard_eq_one] at hc,  
  obtain ⟨e', rfl⟩ := hc, 
  simp only [subset_singleton_iff, mem_singleton_iff, forall_eq] at heI, 
  rw [←hP.flat.cl, ←hI.cl, heI], 
end 

/-- The set of elements that span a point are precisely its nonloop members -/
lemma point.eq_cl_singleton_iff (h : M.point P) : M.cl {e} = P ↔ e ∈ P ∧ M.nonloop e :=
begin
  simp only [nonloop, loop, ←mem_diff,  mem_preimage, mem_singleton_iff], 
  refine ⟨_, λ hP, _⟩,
  { rintro rfl, 
    refine ⟨M.mem_cl_self e, λ (he : M.loop e), he.dep _⟩,
    have hr := h.r, 
    rwa [r_cl, ←ncard_singleton e, ←indep_iff_r_eq_card_of_finite (finite_singleton e)] at hr },
  have he : M.nonloop e := hP.2, 
  obtain ⟨J, hJ, heJ⟩ :=  he.indep.subset_basis_of_subset (singleton_subset_iff.mpr hP.1), 
  have hJcard := hJ.card, 
  rw [h.r, ncard_eq_one] at hJcard, 
  obtain ⟨e', rfl⟩ := hJcard, 
  simp only [subset_singleton_iff, mem_singleton_iff, forall_eq] at heJ, subst heJ,   
  rw [←h.flat.cl, hJ.cl], 
end 

lemma point_iff_loops_covby : M.point P ↔ M.covby (M.cl ∅) P := 
begin
  rw [flat_of_r.covby_iff M.loops_flat_of_r_zero, zero_add, point, iff_self_and],  
  exact λ h, h.flat.loops_subset,  
end

end flat_of_r

section from_axioms

/-- There doesn't seem to be a nice way to axiomatize finite-rank matroids on infinite ground sets 
  without a 'bases for sets exist'-type axiom. A troublesome example is the rank-1 non-matroid where 
  the only rank-1 set is the (infinite) ground set, which satisfies finite versions of submodularity
  but has no nonempty independent sets.  -/

lemma card_le_r_of_card_le_r_of_subset [finite E] (r : set E → ℕ) (r_le_card : ∀ X, r X ≤ X.ncard)
(r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) {I J : set E} 
(hJ : J.ncard ≤ r J) (hIJ : I ⊆ J) :
  I.ncard ≤ r I :=
begin
  have hsm := r_submod I (J \ I), 
  rw [inter_diff_self, union_diff_self, union_eq_self_of_subset_left hIJ] at hsm,  
  linarith [r_le_card (J \ I), ncard_diff_add_ncard_eq_ncard hIJ], 
end    

lemma r_eq_r_of_maximal_indep [finite E] (r : set E → ℕ) (r_le_card : ∀ X, r X ≤ X.ncard)
(r_mono : ∀ ⦃X Y⦄, X ⊆ Y → r X ≤ r Y) (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) 
(I X : set E) (hI : I ∈ maximals (⊆) {J | J ⊆ X ∧ J.ncard ≤ r J}) : 
  r I = r X :=
begin  
  obtain ⟨J, ⟨hJX, hIJ, hJ⟩, hJmax⟩ :=
    (to_finite X).maximals_nonempty_of_exists (λ J, I ⊆ J ∧ r J ≤ r I) hI.1.1 ⟨subset.rfl, rfl.le⟩,  
  obtain (rfl | hss) := hJX.eq_or_ssubset, 
  { exact hJ.antisymm' (r_mono hIJ) },
  obtain ⟨e, heX, heJ⟩ := exists_of_ssubset hss, 
  have hsm := r_submod (insert e I) J, 
  rw [insert_union, union_eq_self_of_subset_left hIJ] at hsm, 
  have heI : r (insert e I) ≤ r I,
  { refine (em (e ∈ I)).elim (λ heI, by rw insert_eq_of_mem heI) (λ heI, le_of_not_lt (λ hlt, _)),
    refine heI (hI.2 ⟨insert_subset.mpr ⟨heX, hI.1.1⟩, _⟩ (subset_insert e I) (mem_insert e I)),
    linarith [hI.1.2, nat.lt_iff_add_one_le.mp hlt, ncard_insert_of_not_mem heI] },
  have heJ : r I + 1 ≤ r (insert e J), 
  { refine nat.add_one_le_iff.mpr (lt_of_not_le (λ hle, heJ _)), 
    exact (hJmax ⟨insert_subset.mpr ⟨heX, hss.subset⟩, ⟨hIJ.trans (subset_insert e J), hle⟩⟩ 
      (subset_insert e J) (mem_insert e J)) },
  linarith [r_mono (subset_inter (subset_insert e I) hIJ)], 
end 

def matroid_of_r [finite E] (r : set E → ℕ) (r_le_card : ∀ X, r X ≤ X.ncard)
(r_mono : ∀ ⦃X Y⦄, X ⊆ Y → r X ≤ r Y) (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) : 
  matroid E :=
matroid_of_indep_of_finite (λ I, I.ncard ≤ r I) (by { use ∅, simp,   })   
(λ I J, card_le_r_of_card_le_r_of_subset r ‹_› ‹_›)
(begin
  intros I J hI hJ hIJ, 
  by_contra' h', 
  have con := r_eq_r_of_maximal_indep r ‹_› ‹_› ‹_› I (I ∪ J) ⟨⟨subset_union_left _ _, hI⟩, _⟩,     
  { exact (r_le_card I).not_lt 
      ((hIJ.trans_le (hJ.trans (r_mono (subset_union_right I J)))).trans_eq con.symm) },
  exact λ K hK hIK e heK, by_contra (λ heI, 
    ((card_le_r_of_card_le_r_of_subset r ‹_› ‹_› hK.2 (insert_subset.mpr ⟨heK, hIK⟩)).not_lt 
      (h' _ ((hK.1 heK).elim (false.elim ∘ heI) id) heI ))), 
end) 

@[simp] lemma matroid_of_r_apply [finite E] (r : set E → ℕ) (r_le_card : ∀ X, r X ≤ X.ncard)
(r_mono : ∀ ⦃X Y⦄, X ⊆ Y → r X ≤ r Y) (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) :
(matroid_of_r r r_le_card r_mono r_submod).r  = r :=
begin
  ext X, 
  obtain ⟨I, hI⟩ := (matroid_of_r r ‹_› ‹_› ‹_›).exists_basis X, 
  rw [←hI.card], 
  simp_rw [matroid_of_r, basis_iff, matroid_of_indep_of_finite_apply] at hI,  
  rw [hI.1.antisymm (r_le_card I), r_eq_r_of_maximal_indep r ‹_› ‹_› ‹_›], 
  exact ⟨⟨hI.2.1,hI.1⟩, λ J hJ hIJ, (hI.2.2 J hJ.2 hIJ hJ.1).symm.subset⟩
end 

/-- Construction of a matroid from an `int`-valued rank function that is everywhere nonnegative,
  rather than a `nat`-valued one. Useful for defining matroids whose rank function involves
  subtraction. -/
def matroid_of_int_r [finite E] (r : set E → ℤ) (r_nonneg : ∀ X, 0 ≤ r X) 
(r_le_card : ∀ X, r X ≤ X.ncard) (r_mono : ∀ X Y, X ⊆ Y → r X ≤ r Y) 
(r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) :
  matroid E :=
matroid_of_r (int.nat_abs ∘ r)
  (λ X, by {zify, convert r_le_card X, rw abs_eq_self, apply r_nonneg})
  (λ X Y hXY, by {zify, convert r_mono X Y hXY, all_goals {rw abs_eq_self, apply r_nonneg}})
  (λ X Y, by {zify, convert r_submod X Y, all_goals {rw abs_eq_self, apply r_nonneg}})

@[simp] lemma matroid_of_int_r_apply [finite E] (r : set E → ℤ) (r_nonneg : ∀ X, 0 ≤ r X)
(r_le_card : ∀ X, r X ≤ X.ncard) (r_mono : ∀ X Y, X ⊆ Y → r X ≤ r Y)
(r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) (X : set E) :
  ((matroid_of_int_r r r_nonneg r_le_card r_mono r_submod).r X : ℤ) = r X :=
by simpa [matroid_of_int_r] using r_nonneg _

end from_axioms

section dual

variables [finite E]

lemma coindep_iff_r : M.coindep X ↔ M.r Xᶜ = M.rk :=
begin
  rw [coindep_iff_disjoint_base],
  split,
  { rintros ⟨B,hB,hBX⟩,
    refine le_antisymm (M.r_le_rk _) _,
    rw ←subset_compl_iff_disjoint_left at hBX,
    rw [←hB.r],
    exact M.r_mono hBX },
  intro hr,
  obtain ⟨B, hB⟩ := M.exists_basis Xᶜ,
  refine ⟨B, hB.indep.base_of_rk_le_card _, subset_compl_iff_disjoint_left.mp hB.subset⟩,
  rw [←hB.indep.r, hB.r, hr],
end

lemma dual_r_add_rk_eq (M : matroid E) (X : set E) : M﹡.r X + M.rk = ncard X + M.r Xᶜ  :=
begin
  set r' : set E → ℤ := λ X, X.ncard + M.r Xᶜ - M.rk with hr',

  have hr'_nonneg : ∀ X, 0 ≤ r' X,
  { intro X, simp_rw hr', linarith [M.rk_le_card_add_r_compl X]},
  have hr'_mono : ∀ X Y, X ⊆ Y → r' X ≤ r' Y,
  { intros X Y hXY, simp_rw hr',
    linarith [M.r_add_card_le_r_add_card_of_subset (compl_subset_compl.mpr hXY),
       ncard_add_ncard_compl X, ncard_add_ncard_compl Y]},
  have hr'_le_card : ∀ X, r' X ≤ X.ncard,
  { intros X, simp_rw hr', linarith [M.r_le_rk Xᶜ] },
  have hr'_submod : ∀ X Y, r' (X ∩ Y) + r' (X ∪ Y) ≤ r' X + r' Y,
  { intros X Y, simp_rw [hr', compl_inter, compl_union],
    linarith [ncard_inter_add_ncard_union X Y, M.r_submod Xᶜ Yᶜ]},

  set M' := matroid_of_int_r r' hr'_nonneg hr'_le_card hr'_mono hr'_submod with hM',

  have hM'M : M' = M﹡,
  { refine eq_of_indep_iff_indep_forall (λ I, _),
    rw [indep_iff_r_eq_card, dual_indep_iff_coindep, coindep_iff_r], zify,
    simp_rw [hM', matroid_of_int_r_apply, hr'],
    refine ⟨λ h, _, λ h, _⟩,
    all_goals { simp only at h, linarith} },

  rw [←hM'M], zify, simp_rw [hM', matroid_of_int_r_apply, hr'],
  ring,
end

lemma dual_r_cast_eq (M : matroid E) (X : set E) : (M﹡.r X : ℤ) = ncard X + M.r Xᶜ - M.rk :=
by linarith [M.dual_r_add_rk_eq X]

end dual 

end matroid 
import .loop
import .flat' 
import mathlib.data.set.ncard

/- The rank of a set in a matroid `M` is the size of one of its bases. When such bases are infinite, 
  this quantity is not defined in general, so rank is not very useful when building API for 
  general matroids, even though it is often the easiest way to do things for finite matroids. 

  A good number of rank lemmas have both `r_fin` versions, for sets of finite rank in a matroid
  of potentially infinite rank, and `[finite_rk M]` version, which apply in the more commonly 
  considered case where the entire matroid has finite rank, and are implied by the `r_fin` version. 
   -/
 
noncomputable theory
open_locale classical

open set

namespace matroid_in

variables {α : Type*} {M : matroid_in α}  {B X Y X' Y' Z I J : set α} {e f x y z : α} {k n : ℕ}

section basic 
/-- The rank `r X` of a set `X` is the cardinality of one of its bases, or zero if its bases are 
  infinite -/
def er {α : Type*} (M : matroid_in α) (X : set α) : ℕ∞ :=
  ⨅ (I : {I | M.basis I (X ∩ M.E)}), encard (I : set α)

def erk (M : matroid_in α) := M.er M.E 

lemma erk_def {α : Type*} (M : matroid_in α) : M.erk = M.er M.E := rfl

lemma basis.encard_of_inter_ground (hI : M.basis I (X ∩ M.E)) : I.encard = M.er X :=
begin
  have hrw : ∀ J : {J : set α | M.basis J (X ∩ M.E)}, (J : set α).encard = I.encard,
  { rintro ⟨J, hJ⟩, exact (hI.encard_eq_encard_of_basis hJ).symm },
  haveI : nonempty {J : set α | M.basis J (X ∩ M.E)}, 
    from let ⟨I,hI⟩ := M.exists_basis (X ∩ M.E) in ⟨⟨I,hI⟩⟩,
  simp_rw [er, hrw, cinfi_const], 
end 

lemma basis.encard (hI : M.basis I X) : I.encard = M.er X := 
hI.basis_inter_ground.encard_of_inter_ground 

lemma eq_er_iff {n : ℕ∞} (hX : X ⊆ M.E . ssE) : M.er X = n ↔ ∃ I, M.basis I X ∧ I.encard = n :=
begin
  obtain ⟨I, hI⟩ := M.exists_basis X, 
  rw [←hI.encard], 
  refine ⟨λ h, ⟨I, hI, h⟩, _⟩,
  rintro ⟨J, hJ, rfl⟩, 
  rw [hI.encard, hJ.encard], 
end  

lemma indep.er (hI : M.indep I) : M.er I = I.encard := eq_er_iff.mpr ⟨I, hI.basis_self, rfl⟩

lemma basis.er (hIX : M.basis I X) : M.er I = M.er X := 
by rw [←hIX.encard, hIX.indep.er]

lemma basis.er_eq_encard (hIX : M.basis I X) : M.er X = I.encard :=
by rw [←hIX.er, hIX.indep.er]

lemma base.er (hB : M.base B) : M.er B = M.erk := 
by { rw base_iff_basis_ground at hB, rw [hB.er, erk] }

lemma base.encard (hB : M.base B) : B.encard = M.erk := 
by rw [(base_iff_basis_ground.mp hB).encard, erk]

lemma er_eq_er_inter_ground (M : matroid_in α) (X : set α) : M.er X = M.er (X ∩ M.E) :=
by { obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E), rwa [←hI.encard_of_inter_ground, ←basis.encard] }

@[simp] lemma er_empty (M : matroid_in α) : M.er ∅ = 0 := 
by rw [←M.empty_indep.basis_self.encard, encard_empty]

@[simp] lemma er_cl (M : matroid_in α) (X : set α) : M.er (M.cl X) = M.er X :=
begin
  rw [cl_eq_cl_inter_ground, M.er_eq_er_inter_ground X], 
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E), 
  rw [←hI.er, ←hI.cl, hI.indep.basis_cl.er], 
end 

@[simp] lemma er_union_cl_right_eq (M : matroid_in α) (X Y : set α) :
  M.er (X ∪ M.cl Y) = M.er (X ∪ Y) :=
by rw [←er_cl, cl_union_cl_right_eq, er_cl]

@[simp] lemma er_union_cl_left_eq (M : matroid_in α) (X Y : set α) :
  M.er (M.cl X ∪ Y) = M.er (X ∪ Y) :=
by rw [←er_cl, cl_union_cl_left_eq, er_cl]

@[simp] lemma er_insert_cl_eq (M : matroid_in α) (e : α) (X : set α) : 
  M.er (insert e (M.cl X)) = M.er (insert e X) :=
by rw [← union_singleton, er_union_cl_left_eq, union_singleton]

lemma er_lt_top_of_finite (M : matroid_in α) (hX : X.finite) : M.er X < ⊤ :=
begin
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E), 
  rw [er_eq_er_inter_ground, ←hI.encard, encard_lt_top_iff_finite], 
  exact hX.subset (hI.subset.trans (inter_subset_left _ _)), 
end 

@[simp] lemma er_union_cl_right_eq_er_union (M : matroid_in α) (X Y : set α) :
  M.er (X ∪ M.cl Y) = M.er (X ∪ Y) :=
by rw [←er_cl, cl_union_cl_right_eq, er_cl]

@[simp] lemma er_union_cl_left_eq_er_union (M : matroid_in α) (X Y : set α) :
  M.er (M.cl X ∪ Y) = M.er (X ∪ Y) :=
by rw [←er_cl, cl_union_cl_left_eq, er_cl]

@[simp] lemma er_insert_cl_eq_er_insert (M : matroid_in α) (e : α) (X : set α) : 
  M.er (insert e (M.cl X)) = M.er (insert e X) :=
by rw [← union_singleton, er_union_cl_left_eq_er_union, union_singleton]

lemma basis.er_eq_er_union (hIX : M.basis I X) (Y : set α) : M.er (I ∪ Y) = M.er (X ∪ Y) :=
begin
  rw [←er_union_cl_right_eq_er_union, ←er_union_cl_right_eq_er_union _ _ Y], 
  obtain ⟨I', hI', hII'⟩ :=
    hIX.indep.subset_basis_of_subset (hIX.subset.trans (subset_union_left _ (M.cl Y))), 
  rw [←hI'.er, ← (hI'.basis_subset _ (union_subset_union_left _ hIX.subset)).er],   
  refine λ e he, (hI'.subset he).elim (λ heX, or.inl _) (λ heY, subset_union_right _ _ heY), 
  exact hIX.mem_of_insert_indep heX (hI'.indep.subset (insert_subset.mpr ⟨he, hII'⟩)), 
end

lemma basis.er_eq_er_insert (hIX : M.basis I X) (e : α) : M.er (insert e I) = M.er (insert e X) :=
by rw [←union_singleton, hIX.er_eq_er_union, union_singleton]

lemma er_le_encard (M : matroid_in α) (X : set α) : M.er X ≤ X.encard := 
begin
  rw [er_eq_er_inter_ground], 
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E), 
  rw ←hI.encard, 
  exact encard_subset_le (hI.subset.trans (inter_subset_left _ _)), 
end 

lemma erk_le_encard_ground (M : matroid_in α) : M.erk ≤ M.E.encard :=
M.er_le_encard M.E 

lemma er_mono (M : matroid_in α) : monotone M.er := 
begin
  rintro X Y (h : X ⊆ Y), 
  rw [er_eq_er_inter_ground, M.er_eq_er_inter_ground Y], 
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E), 
  obtain ⟨J, hJ, hIJ⟩ :=
    hI.indep.subset_basis_of_subset (hI.subset.trans (inter_subset_inter_left M.E h)), 
  rw [←hI.encard, ←hJ.encard], 
  exact encard_mono hIJ,
end 

lemma indep.encard_le_er_of_subset (hI : M.indep I) (hIX : I ⊆ X) : I.encard ≤ M.er X :=
by { rw [←hI.er], exact M.er_mono hIX }

lemma le_er_iff {n : ℕ∞} : n ≤ M.er X ↔ ∃ I ⊆ X, M.indep I ∧ I.encard = n :=
begin
  rw [er_eq_er_inter_ground], 
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E), 
  rw [←hI.encard], 
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨I', hI', rfl⟩ := exists_subset_encard_eq h, 
    exact ⟨I', hI'.trans (hI.subset.trans (inter_subset_left _ _)), hI.indep.subset hI', rfl⟩ },
  obtain ⟨J, hJX, hJ, rfl⟩ := h, 
  exact hJ.le_encard_basis (subset_inter hJX hJ.subset_ground) hI, 
end 

lemma er_le_iff {n : ℕ∞} : M.er X ≤ n ↔ (∀ I ⊆ X, M.indep I → I.encard ≤ n) :=
begin
  refine ⟨λ h I hIX hI, (hI.encard_le_er_of_subset hIX).trans h, λ h, _⟩,
  obtain ⟨J, hJ⟩ := M.exists_basis (X ∩ M.E), 
  rw [er_eq_er_inter_ground, ←hJ.encard], 
  exact h J (hJ.subset.trans (inter_subset_left _ _)) hJ.indep, 
end 

/-- The submodularity axiom for the extended rank function -/
lemma er_inter_add_er_union_le_er_add_er (M : matroid_in α) (X Y : set α) :
  M.er (X ∩ Y) + M.er (X ∪ Y) ≤ M.er X + M.er Y :=
begin
  rw [er_eq_er_inter_ground, M.er_eq_er_inter_ground (_ ∪ _), M.er_eq_er_inter_ground X, 
    M.er_eq_er_inter_ground Y, inter_inter_distrib_right, inter_distrib_right], 
  obtain ⟨Ii, hIi⟩ := M.exists_basis ((X ∩ M.E) ∩ (Y ∩ M.E)),
  obtain ⟨IX, hIX, hIX'⟩ := 
    hIi.indep.subset_basis_of_subset (hIi.subset.trans (inter_subset_left _ _)), 
  obtain ⟨IY, hIY, hIY'⟩ := 
    hIi.indep.subset_basis_of_subset (hIi.subset.trans (inter_subset_right _ _)), 
  rw [←hIX.er_eq_er_union, union_comm, ←hIY.er_eq_er_union, ←hIi.encard, ←hIX.encard, ←hIY.encard, 
    union_comm, ←encard_union_add_encard_inter, add_comm], 
  exact add_le_add (er_le_encard _ _) (encard_mono (subset_inter hIX' hIY')), 
end

lemma er_eq_er_of_subset_le (hXY : X ⊆ Y) (hYX : M.er Y ≤ M.er X) : 
  M.er X = M.er Y := (M.er_mono hXY).antisymm hYX

alias er_inter_add_er_union_le_er_add_er ← er_submod 

lemma er_union_le_er_add_er (M : matroid_in α) (X Y : set α) : M.er (X ∪ Y) ≤ M.er X + M.er Y :=
le_add_self.trans (M.er_submod X Y)

lemma er_eq_zero_iff_subset_loops (hX : X ⊆ M.E . ssE) : M.er X = 0 ↔ X ⊆ M.cl ∅ :=
begin
  obtain ⟨I, hI⟩ := M.exists_basis X, 
  rw [←hI.encard, encard_eq_zero], 
  refine ⟨_, λ h, _⟩,
  { rintro rfl, exact hI.subset_cl },
  simpa using hI.indep.encard_le_er_of_subset (hI.subset.trans h),  
end 

lemma er_eq_er_union_er_le_zero (X : set α) (hY : M.er Y ≤ 0) : M.er (X ∪ Y) = M.er X :=
(((M.er_union_le_er_add_er X Y).trans (add_le_add_left hY _)).trans_eq (add_zero _)).antisymm 
  (M.er_mono (subset_union_left _ _))
  
lemma er_eq_er_diff_er_le_zero (X : set α) (hY : M.er Y ≤ 0) : M.er (X \ Y) = M.er X :=
by rw [←er_eq_er_union_er_le_zero (X \ Y) hY, diff_union_self, er_eq_er_union_er_le_zero _ hY]

lemma er_le_er_inter_add_er_diff (X Y : set α) : M.er X ≤ M.er (X ∩ Y) + M.er (X \ Y) :=
by { nth_rewrite 0 ←inter_union_diff X Y, apply er_union_le_er_add_er }

lemma er_le_er_add_er_diff (h : Y ⊆ X) : M.er X ≤ M.er Y + M.er (X \ Y) :=
by { nth_rewrite 0 ←union_diff_cancel h, apply er_union_le_er_add_er }

lemma indep_iff_er_eq_encard_of_finite (hI : I.finite) :
  M.indep I ↔ M.er I = I.encard :=
begin
  refine ⟨indep.er, λ h, _⟩,
  obtain ⟨J, hJ⟩ := M.exists_basis (I ∩ M.E), 
  have hJI : J ⊆ I := hJ.subset.trans (inter_subset_left _ _), 
  rw [hI.encard_eq, er_eq_er_inter_ground, ←hJ.encard, (hI.subset hJI).encard_eq, 
    nat.cast_inj] at h, 
  rw ←eq_of_subset_of_ncard_le hJI h.symm.le hI, 
  exact hJ.indep, 
end

lemma er_singleton_le (M : matroid_in α) (e : α) : M.er {e} ≤ 1 :=
by { rw [er_le_iff], exact λ I hI _, (encard_mono hI).trans_eq (encard_singleton e) }

lemma indep_iff_er_eq_card [finite M] (hI : I ⊆ M.E . ssE) : 
  M.indep I ↔ M.er I = I.encard :=
indep_iff_er_eq_encard_of_finite (M.set_finite I)
  
lemma er_lt_encard_of_dep_of_finite (h : X.finite) (hX : M.dep X) : 
  M.er X < X.encard :=
lt_of_le_of_ne (M.er_le_encard X) 
  (λ h', ((indep_iff_er_eq_encard_of_finite h).mpr h').not_dep hX)

lemma er_lt_encard_iff_dep_of_finite (hX : X.finite) (hXE : X ⊆ M.E . ssE) : 
  M.er X < X.encard ↔ M.dep X := 
begin
  rw [←not_iff_not, not_lt, not_dep_iff, indep_iff_er_eq_encard_of_finite hX, 
    le_iff_eq_or_lt, eq_comm, or_iff_left],  
  rw [not_lt], 
  apply er_le_encard, 
end 

lemma er_lt_encard_of_dep [finite M] (hX : M.dep X) : M.er X < X.encard :=
er_lt_encard_of_dep_of_finite (M.set_finite _) hX 

lemma r_lt_card_iff_dep [finite M] (hXE : X ⊆ M.E . ssE) : 
  M.er X < X.encard ↔ M.dep X :=
er_lt_encard_iff_dep_of_finite (M.set_finite X)

lemma basis_iff_indep_encard_eq_of_finite (hIfin : I.finite) (hXE : X ⊆ M.E . ssE) :
  M.basis I X ↔ I ⊆ X ∧ M.indep I ∧ I.encard = M.er X :=
begin
  rw [basis_iff_indep_cl, and_comm (I ⊆ X), ←and_assoc, and.congr_left_iff, and.congr_right_iff], 
  refine λ hIX hI, ⟨λ h, (hI.encard_le_er_of_subset hIX).antisymm _, λ h, _⟩, 
  { refine (M.er_mono h).trans _, 
    rw [er_cl, hI.er], exact rfl.le }, 
  intros e he, 
  rw [hI.mem_cl_iff (hXE he)], 
  refine λ hi, by_contra (λ he', _), 
  have hr := hi.er, rw [encard_insert_of_not_mem he'] at hr, 
  have hle := M.er_mono (insert_subset.mpr ⟨he, hIX⟩), 
  rw [hr, ←h, hIfin.encard_eq, ←nat.cast_one, ←nat.cast_add, nat.cast_le] at hle, 
  simpa using hle, 
end  

lemma indep.basis_of_subset_of_er_le_of_finite (hI : M.indep I) (hIX : I ⊆ X) 
(h : M.er X ≤ M.er I) (hIfin : I.finite) (hX : X ⊆ M.E . ssE) : M.basis I X :=
begin
  rw [basis_iff_indep_encard_eq_of_finite hIfin hX, and_iff_right hIX, and_iff_right hI, 
    le_antisymm_iff, and_iff_left (h.trans hI.er.le)],
  exact hI.encard_le_er_of_subset hIX,
end 

lemma er_insert_le_add_one (M : matroid_in α) (e : α) (X : set α) : 
  M.er (insert e X) ≤ M.er X + 1 :=
begin
  rw [←union_singleton], 
  exact (M.er_union_le_er_add_er _ _).trans (add_le_add_left (er_singleton_le _ _) _), 
end 

lemma er_union_le_encard_add_er (M : matroid_in α) (X Y : set α) : 
  M.er (X ∪ Y) ≤ X.encard + M.er Y :=
(M.er_union_le_er_add_er X Y).trans (add_le_add_right (M.er_le_encard _) _)

lemma er_union_le_er_add_encard (M : matroid_in α) (X Y : set α) :
  M.er (X ∪ Y) ≤ M.er X + Y.encard :=
(M.er_union_le_er_add_er X Y).trans (add_le_add_left (M.er_le_encard _) _)

lemma erk_le_encard_add_er_compl (M : matroid_in α) (X : set α) :
  M.erk ≤ X.encard + M.er (M.E \ X) :=
begin
  refine le_trans _ (M.er_union_le_encard_add_er X (M.E \ X)), 
  rw [erk_def, union_diff_self, M.er_eq_er_inter_ground (X ∪ M.E), union_inter_cancel_right], 
  exact rfl.le, 
end

lemma er_augment (h : M.er X < M.er Z) : ∃ z ∈ Z \ X, M.er (insert z X) = M.er X + 1 :=
begin
  rw [M.er_eq_er_inter_ground Z, M.er_eq_er_inter_ground] at h, 
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E),
  obtain ⟨J, hJ⟩ := M.exists_basis (Z ∩ M.E), 
  obtain ⟨z, hzJ, hzI, h⟩ := hI.indep.augment_of_encard_lt hJ.indep (by rwa [hI.encard, hJ.encard]),   
  refine ⟨z, ⟨(hJ.subset hzJ).1, hzI ∘ (λ hzX, _)⟩, _⟩, 
  { exact hI.mem_of_insert_indep ⟨hzX, hJ.indep.subset_ground hzJ⟩ h },
  rw [←er_insert_cl_eq_er_insert, cl_eq_cl_inter_ground, ←hI.cl, er_insert_cl_eq_er_insert, 
    h.er, er_eq_er_inter_ground, ←hI.encard, encard_insert_of_not_mem hzI], 
end 

lemma er_eq_of_er_insert_le_forall (hXY : X ⊆ Y) (hY : ∀ e ∈ Y \ X, M.er (insert e X) ≤ M.er X) :
  M.er X = M.er Y :=
begin
  refine (M.er_mono hXY).antisymm (le_of_not_lt (λ hlt, _)), 
  obtain ⟨z, hz, hr⟩ := er_augment hlt, 
  have hle := hY z hz, 
  rw [hr] at hle, 
  have := enat.eq_of_top_of_add_pos_le (by simp) hle, 
  rw [this] at hlt, 
  exact not_top_lt hlt, 
end 

end basic

section r_fin

def r_fin (M : matroid_in α) (X : set α) := M.er X < ⊤ 

lemma r_fin_iff_er_ne_top : M.r_fin X ↔ M.er X ≠ ⊤ := 
by rw [r_fin, ←lt_top_iff_ne_top]

lemma r_fin_iff_er_lt_top : M.r_fin X ↔ M.er X < ⊤ := 
iff.rfl 

lemma r_fin.ne (h : M.r_fin X) : M.er X ≠ ⊤ := 
(r_fin_iff_er_ne_top.mp h) 

lemma r_fin.lt (h : M.r_fin X) : M.er X < ⊤ := 
h

lemma not_r_fin_iff : ¬ M.r_fin X ↔ M.er X = ⊤ :=
by rw [r_fin_iff_er_ne_top, not_ne_iff]

lemma r_fin_iff_inter_ground : M.r_fin X ↔ M.r_fin (X ∩ M.E) := 
by rw [r_fin, er_eq_er_inter_ground, r_fin]

lemma r_fin.to_inter_ground (h : M.r_fin X) : M.r_fin (X ∩ M.E) := 
r_fin_iff_inter_ground.mp h 

lemma r_fin.finite_of_basis (h : M.r_fin X) (hI : M.basis I X) : I.finite :=
by rwa [←encard_lt_top_iff_finite, hI.encard] 

lemma basis.finite_of_r_fin (hI : M.basis I X) (h : M.r_fin X) : I.finite :=
h.finite_of_basis hI 

lemma r_fin_iff' : M.r_fin X ↔ ∃ I, M.basis I (X ∩ M.E) ∧ I.finite :=
begin  
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E), 
  rw [r_fin_iff_er_ne_top, er_eq_er_inter_ground, ←hI.encard, encard_ne_top_iff_finite], 
  exact ⟨λ h, ⟨I, hI, h⟩, λ ⟨J, hJ, hJfin⟩, hJ.finite_of_finite hJfin hI⟩, 
end 

lemma r_fin_iff_exists_finite_basis (hX : X ⊆ M.E . ssE) : 
  M.r_fin X ↔ ∃ I, M.basis I X ∧ I.finite :=
by simp_rw [r_fin_iff', inter_eq_self_of_subset_left hX]

lemma r_fin.exists_finite_basis (h : M.r_fin X) (hX : X ⊆ M.E . ssE) :
  ∃ I, M.basis I X ∧ I.finite := 
(M.exists_basis X).imp (λ I hI, ⟨hI, h.finite_of_basis hI⟩)

lemma basis.r_fin_of_finite (hIX : M.basis I X) (h : I.finite) : M.r_fin X := 
by rwa [r_fin_iff_er_ne_top, ←hIX.encard, encard_ne_top_iff_finite]

lemma basis.r_fin_iff_finite (hIX : M.basis I X) : M.r_fin X ↔ I.finite := 
⟨hIX.finite_of_r_fin, hIX.r_fin_of_finite⟩

lemma indep.r_fin_iff_finite (hI : M.indep I) : M.r_fin I ↔ I.finite := 
hI.basis_self.r_fin_iff_finite 

lemma indep.finite_of_r_fin (hI : M.indep I) (hfin : M.r_fin I) : I.finite := 
hI.basis_self.finite_of_r_fin hfin   

lemma indep.subset_finite_basis_of_subset_of_r_fin (hI : M.indep I) (hIX : I ⊆ X) (hX : M.r_fin X) 
(hXE : X ⊆ M.E . ssE) :
∃ J, M.basis J X ∧ I ⊆ J ∧ J.finite :=
(hI.subset_basis_of_subset hIX).imp (λ J hJ, ⟨hJ.1, hJ.2, hJ.1.finite_of_r_fin hX⟩)

lemma r_fin_of_finite (M : matroid_in α) (hX : X.finite) : M.r_fin X := 
by { rw [r_fin_iff_er_lt_top], exact (M.er_le_encard X).trans_lt (encard_lt_top_iff_finite.mpr hX) }

lemma r_fin_singleton (M : matroid_in α) (e : α) : M.r_fin {e} := 
M.r_fin_of_finite (finite_singleton e)
 
@[simp] lemma r_fin_empty (M : matroid_in α) : M.r_fin ∅ := M.r_fin_of_finite finite_empty

lemma r_fin.subset (h : M.r_fin Y) (hXY : X ⊆ Y) : M.r_fin X := 
by { rw [r_fin_iff_er_lt_top] at ⊢ h, exact (M.er_mono hXY).trans_lt h }

lemma not_r_fin_supset (h : ¬ M.r_fin X) (hXY : X ⊆ Y) : ¬ M.r_fin Y := 
λ h', h (h'.subset hXY)

lemma not_r_fin_of_er_ge (h : ¬ M.r_fin X) (hXY : M.er X ≤ M.er Y) : ¬ M.r_fin Y :=
λ h', h (hXY.trans_lt h') 
 
lemma r_fin.finite_of_indep_subset (hX : M.r_fin X) (hI : M.indep I) (hIX : I ⊆ X) : I.finite := 
hI.finite_of_r_fin (hX.to_inter_ground.subset (subset_inter hIX hI.subset_ground))

@[simp] lemma r_fin_ground_iff : M.r_fin M.E ↔ M.finite_rk := 
begin
  obtain ⟨B, hB⟩ := M.exists_base, 
  use λ h, ⟨⟨B, hB, h.finite_of_indep_subset hB.indep hB.subset_ground⟩⟩, 
  simp_rw [r_fin_iff_exists_finite_basis, ←base_iff_basis_ground], 
  exact λ ⟨h⟩, h,   
end 

lemma indep.finite_of_subset_r_fin (hI : M.indep I) (hIX : I ⊆ X) (hX : M.r_fin X) : I.finite :=
hX.finite_of_indep_subset hI hIX 

lemma r_fin.to_cl (h : M.r_fin X) : M.r_fin (M.cl X) := 
by rwa [r_fin_iff_er_lt_top, er_cl]

lemma r_fin_iff_cl : M.r_fin X ↔ M.r_fin (M.cl X) := 
by rw [r_fin_iff_er_ne_top, ←er_cl, r_fin_iff_er_ne_top]

lemma r_fin.union (hX : M.r_fin X) (hY : M.r_fin Y) : M.r_fin (X ∪ Y) :=
begin
  rw [r_fin_iff_er_lt_top] at *, 
  apply (M.er_union_le_er_add_er X Y).trans_lt,
  rw [with_top.add_lt_top], 
  exact ⟨hX, hY⟩,  
end 

lemma r_fin.inter_right (hX : M.r_fin X) (Y : set α) : M.r_fin (X ∩ Y) := 
hX.subset (inter_subset_left _ _)

lemma r_fin.inter_left (hX : M.r_fin X) (Y : set α) : M.r_fin (Y ∩ X) := 
hX.subset (inter_subset_right _ _)

lemma r_fin.diff (hX : M.r_fin X) (D : set α) : M.r_fin (X \ D) := 
hX.subset (diff_subset _ _)

lemma r_fin.insert (hX : M.r_fin X) (e : α) (he : e ∈ M.E . ssE) : 
  M.r_fin (insert e X) := (M.r_fin_singleton e).union hX 

lemma to_r_fin (M : matroid_in α) [finite_rk M] (X : set α) : M.r_fin X :=  
begin
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E), 
  rw [r_fin_iff_inter_ground, r_fin_iff_er_lt_top, ← hI.encard, encard_lt_top_iff_finite], 
  exact hI.finite, 
end
 
lemma r_fin.cl_eq_cl_of_subset_of_er_ge_er (hX : M.r_fin X) (hXY : X ⊆ Y) (hr : M.er Y ≤ M.er X) : 
  M.cl X = M.cl Y :=
begin
  obtain ⟨I, J, hIX, hJY, hIJ⟩ := M.exists_basis_subset_basis (inter_subset_inter_left M.E hXY), 
  rw [er_eq_er_inter_ground, ←hJY.encard, er_eq_er_inter_ground, ←hIX.encard] at hr, 
  rw [cl_eq_cl_inter_ground, M.cl_eq_cl_inter_ground Y, ←hIX.cl, ←hJY.cl, 
    (hIX.indep.finite_of_subset_r_fin hIX.subset hX.to_inter_ground).eq_of_subset_of_encard_le' hIJ 
    hr], 
end 

lemma r_fin.cl_eq_cl_of_subset_of_er_ge_er' (hY : M.r_fin Y) (hXY : X ⊆ Y) (hr : M.er Y ≤ M.er X) :
  M.cl X = M.cl Y :=
(hY.subset hXY).cl_eq_cl_of_subset_of_er_ge_er hXY hr
  
lemma er_union_eq_of_subset_of_er_le_er (Z : set α) (hXY : X ⊆ Y) (hr : M.er Y ≤ M.er X) :
  M.er (X ∪ Z) = M.er (Y ∪ Z) := 
begin
  obtain (hX' | hX') := em (M.r_fin X), 
  { rw [←er_union_cl_left_eq, hX'.cl_eq_cl_of_subset_of_er_ge_er hXY hr, er_union_cl_left_eq] },
  rw [not_r_fin_iff.mp, not_r_fin_iff.mp], 
  { exact not_r_fin_of_er_ge hX' (M.er_mono (subset_union_of_subset_left hXY _)) },
  exact not_r_fin_of_er_ge hX' (M.er_mono (subset_union_left _ _)), 
end 

lemma er_union_eq_of_subsets_of_er_les (hX : X ⊆ X') (hY : Y ⊆ Y') (hXX' : M.er X' ≤ M.er X)
(hYY' : M.er Y' ≤ M.er Y) : M.er (X ∪ Y) = M.er (X' ∪ Y') :=
by rw [er_union_eq_of_subset_of_er_le_er _ hX hXX', union_comm, 
    er_union_eq_of_subset_of_er_le_er _ hY hYY', union_comm]

end r_fin 

section rank

/-- The rank function. Intended to be used in a `finite_rk` matroid; otherwise `er` is better.-/
def r (M : matroid_in α) (X : set α) : ℕ := (M.er X).to_nat 

/-- The rank of the ground set of a matroid -/
@[reducible] def rk (M : matroid_in α) : ℕ := M.r M.E 

lemma rk_def (M : matroid_in α) : M.rk = M.r M.E := rfl 

@[simp] lemma er_to_nat_eq_r (M : matroid_in α) (X : set α) : (M.er X).to_nat = M.r X := rfl 

lemma r_fin.coe_r_eq_er (hX : M.r_fin X) : (M.r X : ℕ∞) = M.er X :=
begin
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E), 
  rwa [r, er_eq_er_inter_ground, ←hI.encard, enat.coe_to_nat_eq_self, hI.encard, 
    ←er_eq_er_inter_ground, ←r_fin_iff_er_ne_top],  
end 

lemma coe_r_eq_er_of_finite (M : matroid_in α) (hX : X.finite) : (M.r X : ℕ∞) = M.er X :=
(M.r_fin_of_finite hX).coe_r_eq_er

@[simp] lemma coe_r_eq_er (M : matroid_in α) [finite_rk M] (X : set α) : (M.r X : ℕ∞) = M.er X :=
(M.to_r_fin X).coe_r_eq_er

lemma r_eq_of_er_eq (h : M.er X = M.er Y) : M.r X = M.r Y := 
by rw [r, r, h]

lemma r_fin.er_eq_er_iff (hX : M.r_fin X) (hY : M.r_fin Y) : M.er X = M.er Y ↔ M.r X = M.r Y := 
by rw [←hX.coe_r_eq_er, ←hY.coe_r_eq_er, enat.coe_inj]

lemma r_fin.er_le_er_iff (hX : M.r_fin X) (hY : M.r_fin Y) : M.er X ≤ M.er Y ↔ M.r X ≤ M.r Y := 
by rw [←hX.coe_r_eq_er, ←hY.coe_r_eq_er, enat.coe_le_coe_iff]

@[simp] lemma er_eq_er_iff [finite_rk M] : M.er X = M.er Y ↔ M.r X = M.r Y :=
(M.to_r_fin X).er_eq_er_iff (M.to_r_fin Y)

@[simp] lemma er_le_er_iff [finite_rk M] : M.er X ≤ M.er Y ↔ M.r X ≤ M.r Y := 
by rw [←coe_r_eq_er, ←coe_r_eq_er, enat.coe_le_coe_iff]
  
@[simp] lemma er_eq_coe_iff [finite_rk M] {n : ℕ} : M.er X = n ↔ M.r X = n := 
by rw [←coe_r_eq_er, enat.coe_inj]

@[simp] lemma er_le_coe_iff [finite_rk M] {n : ℕ} : M.er X ≤ n ↔ M.r X ≤ n := 
by rw [←coe_r_eq_er, enat.coe_le_coe_iff]

@[simp] lemma coe_le_er_iff [finite_rk M] {n : ℕ} : (n : ℕ∞) ≤ M.er X ↔ n ≤ M.r X := 
by rw [←coe_r_eq_er, enat.coe_le_coe_iff]

lemma r_fin.r_le_r_of_er_le_er (hY : M.r_fin Y) (hle : M.er X ≤ M.er Y) : M.r X ≤ M.r Y :=
by { rwa [←(r_fin.er_le_er_iff _ hY)], exact hle.trans_lt hY.lt }

lemma r_fin.er_le_er_of_r_le_r (hX : M.r_fin X) (hle : M.r X ≤ M.r Y) : M.er X ≤ M.er Y :=
by { obtain (h | h) := em (M.r_fin Y), rwa hX.er_le_er_iff h, rw [not_r_fin_iff.mp h], simp }

lemma r_eq_r_inter_ground (M : matroid_in α) (X : set α) : M.r X = M.r (X ∩ M.E) :=
by rw [←er_to_nat_eq_r, er_eq_er_inter_ground, er_to_nat_eq_r]

lemma le_r_iff [finite_rk M] : n ≤ M.r X ↔ ∃ I ⊆ X, M.indep I ∧ I.ncard = n := 
begin
  simp_rw [←coe_le_er_iff, le_er_iff, encard_eq_coe_iff, exists_prop], 
  exact exists_congr (λ I, ⟨λ hI, by tauto, λ hI, ⟨hI.1, hI.2.1, hI.2.1.finite, hI.2.2⟩⟩), 
end

lemma r_le_iff [finite_rk M] : M.r X ≤ n ↔ (∀ I ⊆ X, M.indep I → I.ncard ≤ n) :=
begin
  simp_rw [←enat.coe_le_coe_iff, coe_r_eq_er, er_le_iff, encard_le_coe_iff, enat.coe_le_coe_iff], 
  exact forall_congr (λ I, ⟨by tauto, λ h hIX hI, ⟨hI.finite, h hIX hI⟩⟩), 
end 

lemma r_mono (M : matroid_in α) [finite_rk M] : monotone M.r :=
by { rintro X Y (hXY : X ⊆ Y), rw [←er_le_er_iff],  exact M.er_mono hXY }

lemma r_le_card (M : matroid_in α) [finite M] (X : set α) (hX : X ⊆ M.E . ssE) : M.r X ≤ X.ncard := 
by { rw [r_le_iff], exact λ I h _, ncard_le_of_subset h (M.set_finite X) }  

lemma r_le_rk (M : matroid_in α) [finite_rk M] (X : set α) : M.r X ≤ M.rk := 
by { rw [r_eq_r_inter_ground], exact M.r_mono (inter_subset_right _ _) }
  
lemma lt_rk_iff_ne_rk [finite_rk M] : M.r X < M.rk ↔ M.r X ≠ M.rk := (M.r_le_rk X).lt_iff_ne

lemma indep.r (hI : M.indep I) : M.r I = I.ncard := 
by rw [←er_to_nat_eq_r, hI.er, encard_to_nat_eq]

lemma indep.card_le_r_of_subset [finite_rk M] (hI : M.indep I) (h : I ⊆ X) : I.ncard ≤ M.r X :=
by { rw [←hI.r], exact M.r_mono h }

lemma indep.card_le_rk [finite_rk M] (hI : M.indep I) : I.ncard ≤ M.rk :=
hI.r.symm.trans_le (M.r_le_rk I)

lemma basis.card (h : M.basis I X) : I.ncard = M.r X := 
by rw [←encard_to_nat_eq, ←er_to_nat_eq_r, h.encard]

lemma basis.r (h : M.basis I X) : M.r I = M.r X := 
by rw [←h.card, h.indep.r]

lemma basis.r_eq_card (h : M.basis I X) : M.r X = I.ncard :=
by rw [←h.r, ←h.indep.r]

lemma base.r (hB : M.base B) : M.r B = M.rk := 
by { rw base_iff_basis_ground at hB, rw [hB.r, rk] }

lemma base.card (hB : M.base B) : B.ncard = M.rk := 
by rw [(base_iff_basis_ground.mp hB).card, rk]

@[simp] lemma r_empty (M : matroid_in α) : M.r ∅ = 0 := 
by rw [←M.empty_indep.basis_self.card, ncard_empty]

@[simp] lemma r_cl (M : matroid_in α) (X : set α) : M.r (M.cl X) = M.r X :=
r_eq_of_er_eq (er_cl _ _)

lemma basis_iff_indep_card [finite_rk M] (hX : X ⊆ M.E . ssE) : 
  M.basis I X ↔ M.indep I ∧ I ⊆ X ∧ I.ncard = M.r X :=
begin
  refine I.finite_or_infinite.symm.elim (λ hI, iff_of_false (hI ∘ (λ h, h.indep.finite)) 
    (hI ∘ λ h, h.1.finite)) (λ hIfin, _), 
  rw [basis_iff_indep_encard_eq_of_finite hIfin hX, and_comm (_ ⊆ _), and_assoc,  
    and_comm (_ ⊆ _),  ←coe_r_eq_er, hIfin.encard_eq, enat.coe_inj], 
end 

lemma indep_iff_r_eq_card_of_finite (hI : I.finite) : M.indep I ↔ M.r I = I.ncard :=
begin
  obtain ⟨J,hJ⟩ := M.exists_basis (I ∩ M.E), 
  rw [r_eq_r_inter_ground, ←hJ.card], 
  refine ⟨λ h, _, λ h, _⟩,
  { rw [←inter_eq_self_of_subset_left h.subset_ground, 
      hJ.eq_of_subset_indep (h.inter_right M.E) hJ.subset subset.rfl] },
  rw ← eq_of_subset_of_ncard_le (hJ.subset.trans (inter_subset_left _ _)) h.symm.le hI, 
  exact hJ.indep, 
end

lemma indep_iff_r_eq_card [finite M] (hI : I ⊆ M.E . ssE): M.indep I ↔ M.r I = I.ncard :=
indep_iff_r_eq_card_of_finite (M.set_finite I)

lemma base_iff_indep_card [finite_rk M] : M.base B ↔ M.indep B ∧ B.ncard = M.rk :=
by rw [base_iff_basis_ground, basis_iff_indep_card, ←and_assoc, 
  and_iff_left_of_imp indep.subset_ground]

lemma base_iff_indep_r [finite_rk M] : M.base B ↔ M.indep B ∧ M.r B = M.rk :=
by { rw [base_iff_indep_card, and.congr_right_iff], exact λ h, by rw h.r }

lemma indep.base_of_rk_le_card [finite_rk M] (hI : M.indep I) (h : M.rk ≤ I.ncard) : M.base I :=
base_iff_indep_card.mpr ⟨hI, h.antisymm' (by {rw ←hI.r, apply r_le_rk})⟩

lemma basis.r_eq_r_union (hIX : M.basis I X) (Y : set α) : M.r (I ∪ Y) = M.r (X ∪ Y) :=
r_eq_of_er_eq (hIX.er_eq_er_union _)

lemma basis.r_eq_r_insert (hIX : M.basis I X) (e : α) : M.r (insert e I) = M.r (insert e X) :=
r_eq_of_er_eq (hIX.er_eq_er_insert _)

lemma indep.basis_of_subset_of_r_le [finite_rk M] (hI : M.indep I) (hIX : I ⊆ X)
(h : M.r X ≤ M.r I) (hX : X ⊆ M.E . ssE) : M.basis I X :=
hI.basis_of_subset_of_er_le_of_finite hIX (er_le_er_iff.mpr h) hI.finite
  
/-- The submodularity axiom for the rank function -/
lemma r_inter_add_r_union_le_r_add_r (M : matroid_in α) [finite_rk M] (X Y : set α) :
  M.r (X ∩ Y) + M.r (X ∪ Y) ≤ M.r X + M.r Y :=
by { simp_rw [←enat.coe_le_coe_iff, enat.coe_add, coe_r_eq_er], apply er_submod } 

alias r_inter_add_r_union_le_r_add_r ← r_submod 

lemma eq_of_r_eq_r_forall {M₁ M₂ : matroid_in α} [finite_rk M₁] (hE : M₁.E = M₂.E) 
  (h : ∀ X ⊆ M₁.E, M₁.r X = M₂.r X) : M₁ = M₂ :=
begin
  have h2 : ∀ I, M₂.indep I → I.finite, 
  { refine λ I hI, by_contra (λ (hinf : I.infinite), _),  
    obtain ⟨B₁,hB₁⟩ := M₁.exists_base, 
    obtain ⟨I₁,hI₁I, hI₁fin, hI₁card⟩ := hinf.exists_subset_ncard_eq (M₁.rk + 1), 
    rw [←(hI.subset hI₁I).r, ←h _ (hI₁I.trans (hI.subset_ground.trans_eq hE.symm)) ] at hI₁card, 
    linarith [M₁.r_le_rk I₁] },
    
  refine eq_of_indep_iff_indep_forall hE (λ I hI, (I.finite_or_infinite.symm.elim 
    (λ hI', iff_of_false (λ h', hI' h'.finite) (λ h', hI' (h2 _ h') ) ) (λ hI', _))),  
  
  suffices : M₁.er I = M₂.er I, 
  by rw [indep_iff_er_eq_encard_of_finite hI', indep_iff_er_eq_encard_of_finite hI', this], 
  rw [←M₁.coe_r_eq_er_of_finite hI', ←M₂.coe_r_eq_er_of_finite hI', h _ hI],
end 

lemma r_inter_left_le_r (M : matroid_in α) [finite_rk M] (X Y : set α) : M.r (X ∩ Y) ≤ M.r X :=
M.r_mono (inter_subset_left X Y)

lemma r_inter_right_le_r (M : matroid_in α) [finite_rk M] (X Y : set α) : M.r (X ∩ Y) ≤ M.r Y :=
M.r_mono (inter_subset_right X Y)

lemma r_le_r_union_left (M : matroid_in α) [finite_rk M] (X Y : set α) : M.r X ≤ M.r (X ∪ Y) :=
M.r_mono (subset_union_left X Y)

lemma r_le_r_union_right (M : matroid_in α) [finite_rk M] (X Y : set α) : M.r Y ≤ M.r (X ∪ Y) :=
M.r_mono (subset_union_right X Y)

lemma r_diff_le_r (M : matroid_in α) [finite_rk M] (X Y : set α) : M.r (X \ Y) ≤ M.r X :=
by { rw diff_eq, apply r_inter_left_le_r }

lemma r_lt_card_iff_not_indep [M.finite] (hX : X ⊆ M.E . ssE) : (M.r X < X.ncard) ↔ ¬M.indep X :=
begin
  rw [lt_iff_not_le, not_iff_not, indep_iff_r_eq_card],
  exact ⟨(M.r_le_card X hX).antisymm, λ h, by rw h⟩ 
end

lemma nonempty_of_r_nonzero (hX : M.r X ≠ 0): X.nonempty :=
by {rw nonempty_iff_ne_empty, rintro rfl, exact hX M.r_empty}

lemma r_singleton_le (M : matroid_in α) (e : α) : M.r {e} ≤ 1 :=
begin
  have := M.er_singleton_le e,  
  rw [←enat.coe_one, with_top.le_coe_iff] at this, 
  obtain ⟨i, hi, hle⟩ := this, 
  rwa [←er_to_nat_eq_r, hi, enat.to_nat_coe], 
end 

lemma r_insert_le_add_one (M : matroid_in α) (e : α) (X : set α) : 
  M.r (insert e X) ≤ M.r X + 1 :=
begin
  have hle := M.er_insert_le_add_one e X, 
  simp_rw [←er_to_nat_eq_r], 
  obtain (h | h) := eq_or_ne (M.er X) ⊤, 
  { have h' := M.er_mono (subset_insert e X), 
    simp [h] at h', 
    simp [h,h'] },
  have h' : M.er X + 1 ≠ ⊤, by { rw with_top.add_ne_top, simp [h] },
  convert enat.to_nat_le_to_nat_of_ne_top hle h', 
  rw [←enat.coe_inj, enat.coe_add, enat.coe_to_nat h, enat.coe_to_nat h', enat.coe_one], 
end 

lemma r_eq_r_of_subset_le [finite_rk M] (hXY : X ⊆ Y) (hYX : M.r Y ≤ M.r X) : M.r X = M.r Y :=
(M.r_mono hXY).antisymm hYX

lemma r_eq_r_diff_r_le_zero [finite_rk M] (X : set α) (hY : M.r Y ≤ 0) : M.r (X \ Y) = M.r X :=
by { apply r_eq_of_er_eq, rw [er_eq_er_diff_er_le_zero], rwa [←enat.coe_zero, er_le_coe_iff] }

lemma r_eq_r_union_r_le_zero [finite_rk M] (X : set α) (hY : M.r Y ≤ 0) : M.r (X ∪ Y) = M.r X :=
by { apply r_eq_of_er_eq, rw [er_eq_er_union_er_le_zero], rwa [←enat.coe_zero, er_le_coe_iff] }

lemma cl_eq_cl_of_subset_of_r_ge_r [finite_rk M] (hXY : X ⊆ Y) (hr : M.r Y ≤ M.r X) : 
  M.cl X = M.cl Y :=
(M.to_r_fin X).cl_eq_cl_of_subset_of_er_ge_er hXY (by rwa er_le_er_iff)

lemma r_union_eq_of_subset_of_r_le_r [finite_rk M] (Z : set α) (hXY : X ⊆ Y) (hr : M.r Y ≤ M.r X) :
  M.r (X ∪ Z) = M.r (Y ∪ Z) := 
r_eq_of_er_eq (er_union_eq_of_subset_of_er_le_er Z hXY ((M.to_r_fin Y).er_le_er_of_r_le_r hr)) 
  
lemma r_union_eq_of_subsets_of_r_les [finite_rk M] (hX : X ⊆ X') (hY : Y ⊆ Y')
(hXX' : M.r X' ≤ M.r X) (hYY' : M.r Y' ≤ M.r Y) : M.r (X ∪ Y) = M.r (X' ∪ Y') :=
begin
  rw [←er_eq_er_iff], rw [←er_le_er_iff] at hXX' hYY', 
  apply er_union_eq_of_subsets_of_er_les; assumption, 
end 

lemma r_union_le_add_r (M : matroid_in α) [finite_rk M] (X Y : set α) :
  M.r (X ∪ Y) ≤ M.r X + M.r Y :=
by linarith [M.r_submod X Y]

lemma r_union_le_card_add_r (M : matroid_in α) [finite M] (X Y : set α) (hX : X ⊆ M.E . ssE) : 
  M.r (X ∪ Y) ≤ X.ncard + M.r Y :=
(M.r_union_le_add_r X Y).trans (add_le_add_right (M.r_le_card X hX) _)

lemma r_union_le_r_add_card (M : matroid_in α) [finite M] (X Y : set α) (hY : Y ⊆ M.E . ssE) : 
  M.r (X ∪ Y) ≤ M.r X + Y.ncard :=
by { rw [add_comm, union_comm], exact M.r_union_le_card_add_r Y X }

lemma rk_le_card_add_r_compl (M : matroid_in α) [finite M] (X : set α) (hX : X ⊆ M.E . ssE) :
  M.rk ≤ X.ncard + M.r (M.E \ X) :=
by simpa only [ground_inter_left, union_diff_self, M.r_eq_r_inter_ground (X ∪ _), 
  union_inter_cancel_right, ←rk_def] using M.r_union_le_card_add_r (X ∩ M.E) (M.E \ X)
  
  
  
end rank 


end matroid_in 

-- /-- The rank `M.rk` of a matroid is the rank of its ground set -/
-- def rk {α : Type*} (M : matroid_in α) : ℕ := M.r M.E

-- lemma rk_def {α : Type*} (M : matroid_in α) : M.rk = M.r M.E := rfl 

-- /-- The rank of a set is the size of a basis -/
-- lemma basis.card_of_inter_ground (hI : M.basis I (X ∩ M.E)) : I.ncard = M.r X :=
-- begin
--   have hrw : ∀ J : {J : set α | M.basis J (X ∩ M.E)}, (J : set α).ncard = I.ncard,
--   { rintro ⟨J, (hJ : M.basis J (X ∩ M.E))⟩, rw [subtype.coe_mk, hI.card_eq_card_of_basis hJ] },
--   haveI : nonempty {J : set α | M.basis J (X ∩ M.E)}, 
--     from let ⟨I,hI⟩ := M.exists_basis (X ∩ M.E) in ⟨⟨I,hI⟩⟩,
--   simp_rw [r, hrw, cinfi_const], 
-- end

-- lemma basis.card (hI : M.basis I X) : I.ncard = M.r X := 
-- hI.basis_inter_ground.card_of_inter_ground

-- lemma eq_r_iff {n : ℕ} (hX : X ⊆ M.E . ssE) : M.r X = n ↔ ∃ I, M.basis I X ∧ I.ncard = n :=
-- begin
--   split,
--   { rintro rfl, 
--     obtain ⟨I,hI⟩ := M.exists_basis X, 
--     refine ⟨I, hI, hI.card⟩ },
--   rintro ⟨I,hI,rfl⟩, 
--   rw hI.card, 
-- end

-- lemma indep.r (hI : M.indep I) : M.r I = I.ncard := eq_r_iff.mpr ⟨I, hI.basis_self, rfl⟩

-- lemma basis.r (hIX : M.basis I X) : M.r I = M.r X := 
-- by rw [←hIX.card, hIX.indep.r]

-- lemma basis.r_eq_card (hIX : M.basis I X) : M.r X = I.ncard :=
-- by rw [←hIX.r, ←hIX.indep.r]

-- lemma base.r (hB : M.base B) : M.r B = M.rk := 
-- by { rw base_iff_basis_ground at hB, rw [hB.r, rk] }

-- lemma base.card (hB : M.base B) : B.ncard = M.rk := 
-- by rw [(base_iff_basis_ground.mp hB).card, rk]

-- lemma r_eq_r_inter_ground (M : matroid_in α) (X : set α) : M.r X = M.r (X ∩ M.E) :=
-- by { obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E), rwa [←hI.card_of_inter_ground, ←basis.card] }

-- @[simp] lemma r_empty (M : matroid_in α) : M.r ∅ = 0 := 
-- by rw [←M.empty_indep.basis_self.card, ncard_empty]

-- @[simp] lemma r_cl (M : matroid_in α) (X : set α) : M.r (M.cl X) = M.r X :=
-- begin
--   rw [cl_eq_cl_inter_ground, M.r_eq_r_inter_ground X], 
--   obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E), 
--   rw [←hI.r, ←hI.cl, hI.indep.basis_cl.r], 
-- end 

-- @[simp] lemma r_union_cl_right_eq_r_union (M : matroid_in α) (X Y : set α) :
--   M.r (X ∪ M.cl Y) = M.r (X ∪ Y) :=
-- by rw [←r_cl, cl_union_cl_right_eq, r_cl]

-- @[simp] lemma r_union_cl_left_eq_r_union (M : matroid_in α) (X Y : set α) :
--   M.r (M.cl X ∪ Y) = M.r (X ∪ Y) :=
-- by rw [←r_cl, cl_union_cl_left_eq, r_cl]

-- @[simp] lemma r_insert_cl_eq_r_insert (M : matroid_in α) (e : α) (X : set α) : 
--   M.r (insert e (M.cl X)) = M.r (insert e X) :=
-- by rw [← union_singleton, r_union_cl_left_eq_r_union, union_singleton]

-- lemma basis.r_eq_r_union (hIX : M.basis I X) (Y : set α) :
--   M.r (I ∪ Y) = M.r (X ∪ Y) :=
-- begin
--   rw [←r_union_cl_right_eq_r_union, ←r_union_cl_right_eq_r_union _ _ Y], 
--   obtain ⟨I', hI', hII'⟩ :=
--     hIX.indep.subset_basis_of_subset (hIX.subset.trans (subset_union_left _ (M.cl Y))), 
--   rw [←hI'.r, ← (hI'.basis_subset _ (union_subset_union_left _ hIX.subset)).r],   
--   refine λ e he, (hI'.subset he).elim (λ heX, or.inl _) (λ heY, subset_union_right _ _ heY), 
--   exact hIX.mem_of_insert_indep heX (hI'.indep.subset (insert_subset.mpr ⟨he, hII'⟩)), 
-- end

-- section finite

-- lemma r_le_card_of_finite (M : matroid_in α) {X : set α} (h : X.finite) : 
--   M.r X ≤ X.ncard := 
-- begin
--   rw [r_eq_r_inter_ground], 
--   obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E), 
--   rw ←hI.card, 
--   refine ncard_le_of_subset (hI.subset.trans (inter_subset_left _ _)) h, 
-- end 

-- lemma r_le_card (M : matroid_in α) [finite M] (X : set α) (hX : X ⊆ M.E . ssE) : M.r X ≤ X.ncard :=
-- M.r_le_card_of_finite (M.set_finite X)

-- lemma indep_iff_r_eq_card_of_finite {M : matroid_in α} (hI : I.finite) :
--   M.indep I ↔ M.r I = I.ncard :=
-- begin
--   obtain ⟨J,hJ⟩ := M.exists_basis (I ∩ M.E), 
--   rw [r_eq_r_inter_ground, ←hJ.card], 
--   refine ⟨λ h, _, λ h, _⟩,
--   { rw [←inter_eq_self_of_subset_left h.subset_ground, 
--       hJ.eq_of_subset_indep (h.inter_right M.E) hJ.subset subset.rfl] },
--   rw ← eq_of_subset_of_ncard_le (hJ.subset.trans (inter_subset_left _ _)) h.symm.le hI, 
--   exact hJ.indep, 
-- end

-- lemma indep_iff_r_eq_card [finite M] (hI : I ⊆ M.E . ssE): M.indep I ↔ M.r I = I.ncard :=
-- indep_iff_r_eq_card_of_finite (M.set_finite I)

-- lemma rk_le_card_ground (M : matroid_in α) [finite M] : M.rk ≤ M.E.ncard :=
-- M.r_le_card_of_finite (M.set_finite M.E)
  
-- lemma r_lt_card_of_dep_of_finite (h : X.finite) (hX : M.dep X) : M.r X < X.ncard :=
-- lt_of_le_of_ne (M.r_le_card_of_finite h) 
--   (λ h', ((indep_iff_r_eq_card_of_finite h).mpr h').not_dep hX)
  
-- lemma r_lt_card_of_dep [finite M] (hX : M.dep X) : M.r X < X.ncard :=
-- r_lt_card_of_dep_of_finite (M.set_finite _) hX 

-- lemma r_lt_card_iff_dep_of_finite (hX : X.finite) (hXE : X ⊆ M.E . ssE) : 
--   M.r X < X.ncard ↔ M.dep X := 
-- ⟨λ hlt, not_indep_iff.mp (λ hI, hlt.ne hI.r), r_lt_card_of_dep_of_finite hX⟩

-- lemma r_lt_card_iff_dep [finite M] (hXE : X ⊆ M.E . ssE) : M.r X < X.ncard ↔ M.dep X :=
-- r_lt_card_iff_dep_of_finite (M.set_finite _)

-- end finite


-- lemma infinite_of_not_r_fin (hX : ¬M.r_fin X) (hXE : X ⊆ M.E . ssE) : X.infinite :=
-- λ hX', hX (M.r_fin_of_finite hX') 

-- lemma basis.infinite_of_not_r_fin (hIX : M.basis I X) (hX : ¬ M.r_fin X) : I.infinite :=
-- hX ∘ (λ hI, hIX.r_fin_of_finite hI)

-- /-- A set with no finite basis has the junk rank value of zero -/
-- lemma r_eq_zero_of_not_r_fin (h : ¬M.r_fin X) (hX : X ⊆ M.E . ssE) : M.r X = 0 :=
-- begin
--   simp_rw [r_fin, not_exists, not_and] at h, 
--   obtain ⟨I, hI⟩ := M.exists_basis X, 
--   rw [←hI.card, infinite.ncard (h _ hI)], 
-- end

-- lemma r_fin_of_r_ne_zero (h : M.r X ≠ 0) (hX : X ⊆ M.E . ssE) : M.r_fin X := 
-- begin
--   obtain ⟨I, hI⟩ := M.exists_basis X, 
--   rw [←hI.card] at h, 
--   exact hI.r_fin_of_finite (finite_of_ncard_ne_zero h),  
-- end 



-- lemma indep.le_card_basis_of_r_fin (hI : M.indep I) (hIX : I ⊆ X) (hX : M.r_fin X) 
-- (hXJ : M.basis J X) : I.ncard ≤ J.ncard :=
-- begin
--   obtain ⟨I', hI, h⟩ := hI.subset_finite_basis_of_subset_of_r_fin hIX hX, 
--   rw hXJ.card_eq_card_of_basis hI, 
--   exact ncard_le_of_subset h.1 (hI.finite_of_r_fin hX), 
-- end 

-- lemma r_fin.le_r_iff (h : M.r_fin X) {n : ℕ} : n ≤ M.r X ↔ ∃ I ⊆ X, M.indep I ∧ I.ncard = n :=
-- begin
--   obtain ⟨J, hJ⟩ := eq_r_iff.mp (@rfl _ (M.r X)),
--   refine ⟨λ h, _, λ h, _⟩,
--   { obtain ⟨I', hI', rfl⟩ := exists_smaller_set _ _ (h.trans_eq hJ.2.symm),
--     exact ⟨I', hI'.trans hJ.1.subset, hJ.1.indep.subset hI', by simp⟩ },
--   obtain ⟨I, hIX, hI, rfl⟩ := h,
--   rw ←hJ.2,
--   exact hI.le_card_basis_of_r_fin hIX h hJ.1, 
-- end 

-- lemma r_fin.r_le_iff (h : M.r_fin X) {n : ℕ} : M.r X ≤ n ↔ (∀ I ⊆ X, M.indep I → I.ncard ≤ n) :=
-- begin
--   obtain ⟨I, hIX, hI⟩ := eq_r_iff.mp (@rfl _ (M.r X)),
--   exact ⟨λ h' J hJX hJ, (hJ.le_card_basis_of_r_fin hJX h hIX).trans (hI.trans_le h'),
--     λ h, hI.symm.trans_le (h I hIX.subset hIX.indep)⟩,
-- end 

-- lemma r_fin.r_mono (hY : M.r_fin Y) (hXY : X ⊆ Y) : M.r X ≤ M.r Y :=
-- by { simp_rw [(hY.subset hXY).r_le_iff, hY.le_r_iff], exact λ I hIX hI, ⟨I,hIX.trans hXY,hI,rfl⟩ }

-- lemma r_fin.r_eq_r_of_subset_le (h : M.r_fin Y) (hXY : X ⊆ Y) (hYX : M.r Y ≤ M.r X) : 
--   M.r X = M.r Y :=
-- (h.r_mono hXY).antisymm hYX

-- lemma indep.card_le_r_of_subset_of_r_fin (hI : M.indep I) (h : I ⊆ X) (hX : M.r_fin X) : 
--   I.ncard ≤ M.r X :=
-- by { rw [←hI.r], exact hX.r_mono h }

-- lemma indep.basis_of_subset_of_r_le_of_r_fin (hI : M.indep I) (hIX : I ⊆ X) (h : M.r X ≤ M.r I) 
-- (hX : M.r_fin X) :
--   M.basis I X :=
-- begin
--   obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset hIX,   
--   rwa eq_of_subset_of_ncard_le hIJ _ (hJ.finite_of_r_fin hX), 
--   rwa [hJ.card, ←hI.r], 
-- end

-- /-- The submodularity axiom for the rank function -/
-- lemma r_fin.r_inter_add_r_union_le_r_add_r (hX : M.r_fin X) (hY : M.r_fin Y) :
--   M.r (X ∩ Y) + M.r (X ∪ Y) ≤ M.r X + M.r Y :=
-- begin
--   obtain ⟨Ii, hIi⟩ := M.exists_basis (X ∩ Y),
--   obtain ⟨IX, hIX, hIX', hIXfin⟩ :=
--     hIi.indep.subset_finite_basis_of_subset_of_r_fin (hIi.subset.trans (inter_subset_left _ _)) hX,
--   obtain ⟨IY, hIY, hIY', hIYfin⟩ :=
--     hIi.indep.subset_finite_basis_of_subset_of_r_fin (hIi.subset.trans (inter_subset_right _ _)) hY,
  
--   rw [←hIX.r_eq_r_union, union_comm, ←hIY.r_eq_r_union, ←hIi.card, ←hIX.card, ←hIY.card, 
--    union_comm, ← ncard_union_add_ncard_inter _ _ hIXfin hIYfin, add_comm], 
--   refine add_le_add (M.r_le_card_of_finite (hIXfin.union hIYfin)) _, 
--   refine (ncard_le_of_subset (subset_inter hIX' hIY') (hIXfin.subset (inter_subset_left _ _))),
-- end

-- alias r_fin.r_inter_add_r_union_le_r_add_r ← r_fin.submod 

-- lemma r_fin.r_union_le_add_r (hX : M.r_fin X) (hY : M.r_fin Y) : M.r (X ∪ Y) ≤ M.r X + M.r Y :=
-- by linarith [hX.submod hY]

-- lemma r_fin.r_union_le_add_r' (hX : M.r_fin (X ∪ Y)) : M.r (X ∪ Y) ≤ M.r X + M.r Y := 
-- by { apply r_fin.r_union_le_add_r; 
--   apply hX.subset, apply subset_union_left, apply subset_union_right }

-- lemma r_fin.basis_iff_finite_indep_card (hX : M.r_fin X) :
--   M.basis I X ↔ M.indep I ∧ I ⊆ X ∧ I.finite ∧ I.ncard = M.r X :=
-- begin
--   refine (I.finite_or_infinite.symm.elim _ (λ hI, ⟨λ hb, ⟨hb.indep,hb.subset,hI,hb.card⟩, λ h, _⟩)), 
--   { exact λ hI, iff_of_false (λ hb, hI (hb.finite_of_r_fin hX)) (by simp [iff_false_intro hI]) }, 
--   refine h.1.basis_of_maximal_subset h.2.1 (λ J hJ hIJ hJX, _), 
--   rw [←eq_of_subset_of_ncard_le hIJ _ (hJ.finite_of_subset_r_fin hJX hX)], 
--   rw [h.2.2.2, hX.le_r_iff], 
--   exact ⟨J, hJX, hJ, rfl⟩, 
-- end 

-- lemma indep.basis_of_r_fin_of_subset_of_r_ge (hI : M.indep I) (hIX : I ⊆ X) (hX : M.r_fin X) 
-- (hr : M.r X ≤ I.ncard) : 
--   M.basis I X  :=
-- hX.basis_iff_finite_indep_card.mpr ⟨hI, hIX, hI.finite_of_subset_r_fin hIX hX, 
--     hr.antisymm' (hX.le_r_iff.mpr ⟨I, hIX, hI,rfl⟩)⟩

-- lemma r_fin.r_eq_zero_iff_subset_loops (hX : M.r_fin X) : M.r X = 0 ↔ X ⊆ M.cl ∅ :=
-- begin
--   obtain ⟨I, hI⟩ := M.exists_basis X,
--   rw [←cl_subset_cl_iff_subset_cl, ←hI.cl], 
--   rw hX.basis_iff_finite_indep_card at hI, 
--   rw [←hI.2.2.2, ncard_eq_zero hI.2.2.1], 
--   exact ⟨by { rintro rfl, exact subset.rfl }, 
--     λ h, hI.1.eq_empty_of_subset_loops ((M.subset_cl I hI.1.subset_ground).trans h)⟩,
-- end 

-- lemma r_fin.r_eq_r_diff_r_le_zero (hY : M.r_fin Y) (X) (hr : M.r Y ≤ 0) : M.r (X \ Y) = M.r X :=
-- by rw [←r_cl, cl_diff_eq_cl_of_subset_loops (hY.r_eq_zero_iff_subset_loops.mp (le_zero_iff.mp hr)), 
--   r_cl]

-- lemma r_fin.r_eq_r_union_r_le_zero (hY : M.r_fin Y) (X) (hr : M.r Y ≤ 0) : M.r (X ∪ Y) = M.r X :=
-- by rw [←r_cl, cl_union_eq_cl_of_subset_loops (hY.r_eq_zero_iff_subset_loops.mp (le_zero_iff.mp hr)), 
--   r_cl]

-- lemma r_fin.r_le_r_inter_add_r_diff (hX : M.r_fin X) (Y : set α) : 
--   M.r X ≤ M.r (X ∩ Y) + M.r (X \ Y) :=
-- begin
--   convert r_fin.r_union_le_add_r (hX.subset (inter_subset_left _ _)) (hX.subset (diff_subset _ _)), 
--   rw (inter_union_diff X Y), 
-- end 

-- lemma r_fin.r_le_r_add_r_diff (hX : M.r_fin X) (hYX : Y ⊆ X) : M.r X ≤ M.r Y + M.r (X \ Y) :=
-- begin
--   convert hX.r_le_r_inter_add_r_diff _, 
--   rw [inter_eq_self_of_subset_right hYX], 
-- end 

-- lemma r_fin.cl_eq_cl_of_subset_of_r_ge_r (hY : M.r_fin Y) (hXY : X ⊆ Y) (hr : M.r Y ≤ M.r X) : 
--   M.cl X = M.cl Y :=
-- begin
--   have hXE : X ⊆ M.E := hXY.trans hY.subset_ground, 
--   obtain ⟨I, hI⟩ := M.exists_basis X, 
--   obtain ⟨J, hJ, hIJ, hJfin⟩ := hI.indep.subset_finite_basis_of_subset_of_r_fin 
--     (hI.subset.trans hXY) hY, 
--   rw [←hI.cl, ←hJ.cl, eq_of_subset_of_ncard_le hIJ _ hJfin], 
--   rwa [hI.card, hJ.card],
-- end 

-- end r_fin

-- lemma le_r_iff [finite_rk M] : n ≤ M.r X ↔ ∃ I ⊆ X, M.indep I ∧ I.ncard = n := 
-- begin
--   rw [r_eq_r_inter_ground], 
--   convert (M.to_r_fin (X ∩ M.E)).le_r_iff,
--   ext I, 
--   simp only [exists_prop, subset_inter_iff, and.congr_left_iff, iff_self_and, and_imp], 
--   exact λ h _ _, h.subset_ground,  
-- end 

-- lemma r_le_iff [finite_rk M] : M.r X ≤ n ↔ (∀ I ⊆ X, M.indep I → I.ncard ≤ n) :=
-- begin
--   rw [r_eq_r_inter_ground], 
--   convert (M.to_r_fin (X ∩ M.E)).r_le_iff, 
--   simp only [subset_inter_iff, and_imp, eq_iff_iff], 
--   exact forall_congr (λ I, ⟨λ h hIX hIE hI, h hIX hI, λ h hIX hI, h hIX (by ssE) hI⟩), 
-- end 

-- lemma r_mono (M : matroid_in α) [finite_rk M] {X Y : set α} (hXY : X ⊆ Y) : M.r X ≤ M.r Y :=
-- begin
--   rw [r_eq_r_inter_ground, M.r_eq_r_inter_ground Y], 
--   exact (M.to_r_fin _).r_mono (inter_subset_inter_left _ hXY), 
-- end 

-- lemma basis_iff_indep_card [finite_rk M] (hX : X ⊆ M.E . ssE) : 
--   M.basis I X ↔ M.indep I ∧ I ⊆ X ∧ I.ncard = M.r X :=
-- begin
--   rw [r_eq_r_inter_ground, (M.to_r_fin X).basis_iff_finite_indep_card, and.congr_right_iff, 
--     and.congr_right_iff, r_eq_r_inter_ground, and_iff_right_iff_imp], 
--   exact λ h _ _, h.finite,  
-- end 

-- lemma r_le_rk (M : matroid_in α) [finite_rk M] (X : set α) : M.r X ≤ M.rk := 
-- by { rw [r_eq_r_inter_ground], exact M.r_mono (inter_subset_right _ _) }
  
-- lemma lt_rk_iff_ne_rk [finite_rk M] : M.r X < M.rk ↔ M.r X ≠ M.rk := (M.r_le_rk X).lt_iff_ne

-- lemma indep.card_le_r_of_subset [finite_rk M] (hI : M.indep I) (h : I ⊆ X) : 
--   I.ncard ≤ M.r X :=
-- by { rw [←hI.r], exact M.r_mono h }

-- lemma indep.card_le_rk [finite_rk M] (hI : M.indep I) : I.ncard ≤ M.rk :=
-- hI.r.symm.trans_le (M.r_le_rk I)

-- lemma base_iff_indep_r [finite_rk M] : M.base B ↔ M.indep B ∧ M.r B = M.rk :=
-- begin
--   refine ⟨λ h, ⟨h.indep, h.r⟩, λ h, base_iff_maximal_indep.mpr ⟨h.1, λ I hI hBI, _⟩⟩,
--   refine eq_of_le_of_not_lt hBI (λ hBI' : B ⊂ I, _),
--   cases h with hB hB',
--   rw [hB.r] at hB',
--   have := ncard_lt_ncard hBI' hI.finite,
--   rw [←hI.r, hB'] at this,
--   exact this.not_le (M.r_le_rk _), 
-- end

-- lemma base_iff_indep_card [finite_rk M] : M.base B ↔ M.indep B ∧ B.ncard = M.rk :=
-- ⟨λ h, ⟨h.indep, by rw ←h.card⟩, λ h, base_iff_indep_r.mpr ⟨h.1, by rw [←h.2, ←h.1.r]⟩⟩

-- lemma indep.base_of_rk_le_card [finite_rk M] (hI : M.indep I) (h : M.rk ≤ I.ncard) : M.base I :=
-- base_iff_indep_card.mpr ⟨hI, h.antisymm' (by {rw ←hI.r, apply r_le_rk})⟩

-- lemma basis.r_eq_r_insert (hIX : M.basis I X) (e : α) : M.r (insert e I) = M.r (insert e X) :=
-- by simp_rw [←union_singleton, hIX.r_eq_r_union]

-- lemma indep.basis_of_subset_of_r_le [finite_rk M] (hI : M.indep I) (hIX : I ⊆ X)
-- (h : M.r X ≤ M.r I) (hX : X ⊆ M.E . ssE) : M.basis I X :=
-- hI.basis_of_subset_of_r_le_of_r_fin hIX h (M.to_r_fin X)

-- /-- The submodularity axiom for the rank function -/
-- lemma r_inter_add_r_union_le_r_add_r (M : matroid_in α) [finite_rk M] (X Y : set α) :
--   M.r (X ∩ Y) + M.r (X ∪ Y) ≤ M.r X + M.r Y :=
-- begin
--   rw [r_eq_r_inter_ground, inter_inter_distrib_right, M.r_eq_r_inter_ground (X ∪ _), 
--     inter_distrib_right, M.r_eq_r_inter_ground X, M.r_eq_r_inter_ground Y], 
--   exact (M.to_r_fin _).r_inter_add_r_union_le_r_add_r (M.to_r_fin _), 
-- end 

-- alias r_inter_add_r_union_le_r_add_r ← r_submod 

-- lemma eq_of_r_eq_r_forall {M₁ M₂ : matroid_in α} [finite_rk M₁] (hE : M₁.E = M₂.E) 
--   (h : ∀ X ⊆ M₁.E, M₁.r X = M₂.r X) : M₁ = M₂ :=
-- begin
--   have h2 : ∀ I, M₂.indep I → I.finite, 
--   { refine λ I hI, by_contra (λ (hinf : I.infinite), _),  
--     obtain ⟨B₁,hB₁⟩ := M₁.exists_base, 
--     obtain ⟨I₁,hI₁I, hI₁fin, hI₁card⟩ := hinf.exists_subset_ncard_eq (M₁.rk + 1), 
--     rw [←(hI.subset hI₁I).r, ←h _ (hI₁I.trans (hI.subset_ground.trans_eq hE.symm)) ] at hI₁card, 
--     linarith [M₁.r_le_rk I₁] },
    
--   refine eq_of_indep_iff_indep_forall hE (λ I hI, (I.finite_or_infinite.symm.elim 
--     (λ hI, iff_of_false (λ h', hI h'.finite) (λ h', hI (h2 _ h') ) ) (λ hI, _))),  
  
--   rwa [indep_iff_r_eq_card_of_finite hI, h, indep_iff_r_eq_card_of_finite hI], 
-- end 

-- lemma r_le_r_of_subset (M : matroid_in α) [finite_rk M] (hXY : X ⊆ Y) : M.r X ≤ M.r Y :=
-- M.r_mono hXY

-- lemma r_inter_left_le_r (M : matroid_in α) [finite_rk M] (X Y : set α) : M.r (X ∩ Y) ≤ M.r X :=
-- M.r_mono (inter_subset_left X Y)

-- lemma r_inter_right_le_r (M : matroid_in α) [finite_rk M] (X Y : set α) : M.r (X ∩ Y) ≤ M.r Y :=
-- M.r_mono (inter_subset_right X Y)

-- lemma r_le_r_union_left (M : matroid_in α) [finite_rk M] (X Y : set α) : M.r X ≤ M.r (X ∪ Y) :=
-- M.r_mono (subset_union_left X Y)

-- lemma r_le_r_union_right (M : matroid_in α) [finite_rk M] (X Y : set α) : M.r Y ≤ M.r (X ∪ Y) :=
-- M.r_mono (subset_union_right X Y)

-- lemma r_diff_le_r (M : matroid_in α) [finite_rk M] (X Y : set α) : M.r (X \ Y) ≤ M.r X :=
-- by { rw diff_eq, apply r_inter_left_le_r }

-- lemma r_lt_card_iff_not_indep [M.finite] (hX : X ⊆ M.E . ssE) : (M.r X < X.ncard) ↔ ¬M.indep X :=
-- begin
--   rw [lt_iff_not_le, not_iff_not, indep_iff_r_eq_card],
--   exact ⟨(M.r_le_card X).antisymm, λ h, by rw h⟩ 
-- end

-- lemma nonempty_of_r_nonzero (hX : M.r X ≠ 0): X.nonempty :=
-- by {rw nonempty_iff_ne_empty, rintro rfl, exact hX M.r_empty}

-- lemma r_single_ub (M : matroid_in α) [finite_rk M] (e : α) : M.r {e} ≤ 1 :=
-- by { convert M.r_le_card_of_finite _; simp [ncard_singleton] }

-- lemma r_eq_r_of_subset_le [finite_rk M] (hXY : X ⊆ Y) (hYX : M.r Y ≤ M.r X) : M.r X = M.r Y :=
-- (M.r_mono hXY).antisymm hYX

-- lemma r_eq_r_diff_r_le_zero [finite_rk M] (X : set α) (hY : M.r Y ≤ 0) : M.r (X \ Y) = M.r X :=
-- begin
--   rw [r_eq_r_inter_ground] at hY, 
--   rw [r_eq_r_inter_ground, inter_diff_distrib_right, M.r_eq_r_inter_ground X, 
--     (M.to_r_fin (Y ∩ M.E)).r_eq_r_diff_r_le_zero _ hY], 
-- end 

-- lemma r_eq_r_union_r_le_zero [finite_rk M] (X : set α) (hY : M.r Y ≤ 0) : M.r (X ∪ Y) = M.r X :=
-- begin
--   rw [r_eq_r_inter_ground] at hY, 
--   rw [r_eq_r_inter_ground, inter_distrib_right, (M.to_r_fin _).r_eq_r_union_r_le_zero _ hY, 
--     ←r_eq_r_inter_ground], 
-- end 

-- lemma cl_eq_cl_of_subset_of_r_ge_r [finite_rk M] (hXY : X ⊆ Y) (hr : M.r Y ≤ M.r X) : 
--   M.cl X = M.cl Y :=
-- begin
--   rw [←M.r_cl Y, ←M.r_cl X] at hr,  
--   have hXY' := M.cl_subset hXY, 
--   convert (M.to_r_fin (M.cl Y)).cl_eq_cl_of_subset_of_r_ge_r hXY' hr using 1; simp,  
-- end 

-- lemma r_union_eq_of_subset_of_r_le_r [finite_rk M] (Z : set α) (hXY : X ⊆ Y) (hr : M.r Y ≤ M.r X) :
--   M.r (X ∪ Z) = M.r (Y ∪ Z) :=
-- by rw [←r_cl, ←cl_union_cl_left_eq, cl_eq_cl_of_subset_of_r_ge_r hXY hr, 
--     cl_union_cl_left_eq, r_cl]

-- -- lemma r_union_eq_of_subset_of_r_eqs (hX : X ⊆ X') (hY : Y ⊆ Y')
-- -- (hXX' : M.r X = M.r X') (hYY' : M.r Y = M.r Y') :
-- --   M.r (X ∪ Y) = M.r (X' ∪ Y') :=
-- -- by rw [r_union_eq_of_subset_of_r_eq Y hX hXX', union_comm, union_comm _ Y',
-- --        r_union_eq_of_subset_of_r_eq _ hY hYY']

-- -- lemma r_eq_of_inter_union (X Y A : set α) :
-- --   M.r (X ∩ A) = M.r X → M.r ((X ∩ A) ∪ Y) = M.r (X ∪ Y) :=
-- -- λ h, r_union_eq_of_subset_of_r_eq _ (inter_subset_left _ _) h

-- -- lemma r_eq_of_union_r_diff_eq (Z : set α) (hX : M.r (X \ Y) = M.r X) :
-- --   M.r (Z ∪ (X \ Y)) = M.r (Z ∪ X) :=
-- -- by {rw diff_eq at *, rw [union_comm _ X, ← r_eq_of_inter_union _ Z _ hX, union_comm Z]}

-- lemma r_union_le_add_r (M : matroid_in α) [finite_rk M] (X Y : set α) :
--   M.r (X ∪ Y) ≤ M.r X + M.r Y :=
-- by linarith [M.r_submod X Y]

-- lemma r_union_le_card_add_r (M : matroid_in α) [finite M] (X Y : set α) (hX : X ⊆ M.E . ssE) : 
--   M.r (X ∪ Y) ≤ X.ncard + M.r Y :=
-- (M.r_union_le_add_r X Y).trans (add_le_add_right (M.r_le_card X hX) _)

-- lemma r_union_le_r_add_card (M : matroid_in α) [finite M] (X Y : set α) (hY : Y ⊆ M.E . ssE) : 
--   M.r (X ∪ Y) ≤ M.r X + Y.ncard :=
-- by { rw [add_comm, union_comm], exact M.r_union_le_card_add_r Y X }

-- lemma rk_le_card_add_r_compl (M : matroid_in α) [finite M] (X : set α) (hX : X ⊆ M.E . ssE) :
--   M.rk ≤ X.ncard + M.r (M.E \ X) :=
-- begin
--   rw [rk], 
--   nth_rewrite 0 [←union_diff_cancel hX], 
--   apply r_union_le_card_add_r, 
-- end

-- lemma rank_eq_of_le_supset [finite_rk M] (h : X ⊆ Y) (hr : M.r Y ≤ M.r X) : M.r X = M.r Y :=
-- hr.antisymm' (M.r_mono h)

-- lemma r_le_r_insert (M : matroid_in α) (e : α) (X : set α) : M.r X ≤ M.r (insert e X) :=
-- begin
--   rw [r_eq_r_inter_ground, M.r_eq_r_inter_ground (insert _ _)], 
--   by_cases he : e ∈ M.E, 
--   refine (em (M.r_fin (X ∩ M.E))).elim (λ h, _) (λ h, _), 
--   { rw [insert_inter_of_mem he], 
--     exact (h.insert e he).r_mono (subset_insert _ _) },
--   { rw [r_eq_zero_of_not_r_fin h (inter_subset_right _ _)], apply zero_le }, 
--   rw [insert_inter_of_not_mem he], 
-- end 
  


-- lemma r_insert_eq_of_not_mem_ground (X : set α) (he : e ∉ M.E) : M.r (insert e X) = M.r X :=
-- by rw [r_eq_r_inter_ground, insert_inter_of_not_mem he, ←r_eq_r_inter_ground]

-- lemma r_diff_singleton_eq_of_not_mem_ground (X : set α) (he : e ∉ M.E) : M.r (X \ {e}) = M.r X :=
-- by rw [←r_insert_eq_of_not_mem_ground (X \ {e}) he, insert_diff_singleton, 
--   r_insert_eq_of_not_mem_ground _ he]

-- lemma r_insert_inter_ground (X : set α) (e : α) : 
--   M.r (insert e X) = M.r (insert e (X ∩ M.E)) :=
-- begin
--   rw r_eq_r_inter_ground, 
--   refine (em (e ∈ M.E)).elim (λ he, by rw insert_inter_of_mem he) (λ he, _), 
--   rw [r_insert_eq_of_not_mem_ground _ he, insert_inter_of_not_mem he],
-- end 

-- lemma r_eq_of_le_insert (h : M.r (insert e X) ≤ M.r X) : M.r (insert e X) = M.r X :=
-- h.antisymm (M.r_le_r_insert e X)

-- lemma r_insert_eq_add_one_of_r_ne (h : M.r (insert e X) ≠ M.r X) : M.r (insert e X) = M.r X + 1 :=
-- (nat.lt_iff_add_one_le.mp ((M.r_le_r_insert e X).lt_of_ne h.symm)).antisymm' 
--   (M.r_insert_le_add_one e X)

-- lemma r_insert_eq_add_one_iff_r_ne : M.r (insert e X) = M.r X + 1 ↔ M.r (insert e X) ≠ M.r X :=
-- ⟨by { intro h, rw h, exact (r M X).succ_ne_self } , r_insert_eq_add_one_of_r_ne⟩ 

-- lemma r_le_r_add_r_diff (M : matroid_in α) [finite_rk M] (X Y : set α) : M.r Y ≤ M.r X + M.r (Y \ X) :=
-- le_trans (M.r_mono (by simp)) (r_union_le_add_r M X (Y \ X))

-- lemma r_le_r_diff_singleton_add_one (M : matroid_in α) (e : α) (X : set α) :
--   M.r X ≤ M.r (X \ {e}) + 1 :=
-- begin
--   refine le_trans _ (M.r_insert_le_add_one e (X \ {e})),
--   rw [insert_diff_singleton], 
--   apply r_le_r_insert, 
-- end 

-- lemma r_diff_singleton_add_one_eq_r_of_ne (h_ne : M.r X ≠ M.r (X \ {e})) :
--   M.r X = M.r (X \ {e}) + 1 :=
-- begin
--   refine (em (e ∈ X)).symm.elim (λ h, (h_ne (by rw [diff_singleton_eq_self h])).elim) (λ he, _),
--   convert (@r_insert_eq_add_one_of_r_ne _ _ _ e _);
--   rwa [insert_diff_singleton, insert_eq_of_mem he],
-- end 

-- lemma r_le_r_add_card_diff_of_subset (M : matroid_in α) [finite M] (hXY : X ⊆ Y) 
-- (hYE : Y ⊆ M.E . ssE) : M.r Y ≤ M.r X + (Y \ X).ncard :=
-- by { nth_rewrite 0 ←union_diff_cancel hXY, apply r_union_le_r_add_card }
   
-- lemma r_add_card_le_r_add_card_of_subset (M : matroid_in α) [finite M] (hXY : X ⊆ Y) 
-- (hYE : Y ⊆ M.E . ssE):
--   M.r Y + X.ncard ≤ M.r X + Y.ncard :=
-- begin
--   rw ← ncard_diff_add_ncard_eq_ncard hXY (M.set_finite Y),  
--   linarith [M.r_le_r_add_card_diff_of_subset hXY],
-- end

-- lemma submod_three (M : matroid_in α) [finite_rk M] (X Y Y' : set α) :
--   M.r (X ∪ (Y ∪ Y')) + M.r (X ∪ (Y ∩ Y')) ≤ M.r (X ∪ Y) + M.r (X ∪ Y') :=
-- begin
--   have := M.r_submod (X ∪ Y) (X ∪ Y'),
--   rwa [←union_distrib_left, ←union_union_distrib_left, add_comm] at this,
-- end

-- lemma submod_three_right (M : matroid_in α) [finite_rk M] (X Y Y' : set α) :
--   M.r ((Y ∪ Y') ∪ X) + M.r ((Y ∩ Y') ∪ X) ≤ M.r (Y ∪ X) + M.r (Y' ∪ X) :=
-- by {simp_rw ←(union_comm X), apply submod_three}

-- lemma submod_three_disj (M : matroid_in α) [finite_rk M] (X Y Y' : set α) (hYY' : Y ∩ Y' = ∅) :
--   M.r (X ∪ (Y ∪ Y')) + M.r X ≤ M.r (X ∪ Y) + M.r (X ∪ Y') :=
-- by {have := submod_three M X Y Y', rwa [hYY', union_empty] at this}

-- lemma r_union_add_r_le_r_union_add_r_of_subset (M : matroid_in α) [finite_rk M] (hXY : X ⊆ Y) 
-- (Z : set α) : 
--   M.r (Y ∪ Z) + M.r X ≤ M.r (X ∪ Z) + M.r Y :=
-- begin
--   have hsm := M.r_submod (X ∪ Z) Y,
--   rw [union_right_comm, union_eq_right_iff_subset.mpr hXY, inter_distrib_right,
--     inter_eq_left_iff_subset.mpr hXY, add_comm] at hsm,
--   exact le_trans (add_le_add_left (M.r_le_r_union_left _ _) _) hsm,
-- end


-- lemma r_fin.augment_of_not_r_fin (hX : M.r_fin X) (hZ : ¬M.r_fin Z) (hZ : Z ⊆ M.E . ssE): 
--   ∃ z ∈ Z \ X, M.r (insert z X) = M.r X + 1 := 
-- begin
--   obtain ⟨J, hJ⟩ := M.exists_basis Z, 
--   have hJinf : J.infinite, by rwa [set.infinite, ←hJ.r_fin_iff_finite], 
--   obtain ⟨J', hJ'J, hJfin, hJcard⟩ := hJinf.exists_subset_ncard_eq (M.r X + 1), 
--   obtain ⟨z, ⟨hzJ',hzX⟩, h⟩ := hX.r_augment 
--     (M.r_fin_of_finite hJfin (hJ'J.trans hJ.subset_ground_left)) 
--     (((lt_add_one _).trans_eq hJcard.symm).trans_eq (hJ.indep.subset hJ'J).r.symm), 
--   exact ⟨z, ⟨hJ.subset (hJ'J hzJ'),hzX⟩, h⟩, 
-- end 

-- lemma r_union_eq_of_r_union_subset_le [finite_rk M] (hXY : X ⊆ Y) (h : M.r (X ∪ Z) ≤ M.r X) :
--   M.r (Y ∪ Z) = M.r Y :=
-- begin
--   have hsm := M.r_submod Y (X ∪ Z),
--   rw [←union_assoc, union_eq_left_iff_subset.mpr hXY, inter_distrib_left,
--     inter_eq_right_iff_subset.mpr hXY] at hsm,
--   linarith [M.r_le_r_union_left X (Y ∩ Z), M.r_le_r_union_left Y Z],
-- end

-- lemma r_insert_eq_of_r_insert_subset_le [finite_rk M] (hXY : X ⊆ Y) (h : M.r (insert e X) ≤ M.r X) :
--   M.r (insert e Y) = M.r Y :=
-- by {rw [←union_singleton] at *, rw [r_union_eq_of_r_union_subset_le hXY h],}

-- lemma r_eq_of_r_all_insert_le (hXY : X ⊆ Y) (hY : ∀ e ∈ Y, M.r (insert e X) ≤ M.r X) :
--    M.r X = M.r Y :=
-- begin
--   simp_rw [M.r_eq_r_inter_ground X, M.r_eq_r_inter_ground Y, M.r_eq_r_inter_ground (insert _ _)] 
--     at *,
--   refine (em' (M.r_fin (Y ∩ M.E))).elim (λ hY', _) (λ hY', _), 
--   { refine (em' (M.r_fin (X ∩ M.E))).elim (λ hX, _) (λ hX, _), 
--     { rw [r_eq_zero_of_not_r_fin hX, r_eq_zero_of_not_r_fin hY'] },
--     obtain ⟨z, hz, hr⟩ := hX.augment_of_not_r_fin hY', 
--     have h' := hY z hz.1.1, 
--     rw [←nat.lt_add_one_iff, ←hr, insert_inter_of_mem hz.1.2] at h', 
--     exact (h'.ne rfl).elim },
  
--   have hss : X ∩ M.E ⊆ Y ∩ M.E := (inter_subset_inter_left _ hXY), 
--   refine (hY'.r_mono hss).antisymm (le_of_not_lt (λ hlt, _)), 
--   obtain ⟨z, hz, hr⟩ := (hY'.subset hss).r_augment hY' hlt,  
--   have h' := hY z hz.1.1, 
--   rw [←nat.lt_add_one_iff, ←hr, insert_inter_of_mem hz.1.2] at h', 
--   exact h'.ne rfl, 
-- end

-- lemma r_union_eq_of_r_all_insert_le (hY : ∀ e ∈ Y, M.r (insert e X) ≤ M.r X) : 
--   M.r (X ∪ Y) = M.r X :=
-- begin
--   refine (r_eq_of_r_all_insert_le (subset_union_left X Y) _).symm,
--   rintro e (heX | heY),
--   { rw [insert_eq_of_mem heX]},
--   exact hY _ heY,
-- end

-- lemma r_eq_of_r_all_insert_eq (hXY : X ⊆ Y) (hY : ∀ e ∈ Y, M.r X = M.r (insert e X)) :
--    M.r X = M.r Y :=
-- r_eq_of_r_all_insert_le hXY (λ e h, (hY e h).symm.le)

-- lemma indep_inter_r_zero_eq_empty [finite_rk M] (hI : M.indep I) (hX : M.r X = 0) : I ∩ X = ∅ :=
-- begin
--   have h := hI.subset (inter_subset_left _ X),
--   rw [←ncard_eq_zero (hI.finite.subset (inter_subset_left _ _)), ←le_zero_iff], 
--   rw indep_iff_r_eq_card_of_finite (hI.finite.subset (inter_subset_left _ _)) at h, 
--   rw ←h, exact (M.r_mono (inter_subset_right I X)).trans_eq hX, 
-- end

-- lemma base_iff_indep_card_eq_r [finite_rk M] : M.base B ↔ M.indep B ∧ B.ncard = M.rk :=
-- begin
--   refine ⟨λ hB, ⟨hB.indep, hB.card⟩, 
--     λ h, base_iff_maximal_indep.mpr ⟨h.1, λ I hI hBI, eq_of_subset_of_ncard_le hBI _ hI.finite⟩⟩,
--   rw [h.2], exact hI.card_le_rk,
-- end

-- end basic 

-- section circuit 

-- variables {C : set α}

-- lemma circuit.finite_of_r_fin (hC : M.circuit C) (hCfin : M.r_fin C) : C.finite :=
-- begin
--   obtain ⟨e,he⟩ := hC.nonempty,
--   convert ((hC.diff_singleton_indep he).finite_of_r_fin (hCfin.subset (diff_subset _ _))).insert e, 
--   rw [insert_diff_singleton, insert_eq_of_mem he],  
-- end 

-- lemma circuit.r_fin_iff_finite (hC : M.circuit C) : M.r_fin C ↔ C.finite :=
-- ⟨hC.finite_of_r_fin, M.r_fin_of_finite⟩ 

-- lemma circuit.card_of_finite (hC : M.circuit C) (hfin : C.finite) : C.ncard = M.r C + 1 :=
-- begin
--   obtain ⟨e,he⟩ := hC.nonempty,
--   have hss : C \ {e} ⊂ C, by {refine ssubset_of_ne_of_subset _ (diff_subset _ _),
--     simpa only [ne.def, sdiff_eq_left, disjoint_singleton_right, not_not_mem]},
--   have hlb := (M.r_fin_of_finite hfin).r_mono hss.subset,
--   rw [(hC.ssubset_indep hss).r] at hlb,
--   linarith [ncard_diff_singleton_add_one he hfin, r_lt_card_of_dep_of_finite hfin hC.dep],
-- end 

-- lemma circuit.card [finitary M] (hC : M.circuit C) : C.ncard = M.r C + 1 :=
-- hC.card_of_finite hC.finite

-- /-- This lemma is phrased in terms of `nat` subtraction; it never underflows but is probably still
--   best avoided -/
-- lemma circuit.nat_r_eq [finitary M] (hC : M.circuit C) : M.r C = C.ncard - 1 :=
-- by rw [hC.card, nat.add_succ_sub_one, add_zero]

-- lemma circuit.cast_r_eq [finitary M] (hC : M.circuit C) : (M.r C : ℤ) = C.ncard - 1 :=
-- by rw [hC.card, nat.cast_add, nat.cast_one, add_tsub_cancel_right]

-- lemma exists_circuit_iff_card_lt_rk [finite M] : M.rk < M.E.ncard ↔ ∃ C, M.circuit C :=
-- begin
--   rw [rk, r_lt_card_iff_dep, dep_iff_supset_circuit], 
--   split, 
--   { rintro ⟨C, -, hC⟩, exact ⟨C, hC⟩}, 
--   rintro ⟨C, hC⟩, exact ⟨C, hC.subset_ground, hC⟩, 
-- end 

-- end circuit 

-- section cl_flat

-- variables {F F' F₁ F₂ H H₁ H₂ : set α}

-- lemma flat.r_insert_of_not_mem_of_r_fin (hF : M.flat F) (hfin : M.r_fin F) (he : e ∉ F) 
-- (heE : e ∈ M.E . ssE) :
--   M.r (insert e F) = M.r F + 1 :=
-- begin
--   obtain ⟨I, hI⟩ := M.exists_basis F, 
--   rw [←hF.cl, ←hI.cl, hI.indep.not_mem_cl_iff] at he, 
--   rw [←(hI.insert_basis_insert he.2).card, ←hI.card, 
--     ncard_insert_of_not_mem he.1 (hI.finite_of_r_fin hfin)],
-- end

-- lemma flat.r_insert_of_mem_compl_of_r_fin (hF : M.flat F) (he : e ∈ M.E \ F) (hfin : M.r_fin F) :
--   M.r (insert e F) = M.r F + 1 := hF.r_insert_of_not_mem_of_r_fin hfin he.2 he.1 

-- lemma flat.r_insert_of_mem_compl [finite_rk M] (hF : M.flat F) (he : e ∈ M.E \ F) :
--   M.r (insert e F) = M.r F + 1 := hF.r_insert_of_mem_compl_of_r_fin he (M.to_r_fin F)

-- lemma flat_iff_r_lt_r_insert_forall [finite_rk M] (hFE : F ⊆ M.E . ssE) : 
--   M.flat F ↔ ∀ e ∈ M.E \ F, M.r F < M.r (insert e F) :=
-- begin
--   refine ⟨λ hF e he, _, λ h, _⟩,
--   { rw [hF.r_insert_of_mem_compl he], norm_num },
--   rw [flat_iff_ssubset_cl_insert_forall], 
--   refine λ e he', (M.cl_subset (subset_insert _ _)).ssubset_of_ne (λ h_eq, (h e he').ne _), 
--   rw [←r_cl, h_eq, r_cl], 
-- end

-- lemma flat.mem_compl_iff_r_insert_of_r_fin (hF : M.flat F) (hfin : M.r_fin F) : 
--   e ∈ M.E \ F ↔ M.r (insert e F) = M.r F + 1 :=
-- begin
--   refine (em' (e ∈ M.E)).elim (λ h, iff_of_false (not_mem_subset (diff_subset _ _) h) _) (λ heE, _), 
--   { simp [r_insert_eq_of_not_mem_ground _ h] },
--   refine ⟨λ he, hF.r_insert_of_mem_compl_of_r_fin he hfin, λ h, _⟩,
--   rw [r_insert_eq_add_one_iff_r_ne] at h, 
--   refine by_contra (λ hss, h _), 
--   rw [mem_diff, not_and, not_not] at hss, 
--   rw [insert_eq_of_mem (hss heE)], 
-- end

-- lemma flat.mem_compl_iff_r_insert_eq [finite_rk M] (hF : M.flat F) : 
--   e ∈ M.E \ F ↔ M.r (insert e F) = M.r F + 1 :=
-- hF.mem_compl_iff_r_insert_of_r_fin (M.to_r_fin F)

-- lemma flat.r_lt_r_of_ssubset_of_r_fin (hF : M.flat F) (hFX : F ⊂ X) (hX : M.r_fin X) : 
--   M.r F < M.r X :=
-- begin
--   obtain ⟨e, heX, heF⟩ := exists_of_ssubset hFX, 
--   rw [nat.lt_iff_add_one_le, ←hF.r_insert_of_mem_compl_of_r_fin ⟨_, heF⟩ (hX.subset hFX.subset)], 
--   { exact hX.r_mono (insert_subset.mpr ⟨heX, hFX.subset⟩) },
--   exact hX.subset_ground heX,
-- end 

-- lemma flat.eq_of_r_le_r_subset_of_r_fin (hF : M.flat F) (hFfin : M.r_fin X) (hFX : F ⊆ X) 
-- (hr : M.r X ≤ M.r F) : 
--   F = X :=
-- by_contra (λ hne, (hF.r_lt_r_of_ssubset_of_r_fin (hFX.ssubset_of_ne hne) hFfin).not_le hr)

-- lemma flat.r_lt_r_of_ssubset [finite_rk M] (hF : M.flat F) (hFX : F ⊂ X) (hX : X ⊆ M.E . ssE) :
--   M.r F < M.r X := hF.r_lt_r_of_ssubset_of_r_fin hFX (M.to_r_fin X)

-- lemma flat.eq_of_le_r_subset [finite_rk M] (hF : M.flat F) (hFX : F ⊆ X) (hr : M.r X ≤ M.r F) 
-- (hXE : X ⊆ M.E . ssE) : F = X := hF.eq_of_r_le_r_subset_of_r_fin (M.to_r_fin X) hFX hr  

-- lemma flat.eq_ground_of_rk_le_r [finite_rk M] (hF : M.flat F) (hr : M.rk ≤ M.r F) : F = M.E :=
-- hF.eq_of_le_r_subset hF.subset_ground hr

-- lemma flat.r_eq_rk_iff_eq_ground [finite_rk M] (hF : M.flat F) : M.r F = M.rk ↔ F = M.E :=
-- ⟨λ h, hF.eq_ground_of_rk_le_r h.symm.le, by { rintro rfl, refl }⟩
  
-- lemma r_fin.mem_cl_iff_r_insert (hX : M.r_fin X) (he : e ∈ M.E . ssE) : 
--   e ∈ M.cl X ↔ M.r (insert e X) = M.r X :=
-- by rw [←not_iff_not, ←ne.def, not_mem_iff_mem_diff_of_mem he, ←r_insert_eq_add_one_iff_r_ne, 
--     ←r_insert_cl_eq_r_insert, ←M.r_cl X, (M.flat_of_cl X).mem_compl_iff_r_insert_of_r_fin hX.to_cl]

-- lemma r_fin.not_mem_cl_iff_r_insert (hX : M.r_fin X) :
--   e ∈ M.E \ M.cl X ↔ M.r (insert e X) = M.r X + 1 :=
-- begin
--   rw [r_insert_eq_add_one_iff_r_ne, ne.def], 
--   refine (em' (e ∈ M.E)).elim (λ he, iff_of_false (not_mem_subset (diff_subset _ _) he) 
--     (by simp [r_insert_eq_of_not_mem_ground _ he])) (λ he, _), 
--   rw [← hX.mem_cl_iff_r_insert, mem_diff, and_iff_right he], 
-- end

-- lemma mem_cl_iff_r_insert [finite_rk M] (X : set α) (he : e ∈ M.E . ssE) : 
--   e ∈ M.cl X ↔ M.r (insert e X) = M.r X :=
-- by rw [cl_eq_cl_inter_ground, r_eq_r_inter_ground, insert_inter_of_mem he, 
--       M.r_eq_r_inter_ground X, (M.to_r_fin (X ∩ M.E)).mem_cl_iff_r_insert]

-- lemma mem_compl_cl_iff_r_insert [finite_rk M] : e ∈ M.E \ M.cl X ↔ M.r (insert e X) = M.r X + 1 :=
-- by rw [r_insert_inter_ground, cl_eq_cl_inter_ground, M.r_eq_r_inter_ground X, 
--     (M.to_r_fin (X ∩ M.E)).not_mem_cl_iff_r_insert]

-- lemma subset_cl_iff_r_union_eq_r [finite_rk M] (hX : X ⊆ M.E . ssE) : 
--   X ⊆ M.cl Y ↔ M.r (Y ∪ X) = M.r Y :=
-- begin
--   refine ⟨λ h, _, λ h e heX, _⟩,
--   { rw [←r_union_cl_left_eq_r_union, union_eq_self_of_subset_right h, r_cl] }, 
--   rw [mem_cl_iff_r_insert _ (hX heX)], 
--   refine (M.r_mono (subset_insert _ _)).antisymm' ((M.r_mono _).trans_eq h),
--   exact insert_subset.mpr ⟨or.inr heX, subset_union_left _ _⟩,  
-- end

-- lemma r_insert_eq_add_one_of_not_mem_cl [finite_rk M] (h : e ∈ M.E \ M.cl X) :
--   M.r (insert e X) = M.r X + 1 := mem_compl_cl_iff_r_insert.mp h 

-- lemma mem_compl_cl_of_r_insert_gt [finite_rk M] (h : M.r X < M.r (insert e X)) : e ∈ M.E \ M.cl X :=
-- by { rw [mem_compl_cl_iff_r_insert, r_insert_eq_add_one_iff_r_ne], exact h.ne.symm  }

-- lemma mem_cl_of_r_insert_le [finite_rk M] (h : M.r (insert e X) ≤ M.r X) (he : e ∈ M.E . ssE) :
--   e ∈ M.cl X :=
-- by { rw [mem_cl_iff_r_insert], exact h.antisymm (M.r_mono (subset_insert _ _)) }

-- lemma spanning.r_eq (hX : M.spanning X) : M.r X = M.rk :=
-- by rw [←r_cl, hX.cl, rk]  

-- lemma r_eq_rk_iff_spanning [finite_rk M] (hX : X ⊆ M.E . ssE) : M.r X = M.rk ↔ M.spanning X :=
-- by rw [←r_cl, spanning_iff_cl, (M.flat_of_cl X).r_eq_rk_iff_eq_ground]

-- lemma spanning_iff_r_eq_rk [finite_rk M] : M.spanning X ↔ M.r X = M.rk ∧ X ⊆ M.E :=
-- by { rw [spanning, and.congr_left_iff], intro h, rw [←spanning_iff_cl, r_eq_rk_iff_spanning] }

-- lemma rk_le_r_iff_spanning [finite_rk M] (hX : X ⊆ M.E . ssE) : M.rk ≤ M.r X ↔ M.spanning X :=
-- by rw [←r_eq_rk_iff_spanning, le_iff_lt_or_eq, or_iff_right (M.r_le_rk X).not_lt, eq_comm]

-- lemma r_le_iff_cl {n : ℕ} [finite_rk M] (hX : X ⊆ M.E . ssE) : 
--   M.r X ≤ n ↔ ∃ I, X ⊆ M.cl I ∧ I.ncard ≤ n ∧ I.finite :=
-- begin
--   refine ⟨λ h, _, _⟩,
--   { obtain ⟨I,hI⟩ := M.exists_basis X,
--     exact ⟨I, hI.subset_cl, by rwa hI.card, hI.finite⟩ },
--   rintro ⟨I, hXI, hIn⟩,
--   refine (M.r_mono hXI).trans _, 
--   rw [r_cl],
--   exact (M.r_le_card_of_finite hIn.2).trans hIn.1,
-- end

-- lemma le_r_iff_cl {n : ℕ} [finite_rk M] (hX : X ⊆ M.E . ssE) : 
--   n ≤ M.r X ↔ ∀ I, X ⊆ M.cl I → I.finite → n ≤ I.ncard :=
-- begin
--   cases n, simp,
--   rw [←not_lt, ←not_iff_not, not_not, not_forall],
--   simp_rw [not_imp, not_le, nat.lt_succ_iff],
--   rw r_le_iff_cl,
--   tauto, 
-- end

-- lemma flat.covby_iff_r_of_r_fin (hF : M.flat F) (hFfin : M.r_fin F) (hF' : M.flat F') :
--   M.covby F F' ↔ F ⊆ F' ∧ M.r F' = M.r F + 1 :=
-- begin
--   rw hF.covby_iff_eq_cl_insert, 
--   refine ⟨_, λ h, _⟩, 
--   { rintro ⟨e, he, rfl⟩,
--     rw [and_iff_right 
--       (M.subset_cl_of_subset (subset_insert e F) (insert_subset.mpr ⟨he.1, hF.subset_ground⟩)), 
--       r_cl, (hF.mem_compl_iff_r_insert_of_r_fin hFfin).mp he],  }, 
--   have hss : F ⊂ F', from h.1.ssubset_of_ne (by { rintro rfl, simpa using h.2 }), 
--   obtain ⟨e, heF', heF⟩ := exists_of_ssubset hss, 
--   refine ⟨e, ⟨hF'.subset_ground heF',heF⟩, 
--     ((M.flat_of_cl _).eq_of_r_le_r_subset_of_r_fin _ _ _).symm⟩, 
--   { refine r_fin_of_r_ne_zero _, rw h.2, exact nat.succ_ne_zero _ },
--   { exact hF'.cl_subset_of_subset (insert_subset.mpr ⟨heF', h.1⟩) },
--   rw [h.2, r_cl, hF.r_insert_of_mem_compl_of_r_fin ⟨hF'.subset_ground heF',heF⟩ hFfin], 
-- end 

-- lemma flat.covby_iff_r [finite_rk M] (hF : M.flat F) (hF' : M.flat F') : 
--   M.covby F F' ↔ F ⊆ F' ∧ M.r F' = M.r F + 1 :=
-- hF.covby_iff_r_of_r_fin (M.to_r_fin F) hF'  

-- lemma hyperplane_iff_maximal_r [finite_rk M] (hH : H ⊆ M.E . ssE) : 
--   M.hyperplane H ↔ M.r H < M.rk ∧ ∀ X, H ⊂ X → X ⊆ M.E → M.r X = M.rk :=
-- begin
--   simp_rw [hyperplane_iff_maximal_nonspanning, mem_maximals_set_of_iff', not_and, not_not, 
--     lt_iff_not_le, and_iff_right hH, rk_le_r_iff_spanning, and.congr_right_iff], 
--   refine λ hH, ⟨λ h X hHX hXE, spanning.r_eq (h hHX hXE), λ h X hHX hXE, _⟩,
--   rw spanning_iff_r_eq_rk, 
--   exact ⟨h X hHX hXE, hXE⟩,
-- end 

-- lemma hyperplane.r_add_one [finite_rk M] (hH : M.hyperplane H) : M.r H + 1 = M.rk :=
-- by rw [←((hH.flat.covby_iff_r M.ground_flat).mp hH.covby).2, rk]

-- lemma hyperplane.cast_r [finite_rk M] (hH : M.hyperplane H) : (M.r H : ℤ) = M.rk - 1 := 
-- by simp [←hH.r_add_one]

-- lemma flat.hyperplane_of_r_add_one_eq_rk [finite_rk M] (hF : M.flat F) (h : M.r F + 1 = M.rk) :
--   M.hyperplane F :=
-- by rwa [hyperplane_iff_covby, hF.covby_iff_r M.ground_flat, and_iff_right hF.subset_ground, eq_comm]

-- lemma hyperplane_iff_flat_r_add_one_eq_r [finite_rk M] : 
--   M.hyperplane H ↔ M.flat H ∧ M.r H + 1 = M.rk :=
-- ⟨λ h, ⟨h.flat, h.r_add_one⟩, λ h, h.1.hyperplane_of_r_add_one_eq_rk h.2⟩

-- end cl_flat

-- section loop

-- lemma loop_iff_r (he : e ∈ M.E . ssE) : M.loop e ↔ M.r {e} = 0 :=
-- by rw [loop_iff_dep, ←r_lt_card_iff_dep_of_finite (finite_singleton e), ncard_singleton, 
--   nat.lt_one_iff]

-- lemma loop.r (he : M.loop e) : M.r {e} = 0 := loop_iff_r.mp he 

-- lemma r_eq_zero_iff_subset_loops [finite_rk M] (hX : X ⊆ M.E . ssE) : M.r X = 0 ↔ X ⊆ M.cl ∅ :=
-- (M.to_r_fin X).r_eq_zero_iff_subset_loops

-- lemma r_eq_zero_iff_inter_ground_subset_loops [finite_rk M] : M.r X = 0 ↔ X ∩ M.E ⊆ M.cl ∅ :=
-- by rw [←r_eq_zero_iff_subset_loops, r_eq_r_inter_ground]

-- lemma r_eq_zero_iff_forall_loop [finite_rk M] (hX : X ⊆ M.E . ssE) :
--   M.r X = 0 ↔ ∀ e ∈ X, M.loop e :=
-- r_eq_zero_iff_subset_loops

-- lemma r_eq_zero_of_subset_loops (h : X ⊆ M.cl ∅) : M.r X = 0 := 
-- by rw [←r_cl, cl_eq_loops_of_subset h, r_cl, r_empty]

-- lemma nonloop_iff_r : M.nonloop e ↔ M.r {e} = 1 :=
-- by rw [←indep_singleton, indep_iff_r_eq_card_of_finite (finite_singleton e), ncard_singleton]

-- lemma nonloop.r (he : M.nonloop e) : M.r {e} = 1 := nonloop_iff_r.mp he 

-- lemma coloop.r_compl_add_one [finite_rk M] (he : M.coloop e) : M.r (M.E \ {e}) + 1 = M.rk :=
-- begin
--   have := he.mem_ground,
--   rw [coloop_iff_cocircuit, ←compl_hyperplane_iff_cocircuit, hyperplane_iff_flat_r_add_one_eq_r] 
--     at he, 
--   exact he.2, 
-- end

-- lemma coloop_iff_r_compl_add_one_eq [finite_rk M] : M.coloop e ↔ M.r (M.E \ {e}) + 1 = M.rk :=
-- begin
--   refine ⟨coloop.r_compl_add_one, λ h, _⟩, 
--   have he : e ∈ M.E, 
--   { by_contra he', rw [r_diff_singleton_eq_of_not_mem_ground _ he', rk_def] at h, simpa using h },
--   rw [coloop_iff_cocircuit, ←compl_hyperplane_iff_cocircuit (singleton_subset_iff.mpr he), 
--     hyperplane_iff_flat_r_add_one_eq_r, and_iff_left h], 
--   simp_rw [flat_iff_r_lt_r_insert_forall, sdiff_sdiff_right_self, inf_eq_inter, 
--     ground_inter_right, mem_singleton_iff, forall_eq, insert_diff_singleton, insert_eq_of_mem he, 
--     ←rk_def, nat.lt_iff_add_one_le], 
--   rw h,
-- end

-- lemma coloop_iff_r_compl_lt [finite_rk M] : M.coloop e ↔ M.r (M.E \ {e}) < M.rk :=
-- by rw [coloop_iff_r_compl_add_one_eq, rk_def, nat.lt_iff_add_one_le, le_antisymm_iff, 
--     and_iff_left (M.r_le_r_diff_singleton_add_one e M.E)]

-- lemma coloop.cast_r_compl [finite_rk M] (he : M.coloop e) : (M.r (M.E \ {e}) : ℤ) = M.rk - 1 :=
-- by simp [←he.r_compl_add_one]

-- end loop 

-- section flat_of_r

-- variables {F F' P L : set α}

-- /-- `M.flat_of_r k F` means that `F` is a flat in `r` with finite rank `k`. -/
-- def flat_of_r (M : matroid_in α) (k : ℕ) (F : set α) := M.flat F ∧ M.r F = k ∧ M.r_fin F  

-- lemma flat_of_r.flat (h : M.flat_of_r k F) : M.flat F := h.1 

-- @[ssE_finish_rules] lemma flat_of_r.subset_ground (h : M.flat_of_r k F) : F ⊆ M.E :=
-- h.flat.subset_ground 

-- lemma flat_of_r.r (h : M.flat_of_r k F) : M.r F = k := h.2.1 

-- lemma flat_of_r.r_fin (h : M.flat_of_r k F) : M.r_fin F := h.2.2 

-- lemma flat.flat_of_r_of_ne_zero (hF : M.flat F) (hk : M.r F ≠ 0) : M.flat_of_r (M.r F) F :=
-- ⟨hF, rfl, r_fin_of_r_ne_zero hk⟩  

-- lemma flat.flat_of_r_of_ne_zero' (hF : M.flat F) (hr : M.r F = k) (hk : k ≠ 0) : 
--   M.flat_of_r (M.r F) F :=
-- hF.flat_of_r_of_ne_zero (by { subst hr, assumption } )   

-- lemma flat_of_r.nonempty (hF : M.flat_of_r k F) (hk : k ≠ 0) : F.nonempty := 
-- nonempty_of_r_nonzero (ne_of_eq_of_ne hF.r hk)

-- @[simp] lemma flat_of_r_zero_iff_loops : M.flat_of_r 0 F ↔ F = M.cl ∅ :=
-- begin
--   refine ⟨λ h,_, _⟩,
--   { obtain ⟨I, hI⟩ := M.exists_basis F, 
--     have hc := hI.card, 
--     rw [h.r, ncard_eq_zero (hI.finite_of_r_fin h.r_fin)] at hc, subst hc, 
--     rw [←h.flat.cl, hI.cl] },
--   rintro rfl, 
--   exact ⟨M.flat_of_cl _, by simp, M.r_fin_empty.to_cl⟩,   
-- end

-- lemma loops_flat_of_r_zero (M : matroid_in α) : M.flat_of_r 0 (M.cl ∅) :=
-- by rw flat_of_r_zero_iff_loops

-- lemma flat_of_r.covby_iff (hF : M.flat_of_r k F) : M.covby F F' ↔ M.flat_of_r (k+1) F' ∧ F ⊆ F' :=
-- begin
--   refine (em (M.flat F')).symm.elim (λ hF', iff_of_false (mt covby.flat_right hF') _) (λ hF', _), 
--   { exact mt (λ h, h.1.flat) hF' },
--   have hr := hF.r, subst hr, 
--   simp_rw [hF.flat.covby_iff_r_of_r_fin hF.r_fin hF', flat_of_r, and_comm, and.congr_right_iff, 
--     ← and_assoc, iff_and_self, and_iff_right hF'], 
--   refine λ h hF', r_fin_of_r_ne_zero _, 
--   rw hF', 
--   simp,  
-- end 

-- lemma flat_of_r.flat_of_r_add_one_of_covby (hF : M.flat_of_r k F) (hFF' : M.covby F F') : 
--   M.flat_of_r (k+1) F' := 
-- by { rw [hF.covby_iff] at hFF', exact hFF'.1 }

-- /-- A `point` is a rank-one flat -/
-- def point (M : matroid_in α) (P : set α) := M.flat_of_r 1 P 

-- /-- A `line` is a rank-two flat -/
-- def line (M : matroid_in α) (L : set α) := M.flat_of_r 2 L

-- /-- A `plane` is a rank-three flat -/
-- def plane (M : matroid_in α) (P : set α) := M.flat_of_r 3 P

-- lemma point.nonempty (hP : M.point P) : P.nonempty := flat_of_r.nonempty hP one_ne_zero

-- @[ssE_finish_rules] lemma point.subset_ground (hP : M.point P) : P ⊆ M.E := hP.flat.subset_ground 

-- lemma line.nonempty (hL : M.line L) : L.nonempty := flat_of_r.nonempty hL two_ne_zero

-- @[ssE_finish_rules] lemma line.subset_ground (hL : M.line L) : L ⊆ M.E := hL.flat.subset_ground 

-- lemma plane.nonempty (hP : M.plane P) : P.nonempty := flat_of_r.nonempty hP three_pos.ne.symm 

-- @[ssE_finish_rules] lemma plane.subset_ground (hP : M.plane P) : P ⊆ M.E := hP.flat.subset_ground 

-- lemma nonloop.cl_point (he : M.nonloop e) : M.point (M.cl {e}) := 
-- begin
--   rw [point, ←ncard_singleton e, ←he.indep.r, ←r_cl ],
--   exact (M.flat_of_cl _).flat_of_r_of_ne_zero (by { rw [r_cl, he.indep.r], simp }), 
-- end

-- lemma point.diff_loops_nonempty (hP : M.point P) : (P \ M.cl ∅).nonempty := 
-- nonempty_of_r_nonzero (by { rw [←r_cl, cl_diff_loops_eq_cl, r_cl, hP.r], exact one_ne_zero })

-- lemma point.exists_eq_cl_nonloop (hP : M.point P) : ∃ e, M.nonloop e ∧ P = M.cl {e} := 
-- begin
--   obtain ⟨I, hI⟩ := M.exists_basis P,
--   have hc := hI.card, 
--   rw [hP.r, ncard_eq_one] at hc, 
--   obtain ⟨e, rfl⟩ := hc, 
--   use e, 
--   rw [hI.cl, hP.flat.cl, and_iff_left rfl, nonloop_iff_r, hI.r, hP.r], 
-- end 

-- lemma point.eq_cl_nonloop (hP : M.point P) (heP : e ∈ P) (he : M.nonloop e) : P = M.cl {e} := 
-- begin
--   obtain ⟨I, hI, heI⟩ := he.indep.subset_basis_of_subset (singleton_subset_iff.mpr heP), 
--   have hc := hI.card, 
--   rw [hP.r, ncard_eq_one] at hc,  
--   obtain ⟨e', rfl⟩ := hc, 
--   simp only [subset_singleton_iff, mem_singleton_iff, forall_eq] at heI, 
--   rw [←hP.flat.cl, ←hI.cl, heI], 
-- end 

-- /-- The set of elements that span a point are precisely its nonloop members -/
-- lemma point.eq_cl_singleton_iff (h : M.point P) : M.cl {e} = P ↔ e ∈ P ∧ M.nonloop e :=
-- begin
--   simp only [nonloop, loop, ←mem_diff,  mem_preimage, mem_singleton_iff], 
--   refine ⟨_, λ hP, _⟩,
--   { rintro rfl, 
--     have hel : M.nonloop e,
--     { have he' := h.r, rwa [r_cl, ←nonloop_iff_r] at he',  }, 
--     exact ⟨M.mem_cl_self e, hel.not_loop, hel.mem_ground⟩ },
--   have he : M.nonloop e := hP.2, 
--   obtain ⟨J, hJ, heJ⟩ :=  he.indep.subset_basis_of_subset (singleton_subset_iff.mpr hP.1), 
--   have hJcard := hJ.card, 
--   rw [h.r, ncard_eq_one] at hJcard, 
--   obtain ⟨e', rfl⟩ := hJcard, 
--   simp only [subset_singleton_iff, mem_singleton_iff, forall_eq] at heJ, subst heJ,   
--   rw [←h.flat.cl, hJ.cl], 
-- end 

-- lemma point_iff_loops_covby : M.point P ↔ M.covby (M.cl ∅) P := 
-- begin
--   rw [flat_of_r.covby_iff M.loops_flat_of_r_zero, zero_add, point, iff_self_and],  
--   exact λ h, h.flat.loops_subset,  
-- end

-- end flat_of_r

-- -- section from_axioms

-- -- /-- There doesn't seem to be a nice way to axiomatize finite-rank matroids on infinite ground sets 
-- --   without a 'bases for sets exist'-type axiom. A troublesome example is the rank-1 non-matroid where 
-- --   the only rank-1 set is the (infinite) ground set, which satisfies finite versions of submodularity
-- --   but has no nonempty independent sets.  -/

-- -- lemma card_le_r_of_card_le_r_of_subset [finite E] (r : set α → ℕ) (r_le_card : ∀ X, r X ≤ X.ncard)
-- -- (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) {I J : set α} 
-- -- (hJ : J.ncard ≤ r J) (hIJ : I ⊆ J) :
-- --   I.ncard ≤ r I :=
-- -- begin
-- --   have hsm := r_submod I (J \ I), 
-- --   rw [inter_diff_self, union_diff_self, union_eq_self_of_subset_left hIJ] at hsm,  
-- --   linarith [r_le_card (J \ I), ncard_diff_add_ncard_eq_ncard hIJ], 
-- -- end    

-- -- lemma r_eq_r_of_maximal_indep [finite E] (r : set α → ℕ) (r_le_card : ∀ X, r X ≤ X.ncard)
-- -- (r_mono : ∀ ⦃X Y⦄, X ⊆ Y → r X ≤ r Y) (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) 
-- -- (I X : set α) (hI : I ∈ maximals (⊆) {J | J ⊆ X ∧ J.ncard ≤ r J}) : 
-- --   r I = r X :=
-- -- begin  
-- --   obtain ⟨J, ⟨hJX, hIJ, hJ⟩, hJmax⟩ :=
-- --     (to_finite X).maximals_nonempty_of_exists (λ J, I ⊆ J ∧ r J ≤ r I) hI.1.1 ⟨subset.rfl, rfl.le⟩,  
-- --   obtain (rfl | hss) := hJX.eq_or_ssubset, 
-- --   { exact hJ.antisymm' (r_mono hIJ) },
-- --   obtain ⟨e, heX, heJ⟩ := exists_of_ssubset hss, 
-- --   have hsm := r_submod (insert e I) J, 
-- --   rw [insert_union, union_eq_self_of_subset_left hIJ] at hsm, 
-- --   have heI : r (insert e I) ≤ r I,
-- --   { refine (em (e ∈ I)).elim (λ heI, by rw insert_eq_of_mem heI) (λ heI, le_of_not_lt (λ hlt, _)),
-- --     refine heI (hI.2 ⟨insert_subset.mpr ⟨heX, hI.1.1⟩, _⟩ (subset_insert e I) (mem_insert e I)),
-- --     linarith [hI.1.2, nat.lt_iff_add_one_le.mp hlt, ncard_insert_of_not_mem heI] },
-- --   have heJ : r I + 1 ≤ r (insert e J), 
-- --   { refine nat.add_one_le_iff.mpr (lt_of_not_le (λ hle, heJ _)), 
-- --     exact (hJmax ⟨insert_subset.mpr ⟨heX, hss.subset⟩, ⟨hIJ.trans (subset_insert e J), hle⟩⟩ 
-- --       (subset_insert e J) (mem_insert e J)) },
-- --   linarith [r_mono (subset_inter (subset_insert e I) hIJ)], 
-- -- end 

-- -- def matroid_of_r [finite E] (r : set α → ℕ) (r_le_card : ∀ X, r X ≤ X.ncard)
-- -- (r_mono : ∀ ⦃X Y⦄, X ⊆ Y → r X ≤ r Y) (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) : 
-- --   matroid_in α :=
-- -- matroid_of_indep_of_finite (λ I, I.ncard ≤ r I) (by { use ∅, simp,   })   
-- -- (λ I J, card_le_r_of_card_le_r_of_subset r ‹_› ‹_›)
-- -- (begin
-- --   intros I J hI hJ hIJ, 
-- --   by_contra' h', 
-- --   have con := r_eq_r_of_maximal_indep r ‹_› ‹_› ‹_› I (I ∪ J) ⟨⟨subset_union_left _ _, hI⟩, _⟩,     
-- --   { exact (r_le_card I).not_lt 
-- --       ((hIJ.trans_le (hJ.trans (r_mono (subset_union_right I J)))).trans_eq con.symm) },
-- --   exact λ K hK hIK e heK, by_contra (λ heI, 
-- --     ((card_le_r_of_card_le_r_of_subset r ‹_› ‹_› hK.2 (insert_subset.mpr ⟨heK, hIK⟩)).not_lt 
-- --       (h' _ ((hK.1 heK).elim (false.elim ∘ heI) id) heI ))), 
-- -- end) 

-- -- @[simp] lemma matroid_of_r_apply [finite E] (r : set α → ℕ) (r_le_card : ∀ X, r X ≤ X.ncard)
-- -- (r_mono : ∀ ⦃X Y⦄, X ⊆ Y → r X ≤ r Y) (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) :
-- -- (matroid_of_r r r_le_card r_mono r_submod).r  = r :=
-- -- begin
-- --   ext X, 
-- --   obtain ⟨I, hI⟩ := (matroid_of_r r ‹_› ‹_› ‹_›).exists_basis X, 
-- --   rw [←hI.card], 
-- --   simp_rw [matroid_of_r, basis_iff, matroid_of_indep_of_finite_apply] at hI,  
-- --   rw [hI.1.antisymm (r_le_card I), r_eq_r_of_maximal_indep r ‹_› ‹_› ‹_›], 
-- --   exact ⟨⟨hI.2.1,hI.1⟩, λ J hJ hIJ, (hI.2.2 J hJ.2 hIJ hJ.1).symm.subset⟩
-- -- end 

-- -- /-- Construction of a matroid from an `int`-valued rank function that is everywhere nonnegative,
-- --   rather than a `nat`-valued one. Useful for defining matroids whose rank function involves
-- --   subtraction. -/
-- -- def matroid_of_int_r [finite E] (r : set α → ℤ) (r_nonneg : ∀ X, 0 ≤ r X) 
-- -- (r_le_card : ∀ X, r X ≤ X.ncard) (r_mono : ∀ X Y, X ⊆ Y → r X ≤ r Y) 
-- -- (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) :
-- --   matroid_in α :=
-- -- matroid_of_r (int.nat_abs ∘ r)
-- --   (λ X, by {zify, convert r_le_card X, rw abs_eq_self, apply r_nonneg})
-- --   (λ X Y hXY, by {zify, convert r_mono X Y hXY, all_goals {rw abs_eq_self, apply r_nonneg}})
-- --   (λ X Y, by {zify, convert r_submod X Y, all_goals {rw abs_eq_self, apply r_nonneg}})

-- -- @[simp] lemma matroid_of_int_r_apply [finite E] (r : set α → ℤ) (r_nonneg : ∀ X, 0 ≤ r X)
-- -- (r_le_card : ∀ X, r X ≤ X.ncard) (r_mono : ∀ X Y, X ⊆ Y → r X ≤ r Y)
-- -- (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) (X : set α) :
-- --   ((matroid_of_int_r r r_nonneg r_le_card r_mono r_submod).r X : ℤ) = r X :=
-- -- by simpa [matroid_of_int_r] using r_nonneg _

-- -- end from_axioms

-- -- section dual

-- -- variables [finite E]

-- -- lemma coindep_iff_r : M.coindep X ↔ M.r Xᶜ = M.rk :=
-- -- begin
-- --   rw [coindep_iff_disjoint_base],
-- --   split,
-- --   { rintros ⟨B,hB,hBX⟩,
-- --     refine le_antisymm (M.r_le_rk _) _,
-- --     rw ←subset_compl_iff_disjoint_left at hBX,
-- --     rw [←hB.r],
-- --     exact M.r_mono hBX },
-- --   intro hr,
-- --   obtain ⟨B, hB⟩ := M.exists_basis Xᶜ,
-- --   refine ⟨B, hB.indep.base_of_rk_le_card _, subset_compl_iff_disjoint_left.mp hB.subset⟩,
-- --   rw [←hB.indep.r, hB.r, hr],
-- -- end

-- -- lemma dual_r_add_rk_eq (M : matroid_in α) (X : set α) : M﹡.r X + M.rk = ncard X + M.r Xᶜ  :=
-- -- begin
-- --   set r' : set α → ℤ := λ X, X.ncard + M.r Xᶜ - M.rk with hr',

-- --   have hr'_nonneg : ∀ X, 0 ≤ r' X,
-- --   { intro X, simp_rw hr', linarith [M.rk_le_card_add_r_compl X]},
-- --   have hr'_mono : ∀ X Y, X ⊆ Y → r' X ≤ r' Y,
-- --   { intros X Y hXY, simp_rw hr',
-- --     linarith [M.r_add_card_le_r_add_card_of_subset (compl_subset_compl.mpr hXY),
-- --        ncard_add_ncard_compl X, ncard_add_ncard_compl Y]},
-- --   have hr'_le_card : ∀ X, r' X ≤ X.ncard,
-- --   { intros X, simp_rw hr', linarith [M.r_le_rk Xᶜ] },
-- --   have hr'_submod : ∀ X Y, r' (X ∩ Y) + r' (X ∪ Y) ≤ r' X + r' Y,
-- --   { intros X Y, simp_rw [hr', compl_inter, compl_union],
-- --     linarith [ncard_inter_add_ncard_union X Y, M.r_submod Xᶜ Yᶜ]},

-- --   set M' := matroid_of_int_r r' hr'_nonneg hr'_le_card hr'_mono hr'_submod with hM',

-- --   have hM'M : M' = M﹡,
-- --   { refine eq_of_indep_iff_indep_forall (λ I, _),
-- --     rw [indep_iff_r_eq_card, dual_indep_iff_coindep, coindep_iff_r], zify,
-- --     simp_rw [hM', matroid_of_int_r_apply, hr'],
-- --     refine ⟨λ h, _, λ h, _⟩,
-- --     all_goals { simp only at h, linarith} },

-- --   rw [←hM'M], zify, simp_rw [hM', matroid_of_int_r_apply, hr'],
-- --   ring,
-- -- end

-- -- lemma dual_r_cast_eq (M : matroid_in α) (X : set α) : (M﹡.r X : ℤ) = ncard X + M.r Xᶜ - M.rk :=
-- -- by linarith [M.dual_r_add_rk_eq X]

-- -- end dual 

-- end matroid_in
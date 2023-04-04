import .circuit

noncomputable theory
open_locale classical
open_locale big_operators


/-
  Flats and closure.

  TODO : Flats are a `modular_lattice`
-/

variables {E : Type*} [finite E] {M M₁ M₂ : matroid E}
  {I I₁ I₂ B₁ B₂ J B C X Y Z F F₀ F₁ F₂ H H₁ H₂ : set E} {e f x y z : E}

open set

namespace matroid

lemma flat_def :
  M.flat F ↔ ∀ I X, M.basis I F → M.basis I X → X ⊆ F  :=
iff.rfl

lemma flat.r_insert_of_not_mem (hF : M.flat F) (he : e ∉ F) :
  M.r (insert e F) = M.r F + 1 :=
begin
  suffices h' : M.r F < M.r (insert e F),
  { rw (nat.lt_iff_add_one_le.mp h').antisymm (M.r_insert_le_add_one F e)},
  obtain ⟨I,hI⟩ := M.exists_basis F,
  have hnb : ¬ M.basis I (insert e F),
    from λ hI', he (hF I (insert e F) hI hI' (mem_insert e F)),
  by_contra' h_le,
  exact hnb (hI.indep.basis_of_subset_of_r_le (hI.subset.trans (subset_insert _ _))
    (h_le.trans_eq hI.r.symm)),
end

lemma flat_iff_r_lt_r_insert :
  M.flat F ↔ ∀ e ∉ F, M.r F < M.r (insert e F) :=
begin
  refine ⟨λ hF e heF, nat.lt_iff_add_one_le.mpr (hF.r_insert_of_not_mem heF).symm.le,
    λ h, flat_def.mpr (λ I X hIF hIX, _)⟩,
  by_contra' hXF,
  obtain ⟨e,heX,heF⟩ := not_subset.mp hXF,
  apply (h e heF).ne,
  rw [←hIF.r_eq_r_insert, hIX.r_eq_r_insert, insert_eq_of_mem heX, ←hIF.r, ←hIX.r],
end

lemma flat.not_mem_iff_r_insert (hF : M.flat F) :
  e ∉ F ↔ M.r (insert e F) = M.r F + 1 :=
begin
  refine ⟨hF.r_insert_of_not_mem, λ h he, _⟩,
  rw [insert_eq_of_mem he, self_eq_add_right] at h,
  simpa only using h,
end

lemma flat.Inter {ι : Type*} (F : ι → set E) (hF : ∀ i, M.flat (F i)) :
  M.flat (⋂ i, F i) :=
begin
  simp_rw [flat_iff_r_lt_r_insert],
  by_contra' h,
  obtain ⟨e, he, hre⟩ := h,
  rw [mem_Inter, not_forall] at he,
  obtain ⟨j, hj⟩ := he,
  have hj' := (hF j).r_insert_of_not_mem hj,
  rw r_insert_eq_of_r_insert_subset_le (Inter_subset F j) hre at hj',
  simpa using hj',
end

lemma flat.inter (hF₁ : M.flat F₁) (hF₂ : M.flat F₂) :
  M.flat (F₁ ∩ F₂) :=
begin
  rw inter_eq_Inter,
  refine flat.Inter _ (λ i, _),
  cases i; assumption,
end

lemma univ_flat (M : matroid E) :
  M.flat univ :=
flat_iff_r_lt_r_insert.mpr (λ e he, (he (mem_univ e)).elim)

lemma exists_flat_not_mem_of_r_insert_ne (M : matroid E) (h : M.r (insert e X) ≠ M.r X):
  ∃ F, M.flat F ∧ X ⊆ F ∧ e ∉ F :=
begin
  have hr := r_insert_eq_add_one_of_r_ne h,
  have heX : e ∉ X,
  { intro heX, rw [insert_eq_of_mem heX] at h, exact h rfl},
  obtain ⟨F, ⟨hXF, hF⟩, hF'⟩ :=
    finite.exists_maximal (λ F, X ⊆ F ∧ M.r F ≤ M.r X) ⟨X, rfl.subset, rfl.le⟩,
  dsimp only at hF',
  have heF : e ∉ F,
  { intro heF,
    simpa only [add_le_iff_nonpos_right, le_zero_iff, hr, ←(hF.antisymm (M.r_mono hXF))] using
      M.r_mono (insert_subset.mpr ⟨heF, hXF⟩)},
  refine ⟨F, flat_iff_r_lt_r_insert.mpr (λ f hfF, _), hXF, heF⟩,
  by_contra' hle,
  rw hF' (insert f F) ⟨hXF.trans (subset_insert _ _), hle.trans hF⟩ (subset_insert _ _) at hfF,
  simpa only [mem_insert_iff, eq_self_iff_true, true_or, not_true] using hfF,
end

lemma cl_def (M : matroid E) : M.cl X = ⋂₀ {F | M.flat F ∧ X ⊆ F} := rfl

lemma mem_cl_iff_forall_mem_flat :
  e ∈ M.cl X ↔ ∀ F, M.flat F → X ⊆ F → e ∈ F :=
by simp_rw [cl_def, mem_sInter, mem_set_of_eq, and_imp]

lemma flat_of_cl (M : matroid E) (X : set E) :
  M.flat (M.cl X) :=
begin
  rw [cl_def, sInter_eq_Inter],
  refine flat.Inter _ _,
  rintro ⟨F,hF⟩,
  exact hF.1,
end

lemma subset_cl (M : matroid E) (X : set E) :
  X ⊆ M.cl X :=
by simp only [cl_def, subset_sInter_iff, mem_set_of_eq, and_imp, imp_self, implies_true_iff]

lemma mem_cl :
  e ∈ M.cl X ↔ M.r (insert e X) = M.r X :=
begin
  have hF := M.flat_of_cl X,
  rw flat_iff_r_lt_r_insert at hF,
  refine ⟨λ hecl, by_contra (λ hne, _),λ h, by_contra (λ heX, (hF e heX).ne _)⟩,
  { have hlem : ∃ F, M.flat F ∧ X ⊆ F ∧ e ∉ F,
    { have hr := r_insert_eq_add_one_of_r_ne hne,
      have heX : e ∉ X,
      { intro heX, rw [insert_eq_of_mem heX] at hne, exact hne rfl},
      obtain ⟨F, ⟨hXF, hF⟩, hF'⟩ :=
        finite.exists_maximal (λ F, X ⊆ F ∧ M.r F ≤ M.r X) ⟨X, rfl.subset, rfl.le⟩,
      dsimp only at hF',
      have heF : e ∉ F,
      { intro heF,
        simpa only [add_le_iff_nonpos_right, le_zero_iff, hr, ←(hF.antisymm (M.r_mono hXF))] using
          M.r_mono (insert_subset.mpr ⟨heF, hXF⟩)},
      refine ⟨F, flat_iff_r_lt_r_insert.mpr (λ f hfF, _), hXF, heF⟩,
      by_contra' hle,
      rw hF' (insert f F) ⟨hXF.trans (subset_insert _ _), hle.trans hF⟩ (subset_insert _ _) at hfF,
      simpa only [mem_insert_iff, eq_self_iff_true, true_or, not_true] using hfF},
    obtain ⟨F, hF, hXf, heF⟩ := hlem,
    rw mem_cl_iff_forall_mem_flat at hecl,
    exact heF (hecl _ hF hXf)},
  rw r_insert_eq_of_r_insert_subset_le (M.subset_cl X) h.le,
end

lemma not_mem_cl :
  e ∉ M.cl X ↔ M.r (insert e X) = M.r X + 1 :=
begin
  rw [mem_cl, ←ne.def],
  refine ⟨r_insert_eq_add_one_of_r_ne, λ h,
    by simp only [h, ne.def, nat.succ_ne_self, not_false_iff]⟩,
end

@[simp] lemma r_cl (M : matroid E) (X : set E) :
  M.r (M.cl X) = M.r X :=
(r_eq_of_r_all_insert_eq (M.subset_cl X) (λ e h, (mem_cl.mp h).symm)).symm

@[simp] lemma cl_cl (M : matroid E) (X : set E) :
  M.cl (M.cl X) = M.cl X :=
begin
  ext x,
  simp_rw [mem_cl, r_cl],
  refine ⟨λ h, (M.r_mono (subset_insert _ _)).antisymm' _, λ h, _⟩,
  { rw ←h,
    exact M.r_mono (insert_subset_insert (M.subset_cl _))},
  convert (@r_union_eq_of_subset_of_r_eq _ _ M _ _ (M.cl X) (subset_insert x X) h.symm).symm
    using 1,
  { rw [insert_union, union_eq_right_iff_subset.mpr (M.subset_cl X)]},
  rw [union_eq_right_iff_subset.mpr (M.subset_cl X), r_cl],
end

lemma cl_subset_cl_of_subset (M : matroid E) (h : X ⊆ Y) :
  M.cl X ⊆ M.cl Y :=
sInter_subset_sInter (λ F hF, ⟨hF.1, h.trans hF.2⟩)

lemma cl_mono (M : matroid E) : monotone M.cl :=
  λ _ _, M.cl_subset_cl_of_subset

lemma cl_subset_cl_of_subset_cl (hXY : X ⊆ M.cl Y) :
  M.cl X ⊆ M.cl Y :=
by simpa only [cl_cl] using M.cl_subset_cl_of_subset hXY

lemma cl_subset_cl_iff_subset_cl :
  M.cl X ⊆ M.cl Y ↔ X ⊆ M.cl Y :=
⟨λ h, (M.subset_cl _).trans h, cl_subset_cl_of_subset_cl⟩

lemma subset_cl_of_subset (M : matroid E) (hXY : X ⊆ Y) :
  X ⊆ M.cl Y :=
hXY.trans (M.subset_cl Y)

lemma mem_cl_of_mem (M : matroid E) (h : e ∈ X) :
  e ∈ M.cl X :=
(M.subset_cl X) h

lemma r_insert_eq_add_one_of_not_mem_cl (h : e ∉ M.cl X) :
  M.r (insert e X) = M.r X + 1 :=
r_insert_eq_add_one_of_r_ne (h ∘ mem_cl.mpr)

lemma not_mem_cl_of_r_insert_gt (h : M.r X < M.r (insert e X)) :
  e ∉ M.cl X :=
h.ne.symm ∘ mem_cl.mp

lemma mem_cl_of_r_insert_le (h : M.r (insert e X) ≤ M.r X) :
  e ∈ M.cl X :=
mem_cl.mpr (h.antisymm (M.r_le_r_insert X e))

lemma not_mem_cl_iff_r_insert_eq_add_one  :
  e ∉ M.cl X ↔ M.r (insert e X) = M.r X + 1 :=
⟨r_insert_eq_add_one_of_not_mem_cl, λ h, not_mem_cl_of_r_insert_gt (by {rw h, apply lt_add_one})⟩

lemma cl_insert_eq_of_mem_cl (he : e ∈ M.cl X) :
  M.cl (insert e X) = M.cl X :=
begin
  refine (M.cl_mono (subset_insert _ _)).antisymm' _,
  rw [←M.cl_cl X],
  exact M.cl_subset_cl_of_subset (insert_subset.mpr ⟨he, M.subset_cl _⟩),
end

lemma mem_cl_insert (he : e ∉ M.cl X) (hef : e ∈ M.cl (insert f X)) :
  f ∈ M.cl (insert e X) :=
begin
  by_contra hf,
  rw not_mem_cl_iff_r_insert_eq_add_one at he hf,
  rw [mem_cl, insert_comm, hf, he] at hef,
  have h := M.r_insert_le_add_one X f,
  rw ←hef at h,
  exact (lt_add_one _).not_le h,
end

@[simp] lemma cl_union_cl_right_eq_cl_union (M : matroid E) (X Y : set E) :
  M.cl (X ∪ M.cl Y) = M.cl (X ∪ Y) :=
begin
  refine ((M.cl_mono (union_subset_union_right X (M.subset_cl _)))).antisymm' _,
  rw [←M.cl_cl (X ∪ Y)],
  exact M.cl_mono (union_subset ((subset_union_left _ _).trans (M.subset_cl _))
    (M.cl_mono (subset_union_right _ _))),
end

@[simp] lemma cl_union_cl_left_eq_cl_union (M : matroid E) (X Y : set E) :
  M.cl (M.cl X ∪ Y) = M.cl (X ∪ Y) :=
by rw [union_comm, cl_union_cl_right_eq_cl_union, union_comm]

@[simp] lemma cl_cl_union_cl_eq_cl_union (M : matroid E) (X Y : set E) :
  M.cl (M.cl X ∪ M.cl Y) = M.cl (X ∪ Y) :=
by rw [cl_union_cl_left_eq_cl_union, cl_union_cl_right_eq_cl_union]

@[simp] lemma cl_insert_cl_eq_cl_insert (M : matroid E) (e : E) (X : set E) :
  M.cl (insert e (M.cl X)) = M.cl (insert e X) :=
by simp_rw [←singleton_union, cl_union_cl_right_eq_cl_union]

lemma cl_exchange (he : e ∈ M.cl (insert f X) \ M.cl X ) :
  f ∈ M.cl (insert e X) \ M.cl X :=
begin
  refine ⟨mem_cl_insert he.2 he.1, λ hf, _ ⟩,
  rw [cl_insert_eq_of_mem_cl hf, diff_self] at he,
  exact not_mem_empty _ he,
end

lemma cl_exchange_iff :
  e ∈ M.cl (insert f X) \ M.cl X ↔ f ∈ M.cl (insert e X) \ M.cl X :=
⟨cl_exchange, cl_exchange⟩  

lemma cl_diff_singleton_eq_cl (h : e ∈ M.cl (X \ {e})) :
  M.cl (X \ {e}) = M.cl X :=
begin
  refine (M.cl_mono (diff_subset _ _)).antisymm _,
  have h' := M.cl_mono (insert_subset.mpr ⟨h, (M.subset_cl _ )⟩),
  rw [insert_diff_singleton, cl_cl] at h',
  exact (M.cl_mono (subset_insert _ _)).trans h',
end

lemma mem_cl_diff_singleton_iff_cl (he : e ∈ X) :
  e ∈ M.cl (X \ {e}) ↔ M.cl (X \ {e}) = M.cl X :=
⟨cl_diff_singleton_eq_cl, λ h, by {rw h, exact subset_cl _ _ he}⟩

lemma circuit.subset_cl_diff_singleton (hC : M.circuit C) (e : E) :
  C ⊆ M.cl (C \ {e}) :=
begin
  nth_rewrite 0 [←inter_union_diff C {e}],
  refine union_subset  _ (M.subset_cl _),
  obtain he | he := em (e ∈ C),
  { refine (inter_subset_right _ _).trans (singleton_subset_iff.mpr _),
    rw [mem_cl, insert_diff_singleton, insert_eq_of_mem he, hC.r,
      (hC.diff_singleton_indep he).r, ncard_diff_singleton_of_mem he]},
  convert empty_subset _,
  rwa inter_singleton_eq_empty,
end

lemma indep_iff_cl_diff_ne_forall :
  M.indep I ↔ ∀ x ∈ I, M.cl (I \ {x}) ≠ M.cl I :=
begin
  refine ⟨λ h x hxI h_eq, _, λ h, _⟩,
  { have h' : x ∈ M.cl (I \ {x}),
    { rw [h_eq], exact M.subset_cl _ hxI},
    rw [mem_cl, insert_diff_singleton, insert_eq_of_mem hxI, h.r, (h.diff _).r,
      ←ncard_diff_singleton_add_one hxI] at h',
    simpa using h'},
  rw [indep_iff_forall_subset_not_circuit],
  by_contra' hC,
  obtain ⟨C, hCI, hC⟩ := hC,
  obtain ⟨x,hxC⟩ := hC.nonempty,
  exact h x (hCI hxC) (cl_diff_singleton_eq_cl
    (M.cl_mono (diff_subset_diff_left hCI) (hC.subset_cl_diff_singleton _ hxC))),
end

 lemma indep_iff_not_mem_cl_diff_forall :
  M.indep I ↔ ∀ x ∈ I, x ∉ M.cl (I \ {x}) :=
begin
  rw indep_iff_cl_diff_ne_forall,
  exact ⟨λ h, λ x hxI, by {rw mem_cl_diff_singleton_iff_cl hxI, exact h x hxI},
    λ h x hxI, by {rw [ne.def, ←mem_cl_diff_singleton_iff_cl hxI], exact h x hxI}⟩,
end

lemma indep_iff_cl_ssubset_ssubset_forall :
  M.indep I ↔ ∀ J ⊂ I, M.cl J ⊂ M.cl I :=
begin
  refine ⟨λ hI J hJI, _,
    λ h, indep_iff_cl_diff_ne_forall.mpr (λ x hx, (h _ $ diff_singleton_ssubset.2 hx).ne)⟩,
  obtain ⟨e,heI,heJ⟩ := exists_of_ssubset hJI,
  exact (M.cl_subset_cl_of_subset (subset_diff_singleton hJI.subset heJ)).trans_ssubset
    ((M.cl_subset_cl_of_subset (diff_subset I {e})).ssubset_of_ne
    (indep_iff_cl_diff_ne_forall.mp hI e heI)),
end

lemma indep.not_mem_cl_iff (hI : M.indep I) :
  x ∉ M.cl I ↔ x ∉ I ∧ M.indep (insert x I) :=
begin
  rw [←not_iff_not, not_not_mem, not_and, mem_cl],
  refine ⟨λ h hxI hI', indep_iff_cl_diff_ne_forall.mp hI' x (mem_insert _ _) _,
    λ h, (M.r_mono (subset_insert _ _)).antisymm' _⟩,
  { rw [hI.r, hI'.r, ncard_insert_of_not_mem hxI] at h, simpa using h},
  obtain (hxI | hxI) := em (x ∈ I),
  { rw [insert_eq_of_mem hxI]},
  have hIi := h hxI,
  rwa [←r_lt_card_iff_dep, ←nat.add_one_le_iff, ncard_insert_of_not_mem hxI, add_le_add_iff_right,
    ←hI.r] at hIi,
end

lemma indep.mem_cl_iff (hI : M.indep I) :
  x ∈ M.cl I ↔ x ∈ I ∨ ¬ M.indep (insert x I) :=
by rw [←not_iff_not, hI.not_mem_cl_iff, not_or_distrib, not_not] 

lemma mem_cl_self (M : matroid E) (e : E) : e ∈ M.cl {e} := (M.subset_cl {e}) (mem_singleton e)

lemma indep.cl_diff_singleton_ssubset (hI : M.indep I) (he : e ∈ I) : M.cl (I \ {e}) ⊂  M.cl I :=
ssubset_of_subset_of_ne (M.cl_mono (diff_subset _ _)) (indep_iff_cl_diff_ne_forall.mp hI _ he)

lemma indep.cl_ssubset_ssubset (hI : M.indep I) (hJI : J ⊂ I) : M.cl J ⊂ M.cl I :=
indep_iff_cl_ssubset_ssubset_forall.mp hI J hJI

lemma subset_cl_iff_r_union_eq_r : X ⊆ M.cl Y ↔ M.r (Y ∪ X) = M.r Y := 
begin
  refine ⟨λ h, r_union_eq_of_r_all_insert_le (λ e he, by rw mem_cl.mp (h he)),
    λ hu e heX, mem_cl.mpr ((M.r_mono (subset_insert _ _)).antisymm' _)⟩,
  rw ←hu,
  apply r_mono,
  rw insert_subset,
  simp only [mem_union, subset_union_left, and_true],
  exact or.inr heX,
end

lemma basis.subset_cl (hI : M.basis I X) :
  X ⊆ M.cl I :=
begin
  rw subset_cl_iff_r_union_eq_r,
  refine le_antisymm _ (M.r_le_r_union_left _ _),
  rw [hI.r, union_eq_right_iff_subset.mpr hI.subset],
end

lemma cl_flat (M : matroid E) (X : set E) :
  M.flat (M.cl X) :=
λ I Y hIcl hIY, hIY.subset_cl.trans (cl_subset_cl_of_subset_cl hIcl.subset)

lemma flat_iff_cl_self :
  M.flat F ↔ M.cl F = F :=
begin
  refine ⟨λ hF, (sInter_subset_of_mem _).antisymm (subset_sInter _), λ hF, _⟩,
  { exact ⟨hF, rfl.subset⟩,   },
  { rintro F' ⟨hF', hFF'⟩, exact hFF'},
  rw ←hF,
  apply cl_flat,
end

lemma flat.cl (hF : M.flat F) :
  M.cl F = F :=
flat_iff_cl_self.mp hF

lemma flat_iff_ssubset_cl_insert_forall :
  M.flat F ↔ ∀ e ∉ F, M.cl F ⊂ M.cl (insert e F) :=
begin
  refine ⟨λ h e he, (M.cl_subset_cl_of_subset (subset_insert _ _)).ssubset_of_ne _, λ h, _⟩,
  { rw [h.cl], exact λ h', mt ((set.ext_iff.mp h') e).mpr he ((M.subset_cl _) (mem_insert _ _))},
  rw flat_iff_cl_self,
  by_contra h',
  obtain ⟨e,he',heF⟩ := exists_of_ssubset (ssubset_of_ne_of_subset (ne.symm h') (M.subset_cl F)),
  have h'' := (h e heF),
  rw [←cl_insert_cl_eq_cl_insert, insert_eq_of_mem he', cl_cl] at h'',
  exact h''.ne rfl,
end

lemma flat.cl_exchange (hF : M.flat F) (he : e ∈ M.cl (insert f F) \ F) :
  f ∈ M.cl (insert e F) \ F :=
by {nth_rewrite 1 ←hF.cl, apply cl_exchange, rwa hF.cl}

lemma flat.cl_subset_of_subset (hF : M.flat F) (h : X ⊆ F) :
  M.cl X ⊆ F :=
by {have h' := M.cl_mono h, rwa hF.cl at h'}

lemma base.cl (hB : M.base B) :
  M.cl B = univ :=
eq_univ_of_forall (λ x, by_contra (λ hx,
    (hB.dep_of_insert (not_mem_subset (M.subset_cl B) hx) (hB.indep.not_mem_cl_iff.mp hx).2)))

lemma indep.basis_cl (hI : M.indep I) :
  M.basis I (M.cl I) :=
begin
  refine ⟨hI, M.subset_cl _, λ J hJ hIJ hJI, hIJ.antisymm (λ e he, by_contra (λ heI, _))⟩,
  apply indep_iff_cl_diff_ne_forall.mp (hJ.subset (insert_subset.mpr ⟨he, hIJ⟩)) e (mem_insert _ _),
  rw [insert_diff_of_mem _ (mem_singleton e), diff_singleton_eq_self heI],
  refine (M.cl_mono (subset_insert _ _)).antisymm (subset_trans _ (cl_subset_cl_of_subset_cl hJI)),
  exact M.cl_subset_cl_of_subset (insert_subset.mpr ⟨he, hIJ⟩),
end

lemma basis.cl (hI : M.basis I X) :
  M.cl I = M.cl X :=
(M.cl_mono hI.subset).antisymm ((M.cl_flat I).cl_subset_of_subset hI.subset_cl)

lemma basis.basis_cl (hI : M.basis I X) :
  M.basis I (M.cl X) :=
by {rw [←hI.cl], exact hI.indep.basis_cl}

lemma basis_iff_basis_cl_of_subset (hIX : I ⊆ X) :
  M.basis I X ↔ M.basis I (M.cl X) :=
⟨λ h, h.basis_cl,λ h, h.basis_subset hIX (subset_cl _ _)⟩

lemma basis.basis_of_cl_eq_cl (hI : M.basis I X) (hIY : I ⊆ Y) (h : M.cl X = M.cl Y) :
  M.basis I Y :=
begin
  rw [basis_iff_basis_cl_of_subset hIY, ←h],
  exact hI.basis_cl,
end

lemma base_subset_iff_cl_eq_univ :
  (∃ B ⊆ X, M.base B) ↔ M.cl X = univ :=
begin
  split,
  { rintro ⟨B, hBX, hB⟩,
    have h' := M.cl_subset_cl_of_subset hBX,
    rw [hB.cl] at h',
    exact h'.antisymm' (subset_univ _)},
  intro h,
  obtain ⟨I, hIX⟩ := M.exists_basis X,
  have h' := hIX.basis_cl,
  rw [h, ←base_iff_basis_univ] at h',
  exact ⟨I, hIX.subset, h'⟩,
end

lemma basis.insert_basis_insert_of_not_mem_cl (hI : M.basis I X) (he : e ∉ M.cl X) :
  M.basis (insert e I) (insert e X) :=
begin
  rw [←hI.cl, hI.indep.not_mem_cl_iff] at he,
  refine ⟨he.2, insert_subset_insert hI.subset, λ J hJ heIJ hJeX, heIJ.antisymm _⟩,
  rw [←union_singleton, ←inter_union_diff J X, union_subset_iff, (@diff_subset_iff _ J _ _),
    ←union_assoc, union_eq_left_iff_subset.mpr hI.subset, union_singleton, union_singleton,
    ←hI.eq_of_subset_indep (hJ.inter_right X)
      (subset_inter ((subset_insert _ _).trans heIJ) hI.subset) (inter_subset_right _ _)],
  exact ⟨subset_insert _ _, hJeX⟩,
end

lemma not_mem_cl_iff_forall_insert_basis_insert :
  e ∉ M.cl X ↔ (e ∉ X ∧ (∀ I, M.basis I X → M.basis (insert e I) (insert e X))) :=
begin
  refine ⟨λ he, ⟨λ heX, he (M.subset_cl X heX), λ I hI, hI.insert_basis_insert_of_not_mem_cl he⟩,
    λ h he, _⟩,
  obtain ⟨I, hI⟩ := M.exists_basis X,
  exact (h.2 I hI).not_basis_of_ssubset (ssubset_insert (λ heI, h.1 (hI.subset heI)))
    (hI.basis_cl.basis_subset (hI.subset.trans (subset_insert _ _))
      (insert_subset.mpr ⟨he,M.subset_cl _⟩)),
end

lemma basis_iff_cl :
  M.basis I X ↔ I ⊆ X ∧ X ⊆ M.cl I ∧ ∀ J ⊆ I, X ⊆ M.cl J → J = I :=
begin
  revert I,
  by_contra' hcon,
  obtain ⟨I, hI, hImin⟩ := finite.exists_minimal _ hcon,
  apply hI,
  refine ⟨λ hI, ⟨hI.subset, hI.subset_cl, _ ⟩, _⟩,
  { by_contra' h',
    obtain ⟨J, ⟨hJI, hXJ, hJne⟩, hJmin⟩ := finite.exists_minimal _ h',
    refine hJne (hImin J (λ hJgood,_) hJI).symm,
    have hJ : M.basis J X,
    { rw hJgood,
      refine ⟨hJI.trans hI.subset, hXJ, λ J' hJ' hXJ', _⟩,
      rw hJmin J' ⟨hJ'.trans hJI,hXJ',_⟩ hJ',
      rintro rfl,
      exact hJne (hJI.antisymm hJ')},
    exact hJne (hJ.eq_of_subset_indep hI.indep hJI hI.subset)},
  rintros ⟨hIX, hXI, hI⟩,
  refine ⟨_,hIX,λ J hJ hIJ hJX, by_contra (λ hne, _)⟩,
  { rw indep_iff_cl_ssubset_ssubset_forall,
    intros J hJI,
    refine (M.cl_subset_cl_of_subset (hJI.subset)).ssubset_of_ne (λ he, hJI.ne _),
    exact hI J hJI.subset (hXI.trans_eq he.symm)},
  rw indep_iff_cl_ssubset_ssubset_forall at hJ,
  refine ((hJ I (hIJ.ssubset_of_ne hne)).trans_subset (M.cl_mono hJX)).not_subset _,
  exact cl_subset_cl_of_subset_cl hXI,
end

lemma basis_union_iff_indep_cl :
  M.basis I (I ∪ X) ↔ M.indep I ∧ X ⊆ M.cl I :=
begin
  refine ⟨λ h, ⟨h.indep, (subset_union_right _ _).trans h.subset_cl⟩, _⟩,
  rw basis_iff_cl,
  rintros ⟨hI, hXI⟩,
  refine ⟨subset_union_left _ _, union_subset (M.subset_cl _) hXI, λ J hJI hJ, by_contra (λ h', _)⟩,
  obtain ⟨e,heI,heJ⟩ := exists_of_ssubset (hJI.ssubset_of_ne h'),
  have heJ' : e ∈ M.cl J,
    from hJ (or.inl heI),
  refine indep_iff_not_mem_cl_diff_forall.mp hI e heI (mem_of_mem_of_subset heJ' _),
  exact M.cl_subset_cl_of_subset (subset_diff_singleton hJI heJ),
end

lemma basis_iff_indep_cl :
  M.basis I X ↔ M.indep I ∧ X ⊆ M.cl I ∧ I ⊆ X :=
⟨λ h, ⟨h.indep, h.subset_cl, h.subset⟩,
  λ h, (basis_union_iff_indep_cl.mpr ⟨h.1,h.2.1⟩).basis_subset h.2.2 (subset_union_right _ _)⟩

lemma basis.eq_of_cl_subset (hI : M.basis I X) (hJI : J ⊆ I) (hJ : X ⊆ M.cl J) :
  J = I :=
(basis_iff_cl.mp hI).2.2 J hJI hJ

lemma empty_basis_iff :
  M.basis ∅ X ↔ X ⊆ M.cl ∅ :=
begin
  simp only [basis_iff_cl, empty_subset, true_and, and_iff_left_iff_imp],
  exact λ h J hJ hXJ, subset_empty_iff.mp hJ,
end

lemma mem_cl_iff_exists_circuit :
  e ∈ M.cl X ↔ e ∈ X ∨ ∃ C, M.circuit C ∧ e ∈ C ∧ C \ {e} ⊆ X :=
begin
  refine ⟨λ h, _,_⟩,
  { by_contra' h',
    obtain ⟨I, hI⟩ := M.exists_basis X,
    have hIe : ¬ M.indep (insert e I),
    { intro hI',
      refine indep_iff_not_mem_cl_diff_forall.mp hI' e (mem_insert _ _) _,
      rwa [insert_diff_of_mem _ (mem_singleton _),
        diff_singleton_eq_self (not_mem_subset hI.subset h'.1), hI.cl]},
    obtain ⟨C,⟨hCeI, hC, heC⟩,-⟩ :=  hI.indep.unique_circuit_of_insert _ hIe,
    refine h'.2 C hC heC (diff_subset_iff.mpr (hCeI.trans _)),
    rw singleton_union,
    apply insert_subset_insert hI.subset},
  rintro (heX | ⟨C,hC, heC, hCX⟩),
  { exact (M.subset_cl X) heX},
  exact (M.cl_mono hCX) (hC.subset_cl_diff_singleton e heC),
end

lemma flat_iff_forall_circuit :
  M.flat F ↔ ∀ C e, M.circuit C → e ∈ C → C \ {e} ⊆ F → e ∈ F :=
begin
  rw [flat_iff_cl_self],
  refine ⟨λ h C e hC heC hCF , _, λ h, (M.subset_cl _).antisymm' (λ e heF, _) ⟩,
  { rw ←h, exact (hC.subset_cl_diff_singleton e).trans (M.cl_mono hCF) heC},
  exact (mem_cl_iff_exists_circuit.mp heF).elim id (λ ⟨C, hC, heC, hCF⟩, h _ _ hC heC hCF),
end

/- ### Basis exchange -/
/- These lemmas doesn't actually use closure in their statements, but we prove them using closure.
  TODO : Avoid cardinality in the proofs. -/

/- Given two bases `I₁,I₂` of `X` and an element `e` of `I₁ \ I₂`, we can find an `f ∈ I₂ \ I₁`
  so that swapping `e` for `f` in yields bases in both `I₁` and `I₂`.  -/
theorem basis.strong_exchange (hI₁ : M.basis I₁ X) (hI₂ : M.basis I₂ X) (he : e ∈ I₁ \ I₂) :
  ∃ f ∈ I₂ \ I₁, M.basis (insert e (I₂ \ {f})) X ∧ M.basis (insert f (I₁ \ {e})) X :=
begin
  by_contra,
  simp_rw [not_exists, not_and] at h,

  have heX : e ∈ X := hI₁.subset he.1,
  obtain ⟨C, ⟨hCB₂,hC⟩, hCunique⟩ :=
    hI₂.indep.unique_circuit_of_insert e (hI₂.insert_dep ⟨heX, he.2⟩),

  have hCss := diff_singleton_subset_iff.mpr hCB₂,

  simp only [exists_unique_iff_exists, exists_prop, and_imp] at hCunique,
  have hC_exchange : ∀ f ∈ C \ {e}, M.basis (insert e (I₂ \ {f})) X,
  { rintros y ⟨hyC, hyx⟩,

    rw [basis_iff_indep_card, ncard_exchange he.2 (hCss ⟨hyC,hyx⟩), hI₂.card, eq_self_iff_true,
      and_true],
    refine ⟨by_contra (λ hdep, _), insert_subset.mpr ⟨heX, ((diff_subset _ _).trans hI₂.subset)⟩⟩,

    rw [dep_iff_supset_circuit] at hdep,
    obtain ⟨C', hC'ss, hC'⟩ := hdep,
    have  hC'e : e ∈ C',
    { by_contra he',
      exact hC'.dep (hI₂.indep.subset (((subset_insert_iff_of_not_mem he').mp hC'ss).trans
          (diff_subset _ _)))},
    have := hCunique C' (hC'ss.trans (insert_subset_insert (diff_subset _ _))) hC' hC'e,
    subst this,
    simpa using hC'ss hyC},

  have hcl : ∀ f ∈ I₂ \ M.cl (I₁ \ {e}), M.basis (insert f (I₁ \ {e})) X,
  { rintro f ⟨hf₂, hf₁⟩,
    obtain rfl | hfe := em (f = e),
    { rwa [insert_diff_singleton, insert_eq_self.mpr he.1]},
    have hfI₁ : f ∉ I₁, from
      λ hfI₁, hf₁ (M.subset_cl (I₁ \ {e}) (mem_diff_singleton.mpr ⟨hfI₁, hfe⟩)),
    simp_rw [basis_iff_indep_card, indep_iff_r_eq_card, ncard_exchange hfI₁ he.1,
      hI₁.card, eq_self_iff_true, and_true, ←hI₁.card, not_mem_cl.mp hf₁, insert_subset,
      (hI₁.indep.diff {e}).r, ncard_diff_singleton_add_one he.1, eq_self_iff_true, true_and],
    exact ⟨hI₂.subset hf₂, (diff_subset _ _).trans hI₁.subset⟩},

  have hss : C \ {e} ⊆ M.cl (I₁ \ {e}),
  from λ f hf, by_contra (λ hf', h _ ⟨hCss hf, λ hf₁, hf' (M.subset_cl _ ⟨hf₁,hf.2⟩)⟩
      (hC_exchange f hf) (hcl _ ⟨hCss hf,hf'⟩)),

  have he' := (hC.1.subset_cl_diff_singleton _).trans (cl_subset_cl_of_subset_cl hss) hC.2,
  rw [mem_cl, insert_diff_singleton, insert_eq_of_mem he.1, hI₁.indep.r, (hI₁.indep.diff _).r,
    ←ncard_diff_singleton_add_one he.1] at he',
  simpa only [nat.succ_ne_self] using he',
end

/- This lemma is tantamount to saying that matroid restriction is well-defined. -/
lemma basis.exchange (hI₁ : M.basis I₁ X) (hI₂ : M.basis I₂ X) (he : e ∈ I₁ \ I₂) :
  ∃ f ∈ I₂ \ I₁, M.basis (insert f (I₁ \ {e})) X :=
(hI₁.strong_exchange hI₂ he).imp (λ h, Exists.imp (λ h', and.right))

lemma basis.rev_exchange (hI₁ : M.basis I₁ X) (hI₂ : M.basis I₂ X) (he : e ∈ I₁ \ I₂) :
  ∃ f ∈ I₂ \ I₁, M.basis (insert e (I₂ \ {f})) X :=
(hI₁.strong_exchange hI₂ he).imp (λ h, Exists.imp (λ h', and.left))

theorem base.strong_exchange (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hx : x ∈ B₁ \ B₂) :
  ∃ y ∈ B₂ \ B₁, M.base (insert x (B₂ \ {y})) ∧ M.base (insert y (B₁ \ {x})) :=
by {simp_rw base_iff_basis_univ at *, exact hB₁.strong_exchange hB₂ hx}

lemma base.rev_exchange (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hx : x ∈ B₁ \ B₂) :
  ∃ y ∈ B₂ \ B₁, M.base (insert x (B₂ \ {y})) :=
(hB₁.strong_exchange hB₂ hx).imp (by {rintro y ⟨hy,h,-⟩, use [hy,h]})

/- ### Flats and rank -/

lemma flat.r_strict_mono (hF₁ : M.flat F₁) (hF₂ : M.flat F₂) (h : F₁ ⊂ F₂) :
  M.r F₁ < M.r F₂ :=
begin
  refine lt_of_le_of_ne (M.r_mono h.subset) (λ he, _),
  obtain ⟨x,hx, hxF₁⟩ := exists_of_ssubset h,
  have hle := M.r_mono (insert_subset.mpr ⟨hx, h.subset⟩),
  rw [hF₁.r_insert_of_not_mem hxF₁, ←he] at hle,
  simpa only [add_le_iff_nonpos_right, le_zero_iff] using hle,
end

lemma flat.eq_of_le_r_subset (hF₁ : M.flat F₁) (hF₂ : M.flat F₂) (h : F₁ ⊆ F₂)
(hr : M.r F₂ ≤ M.r F₁):
  F₁ = F₂ :=
by_contra (λ h', (hF₁.r_strict_mono hF₂ (ssubset_of_ne_of_subset h' h)).not_le hr)

lemma flat.eq_univ_of_rk_le_r (hF : M.flat F) (hr : M.rk ≤ M.r F) :
  F = univ :=
hF.eq_of_le_r_subset (M.univ_flat) (subset_univ _) hr

lemma r_le_iff_cl {n : ℕ} :
  M.r X ≤ n ↔ ∃ I, X ⊆ M.cl I ∧ I.ncard ≤ n :=
begin
  refine ⟨λ h, _, _⟩,
  { obtain ⟨I,hI⟩ := M.exists_basis X,
    exact ⟨I, hI.subset_cl, by rwa hI.card⟩},
  rintro ⟨I, hXI, hIn⟩,
  refine (M.r_mono hXI).trans (le_trans _ hIn),
  rw [r_cl],
  exact M.r_le_card I,
end

lemma le_r_iff_cl {n : ℕ} :
 n ≤ M.r X ↔ ∀ I, X ⊆ M.cl I → n ≤ I.ncard :=
begin
  cases n, simp,
  rw [←not_lt, ←not_iff_not, not_not, not_forall],
  simp_rw [not_imp, not_le, nat.lt_succ_iff],
  exact r_le_iff_cl,
end

lemma eq_of_cl_eq_cl_forall {M₁ M₂ : matroid E} (h : ∀ X, M₁.cl X = M₂.cl X) :
  M₁ = M₂ :=
eq_of_indep_iff_indep_forall (λ I, by simp_rw [indep_iff_cl_diff_ne_forall, h])

/- ### Covering  -/

/-- A set is covered by another in a matroid if they are strictly nested flats, with no flat
  between them . -/
def covby (M : matroid E) (F₀ F₁ : set E) : Prop :=
  M.flat F₀ ∧ M.flat F₁ ∧ F₀ ⊂ F₁ ∧ ∀ F, M.flat F → F₀ ⊆ F → F ⊆ F₁ → F = F₀ ∨ F = F₁

lemma covby_iff :
  M.covby F₀ F₁ ↔ M.flat F₀ ∧ M.flat F₁ ∧ F₀ ⊂ F₁ ∧
    ∀ F, M.flat F → F₀ ⊆ F → F ⊆ F₁ → F = F₀ ∨ F = F₁ :=
iff.rfl

lemma covby.flat_left (h : M.covby F₀ F₁) :
  M.flat F₀ :=
h.1

lemma covby.flat_right (h : M.covby F₀ F₁) :
  M.flat F₁ :=
h.2.1

lemma covby.ssubset (h : M.covby F₀ F₁) :
  F₀ ⊂ F₁ :=
h.2.2.1

lemma covby.subset (h : M.covby F₀ F₁) :
  F₀ ⊆ F₁ :=
h.2.2.1.subset

lemma covby.eq_or_eq (h : M.covby F₀ F₁) (hF : M.flat F) (h₀ : F₀ ⊆ F) (h₁ : F ⊆ F₁) :
  F = F₀ ∨ F = F₁ :=
h.2.2.2 F hF h₀ h₁

lemma covby.eq_of_subset_of_ssubset (h : M.covby F₀ F₁) (hF : M.flat F) (hF₀ : F₀ ⊆ F)
(hF₁ : F ⊂ F₁) :
  F = F₀ :=
(h.2.2.2 F hF hF₀ hF₁.subset).elim id (λ h', (hF₁.ne h').elim)

lemma covby.eq_of_ssubset_of_subset (h : M.covby F₀ F₁) (hF : M.flat F) (hF₀ : F₀ ⊂ F)
(hF₁ : F ⊆ F₁) :
  F = F₁ :=
(h.2.2.2 F hF hF₀.subset hF₁).elim (λ h', (hF₀.ne.symm h').elim) id

lemma covby.cl_insert_eq (h : M.covby F₀ F₁) (he : e ∈ F₁ \ F₀) :
  M.cl (insert e F₀) = F₁ :=
h.eq_of_ssubset_of_subset (M.cl_flat _)
  ((ssubset_insert he.2).trans_subset (M.subset_cl _))
  (h.flat_right.cl_subset_of_subset (insert_subset.mpr ⟨he.1, h.ssubset.subset⟩))

lemma flat.exists_unique_flat_of_not_mem (hF₀ : M.flat F₀) (he : e ∉ F₀) :
  ∃! F₁, e ∈ F₁ ∧ M.covby F₀ F₁ :=
begin
  refine ⟨M.cl (insert e F₀), ⟨(M.subset_cl _) (mem_insert _ _),_⟩, _⟩,
  { refine ⟨hF₀,M.cl_flat _, (ssubset_insert he).trans_subset (M.subset_cl _), λ F hF hF₀F hFeF₀,_⟩,
    by_contra' h,
    refine h.2 (hFeF₀.antisymm (hF.cl_subset_of_subset (insert_subset.mpr ⟨_,hF₀F⟩))),
    obtain ⟨x,hxF,hxF₀⟩ := exists_of_ssubset (hF₀F.ssubset_of_ne (ne.symm h.1)),
    exact mem_of_mem_of_subset (hF₀.cl_exchange ⟨hFeF₀ hxF, hxF₀⟩).1
      (hF.cl_subset_of_subset (insert_subset.mpr ⟨hxF, hF₀F⟩))},
  rintro F ⟨heF, ⟨-,hF,hF₀F,hmin⟩⟩,
  obtain (h' | rfl) := hmin (M.cl (insert e F₀)) (M.cl_flat _)
    ((subset_insert _ _).trans (M.subset_cl _))
    (hF.cl_subset_of_subset (insert_subset.mpr ⟨heF,hF₀F.subset⟩)),
  { exact (((ssubset_insert he).trans_subset (M.subset_cl _)).ne.symm h').elim},
  refl,
end

/- ### Hyperplanes -/

lemma hyperplane_def : M.hyperplane H ↔ (M.flat H ∧ H ⊂ univ ∧ ∀ F, H ⊂ F → M.flat F → F = univ) :=
iff.rfl

lemma cocircuit.compl_hyperplane {K : set E} (hK : M.cocircuit K) : M.hyperplane Kᶜ := hK  

lemma hyperplane.flat (hH : M.hyperplane H) : M.flat H := hH.1

lemma hyperplane.ssubset_univ (hH : M.hyperplane H) : H ⊂ univ := hH.2.1

lemma univ_not_hyperplane (M : matroid E) : ¬ M.hyperplane univ := λ h, h.2.1.ne rfl

lemma hyperplane.eq_of_subset (h₁ : M.hyperplane H₁) (h₂ : M.hyperplane H₂) (h : H₁ ⊆ H₂) :
  H₁ = H₂ :=
by_contra (λ he, h₂.ssubset_univ.ne (h₁.2.2 H₂ (h.ssubset_of_ne he) h₂.flat))

lemma hyperplane.not_ssubset (h₁ : M.hyperplane H₁) (h₂ : M.hyperplane H₂) :
  ¬ H₁ ⊂ H₂ :=
λ hss, hss.ne (h₁.eq_of_subset h₂ hss.subset)

lemma hyperplane.exists_not_mem (hH : M.hyperplane H) :
  ∃ e, e ∉ H :=
by {by_contra' h, apply M.univ_not_hyperplane, convert hH, rwa [eq_comm, eq_univ_iff_forall] }

lemma hyperplane_iff_maximal_cl_ne_univ :
  M.hyperplane H ↔ M.cl H ≠ univ ∧ ∀ X, H ⊂ X → M.cl X = univ :=
begin
  rw [hyperplane_def, cl_def],
  simp only [ne.def, sInter_eq_univ, mem_set_of_eq, and_imp, not_forall, exists_prop],
  refine ⟨λ h, ⟨⟨H, h.1, rfl.subset, h.2.1.ne⟩, λ X hHX, h.2.2 _
    (hHX.trans_subset (M.subset_cl _)) (M.cl_flat _)⟩, λ h, _⟩,
  obtain ⟨⟨F,hF,hHF,hFne⟩,hmax⟩ := h,
  suffices h_eq : H = F,
  { subst h_eq,
    refine ⟨hF, ssubset_univ_iff.mpr hFne, λ F hHF hF, _⟩,
    rw ←hF.cl,
    exact hmax _ hHF, },
  refine by_contra (λ hne, hFne _),
  rw [←hmax F (ssubset_of_ne_of_subset hne hHF), hF.cl],
end

lemma hyperplane_iff_maximal_not_supset_base :
  M.hyperplane H ↔ (¬∃ B ⊆ H, M.base B) ∧ ∀ X, H ⊂ X → ∃ B ⊆ X, M.base B :=
by simp_rw [hyperplane_iff_maximal_cl_ne_univ, ne.def, ←base_subset_iff_cl_eq_univ]

lemma hyperplane_iff_maximal_r :
  M.hyperplane H ↔ M.r H < M.rk ∧ ∀ X, H ⊂ X → M.r X = M.rk :=
begin
  rw hyperplane_def,
  refine ⟨_,λ hH, ⟨flat_iff_r_lt_r_insert.mpr (λ e heH, _),
    ssubset_of_ne_of_subset (λ hH', _) (subset_univ _), λ F hHF hF, _⟩⟩,
  { rintro ⟨hH, hHss, hHmax⟩,
    have hlt := hH.r_strict_mono (M.univ_flat) hHss,
    refine ⟨hlt,λ X hHX, _⟩,
    convert congr_arg M.r (hHmax _ (hHX.trans_subset (M.subset_cl X)) (M.cl_flat _)) using 1,
    rw [r_cl]},
  { rw hH.2 (insert e H) (ssubset_insert heH), exact hH.1 },
  { subst hH', exact hH.1.ne rfl},
  apply hF.eq_of_le_r_subset (M.univ_flat) (subset_univ _),
  rw hH.2 _ hHF,
end

lemma hyperplane.r_add_one (hH : M.hyperplane H) :
  M.r H + 1 = M.rk :=
begin
  rw [hyperplane_iff_maximal_r] at hH,
  cases hH with h₁ h₂,
  refine (nat.add_one_le_iff.mpr h₁).antisymm _,
  by_cases ∃ x, x ∉ H,
  { obtain ⟨x,hxH⟩ := h,
    rw [←h₂ _ (ssubset_insert hxH)],
    exact (M.r_insert_le_add_one H x)},
  simp_rw [not_exists, not_not_mem, ←eq_univ_iff_forall] at h,
  rw h,
  apply nat.le_succ,
end

lemma hyperplane.coe_r (hH : M.hyperplane H) :
  (M.r H : ℤ) = M.rk - 1 :=
by simp [←hH.r_add_one]

lemma hyperplane_iff_flat_r_eq :
  M.hyperplane H ↔ M.flat H ∧ M.r H + 1 = M.rk :=
begin
  refine ⟨λ h, ⟨h.1,h.r_add_one⟩,λ h,
    ⟨h.1,ssubset_univ_iff.mpr (λ hH, by {subst hH, simpa using h.2}), λ F hHF hF,
      hF.eq_univ_of_rk_le_r _⟩⟩,
  rw [←h.2, nat.add_one_le_iff],
  exact h.1.r_strict_mono hF hHF,
end

lemma base.hyperplane_of_cl_diff_singleton (hB : M.base B) (heB : e ∈ B) :
  M.hyperplane (M.cl (B \ {e})) :=
begin
  rw [hyperplane_iff_maximal_cl_ne_univ, cl_cl, ne_univ_iff_exists_not_mem],
  refine ⟨⟨e, λ he, indep_iff_cl_diff_ne_forall.mp hB.indep _ heB (cl_diff_singleton_eq_cl he)⟩,
    λ X hX, univ_subset_iff.mp _⟩,
  obtain ⟨f,hfX, hfB⟩ := exists_of_ssubset hX,
  obtain (rfl | hef) := eq_or_ne f e,
  { have hu := union_subset (singleton_subset_iff.mpr hfX) ((subset_cl _ _).trans hX.subset),
    rw [singleton_union, insert_diff_singleton, insert_eq_of_mem heB] at hu,
    exact (hB.cl.symm.trans_subset (M.cl_subset_cl_of_subset hu))},
  rw (hB.indep.diff {e}).not_mem_cl_iff at hfB,
  have  hf : f ∉ B,
  { refine λ hf, hef _,
    simp only [mem_diff, mem_singleton_iff, not_and, not_not] at hfB,
    exact hfB.1 hf},
  rw ←(hB.exchange_base_of_indep heB hf hfB.2).cl,
  exact M.cl_subset_cl_of_subset (insert_subset.mpr ⟨hfX,subset_trans (M.subset_cl _) hX.subset⟩),
end

lemma hyperplane.ssupset_eq_univ_of_flat (hH : M.hyperplane H) (hF : M.flat F) (h : H ⊂ F) :
  F = univ :=
begin
  apply hF.eq_univ_of_rk_le_r,
  have hlt := hH.flat.r_strict_mono hF h,
  rwa [nat.lt_iff_add_one_le, hH.r_add_one] at hlt,
end

lemma hyperplane.cl_insert_eq_univ (hH : M.hyperplane H) (he : e ∉ H) :
  M.cl (insert e H) = univ :=
hH.ssupset_eq_univ_of_flat (M.cl_flat _) ((ssubset_insert he).trans_subset (M.subset_cl _))

lemma exists_hyperplane_sep_of_not_mem_cl (h : e ∉ M.cl X) :
  ∃ H, M.hyperplane H ∧ X ⊆ H ∧ e ∉ H :=
begin
  rw not_mem_cl_iff_forall_insert_basis_insert at h,
  obtain ⟨I,hI⟩ := M.exists_basis X,
  have hIe := h.2 I hI,
  obtain ⟨B,hB,heIB⟩ := hIe.indep.exists_base_supset,
  rw insert_subset at heIB,
  refine ⟨M.cl (B \ {e}), hB.hyperplane_of_cl_diff_singleton heIB.1,_,λ hecl, _ ⟩,
  { have hIBe : I ⊆ B \ {e} := subset_diff_singleton heIB.2 (not_mem_subset hI.subset h.1),
    exact hI.subset_cl.trans (M.cl_mono hIBe)},
  exact indep_iff_cl_diff_ne_forall.mp hB.indep e heIB.1 (cl_diff_singleton_eq_cl hecl),
end

lemma cl_eq_sInter_hyperplanes (M : matroid E) (X : set E) :
  M.cl X = ⋂₀ {H | M.hyperplane H ∧ X ⊆ H} :=
begin
  apply subset_antisymm,
  { simp only [subset_sInter_iff, mem_set_of_eq, and_imp],
    exact λ H hH hXH, hH.flat.cl_subset_of_subset hXH},
  by_contra' h',
  obtain ⟨x, h, hx⟩ := not_subset.mp h',
  obtain ⟨H, hH, hXH, hxH⟩ := exists_hyperplane_sep_of_not_mem_cl hx,
  exact hxH (h H ⟨hH, hXH⟩),
end

lemma flat.subset_hyperplane_of_ne_univ (hF : M.flat F) (h : F ≠ univ) :
  ∃ H, M.hyperplane H ∧ F ⊆ H :=
begin
  obtain ⟨H,⟨hFH,hH,hne⟩,hHmax⟩ := finite.exists_maximal (λ X, F ⊆ X ∧ M.flat X ∧ X ≠ univ)
    ⟨F,subset.rfl,hF, h⟩,
  refine ⟨H, _, hFH⟩,
  rw [hyperplane_iff_maximal_cl_ne_univ, hH.cl],
  refine ⟨hne, λ X hHX, by_contra (λ hne', hHX.not_subset _)⟩,

  rw hHmax (M.cl X) ⟨hFH.trans (hHX.subset.trans (M.subset_cl _)), M.cl_flat _, hne'⟩
     (hHX.subset.trans (M.subset_cl _)),
  exact M.subset_cl _,
end

lemma subset_hyperplane_iff_cl_ne_univ :
  M.cl Y ≠ univ ↔ ∃ H, M.hyperplane H ∧ Y ⊆ H :=
begin
  refine ⟨λ h, _,_⟩,
  { obtain ⟨H, hH, hYH⟩ := (M.cl_flat Y).subset_hyperplane_of_ne_univ h,
    exact ⟨H, hH, (M.subset_cl Y).trans hYH⟩},
  rintro ⟨H, hH, hYH⟩ hY,
  refine hH.ssubset_univ.not_subset _,
  rw ←hH.flat.cl,
  exact (hY.symm.trans_subset (M.cl_mono hYH)),
end

lemma coindep_iff_cl_compl_eq_univ :
  M.coindep I ↔ M.cl Iᶜ = univ :=
begin
  rw [coindep, ←not_iff_not, not_not, ←ne.def, subset_hyperplane_iff_cl_ne_univ],  
  simp_rw [cocircuit], 
  split, 
  { rintro ⟨K, hKI, hK⟩, exact ⟨_, hK, compl_subset_compl.mpr hKI⟩},
  rintro ⟨H, hH, hIH⟩, 
  exact ⟨Hᶜ, compl_subset_comm.mp hIH, by rwa compl_compl⟩,     
end 
  

/- This follows more easily from a rank argument, but I'm trying to avoid rank. -/
lemma hyperplane.inter_right_covby_of_inter_left_covby
(hH₁ : M.hyperplane H₁) (hH₂ : M.hyperplane H₂) (h : M.covby (H₁ ∩ H₂) H₁) :
  M.covby (H₁ ∩ H₂) H₂ :=
begin
  obtain (rfl | hne) := eq_or_ne H₁ H₂, assumption,
  have hssu : H₁ ∩ H₂ ⊂ H₂,
  { refine (inter_subset_right _ _).ssubset_of_ne (λh'', hne _ ),
    rw [inter_eq_right_iff_subset, ←le_iff_subset] at h'',
    rw eq_of_le_of_not_lt h'' (hH₂.not_ssubset hH₁)},

  refine ⟨hH₁.flat.inter hH₂.flat, hH₂.flat, hssu, λ F hF hssF hFH₂, _⟩,
  by_contra' h',

  obtain ⟨x,hxF,hx⟩ := exists_of_ssubset (hssF.ssubset_of_ne (ne.symm h'.1)),
  obtain ⟨y,hyH₂,hy⟩ := exists_of_ssubset (hFH₂.ssubset_of_ne h'.2),
  obtain ⟨z,hzH₁,hz⟩ := exists_of_ssubset h.ssubset,
  have hzcl : M.cl (insert z (H₁ ∩ H₂)) = H₁ := h.cl_insert_eq ⟨hzH₁,hz⟩,
  have hxH₁ : x ∉ H₁ := λ hxH₁, hx ⟨hxH₁, hFH₂ hxF⟩,

  have h₁ : z ∉ M.cl (insert x (H₁ ∩ H₂)),
  { intro hz', apply hxH₁,
    have h' := cl_exchange ⟨hz', by rwa (hH₁.flat.inter hH₂.flat).cl⟩,
    rw [h.cl_insert_eq ⟨hzH₁,hz⟩] at h',
    exact h'.1},

  have hycl : y ∈ M.cl (insert z (insert x (H₁ ∩ H₂))) \ M.cl (insert x (H₁ ∩ H₂)),
  { refine ⟨_,λ hy',hy _⟩,
    { rw [insert_comm, ←cl_insert_cl_eq_cl_insert, hzcl, hH₁.cl_insert_eq_univ hxH₁],
      exact mem_univ _ },
    exact hF.cl_subset_of_subset (insert_subset.mpr ⟨hxF,hssF⟩) hy' },

  refine hz ⟨hzH₁, mem_of_mem_of_subset (cl_exchange hycl) ((diff_subset _ _).trans
    (hH₂.flat.cl_subset_of_subset _))⟩,
  rw [insert_subset, insert_subset],
  exact ⟨hyH₂, hFH₂ hxF, inter_subset_right _ _⟩,
end

lemma hyperplane.inter_covby_comm (hH₁ : M.hyperplane H₁) (hH₂ : M.hyperplane H₂) :
  M.covby (H₁ ∩ H₂) H₁ ↔  M.covby (H₁ ∩ H₂) H₂ :=
⟨hH₁.inter_right_covby_of_inter_left_covby hH₂,
  by {rw inter_comm, intro h, exact hH₂.inter_right_covby_of_inter_left_covby hH₁ h}⟩

end matroid

section from_axioms

lemma cl_diff_singleton_eq_cl (cl : set E → set E) (subset_cl : ∀ X, X ⊆ cl X)
(cl_mono : ∀ X Y, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X )
{x : E} {I : set E} (h : x ∈ cl (I \ {x})) :
  cl (I \ {x}) = cl I :=
begin
  refine (cl_mono _ _ (diff_subset _ _)).antisymm _,
  have h' := cl_mono _ _ (insert_subset.mpr ⟨h, (subset_cl _ )⟩),
  rw [insert_diff_singleton, cl_idem] at h',
  exact (cl_mono _ _ (subset_insert _ _)).trans h',
end

/- ### closure and flat axioms -/
/-- A function satisfying the closure axioms determines a matroid -/
def matroid_of_cl (cl : set E → set E)
  (subset_cl : ∀ X, X ⊆ cl X )
  (cl_mono : ∀ X Y, X ⊆ Y → cl X ⊆ cl Y )
  (cl_idem : ∀ X, cl (cl X) = cl X )
  (cl_exchange : ∀ X e f, f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X ) :
matroid E :=
{ base := λ B, cl B = univ ∧ ∀ X ⊂ B, cl X ≠ univ,
  exists_base' :=
  let ⟨B,hB,hBmin⟩ := finite.exists_minimal (λ B, cl B = univ)
      ⟨univ, eq_univ_of_univ_subset (subset_cl _)⟩ in
    ⟨B, hB, λ X hXB hX, hXB.ne.symm (hBmin _ hX hXB.subset)⟩,
  base_exchange' :=
  begin
    intros B₁ B₂ hB₁ hB₂ x hx,
    by_contra' h,
    have h₁ : ∀ y ∈ B₂, y ∉ cl (B₁ \ {x}) → cl (insert y (B₁ \ {x})) = univ,
    { refine λ y hyB₂ hynotin, _,
      have hex := cl_exchange (B₁ \ {x}) x y,
      rw [insert_diff_singleton, insert_eq_of_mem hx.1, hB₁.1, ←compl_eq_univ_diff,
        mem_compl_iff] at hex,
      have h' := insert_subset.mpr ⟨(hex hynotin).1, (subset_insert _ _).trans (subset_cl _)⟩,
      rw [insert_diff_singleton, insert_eq_of_mem hx.1] at h',
      have h'' := cl_mono _ _ h',
      rwa [cl_idem, hB₁.1, univ_subset_iff] at h''},

    have hss : B₂ \ B₁ ⊆ cl (B₁ \ {x}),
    { refine λ y hy, by_contra (λ h', _),
      have hxy : x ≠ y,
      { rintro rfl, exact hx.2 hy.1},
      obtain ⟨A,⟨hAs,hA⟩,hAmin⟩ := finite.exists_minimal _ (h y hy (h₁ y hy.1 h')),
      have hxA : x ∉ A,
      { refine λ hxA, hxy _,  have := hAs.subset, simpa using this hxA},
      have hyA : y ∈ A,
      { by_contra hyA,
        exact hB₁.2 _ (((subset_insert_iff_of_not_mem hyA).mp hAs.subset).trans_ssubset
          $ diff_singleton_ssubset.2 hx.1) hA },
      have hy' : B₁ ⊆ cl (A \ {y}),
      { refine λ z hz, by_contra (λ hz', _ ),
        have hzA : z ∈ cl (insert y (A \ {y})),
        { rw [insert_diff_singleton, insert_eq_of_mem hyA, hA], exact mem_univ _,},
        have h' := (cl_exchange _ _ _ ⟨hzA,hz'⟩).1,
        have h'' := insert_subset.mpr ⟨h', (subset_insert _ _).trans (subset_cl _)⟩,
        rw [insert_diff_singleton, insert_eq_of_mem hyA] at h'',
        have h''' := cl_mono _ _ h'',
        rw [hA, univ_subset_iff, cl_idem] at h''',
        refine hB₁.2 _ _ h''',
        refine ssubset_of_ne_of_subset _ (insert_subset.mpr ⟨hz,_⟩),
        { obtain (rfl | hxz) := eq_or_ne x z,
          { intro h_eq,
            rw [←h_eq, insert_diff_singleton_comm hxy.symm] at hAs,
            refine hAs.not_subset _,
            rw [diff_subset_iff, insert_comm, singleton_union, insert_diff_singleton,
              insert_eq_of_mem hyA], },
          simp_rw [ne.def, ext_iff, not_forall, mem_insert_iff, mem_diff, mem_singleton_iff],
          use x,
          have := hx.1, tauto},
        rw [diff_subset_iff, singleton_union],
        exact hAs.subset.trans (insert_subset_insert (diff_subset _ _))},
      have hA' := cl_mono _ _ hy',
      rw [hB₁.1, univ_subset_iff, cl_idem] at hA',
      refine (diff_singleton_ssubset.2 hyA).ne.symm (hAmin _ ⟨_,hA'⟩ (diff_subset _ _)),
      exact (diff_subset _ _).trans_ssubset hAs},

  have ht : B₂ ⊆ _ := subset_trans _ (union_subset hss (subset_cl (B₁ \ {x}))),
  { have ht' := cl_mono _ _ ht,
    rw [hB₂.1, cl_idem, univ_subset_iff] at ht',
    exact hB₁.2 _ (diff_singleton_ssubset.2 hx.1) ht'},
  nth_rewrite 0 [←diff_union_inter B₂ B₁],
  apply union_subset_union rfl.subset,
  rintros y ⟨hy2,hy1⟩,
  rw mem_diff_singleton,
  use hy1,
  rintro rfl,
  exact hx.2 hy2,
  end }

lemma matroid_of_cl_aux (cl : set E → set E)
  (subset_cl : ∀ X, X ⊆ cl X )
  (cl_mono : ∀ X Y, X ⊆ Y → cl X ⊆ cl Y )
  (cl_idem : ∀ X, cl (cl X) = cl X )
  (cl_exchange : ∀ X e f, f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X )
  {I : set E} :
(∀ x ∈ I, cl (I \ {x}) ≠ cl I) ↔ ∃ B, cl B = univ ∧ (∀ X ⊂ B, cl X ≠ univ) ∧ I ⊆ B :=
begin
  refine ⟨λ h, _, λ h x hI hcl, _⟩,
  { obtain ⟨B, ⟨hB, hIB⟩, hBmax⟩ :=
      finite.exists_maximal (λ X, (∀ e ∈ X, cl (X \ {e}) ≠ cl X) ∧ I ⊆ X)
         ⟨I, h, rfl.subset⟩,
    refine ⟨B, by_contra (λ hBu, _), λ X hXB hX, _, hIB⟩,
    { rw [←ne.def, ne_univ_iff_exists_not_mem] at hBu,
      obtain ⟨a,haB⟩ := hBu,
      have haB' : a ∉ B := λ haB', haB (subset_cl B haB'),
      rw hBmax (insert a B) _ (subset_insert _ _) at haB',
      { exact haB' (mem_insert _ _)},
      refine ⟨λ e heaB hcl, _,  hIB.trans (subset_insert _ _)⟩,
      have hea : e ≠ a,
      { rintro rfl,
        rw [insert_diff_self_of_not_mem haB'] at hcl,
        rw hcl at haB,
        exact haB ((subset_cl (insert e B)) (mem_insert e B))},
      have heB : e ∈ B := mem_of_mem_insert_of_ne heaB hea,
      have hecl : e ∉ cl ((insert a B) \ {e}),
      { refine λ h_in, hB e heB (cl_diff_singleton_eq_cl cl subset_cl cl_mono cl_idem _),
        by_contra hecl, apply haB,
        rw ←insert_diff_singleton_comm hea.symm  at h_in,
        have := (cl_exchange _ _ _ ⟨h_in,hecl⟩).1,
        rwa [insert_diff_singleton, insert_eq_of_mem heB] at this},
      rw hcl at hecl,
      exact hecl ((subset_cl _) heaB)},
    obtain ⟨e,heB, heX⟩ := exists_of_ssubset hXB,
    have hcon := hX.symm.trans_subset (cl_mono _ _ (subset_diff_singleton hXB.subset heX)),
    rw [univ_subset_iff] at hcon,
    refine hB e heB ((cl_mono _ _ (diff_subset _ _)).antisymm _),
    rw [hcon],
    apply subset_univ},
  obtain ⟨B, hBu, hBmax, hIB⟩ := h,
  refine hBmax _ (diff_singleton_ssubset.2 $ hIB hI) _,
  rwa cl_diff_singleton_eq_cl cl subset_cl cl_mono cl_idem,
  have hdiff := cl_mono _ _  (@diff_subset_diff_left _ _ _ {x} hIB),
  rw [hcl] at hdiff,
  apply hdiff,
  apply subset_cl,
  exact hI,
end

@[simp] lemma matroid_of_cl_apply (cl : set E → set E)
  (subset_cl : ∀ X, X ⊆ cl X )
  (cl_mono : ∀ X Y, X ⊆ Y → cl X ⊆ cl Y )
  (cl_idem : ∀ X, cl (cl X) = cl X )
  (cl_exchange : ∀ X e f, f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X ) :
(matroid_of_cl cl subset_cl cl_mono cl_idem cl_exchange).cl = cl :=
begin
  set M := matroid_of_cl cl subset_cl cl_mono cl_idem cl_exchange with hM,
  apply funext,
  by_contra' h,
  obtain ⟨I,hI,hImin⟩ := finite.exists_minimal _ h,

  have hImin' : ∀ x ∈ I, M.cl (I \ {x}) = cl (I \ {x}),
  { by_contra' h,
    obtain ⟨x,hxI,hne⟩ := h,
    exact (diff_singleton_ssubset.2 hxI).ne' (hImin _ hne  $diff_subset _ _) },

  set indep : set E → Prop := λ I, ∀ x ∈ I, cl (I \ {x}) ≠ cl I with h_indep,

  have hIi : (M.indep I) ∧ (indep I),
  { rw [matroid.indep_iff_cl_diff_ne_forall],
    by_contra h', apply hI,
    simp_rw [not_and_distrib, h_indep, not_forall, not_ne_iff] at h',
    obtain (⟨x,hxI,hne⟩ | ⟨x,hxI,hne⟩) := h',
    { rw [←hne, hImin' _ hxI, cl_diff_singleton_eq_cl cl subset_cl cl_mono cl_idem],
      rw [←hImin' x hxI, hne],
      exact (M.subset_cl I) hxI},
    rw [←hne, ←hImin' _ hxI, cl_diff_singleton_eq_cl M.cl M.subset_cl M.cl_mono M.cl_cl],
    rw [hImin' _ hxI, hne],
    exact (subset_cl I) hxI},

  simp_rw [set.ext_iff, not_forall, not_iff, hIi.1.not_mem_cl_iff,
    matroid.indep_iff_subset_base, hM, matroid_of_cl] at hI,

  obtain ⟨x,hx⟩:= hI,
  obtain (hxI | hxI) := em (x ∈ cl I),
  { obtain ⟨hxI', B, ⟨hB, hBmin⟩, hxIB⟩ := hx.mpr hxI,
    refine hBmin (B \ {x}) (diff_singleton_ssubset.2 $ hxIB $ mem_insert _ _) _,
    rwa [cl_diff_singleton_eq_cl cl subset_cl cl_mono cl_idem],
    have hIBx : I ⊆ B \ {x}, from ((subset_diff_singleton ((subset_insert _ _).trans hxIB)) hxI'),
    exact cl_mono I (B \ {x}) hIBx hxI},

  have hxI' : x ∉ I, from λ hxI', hxI ((subset_cl _) hxI'),
  simp_rw [iff_false_right hxI, not_and, not_exists, not_and] at hx,

  have hxI : indep (insert x I),
   { rintro y (rfl | hy) h_eq,

    { simp only [insert_diff_of_mem, mem_singleton] at h_eq,
      refine hxI (cl_mono _ _ (diff_subset _ {y}) _),
      rw h_eq,
      refine subset_cl _ (mem_insert _ _)},

    have hxy : x ≠ y, {rintro rfl, exact hxI' hy},
    have hycl : y ∈ cl (insert x (I \ {y})),
    { rw [insert_diff_singleton_comm hxy, h_eq], apply subset_cl, exact subset_insert _ _ hy},
    have hy' : y ∉ cl (I \ {y}), from
      λ hy', hIi.2 y hy (cl_diff_singleton_eq_cl cl subset_cl cl_mono cl_idem  hy'),
    have h' := (cl_exchange _ _ _ ⟨hycl,hy'⟩).1,
    rw [insert_diff_singleton, insert_eq_of_mem hy] at h',
    exact hxI h' },
  rw [h_indep, matroid_of_cl_aux cl subset_cl cl_mono cl_idem cl_exchange] at hxI,
  obtain ⟨B, hB, hIB⟩ := hxI,
  exact hx hxI' B ⟨hB, hIB.1⟩ hIB.2,
end

lemma matroid_of_flat_aux (flat : set E → Prop) (univ_flat : flat univ)
(flat_inter : ∀ F₁ F₂, flat F₁ → flat F₂ → flat (F₁ ∩ F₂)) (X : set E) :
  flat (⋂₀ {F | flat F ∧ X ⊆ F}) ∧ ∀ F₀, flat F₀ → ((⋂₀ {F | flat F ∧ X ⊆ F}) ⊆ F₀ ↔ X ⊆ F₀) :=
begin
  set F₁ := ⋂₀ {F | flat F ∧ X ⊆ F} with hF₁,
  refine ⟨_, λ F₀ hF₀, ⟨λ hF₁F₀, _, λ hXF, _⟩⟩ ,
  { obtain ⟨F',⟨hF',hYF'⟩,hmin⟩ := finite.exists_minimal (λ F, flat F ∧ X ⊆ F)
      ⟨univ, univ_flat, subset_univ _⟩,
    convert hF',
    refine subset_antisymm (sInter_subset_of_mem ⟨hF',hYF'⟩) (subset_sInter _),
    rintro F ⟨hF,hYF⟩,
    rw hmin _ ⟨flat_inter _ _ hF hF', subset_inter hYF hYF'⟩ _,
    { apply inter_subset_left},
    apply inter_subset_right},
  { refine subset_trans (subset_sInter (λ F h, _)) hF₁F₀, exact h.2},
  apply sInter_subset_of_mem,
  exact ⟨hF₀, hXF⟩,
end

/-- A collection of sets satisfying the flat axioms determines a matroid -/
def matroid_of_flat (flat : set E → Prop) (univ_flat : flat univ)
(flat_inter : ∀ F₁ F₂, flat F₁ → flat F₂ → flat (F₁ ∩ F₂))
(flat_partition : ∀ F₀ e, flat F₀ → e ∉ F₀ →
  ∃! F₁, flat F₁ ∧ insert e F₀ ⊆ F₁ ∧ ∀ F, flat F → F₀ ⊆ F → F ⊂ F₁ → F₀ = F) :=
matroid_of_cl (λ X, ⋂₀ {F | flat F ∧ X ⊆ F})
(λ X, subset_sInter (λ F, and.right))
(λ X Y hXY, subset_sInter (λ F hF, by {apply sInter_subset_of_mem, exact ⟨hF.1, hXY.trans hF.2⟩}))
(begin
  refine λ X, (subset_sInter (λ F, and.right)).antisymm' _,
  simp only [subset_sInter_iff, mem_set_of_eq, and_imp],
  rintro F hF hXF,
  apply sInter_subset_of_mem,
  split, assumption,
  apply sInter_subset_of_mem,
  exact ⟨hF, hXF⟩,
end )
(begin
  simp only [mem_diff, mem_sInter, mem_set_of_eq, and_imp, not_forall, exists_prop,
    forall_exists_index],
  refine λ X e f h F₀ hF₀ hXF₀ hfF₀, ⟨λ Ff hFf hfXf, _,
    ⟨F₀, hF₀, hXF₀, λ heF₀, hfF₀ (h _ hF₀ (insert_subset.mpr ⟨heF₀,hXF₀⟩))⟩⟩,

  obtain ⟨hFX, hX'⟩    := matroid_of_flat_aux flat univ_flat flat_inter X,
  obtain ⟨hFXe, hXe'⟩  := matroid_of_flat_aux flat univ_flat flat_inter (insert e X),
  obtain ⟨hFXf, hXf'⟩  := matroid_of_flat_aux flat univ_flat flat_inter (insert f X),

  set FX := sInter {F | flat F ∧ X ⊆ F} with hFX_def,
  set FXe := sInter {F | flat F ∧ insert e X ⊆ F} with hFXe_def,
  set FXf := sInter {F | flat F ∧ insert f X ⊆ F} with hFXe_def,

  apply (hXf' Ff hFf).mpr hfXf,
  have heFXe : e ∈ FXe := mem_sInter.mpr (λ _ hF, hF.2 (mem_insert _ _)),
  have hfFXf : f ∈ FXf := mem_sInter.mpr (λ _ hF, hF.2 (mem_insert _ _)),

  have hXFX : X ⊆ FX := subset_sInter (λ _, and.right),
  have hfFX : f ∉ FX := λ hfFX, hfF₀ ((hX' F₀ hF₀).mpr hXF₀ hfFX),
  have heFX : e ∉ FX := λ heFX, hfFX (h _ hFX (insert_subset.mpr ⟨heFX, hXFX⟩)),
  have hFXFXe : FX ⊆ FXe,
  { rw [hX' FXe hFXe], exact subset_sInter (λ F hF, (subset_insert _ _).trans hF.2)},
  have hFXFXf : FX ⊆ FXf,
  { rw [hX' FXf hFXf], exact subset_sInter (λ F hF, (subset_insert _ _).trans hF.2)},

  have hfFXe := h FXe hFXe (insert_subset.mpr ⟨heFXe,hXFX.trans hFXFXe⟩),

  have hss := (hXf' _ hFXe).mpr (insert_subset.mpr ⟨hfFXe, hXFX.trans hFXFXe⟩),

  suffices h_eq : FXf = FXe, by rwa h_eq,
  by_contra h_ne, apply hfFX,
  have hssu := ssubset_of_subset_of_ne hss h_ne,

  obtain ⟨FXe',⟨hFXe',heFX',hmin⟩, hunique⟩ := flat_partition FX e hFX heFX,

  have hFXemin : ∀ (F : set E), flat F → FX ⊆ F → F ⊂ FXe → FX = F, from
  λ F hF hFXF hFFXe, hmin _ hF hFXF
    (hFFXe.trans_subset ((hXe' _ hFXe').mpr ((insert_subset_insert hXFX).trans heFX'))),

  rw hunique FXe ⟨hFXe, insert_subset.mpr ⟨heFXe, hFXFXe⟩, hFXemin⟩ at hssu,
  rwa ← (hmin _ hFXf hFXFXf hssu) at hfFXf,
end)

@[simp] lemma matroid_of_flat_apply (flat : set E → Prop) (univ_flat : flat univ)
(flat_inter : ∀ F₁ F₂, flat F₁ → flat F₂ → flat (F₁ ∩ F₂))
(flat_partition : ∀ F₀ e, flat F₀ → e ∉ F₀ →
∃! F₁, flat F₁ ∧ insert e F₀ ⊆ F₁ ∧ ∀ F, flat F → F₀ ⊆ F → F ⊂ F₁ → F₀ = F) :
  (matroid_of_flat flat univ_flat flat_inter flat_partition).flat = flat :=
begin
  ext F,
  simp_rw [matroid_of_flat, matroid.flat_iff_cl_self, matroid_of_cl_apply],
  refine ⟨λ hF, _, λ hF, _⟩,
  { rw ←hF, exact (matroid_of_flat_aux flat univ_flat flat_inter _).1},
  exact (subset_sInter (λ F', and.right)).antisymm' (sInter_subset_of_mem ⟨hF,rfl.subset⟩),
end


end from_axioms
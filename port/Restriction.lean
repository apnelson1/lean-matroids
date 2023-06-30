import Oneshot.Equiv

open Set

variable {α : Type _} {I J B B' B₁ B₂ X Y R : Set α} {e f : α} {M N : MatroidIn α}

namespace MatroidIn

section Restrict

/-- Restrict the matroid `M` to `X : set α`.  -/
def restrict (M : MatroidIn α) (X : Set α) : MatroidIn α :=
  matroidOfIndep (X ∩ M.e) (fun I => M.indep I ∧ I ⊆ X ∩ M.e) ⟨M.empty_indep, empty_subset _⟩
    (fun I J hJ hIJ => ⟨hJ.1.Subset hIJ, hIJ.trans hJ.2⟩)
    (by
      set Y := X ∩ M.E with hY_def
      have hY : Y ⊆ M.E := inter_subset_right _ _
      rintro I I' ⟨hI, hIY⟩ hIn hI'
      rw [← basis_iff_mem_maximals] at hIn hI' 
      obtain ⟨B', hB', rfl⟩ := hI'.exists_base
      obtain ⟨B, hB, hIB, hBIB'⟩ := hI.exists_base_subset_union_base hB'
      rw [hB'.inter_basis_iff_compl_inter_basis_dual hY, diff_inter_diff] at hI' 
      have hss : M.E \ (B' ∪ Y) ⊆ M.E \ (B ∪ Y) :=
        by
        rw [subset_diff, and_iff_right (diff_subset _ _), ← subset_compl_iff_disjoint_left, diff_eq,
          compl_inter, compl_compl, ← union_assoc, union_subset_iff,
          and_iff_left (subset_union_right _ _)]
        refine'
          hBIB'.trans
            (union_subset (hIY.trans _) (subset_union_of_subset_left (subset_union_right _ _) _))
        apply subset_union_right
      have hi : M﹡.indep (M.E \ (B ∪ Y)) :=
        by
        rw [dual_indep_iff_coindep, coindep_iff_exists]
        exact ⟨B, hB, disjoint_of_subset_right (subset_union_left _ _) disjoint_sdiff_left⟩
      have h_eq :=
        hI'.eq_of_subset_indep hi hss
          (by rw [diff_subset_iff, union_assoc, union_diff_self, ← union_assoc]; simp)
      rw [h_eq, ← diff_inter_diff, ← hB.inter_basis_iff_compl_inter_basis_dual hY] at hI' 
      have hssu : I ⊂ B ∩ Y := (subset_inter hIB hIY).ssubset_of_ne (by rintro rfl; exact hIn hI')
      obtain ⟨e, heBY, heI⟩ := exists_of_ssubset hssu
      exact
        ⟨e, ⟨⟨(hBIB' heBY.1).elim (fun h' => (heI h').elim) id, heBY.2⟩, heI⟩,
          (hB.indep.inter_right Y).Subset (insert_subset.mpr ⟨heBY, hssu.subset⟩),
          insert_subset.mpr ⟨heBY.2, hssu.subset.trans (inter_subset_right _ _)⟩⟩)
    (by
      rintro X hX I ⟨hI, hIX⟩ hIA
      obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset (subset_inter hIA hIX)
      refine'
        ⟨J,
          ⟨⟨hJ.indep, hJ.subset.trans (inter_subset_right _ _)⟩, hIJ,
            hJ.subset.trans (inter_subset_left _ _)⟩,
          fun B hB hJB => _⟩
      rw [hJ.eq_of_subset_indep hB.1.1 hJB (subset_inter hB.2.2 hB.1.2)])
    (by tauto)
#align matroid_in.restrict MatroidIn.restrict

@[class]
structure HasRestrict (α β : Type _) where
  restrict : α → β → α
#align matroid_in.has_restrict MatroidIn.HasRestrict

infixl:75 " ‖ " => HasRestrict.restrict

instance : HasRestrict (MatroidIn α) (Set α) :=
  ⟨fun M E => M.restrict E⟩

@[simp]
theorem restrict_indep_iff : (M ‖ R).indep I ↔ M.indep I ∧ I ⊆ R :=
  by
  unfold has_restrict.restrict; rw [restrict]
  simp only [subset_inter_iff, matroid_of_indep_apply, and_congr_right_iff, and_iff_left_iff_imp]
  refine' fun hI h => hI.subset_ground
#align matroid_in.restrict_indep_iff MatroidIn.restrict_indep_iff

theorem Indep.indep_restrict_of_subset (h : M.indep I) (hIR : I ⊆ R) : (M ‖ R).indep I :=
  restrict_indep_iff.mpr ⟨h, hIR⟩
#align matroid_in.indep.indep_restrict_of_subset MatroidIn.Indep.indep_restrict_of_subset

theorem restrict_ground_eq' : (M ‖ R).e = R ∩ M.e :=
  rfl
#align matroid_in.restrict_ground_eq' MatroidIn.restrict_ground_eq'

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
@[simp]
theorem restrict_ground_eq
    (hR : R ⊆ M.e := by
      run_tac
        ssE) :
    (M ‖ R).e = R := by rwa [restrict_ground_eq', inter_eq_left_iff_subset]
#align matroid_in.restrict_ground_eq MatroidIn.restrict_ground_eq

instance restrict_finite [M.Finite] : (M ‖ R).Finite :=
  ⟨M.ground_finite.Subset (inter_subset_right _ _)⟩
#align matroid_in.restrict_finite MatroidIn.restrict_finite

@[simp]
theorem restrict_dep_iff : (M ‖ R).Dep X ↔ M.Dep X ∧ X ⊆ R :=
  by
  rw [dep, restrict_indep_iff, dep, restrict_ground_eq', subset_inter_iff, and_comm' (X ⊆ R), ←
    and_assoc', and_congr_left_iff, and_congr_left_iff, not_and, imp_not_comm, imp_iff_right_iff]
  exact fun h _ => Or.inl h
#align matroid_in.restrict_dep_iff MatroidIn.restrict_dep_iff

theorem restrict_restrict (R₁ R₂ : Set α) : M ‖ R₁ ‖ R₂ = M ‖ (R₁ ∩ R₂) :=
  eq_of_indep_iff_indep_forall
    (by
      rw [restrict_ground_eq', inter_comm, restrict_ground_eq', restrict_ground_eq',
        inter_right_comm])
    fun I hI => by simp [and_assoc']
#align matroid_in.restrict_restrict MatroidIn.restrict_restrict

theorem restrict_restrict_of_subset {R₁ R₂ : Set α} (hR : R₂ ⊆ R₁) : M ‖ R₁ ‖ R₂ = M ‖ R₂ := by
  rw [restrict_restrict, inter_eq_self_of_subset_right hR]
#align matroid_in.restrict_restrict_of_subset MatroidIn.restrict_restrict_of_subset

theorem restrict_eq_restrict_iff {R₁ R₂ : Set α} : M ‖ R₁ = M ‖ R₂ ↔ R₁ ∩ M.e = R₂ ∩ M.e :=
  by
  simp only [eq_iff_indep_iff_indep_forall, subset_inter_iff, restrict_ground_eq',
    restrict_indep_iff, and_congr_right_iff, and_imp, and_iff_left_iff_imp]
  intro h_eq I hIR₁ hIE hI
  rw [iff_true_intro hIR₁, true_iff_iff]
  exact (subset_inter hIR₁ hIE).trans (h_eq.trans_subset (inter_subset_left _ _))
#align matroid_in.restrict_eq_restrict_iff MatroidIn.restrict_eq_restrict_iff

theorem restrict_inter_ground (M : MatroidIn α) (R : Set α) : M ‖ (R ∩ M.e) = M ‖ R := by
  rw [restrict_eq_restrict_iff, inter_assoc, inter_self]
#align matroid_in.restrict_inter_ground MatroidIn.restrict_inter_ground

theorem Indep.of_restrict (hI : (M ‖ R).indep I) : M.indep I :=
  (restrict_indep_iff.mp hI).1
#align matroid_in.indep.of_restrict MatroidIn.Indep.of_restrict

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
@[simp]
theorem restrict_base_iff
    (hX : X ⊆ M.e := by
      run_tac
        ssE) :
    (M ‖ X).base I ↔ M.Basis I X :=
  by
  rw [base_iff_mem_maximals, basis_iff_mem_maximals]
  conv =>
    lhs
    congr
    skip
    congr
    skip
    congr
    ext
    rw [restrict_indep_iff]
  rfl
#align matroid_in.restrict_base_iff MatroidIn.restrict_base_iff

instance restrict_finiteRk [M.FiniteRk] : (M ‖ R).FiniteRk :=
  let ⟨B, hB⟩ := (M ‖ R).exists_base
  hB.finiteRk_of_finite hB.indep.of_restrict.Finite
#align matroid_in.restrict_finite_rk MatroidIn.restrict_finiteRk

@[simp]
theorem Basis.base_restrict (h : M.Basis I X) : (M ‖ X).base I :=
  restrict_base_iff.mpr h
#align matroid_in.basis.base_restrict MatroidIn.Basis.base_restrict

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
theorem Basis.basis_restrict_of_subset (hI : M.Basis I X) (hXY : X ⊆ Y)
    (hY : Y ⊆ M.e := by
      run_tac
        ssE) :
    (M ‖ Y).Basis I X := by
  rwa [← restrict_base_iff, restrict_restrict_of_subset hXY, restrict_base_iff]; simpa
#align matroid_in.basis.basis_restrict_of_subset MatroidIn.Basis.basis_restrict_of_subset

@[simp]
theorem restrict_ground_eq_self (M : MatroidIn α) : M ‖ M.e = M :=
  by
  refine' eq_of_indep_iff_indep_forall (restrict_ground_eq subset.rfl) fun I hI => _
  rw [restrict_ground_eq] at hI 
  rw [restrict_indep_iff, and_iff_left_iff_imp]
  exact fun _ => hI
#align matroid_in.restrict_ground_eq_self MatroidIn.restrict_ground_eq_self

theorem restrict_eq_self_iff : M ‖ X = M ↔ M.e ⊆ X :=
  by
  simp only [eq_iff_indep_iff_indep_forall, restrict_indep_iff, and_iff_left_iff_imp,
    restrict_ground_eq', inter_eq_right_iff_subset]
  exact fun h I hI hI' => hI.trans (inter_subset_left _ _)
#align matroid_in.restrict_eq_self_iff MatroidIn.restrict_eq_self_iff

def Restriction (N M : MatroidIn α) : Prop :=
  M ‖ N.e = N
#align matroid_in.restriction MatroidIn.Restriction

def StrictRestriction (N M : MatroidIn α) : Prop :=
  M ‖ N.e = N ∧ N.e ⊂ M.e
#align matroid_in.strict_restriction MatroidIn.StrictRestriction

infixl:75 " ≤r " => MatroidIn.Restriction

infixl:75 " <r " => MatroidIn.StrictRestriction

theorem Restriction.eq_restrict (h : N ≤r M) : M ‖ N.e = N :=
  h
#align matroid_in.restriction.eq_restrict MatroidIn.Restriction.eq_restrict

theorem Restriction.ground_subset_ground (h : N ≤r M) : N.e ⊆ M.e := by rw [← h.eq_restrict];
  apply inter_subset_right
#align matroid_in.restriction.ground_subset_ground MatroidIn.Restriction.ground_subset_ground

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (R «expr ⊆ » M.E) -/
theorem Restriction.exists_eq_restrict (h : N ≤r M) : ∃ (R : _) (_ : R ⊆ M.e), N = M ‖ R := by
  rw [← h.eq_restrict]; exact ⟨N.E, h.ground_subset_ground, rfl⟩
#align matroid_in.restriction.exists_eq_restrict MatroidIn.Restriction.exists_eq_restrict

theorem StrictRestriction.restriction (h : N <r M) : N ≤r M :=
  h.1
#align matroid_in.strict_restriction.restriction MatroidIn.StrictRestriction.restriction

@[simp]
theorem restrict_restriction (M : MatroidIn α) (R : Set α) : M ‖ R ≤r M := by
  rw [restriction, restrict_ground_eq', restrict_inter_ground]
#align matroid_in.restrict_restriction MatroidIn.restrict_restriction

theorem StrictPminor.ne (h : N <r M) : N ≠ M := by rintro rfl; exact h.2.Ne rfl
#align matroid_in.strict_pminor.ne MatroidIn.StrictPminor.ne

theorem Restriction.strictRestriction_of_ne (h : N ≤r M) (hne : N ≠ M) : N <r M :=
  by
  rw [strict_restriction, and_iff_right h.eq_restrict, ssubset_iff_subset_ne, ← h.eq_restrict,
    restrict_ground_eq', and_iff_right (inter_subset_right _ _), Ne.def, inter_eq_right_iff_subset]
  intro h_eq
  rw [← h.eq_restrict, ← restrict_inter_ground, inter_eq_self_of_subset_right h_eq,
    restrict_ground_eq_self] at hne 
  exact hne rfl
#align matroid_in.restriction.strict_restriction_of_ne MatroidIn.Restriction.strictRestriction_of_ne

instance Restriction.trans : IsTrans (MatroidIn α) (· ≤r ·) :=
  ⟨fun M₁ M₂ M₃ h₁ h₂ =>
    by
    rw [← h₁.eq_restrict, ← h₂.eq_restrict, restriction]
    simp_rw [restrict_ground_eq', restrict_restrict, restrict_eq_restrict_iff]
    rw [inter_assoc, inter_assoc, inter_self, inter_right_comm, inter_comm _ M₁.E]⟩
#align matroid_in.restriction.trans MatroidIn.Restriction.trans

instance Restriction.refl : IsRefl (MatroidIn α) (· ≤r ·) :=
  ⟨restrict_ground_eq_self⟩
#align matroid_in.restriction.refl MatroidIn.Restriction.refl

instance Restriction.antisymm : IsAntisymm (MatroidIn α) (· ≤r ·) :=
  ⟨fun M M' h h' => by
    rw [← h.eq_restrict, h.ground_subset_ground.antisymm h'.ground_subset_ground,
      restrict_ground_eq_self]⟩
#align matroid_in.restriction.antisymm MatroidIn.Restriction.antisymm

-- This proof is HORRIBLE. There is possibly a much better way to do isomorphisms.
noncomputable def restrictIso {β : Type _} {N : MatroidIn β} (i : M ≃i N) (R : Set α) :
    M ‖ R ≃i (N ‖ i.image R) :=
  let f : (M ‖ R).e → β := fun x => i ⟨x, mem_of_mem_of_subset x.Prop (inter_subset_right _ _)⟩
  let hf : f.Injective := fun x y hxy => Subtype.coe_inj.mp (by simpa using subtype.coe_inj.mp hxy)
  isoOfIndep
    ((Equiv.ofInjective f hf).trans
      (Equiv.Set.ofEq
        (by
          simp_rw [restrict_ground_eq']
          rw [inter_eq_self_of_subset_left (iso.image_subset_ground _ _), iso.image,
            subset_antisymm_iff]
          simp only [image_subset_iff]
          constructor
          · rintro y ⟨⟨x, hx⟩, rfl⟩
            exact ⟨i ⟨x, (inter_subset_right _ _) hx⟩, ⟨⟨x, hx.2⟩, hx.1, rfl⟩, rfl⟩
          rintro x (hx : coe x ∈ R)
          simp only [mem_preimage, mem_range, SetCoe.exists]
          refine' ⟨x, ⟨hx, x.2⟩, _⟩
          simp [Subtype.coe_inj])))
    (by
      intro I
      simp only [image_subset_iff, Subtype.coe_mk, restrict_indep_iff, Equiv.coe_trans,
        Function.comp_apply, Equiv.ofInjective_apply, Equiv.Set.ofEq_apply]
      rw [i.on_indep, and_iff_left, and_iff_left]
      · convert Iff.rfl using 2
        unfold iso.image
        rw [subset_antisymm_iff]; constructor
        · rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
          exact ⟨i ⟨z, (inter_subset_right _ _) z.prop⟩, ⟨_, by simpa, rfl⟩, rfl⟩
        rintro x ⟨y, ⟨⟨z, hzE⟩, ⟨⟨w, hw⟩, hwI, rfl : w = z⟩, rfl⟩, rfl⟩
        rw [restrict_ground_eq', mem_inter_iff] at hw 
        exact
          ⟨⟨i ⟨w, hzE⟩, ⟨⟨i ⟨w, hzE⟩, ⟨_, by simpa using hw.1, rfl⟩, rfl⟩, by simp⟩⟩,
            ⟨⟨w, hw⟩, hwI, rfl⟩, rfl⟩
      · rintro ⟨x, hxR, hxE⟩ hxI
        simp only [mem_preimage, Subtype.coe_mk]
        exact ⟨i ⟨x, _⟩, ⟨_, by simpa, rfl⟩, rfl⟩
      · rintro ⟨x, hxR, hxE⟩ hxI; exact hxR
      rintro _ ⟨⟨x, hxR, hxE⟩, hI, rfl⟩
      exact hxE)
#align matroid_in.restrict_iso MatroidIn.restrictIso

end Restrict

section Basis

theorem Basis.transfer (hIX : M.Basis I X) (hJX : M.Basis J X) (hXY : X ⊆ Y) (hJY : M.Basis J Y) :
    M.Basis I Y := by
  rw [← restrict_base_iff]
  exact
    (restrict_base_iff.mpr hJY).base_of_basis_supset hJX.subset (hIX.basis_restrict_of_subset hXY)
#align matroid_in.basis.transfer MatroidIn.Basis.transfer

theorem Basis.transfer' (hI : M.Basis I X) (hJ : M.Basis J Y) (hJX : J ⊆ X) (hIY : I ⊆ Y) :
    M.Basis I Y :=
  by
  have hI' := hI.basis_subset (subset_inter hI.subset hIY) (inter_subset_left _ _)
  have hJ' := hJ.basis_subset (subset_inter hJX hJ.subset) (inter_subset_right _ _)
  exact hI'.transfer hJ' (inter_subset_right _ _) hJ
#align matroid_in.basis.transfer' MatroidIn.Basis.transfer'

theorem Basis.transfer'' (hI : M.Basis I X) (hJ : M.Basis J Y) (hJX : J ⊆ X) : M.Basis I (I ∪ Y) :=
  by
  obtain ⟨J', hJ', hJJ'⟩ := hJ.indep.subset_basis_of_subset hJX
  have hJ'Y := (hJ.basis_union_of_subset hJ'.indep hJJ').basis_union hJ'
  refine' (hI.transfer' hJ'Y hJ'.subset _).basis_subset _ _
  · exact subset_union_of_subset_right hI.subset _
  · exact subset_union_left _ _
  refine' union_subset (subset_union_of_subset_right hI.subset _) _
  rw [union_right_comm]
  exact subset_union_right _ _
#align matroid_in.basis.transfer'' MatroidIn.Basis.transfer''

theorem Indep.exists_basis_subset_union_basis (hI : M.indep I) (hIX : I ⊆ X) (hJ : M.Basis J X) :
    ∃ I', M.Basis I' X ∧ I ⊆ I' ∧ I' ⊆ I ∪ J :=
  by
  obtain ⟨I', hI', hII', hI'IJ⟩ :=
    (hI.indep_restrict_of_subset hIX).exists_base_subset_union_base (basis.base_restrict hJ)
  exact ⟨I', restrict_base_iff.mp hI', hII', hI'IJ⟩
#align matroid_in.indep.exists_basis_subset_union_basis MatroidIn.Indep.exists_basis_subset_union_basis

theorem Indep.exists_insert_of_not_basis (hI : M.indep I) (hIX : I ⊆ X) (hI' : ¬M.Basis I X)
    (hJ : M.Basis J X) : ∃ e ∈ J \ I, M.indep (insert e I) :=
  by
  rw [← restrict_base_iff] at hI' ; rw [← restrict_base_iff] at hJ 
  -- hJ,
  obtain ⟨e, he, hi⟩ := (hI.indep_restrict_of_subset hIX).exists_insert_of_not_base hI' hJ
  exact ⟨e, he, (restrict_indep_iff.mp hi).1⟩
#align matroid_in.indep.exists_insert_of_not_basis MatroidIn.Indep.exists_insert_of_not_basis

theorem Basis.base_of_base_subset (hIX : M.Basis I X) (hB : M.base B) (hBX : B ⊆ X) : M.base I :=
  hB.base_of_basis_supset hBX hIX
#align matroid_in.basis.base_of_base_subset MatroidIn.Basis.base_of_base_subset

theorem Basis.exchange (hIX : M.Basis I X) (hJX : M.Basis J X) (he : e ∈ I \ J) :
    ∃ f ∈ J \ I, M.Basis (insert f (I \ {e})) X := by simp_rw [← restrict_base_iff] at *;
  exact hIX.exchange hJX he
#align matroid_in.basis.exchange MatroidIn.Basis.exchange

theorem Basis.eq_exchange_of_diff_eq_singleton (hI : M.Basis I X) (hJ : M.Basis J X)
    (hIJ : I \ J = {e}) : ∃ f ∈ J \ I, J = insert f I \ {e} := by
  rw [← restrict_base_iff] at hI hJ ; exact hI.eq_exchange_of_diff_eq_singleton hJ hIJ
#align matroid_in.basis.eq_exchange_of_diff_eq_singleton MatroidIn.Basis.eq_exchange_of_diff_eq_singleton

end Basis

section Finite

theorem Basis.encard_eq_encard_of_basis (hIX : M.Basis I X) (hJX : M.Basis J X) :
    I.encard = J.encard := by rw [← restrict_base_iff] at hIX hJX ;
  exact hIX.encard_eq_encard_of_base hJX
#align matroid_in.basis.encard_eq_encard_of_basis MatroidIn.Basis.encard_eq_encard_of_basis

theorem Basis.encard_diff_comm (hI : M.Basis I X) (hJ : M.Basis J X) :
    (I \ J).encard = (J \ I).encard := by rw [← restrict_base_iff] at hI hJ ;
  rw [hJ.encard_diff_comm hI]
#align matroid_in.basis.encard_diff_comm MatroidIn.Basis.encard_diff_comm

theorem Basis.card_eq_card_of_basis (hIX : M.Basis I X) (hJX : M.Basis J X) : I.ncard = J.ncard :=
  by rw [← restrict_base_iff] at hIX hJX ; exact hIX.card_eq_card_of_base hJX
#align matroid_in.basis.card_eq_card_of_basis MatroidIn.Basis.card_eq_card_of_basis

theorem Basis.finite_of_finite (hIX : M.Basis I X) (hI : I.Finite) (hJX : M.Basis J X) : J.Finite :=
  by rw [← restrict_base_iff] at hIX hJX ; exact hIX.finite_of_finite hI hJX
#align matroid_in.basis.finite_of_finite MatroidIn.Basis.finite_of_finite

theorem Basis.infinite_of_infinite (hIX : M.Basis I X) (hI : I.Infinite) (hJX : M.Basis J X) :
    J.Infinite := by rw [← restrict_base_iff] at hIX hJX ; exact hIX.infinite_of_infinite hI hJX
#align matroid_in.basis.infinite_of_infinite MatroidIn.Basis.infinite_of_infinite

theorem Basis.card_diff_comm (hI : M.Basis I X) (hJ : M.Basis J X) :
    (I \ J).ncard = (J \ I).ncard := by rw [← restrict_base_iff] at hI hJ ;
  rw [hJ.card_diff_comm hI]
#align matroid_in.basis.card_diff_comm MatroidIn.Basis.card_diff_comm

theorem Basis.diff_finite_comm (hIX : M.Basis I X) (hJX : M.Basis J X) :
    (I \ J).Finite ↔ (J \ I).Finite := by rw [← restrict_base_iff] at hIX hJX ;
  exact hIX.diff_finite_comm hJX
#align matroid_in.basis.diff_finite_comm MatroidIn.Basis.diff_finite_comm

theorem Basis.diff_infinite_comm (hIX : M.Basis I X) (hJX : M.Basis J X) :
    (I \ J).Infinite ↔ (J \ I).Infinite := by rw [← restrict_base_iff] at hIX hJX ;
  exact hIX.diff_infinite_comm hJX
#align matroid_in.basis.diff_infinite_comm MatroidIn.Basis.diff_infinite_comm

theorem Indep.augment_of_finite (hI : M.indep I) (hJ : M.indep J) (hIfin : I.Finite)
    (hIJ : I.ncard < J.ncard) : ∃ x ∈ J, x ∉ I ∧ M.indep (insert x I) :=
  by
  obtain ⟨K, hK, hIK⟩ := (hI.indep_restrict_of_subset (subset_union_left I J)).exists_base_supset
  obtain ⟨K', hK', hJK'⟩ :=
    (hJ.indep_restrict_of_subset (subset_union_right I J)).exists_base_supset
  have hJfin := finite_of_ncard_pos ((Nat.zero_le _).trans_lt hIJ)
  rw [restrict_base_iff] at hK hK' 
  have hK'fin := (hIfin.union hJfin).Subset hK'.subset
  have hlt :=
    hIJ.trans_le ((ncard_le_of_subset hJK' hK'fin).trans_eq (hK'.card_eq_card_of_basis hK))
  obtain ⟨e, he⟩ := exists_mem_not_mem_of_ncard_lt_ncard hlt hIfin
  exact
    ⟨e, (hK.subset he.1).elim (False.elim ∘ he.2) id, he.2,
      hK.indep.subset (insert_subset.mpr ⟨he.1, hIK⟩)⟩
#align matroid_in.indep.augment_of_finite MatroidIn.Indep.augment_of_finite

theorem Indep.augment_of_encard_lt (hI : M.indep I) (hJ : M.indep J) (hIJ : I.encard < J.encard) :
    ∃ x ∈ J, x ∉ I ∧ M.indep (insert x I) :=
  by
  have hIfin := finite_of_encard_lt hIJ
  have hle := ENat.add_one_le_of_lt hIJ
  obtain ⟨J', hJ'ss, hJ'⟩ := exists_subset_encard_eq hle
  obtain ⟨x, hxJ', h⟩ := hI.augment_of_finite (hJ.subset hJ'ss) hIfin _
  · exact ⟨_, hJ'ss hxJ', h⟩
  rw [← encard_to_nat_eq J', hJ', ENat.toNat_add hIfin.encard_lt_top.ne] <;> simp
#align matroid_in.indep.augment_of_encard_lt MatroidIn.Indep.augment_of_encard_lt

/-- The independence augmentation axiom; given independent sets `I,J` with `I` smaller than `J`, 
  there is an element `e` of `J \ I` whose insertion into `e` gives an independent set.  -/
theorem Indep.augment [FiniteRk M] (hI : M.indep I) (hJ : M.indep J) (hIJ : I.ncard < J.ncard) :
    ∃ x ∈ J, x ∉ I ∧ M.indep (insert x I) :=
  hI.augment_of_finite hJ hI.Finite hIJ
#align matroid_in.indep.augment MatroidIn.Indep.augment

/-- The independence augmentation axiom in a form that finds a strict superset -/
theorem Indep.sSubset_indep_of_card_lt_of_finite (hI : M.indep I) (hI_fin : I.Finite)
    (hJ : M.indep J) (hIJ : I.ncard < J.ncard) : ∃ I', M.indep I' ∧ I ⊂ I' ∧ I' ⊆ I ∪ J :=
  by
  obtain ⟨e, heJ, heI, hI'⟩ := hI.augment_of_finite hJ hI_fin hIJ
  exact ⟨_, hI', ssubset_insert heI, insert_subset.mpr ⟨Or.inr heJ, subset_union_left _ _⟩⟩
#align matroid_in.indep.ssubset_indep_of_card_lt_of_finite MatroidIn.Indep.sSubset_indep_of_card_lt_of_finite

theorem Indep.sSubset_indep_of_card_lt [FiniteRk M] (hI : M.indep I) (hJ : M.indep J)
    (hIJ : I.ncard < J.ncard) : ∃ I', M.indep I' ∧ I ⊂ I' ∧ I' ⊆ I ∪ J :=
  hI.sSubset_indep_of_card_lt_of_finite hI.Finite hJ hIJ
#align matroid_in.indep.ssubset_indep_of_card_lt MatroidIn.Indep.sSubset_indep_of_card_lt

theorem Indep.le_encard_basis (hI : M.indep I) (hIX : I ⊆ X) (hJX : M.Basis J X) :
    I.encard ≤ J.encard :=
  by
  obtain ⟨I', hI', h⟩ := hI.subset_basis_of_subset hIX
  rw [hJX.encard_eq_encard_of_basis hI']
  exact encard_mono h
#align matroid_in.indep.le_encard_basis MatroidIn.Indep.le_encard_basis

theorem Indep.le_card_basis [FiniteRk M] (hI : M.indep I) (hIX : I ⊆ X) (hJX : M.Basis J X) :
    I.ncard ≤ J.ncard := by
  have hle := hI.le_encard_basis hIX hJX
  rwa [hI.finite.encard_eq, hJX.finite.encard_eq, Nat.cast_le] at hle 
#align matroid_in.indep.le_card_basis MatroidIn.Indep.le_card_basis

-- refine le_of_not_lt (λ hlt, _),
-- obtain ⟨I', hI'⟩ := hJX.indep.ssubset_indep_of_card_lt hI hlt,
-- have := hJX.eq_of_subset_indep hI'.1 hI'.2.1.subset (hI'.2.2.trans (union_subset hJX.subset hIX)),
-- subst this,
-- exact hI'.2.1.ne rfl,
end Finite

end MatroidIn


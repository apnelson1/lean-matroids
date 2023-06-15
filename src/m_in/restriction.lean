import .equiv

open set

variables {α : Type*} {I J B B' B₁ B₂ X Y R : set α} {e f : α} {M N : matroid_in α}

namespace matroid_in 

section restrict 

/-- Restrict the matroid `M` to `X : set α`.  -/
def restrict (M : matroid_in α) (X : set α) : matroid_in α :=
matroid_of_indep (X ∩ M.E) (λ I, M.indep I ∧ I ⊆ X ∩ M.E) ⟨M.empty_indep, empty_subset _⟩ 
(λ I J hJ hIJ, ⟨hJ.1.subset hIJ, hIJ.trans hJ.2⟩)
(begin
  set Y := X ∩ M.E with hY_def, 
  have hY : Y ⊆ M.E := inter_subset_right _ _, 
  rintro I I' ⟨hI, hIY⟩ hIn hI',
  rw ←basis_iff_mem_maximals at hIn hI', 
  obtain ⟨B', hB', rfl⟩ := hI'.exists_base, 
  obtain ⟨B, hB, hIB, hBIB'⟩ := hI.exists_base_subset_union_base hB',
  
  rw [hB'.inter_basis_iff_compl_inter_basis_dual hY, diff_inter_diff] at hI', 
  
  have hss : M.E \ (B' ∪ Y) ⊆ M.E \ (B ∪ Y), 
  { rw [subset_diff, and_iff_right (diff_subset _ _), ←subset_compl_iff_disjoint_left, 
      diff_eq, compl_inter, compl_compl, ←union_assoc, union_subset_iff, 
      and_iff_left (subset_union_right _ _)],
    refine hBIB'.trans (union_subset (hIY.trans _) 
      (subset_union_of_subset_left (subset_union_right _ _) _)), 
    apply subset_union_right },

  have hi : M﹡.indep (M.E \ (B ∪ Y)), 
  { rw [dual_indep_iff_exists, and_iff_right (diff_subset _ _)], 
    exact ⟨B, hB, disjoint_of_subset_right (subset_union_left _ _) disjoint_sdiff_left⟩ }, 
  have h_eq := hI'.eq_of_subset_indep hi hss 
    (by {rw [diff_subset_iff, union_assoc, union_diff_self, ←union_assoc], simp }), 
  
  rw [h_eq, ←diff_inter_diff, ←hB.inter_basis_iff_compl_inter_basis_dual hY] at hI', 

  have hssu : I ⊂ (B ∩ Y) := (subset_inter hIB hIY).ssubset_of_ne 
    (by { rintro rfl, exact hIn hI' }), 

  obtain ⟨e, heBY, heI⟩ := exists_of_ssubset hssu, 
  exact ⟨e, ⟨⟨(hBIB' heBY.1).elim (λ h', (heI h').elim) id ,heBY.2⟩,heI⟩, 
    (hB.indep.inter_right Y).subset (insert_subset.mpr ⟨heBY,hssu.subset⟩), 
    insert_subset.mpr ⟨heBY.2,hssu.subset.trans (inter_subset_right _ _)⟩⟩, 
end)
(begin
  rintro I A ⟨hI, hIX⟩ hIA, 
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset (subset_inter hIA hIX), 
  refine ⟨J, ⟨⟨hJ.indep,hJ.subset.trans (inter_subset_right _ _)⟩,hIJ,
    hJ.subset.trans (inter_subset_left _ _)⟩, λ B hB hJB, _⟩, 
  rw hJ.eq_of_subset_indep hB.1.1 hJB (subset_inter hB.2.2 hB.1.2), 
end)
( by tauto )   

@[class] structure has_restrict (α β : Type*) := (restrict : α → β → α)

infix ` ‖ ` :75 :=  has_restrict.restrict 

instance : has_restrict (matroid_in α) (set α) := ⟨λ M E, M.restrict E⟩  

@[simp] lemma restrict_indep_iff : (M ‖ R).indep I ↔ M.indep I ∧ I ⊆ R :=
begin
  unfold has_restrict.restrict, rw [restrict], 
  simp only [subset_inter_iff, matroid_of_indep_apply, and.congr_right_iff, and_iff_left_iff_imp],  
  refine λ hI h, hI.subset_ground, 
end 

lemma indep.indep_restrict_of_subset (h : M.indep I) (hIR : I ⊆ R) : (M ‖ R).indep I := 
restrict_indep_iff.mpr ⟨h,hIR⟩

lemma restrict_ground_eq' : (M ‖ R).E = R ∩ M.E := rfl 

@[simp] lemma restrict_ground_eq (hR : R ⊆ M.E . ssE) : (M ‖ R).E = R := 
by rwa [restrict_ground_eq', inter_eq_left_iff_subset]

instance restrict_finite [M.finite] : (M ‖ R).finite := 
⟨M.ground_finite.subset (inter_subset_right _ _)⟩  

@[simp] lemma restrict_dep_iff : (M ‖ R).dep X ↔ M.dep X ∧ X ⊆ R :=
begin
  rw [dep, restrict_indep_iff, dep, restrict_ground_eq', subset_inter_iff, and_comm (X ⊆ R), 
    ←and_assoc, and.congr_left_iff, and.congr_left_iff, not_and, imp_not_comm, imp_iff_right_iff], 
  exact λ h _, or.inl h, 
end  

lemma restrict_restrict (R₁ R₂ : set α) : (M ‖ R₁) ‖ R₂ = M ‖ (R₁ ∩ R₂) := 
eq_of_indep_iff_indep_forall 
(by rw [restrict_ground_eq', inter_comm, restrict_ground_eq', restrict_ground_eq', inter_right_comm]) 
(λ I hI, by simp [and_assoc])

lemma restrict_restrict_of_subset {R₁ R₂ : set α} (hR : R₂ ⊆ R₁) : (M ‖ R₁) ‖ R₂ = M ‖ R₂ :=
by rw [restrict_restrict, inter_eq_self_of_subset_right hR]

lemma restrict_eq_restrict_iff {R₁ R₂ : set α} : M ‖ R₁ = M ‖ R₂ ↔ R₁ ∩ M.E = R₂ ∩ M.E :=
begin
  simp only [eq_iff_indep_iff_indep_forall, subset_inter_iff, restrict_ground_eq', 
    restrict_indep_iff, and.congr_right_iff, and_imp, and_iff_left_iff_imp], 
  intros h_eq I hIR₁ hIE hI, 
  rw [iff_true_intro hIR₁, true_iff], 
  exact (subset_inter hIR₁ hIE).trans (h_eq.trans_subset (inter_subset_left _ _)), 
end 

lemma restrict_inter_ground (M : matroid_in α) (R : set α) : M ‖ (R ∩ M.E) = M ‖ R := 
by rw [restrict_eq_restrict_iff, inter_assoc, inter_self]

lemma indep.of_restrict (hI : (M ‖ R).indep I) : M.indep I := 
(restrict_indep_iff.mp hI).1 

@[simp] lemma restrict_base_iff (hX : X ⊆ M.E . ssE) : (M ‖ X).base I ↔ M.basis I X := 
begin
  rw [base_iff_mem_maximals, basis_iff_mem_maximals], 
  conv {to_lhs, congr, skip, congr, skip, congr, funext, rw restrict_indep_iff}, 
  refl, 
end 

instance restrict_finite_rk [M.finite_rk] : (M ‖ R).finite_rk := 
let ⟨B, hB⟩ := (M ‖ R).exists_base in hB.finite_rk_of_finite (hB.indep.of_restrict.finite)

@[simp] lemma basis.base_restrict (h : M.basis I X) : (M ‖ X).base I := 
restrict_base_iff.mpr h

lemma basis.basis_restrict_of_subset (hI : M.basis I X) (hXY : X ⊆ Y) (hY : Y ⊆ M.E . ssE) : 
  (M ‖ Y).basis I X :=
by { rwa [←restrict_base_iff, restrict_restrict_of_subset hXY, restrict_base_iff], simpa }

@[simp] lemma restrict_ground_eq_self (M : matroid_in α) : M ‖ M.E = M :=
begin
  refine eq_of_indep_iff_indep_forall (restrict_ground_eq subset.rfl) (λ I hI, _), 
  rw [restrict_ground_eq] at hI, 
  rw [restrict_indep_iff, and_iff_left_iff_imp],
  exact λ _, hI, 
end 

@[simp] lemma restrict_empty_eq_empty (M : matroid_in α) : M ‖ (∅ : set α) = (empty α) :=  
by rw [←ground_eq_empty_iff_eq_empty, restrict_ground_eq]

lemma restrict_eq_self_iff : M ‖ X = M ↔ M.E ⊆ X := 
begin
  simp only [eq_iff_indep_iff_indep_forall, restrict_indep_iff, and_iff_left_iff_imp, 
    restrict_ground_eq', inter_eq_right_iff_subset], 
  exact λ h I hI hI', hI.trans (inter_subset_left _ _), 
end   

def restriction (N M : matroid_in α) : Prop := M ‖ N.E = N 

def strict_restriction (N M : matroid_in α) : Prop := (M ‖ N.E = N) ∧ N.E ⊂ M.E 

infix ` ≤r ` :75 :=  matroid_in.restriction

infix ` <r ` :75 :=  matroid_in.strict_restriction

lemma restriction.eq_restrict (h : N ≤r M) : M ‖ N.E = N :=
h 

lemma strict_restriction.restriction (h : N <r M) : N ≤r M :=
h.1

@[simp] lemma restrict_restriction (M : matroid_in α) (R : set α) : M ‖ R ≤r M := 
by rw [restriction, restrict_ground_eq', restrict_inter_ground]

lemma strict_pminor.ne (h : N <r M) : N ≠ M := 
by { rintro rfl, exact h.2.ne rfl }

lemma restriction.strict_restriction_of_ne (h : N ≤r M) (hne : N ≠ M) : N <r M :=
begin
  rw [strict_restriction, and_iff_right h.eq_restrict, ssubset_iff_subset_ne, ←h.eq_restrict, 
    restrict_ground_eq', and_iff_right (inter_subset_right _ _), ne.def, inter_eq_right_iff_subset], 
  intro h_eq, 
  rw [←h.eq_restrict, ←restrict_inter_ground, inter_eq_self_of_subset_right h_eq, 
    restrict_ground_eq_self] at hne, 
  exact hne rfl, 
end 

instance restriction.trans : is_trans (matroid_in α) (≤r) := 
⟨λ M₁ M₂ M₃ h₁ h₂, by { rw [←h₁.eq_restrict, ←h₂.eq_restrict, restriction],
  simp_rw [restrict_ground_eq', restrict_restrict, restrict_eq_restrict_iff], 
  rw [inter_assoc, inter_assoc, inter_self, inter_right_comm, inter_comm _ M₁.E] }⟩ 

instance restriction.refl : is_refl (matroid_in α) (≤r) := 
⟨restrict_ground_eq_self⟩   

instance restriction.antisymm : is_antisymm (matroid_in α) (≤r) :=
begin
  refine ⟨λ M M' (h : _ = M) (h' : _ = M'), _⟩,  
  rw [←h', ←M.restrict_ground_eq_self, restrict_restrict, restrict_eq_restrict_iff, 
    inter_right_comm, inter_self, eq_comm, inter_eq_left_iff_subset, ←h, restrict_ground_eq'],
  exact inter_subset_right _ _,  
end 


def foo {α β : Type*} {s : set α} {t : set β} (e : s ≃ t) (a : set s) : 
  (coe '' a : set α) ≃ (coe '' (e '' a) : set β) :=
begin
  have := @equiv.subtype_equiv _ _ a (e '' a) e _, 
  { refine (equiv.trans _ this).trans _,  
    { symmetry, 
      have := @equiv.subtype_subtype_equiv_subtype α s (coe '' a),   },  }, 
  { rintro ⟨x, hx⟩, 
    refine ⟨λ h, ⟨⟨x,hx⟩, h, rfl⟩ , _⟩,
    rintro ⟨⟨y,hy⟩, hya, h⟩, 
    convert hya, 
    simpa using e.apply_eq_iff_eq.mp h.symm }, 
  -- refine (@equiv.subtype_subtype_equiv_subtype α s (coe '' a) sorry).symm.trans _,  
  -- apply @equiv.subtype_equiv (coe '' a : set α), 
end 
-- { to_fun := λ x,  
--     let (hx : (x : α) ∈ s) := mem_of_mem_of_subset x.prop (by simp : coe '' a ⊆ s) in 
--   ⟨e ⟨x, hx⟩, 
--     begin
--        refine ⟨e ⟨x, hx⟩, ⟨⟨x,hx⟩,_,rfl⟩, rfl⟩,    
--         obtain ⟨y,hy,hy'⟩ := x.prop, 
--         convert hy,   apply subtype.coe_injective,   
--         rw [hy'], 
--         refl, 
--     end⟩,
--   inv_fun := ,
--   left_inv := _,
--   right_inv := _ }

def restrict_iso' (i : M ≃i N) (R : set M.E) : 
  (M ‖ (coe '' R : set α)) ≃i (N ‖ (coe '' (i '' R) : set α)) := 
{ to_fun := by {},
  -- { to_fun := λ e, ⟨i ⟨e, by { apply mem_of_mem_of_subset e.2, simp } ⟩, 
  --               by { simp,  }⟩ ,
  -- inv_fun := _,
  -- left_inv := _,
  -- right_inv := _ } ,

  on_base := sorry }


def restrict_iso (i : M ≃i N) (R : set α) : 
  M ‖ R ≃i (N ‖ (coe '' (i '' (coe ⁻¹' R : set M.E)) : set α)) := 
begin
end 

end restrict 

section basis

lemma basis.transfer (hIX : M.basis I X) (hJX : M.basis J X) (hXY : X ⊆ Y) (hJY : M.basis J Y) : 
  M.basis I Y :=
begin
  rw [←restrict_base_iff], 
  exact (restrict_base_iff.mpr hJY).base_of_basis_supset hJX.subset (hIX.basis_restrict_of_subset hXY), 
end 

lemma basis.transfer' (hI : M.basis I X) (hJ : M.basis J Y) (hJX : J ⊆ X) (hIY : I ⊆ Y) : 
  M.basis I Y :=
begin
  have hI' := hI.basis_subset (subset_inter hI.subset hIY) (inter_subset_left _ _), 
  have hJ' := hJ.basis_subset (subset_inter hJX hJ.subset) (inter_subset_right _ _), 
  exact hI'.transfer hJ' (inter_subset_right _ _) hJ, 
end 

lemma basis.transfer'' (hI : M.basis I X) (hJ : M.basis J Y) (hJX : J ⊆ X) : M.basis I (I ∪ Y) :=
begin
  obtain ⟨J', hJ', hJJ'⟩  := hJ.indep.subset_basis_of_subset hJX, 
  have hJ'Y := (hJ.basis_union_of_subset hJ'.indep hJJ').basis_union hJ', 
  refine (hI.transfer' hJ'Y hJ'.subset _).basis_subset _ _,  
  { exact subset_union_of_subset_right hI.subset _ },
  { exact subset_union_left _ _ }, 
  refine union_subset (subset_union_of_subset_right hI.subset _) _,
  rw union_right_comm, 
  exact subset_union_right _ _, 
end 

lemma indep.exists_basis_subset_union_basis (hI : M.indep I) (hIX : I ⊆ X) (hJ : M.basis J X) : 
  ∃ I', M.basis I' X ∧ I ⊆ I' ∧ I' ⊆ I ∪ J :=
begin
  obtain ⟨I', hI', hII', hI'IJ⟩ := 
    (hI.indep_restrict_of_subset hIX).exists_base_subset_union_base (basis.base_restrict hJ), 
  exact ⟨I', restrict_base_iff.mp hI', hII', hI'IJ⟩, 
end 

lemma indep.exists_insert_of_not_basis (hI : M.indep I) (hIX : I ⊆ X) (hI' : ¬M.basis I X) 
(hJ : M.basis J X) : 
  ∃ e ∈ J \ I, M.indep (insert e I) :=
begin
  rw [←restrict_base_iff] at hI', rw [←restrict_base_iff] at hJ, -- hJ, 
  obtain ⟨e, he, hi⟩ := (hI.indep_restrict_of_subset hIX).exists_insert_of_not_base hI' hJ, 
  exact ⟨e, he, (restrict_indep_iff.mp hi).1⟩,
end 

lemma basis.base_of_base_subset (hIX : M.basis I X) (hB : M.base B) (hBX : B ⊆ X) : M.base I :=
hB.base_of_basis_supset hBX hIX

lemma basis.exchange (hIX : M.basis I X) (hJX : M.basis J X) (he : e ∈ I \ J) : 
  ∃ f ∈ J \ I, M.basis (insert f (I \ {e})) X :=
by { simp_rw ←restrict_base_iff at *, exact hIX.exchange hJX he }

lemma basis.eq_exchange_of_diff_eq_singleton (hI : M.basis I X) (hJ : M.basis J X) 
(hIJ : I \ J = {e}) : 
  ∃ f ∈ J \ I, J = (insert f I) \ {e} :=
by { rw [←restrict_base_iff] at hI hJ, exact hI.eq_exchange_of_diff_eq_singleton hJ hIJ }

end basis

section finite

lemma basis.card_eq_card_of_basis (hIX : M.basis I X) (hJX : M.basis J X) : I.ncard = J.ncard :=
by { rw [←restrict_base_iff] at hIX hJX, exact hIX.card_eq_card_of_base hJX }

lemma basis.finite_of_finite (hIX : M.basis I X) (hI : I.finite) (hJX : M.basis J X) : J.finite := 
by { rw [←restrict_base_iff] at hIX hJX, exact hIX.finite_of_finite hI hJX }

lemma basis.infinite_of_infinite (hIX : M.basis I X) (hI : I.infinite) (hJX : M.basis J X) : 
  J.infinite := 
by { rw [←restrict_base_iff] at hIX hJX, exact hIX.infinite_of_infinite hI hJX }

lemma basis.card_diff_comm (hI : M.basis I X) (hJ : M.basis J X) : (I \ J).ncard = (J \ I).ncard :=
by { rw [←restrict_base_iff] at hI hJ, rw hJ.card_diff_comm hI }

lemma basis.diff_finite_comm (hIX : M.basis I X) (hJX : M.basis J X) :
  (I \ J).finite ↔ (J \ I).finite := 
by { rw [←restrict_base_iff] at hIX hJX, exact hIX.diff_finite_comm hJX }

lemma basis.diff_infinite_comm (hIX : M.basis I X) (hJX : M.basis J X) :
  (I \ J).infinite ↔ (J \ I).infinite := 
by { rw [←restrict_base_iff] at hIX hJX, exact hIX.diff_infinite_comm hJX }

lemma indep.augment_of_finite (hI : M.indep I) (hJ : M.indep J) (hIfin : I.finite) 
(hIJ : I.ncard < J.ncard) :
  ∃ x ∈ J, x ∉ I ∧ M.indep (insert x I) :=
begin
  obtain ⟨K, hK, hIK⟩ :=  
    (hI.indep_restrict_of_subset (subset_union_left I J)).exists_base_supset, 
  obtain ⟨K', hK', hJK'⟩ :=
    (hJ.indep_restrict_of_subset (subset_union_right I J)).exists_base_supset, 
  have hJfin := finite_of_ncard_pos ((nat.zero_le _).trans_lt hIJ), 
  rw restrict_base_iff at hK hK', 
  have hK'fin := (hIfin.union hJfin).subset hK'.subset, 
  have hlt := 
    hIJ.trans_le ((ncard_le_of_subset hJK' hK'fin).trans_eq (hK'.card_eq_card_of_basis hK)), 
  obtain ⟨e,he⟩ := exists_mem_not_mem_of_ncard_lt_ncard hlt hIfin, 
  exact ⟨e, (hK.subset he.1).elim (false.elim ∘ he.2) id, 
    he.2, hK.indep.subset (insert_subset.mpr ⟨he.1,hIK⟩)⟩, 
end 

/-- The independence augmentation axiom; given independent sets `I,J` with `I` smaller than `J`, 
  there is an element `e` of `J \ I` whose insertion into `e` gives an independent set.  -/
lemma indep.augment [finite_rk M] (hI : M.indep I) (hJ : M.indep J) (hIJ : I.ncard < J.ncard) :
  ∃ x ∈ J, x ∉ I ∧ M.indep (insert x I) :=
hI.augment_of_finite hJ hI.finite hIJ

/-- The independence augmentation axiom in a form that finds a strict superset -/
lemma indep.ssubset_indep_of_card_lt_of_finite (hI : M.indep I) (hI_fin : I.finite) (hJ : M.indep J) 
(hIJ : I.ncard < J.ncard) :
  ∃ I', M.indep I' ∧ I ⊂ I' ∧ I' ⊆ I ∪ J :=
begin
  obtain ⟨e, heJ, heI, hI'⟩ := hI.augment_of_finite hJ hI_fin hIJ ,
  exact ⟨_, hI', ssubset_insert heI, insert_subset.mpr ⟨or.inr heJ,subset_union_left _ _⟩⟩,
end

lemma indep.ssubset_indep_of_card_lt [finite_rk M] (hI : M.indep I) (hJ : M.indep J) 
(hIJ : I.ncard < J.ncard) :
  ∃ I', M.indep I' ∧ I ⊂ I' ∧ I' ⊆ I ∪ J :=
hI.ssubset_indep_of_card_lt_of_finite hI.finite hJ hIJ

lemma indep.le_card_basis [finite_rk M] (hI : M.indep I) (hIX : I ⊆ X) (hJX : M.basis J X) :
  I.ncard ≤ J.ncard :=
begin
  refine le_of_not_lt (λ hlt, _),
  obtain ⟨I', hI'⟩ := hJX.indep.ssubset_indep_of_card_lt hI hlt,
  have := hJX.eq_of_subset_indep hI'.1 hI'.2.1.subset (hI'.2.2.trans (union_subset hJX.subset hIX)),
  subst this,
  exact hI'.2.1.ne rfl,
end

end finite 

end matroid_in 

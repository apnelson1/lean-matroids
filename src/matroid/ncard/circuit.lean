import .rank

noncomputable theory
open_locale classical

variables {E : Type*} [finite E] {M M₁ M₂ : matroid E} 
  {I C C' C₁ C₂ X : set E} {e : E}

open set 

namespace matroid 

lemma circuit_def : 
  M.circuit C ↔ ¬M.indep C ∧ ∀ I ⊂ C, M.indep I :=
iff.rfl 

lemma circuit.dep (hC : M.circuit C) : 
  ¬M.indep C := 
hC.1 

lemma circuit.indep_of_ssubset (hC : M.circuit C) (hXC : X ⊂ C) :
  M.indep X := 
hC.2 _ hXC

lemma circuit.eq_of_dep_subset (hC : M.circuit C) (hX : ¬M.indep X) (hXC : X ⊆ C) :
  X = C :=
eq_of_le_of_not_lt hXC (hX ∘ hC.indep_of_ssubset) 

lemma circuit.not_ssubset (hC : M.circuit C) (hC' : M.circuit C') : 
  ¬ (C' ⊂ C) :=
λ h, hC'.1 (hC.2 _ h)

lemma circuit.nonempty (hC : M.circuit C) : 
  C.nonempty := 
by {rw set.nonempty_iff_ne_empty, rintro rfl, exact hC.1 M.empty_indep}

lemma circuit.card_eq (hC : M.circuit C) : 
  C.ncard = M.r C + 1 :=
begin
  obtain ⟨e,he⟩ := hC.nonempty, 
  have hss : C \ {e} ⊂ C, by {refine ssubset_of_ne_of_subset _ (diff_subset _ _), 
    simpa only [ne.def, sdiff_eq_left, disjoint_singleton_right, not_not_mem]},   
  have hlb := M.r_mono hss.subset, 
  have hub := r_lt_card_of_dep hC.dep, 
  rw [←nat.add_one_le_iff] at hub, 
  rw [(hC.indep_of_ssubset hss).r] at hlb, 
  have := ncard_diff_singleton_add_one he, 
  linarith, 
end 

lemma circuit.coe_r_eq (hC : M.circuit C) : 
  (M.r C : ℤ) = C.ncard - 1 :=
by rw [hC.card_eq, nat.cast_add, nat.cast_one, add_tsub_cancel_right]

lemma circuit.eq_of_dep_subset_self (hC : M.circuit C) (hX : ¬M.indep X) (hXC : X ⊆ C) : 
  C = X :=
by_contra (λ h, hX (hC.indep_of_ssubset (ssubset_of_subset_of_ne hXC (ne.symm h))))

lemma circuit.eq_of_subset_circuit (hC₁ : M.circuit C₁) (hC₂ : M.circuit C₂) (h : C₁ ⊆ C₂) : 
  C₁ = C₂ :=
(hC₂.eq_of_dep_subset_self hC₁.dep h).symm

lemma exists_circuit_subset_of_dep (hX : ¬M.indep X) : 
  ∃ C ⊆ X, M.circuit C :=
begin
  obtain ⟨C,⟨hCX,hCdep⟩,hmin⟩ := finite.exists_minimal (λ Y, Y ⊆ X ∧ ¬M.indep Y) ⟨_,rfl.subset,hX⟩,
  exact ⟨C, hCX, ⟨hCdep,λ I hIC, 
    by_contra (λ hI, hIC.ne ((hmin I ⟨hIC.subset.trans hCX,hI⟩ hIC.subset).symm))⟩⟩,  
end   
  
lemma dep_iff_supset_circuit :
  ¬ M.indep X ↔ ∃ C ⊆ X, M.circuit C  :=
⟨exists_circuit_subset_of_dep, λ ⟨C, hCX, hC⟩ hX, hC.dep (hX.subset hCX)⟩

lemma indep_iff_forall_subset_not_circuit : 
  M.indep I ↔ ∀ C ⊆ I, ¬ M.circuit C := 
by {rw ← not_iff_not, simp_rw [dep_iff_supset_circuit, not_forall, not_not]}

lemma exists_circuit_iff_card_lt_rk : 
  M.rk < (univ : set E).ncard ↔ ∃ C, M.circuit C :=
begin
  rw [matroid.rk, r_lt_card_iff_dep, dep_iff_supset_circuit], 
  split, 
  { rintro ⟨C,-,hC⟩, exact ⟨C,hC⟩},
  rintro ⟨C,hC⟩, 
  exact ⟨C, subset_univ _, hC⟩
end 

/-- The circuit eliminiation axiom : for any pair of distinct circuits `C₁,C₂` and any `e`, some 
  circuit is contained in `C₁ ∪ C₂ \ {e}`. Traditionally this includes the stipulation that 
  `e ∈ C₁ ∩ C₂`, but we can derive the stronger version. -/
lemma circuit.elimination (hC₁ : M.circuit C₁) (hC₂ : M.circuit C₂) (h : C₁ ≠ C₂) (e : E) : 
  ∃ C ⊆ (C₁ ∪ C₂) \ {e}, M.circuit C  :=
begin
  by_cases he : e ∈ (C₁ ∪ C₂), swap, 
  { have h' := subset_union_left C₁ C₂, 
    exact ⟨C₁, subset_diff_singleton h' (λ he', he (h' he')), hC₁⟩},
  simp_rw [←dep_iff_supset_circuit, ←r_lt_card_iff_dep, nat.lt_iff_add_one_le], 
  
  have hss : C₁ ∩ C₂ ⊂ C₁ := ssubset_of_ne_of_subset 
    (by {simp only [ne.def, inter_eq_left_iff_subset], 
      exact λ h', h (hC₁.eq_of_subset_circuit hC₂ h')}) (inter_subset_left _ _),  
  linarith [hC₁.card_eq, hC₂.card_eq, ncard_inter_add_ncard_union C₁ C₂, 
      (hC₁.indep_of_ssubset hss).r, M.r_inter_add_r_union_le_r_add_r C₁ C₂, 
      ncard_diff_singleton_add_one he, 
      M.r_mono (diff_subset (C₁ ∪ C₂) {e})], 
end 

lemma set.mem_of_nsubset_insert_iff {s t : set E} {a : E} (h : s ⊆ insert a t ∧ ¬ s ⊆ t) : a ∈ s :=
begin
  contrapose h,
  push_neg,
  intros h2,
  exact (subset_insert_iff_of_not_mem h).1 h2,
end

lemma indep.unique_circuit_of_insert (hX : M.indep X) (a : E) (hXa : ¬ M.indep (insert a X) ): 
  ∃! (C ⊆ insert a X), M.circuit C ∧ a ∈ C :=
begin
  apply exists_unique_of_exists_of_unique, 
  { simp only [union_singleton, exists_unique_iff_exists, exists_prop],  
    refine (dep_iff_supset_circuit.mp hXa).imp (λ C, _), 
    rintro ⟨hCX,hC⟩,
    refine ⟨hCX ,hC, by_contra (λ haC, _)⟩, 
    exact hC.dep (hX.subset ((subset_insert_iff_of_not_mem haC).mp hCX))}, 
  simp only [exists_unique_iff_exists, exists_prop, and_imp], 
  refine λ  C₁ C₂ hC₁X hC₁ haC₁ hC₂X hC₂ haC₂, by_contra (λ hne, _), 
  obtain ⟨C,hCss,hC⟩ := hC₁.elimination hC₂ hne a,  
  have h := hCss.trans (@diff_subset_diff_left _ _ _ {a} (union_subset hC₁X hC₂X)), 
  simp only [insert_diff_of_mem, mem_singleton] at h, 
  refine hC.dep (hX.subset (h.trans (diff_subset _ _))), 
end

-- trying to make alternate basis exchange axiom (B2)*

end matroid
  
section from_axioms

/-- A collection of sets satisfying the circuit axioms determines a matroid -/
def matroid_of_circuit 
  (circuit : set E → Prop) 
  (empty_not_circuit : ¬ circuit ∅)
  (antichain : ∀ C₁ C₂, circuit C₁ → circuit C₂ → C₁ ⊆ C₂ → C₁ = C₂)
  (elimination : ∀ C₁ C₂ e, C₁ ≠ C₂ → e ∈ C₁ ∩ C₂ → ∃ C ⊆ (C₁ ∪ C₂) \ {e}, circuit C) :
matroid E :=
matroid_of_indep (λ I, ∀ C ⊆ I, ¬circuit C) ⟨∅, λ C hC, (by rwa subset_empty_iff.mp hC)⟩ 
(λ I J hIJ hJ C hCI, hJ C (hCI.trans hIJ)) 
begin
  by_contra' h, 
  obtain ⟨I,J,hI,hJ,hIJ,Hbad⟩ := h, 
  set indep := (λ I, ∀ C ⊆ I, ¬circuit C) with hi,
  
  /- Choose an independent set `K ⊆ I ∪ J`, larger than `I`, for which `I \ K` is minimized -/
  set sbad := {K : set E | indep K ∧ K ⊆ I ∪ J ∧ I.ncard < K.ncard} with hsbad, 
  have hbad_ne : sbad.nonempty := ⟨J, hJ, subset_union_right _ _, hIJ⟩,  
  obtain ⟨K, ⟨hK, hKIJ, hIK⟩, hKmin⟩ := 
    @set.finite.exists_minimal_wrt (set E) _ _ (λ X, (I \ X).ncard) sbad (to_finite sbad) hbad_ne, 
  simp only [hsbad, mem_set_of_eq, and_imp] at hKmin, 
  
  obtain hIK_empty | ⟨e, heI, heK⟩ := (I \ K).eq_empty_or_nonempty,
  /- If `I \ K` is empty then we get an easy contradiction by augmenting `I` into `K`. -/
  { obtain ⟨e,heK,heI⟩ := exists_mem_not_mem_of_ncard_lt_ncard hIK, 
    have heJ : e ∈ J := by_contra (λ heJ, not_or heI heJ (hKIJ heK)), 
    obtain ⟨C, hCeI, hC⟩ := Hbad e heJ heI, 
    exact hK C (hCeI.trans (insert_subset.mpr ⟨heK, diff_eq_empty.mp hIK_empty⟩)) hC}, 
  
  have hCf : ∀ f ∈ K \ I, ∃ Cf ⊆ (insert e K), circuit Cf ∧ f ∉ Cf ∧ e ∈ Cf, 
  { rintro f ⟨hfK,hfI⟩,  
    have hef : e ≠ f, from λ h, hfI (h ▸heI ), 
    set T := ((insert e K) \ {f}) with hT, 
    have hTIJ : T ⊆ I ∪ J, from 
      ((diff_subset _ _).trans (insert_subset.mpr ⟨or.inl heI,hKIJ⟩)),  
    have hTcard : T.ncard = K.ncard, by rw [hT, ncard_exchange' heK hfK], 
    have hITcard : (I \ T).ncard < (I \ K).ncard, 
    { rw [nat.lt_iff_add_one_le, hT, ←insert_diff_singleton_comm hef, ←union_singleton, ←diff_diff, 
        ncard_diff_singleton_add_one ], 
      { convert rfl.le using 2,
        rw [diff_eq_compl_inter, diff_eq_compl_inter, diff_eq_compl_inter, compl_inter, 
          inter_distrib_right, compl_compl, singleton_inter_eq_empty.mpr hfI, empty_union]},
      exact ⟨heI,λ he', heK he'.1⟩},

    have hTi : ¬indep T, from 
      λ hTi, hITcard.ne (hKmin _ hTi hTIJ (hIK.trans_eq hTcard.symm) hITcard.le).symm,

    push_neg at hTi, 
    obtain ⟨Cf, hCfT, hCf⟩ := hTi, 
    refine ⟨Cf, hCfT.trans (diff_subset _ _), hCf, _, _⟩, 
    { exact mt (@hCfT f) (not_mem_diff_of_mem (mem_singleton f))}, 
    
    refine by_contra (λ heCf, hK Cf (λ x hxCf, _) hCf),  
    
    exact mem_of_mem_insert_of_ne (hCfT hxCf).1 (by {rintro rfl, exact heCf hxCf})},
  
  obtain ⟨g,hgK,hgI⟩ := exists_mem_not_mem_of_ncard_lt_ncard hIK,  
  obtain ⟨Cg, hCgss, hCg, hgCg, heCg⟩ := hCf g ⟨hgK,hgI⟩,      

  have hg_ex : ∃ g', g' ∈ Cg ∧ g' ∈ K \ I, 
  { by_contra' hg', 
    exact hI _ (λ x hx, 
      or.elim (hCgss hx) (λ h, h.symm ▸ heI) (λ hxK, by_contra (λ hxI, hg' _ hx ⟨hxK, hxI⟩))) hCg},
  obtain ⟨g', hg', hg'KI⟩ := hg_ex,   

  obtain ⟨Cg', hCg'ss, hCg', hgCg', heCg'⟩ := hCf g' hg'KI,  
  have hne : Cg ≠ Cg', 
  { intro heq, rw ←heq at hgCg', exact hgCg' hg', }, 
  obtain ⟨C, hCss, hC⟩ := elimination Cg Cg' e hne ⟨heCg, heCg'⟩, 
  refine hK C (hCss.trans _) hC, 
  rw [diff_subset_iff, singleton_union], 
  exact union_subset hCgss hCg'ss, 
end 

@[simp] lemma matroid_of_circuit_apply 
  (circuit : set E → Prop) 
  (empty_not_circuit : ¬ circuit ∅)
  (antichain : ∀ C₁ C₂, circuit C₁ → circuit C₂ → C₁ ⊆ C₂ → C₁ = C₂)
  (elimination : ∀ C₁ C₂ e, C₁ ≠ C₂ → e ∈ C₁ ∩ C₂ → ∃ C ⊆ (C₁ ∪ C₂) \ {e}, circuit C) :
(matroid_of_circuit circuit empty_not_circuit antichain elimination).circuit = circuit :=
begin
  ext C, 
  simp_rw [matroid_of_circuit, matroid.circuit_def, matroid_of_indep_apply, not_forall, not_not, 
    exists_prop], 
  refine ⟨λ h, _,λ h, ⟨⟨_,rfl.subset, h⟩,λ I hIC C' hC'I hC', 
    hIC.not_subset ((antichain C' C hC' h (hC'I.trans hIC.subset)) ▸ hC'I )⟩⟩, 
  obtain ⟨⟨C₀,hC₀C, hC₀⟩,hI⟩ := h,  
  obtain rfl | hC₀C := eq_or_ssubset_of_subset hC₀C, 
    assumption, 
  exact (hI _ hC₀C _ rfl.subset hC₀).elim,
end 

end from_axioms   


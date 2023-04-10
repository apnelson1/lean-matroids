import .rank

noncomputable theory
open_locale classical

variables {E : Type*} {M M₁ M₂ : matroid E} [matroid.finite_rk M]
  {I C C' C₁ C₂ X : set E} {e : E}

open set

namespace matroid

lemma circuit_def : M.circuit C ↔ ¬M.indep C ∧ ∀ I ⊂ C, M.indep I := iff.rfl

lemma circuit.dep (hC : M.circuit C) : ¬M.indep C := hC.1

lemma circuit.ssubset_indep (hC : M.circuit C) (hXC : X ⊂ C) : M.indep X := hC.2 _ hXC

lemma circuit.diff_singleton_indep (hC : M.circuit C) (he : e ∈ C) : M.indep (C \ {e}) :=
hC.ssubset_indep (diff_singleton_ssubset.2 he)

lemma circuit.eq_of_dep_subset (hC : M.circuit C) (hX : ¬M.indep X) (hXC : X ⊆ C) : X = C :=
eq_of_le_of_not_lt hXC (hX ∘ hC.ssubset_indep)

lemma circuit.not_ssubset (hC : M.circuit C) (hC' : M.circuit C') : ¬ (C' ⊂ C) :=
λ h, hC'.1 (hC.2 _ h)

lemma circuit.nonempty (hC : M.circuit C) : C.nonempty :=
by {rw set.nonempty_iff_ne_empty, rintro rfl, exact hC.1 M.empty_indep}

lemma empty_not_circuit (M : matroid E) [finite_rk M] : ¬M.circuit ∅ :=
λ h, by simpa using h.nonempty

lemma circuit.finite [finite_rk M] (hC : M.circuit C) : C.finite := 
begin
  obtain ⟨e, he⟩ := hC.nonempty, 
  have hfin := (hC.diff_singleton_indep he).finite.union (to_finite {e}), 
  rwa [diff_union_self, union_singleton, insert_eq_of_mem he] at hfin, 
end 

lemma circuit.card (hC : M.circuit C) : C.ncard = M.r C + 1 :=
begin
  obtain ⟨e,he⟩ := hC.nonempty,
  have hss : C \ {e} ⊂ C, by {refine ssubset_of_ne_of_subset _ (diff_subset _ _),
    simpa only [ne.def, sdiff_eq_left, disjoint_singleton_right, not_not_mem]},
  have hlb := M.r_mono hss.subset,
  rw [(hC.ssubset_indep hss).r] at hlb,
  linarith [ncard_diff_singleton_add_one he hC.finite, r_lt_card_of_dep_of_finite hC.finite hC.dep],
end

lemma circuit_iff_dep_forall_diff_singleton_indep :
  M.circuit C ↔ (¬M.indep C) ∧ ∀ e ∈ C, M.indep (C \ {e}) :=
begin
  rw [circuit_def, and.congr_right_iff],
  refine λ hdep, ⟨λ h e heC, (h _ $ diff_singleton_ssubset.2 heC), λ h I hIC, _⟩,
  obtain ⟨e, heC,heI⟩ := exists_of_ssubset hIC,
  exact (h e heC).subset (subset_diff_singleton hIC.subset heI),
end

lemma circuit.r (hC : M.circuit C) : M.r C = C.ncard - 1 :=
by rw [hC.card, nat.add_succ_sub_one, add_zero]

lemma circuit.coe_r_eq (hC : M.circuit C) : (M.r C : ℤ) = C.ncard - 1 :=
by rw [hC.card, nat.cast_add, nat.cast_one, add_tsub_cancel_right]

lemma circuit.eq_of_dep_subset_self (hC : M.circuit C) (hX : ¬M.indep X) (hXC : X ⊆ C) : C = X :=
by_contra (λ h, hX (hC.ssubset_indep (ssubset_of_subset_of_ne hXC (ne.symm h))))

lemma circuit.eq_of_subset_circuit (hC₁ : M.circuit C₁) (hC₂ : M.circuit C₂) (h : C₁ ⊆ C₂) :
  C₁ = C₂ :=
(hC₂.eq_of_dep_subset_self hC₁.dep h).symm

lemma exists_circuit_subset_of_dep (hX : ¬M.indep X) : ∃ C ⊆ X, M.circuit C :=
begin
  obtain ⟨I, hI⟩ := M.exists_basis X, 
  have hIX : I ⊂ X := hI.subset.ssubset_of_ne (by { rintro rfl, exact hX hI.indep }),
  obtain ⟨e,heX, heI⟩ := exists_of_ssubset hIX, 
  obtain ⟨C, hCeI, hC, hmin⟩ := @set.finite.exists_minimal_subset _ _ 
    (λ D, ¬ M.indep D) (hI.finite.insert e) 
    (hI.dep_of_ssubset (ssubset_insert heI) (insert_subset.mpr ⟨heX, hIX.subset⟩)), 
  simp only [not_not] at hmin, 
  exact ⟨C,hCeI.trans (insert_subset.mpr ⟨heX, hIX.subset⟩), hC, hmin⟩, 
end

lemma dep_iff_supset_circuit : ¬ M.indep X ↔ ∃ C ⊆ X, M.circuit C  :=
⟨exists_circuit_subset_of_dep, λ ⟨C, hCX, hC⟩ hX, hC.dep (hX.subset hCX)⟩

lemma indep_iff_forall_subset_not_circuit : M.indep I ↔ ∀ C ⊆ I, ¬ M.circuit C :=
by {rw ← not_iff_not, simp_rw [dep_iff_supset_circuit, not_forall, not_not]}

lemma exists_circuit_iff_card_lt_rk [finite E] : M.rk < (univ : set E).ncard ↔ ∃ C, M.circuit C :=
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
  rw [←dep_iff_supset_circuit, ←r_lt_card_iff_dep_of_finite _, nat.lt_iff_add_one_le],
  swap, apply_instance, swap, exact (hC₁.finite.union hC₂.finite).diff _, 

  have hss : C₁ ∩ C₂ ⊂ C₁ := ssubset_of_ne_of_subset
    (by {simp only [ne.def, inter_eq_left_iff_subset],
      exact λ h', h (hC₁.eq_of_subset_circuit hC₂ h')}) (inter_subset_left _ _),
  
  linarith [hC₁.card, hC₂.card, ncard_inter_add_ncard_union C₁ C₂ hC₁.finite hC₂.finite,
    (hC₁.ssubset_indep hss).r, M.r_inter_add_r_union_le_r_add_r C₁ C₂,
    ncard_diff_singleton_add_one he (hC₁.finite.union hC₂.finite),     
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
  ∃! C, C ⊆ insert a X ∧ M.circuit C ∧ a ∈ C :=
begin
  apply exists_unique_of_exists_of_unique,
  { refine (dep_iff_supset_circuit.mp hXa).imp (λ C, _),
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

end matroid

section from_axioms

/-- A collection of sets satisfying the circuit axioms determines a matroid -/
def matroid_of_circuit [finite E] (circuit : set E → Prop) (empty_not_circuit : ¬ circuit ∅)
  (antichain : ∀ C₁ C₂, circuit C₁ → circuit C₂ → C₁ ⊆ C₂ → C₁ = C₂)
  (elimination : ∀ C₁ C₂ e,
    circuit C₁ → circuit C₂ → C₁ ≠ C₂ → e ∈ C₁ ∩ C₂ → ∃ C ⊆ (C₁ ∪ C₂) \ {e}, circuit C) :
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
  obtain ⟨C, hCss, hC⟩ := elimination _ _ e hCg hCg' hne ⟨heCg, heCg'⟩,
  refine hK C (hCss.trans _) hC,
  rw [diff_subset_iff, singleton_union],
  exact union_subset hCgss hCg'ss,
end

@[simp] lemma matroid_of_circuit_apply [finite E] (circuit : set E → Prop)
  (empty_not_circuit : ¬ circuit ∅)
  (antichain : ∀ C₁ C₂, circuit C₁ → circuit C₂ → C₁ ⊆ C₂ → C₁ = C₂)
  (elimination : ∀ C₁ C₂ e,
    circuit C₁ → circuit C₂ → C₁ ≠ C₂ → e ∈ C₁ ∩ C₂ → ∃ C ⊆ (C₁ ∪ C₂) \ {e}, circuit C) :
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


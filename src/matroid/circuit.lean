import .flat
import mathlib.data.set.basic

noncomputable theory
open_locale classical

variables {E : Type*} {M M₁ M₂ : matroid E} 
  {I C C' C₁ C₂ X : set E} {e f : E}

open set

namespace matroid

lemma circuit_def : M.circuit C ↔ ¬M.indep C ∧ ∀ I ⊂ C, M.indep I := iff.rfl

lemma circuit.dep (hC : M.circuit C) : ¬M.indep C := hC.1

lemma circuit.ssubset_indep (hC : M.circuit C) (hXC : X ⊂ C) : M.indep X := hC.2 _ hXC

lemma circuit.diff_singleton_indep (hC : M.circuit C) (he : e ∈ C) : M.indep (C \ {e}) :=
hC.ssubset_indep (diff_singleton_ssubset.2 he)

lemma circuit.diff_singleton_basis (hC : M.circuit C) (he : e ∈ C) : M.basis (C \ {e}) C :=
begin
  refine (hC.diff_singleton_indep he).basis_of_forall_insert (diff_subset _ _) (λ f hf hI, _), 
  simp only [mem_diff, mem_singleton_iff, not_and, not_not] at hf, 
  have := hf.2 (hf.1), subst this, 
  rw [insert_diff_singleton, insert_eq_of_mem he] at hI, 
  exact hC.dep hI, 
end 

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

lemma circuit_iff_dep_forall_diff_singleton_indep :
  M.circuit C ↔ (¬M.indep C) ∧ ∀ e ∈ C, M.indep (C \ {e}) :=
begin
  rw [circuit_def, and.congr_right_iff],
  refine λ hdep, ⟨λ h e heC, (h _ $ diff_singleton_ssubset.2 heC), λ h I hIC, _⟩,
  obtain ⟨e, heC,heI⟩ := exists_of_ssubset hIC,
  exact (h e heC).subset (subset_diff_singleton hIC.subset heI),
end

lemma circuit.eq_of_dep_subset_self (hC : M.circuit C) (hX : ¬M.indep X) (hXC : X ⊆ C) : C = X :=
by_contra (λ h, hX (hC.ssubset_indep (ssubset_of_subset_of_ne hXC (ne.symm h))))

lemma circuit.eq_of_subset_circuit (hC₁ : M.circuit C₁) (hC₂ : M.circuit C₂) (h : C₁ ⊆ C₂) :
  C₁ = C₂ :=
(hC₂.eq_of_dep_subset_self hC₁.dep h).symm

lemma circuit.circuit_lrestrict_of_subset (hC : M.circuit C) (hCX : C ⊆ X) :
  (M.lrestrict X).circuit C :=
begin
  simp_rw [circuit, lrestrict_indep_iff, not_and],  
  exact ⟨λ h, (hC.dep h).elim, λ I hIC, ⟨hC.ssubset_indep hIC, hIC.subset.trans hCX⟩⟩, 
end 

/-- Every dependent set contains a circuit. This could likely be a shorter proof -/
lemma exists_circuit_subset_of_dep (hX : ¬M.indep X) : ∃ C ⊆ X, M.circuit C :=
begin
  obtain ⟨I, hI⟩ := M.exists_basis X, 
  obtain (rfl | hss) := (ssubset_or_eq_of_subset hI.subset).symm,
  { exact (hX hI.indep).elim },
  obtain ⟨z,hzX, hzI⟩ := exists_of_ssubset hss, 
  set Is : set (set E) := {J | J ⊆ I ∧ z ∈ M.cl J} with hIs, 
  have hui : ⋃₀ Is ⊆ I := (sUnion_subset (λ J, and.left)), 
  have hu : M.indep (⋃₀ Is) := hI.indep.subset hui,
  have hIz : I ∈ Is, from ⟨subset.rfl, hI.subset_cl hzX⟩, 
  have hiI := sInter_subset_of_mem hIz, 
  have hcl := bInter_cl_eq_cl_bInter_of_sUnion_indep _ hu,
  refine ⟨insert z (⋂₀ Is), insert_subset.mpr ⟨hzX, (hiI).trans hI.subset⟩, 
    λ hind, hzI (hiI _), λ J hJ, _⟩,  
  { suffices : z ∈ M.cl (⋂₀ Is), 
    { rw indep.mem_cl_iff (hI.indep.subset (hiI)) at this, 
      exact this hind },
      simp_rw [sInter_eq_bInter, ←hcl, mem_Inter], 
      exact λ i, and.right },
  
  have hJ' : J \ (⋂₀ Is) ⊆ {z},  
  { have hJ' := hJ.subset, rwa [←union_singleton, ←diff_subset_iff ] at hJ' },
  by_contra h_dep_J, apply h_dep_J, 
  rw [←inter_union_diff J (⋂₀ Is)], 
  have hiJ : M.indep (J ∩ ⋂₀ Is), from hI.indep.subset ((inter_subset_right _ _).trans (hiI)), 
  have hzJ : z ∉ (J ∩ ⋂₀ Is), from not_mem_subset ((inter_subset_right _ _).trans (hiI)) hzI,
  obtain (h0 | h1) := subset_singleton_iff_eq.mp hJ', 
  { rw [h0, union_empty], exact hiJ },
  rw [h1, union_singleton, hiJ.insert_indep_iff_of_not_mem hzJ], 
     
  intro hcl', 
  have hJIs : J ∩ ⋂₀ Is ∈ Is, from ⟨(inter_subset_right _ _).trans (hiI), hcl'⟩, 

  obtain ⟨y,(rfl | hy), hyJ⟩ := exists_of_ssubset hJ,  
  { exact hyJ (h1.symm.subset (mem_singleton y)).1 },
  exact hyJ (sInter_subset_of_mem hJIs hy).1, 
end

lemma dep_iff_supset_circuit : ¬ M.indep X ↔ ∃ C ⊆ X, M.circuit C  :=
⟨exists_circuit_subset_of_dep, λ ⟨C, hCX, hC⟩ hX, hC.dep (hX.subset hCX)⟩

lemma indep_iff_forall_subset_not_circuit : M.indep I ↔ ∀ C ⊆ I, ¬ M.circuit C :=
by {rw ← not_iff_not, simp_rw [dep_iff_supset_circuit, not_forall, not_not]}


lemma circuit.subset_cl_diff_singleton (hC : M.circuit C) (e : E) :
  C ⊆ M.cl (C \ {e}) :=
begin
  by_cases he : e ∈ C, 
  { rw [(hC.diff_singleton_basis he).cl], exact subset_cl _ _ }, 
  rw [diff_singleton_eq_self he], exact subset_cl _ _, 
end


lemma indep.unique_circuit_of_insert (hI : M.indep I) (a : E) (hXa : ¬ M.indep (insert a I) ):
  ∃! C, C ⊆ insert a I ∧ M.circuit C ∧ a ∈ C :=
begin
  apply exists_unique_of_exists_of_unique,
  { refine (dep_iff_supset_circuit.mp hXa).imp (λ C, _),
    rintro ⟨hCX,hC⟩,
    refine ⟨hCX ,hC, by_contra (λ haC, _)⟩,
    exact hC.dep (hI.subset ((subset_insert_iff_of_not_mem haC).mp hCX))},
  
  simp only [exists_unique_iff_exists, exists_prop, and_imp],
  refine λ  C₁ C₂ hC₁I hC₁ haC₁ hC₂I hC₂ haC₂, _,
  rw [←singleton_union, ←diff_subset_iff] at hC₁I hC₂I, 
  have hcl : a ∈ M.cl (C₁ \ {a}) ∩ M.cl (C₂ \ {a}), 
    from ⟨ hC₁.subset_cl_diff_singleton a haC₁, hC₂.subset_cl_diff_singleton a haC₂⟩, 
  have hi := (hI.subset (union_subset hC₁I hC₂I)), 
  have hii : M.indep ((C₁ \ {a}) ∩ (C₂ \ {a})), sorry, 
  rw [inter_cl_eq_cl_inter_of_union_indep hi, hii.mem_cl_iff] at hcl,  
  simp only [mem_inter_iff, not_mem_diff_singleton, and_self] at hcl, 
  rw [insert_inter_distrib] at hcl, simp only [insert_diff_singleton] at hcl, 

  


  -- obtain ⟨C,hCss,hC⟩ := hC₁.elimination hC₂ hne a,
  -- have h := hCss.trans (@diff_subset_diff_left _ _ _ {a} (union_subset hC₁X hC₂X)),
  -- simp only [insert_diff_of_mem, mem_singleton] at h,
  -- refine hC.dep (hX.subset (h.trans (diff_subset _ _))),
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

lemma flat_iff_forall_circuit {F : set E} :
  M.flat F ↔ ∀ C e, M.circuit C → e ∈ C → C \ {e} ⊆ F → e ∈ F :=
begin
  rw [flat_iff_cl_self],
  refine ⟨λ h C e hC heC hCF , _, λ h, (M.subset_cl _).antisymm' (λ e heF, _) ⟩,
  { rw ←h, exact (hC.subset_cl_diff_singleton e).trans (M.cl_mono hCF) heC},
  exact (mem_cl_iff_exists_circuit.mp heF).elim id (λ ⟨C, hC, heC, hCF⟩, h _ _ hC heC hCF),
end

/-- A generalization of the strong circuit elimination axiom. For finite matroids, this is 
  equivalent to the case where `ι` is a singleton type, which is the usual two-circuit version. 
  The stronger version is required for axiomatizing infinite matroids via circuits. -/
lemma circuit.strong_multi_elimination {ι : Type*} (hC : M.circuit C) (x : ι → E) (Cs : ι → set E) 
(hCs : ∀ i, M.circuit (Cs i)) (h_mem : ∀ i, (x i) ∈ C ∩ (Cs i)) 
(h_unique : ∀ i i', x i ∈ Cs i' → i = i') {z : E} (hz : z ∈ C \ ⋃ i, Cs i) :
  ∃ C', M.circuit C' ∧ z ∈ C' ∧ C' ⊆ (C ∪ ⋃ i, (Cs i)) \ range x :=
begin
  set Y := (C ∪ ⋃ x, Cs x) \ (insert z (range x)) with hY, 
  have h₁ : range x ⊆ M.cl (⋃ i, ((Cs i) \ {x i} \ (insert z (range x)))), 
  { rintro e ⟨i, rfl⟩,  
    have h' := (hCs i).subset_cl_diff_singleton (x i) (h_mem i).2, 
    refine mem_of_mem_of_subset h' (M.cl_subset_cl_of_subset _), 
    refine subset_Union_of_subset i (subset_diff.mpr ⟨rfl.subset,_⟩), 
    rw disjoint_iff_forall_ne, 
    rintro y hy z (rfl | ⟨j, rfl⟩) rfl, 
    { exact hz.2 (mem_Union_of_mem i hy.1) },
    refine hy.2 (mem_singleton_iff.mpr _), 
    rw h_unique _ _ hy.1 },
  have h₂ : range x ⊆ M.cl Y, 
  { refine h₁.trans (M.cl_subset_cl_of_subset (Union_subset (λ x, _))),  
    refine diff_subset_diff_left (subset_union_of_subset_right _ _),
    exact subset_Union_of_subset x (diff_subset _ _) },
  have h₃ : C \ {z} ⊆ M.cl Y, 
  { suffices : C \ {z} ⊆ (C \ insert z (range x)) ∪ (range x), 
    { rw [union_diff_distrib] at hY, 
      convert this.trans (union_subset_union ((subset_union_left _ _).trans_eq hY.symm) h₂), 
      rw union_eq_right_iff_subset.mpr (M.subset_cl _) },
    rw [←union_singleton, ←diff_diff, diff_subset_iff, singleton_union, ←insert_union, 
      insert_diff_singleton, ←singleton_union, union_assoc, diff_union_self], 
    exact subset_union_of_subset_right (subset_union_left _ _) _ },
  rw [←cl_subset_cl_iff_subset_cl] at h₃, 
  have h₄ := h₃ (hC.subset_cl_diff_singleton z hz.1), 
  obtain (hzY | ⟨C', hC', hzC', hCzY⟩) := mem_cl_iff_exists_circuit.mp h₄, 
  { exact ((hY.subset hzY).2 (mem_insert z _)).elim },
  
  refine ⟨C', hC', hzC', subset_diff.mpr ⟨_,_⟩⟩, 
  { exact (diff_singleton_subset_iff.mp hCzY).trans 
    (insert_subset.mpr ⟨or.inl hz.1,diff_subset _ _⟩) },
  rw [←insert_eq_of_mem hzC', ←@insert_diff_singleton _ z C', ←singleton_union, 
    disjoint_union_left, disjoint_singleton_left],
  refine ⟨not_mem_subset _ hz.2, disjoint_of_subset_left hCzY _⟩,   
  { rintro x' ⟨i,rfl⟩, exact mem_Union_of_mem i ((h_mem i).2) },
  exact disjoint_of_subset_right (subset_insert z _) disjoint_sdiff_left,  
end 

/-- The strong circuit elimination axiom. For any two circuits `C₁,C₂` and all `e ∈ C₁ ∩ C₂` and 
  `f ∈ C₁ \ C₂`, there is a circuit `C` with `f ∈ C ⊆ (C₁ ∪ C₂) \ {e}`. -/
lemma circuit.strong_elimination (hC₁ : M.circuit C₁) (hC₂ : M.circuit C₂) (he : e ∈ C₁ ∩ C₂) 
(hf : f ∈ C₁ \ C₂) : ∃ C ⊆ (C₁ ∪ C₂) \ {e}, M.circuit C ∧ f ∈ C :=
begin
  obtain ⟨C, hC, hfC, hCss⟩  := 
    @circuit.strong_multi_elimination E M C₁ unit hC₁ (λ _, e) (λ _, C₂) (by simpa) 
    (by simpa) (by simp) f (by simpa),   
  simp only [range_const, Union_const] at hCss, 
  exact ⟨C, hCss, hC, hfC⟩, 
end      

/-- The circuit eliminiation axiom : for any pair of distinct circuits `C₁,C₂` and any `e`, some
  circuit is contained in `C₁ ∪ C₂ \ {e}`. Traditionally this is stated with the assumption that 
  `e ∈ C₁ ∩ C₂`, but it is also true without it. -/
lemma circuit.elimination (hC₁ : M.circuit C₁) (hC₂ : M.circuit C₂) (h : C₁ ≠ C₂) (e : E) : 
  ∃ C ⊆ (C₁ ∪ C₂) \ {e}, M.circuit C :=
begin
  by_contra' h',
  have he : e ∈ C₁ ∩ C₂, 
  { by_contra he, 
    refine h' C₁ (by_contra (λ h₁, _)) hC₁,
    refine h' C₂ (by_contra (λ h₂, he _)) hC₂, 
    rw [subset_diff, not_and, disjoint_singleton_right, not_not_mem] at h₁ h₂, 
    exact ⟨h₁ (subset_union_left _ _), h₂ (subset_union_right _ _)⟩ },   
  have hf : (C₁ \ C₂).nonempty,
  { rw [nonempty_iff_ne_empty, ne.def, diff_eq_empty], 
    refine λ hss, h _, 
    exact (hC₁.eq_of_subset_circuit hC₂ hss)}, 
  obtain ⟨f, hf⟩ := hf, 
  obtain ⟨C, hCss, hC,-⟩ := hC₁.strong_elimination hC₂ he hf, 
  exact h' C hCss hC, 
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


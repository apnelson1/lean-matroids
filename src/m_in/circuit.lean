import .closure
import .restriction
import mathlib.data.set.basic
import data.nat.lattice 

noncomputable theory
open_locale classical

variables {α : Type*} {M M₁ M₂ : matroid_in α} 
  {I C C' C₁ C₂ X : set α} {e f : α}

open set

namespace matroid_in

lemma circuit.dep (hC : M.circuit C) : M.dep C := hC.1

@[ssE_finish_rules] lemma circuit.subset_ground (hC : M.circuit C) : C ⊆ M.E :=
hC.dep.subset_ground

lemma circuit.ssubset_indep (hC : M.circuit C) (hXC : X ⊂ C) : M.indep X := 
begin
  rw [← not_dep_iff (hXC.subset.trans hC.subset_ground)],
  rw [circuit, mem_minimals_set_of_iff] at hC, 
  exact λ h, hXC.ne.symm (hC.2 h hXC.subset),     
end 

lemma circuit_iff : M.circuit C ↔ M.dep C ∧ (∀ I, M.dep I → I ⊆ C → I = C) :=
by { rw [circuit, mem_minimals_set_of_iff], tauto }
  
lemma circuit_iff_forall_ssubset : M.circuit C ↔ M.dep C ∧ ∀ I ⊂ C, M.indep I := 
begin
  simp_rw [circuit_iff, ssubset_iff_subset_ne, and.congr_right_iff], 
  exact λ hC, ⟨λ h I hIC, indep_of_not_dep (hIC.2 ∘ (λ hD, h _ hD hIC.1)) 
    (hIC.1.trans hC.subset_ground), 
    λ h I hD hIC, by_contra (λ hne, hD.not_indep (h _ ⟨hIC, hne⟩))⟩,
end

lemma circuit.diff_singleton_indep (hC : M.circuit C) (he : e ∈ C) : M.indep (C \ {e}) :=
hC.ssubset_indep (diff_singleton_ssubset.2 he)

lemma circuit.diff_singleton_basis (hC : M.circuit C) (he : e ∈ C) : M.basis (C \ {e}) C :=
begin
  refine (hC.diff_singleton_indep he).basis_of_forall_insert (diff_subset _ _) (λ f hf hI, _),
  simp only [mem_diff, mem_singleton_iff, not_and, not_not] at hf, 
  have := hf.2 (hf.1), subst this, 
  rw [insert_diff_singleton, insert_eq_of_mem he] at hI, 
  exact hC.dep.not_indep hI, 
end 

lemma circuit_iff_mem_minimals : M.circuit C ↔ C ∈ minimals (⊆) {X | M.dep X} := iff.rfl 

lemma circuit.eq_of_dep_subset (hC : M.circuit C) (hX : M.dep X) (hXC : X ⊆ C) : X = C :=
eq_of_le_of_not_lt hXC (hX.not_indep ∘ hC.ssubset_indep)

lemma circuit.not_ssubset (hC : M.circuit C) (hC' : M.circuit C') : ¬ (C' ⊂ C) :=
λ h', h'.ne $ hC.eq_of_dep_subset hC'.dep h'.subset

lemma circuit.nonempty (hC : M.circuit C) : C.nonempty :=
by {rw set.nonempty_iff_ne_empty, rintro rfl, exact hC.1.1 M.empty_indep}

lemma empty_not_circuit (M : matroid_in α) : ¬M.circuit ∅ :=
λ h, by simpa using h.nonempty

lemma circuit.finite [finitary M] (hC : M.circuit C) : C.finite := let ⟨h⟩ := ‹M.finitary› in h C hC  

lemma circuit_iff_dep_forall_diff_singleton_indep :
  M.circuit C ↔ M.dep C ∧ ∀ e ∈ C, M.indep (C \ {e}) :=
begin
  rw [circuit_iff_forall_ssubset, and.congr_right_iff],
  refine λ hdep, ⟨λ h e heC, (h _ $ diff_singleton_ssubset.2 heC), λ h I hIC, _⟩,
  obtain ⟨e, heC,heI⟩ := exists_of_ssubset hIC,
  exact (h e heC).subset (subset_diff_singleton hIC.subset heI),
end

lemma circuit.eq_of_dep_subset_self (hC : M.circuit C) (hX : M.dep X) (hXC : X ⊆ C) : C = X :=
by_contra (λ h, hX.not_indep (hC.ssubset_indep (ssubset_of_subset_of_ne hXC (ne.symm h))))

lemma circuit.eq_of_subset_circuit (hC₁ : M.circuit C₁) (hC₂ : M.circuit C₂) (h : C₁ ⊆ C₂) :
  C₁ = C₂ :=
(hC₂.eq_of_dep_subset_self hC₁.dep h).symm

lemma circuit.circuit_restrict_of_subset (hC : M.circuit C) (hCX : C ⊆ X) : (M ‖ X).circuit C :=
begin
  rw [←restrict_inter_ground], 
  have hCX' : C ⊆ (M ‖ (X ∩ M.E)).E, 
  { rw [restrict_ground_eq], exact subset_inter hCX hC.subset_ground }, 
  simp_rw [circuit_iff, restrict_dep_iff, subset_inter_iff, and_iff_right hCX, 
    and_iff_left hC.subset_ground, and_iff_right hC.dep], 
  exact λ D hD hDC, hC.eq_of_dep_subset hD.1 hDC, 
end 

/-- For an independent set `I` that spans a point `e ∉ I`, the unique circuit contained in 
`I ∪ {e}`. Has the junk value `{e}` if `e ∈ I` and `univ` if `e ∉ M.cl I`. -/
def fund_circuit (M : matroid_in α) (e : α) (I : set α) := insert e (⋂₀ {J | J ⊆ I ∧ e ∈ M.cl J})

lemma fund_circuit_subset_ground (heI : e ∈ M.cl I) : M.fund_circuit e I ⊆ M.E := 
begin
  refine (insert_subset.mpr ⟨(cl_subset_ground _ _) heI, 
    (sInter_subset_of_mem _).trans (inter_subset_right I M.E)⟩), 
  refine ⟨inter_subset_left _ _,_⟩,   
  rwa [←cl_eq_cl_inter_ground], 
end 

lemma fund_circuit_subset_insert (he : e ∈ M.cl I) : 
  M.fund_circuit e I ⊆ insert e I :=
insert_subset_insert (sInter_subset_of_mem ⟨rfl.subset, he⟩)

lemma mem_fund_circuit (M : matroid_in α) (e : α) (I : set α) : e ∈ fund_circuit M e I := 
  mem_insert _ _

/-- The fundamental circuit of `e` and `I` has the junk value `{e}` if `e ∈ I` -/
lemma indep.fund_circuit_eq_of_mem (hI : M.indep I) (he : e ∈ I) : M.fund_circuit e I = {e} :=
begin
  rw [fund_circuit, ←union_singleton, union_eq_right_iff_subset], 
  refine sInter_subset_of_mem _, 
  simp only [mem_set_of_eq, singleton_subset_iff, and_iff_right he], 
  exact mem_cl_of_mem _ (mem_singleton _) (singleton_subset_iff.mpr (by ssE)), 
end 

lemma indep.fund_circuit_circuit (hI : M.indep I) (he : e ∈ M.cl I \ I) : 
  M.circuit (M.fund_circuit e I) :=
begin
  rw [circuit_iff_dep_forall_diff_singleton_indep, 
    ←not_indep_iff (fund_circuit_subset_ground he.1), fund_circuit], 
  -- rw [circuit_iff_dep_forall_diff_singleton_indep (fund_circuit_subset_ground he.1), fund_circuit], 
  have hu : M.indep (⋃₀ {J : set α | J ⊆ I ∧ e ∈ M.cl J}), 
    from hI.subset (sUnion_subset (λ J, and.left)), 
  have hI' : I ∈ {J : set α | J ⊆ I ∧ e ∈ M.cl J}, from ⟨rfl.subset, he.1⟩,  
  refine ⟨λ hi, _, λ f hf, _⟩,  
  { rw [indep.insert_indep_iff_of_not_mem, ←bInter_cl_eq_cl_sInter_of_sUnion_indep _ ⟨I, hI'⟩ hu] 
      at hi, 
    { simpa using hi },
    { exact hI.subset (sInter_subset_of_mem hI') },
    exact λ heIs, he.2 (sInter_subset_of_mem hI' heIs) },
  obtain (rfl | hne) := em (e = f), 
  { refine hu.subset _, 
    simp only [insert_diff_of_mem, mem_singleton], 
    exact subset_trans (diff_subset _ _) 
      ((sInter_subset_of_mem hI').trans (subset_sUnion_of_mem hI')) },
  rw [mem_insert_iff, mem_sInter, eq_comm, iff_false_intro hne, false_or] at hf, 
  rw [←insert_diff_singleton_comm hne, indep.insert_indep_iff_of_not_mem], 
  { intro hcl, 
    exact (hf _ ⟨(diff_subset _ _).trans (sInter_subset_of_mem hI'), hcl⟩).2 rfl,  },
  { exact hI.subset ((diff_subset _ _).trans (sInter_subset_of_mem hI')) },
  -- needs fixed insert_indep_iff_of_not_mem 
  sorry 
  
  -- exact λ h'e, he.2 ((diff_subset _ _).trans (sInter_subset_of_mem hI') h'e),  
end 

lemma exists_circuit_subset_of_dep (hX : M.dep X) : ∃ C ⊆ X, M.circuit C :=
begin
  obtain ⟨I, hI⟩ := M.exists_basis X, 
  obtain (rfl | hss) := (ssubset_or_eq_of_subset hI.subset).symm,
  { exact (hX.not_indep hI.indep).elim },
  obtain ⟨e, heX, heI⟩ := exists_of_ssubset hss, 
  have he : e ∈ M.cl I \ I := ⟨hI.subset_cl heX, heI⟩,  
  exact ⟨M.fund_circuit e I, (fund_circuit_subset_insert he.1).trans 
    (insert_subset.mpr ⟨heX, hss.subset⟩), hI.indep.fund_circuit_circuit he⟩,  
end 

lemma dep_iff_supset_circuit (hX : X ⊆ M.E . ssE) : M.dep X ↔ ∃ C ⊆ X, M.circuit C  :=
⟨exists_circuit_subset_of_dep, by { rintro ⟨C, hCX, hC⟩, exact hC.dep.supset hCX }⟩

lemma indep_iff_forall_subset_not_circuit' : M.indep I ↔ (∀ C ⊆ I, ¬ M.circuit C) ∧ I ⊆ M.E  :=
begin
  by_cases hI : I ⊆ M.E, 
  { rw [←not_iff_not, not_indep_iff], 
    simp_rw [dep_iff_supset_circuit, and_iff_left hI, not_forall, not_not] },
  exact iff_of_false (hI ∘ indep.subset_ground) (hI ∘ and.right), 
end 

lemma indep_iff_forall_subset_not_circuit (hI : I ⊆ M.E . ssE) : 
  M.indep I ↔ (∀ C ⊆ I, ¬ M.circuit C) :=
by rw [indep_iff_forall_subset_not_circuit', and_iff_left hI]

lemma circuit.subset_cl_diff_singleton (hC : M.circuit C) (e : α) : C ⊆ M.cl (C \ {e}) :=
begin
  by_cases he : e ∈ C, 
  { rw [(hC.diff_singleton_basis he).cl], exact subset_cl _ }, 
  rw [diff_singleton_eq_self he], exact subset_cl _, 
end

lemma mem_cl_iff_exists_circuit (hX : X ⊆ M.E . ssE):
  e ∈ M.cl X ↔ e ∈ X ∨ ∃ C, M.circuit C ∧ e ∈ C ∧ C ⊆ insert e X :=
begin
  refine ⟨λ h, _,_⟩,
  { by_contra' h',
    obtain ⟨I, hI⟩ := M.exists_basis X,
    have hIe : ¬ M.indep (insert e I),
    { intro hI',
      refine indep_iff_not_mem_cl_diff_forall.mp hI' e (mem_insert _ _) _,
      rwa [insert_diff_of_mem _ (mem_singleton _),
        diff_singleton_eq_self (not_mem_subset hI.subset h'.1), hI.cl]},
    have heI : e ∈ M.cl I \ I, by { rw [hI.cl], exact ⟨h, not_mem_subset hI.subset h'.1⟩ }, 
    have hC := hI.indep.fund_circuit_circuit heI, 
    exact h'.2 _ hC (mem_fund_circuit _ _ _) 
      ((fund_circuit_subset_insert heI.1).trans (insert_subset_insert hI.subset)) },
  rintro (heX | ⟨C,hC, heC, hCX⟩),
  apply mem_cl_of_mem _ heX,  
  refine (M.cl_subset _) (hC.subset_cl_diff_singleton e heC), 
  rwa [diff_subset_iff],  
end

lemma mem_cl_iff_exists_circuit_of_not_mem (he : e ∉ X) : 
  e ∈ M.cl X ↔ ∃ C, M.circuit C ∧ e ∈ C ∧ C ⊆ insert e X := 
begin
  rw [cl_eq_cl_inter_ground, mem_cl_iff_exists_circuit, mem_inter_iff, iff_false_intro he, 
    false_and, false_or], 
  refine exists_congr (λ C, _), 
  simp_rw [and.congr_right_iff], 
  refine λ hC heC, ⟨λ hCX, hCX.trans (insert_subset_insert (inter_subset_left _ _)), λ hCX, _⟩,   
  refine (subset_inter hCX hC.subset_ground).trans _, 
  rw [insert_inter_distrib], 
  exact inter_subset_inter_right _ (subset_insert _ _),
end 

/-- A generalization of the strong circuit elimination axiom. For finite matroids, this is 
  equivalent to the case where `ι` is a singleton type, which is the usual two-circuit version. 
  The stronger version is required for axiomatizing infinite matroids via circuits. -/
lemma circuit.strong_multi_elimination {ι : Type*} (hC : M.circuit C) (x : ι → α) (Cs : ι → set α) 
(hCs : ∀ i, M.circuit (Cs i)) (h_mem : ∀ i, (x i) ∈ C ∩ (Cs i)) 
(h_unique : ∀ i i', x i ∈ Cs i' → i = i') {z : α} (hz : z ∈ C \ ⋃ i, Cs i) :
  ∃ C', M.circuit C' ∧ z ∈ C' ∧ C' ⊆ (C ∪ ⋃ i, (Cs i)) \ range x :=
begin
  set Y := (C ∪ ⋃ x, Cs x) \ (insert z (range x)) with hY, 
  have hYE : Y ⊆ M.E, 
  { refine (diff_subset _ _).trans (union_subset hC.subset_ground _), 
    exact (Union_subset (λ i, (hCs i).subset_ground )) },
  
  have h₁ : range x ⊆ M.cl (⋃ i, ((Cs i) \ {x i} \ (insert z (range x)))), 
  { rintro e ⟨i, rfl⟩,  
    have h' := (hCs i).subset_cl_diff_singleton (x i) (h_mem i).2, 
    refine mem_of_mem_of_subset h' (M.cl_subset _), 
    refine subset_Union_of_subset i (subset_diff.mpr ⟨rfl.subset,_⟩), 
    rw disjoint_iff_forall_ne, 
    rintro y hy z (rfl | ⟨j, rfl⟩) rfl, 
    { exact hz.2 (mem_Union_of_mem i hy.1) },
    refine hy.2 (mem_singleton_iff.mpr _), 
    rw h_unique _ _ hy.1 },
  have h₂ : range x ⊆ M.cl Y, 
  { refine h₁.trans (M.cl_subset (Union_subset (λ x, _))),  
    refine diff_subset_diff_left (subset_union_of_subset_right _ _),
    exact subset_Union_of_subset x (diff_subset _ _) },
  have h₃ : C \ {z} ⊆ M.cl Y, 
  { suffices : C \ {z} ⊆ (C \ insert z (range x)) ∪ (range x), 
    { rw [union_diff_distrib] at hY, 
      convert this.trans (union_subset_union ((subset_union_left _ _).trans_eq hY.symm) h₂), 
      rw union_eq_right_iff_subset.mpr,
      exact subset_cl Y },
    rw [←union_singleton, ←diff_diff, diff_subset_iff, singleton_union, ←insert_union, 
      insert_diff_singleton, ←singleton_union, union_assoc, diff_union_self], 
    exact subset_union_of_subset_right (subset_union_left _ _) _ },
  rw [←cl_subset_cl_iff_subset_cl] at h₃, 
  have h₄ := h₃ (hC.subset_cl_diff_singleton z hz.1), 
  obtain (hzY | ⟨C', hC', hzC', hCzY⟩) := mem_cl_iff_exists_circuit.mp h₄, 
  { exact ((hY.subset hzY).2 (mem_insert z _)).elim },
  
  refine ⟨C', hC', hzC', subset_diff.mpr ⟨_,_⟩⟩, 
  { exact hCzY.trans (insert_subset.mpr ⟨or.inl hz.1,diff_subset _ _⟩) },
  refine disjoint_of_subset_left hCzY _, 
  rw [←singleton_union, disjoint_union_left, disjoint_singleton_left], 
  refine ⟨not_mem_subset _ hz.2, _⟩,   
  { rintro x' ⟨i,rfl⟩, exact mem_Union_of_mem i ((h_mem i).2) },
  exact disjoint_of_subset_right (subset_insert z _) disjoint_sdiff_left,  
end 

/-- The strong circuit elimination axiom. For any two circuits `C₁,C₂` and all `e ∈ C₁ ∩ C₂` and 
  `f ∈ C₁ \ C₂`, there is a circuit `C` with `f ∈ C ⊆ (C₁ ∪ C₂) \ {e}`. -/
lemma circuit.strong_elimination (hC₁ : M.circuit C₁) (hC₂ : M.circuit C₂) (he : e ∈ C₁ ∩ C₂) 
(hf : f ∈ C₁ \ C₂) : ∃ C ⊆ (C₁ ∪ C₂) \ {e}, M.circuit C ∧ f ∈ C :=
begin
  obtain ⟨C, hC, hfC, hCss⟩  := 
    @circuit.strong_multi_elimination _ M C₁ unit hC₁ (λ _, e) (λ _, C₂) (by simpa) 
    (by simpa) (by simp) f (by simpa),   
  simp only [range_const, Union_const] at hCss, 
  exact ⟨C, hCss, hC, hfC⟩, 
end      

/-- The circuit eliminiation axiom : for any pair of distinct circuits `C₁,C₂` and any `e`, some
  circuit is contained in `C₁ ∪ C₂ \ {e}`. Traditionally this is stated with the assumption that 
  `e ∈ C₁ ∩ C₂`, but it is also true without it. -/
lemma circuit.elimination (hC₁ : M.circuit C₁) (hC₂ : M.circuit C₂) (h : C₁ ≠ C₂) (e : α) : 
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

lemma circuit.eq_fund_circuit_of_subset_insert_indep (hC : M.circuit C) (hI : M.indep I) 
(hCI : C ⊆ insert e I) : 
  C = M.fund_circuit e I := 
begin
  by_cases heE : e ∈ M.E,
  { by_contra' hne, 
    have he : e ∉ I, { intro heI, rw [insert_eq_of_mem heI] at hCI, exact hC.dep (hI.subset hCI) },
    have heI : e ∈ M.cl I \ I, 
    { rw [mem_diff, hI.mem_cl_iff_of_not_mem he, dep_iff_supset_circuit, and_iff_right heE],
      exact ⟨⟨C, hCI, hC⟩, he⟩ },
    obtain ⟨C', hC'ss, hC'⟩ := hC.elimination (hI.fund_circuit_circuit heI) hne e, 
    refine hC'.dep (hI.subset (hC'ss.trans _)), 
    rw [diff_subset_iff, singleton_union], 
    exact union_subset hCI (fund_circuit_subset_insert heI.1) }, 
  refine (hC.dep (hI.subset (λ x hxC, (hCI hxC).elim _ id))).elim, 
  rintro rfl, 
  exact (heE (hC.subset_ground hxC)).elim, 
end 

lemma eq_of_circuit_iff_circuit_forall {M₁ M₂ : matroid_in α} (hE : M₁.E = M₂.E)
(h : ∀ C ⊆ M₁.E , M₁.circuit C ↔ M₂.circuit C) :
  M₁ = M₂ :=
begin
  refine eq_of_indep_iff_indep_forall hE (λ I hI, _), 
  simp_rw [indep_iff_forall_subset_not_circuit', ←hE, and_iff_left hI],
  exact ⟨λ h' C hCI, by { rw ←h _ (hCI.trans hI), exact h' _ hCI } , 
    λ h' C hCI, by { rw h _ (hCI.trans hI), exact h' _ hCI }⟩, 
end 

lemma indep_iff_forall_finite_subset_indep [finitary M] : 
  M.indep I ↔ ∀ J ⊆ I, J.finite → M.indep J :=   
begin
  refine ⟨λ h J hJI hJ, h.subset hJI, _⟩, 
  rw indep_iff_forall_subset_not_circuit', 
  exact λ h, ⟨λ C hCI hC, hC.dep.not_indep (h _ hCI hC.finite), 
    λ e heI, singleton_subset_iff.mp 
      (h _ (singleton_subset_iff.mpr heI) (to_finite _)).subset_ground⟩,  
end 

section dual 

/-- A cocircuit is the complement of a hyperplane -/
def cocircuit (M : matroid_in α) (K : set α) : Prop := M﹡.circuit K

@[simp] lemma dual_circuit_iff_cocircuit {K : set α} : M﹡.circuit K ↔ M.cocircuit K := iff.rfl 

lemma coindep_iff_forall_subset_not_cocircuit' : 
  M.coindep X ↔ (∀ K ⊆ X, ¬ M.cocircuit K) ∧ X ⊆ M.E  := 
by simp [←dual_indep_iff_coindep, indep_iff_forall_subset_not_circuit']
  
lemma coindep_iff_forall_subset_not_cocircuit (hX : X ⊆ M.E . ssE) : 
  M.coindep X ↔ (∀ K ⊆ X, ¬ M.cocircuit K) :=
by rw [coindep_iff_forall_subset_not_cocircuit', and_iff_left hX]

lemma cocircuit_iff_mem_minimals {K : set α} : 
  M.cocircuit K ↔ K ∈ minimals (⊆) {X | ∀ B, M.base B → (X ∩ B).nonempty} :=  
begin
  simp_rw [cocircuit, circuit, mem_minimals_set_of_iff, dep_iff, dual_indep_iff_coindep, 
    dual_ground, and_imp, coindep, not_and, not_exists, not_and, not_disjoint_iff_nonempty_inter, 
    inter_comm K],  
  split, 
  { rintro ⟨⟨h, hKE⟩,h'⟩, refine ⟨h hKE, λ X hX hXK, h' (λ _, hX) (hXK.trans hKE) hXK⟩ }, 
  rintro ⟨h1, h2⟩,
  have hKE : K ⊆ M.E, 
  { rw [←inter_eq_left_iff_subset, eq_comm],
    apply h2 (λ B hB, _) (inter_subset_left _ _), 
    rw [inter_assoc, inter_eq_self_of_subset_right hB.subset_ground, inter_comm],
    exact h1 B hB }, 
  exact ⟨⟨λ _, h1,hKE⟩, λ X hX hXE hXK , h2 (hX hXE) hXK ⟩, 
end 

lemma cocircuit.finite [finitary M﹡] {K : set α} (hK : M.cocircuit K) : K.finite :=
(dual_circuit_iff_cocircuit.mpr hK).finite 

end dual 

section girth

variables {k : ℕ}

/- Todo : `finitary` versions without finiteness in the statements -/

/-- The girth of a matroid_in is the size of its smallest finite circuit 
  (or zero if there is no finite circuit)-/
def girth (M : matroid_in α) : ℕ :=  Inf (ncard '' {C | M.circuit C ∧ C.finite})

lemma girth_eq_zero_iff : M.girth = 0 ↔ ∀ C, M.circuit C → C.infinite :=
begin
  simp_rw [girth, nat.Inf_eq_zero, mem_image, mem_set_of_eq, image_eq_empty, set.infinite, 
    ←not_nonempty_iff_eq_empty, imp_iff_or_not, ←imp_iff_or_not, nonempty_def, mem_set_of],
  rw [imp_iff_not], 
  { simp },
  simp only [not_exists, not_and, and_imp], 
  intros C hC hCfin hc, 
  rw [ncard_eq_zero hCfin] at hc, subst hc, 
  exact M.empty_not_circuit hC, 
end 

@[simp] lemma girth_eq_zero_iff_free [finitary M] : M.girth = 0 ↔ M = free_on M.E :=
begin
  rw [←ground_indep_iff_eq_free_on, girth_eq_zero_iff, indep_iff_forall_subset_not_circuit], 
  exact ⟨λ h C hCE hC, h C hC hC.finite, λ h C hC hi, h C hC.subset_ground hC⟩,
end 

lemma circuit.girth_le (hC : M.circuit C) (hCfin : C.finite) : M.girth ≤ C.ncard :=
nat.Inf_le ⟨C, ⟨hC, hCfin⟩, rfl⟩

lemma exists_circuit_girth (h : M.girth ≠ 0) : ∃ C, M.circuit C ∧ C.finite ∧ C.ncard = M.girth :=
begin
  simp_rw [ne.def, girth_eq_zero_iff, not_forall, exists_prop, not_infinite] at h, 
  obtain ⟨C, ⟨hC,hCfin⟩, hc⟩ := 
    nat.Inf_mem (nonempty.image ncard (h : {C | M.circuit C ∧ C.finite}.nonempty)), 
  exact ⟨C, hC, hCfin, hc⟩, 
end    

lemma girth_eq_iff (hk : k ≠ 0) : 
  M.girth = k ↔ (∀ C, M.circuit C → C.finite → k ≤ C.ncard) ∧ 
    (∃ C, M.circuit C ∧ C.finite ∧ C.ncard = k) :=
begin
  split,
  { rintro rfl, 
    refine ⟨λ C hC hCfin, hC.girth_le hCfin, (exists_circuit_girth hk).imp (λ C, id)⟩ },
  rintro ⟨h, C, ⟨hC, hCfin, rfl⟩⟩, 
  have hg : M.girth ≠ 0,  
  { simp_rw [ne.def, girth_eq_zero_iff, not_forall, exists_prop, not_infinite], 
    exact ⟨C, hC, hCfin⟩ }, 
  obtain ⟨C', hC', hC'fin, hC'card⟩ := exists_circuit_girth hg, 
  rw [←hC'card, le_antisymm_iff, and_iff_left (h _ hC' hC'fin)], 
  convert hC.girth_le hCfin, 
end 

lemma girth_le_iff (h : M.girth ≠ 0) : M.girth ≤ k ↔ ∃ C, M.circuit C ∧ C.finite ∧ C.ncard ≤ k :=
begin
  obtain ⟨C, hC, hCfin, hCcard⟩ := exists_circuit_girth h, 
  refine ⟨λ h, ⟨C, hC, hCfin, hCcard.trans_le h⟩, _⟩,
  rintro ⟨C', hC', hC'fin, hC'card⟩, 
  exact (hC'.girth_le hC'fin).trans hC'card, 
end 

lemma le_girth_iff (h : M.girth ≠ 0) : k ≤ M.girth ↔ ∀ C, M.circuit C → C.finite → k ≤ C.ncard :=
begin
  refine ⟨λ h C hC hCfin, h.trans (hC.girth_le hCfin), λ h', _⟩,
  obtain ⟨C, hC, hCfin, hCc⟩ := exists_circuit_girth h, 
  exact (h' C hC hCfin).trans_eq hCc, 
end     

end girth

section basis_exchange

variables {B₁ B₂ I₁ I₂ : set α}

lemma indep.rev_exchange_indep_iff (hI : M.indep I) (he : e ∈ M.cl I \ I) (hf : f ∈ I) : 
  M.indep (insert e I \ {f}) ↔ f ∈ M.fund_circuit e I :=   
begin
  have heE : e ∈ M.E := (M.cl_subset_ground I) he.1, 
  rw [←not_iff_not, dep_iff_supset_circuit ((diff_subset _ _).trans (by ssE : insert e I ⊆ M.E))], 
  refine ⟨_, λ h, ⟨M.fund_circuit e I, 
    subset_diff_singleton (fund_circuit_subset_insert he.1) h, hI.fund_circuit_circuit he⟩⟩,
  rintro ⟨C, hCss, hC⟩ hf, 
  have := hC.eq_fund_circuit_of_subset_insert_indep hI (hCss.trans (diff_subset _ _)), 
  subst this, 
  exact (hCss hf).2 rfl, 
end 

/- Given two bases `B₁,B₂` of `M` and an element `e` of `B₁ \ B₂`, we can find an `f ∈ B₂ \ B₁`
  so that swapping `e` for `f` in yields bases in both `B₁` and `B₂`.  -/
theorem base.strong_exchange (hB₁ : M.base B₁) (hB₂ : M.base B₂) (he : e ∈ B₁ \ B₂) :
  ∃ f ∈ B₂ \ B₁, M.base (insert e B₂ \ {f}) ∧ M.base (insert f B₁ \ {e}) :=
begin
  suffices : ∃ f ∈ B₂ \ B₁, M.indep (insert e B₂ \ {f}) ∧ M.indep (insert f B₁ \ {e}),
  { obtain ⟨f,hf,h₁,h₂⟩:= this, 
    exact ⟨f,hf,hB₂.exchange_base_of_indep' hf.1 he.2 h₁, 
      hB₁.exchange_base_of_indep' he.1 hf.2 h₂⟩ },
  by_contra' h', 
  
  have hecl : e ∈ M.cl B₂ \ B₂ := ⟨by { rw [hB₂.cl], exact mem_univ _ }, he.2⟩,  
  set C := M.fund_circuit e B₂, 
  have hC : M.circuit C, from indep.fund_circuit_circuit hB₂.indep hecl, 

  have h : C \ B₁ ⊆ M.cl (B₁ \ {e}),   
  { intros f hf,
    have hne : f ≠ e, {rintro rfl, exact hf.2 he.1 },
    have hfB₂ : f ∈ B₂, from ((fund_circuit_subset_insert hecl.1) hf.1).elim (false.elim ∘ hne) id, 
    rw [mem_diff, ←hB₂.indep.rev_exchange_indep_iff hecl hfB₂] at hf,
    rw [(hB₁.indep.diff _).mem_cl_iff_of_not_mem (not_mem_subset (diff_subset _ _) hf.2), 
      insert_diff_singleton_comm hne, and_iff_right (hB₂.subset_ground hfB₂)], 
    exact h' f ⟨hfB₂,hf.2⟩ hf.1 },

  nth_rewrite 0 ←union_diff_cancel (singleton_subset_iff.mpr he.1) at h, 
  rw [diff_subset_iff, union_assoc, union_eq_self_of_subset_left (subset_cl (B₁ \ {e})), 
    ←diff_subset_iff, ←cl_subset_cl_iff_subset_cl] at h, 
  have heB₁ := (hC.subset_cl_diff_singleton e).trans h (mem_fund_circuit _ _ _), 
  exact indep_iff_not_mem_cl_diff_forall.mp hB₁.indep e he.1 heB₁, 
end 

/- Given two bases `I₁,I₂` of `X` and an element `e` of `I₁ \ I₂`, we can find an `f ∈ I₂ \ I₁`
  so that swapping `e` for `f` in yields bases in both `I₁` and `I₂`.  -/
theorem basis.strong_exchange (hI₁ : M.basis I₁ X) (hI₂ : M.basis I₂ X) (he : e ∈ I₁ \ I₂) :
  ∃ f ∈ I₂ \ I₁, M.basis (insert e I₂ \ {f}) X ∧ M.basis (insert f I₁ \ {e}) X :=
by { convert hI₁.base_restrict.strong_exchange hI₂.base_restrict he, simp }
  
lemma base.rev_exchange (hB₁ : M.base B₁) (hB₂ : M.base B₂) (he : e ∈ B₁ \ B₂) :
  ∃ f ∈ B₂ \ B₁, M.base (insert e B₂ \ {f}) :=
(hB₁.strong_exchange hB₂ he).imp (λ f ⟨hf,h,h'⟩, ⟨hf,h⟩)

theorem basis.rev_exchange (hI₁ : M.basis I₁ X) (hI₂ : M.basis I₂ X) (he : e ∈ I₁ \ I₂) :
  ∃ f ∈ I₂ \ I₁, M.basis (insert e I₂ \ {f}) X :=
(hI₁.strong_exchange hI₂ he).imp (by { simp_rw [exists_prop], tauto })

end basis_exchange

-- section from_axioms TODO : Fix this for `matroid_in`.  

-- /-- A collection of sets satisfying the circuit axioms determines a matroid_in -/
-- def matroid_in_of_circuit_of_finite [finite E] (circuit : set α → Prop) 
-- (empty_not_circuit : ¬ circuit ∅) (antichain : ∀ C₁ C₂, circuit C₁ → circuit C₂ → C₁ ⊆ C₂ → C₁ = C₂)
-- (elimination : ∀ C₁ C₂ e,
--     circuit C₁ → circuit C₂ → C₁ ≠ C₂ → e ∈ C₁ ∩ C₂ → ∃ C ⊆ (C₁ ∪ C₂) \ {e}, circuit C) :
-- matroid_in α :=
-- matroid_in_of_indep_of_finite (λ I, ∀ C ⊆ I, ¬circuit C) ⟨∅, λ C hC, (by rwa subset_empty_iff.mp hC)⟩
-- (λ I J hIJ hJ C hCI, hIJ C (hCI.trans hJ))
-- begin
--   by_contra' h,
--   obtain ⟨I,J,hI,hJ,hIJ,Hbad⟩ := h,
--   set indep := (λ I, ∀ C ⊆ I, ¬circuit C) with hi,

--   /- Choose an independent set `K ⊆ I ∪ J`, larger than `I`, for which `I \ K` is minimized -/
--   set sbad := {K : set α | indep K ∧ K ⊆ I ∪ J ∧ I.ncard < K.ncard} with hsbad,
--   have hbad_ne : sbad.nonempty := ⟨J, hJ, subset_union_right _ _, hIJ⟩,
--   obtain ⟨K, ⟨hK, hKIJ, hIK⟩, hKmin⟩ :=
--     @set.finite.exists_minimal_wrt (set α) _ _ (λ X, (I \ X).ncard) sbad (to_finite sbad) hbad_ne,
--   simp only [hsbad, mem_set_of_eq, and_imp] at hKmin,

--   obtain hIK_empty | ⟨e, heI, heK⟩ := (I \ K).eq_empty_or_nonempty,
--   /- If `I \ K` is empty then we get an easy contradiction by augmenting `I` into `K`. -/
--   { obtain ⟨e,heK,heI⟩ := exists_mem_not_mem_of_ncard_lt_ncard hIK,
--     have heJ : e ∈ J := by_contra (λ heJ, not_or heI heJ (hKIJ heK)),
--     obtain ⟨C, hCeI, hC⟩ := Hbad e heJ heI,
--     exact hK C (hCeI.trans (insert_subset.mpr ⟨heK, diff_eq_empty.mp hIK_empty⟩)) hC},

--   have hCf : ∀ f ∈ K \ I, ∃ Cf ⊆ (insert e K), circuit Cf ∧ f ∉ Cf ∧ e ∈ Cf,
--   { rintro f ⟨hfK,hfI⟩,
--     have hef : e ≠ f, from λ h, hfI (h ▸heI ),
--     set T := ((insert e K) \ {f}) with hT,
--     have hTIJ : T ⊆ I ∪ J, from
--       ((diff_subset _ _).trans (insert_subset.mpr ⟨or.inl heI,hKIJ⟩)),
--     have hTcard : T.ncard = K.ncard, by rw [hT, ncard_exchange' heK hfK],
--     have hITcard : (I \ T).ncard < (I \ K).ncard,
--     { rw [nat.lt_iff_add_one_le, hT, ←insert_diff_singleton_comm hef, ←union_singleton, ←diff_diff,
--         ncard_diff_singleton_add_one ],
--       { convert rfl.le using 2,
--         rw [diff_eq_compl_inter, diff_eq_compl_inter, diff_eq_compl_inter, compl_inter,
--           inter_distrib_right, compl_compl, singleton_inter_eq_empty.mpr hfI, empty_union]},
--       exact ⟨heI,λ he', heK he'.1⟩},

--     have hTi : ¬indep T, from
--       λ hTi, hITcard.ne (hKmin _ hTi hTIJ (hIK.trans_eq hTcard.symm) hITcard.le).symm,

--     push_neg at hTi,
--     obtain ⟨Cf, hCfT, hCf⟩ := hTi,
--     refine ⟨Cf, hCfT.trans (diff_subset _ _), hCf, _, _⟩,
--     { exact mt (@hCfT f) (not_mem_diff_of_mem (mem_singleton f))},

--     refine by_contra (λ heCf, hK Cf (λ x hxCf, _) hCf),

--     exact mem_of_mem_insert_of_ne (hCfT hxCf).1 (by {rintro rfl, exact heCf hxCf})},

--   obtain ⟨g,hgK,hgI⟩ := exists_mem_not_mem_of_ncard_lt_ncard hIK,
--   obtain ⟨Cg, hCgss, hCg, hgCg, heCg⟩ := hCf g ⟨hgK,hgI⟩,

--   have hg_ex : ∃ g', g' ∈ Cg ∧ g' ∈ K \ I,
--   { by_contra' hg',
--     exact hI _ (λ x hx,
--       or.elim (hCgss hx) (λ h, h.symm ▸ heI) (λ hxK, by_contra (λ hxI, hg' _ hx ⟨hxK, hxI⟩))) hCg},
--   obtain ⟨g', hg', hg'KI⟩ := hg_ex,

--   obtain ⟨Cg', hCg'ss, hCg', hgCg', heCg'⟩ := hCf g' hg'KI,
--   have hne : Cg ≠ Cg',
--   { intro heq, rw ←heq at hgCg', exact hgCg' hg', },
--   obtain ⟨C, hCss, hC⟩ := elimination _ _ e hCg hCg' hne ⟨heCg, heCg'⟩,
--   refine hK C (hCss.trans _) hC,
--   rw [diff_subset_iff, singleton_union],
--   exact union_subset hCgss hCg'ss,
-- end

-- @[simp] lemma matroid_in_of_circuit_of_finite_apply [finite E] (circuit : set α → Prop)
--   (empty_not_circuit : ¬ circuit ∅)
--   (antichain : ∀ C₁ C₂, circuit C₁ → circuit C₂ → C₁ ⊆ C₂ → C₁ = C₂)
--   (elimination : ∀ C₁ C₂ e,
--     circuit C₁ → circuit C₂ → C₁ ≠ C₂ → e ∈ C₁ ∩ C₂ → ∃ C ⊆ (C₁ ∪ C₂) \ {e}, circuit C) :
--   (matroid_in_of_circuit_of_finite circuit empty_not_circuit antichain elimination).circuit = circuit :=
-- begin
--   ext C,
--   simp_rw [matroid_in_of_circuit_of_finite, matroid_in.circuit_iff_forall_ssubset,
--    matroid_in_of_indep_of_finite_apply, 
-- not_forall, not_not, exists_prop],
--   refine ⟨λ h, _,λ h, ⟨⟨_,rfl.subset, h⟩,λ I hIC C' hC'I hC',
--     hIC.not_subset ((antichain C' C hC' h (hC'I.trans hIC.subset)) ▸ hC'I )⟩⟩,
--   obtain ⟨⟨C₀,hC₀C, hC₀⟩,hI⟩ := h,
--   obtain rfl | hC₀C := eq_or_ssubset_of_subset hC₀C,
--     assumption,
--   exact (hI _ hC₀C _ rfl.subset hC₀).elim,
-- end

-- end from_axioms

end matroid_in 
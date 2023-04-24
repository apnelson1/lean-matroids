import .flat 

/-
  A `loop` of a matroid is a one-element circuit, or, definitionally, a member of `M.cl ∅`.  
  Thus, the set of loops of `M` is equal to `M.cl ∅`, and we prefer this notation instead of 
  `{e | M.loop e}` or similar. A `nonloop` is simply an element that is not a loop, but we give 
  it a definition for the sake of dot notation. 
-/

open_locale classical

variables {E : Type*} {M M₁ M₂ : matroid E} {I C X Y Z K F F₁ F₂ : set E} {e f x y z : E}
    
open set

namespace matroid

/- ### Loops -/

/-- A loop is a member of the closure of the empty set -/
def loop (M : matroid E) (e : E) : Prop := e ∈ M.cl ∅

lemma loop_iff_mem_cl_empty : M.loop e ↔ e ∈ M.cl ∅ := iff.rfl 

lemma cl_empty_eq_loops (M : matroid E) : M.cl ∅ = {e | M.loop e} := rfl 

lemma loop_iff_dep : M.loop e ↔ ¬ M.indep {e} :=
by rw [loop_iff_mem_cl_empty, iff_not_comm, M.empty_indep.not_mem_cl_iff, 
  mem_empty_iff_false, not_false_iff, true_and, insert_emptyc_eq]

lemma loop_iff_circuit : M.loop e ↔ M.circuit {e} := 
begin
  simp_rw [circuit_iff_forall_ssubset, 
    loop_iff_dep, iff_self_and, ssubset_singleton_iff, forall_eq], 
  exact λ _, M.empty_indep, 
end 

lemma loop_iff_not_mem_base_forall : M.loop e ↔ ∀ B, M.base B → e ∉ B :=
by simp_rw [loop_iff_dep, indep_iff_subset_base, not_exists, not_and, singleton_subset_iff]

lemma loop.circuit (he : M.loop e) : M.circuit {e} := loop_iff_circuit.mp he 


lemma loop.dep (he : M.loop e) : ¬ M.indep {e} := loop_iff_dep.mp he 

lemma loop.mem_cl (he : M.loop e) (X : set E) : e ∈ M.cl X :=
M.cl_mono (empty_subset _) he 

lemma loop.mem_flat (he : M.loop e) {F : set E} (hF : M.flat F) : e ∈ F :=
by { have := he.mem_cl F, rwa hF.cl at this }

lemma loop.dep_of_mem (he : M.loop e) (h : e ∈ X) : ¬M.indep X :=
λ hX, he.circuit.dep (hX.subset (singleton_subset_iff.mpr h))

lemma loop.not_mem_indep (he : M.loop e) (hI : M.indep I) : e ∉ I :=
λ h, he.dep_of_mem h hI

lemma loop.eq_of_circuit_mem (he : M.loop e) (hC : M.circuit C) (h : e ∈ C) : C = {e} :=
by rw he.circuit.eq_of_subset_circuit hC (singleton_subset_iff.mpr h)

lemma indep.disjoint_loops (hI : M.indep I) : disjoint I (M.cl ∅) :=
by_contra (λ h, let ⟨e,⟨heI,he⟩⟩ := not_disjoint_iff.mp h in loop.not_mem_indep he hI heI)

lemma indep.eq_empty_of_subset_loops (hI : M.indep I) (h : I ⊆ M.cl ∅) : I = ∅ :=
eq_empty_iff_forall_not_mem.mpr (λ e he, loop.not_mem_indep (h he) hI he) 

lemma cl_eq_loops_of_subset (h : X ⊆ M.cl ∅) : M.cl X = M.cl ∅ :=
(cl_subset_cl_of_subset_cl h).antisymm (M.cl_mono (empty_subset _))

lemma loop.cl (he : M.loop e) : M.cl {e} = M.cl ∅ :=
cl_eq_loops_of_subset (singleton_subset_iff.mpr he)

lemma loop_iff_cl_eq_cl_empty : M.loop e ↔ M.cl {e} = M.cl ∅ :=
⟨λ h, by rw h.cl ,λ h, by { rw [loop_iff_mem_cl_empty, ←h], exact M.mem_cl_self e }⟩


lemma cl_union_eq_cl_of_subset_loops {Y : set E} (hY : Y ⊆ M.cl ∅) (X : set E) :
  M.cl (X ∪ Y) = M.cl X := 
by rw [←cl_union_cl_right_eq_cl_union, cl_eq_loops_of_subset hY, cl_union_cl_right_eq_cl_union, 
    union_empty]

lemma cl_diff_eq_cl_of_subset_loops {Y : set E} (hY : Y ⊆ M.cl ∅) (X : set E) :
  M.cl (X \ Y) = M.cl X := 
by rw [←cl_union_eq_cl_of_subset_loops hY, diff_union_self, cl_union_eq_cl_of_subset_loops hY]

/- ### Nonloops -/

/-- A `nonloop` is an element that is not a loop -/
def nonloop (M : matroid E) (e : E) : Prop := ¬ M.loop e 

def nonloops (M : matroid E) : set E := {e | M.nonloop e}

@[simp] lemma not_loop_iff : ¬ M.loop e ↔ M.nonloop e := iff.rfl 

@[simp] lemma not_nonloop_iff : ¬ M.nonloop e ↔ M.loop e := by rw [←not_loop_iff, not_not]

lemma nonloops_eq_compl_cl_empty : M.nonloops = (M.cl ∅)ᶜ := rfl 

@[simp] lemma compl_nonloops_eq_cl_empty : (M.nonloops)ᶜ = M.cl ∅ := 
by rw [nonloops_eq_compl_cl_empty, compl_compl] 

lemma loop_or_nonloop (M : matroid E) (e : E) : M.loop e ∨ M.nonloop e := em _ 

@[simp] lemma indep_singleton : M.indep {e} ↔ M.nonloop e := by rw [nonloop, loop_iff_dep, not_not]

alias indep_singleton ↔ indep.nonloop nonloop.indep

attribute [protected] indep.nonloop nonloop.indep

lemma indep.nonloop_of_mem (hI : M.indep I) (h : e ∈ I) : ¬ M.loop e := 
λ he, (he.not_mem_indep hI) h

lemma cocircuit.nonloop_of_mem {K : set E} (hK : M.cocircuit K) (he : e ∈ K) : M.nonloop e := 
λ h, (h.mem_flat hK.compl_hyperplane.flat) he

lemma circuit.nonloop_of_mem_of_one_lt_card (hC : M.circuit C) (h : 1 < C.ncard) (he : e ∈ C) :
  M.nonloop e :=
not_loop_iff.mp (λ hlp, by simpa [hlp.eq_of_circuit_mem hC he] using h)

lemma nonloop_of_not_mem_cl (h : e ∉ M.cl X) : M.nonloop e :=
not_loop_iff.mp (λ he, h (he.mem_cl X))

lemma nonloop.mem_cl_singleton (he : M.nonloop e) (hef : e ∈ M.cl {f}) : f ∈ M.cl {e} :=
begin
  refine (M.loop_or_nonloop f).elim (λ hf, hf.mem_cl _) (λ hf, _), 
  rw [he.indep.mem_cl_iff, mem_singleton_iff], 
  rwa [hf.indep.mem_cl_iff, mem_singleton_iff, eq_comm, pair_comm] at hef, 
end 

lemma nonloop.mem_cl_comm (he : M.nonloop e) (hf : M.nonloop f) : f ∈ M.cl {e} ↔ e ∈ M.cl {f} :=
⟨hf.mem_cl_singleton, he.mem_cl_singleton⟩ 

lemma nonloop.nonloop_of_mem_cl (he : M.nonloop e) (hef : e ∈ M.cl {f}) : M.nonloop f :=
λ hf, he (by rwa [hf.cl] at hef)
  
lemma nonloop.cl_eq_of_mem_cl (he : M.nonloop e) (hef : e ∈ M.cl {f}) : M.cl {e} = M.cl {f} :=
begin
  ext x, 
  obtain (hx | hx) := M.loop_or_nonloop x, 
  { exact ⟨λ _, hx.mem_cl _, λ _, hx.mem_cl _⟩ },
  refine ⟨λ h, _, λ h, he.mem_cl_singleton _⟩,
  { rw [←singleton_subset_iff, ←cl_subset_cl_iff_subset_cl] at *,
    exact h.trans hef },
  have hfx := hx.mem_cl_singleton h, 
  rw [←singleton_subset_iff, ←cl_subset_cl_iff_subset_cl] at *,
  exact hef.trans hfx, 
end 

lemma nonloop.cl_eq_cl_iff_dep (he : M.nonloop e) (hf : M.nonloop f) : 
  M.cl {e} = M.cl {f} ↔ e = f ∨ ¬ M.indep {e,f} := 
begin
  rw [←imp_iff_or_not], 
  refine ⟨λ hef, _, λ h, he.cl_eq_of_mem_cl (by rwa [hf.indep.mem_cl_iff])⟩,
  have hf : f ∈ M.cl {e}, by {rw hef, exact M.mem_cl_self f },
  rw [pair_comm, eq_comm, ←mem_singleton_iff], 
  exact he.indep.mem_cl_iff.mp hf,  
end 

/- ### Coloops -/ 

/-- A coloop is a loop of the dual  -/
def coloop (M : matroid E) (e : E) : Prop := M﹡.loop e   

lemma coloop_iff_mem_cl_empty : M.coloop e ↔ e ∈ M﹡.cl ∅ := iff.rfl    

lemma coloops_eq_dual_cl_empty : {e | M.coloop e} = M﹡.cl ∅ := rfl 

lemma coloop.dual_loop (he : M.coloop e) : M﹡.loop e := he 

lemma loop.dual_coloop (he : M.loop e) : M﹡.coloop e := by rwa [coloop, dual_dual]

@[simp] lemma dual_coloop_iff_loop : M﹡.coloop e ↔ M.loop e :=
⟨λ h, by {rw ← dual_dual M, exact h.dual_loop}, loop.dual_coloop⟩

@[simp] lemma dual_loop_iff_coloop : M﹡.loop e ↔ M.coloop e :=
⟨λ h, by {rw ←dual_dual M, exact h.dual_coloop}, coloop.dual_loop⟩

lemma coloop_iff_forall_mem_base : M.coloop e ↔ ∀ ⦃B⦄, M.base B → e ∈ B := 
begin
  simp_rw [←dual_loop_iff_coloop, loop_iff_not_mem_base_forall, dual.base_iff], 
  exact ⟨λ h B hB, not_mem_compl_iff.mp (h _ (by rwa compl_compl)),
    λ h B hB, h hB⟩, 
end 

lemma coloop.nonloop (h : M.coloop e) : M.nonloop e := 
let ⟨B, hB⟩ := M.exists_base in hB.indep.nonloop_of_mem ((coloop_iff_forall_mem_base.mp h) hB)

lemma loop.not_coloop (h : M.loop e) : ¬M.coloop e := 
by { rw [←dual_loop_iff_coloop], rw [←dual_dual M, dual_loop_iff_coloop] at h, exact h.nonloop }

lemma coloop.not_mem_circuit (he : M.coloop e) (hC : M.circuit C) : e ∉ C :=
begin
  intro heC,
  rw coloop_iff_forall_mem_base at he, 
  obtain ⟨B,hB, hCB⟩ := (hC.diff_singleton_indep heC).exists_base_supset,
  have h := insert_subset.mpr ⟨he hB, hCB⟩,
  rw [insert_diff_singleton, insert_eq_of_mem heC] at h,
  exact hC.dep (hB.indep.subset h),
end

lemma circuit.not_coloop_of_mem (hC : M.circuit C) (heC : e ∈ C) : ¬M.coloop e :=  
λ h, h.not_mem_circuit hC heC 

lemma coloop_iff_forall_mem_cl_iff_mem : M.coloop e ↔ ∀ X, e ∈ M.cl X ↔ e ∈ X :=
begin
  rw coloop_iff_forall_mem_base, 
  refine ⟨λ h, λ X, ⟨λ heX, by_contra (λ heX', _), λ h', M.subset_cl X h'⟩, 
    λ h B hB, (h B).mp (hB.cl.symm.subset (mem_univ e))⟩,
  obtain ⟨I, hI⟩ := M.exists_basis X, 
  obtain ⟨B, hB, hIB⟩ := hI.indep.exists_base_supset, 
  exact (hI.mem_cl_iff_of_not_mem heX').mp heX (hB.indep.subset (insert_subset.mpr ⟨h hB, hIB⟩)), 
end 

lemma coloop.mem_cl_iff_mem (he : M.coloop e) : e ∈ M.cl X ↔ e ∈ X :=
coloop_iff_forall_mem_cl_iff_mem.mp he X

lemma coloop.mem_of_mem_cl (he : M.coloop e) (hX : e ∈ M.cl X) : e ∈ X := he.mem_cl_iff_mem.mp hX

@[simp] lemma cl_inter_coloops_eq (M : matroid E) (X : set E) : 
  M.cl X ∩ M﹡.cl ∅ = X ∩ M﹡.cl ∅ :=
begin
  simp_rw [set.ext_iff, mem_inter_iff, ←coloop_iff_mem_cl_empty, and.congr_left_iff], 
  exact λ x, coloop.mem_cl_iff_mem, 
end 

lemma cl_inter_eq_of_subset_coloops (X : set E) (hK : K ⊆ M﹡.cl ∅) : 
  M.cl X ∩ K = X ∩ K :=
begin
  refine inter_eq_inter_iff_right.mpr ⟨(inter_subset_left _ _).trans (M.subset_cl X), _⟩, 
  refine ((inter_subset_inter_right (M.cl X) hK).trans (M.cl_inter_coloops_eq X).subset).trans _, 
  exact inter_subset_left _ _, 
end  

lemma cl_union_eq_of_subset_coloops (X : set E) {K : set E} (hK : K ⊆ M﹡.cl ∅) :   
  M.cl (X ∪ K) = M.cl X ∪ K :=
begin
  rw [←cl_union_cl_left_eq_cl_union], 
  refine (M.subset_cl _).antisymm' (λ e he, _), 
  obtain (he' | ⟨C, hC, heC, hCss⟩) := mem_cl_iff_exists_circuit.mp he, assumption, 
  have hCX : C \ {e} ⊆ M.cl X, from λ f hfC, (hCss hfC).elim id 
      (λ hfK, (hC.not_coloop_of_mem ((diff_subset C {e}) hfC)).elim (hK hfK)), 
  exact or.inl (cl_subset_cl_of_subset_cl hCX (hC.subset_cl_diff_singleton e heC)), 
end 

lemma cl_diff_eq_of_subset_coloops (X : set E) {K : set E} (hK : K ⊆ M﹡.cl ∅) : 
  M.cl (X \ K) = M.cl X \ K :=
begin
  nth_rewrite 1 ←inter_union_diff X K, 
  rw [union_comm, cl_union_eq_of_subset_coloops _ ((inter_subset_right X K).trans hK), 
    union_diff_distrib, diff_eq_empty.mpr (inter_subset_right X K), union_empty, eq_comm, 
    sdiff_eq_self_iff_disjoint,  disjoint_iff_forall_ne], 
  rintro e heK _ heX rfl, 
  rw coloop.mem_cl_iff_mem (hK heK) at heX,
  exact heX.2 heK,   
end 

lemma cl_disjoint_of_disjoint_of_subset_coloops (hXK : disjoint X K) (hK : K ⊆ M﹡.cl ∅) :
  disjoint (M.cl X) K := 
by rwa [disjoint_iff_inter_eq_empty, cl_inter_eq_of_subset_coloops X hK, 
  ←disjoint_iff_inter_eq_empty]

lemma cl_disjoint_coloops_of_disjoint_coloops (hX : disjoint X (M﹡.cl ∅)) : 
  disjoint (M.cl X) (M﹡.cl ∅) :=
cl_disjoint_of_disjoint_of_subset_coloops hX subset.rfl

lemma cl_insert_coloop_eq (X : set E) {he : M.coloop e} : M.cl (insert e X) = insert e (M.cl X) :=
begin
  rw [←union_singleton, ←union_singleton, cl_union_eq_of_subset_coloops],
  rwa [singleton_subset_iff], 
end 

@[simp] lemma cl_union_coloops_eq (M : matroid E) (X : set E) : 
  M.cl (X ∪ M﹡.cl ∅) = M.cl X ∪ M﹡.cl ∅ := cl_union_eq_of_subset_coloops _ subset.rfl 

lemma coloop.not_mem_cl_of_not_mem (he : M.coloop e) (hX : e ∉ X) : e ∉ M.cl X := 
mt he.mem_cl_iff_mem.mp  hX 

lemma coloop.insert_indep_of_indep (he : M.coloop e) (hI : M.indep I) : M.indep (insert e I) :=
(em (e ∈ I)).elim (λ h, by rwa insert_eq_of_mem h) 
  (λ h, by rwa [hI.insert_indep_iff_of_not_mem h, he.mem_cl_iff_mem])  

lemma coloops_indep (M : matroid E) : M﹡.indep (M.cl ∅) := 
begin
  obtain ⟨B, hB⟩ := M.exists_base,  
  rw [dual_indep_iff_coindep, coindep_iff_disjoint_base], 
  exact ⟨B, hB, hB.indep.disjoint_loops.symm⟩, 
end

lemma union_indep_iff_indep_of_subset_coloops (hK : K ⊆ M﹡.cl ∅) : M.indep (I ∪ K) ↔ M.indep I :=
⟨λ h, h.subset (subset_union_left I K), λ h, indep_iff_forall_subset_not_circuit.mpr 
  (λ C hCIK hC, hC.dep (h.subset (λ e h', (hCIK h').elim id 
  (λ heK, (hC.not_coloop_of_mem h' (hK heK)).elim) )))⟩
   
lemma diff_indep_iff_indep_of_subset_coloops (hK : K ⊆ M﹡.cl ∅) : M.indep (I \ K) ↔ M.indep I :=
by rw [←union_indep_iff_indep_of_subset_coloops hK, diff_union_self, 
  union_indep_iff_indep_of_subset_coloops hK]

lemma indep_iff_union_coloops_indep : M.indep I ↔ M.indep (I ∪ M﹡.cl ∅) := 
  (union_indep_iff_indep_of_subset_coloops subset.rfl).symm 

lemma indep_iff_diff_coloops_indep : M.indep I ↔ M.indep (I \ M﹡.cl ∅) := 
  (diff_indep_iff_indep_of_subset_coloops subset.rfl).symm 

lemma coloop.cocircuit (he : M.coloop e) : M.cocircuit {e} := 
by rwa [←dual_loop_iff_coloop, loop_iff_circuit, dual_circuit_iff_cocircuit] at he

lemma coloop_iff_cocircuit : M.coloop e ↔ M.cocircuit {e} := 
by rw [←dual_loop_iff_coloop, loop_iff_circuit, dual_circuit_iff_cocircuit]

/-- If two matroids agree on loops and coloops, and have the same independent sets after 
  loops/coloops are removed, they are equal. -/
lemma eq_of_indep_iff_indep_forall_disjoint_loops_coloops 
{M₁ M₂ : matroid E} (hl : M₁.cl ∅ = M₂.cl ∅) (hc : M₁﹡.cl ∅ = M₂﹡.cl ∅) 
(h : ∀ I, disjoint I (M₁.cl ∅ ∪ M₁﹡.cl ∅) → (M₁.indep I ↔ M₂.indep I)) : 
  M₁ = M₂ :=
begin
  refine eq_of_indep_iff_indep_forall (λ I, _), 
  rw [indep_iff_diff_coloops_indep, @indep_iff_diff_coloops_indep _ M₂, ←hc], 
  obtain (hdj | hndj) := em (disjoint I (M₁.cl ∅)), 
  { rw h, 
    rw disjoint_union_right,
    exact ⟨disjoint_of_subset_left (diff_subset _ _) hdj, disjoint_sdiff_left⟩ },
  obtain ⟨e, heI, (hel : M₁.loop e)⟩ := not_disjoint_iff_nonempty_inter.mp hndj, 
  refine iff_of_false (hel.dep_of_mem ⟨heI, hel.not_coloop⟩) _, 
  rw [loop_iff_mem_cl_empty, hl, ←loop_iff_mem_cl_empty] at hel, rw [hc], 
  exact hel.dep_of_mem ⟨heI, hel.not_coloop⟩, 
end 



end matroid

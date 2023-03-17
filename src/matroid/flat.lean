import .circuit 

noncomputable theory
open_locale classical
open_locale big_operators

variables {E : Type*} [finite E] {M M₁ M₂ : matroid E} 
  {I C X Y Z F F₁ F₂ : set E} {e f x y z : E}

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

lemma cl_le_cl_of_subset (M : matroid E) (h : X ⊆ Y) :
  M.cl X ⊆ M.cl Y :=
sInter_subset_sInter (λ F hF, ⟨hF.1, h.trans hF.2⟩)

lemma cl_mono (M : matroid E) : monotone M.cl := 
  λ _ _, M.cl_le_cl_of_subset

lemma cl_subset_cl_of_subset_cl (hXY : X ⊆ M.cl Y) : 
  M.cl X ⊆ M.cl Y :=
by simpa only [cl_cl] using M.cl_le_cl_of_subset hXY

lemma r_insert_eq_add_one_of_not_mem_cl (h : e ∉ M.cl X) : 
  M.r (insert e X) = M.r X + 1 :=
r_insert_eq_add_one_of_r_ne (h ∘ mem_cl.mpr)
 
lemma not_mem_cl_of_r_insert_gt (h : M.r X < M.r (insert e X)) : 
  e ∉ M.cl X := 
h.ne.symm ∘ mem_cl.mp

lemma not_mem_cl_iff_r_insert_eq_add_one  : 
  e ∉ M.cl X ↔ M.r (insert e X) = M.r X + 1 :=
⟨r_insert_eq_add_one_of_not_mem_cl, λ h, not_mem_cl_of_r_insert_gt (by {rw h, apply lt_add_one})⟩ 

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

lemma indep.not_mem_cl_iff (hI : M.indep I) : 
  x ∉ M.cl I ↔ x ∉ I ∧ M.indep (insert x I) :=  
sorry 

lemma indep_of_cl_diff_ne_forall (h : ∀ x ∈ I, M.cl (I \ {x}) ≠ M.cl I) :
  M.indep I :=
begin
  sorry, 
end 
   
lemma mem_cl_iff_exists_basis : 
  e ∈ M.cl X ↔ ∃ I, M.basis I X ∧ M.basis I (insert e X) :=  
begin
  rw mem_cl, sorry, 
end 

lemma mem_cl_iff_forall_basis : 
  e ∈ M.cl X ↔ ∀ I, M.basis I X ↔ M.basis I (insert e X) :=  
begin
  rw mem_cl, sorry, 
end 

lemma not_mem_cl_of_basis (hI : M.basis I X) (hI' : ¬M.basis I (insert e X)) :
  e ∉ M.cl X :=
sorry 

lemma basis_iff_not_mem_cl :
  e ∉ M.cl X ↔ e ∉ X ∧ ∃ I, M.basis I X ∧ M.indep (insert e I) := 
sorry 


lemma not_mem_cl_iff_exists_base : 
  e ∉ M.cl X ↔ e ∉ X ∧ ∃ B, M.base B ∧ e ∈ B ∧ ∀ B', M.base B' → B ∩ X ⊆ B' ∩ X → B' ∩ X = B ∩ X :=     
begin
  split, 
  { sorry},
  rintros ⟨heX, ⟨B, hB, heB, hBmax⟩⟩ he, 
  obtain ⟨I, hIBX, hI⟩ := (hB.indep.inter_right X).subset_basis_of_subset (inter_subset_right _ _),  
  obtain ⟨B',hB', hIB'⟩ := hI.indep,   
  have := (hBmax _ hB' (hIBX.trans (subset_inter hIB' hI.subset))), 
  
  -- rw mem_cl_iff_forall_basis.mp he at hI, 
  -- have hei : M.indep {e} := hB.indep.subset (by simpa), 
  -- obtain ⟨I, heI, ⟨B',hB',hIB'⟩, h⟩ := hei.subset_basis_of_subset (subset_union_left {e} X), 
  

  


end 

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

end matroid 

section from_axioms 

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
          (diff_singleton_ssubset hx.1)) hA},
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
      refine (diff_singleton_ssubset hyA).ne.symm (hAmin _ ⟨_,hA'⟩ (diff_subset _ _)), 
      exact (diff_subset _ _).trans_ssubset hAs},
   
  have ht : B₂ ⊆ _ := subset_trans _ (union_subset hss (subset_cl (B₁ \ {x}))),  
  { have ht' := cl_mono _ _ ht, 
    rw [hB₂.1, cl_idem, univ_subset_iff] at ht', 
    exact hB₁.2 _ (diff_singleton_ssubset hx.1) ht'},
  nth_rewrite 0 [←diff_union_inter B₂ B₁], 
  apply union_subset_union rfl.subset, 
  rintros y ⟨hy2,hy1⟩, 
  rw mem_diff_singleton, 
  use hy1, 
  rintro rfl, 
  exact hx.2 hy2, 
  end }

@[simp] lemma matroid_of_cl_apply (cl : set E → set E) 
  (subset_cl : ∀ X, X ⊆ cl X )
  (cl_mono : ∀ X Y, X ⊆ Y → cl X ⊆ cl Y )
  (cl_idem : ∀ X, cl (cl X) = cl X )
  (cl_exchange : ∀ X e f, f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X ) : 
(matroid_of_cl cl subset_cl cl_mono cl_idem cl_exchange).cl = cl :=
begin

  -- rw [←not_iff_not], 
  set M := matroid_of_cl cl subset_cl cl_mono cl_idem cl_exchange with hM, 
  apply funext, 
  by_contra' h, 
  obtain ⟨I,hI,hImin⟩ := finite.exists_minimal _ h,  
  have hI' : M.indep I, 
  { apply matroid.indep_of_cl_diff_ne_forall,
    by_contra' hI', 
    obtain ⟨x,hxI,hx⟩ := hI', 
    rw ←hx at hI, 
    have h' : M.cl (I \ {x}) = cl (I \ {x}), sorry, 
    apply hI, 
    refine subset_antisymm _ (hI _).elim,
    { rw h', apply cl_mono _ _ (diff_subset _ _),  }, 
    rw h' at hI,  
    have h'' := M.subset_cl I hxI, 
    rw [←hx, h'] at h'',  
    have hi' := insert_subset.mpr ⟨h'', subset_cl _⟩,  
    rw [insert_diff_singleton, insert_eq_of_mem hxI] at hi', 
    have hi'' := cl_mono _ _ hi', 
    rw [cl_idem] at hi'', 
    rw [hi''.antisymm (cl_mono _ _ (diff_subset _ _)), h']},

  simp_rw [set.ext_iff, not_forall, not_iff, hI'.not_mem_cl_iff, 
    matroid.indep_iff_subset_base, hM, matroid_of_cl] at hI, 
  obtain ⟨x,hx⟩ := hI,
  obtain hxI' | hxI' := em (x ∈ cl I), 
  { rw [(iff_true _).mpr hxI', iff_true] at hx, 
    obtain ⟨hxI, B', ⟨hB', hB'min⟩, hIxB'⟩ := hx,   
      
    apply hB'min _ (diff_singleton_ssubset (hIxB' (mem_insert x _))), 
    have hI' : I ⊆ B' \ {x}, 
      from subset_diff_singleton ((subset_insert _ _).trans hIxB') hxI,   
    have hx'' : x ∈ cl (B' \ {x}), 
      from cl_mono _ _ hI' hxI', 
    have hins := insert_subset.mpr ⟨hx'', subset_cl _⟩,  
    rw [insert_diff_singleton] at hins, 
    have hlast := cl_mono _ _ ((subset_insert _ B').trans hins), 
    rwa [hB', cl_idem, univ_subset_iff] at hlast},
  have h' := mt hx.1 hxI', 
  -- rw ←false_iff at hxI', 
  
  -- obtain ⟨B, ⟨hB, hBmax⟩, hIB⟩ := hI'
  simp_rw [not_and, not_exists, ne.def, not_and, and_imp] at h',  
  obtain ⟨B, hB, hBmin⟩ := finite.exists_minimal (λ B, insert x I ⊆ B ∧ cl B = univ) sorry,
  refine h' (λ hxI, hxI' (subset_cl I hxI)) _ hB.2 (λ X hXB hXcl, hXB.ne.symm _) hB.1, 
  -- apply hBmin, 
  
  

  


  
end 

end from_axioms
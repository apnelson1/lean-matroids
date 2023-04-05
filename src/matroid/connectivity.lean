import .dual 

open_locale classical 
open_locale big_operators
open set 

namespace matroid

variables {E ι : Type*} [finite E] {X Y X' Y'  I C : set E} {e f : E} {M : matroid E}

-- def Skew (M : matroid E) (X : ι → set E) := 
-- ∃ (I : ι → set E), (M.basis (⋃ i, I i) (⋃ i, X i)) ∧ 
--   (∀ i, M.basis (I i) (X i)) ∧ pairwise (disjoint on I) 

-- lemma Skew.disjoint_of_bases {X I : ι → set E} (hX : M.Skew X) (hI : ∀ i, M.basis (I i) (X i)) :
--   pairwise (disjoint on I) :=
-- begin

-- end 

-- def skew (M : matroid E) (X Y : set E) : Prop := 
--   ∃ I, M.basis I (X ∪ Y) ∧ M.basis (I ∩ X) X ∧ M.basis (I ∩ Y) Y ∧ disjoint (I ∩ X) (I ∩ Y) 

def skew (M : matroid E) (X Y : set E) : Prop :=
  ∀ (I ⊆ X) (J ⊆ Y), M.indep I → M.indep J → disjoint I J ∧ M.indep (I ∪ J) 

lemma skew_iff_r' :
  M.skew X Y ↔ M.r X + M.r Y = M.r (X ∪ Y) :=
begin
  refine ⟨λ h, _, λ h I hIX J hJY hI hJ, _⟩,
  { obtain ⟨⟨I,hI⟩,⟨J,hJ⟩⟩ := ⟨M.exists_basis X, M.exists_basis Y⟩, 
    obtain ⟨hdj, hIJ⟩ := h I hI.subset J hJ.subset hI.indep hJ.indep,  
    rw [hI.r_eq_card, hJ.r_eq_card, ←ncard_union_eq hdj, ←hIJ.r], 
    refine (M.r_mono (union_subset_union hI.subset hJ.subset)).antisymm _, 
    rw [←r_cl _ (I ∪ J), ←cl_union_cl_left_eq_cl_union, hI.cl, 
      ←cl_union_cl_right_eq_cl_union, hJ.cl, cl_union_cl_left_eq_cl_union, 
      cl_union_cl_right_eq_cl_union, r_cl] },
  have hdj : disjoint I J, 
  { rw [disjoint_iff_inter_eq_empty, ←ncard_eq_zero, ←(hI.inter_right J).r],
    have hsm := M.r_submod X Y, 
    rw [h,add_le_iff_nonpos_right, le_zero_iff] at hsm, 
    exact (nat.zero_le _).antisymm' ((M.r_mono (inter_subset_inter hIX hJY)).trans_eq hsm) },

  refine ⟨hdj, _⟩, 

  
end 

-- lemma skew.loop_of_inter (h : M.skew X Y) (he : e ∈ X ∩ Y) : M.loop e :=
-- begin
--   rw [loop_iff_dep, indep_iff_forall_subset_not_circuit], intro hi, 

--   obtain ⟨I, hI, hIX, hIY, hdj⟩ := h, 
--   have heI : e ∉ I, from λ heI, hdj.ne_of_mem ⟨heI,he.1⟩ ⟨heI,he.2⟩ rfl,
--   obtain ⟨CX, hCXe, hCX⟩ := exists_circuit_subset_of_dep
--     (hIX.insert_dep ⟨he.1,not_mem_subset (inter_subset_left _ _ ) heI⟩),  
--   obtain ⟨CY, hCYe, hCY⟩ := exists_circuit_subset_of_dep
--     (hIY.insert_dep ⟨he.2,not_mem_subset (inter_subset_left _ _ ) heI⟩),  

--   obtain ⟨C, hCss,hC⟩ := hCX.elimination hCY _ e, 
--   { refine (hC.dep (hI.indep.subset (hCss.trans _))).elim, 
--     rw [diff_subset_iff, singleton_union, union_subset_iff], 
--     exact ⟨hCXe.trans (insert_subset_insert (inter_subset_left _ _)),
--            hCYe.trans (insert_subset_insert (inter_subset_left _ _))⟩ },
    
--   rintro rfl, 
--   have hinter := subset_inter hCXe hCYe, 
--   rw [←insert_inter_distrib, hdj.inter_eq, insert_emptyc_eq] at hinter, 
--   exact hi CX hinter hCX, 
-- end 

-- lemma skew_iff_r : M.skew X Y ↔ M.r X + M.r Y = M.r (X ∪ Y) :=
-- begin
--   refine ⟨_, λ h, _⟩,
--   { rintro ⟨K, hK, hKX, hKY, hKdj⟩, 
--     rw [hK.r_eq_card, hKX.r_eq_card, hKY.r_eq_card, ←ncard_union_eq hKdj, 
--       ←inter_union_distrib_left, inter_eq_left_iff_subset.mpr hK.subset] },
--   obtain ⟨I,hI⟩ := M.exists_basis (X ∪ Y),
--   have hc := hI.r_eq_card, 
--   rw [←h, ←inter_eq_left_iff_subset.mpr hI.subset, inter_union_distrib_left] at hc, 
--   have hXY := hc.trans_le (ncard_union_le _ _), 
--   have hIX := M.r_mono (inter_subset_right I X), 
--   have hIY := M.r_mono (inter_subset_right I Y), 
--   have hXr := (hI.indep.inter_right X).r, 
--   have hYr := (hI.indep.inter_right Y).r,
--   have hX : M.r X = (I ∩ X).ncard, linarith, 
--   have hY : M.r Y = (I ∩ Y).ncard, linarith, 
--   have h_inter : ((I ∩ X) ∩ (I ∩ Y)).ncard = 0, 
--   by linarith [ncard_union_add_ncard_inter (I ∩ X) (I ∩ Y)], 
--   rw [ncard_eq_zero, ←disjoint_iff_inter_eq_empty] at h_inter, 
  
--   exact ⟨I,hI,
--     (hI.indep.inter_right X).basis_of_subset_of_r_le 
--       (inter_subset_right _ _) (hX.trans_le hXr.symm.le), 
--     (hI.indep.inter_right Y).basis_of_subset_of_r_le 
--       (inter_subset_right _ _) (hY.trans_le hYr.symm.le),
--     h_inter⟩    
-- end 

lemma skew_of_add_r_le (h : M.r X + M.r Y ≤ M.r (X ∪ Y)) : M.skew X Y :=
skew_iff_r.mpr (h.antisymm (M.r_union_le_add_r _ _))

lemma skew.symm (h : M.skew X Y) : M.skew Y X :=  
by rwa [skew_iff_r, add_comm, union_comm, ←skew_iff_r]



lemma skew.subset_left (h : M.skew X Y) (hX' : X' ⊆ X) : M.skew X' Y := 
begin

end 

-- lemma skew_iff_indep :
--   M.skew X Y ↔ ∀ (I ⊆ X) (J ⊆ Y), M.indep I → M.indep J → disjoint I J ∧ M.indep (I ∪ J) :=
-- begin
--   refine ⟨λ h I hIX J hJY hI hJ, ⟨_,_⟩, λ h, _⟩,
--   { obtain ⟨K, hK, hKX, hKY, hKdK⟩ := h, 
--     rw [disjoint_iff_forall_ne], 
--     rintro x hxI y hxJ rfl, 
--     },
-- end 







end matroid
import .basic

open set function 

namespace matroid_in

variables {α β : Type*}

def preimage (M : matroid_in β) [M.finite] (f : α → β) (hf : M.E ⊆ range f) :     
    matroid_in α := 
    matroid_of_indep_of_bdd (f ⁻¹' M.E) 
    (fun I, inj_on f I ∧ M.indep (f '' I)) 
    (by simp) 
    (fun I J ⟨hJ, hJ'⟩ hIJ, ⟨hJ.mono hIJ, hJ'.subset (image_subset _ hIJ)⟩)
    (begin
      rintro I B ⟨hIinj, hI⟩ (hInotmax : I ∉ maximals _ (set_of _)) 
        ((hBmax : B ∈ maximals _ (set_of _))), 
      simp only [mem_maximals_iff', mem_set_of_eq, and_imp, not_and, not_forall, exists_prop, 
        iff_true_intro hIinj, iff_true_intro hI, true_implies_iff] 
        at hInotmax hBmax, 
      have hnb : ¬ M.base (f '' I),
      { obtain ⟨I', hI'inj, hI', hII', hI'ne⟩ := hInotmax, 
        refine fun hIb, hI'ne _,
        have hfI := hIb.eq_of_subset_indep hI' (image_subset _ hII'), 
        refine hII'.antisymm (fun e heI', _), 
        have := (hI'inj.mem_image_iff subset.rfl heI').2 heI', 
        rwa [← hfI, hI'inj.mem_image_iff hII' heI'] at this },
      have hb : M.base (f '' B), 
      { apply hBmax.1.2.base_of_maximal (fun J hJ hBJ, hBJ.antisymm (fun e heJ, _)), 
        obtain ⟨e, he, rfl⟩ := (hJ.subset_ground.trans hf) heJ, 
        by_contra heBf, 
        have hcon := 
          hBmax.2 ((inj_on_insert (fun h', heBf (mem_image_of_mem f h'))).2 ⟨hBmax.1.1, heBf⟩)
            (hJ.subset _) (subset_insert _ _), 
        { rw [hcon] at heBf, exact heBf (mem_image_of_mem _ (mem_insert _ _)) },
        rw [image_insert_eq], 
        exact insert_subset.2 ⟨heJ, hBJ⟩},

      obtain ⟨_, ⟨⟨e, he, rfl⟩, heI⟩, heIi⟩ := hI.exists_insert_of_not_base hnb hb, 
      have heI' : e ∉ I := fun h',heI (mem_image_of_mem _ h'), 
      exact ⟨e, ⟨he,heI'⟩, (inj_on_insert heI').2 ⟨hIinj, heI⟩, by rwa image_insert_eq⟩,  
      end)
    ( begin
      obtain ⟨B, hB⟩ := M.exists_base, 
      refine ⟨B.ncard, fun I hI, 
        ⟨(M.ground_finite.subset hI.2.subset_ground).of_finite_image hI.1,_⟩⟩, 
      rw [←ncard_image_of_inj_on hI.1], 
      obtain ⟨B', hB'⟩ := hI.2.exists_base_supset,  
      have := ncard_le_of_subset hB'.2 (M.ground_finite.subset hB'.1.subset_ground), 
      rwa [hB.card_eq_card_of_base hB'.1], 
      end)
    ( fun I hI x hxI, hI.2.subset_ground (mem_image_of_mem _ hxI) )

def restrict' (M : matroid_in α) (X : set α) : matroid_in α :=
matroid_of_indep X (λ I, M.indep I ∧ I ⊆ X ∩ M.E) ⟨M.empty_indep, empty_subset _⟩ 
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
  { rw [dual_indep_iff_coindep, coindep_iff_exists], 
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
  rintro X hX I ⟨hI, hIX⟩ hIA, 
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset (subset_inter hIA hIX), 
  refine ⟨J, ⟨⟨hJ.indep,hJ.subset.trans (inter_subset_right _ _)⟩,hIJ,
    hJ.subset.trans (inter_subset_left _ _)⟩, λ B hB hJB, _⟩, 
  rw hJ.eq_of_subset_indep hB.1.1 hJB (subset_inter hB.2.2 hB.1.2), 
end)
(fun I hI, hI.2.trans (inter_subset_left _ _))   

lemma restrict'_indep_iff {M : matroid_in α} {X I : set α} : 
  (M.restrict' X).indep I ↔ M.indep I ∧ I ⊆ X := 
begin
  simp only [restrict', subset_inter_iff, matroid_of_indep_apply, and.congr_right_iff, 
    and_iff_left_iff_imp], 
  exact fun h _, h.subset_ground 
end 

def add_loop (M : matroid_in α) (f : α) : matroid_in α := M.restrict' (insert f M.E)

def add_coloop (M : matroid_in α) (f : α) : matroid_in α := (M﹡.add_loop f)﹡  

/-- extend `e` in `M` by a parallel element `f`. -/
def parallel_extend [decidable_eq α] (M : matroid_in α) [M.finite] (e f : α) (hf : f ∉ M.E) : 
    matroid_in α := 
  M.preimage ((@id α).update f e) (begin
    rintro x hx, 
    refine ⟨x, function.update_noteq _ _ _⟩, 
    rintro rfl, 
    exact hf hx
  end)

def series_extend [decidable_eq α] (M : matroid_in α) [M.finite] (e f : α) (hf : f ∉ M.E) :
    matroid_in α := (M﹡.parallel_extend e f hf)﹡ 

end matroid_in 
    


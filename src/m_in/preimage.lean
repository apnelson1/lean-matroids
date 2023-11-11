import .minor

open set function 

namespace matroid_in

variables {α β : Type*} 

section preimage

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

@[simp] lemma preimage_ground_eq (M : matroid_in β) [M.finite] (f : α → β) (hf : M.E ⊆ range f) : 
  (M.preimage f hf).E = f ⁻¹' M.E := rfl 

@[simp] lemma preimage_indep_iff (M : matroid_in β) [M.finite] (f : α → β) (hf : M.E ⊆ range f) 
  (I : set α) : (M.preimage f hf).indep I ↔ inj_on f I ∧ M.indep (f '' I) := by 
  simp [preimage]

end preimage

section restrict

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

@[simp] lemma restrict'_ground (M : matroid_in α) (X : set α) : (M.restrict' X).E = X := rfl 

end restrict 

section extensions

variables {M : matroid_in α} {e f : α} {I : set α}

def add_loop (M : matroid_in α) (f : α) : matroid_in α := M.restrict' (insert f M.E)

@[simp] lemma add_loop_ground (M : matroid_in α) (f : α) : (M.add_loop f).E = insert f M.E := rfl

@[simp] lemma add_loop_indep_iff : (M.add_loop f).indep I ↔ M.indep I := 
begin
  rw [add_loop, restrict'_indep_iff, and_iff_left_iff_imp],
  exact fun hI, hI.subset_ground.trans (subset_insert _ _), 
end 

lemma eq_add_loop_iff (M M' : matroid_in α) (hf : f ∉ M.E) : 
    M' = add_loop M f ↔ M'.loop f ∧ M' ⟍ f = M :=
begin
  rw [loop_iff_dep, dep_iff, singleton_subset_iff], 
  split, 
  { rintro rfl, 
    rw [add_loop_indep_iff, add_loop_ground, and_iff_left (mem_insert _ _), indep_singleton, 
      and_iff_right (show ¬M.nonloop f, from fun h, hf h.mem_ground), 
      eq_iff_indep_iff_indep_forall, delete_elem, delete_ground, add_loop_ground], 
    simp only [insert_diff_of_mem, mem_singleton, sdiff_eq_left, disjoint_singleton_right,  
      delete_indep_iff, add_loop_indep_iff, and_iff_left_iff_imp, and_iff_right hf],
    rintro I hI - hfI,
    exact (hI hfI).2 rfl },
  rintro ⟨hfl,rfl⟩,  
  apply eq_of_indep_iff_indep_forall _ (fun I hI, _), 
  { simp only [delete_elem, add_loop_ground, delete_ground, insert_diff_singleton],
    rw [insert_eq_of_mem hfl.2] },
  simp only [delete_elem, add_loop_indep_iff, delete_indep_iff, disjoint_singleton_right, 
    iff_self_and], 
  exact fun hI' hfI, hfl.1 (hI'.subset (singleton_subset_iff.2 hfI)), 
end 

def add_coloop (M : matroid_in α) (f : α) : matroid_in α := (M﹡.add_loop f)﹡  

lemma add_coloop_eq (M M' : matroid_in α) (hf : f ∉ M.E) : 
    M' = add_coloop M f ↔ M'.coloop f ∧ M' ⟍ f = M := 
begin
  rw [add_coloop, eq_dual_comm, eq_comm, eq_add_loop_iff _ _ (show f ∉ M﹡.E, from hf), 
    dual_loop_iff_coloop, eq_dual_comm, delete_elem, dual_delete_dual_eq_contract, 
    delete_elem, and.congr_right_iff, eq_comm], 
  intro hf', 
  rw [contract_eq_delete_of_subset_coloops], 
  rwa [singleton_subset_iff, ← coloop_iff_mem_cl_empty ], 
end 

lemma add_coloop_del_eq (M : matroid_in α) (hf : f ∉ M.E) : add_coloop M f ⟍ f = M := 
  (((M.add_coloop_eq _) hf).1 rfl).2

variable [decidable_eq α] 

/-- extend `e` in `M` by a parallel element `f`. -/
def parallel_extend (M : matroid_in α) [M.finite] (e f : α) (hf : f ∉ M.E) : 
    matroid_in α := 
  M.preimage ((@id α).update f e) (begin
    rintro x hx, 
    refine ⟨x, function.update_noteq _ _ _⟩, 
    rintro rfl, 
    exact hf hx
  end)

lemma parallel_extend_ground {M : matroid_in α} [M.finite] {e f : α}
  (he : e ∈ M.E) (hf : f ∉ M.E) : (M.parallel_extend e f hf).E = insert f M.E :=
begin
  simp only [matroid_in.preimage_ground_eq, matroid_in.parallel_extend.equations._eqn_1],
  refine subset_antisymm _ (insert_subset.2 ⟨by simpa, fun x hx, _⟩), 
  { rintro x hx, 
    simp only [set.mem_preimage] at hx,
    obtain (rfl | hx') := eq_or_ne x f, 
    { exact mem_insert _ _ },
    rw [update_apply, if_neg hx'] at hx, 
    exact or.inr hx },
  obtain (rfl | hx') := eq_or_ne x f,
  { simpa },
  rwa [mem_preimage, update_apply, if_neg hx'], 
end 

lemma image_update_id_apply (x y : α) (s : set α) [decidable (x ∈ s)] : 
  ((@id α).update x y) '' s = if x ∉ s then s else insert y (s \ {x}) := 
begin
  ext a, 
  simp only [set.mem_image, ite_not], 
  split_ifs, 
  { split, 
    { rintro ⟨x, hx, rfl⟩, 
      rw [update_apply], 
      split_ifs, exact mem_insert _ _, 
      exact or.inr ⟨hx, h_1⟩}, 
    rintro (rfl | ha), 
    { refine ⟨_, h, by simp⟩ },  
    refine ⟨a, ha.1, _⟩, 
    rw [function.update_noteq, id], 
    exact fun hax, ha.2 hax },
  refine ⟨_, fun ha, _⟩, 
  { rintro ⟨a, ha, rfl⟩,
    rwa [update_apply, if_neg, id], 
    exact fun hax, h (hax ▸ ha) },
  refine ⟨a, ha, _⟩, 
  rw [update_apply, if_neg, id], 
  exact fun hax, h (hax ▸ ha)
end 

lemma pair_subset_iff {x y : α} {s : set α} : {x,y} ⊆ s ↔ x ∈ s ∧ y ∈ s :=
  by rw [insert_subset, singleton_subset_iff]

lemma eq_parallel_extend (M M' : matroid_in α) [M.finite] {e f : α} (hM' : M'.circuit {e, f}) 
  (h : M = M' ⟍ f) (hMe : M.nonloop e) (hf : f ∉ M.E) : M' = M.parallel_extend e f hf :=
begin
  classical, 
  have hne : e ≠ f,
  { rintro rfl, exact hf (hMe.mem_ground), },
  apply eq_of_indep_iff_indep_forall, 
  { rw [parallel_extend_ground hMe.mem_ground hf, h, delete_elem, delete_ground, 
      insert_diff_singleton, eq_comm, insert_eq_self], 
    exact hM'.subset_ground (by simp) },
  simp only [parallel_extend, preimage_indep_iff], 
  refine fun I hIE, ⟨fun hI, ⟨fun x hxI y hyI hxy, _,_⟩, fun hI, _⟩, 
  { rw [update_apply, update_apply] at hxy, 
    split_ifs at hxy,
    { rw [h_1, h_2] },
    { subst hxy, subst h_1, 
      refine (hM'.dep.not_indep (hI.subset (show {y,x} ⊆ I, from _))).elim, 
      rw [insert_subset, singleton_subset_iff],
      exact ⟨hyI, hxI⟩ },
    { subst hxy; subst h_2, 
      refine (hM'.dep.not_indep (hI.subset (show {x,y} ⊆ I, from _))).elim, 
      rw [insert_subset, singleton_subset_iff],
      exact ⟨hxI, hyI⟩ },
    exact hxy },
  { rw [h, delete_elem, delete_indep_iff, disjoint_singleton_right, mem_image, 
      image_update_id_apply], 
    split_ifs, 
    { have heI : e ∉ I, 
      { exact fun heI, hM'.dep.not_indep 
          (hI.subset (insert_subset.2 ⟨heI, singleton_subset_iff.2 h_1⟩)) },
      refine ⟨_, _⟩, 
      { rw [indep_iff_forall_subset_not_circuit _], 
        { rintro C hCss hC, 
          have hne : C ≠ {e,f}, 
          { rintro rfl, 
            rw [pair_comm, insert_diff_singleton_comm ] at hCss, 
            { exact (hCss (mem_insert _ _)).2 rfl },
            rintro rfl; exact heI h_1 },
          obtain ⟨C', hC'ss, hC'⟩ := hC.elimination hM' hne e, 
          refine hC'.dep.not_indep (hI.subset (hC'ss.trans _)), 
          rw [diff_subset_iff, union_subset_iff, set.singleton_union, 
            insert_subset, and_iff_right (mem_insert _ _), singleton_subset_iff], 
          exact ⟨hCss.trans (insert_subset_insert (diff_subset _ _)), or.inr h_1⟩ },
        rw [insert_subset],
        exact ⟨hM'.subset_ground (mem_insert _ _), (diff_subset _ _).trans hIE⟩ },
      rintro ⟨x, hxI, hx⟩,    
      obtain (rfl | hxf) := eq_or_ne x f, 
      { simp only [function.update_same] at hx, subst hx, 
        exact heI hxI },
      rw [update_apply, if_neg hxf, id] at hx, 
      exact hxf hx },
    rw [and_iff_right hI], 
    rintro ⟨x, hxI, hx⟩, 
    have hne : x ≠ f := by rintro rfl; exact h_1 hxI, 
    rw [update_apply, if_neg hne] at hx, 
    exact hne hx },
  rw [image_update_id_apply, h, delete_elem, delete_indep_iff, disjoint_singleton_right] at hI, 
  split_ifs at hI, swap, 
  { exact hI.2.1 },
  rw [indep_iff_forall_subset_not_circuit], 
  rintro C hCI hC, 
  
  have hne : C ≠ {e,f},
  { rintro rfl, 
    rw [insert_subset, singleton_subset_iff] at hCI, 
    refine hne ((hI.1.eq_iff hCI.1 hCI.2).1 _),
    rw [update_same, update_apply, if_neg hne, id], }, 
  obtain ⟨C', hC'ss, hC'⟩ := hC.elimination hM' hne f, 
  refine hC'.dep.not_indep (hI.2.1.subset (hC'ss.trans _)), 
  simp only [set.diff_singleton_subset_iff, set.union_insert, set.union_singleton],
  rw [insert_comm f, insert_diff_singleton], 
  exact insert_subset_insert (insert_subset_insert hCI), 
end 

lemma parallel_extend_circuit [M.finite] (he : M.nonloop e) (hf : f ∉ M.E) : 
  (M.parallel_extend e f hf).circuit {e,f} :=
begin
  rw [circuit_iff_dep_forall_diff_singleton_indep, dep_iff, 
    parallel_extend_ground he.mem_ground, parallel_extend, preimage_indep_iff, 
    image_update_id_apply], 
  simp only [set.mem_insert_iff, set.mem_singleton, forall_eq_or_imp, not_and,
    set.insert_diff_of_mem, forall_eq, not_true, if_false, or_true], 
  have hef : e ≠ f := by rintro rfl; exact hf he.mem_ground,  
  refine ⟨⟨fun h, _,_⟩, _, _⟩, 
  { specialize h (mem_insert _ _) (show f ∈ {e,f}, by {rw pair_comm, apply mem_insert}), 
    rw [update_same, update_apply, if_neg hef, id] at h,
    exact (hef (h rfl)).elim },
  { rw [insert_subset, singleton_subset_iff],
    exact ⟨or.inr he.mem_ground, mem_insert _ _⟩ },
  { rw [diff_singleton_eq_self (by rwa mem_singleton_iff), preimage_indep_iff, 
      image_singleton, update_same, indep_singleton, and_iff_left he],
    apply inj_on_singleton  },
  rintro _ (rfl : a = f), 
  rwa [pair_comm, insert_diff_of_mem _ (show a ∈ {a}, by simp), diff_singleton_eq_self, 
    preimage_indep_iff, and_iff_right (inj_on_singleton _ _), image_singleton, 
    update_apply, if_neg hef, id, indep_singleton], 
  rwa [ne_comm] at hef, 
end 

def series_extend (M : matroid_in α) [M.finite] (e f : α) (hf : f ∉ M.E) :
    matroid_in α := (M﹡.parallel_extend e f hf)﹡ 

lemma eq_series_extend (M M' : matroid_in α) [M.finite] {e f : α} (hM' : M'.cocircuit {e, f}) 
  (he : e ∈ M.E) (h : M = M' ⟋ f) (hf : f ∉ M.E) (hMe : ¬ M.coloop e) : 
  M' = M.series_extend e f hf :=
begin
  rw [series_extend, eq_dual_comm, eq_comm], 
  apply eq_parallel_extend, 
  { rwa [dual_circuit_iff_cocircuit] },
  { rw [h, contract_elem, contract_dual_eq_dual_delete, delete_elem] },
  rwa [← dual_loop_iff_coloop, not_loop_iff (show e ∈ M﹡.E, from he)] at hMe,
end 

lemma cocircuit_contr_elem_eq_series_extend (M : matroid_in α) [M.finite] {e f : α} 
  (hM : M.cocircuit {e, f}) (he : e ∈ (M ⟋ f).E) (hf : f ∉ (M ⟋ f).E) (hMe : ¬ (M ⟋ f).coloop e) : 
  series_extend (M ⟋ f) e f hf = M :=
by { rw [eq_comm], exact eq_series_extend _ _  hM he rfl _ hMe }

-- lemma series_extend_cocircuit (M : matroid_in α) [M.finite] {e f : α} (he : e ∈ M.E) 
--   (hMe : ¬ M.coloop e) (hf : f ∉ M.E) : (series_extend M e f hf).cocircuit {e, f} := 
-- begin
  
-- end 

-- lemma series_extend_contr_eq (M : matroid_in α) {e f : α} (he : e ∈ M.E) (hf : f ∉ M.E) 
--   (hMe : ¬ M.coloop e) : M = (series_extend M he hf hMe) ⟋ f := sorry



end extensions

end matroid_in 
    


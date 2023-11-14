import .preimage

open set function 

namespace matroid_in

variables {α : Type*} {M : matroid_in α} {e f : α} {I : set α}

section add_loop

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

@[simp] lemma add_coloop_ground (M : matroid_in α) (f : α) : (M.add_coloop f).E = insert f M.E := rfl

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

end add_loop

section parallel

variable [decidable_eq α]

/-- extend `e` in `M` by a parallel element `f`. -/
def parallel_extend (M : matroid_in α) (e f : α) : matroid_in α := M.preimage ((@id α).update f e)
  
lemma parallel_extend_ground (he : e ∈ M.E) (f : α) : (M.parallel_extend e f).E = insert f M.E :=
begin
  simp only [parallel_extend, matroid_in.preimage_ground_eq], 
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

@[simp] lemma parallel_extend_self (M : matroid_in α) (e : α) : M.parallel_extend e e = M := by 
begin
  simp_rw [parallel_extend, eq_iff_indep_iff_indep_forall, preimage_indep_iff, 
    preimage_ground_eq], 
  rw [(show update (@id α) e e = id, by simp), preimage_id, and_iff_right rfl], 
  rintro I hI, 
  rw [image_id, and_iff_left (injective_id.inj_on I)], 
end 

/-- If `e ∉ M.E`, then `M.parallel_extend e f` has the junk value `M ⟍ f`. -/
lemma parallel_extend_not_mem (he : e ∉ M.E) (f : α) : M.parallel_extend e f = M ⟍ f := 
begin
  classical, 
  simp_rw [eq_iff_indep_iff_indep_forall, parallel_extend, preimage_ground_eq, 
    preimage_update injective_id, if_neg he, preimage_id, preimage_indep_iff, image_update, 
    image_id, id, delete_elem, delete_indep_iff, delete_ground, and_iff_right rfl, subset_diff, 
    disjoint_singleton_right, update_id_inj_on_iff], 
  rintro I ⟨hI, hfI⟩, 
  simp [if_neg hfI, hfI], 
end 

lemma parallel_extend_ground_eq_ite (M : matroid_in α) (e f : α) [decidable (e ∈ M.E)] : 
    (M.parallel_extend e f).E = if e ∈ M.E then insert f M.E else M.E \ {f} := 
begin
  split_ifs with he, 
  { rw [parallel_extend_ground he] },
  rw [parallel_extend_not_mem he, delete_elem, delete_ground], 
end 

/-- If `e` is a loop, then `M.parallel_extend e f` has the junk value `(M ⟍ f).add_loop f`. -/
lemma parallel_extend_loop (he : M.loop e) (f : α) : M.parallel_extend e f = (M ⟍ f).add_loop f := 
begin
  classical, 
  simp_rw [eq_iff_indep_iff_indep_forall, parallel_extend, preimage_ground_eq, 
    preimage_update injective_id, if_pos he.mem_ground, preimage_id, id, add_loop_ground, 
    delete_elem, delete_ground, and_iff_right rfl, add_loop_indep_iff, delete_indep_iff, 
    disjoint_singleton_right, insert_diff_singleton, preimage_indep_iff, image_update, 
    update_id_inj_on_iff, image_id], 
  refine fun I hI, _, 
  split_ifs, 
  { rw [iff_true_intro h, not_true, and_false, iff_false, true_implies_iff, not_and, not_imp],
    exact fun hi, false.elim ((hi.nonloop_of_mem (mem_insert _ _)).not_loop he) },
  simp [h], 
end 

lemma parallel_extend_delete_eq (M : matroid_in α) (e f : α) (hf : f ∉ M.E) : 
    (M.parallel_extend e f) ⟍ f = M := 
begin
  classical,
  obtain (he | he) := em' (e ∈ M.E), 
  { rwa [parallel_extend_not_mem he, delete_elem, delete_elem, delete_delete, union_singleton, 
      pair_eq_singleton, delete_eq_self_iff, disjoint_singleton_left],  },
  simp_rw [delete_elem, eq_iff_indep_iff_indep_forall, delete_ground, parallel_extend_ground he, 
    delete_indep_iff, subset_diff, disjoint_singleton_right, insert_diff_self_of_not_mem hf, 
    and_iff_right rfl, parallel_extend, preimage_indep_iff, image_update, 
    update_inj_on_iff, and_iff_right (injective_id.inj_on _)], 
  rintro I ⟨hIs, hfI⟩,  
  simp [if_neg hfI, hfI], 
end

lemma parallel_extend_indep_iff (he : M.nonloop e) (hf : f ∉ M.E) {I : set α} : 
    (M.parallel_extend e f).indep I ↔ 
      (f ∉ I ∧ M.indep I) ∨ (f ∈ I ∧ e ∉ I ∧ M.indep (insert e (I \ {f}))) := 
begin
  classical,
  rw [parallel_extend, preimage_indep_iff, update_inj_on_iff, 
    and_iff_right (injective_id.inj_on _), image_update, image_id, image_id], 
  split_ifs, 
  { rw [and_iff_right h, iff_true_intro h, true_implies_iff, not_true, false_and, false_or, 
      and_comm, and.congr_left_iff],  
    refine fun h, ⟨fun h' heI, hf _, fun h' x hxI, _⟩, 
    { rw [← h' _ heI rfl], exact he.mem_ground },
    rintro rfl, 
    exact (h' hxI).elim },
  rw [iff_false_intro h, false_implies_iff, and_true, ← not_true, not_not, true_and, not_true, 
    false_and, or_false], 
end 

lemma parallel_extend_circuit (he : M.nonloop e) (hf : f ∉ M.E) : 
    (M.parallel_extend e f).circuit {e,f} :=
begin
  simp_rw [circuit_iff_dep_forall_diff_singleton_indep, dep_iff, 
    parallel_extend_ground he.mem_ground, insert_subset, 
    and_iff_right (mem_insert_of_mem _ he.mem_ground), 
    and_iff_left (singleton_subset_iff.2 (mem_insert _ _)), mem_insert_iff, mem_singleton_iff, 
    parallel_extend_indep_iff he hf], 
  simp only [mem_insert_iff, or_true, not_true, false_and, eq_self_iff_true, mem_singleton_iff, 
  true_or, not_false_iff, mem_diff, true_and, not_not, forall_eq_or_imp, insert_diff_of_mem, 
  sdiff_sdiff_self, bot_eq_empty, insert_emptyc_eq, indep_singleton, forall_eq, or_false, he, 
    and_true],
  obtain (rfl | hne) := eq_or_ne e f, 
  { simp }, 
  simp only [hne.symm, false_and, not_false_iff, false_or, true_and], 
  rwa [← insert_diff_singleton_comm hne, diff_self, insert_emptyc_eq, indep_singleton], 
end 

lemma eq_parallel_extend_iff {M M' : matroid_in α} (he : M.nonloop e) (hf : f ∉ M.E) : 
    M' = M.parallel_extend e f ↔ M'.circuit {e,f} ∧ M' ⟍ f = M := 
begin
  split, 
  { rintro rfl, 
    exact ⟨parallel_extend_circuit he hf, M.parallel_extend_delete_eq e f hf⟩ },
  rintro ⟨hC, rfl⟩, 
  have hef := pair_subset_iff.1 hC.subset_ground, 
  have hne : e ≠ f := by {rintro rfl, exact hf he.mem_ground},  
  have heE : e ∈ (M' ⟍ f).E, 
  { rw [delete_elem, delete_ground, mem_diff], exact ⟨hef.1, hne⟩ },
  rw [eq_iff_indep_iff_indep_forall, parallel_extend_ground heE, delete_elem, delete_ground, 
    insert_diff_singleton, eq_comm, insert_eq_self, and_iff_right hef.2], swap, 
  
  simp_rw [←delete_elem, parallel_extend_indep_iff he hf, delete_elem, delete_indep_iff, 
    disjoint_singleton_right], 
  simp only [mem_insert_iff, not_mem_diff_singleton, or_false, 
    and_iff_left (show ¬ (f = e) , from hne.symm)], 
  refine fun I hI, _, 
  obtain (hfI | hfI) := em (f ∈ I), 
  { simp only [hfI, not_true, and_false, true_and, false_or],
    refine ⟨λ h, ⟨fun heI, _, _⟩, λ h, _⟩,
    { exact hC.dep.not_indep (h.subset (pair_subset_iff.2 ⟨heI, hfI⟩)) },
    { rw [indep_iff_forall_subset_not_circuit', insert_subset, and_iff_right hef.1, 
        and_iff_left ((diff_subset _ _).trans hI)],
      rintro C' hC'ss hC', 
      have hCne : C' ≠ {e,f},
      { rintro rfl, obtain (rfl | h') := hC'ss (or.inr rfl), exact hne rfl, exact h'.2 rfl }, 
      obtain ⟨C₀, hC₀ss, hC₀⟩ := hC'.elimination hC hCne e, 
      refine hC₀.dep.not_indep (h.subset (hC₀ss.trans _)), 
      rw [diff_subset_iff, union_subset_iff, insert_subset, 
        and_iff_right (show e ∈ {e} ∪ I, from or.inl rfl), singleton_subset_iff, 
        and_iff_left (show f ∈ {e} ∪ I, from or.inr hfI), singleton_union] , 
      exact hC'ss.trans (insert_subset_insert (diff_subset _ _)) },
    rw [indep_iff_forall_subset_not_circuit], 
    rintro C' hC'ss hC', 
    have hCne : C' ≠ {e,f},
    { rintro rfl, exact h.1 (pair_subset_iff.1 hC'ss).1, },
    obtain ⟨C₀, hC₀ss, hC₀⟩ := hC'.elimination hC hCne f, 
    rw [union_insert, union_singleton, insert_comm, insert_diff_of_mem _ (by simp : f ∈ {f})] 
      at hC₀ss, 
    
    refine hC₀.dep.not_indep (h.2.subset (hC₀ss.trans _)), 
    rw [insert_diff_singleton_comm hne], 
    exact (diff_subset_diff_left (insert_subset_insert hC'ss)) },
  simp [hfI], 
end 

end parallel

section series

variable [decidable_eq α]

/-- extend `e` in `M` by an element `f` in series. -/
def series_extend (M : matroid_in α) (e f : α) : matroid_in α := (M﹡.parallel_extend e f)﹡ 

lemma series_extend_ground (he : e ∈ M.E) : (M.series_extend e f).E = insert f M.E :=
by simp [series_extend, parallel_extend_ground (show e ∈ M﹡.E, from he)]
  
@[simp] lemma series_extend_self (M : matroid_in α) (e : α) : M.series_extend e e = M := 
by simp [series_extend]

lemma series_extend_not_mem (he : e ∉ M.E) (f : α) : M.series_extend e f = M ⟋ f := 
by rw [series_extend, parallel_extend_not_mem (show e ∉ M﹡.E, from he), 
    delete_elem, contract_elem, dual_delete_dual_eq_contract]

lemma series_extend_contract_eq (M : matroid_in α) (e f : α) (hf : f ∉ M.E) : 
  (M.series_extend e f) ⟋ f = M := 
dual_inj 
  (by rwa [series_extend, contract_elem, dual_contract_dual_eq_delete, ← delete_elem, 
    parallel_extend_delete_eq ])

lemma series_extend_cocircuit (heE : e ∈ M.E) (he : ¬ M.coloop e) (hf : f ∉ M.E) : 
  (M.series_extend e f).cocircuit {e,f} :=
begin
  have hnl : M﹡.nonloop e,
  { rw [nonloop, dual_loop_iff_coloop], exact ⟨he, heE⟩ },
  rw [←dual_circuit_iff_cocircuit ],
  convert parallel_extend_circuit hnl hf, 
  rw [eq_comm, eq_dual_comm], 
  refl, 
end

lemma eq_series_extend_iff {M M' : matroid_in α} (heE : e ∈ M.E) (he : ¬M.coloop e) (hf : f ∉ M.E) : 
  M' = M.series_extend e f ↔ M'.cocircuit {e,f} ∧ M' ⟋ f = M := 
begin
  have hnl : M﹡.nonloop e,
  { rw [nonloop, dual_loop_iff_coloop], exact ⟨he, heE⟩ },
  rw [series_extend, ← dual_circuit_iff_cocircuit, ← dual_inj_iff, dual_dual, 
    eq_parallel_extend_iff hnl (show f ∉ M﹡.E, from hf), eq_dual_comm, delete_elem, 
    dual_delete_dual_eq_contract, ← contract_elem, eq_comm], 
end 

end series


end matroid_in 
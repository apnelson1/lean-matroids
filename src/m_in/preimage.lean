import .minor

open set function 

variables {α β : Type*} 

section update

variables [decidable_eq α] {f : α → β} {s : set α} {a : α} {b : β}

@[simp] lemma image_update (a : α) (f : α → β) (s : set α) (b : β) [decidable (a ∈ s)] :
  (f.update a b) '' s = if a ∈ s then insert b (f '' (s \ {a})) else f '' s :=
begin
  split_ifs, 
  { rw [subset_antisymm_iff, image_subset_iff], 
    refine ⟨λ x hxs, (em (x = a)).elim (fun heq, _) (fun hne, or.inr _), λ x, _⟩,
    { rw [mem_preimage, update_apply, if_pos heq]; exact mem_insert _ _ },
    { exact ⟨x, ⟨hxs, hne⟩, by rw [update_noteq hne]⟩ },
    rintro (rfl | ⟨x, hx, rfl⟩), 
    { use a, simpa },
    exact ⟨x, hx.1, update_noteq hx.2 _ _⟩ },
  rw [subset_antisymm_iff, image_subset_iff, image_subset_iff], 
  refine ⟨fun x hxs, ⟨x, hxs, _⟩, fun x hxs, ⟨x, hxs, _⟩⟩;
  { rw [update_noteq], exact fun hxa, h (by rwa ← hxa) },
end 

lemma preimage_update  {f : α → β} (hf : f.injective) (a : α) (b : β) (s : set β) 
  [decidable (b ∈ s)] :
  (f.update a b) ⁻¹' s = if b ∈ s then insert a (f ⁻¹' (s \ {f a})) else (f ⁻¹' (s \ {f a})) := 
begin
  split_ifs, 
  { rw [subset_antisymm_iff, insert_subset, set.mem_preimage, function.update_same, 
      set.preimage_diff, and_iff_right h, diff_subset_iff, 
      (show {f a} = f '' {a}, by rw [image_singleton]), 
      preimage_image_eq _ hf, singleton_union, insert_diff_singleton],
    refine ⟨fun x hx, _, fun x hx, _⟩, 
    { obtain (rfl | hxa) := eq_or_ne x a,
      { rw [mem_preimage, update_same] at hx,
        apply mem_insert },
      rw [mem_preimage, update_noteq hxa] at hx, 
      exact mem_insert_of_mem _ hx },
    obtain (rfl | hxa) := eq_or_ne x a,
    { exact mem_insert _ _ },
    rw [mem_insert_iff, mem_preimage, update_noteq hxa], 
    exact or.inr hx },
  refine subset_antisymm (fun x hx, _) (fun x hx, _), 
  { obtain (rfl | hxa) := eq_or_ne x a,
    { exact (h (by simpa using hx)).elim },
    rw [mem_preimage, update_noteq hxa] at hx, 
    exact ⟨hx, by rwa [mem_singleton_iff, hf.eq_iff], ⟩ }, 
  rw [mem_preimage, mem_diff, mem_singleton_iff, hf.eq_iff] at hx, 
  rw [mem_preimage, update_noteq hx.2], 
  exact hx.1, 
end 

lemma image_update_id_apply (x y : α) (s : set α) [decidable (x ∈ s)] : 
  ((@id α).update x y) '' s = if x ∉ s then s else insert y (s \ {x}) := by simp

lemma pair_subset_iff {x y : α} {s : set α} : {x,y} ⊆ s ↔ x ∈ s ∧ y ∈ s :=
  by rw [insert_subset, singleton_subset_iff]

lemma update_injective (hf : f.injective) (a : α) (h : b ∉ range f) : (f.update a b).injective := 
begin
  rintro x y hy, 
  rw [update_apply, update_apply] at hy, 
  split_ifs at hy, 
  { rw [h_1,h_2] },
  { exact (h ⟨y, hy.symm⟩).elim },
  { exact (h ⟨x, hy⟩).elim },
  exact hf.eq_iff.1 hy, 
end 

lemma update_inj_on_iff : 
  inj_on (f.update a b) s ↔ inj_on f (s \ {a}) ∧ (a ∈ s → ∀ x ∈ s, f x = b → x = a) :=
begin
  refine ⟨fun h, ⟨fun x hx y hy hxy, h hx.1 hy.1 _, _⟩, fun h x hx y hy hxy, _⟩,
  { rwa [update_noteq hx.2, update_noteq hy.2] },
  { rintro has x hxs rfl, 
    exact by_contra (fun hne, hne (h hxs has (by rw [update_same, update_noteq hne]))) },
  obtain ⟨(rfl | hxa), (rfl | hya)⟩ := ⟨eq_or_ne x a, eq_or_ne y a⟩, 
  { refl },
  { rw [function.update_same, update_noteq hya, eq_comm] at hxy, 
    rw [h.2 hx y hy hxy] },
  { rw [function.update_same, update_noteq hxa] at hxy,
    rw [h.2 hy x hx hxy] },
  rwa [function.update_noteq hxa, function.update_noteq hya, h.1.eq_iff ⟨hx, hxa⟩ ⟨hy,hya⟩] at hxy
end 

@[simp] lemma update_id_inj_on_iff {a b : α} : 
    inj_on ((@id α).update a b) s ↔ (a ∈ s → b ∈ s → a = b) := 
begin
  rw [update_inj_on_iff, and_iff_right (injective_id.inj_on _)], 
  refine ⟨fun h has hbs, (h has b hbs rfl).symm, _⟩, 
  rintro h has _ hbs rfl, 
  exact (h has hbs).symm, 
end 
 
end update

namespace matroid_in

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

@[simp] lemma restrict'_indep_iff {M : matroid_in α} {X I : set α} : 
  (M.restrict' X).indep I ↔ M.indep I ∧ I ⊆ X := 
begin
  simp only [restrict', subset_inter_iff, matroid_of_indep_apply, and.congr_right_iff, 
    and_iff_left_iff_imp], 
  exact fun h _, h.subset_ground 
end 

@[simp] lemma restrict'_ground (M : matroid_in α) (X : set α) : (M.restrict' X).E = X := rfl 

end restrict 

section bij_on

/-- If `f` maps `s` bijectively to `t` and, then for any `s ⊆ s₁` and `t ⊆ t' ⊆ f '' s₁`,
  there is some `s ⊆ s' ⊆ s₁` so that `f` maps `s'` bijectively to `t'`. -/
theorem set.bij_on.extend_of_subset {f : α → β} {s s₁ : set α} {t t' : set β}
    (h : bij_on f s t) (hss₁ : s ⊆ s₁) (htt' : t ⊆ t') (ht' : t' ⊆ f '' s₁) :
    ∃ s', s ⊆ s' ∧ s' ⊆ s₁ ∧ bij_on f s' t' :=
begin
  have hex : ∀ (b : (t' \ t)),  ∃ a, a ∈ s₁ \ s ∧ f a = b,
  { rintro ⟨b, hb⟩,
    obtain ⟨a, ha, rfl⟩ := ht' hb.1,
    exact ⟨_, ⟨ha, fun has, hb.2 (h.maps_to has)⟩, rfl⟩ }, 
  choose g hg using hex,
  have hinj : inj_on f (s ∪ range g),
  { rw [inj_on_union, and_iff_right h.inj_on, and_iff_left],
    { rintro _ ⟨⟨x,hx⟩, rfl⟩ _ ⟨⟨x', hx'⟩,rfl⟩ hf,
      simp only [(hg _).2, (hg _).2] at hf,
      rw [subtype.coe_mk, subtype.coe_mk] at hf, 
      subst hf },
    { rintro x hx _ ⟨⟨y,hy⟩, hy', rfl⟩ h_eq,
      rw [(hg _).2] at h_eq,
      obtain (rfl : _ = y) := h_eq,
      exact hy.2 (h.maps_to hx), },
    rw [disjoint_iff_forall_ne],
    rintro x hx _ ⟨y, hy, rfl⟩ rfl,
    have h' := h.maps_to hx,
    rw [(hg _).2] at h',
    exact y.prop.2 h' },
  have hp : bij_on f (range g) (t' \ t),
  { apply bij_on.mk,
    { rintro _ ⟨x, hx, rfl⟩; rw [(hg _).2]; exact x.2}, 
    { exact hinj.mono (subset_union_right _ _), },
    exact fun x hx, ⟨g ⟨x,hx⟩, by simp [(hg _).2] ⟩,}, 
  refine ⟨s ∪ range g, subset_union_left _ _, union_subset hss₁  _, _⟩,
  { rintro _ ⟨x, hx, rfl⟩; exact (hg _).1.1 }, 
  convert h.union hp _,
  { exact (union_diff_cancel htt').symm }, 
  exact hinj,
end 

theorem set.bij_on.extend {f : α → β} {s : set α} {t t' : set β} (h : bij_on f s t) (htt' : t ⊆ t')
    (ht' : t' ⊆ range f) : ∃ s', s ⊆ s' ∧ bij_on f s' t' := by
  simpa using h.extend_of_subset (subset_univ s) htt' (by simpa)

end bij_on

section preimage

/-- The pullback of a matroid on `β` by a function `f : α → β` to a matroid on `α`.
  Elements with the same image are parallel and the ground set is `f ⁻¹' M.E`. -/
def preimage (M : matroid_in β) (f : α → β) : matroid_in α := matroid_of_indep
  (f ⁻¹' M.E) (fun I, M.indep (f '' I) ∧ inj_on f I) ( by simp )
  ( fun I J ⟨h, h'⟩ hIJ, ⟨h.subset (image_subset _ hIJ), inj_on.mono hIJ h'⟩ )
  ( begin
    rintro I B ⟨hI, hIinj⟩ hImax hBmax,
    change I ∉ maximals _ {I : set α  | _} at hImax, 
    change B ∈ maximals _ {I : set α  | _} at hBmax, 
    simp only [mem_maximals_iff', mem_set_of_eq, hI, hIinj, and_self, and_imp,
      true_and, not_forall, exists_prop, not_and] at hImax hBmax,
    
    obtain ⟨I', hI', hI'inj, hII', hne⟩ := hImax,

    have h₁ : ¬(M.restrict' (set.range f)).base (f '' I),
    { refine fun hB, hne _,
      have h_im := hB.eq_of_subset_indep _ (image_subset _ hII'),
      { refine hII'.antisymm (fun x hxI', _), 
        rw [← hI'inj.mem_image_iff hII' hxI', h_im], 
        exact mem_image_of_mem _ hxI' },
      rwa [restrict'_indep_iff, and_iff_left (image_subset_range _ _)] }, 


    have h₂ : (M.restrict' (range f)).base (f '' B),
    { refine indep.base_of_maximal (by simpa using hBmax.1.1) (fun J hJi hBJ, _),
      simp only [restrict'_indep_iff] at hJi,
      obtain ⟨J₀, hBJ₀, hJ₀⟩ := hBmax.1.2.bij_on_image.extend hBJ hJi.2, 
      obtain rfl := hJ₀.image_eq,
      rw [hBmax.2 hJi.1 hJ₀.inj_on hBJ₀]}, 

    obtain ⟨_, ⟨⟨e, he, rfl⟩, he'⟩, hei⟩ := indep.exists_insert_of_not_base (by simpa) h₁ h₂,
    have heI : e ∉ I := fun heI, he' (mem_image_of_mem f heI),
    rw [← image_insert_eq, restrict'_indep_iff] at hei,
    exact ⟨e, ⟨he, heI⟩, hei.1, (inj_on_insert heI).2 ⟨hIinj, he'⟩⟩,
  end )
  ( begin
    
    rintro X - I ⟨hI, hIinj⟩ hIX,
    obtain ⟨J, hJ, hIJ⟩ := 
      (show (M.restrict' (range f)).indep (f '' I), by simpa).subset_basis_of_subset
      (image_subset _ hIX) (image_subset_range _ _), 
    
    simp only [basis_iff, restrict'_indep_iff] at hJ, 

    obtain ⟨J₀, hIJ₀, hJ₀X, hbij⟩ := hIinj.bij_on_image.extend_of_subset hIX hIJ hJ.2.1, 
    use J₀, 
    simp only [mem_maximals_iff', mem_set_of_eq], 
    rw [and_iff_left hbij.inj_on, hbij.image_eq, and_iff_right hJ.1.1, and_iff_right hIJ₀, 
      and_iff_right hJ₀X], 
    rintro K ⟨⟨hK, hKinj⟩, hIK, hKX⟩ hJ₀K, 
    obtain rfl := hJ.2.2 _ ⟨hK, image_subset_range _ _⟩ _ (image_subset _ hKX),  
    { refine hJ₀K.antisymm (fun x hxK, _),
      rwa [← hKinj.mem_image_iff hJ₀K hxK, hbij.image_eq, hKinj.mem_image_iff subset.rfl hxK] },
    rw [← hbij.image_eq ], 
    exact image_subset _ hJ₀K, 
  end )
  (  fun I hI e heI, hI.1.subset_ground ⟨e, heI, rfl⟩  )

@[simp] lemma preimage_ground_eq (M : matroid_in β) (f : α → β) : (M.preimage f).E = f ⁻¹' M.E :=
rfl

@[simp] lemma preimage_indep_iff {M : matroid_in β} {f : α → β} {I : set α} : 
    (M.preimage f).indep I ↔ M.indep (f '' I) ∧ inj_on f I :=
by simp [preimage]

end preimage

end matroid_in 
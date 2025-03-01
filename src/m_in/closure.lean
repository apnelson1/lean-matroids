import .restriction
import mathlib.data.set.basic 

noncomputable theory
open_locale classical
open_locale big_operators

open set

namespace matroid_in

variables {α : Type*} {M : matroid_in α} {I J B C X Y : set α} {e f x y : α}

/-- A flat is a maximal set having a given basis  -/
def flat (M : matroid_in α) (F : set α) : Prop := 
(∀ ⦃I X⦄, M.basis I F → M.basis I X → X ⊆ F) ∧ F ⊆ M.E  

lemma ground_flat (M : matroid_in α) : M.flat M.E := 
⟨λ _ _ _, basis.subset_ground, subset.rfl⟩

/-- The closure of a subset of the ground set is the intersection of the flats containing it. 
  A set `X` that doesn't satisfy `X ⊆ M.E` has the junk value `M.cl X := M.cl (X ∩ M.E)`. -/
def cl (M : matroid_in α) (X : set α) : set α := ⋂₀ {F | M.flat F ∧ X ∩ M.E ⊆ F} 

lemma cl_def (M : matroid_in α) (X : set α) : M.cl X = ⋂₀ {F | M.flat F ∧ X ∩ M.E ⊆ F} := rfl

lemma cl_eq_sInter_of_subset (X : set α) (hX : X ⊆ M.E . ssE) : 
  M.cl X = ⋂₀ {F | M.flat F ∧ X ⊆ F} :=
by rw [cl, inter_eq_self_of_subset_left hX]

lemma cl_eq_cl_inter_ground (M : matroid_in α) (X : set α) : M.cl X = M.cl (X ∩ M.E) :=
by rw [cl_def, cl_eq_sInter_of_subset]

lemma inter_ground_subset_cl (M : matroid_in α) (X : set α) : X ∩ M.E ⊆ M.cl X := 
by { rw [cl_eq_cl_inter_ground], simp [cl_def] }

@[ssE_finish_rules] lemma cl_subset_ground (M : matroid_in α) (X : set α) : M.cl X ⊆ M.E := 
begin
  apply sInter_subset_of_mem, 
  simp only [mem_set_of_eq, inter_subset_right, and_true], 
  apply ground_flat, 
end 

lemma mem_cl_iff_forall_mem_flat (X : set α) (hX : X ⊆ M.E . ssE) : 
  e ∈ M.cl X ↔ ∀ F, M.flat F → X ⊆ F → e ∈ F :=
by simp_rw [cl_eq_sInter_of_subset, mem_sInter, mem_set_of_eq, and_imp]

lemma subset_cl (M : matroid_in α) (X : set α) (hX : X ⊆ M.E . ssE) : X ⊆ M.cl X :=
by { rw [cl_eq_sInter_of_subset, subset_sInter_iff], simp }

lemma flat.cl {F : set α} (hF : M.flat F) : M.cl F = F :=
(sInter_subset_of_mem (by simpa)).antisymm (M.subset_cl F hF.2)
/- `cl_flat` was previously commented out.
    It is now uncommented for `loop.mem_flat` -/
  
@[simp] lemma cl_ground (M : matroid_in α) : M.cl M.E = M.E := 
(cl_subset_ground M M.E).antisymm (M.subset_cl _)
  
@[simp] lemma cl_univ (M : matroid_in α) : M.cl univ = M.E := 
by rw [cl_eq_cl_inter_ground, univ_inter, cl_ground]

@[simp] lemma cl_cl (M : matroid_in α) (X : set α) : M.cl (M.cl X) = M.cl X :=
begin
  nth_rewrite 2 cl_eq_cl_inter_ground, 
  nth_rewrite 1 cl_eq_cl_inter_ground, 
  refine (M.subset_cl _ (cl_subset_ground _ _)).antisymm' (λ e he, _), 
  rw mem_cl_iff_forall_mem_flat at *,
  refine λ F hF hXF, he _ hF (λ f hf, _), 
  rw mem_cl_iff_forall_mem_flat at hf, 
  exact hf _ hF hXF, 
end

lemma cl_subset (M : matroid_in α) (h : X ⊆ Y) : M.cl X ⊆ M.cl Y :=
begin
  rw [cl_eq_cl_inter_ground, M.cl_eq_cl_inter_ground Y], 
  refine sInter_subset_sInter _, 
  simp only [ground_inter_left, set_of_subset_set_of, and_imp],
  exact λ F hF hiF, ⟨hF, subset_trans (inter_subset_inter_left _ h) hiF⟩, 
end

lemma cl_mono (M : matroid_in α) : monotone M.cl :=
begin
  intros X Y h,
  nth_rewrite 1 cl_eq_cl_inter_ground,
  rw cl_eq_cl_inter_ground,
  apply cl_subset,
  exact inter_subset_inter_left M.E h
end

lemma cl_subset_cl (hXY : X ⊆ M.cl Y) : M.cl X ⊆ M.cl Y :=
by simpa only [cl_cl] using M.cl_subset hXY

lemma cl_subset_cl_iff_subset_cl' : (X ⊆ M.E ∧ M.cl X ⊆ M.cl Y) ↔ X ⊆ M.cl Y :=
⟨λ h, (M.subset_cl _ h.1).trans h.2, λ h, ⟨h.trans (cl_subset_ground _ _), cl_subset_cl h⟩ ⟩

lemma cl_subset_cl_iff_subset_cl (hX : X ⊆ M.E . ssE) : M.cl X ⊆ M.cl Y ↔ X ⊆ M.cl Y :=
begin
  nth_rewrite 1 [←cl_subset_cl_iff_subset_cl'], 
  rw [and_iff_right hX],
end

lemma subset_cl_of_subset (M : matroid_in α) (hXY : X ⊆ Y) (hY : Y ⊆ M.E . ssE) : X ⊆ M.cl Y :=
hXY.trans (M.subset_cl Y hY)

lemma mem_cl_of_mem (M : matroid_in α) (h : x ∈ X) (hX : X ⊆ M.E . ssE) : x ∈ M.cl X :=
(M.subset_cl X hX) h

lemma mem_cl_of_mem' (M : matroid_in α) (h : e ∈ X) (hX : e ∈ M.E . ssE) : e ∈ M.cl X :=
by { rw [cl_eq_cl_inter_ground], apply mem_cl_of_mem, exact ⟨h, hX⟩ }

lemma cl_insert_eq_of_mem_cl (he : e ∈ M.cl X) : M.cl (insert e X) = M.cl X :=
begin
  refine (M.cl_mono (subset_insert _ _)).antisymm' _,
  rw [←M.cl_cl X],
  rw cl_eq_cl_inter_ground,
  nth_rewrite 2 cl_eq_cl_inter_ground,
  apply cl_subset,
  rintros x ⟨h | h, hx⟩,
  { rw [h, ← cl_eq_cl_inter_ground],
      exact he },
  { apply subset_cl, use [h, hx] }
end 


@[simp] lemma cl_union_cl_right_eq (M : matroid_in α) (X Y : set α) :
  M.cl (X ∪ M.cl Y) = M.cl (X ∪ Y) :=
begin
  refine subset_antisymm _ _, 
  { rw [cl_eq_cl_inter_ground, inter_distrib_right, ←cl_cl _ (X ∪ Y) ],
    refine M.cl_subset 
      (union_subset ((inter_ground_subset_cl _ _).trans (cl_subset _ (subset_union_left _ _))) _), 
      rw [ground_inter_left], 
      exact (cl_subset _ (subset_union_right _ _)) },
  rw [cl_eq_cl_inter_ground, inter_distrib_right], 
  exact cl_subset _ (union_subset ((inter_subset_left _ _).trans (subset_union_left _ _)) 
    ((inter_ground_subset_cl _ _).trans (subset_union_right _ _))), 
end

@[simp] lemma cl_union_cl_left_eq (M : matroid_in α) (X Y : set α) :
  M.cl (M.cl X ∪ Y) = M.cl (X ∪ Y) :=
by rw [union_comm, cl_union_cl_right_eq, union_comm]

@[simp] lemma cl_cl_union_cl_eq_cl_union (M : matroid_in α) (X Y : set α) :
  M.cl (M.cl X ∪ M.cl Y) = M.cl (X ∪ Y) :=
by rw [cl_union_cl_left_eq, cl_union_cl_right_eq]

@[simp] lemma cl_insert_cl_eq_cl_insert (M : matroid_in α) (e : α) (X : set α) :
  M.cl (insert e (M.cl X)) = M.cl (insert e X) :=
by simp_rw [←singleton_union, cl_union_cl_right_eq]

@[simp] lemma cl_diff_loops_eq_cl (M : matroid_in α) (X : set α) : M.cl (X \ M.cl ∅) = M.cl X :=
by rw [←union_empty (X \ M.cl ∅), ←cl_union_cl_right_eq, diff_union_self, 
    cl_union_cl_right_eq, union_empty]

lemma mem_cl_self (M : matroid_in α) (e : α) (he : e ∈ M.E . ssE) : e ∈ M.cl {e} :=
singleton_subset_iff.mp (M.subset_cl {e} (singleton_subset_iff.mpr he))
/- need the assumption `e ∈ M.E` for otherwise
  `e ∉ M.E` but `e ∈ M.cl {e} ⊆ M.E`, a contradiction -/

lemma indep.cl_eq_set_of_basis (hI : M.indep I) : M.cl I = {x | M.basis I (insert x I)} :=
begin
  set F := {x | M.basis I (insert x I)} with hF, 

  have hIF : M.basis I F,
  { rw basis_iff, 
    refine ⟨hI, (λ e he, by { rw [hF, mem_set_of, insert_eq_of_mem he], exact hI.basis_self }), 
      λ J hJ hIJ hJF, hIJ.antisymm (λ e he, _)⟩,
    rw basis.eq_of_subset_indep (hJF he) (hJ.subset (insert_subset.mpr ⟨he, hIJ⟩)) 
      (subset_insert _ _) subset.rfl, 
    exact mem_insert _ _,
    rw hF, rintros e ⟨_, he⟩,
    rw ←singleton_union at he,
    exact singleton_subset_iff.mp (union_subset_iff.mp he).1 },
  
  have hF : M.flat F, 
  {
    refine ⟨
      λ J Y hJF hJY y hy, (indep.basis_of_forall_insert hI (subset_insert _ _) (λ e he, _) (insert_subset.mpr ⟨hJY.subset_ground hy, by ssE⟩)),
      hIF.subset_ground
    ⟩,
    refine (basis.insert_dep (hIF.transfer hJF (subset_union_right _ _) (hJY.basis_union hJF)) (mem_of_mem_of_subset he _)).1,
    rw [diff_subset_iff, union_diff_self, insert_subset], 
    simp only [mem_union, subset_union_left, and_true],
    right, left, exact hy
  },

  rw [subset_antisymm_iff, cl, subset_sInter_iff],
  refine ⟨sInter_subset_of_mem ⟨hF, (inter_subset_left I M.E).trans hIF.subset⟩, _⟩,
  rintro F' ⟨hF', hIF'⟩ e (he : M.basis I (insert e I)),
  rw (inter_eq_left_iff_subset.mpr (hIF.subset.trans hIF.subset_ground)) at hIF',
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset hIF' hF'.2,

  exact (hF'.1 hJ (he.basis_union_of_subset hJ.indep hIJ)) (or.inr (mem_insert _ _)),
end

lemma cl_diff_self_eq_cl_inter_ground_diff (M : matroid_in α) : 
  M.cl X \ X = M.cl (X ∩ M.E) \ (X ∩ M.E) :=
begin
  rw [cl_eq_cl_inter_ground, diff_eq_diff_iff_inter_eq_inter, inter_eq_inter_iff_left, 
    inter_comm X],  
  exact ⟨(inter_subset_right _ _).trans (inter_subset_right _ _), 
    inter_subset_inter_left _ (M.cl_subset_ground _)⟩, 
end 

lemma indep.mem_cl_iff' (hI : M.indep I) : 
  x ∈ M.cl I ↔ (x ∈ M.E ∧ (M.indep (insert x I) → x ∈ I)) :=
begin
  simp_rw [hI.cl_eq_set_of_basis, mem_set_of_eq],
  refine ⟨λ h, ⟨h.subset_ground (mem_insert _ _), λ h', h.mem_of_insert_indep (mem_insert _ _) h'⟩, 
    λ h, _⟩, 
  refine hI.basis_of_forall_insert (subset_insert x I) (λ e he hei, he.2  _) 
    (insert_subset.mpr ⟨h.1, hI.subset_ground⟩), 
  rw [←singleton_union, union_diff_right, mem_diff, mem_singleton_iff] at he,
  rw [he.1] at ⊢ hei, 
  exact h.2 hei,
end

lemma indep.mem_cl_iff (hI : M.indep I) (hx : x ∈ M.E . ssE) : 
  x ∈ M.cl I ↔ (M.indep (insert x I) → x ∈ I) :=
begin
  simp_rw [hI.mem_cl_iff', and_iff_right_iff_imp],
  intro _, exact hx
end

lemma indep.mem_cl_iff_insert_dep_or_mem (hI : M.indep I) :
  x ∈ M.cl I ↔ M.dep (insert x I) ∨ x ∈ I :=
begin
  rw [hI.mem_cl_iff', dep_iff, insert_subset, and_iff_left hI.subset_ground, imp_iff_not_or], 
  refine (em' (x ∈ M.E)).elim (λ hxE, _) (by tauto), 
  rw [iff_false_intro hxE, false_and, and_false, false_or, false_iff], 
  exact not_mem_subset hI.subset_ground hxE
end 

lemma indep.insert_dep_iff (hI : M.indep I) :
  M.dep (insert e I) ↔ e ∈ M.cl I \ I :=
begin
  rw [mem_diff, hI.mem_cl_iff_insert_dep_or_mem, or_and_distrib_right, and_not_self, or_false,
    iff_self_and], 
  refine λ hd heI, hd.not_indep _,
  rwa [insert_eq_of_mem heI], 
end  

lemma indep.mem_cl_iff_of_not_mem (hI : M.indep I) (heI : e ∉ I) : 
  e ∈ M.cl I ↔ M.dep (insert e I) :=
by { rw [hI.mem_cl_iff', dep_iff, insert_subset, and_iff_left hI.subset_ground], tauto }

lemma indep.not_mem_cl_iff (hI : M.indep I) (he : e ∈ M.E . ssE) :
  e ∉ M.cl I ↔ (e ∉ I ∧ M.indep (insert e I)) :=
by rw [←not_iff_not, not_not_mem, and_comm, not_and, hI.mem_cl_iff, not_not_mem]

lemma indep.not_mem_cl_iff_of_not_mem (hI : M.indep I) (heI : e ∉ I) (he : e ∈ M.E . ssE) : 
  e ∉ M.cl I ↔ M.indep (insert e I) :=
by rw [hI.mem_cl_iff_of_not_mem heI, not_dep_iff]

lemma Inter_cl_eq_cl_Inter_of_Union_indep {ι : Type*} (I : ι → set α) [hι : nonempty ι]
  (h : M.indep (⋃ i, I i)) : (⋂ i, M.cl (I i)) = M.cl (⋂ i, I i) :=
begin  
  have hi : ∀ i, M.indep (I i), from λ i, h.subset (subset_Union _ _), 
  refine subset.antisymm _ (subset_Inter (λ i, M.cl_subset (Inter_subset _ _))), 
  rintro e he, rw mem_Inter at he, 
  by_contra h',
  obtain i₀ := hι.some,
  have hiu : (⋂ i , I i) ⊆ ⋃ i, I i, from 
    ((Inter_subset _ i₀).trans (subset_Union _ i₀)), 
  have hi_inter : M.indep (⋂ i, I i), from (hi i₀).subset (Inter_subset _ _), 
  rw hi_inter.not_mem_cl_iff ((M.cl_subset_ground (I i₀)) (he i₀)) at h',
  rw mem_Inter at h',
  rw not_forall at h', 
  { obtain ⟨⟨i₁, hei₁⟩, hei⟩ := h',   

    have hdi₁ : ¬M.indep (insert e (I i₁)),
      from λ h_ind, hei₁ (((hi i₁).mem_cl_iff'.mp (he i₁)).2 h_ind),
    
    have heu : e ∉ ⋃ i, I i, from λ he, hdi₁ (h.subset (insert_subset.mpr ⟨he, subset_Union _ _⟩)), 
    
    have hd_all : ∀ i, ¬M.indep (insert e (I i)), 
      from λ i hind, heu (mem_Union_of_mem _ (((hi i).mem_cl_iff'.mp (he i)).2 hind)),
    
    have hb : M.basis (⋃ i, I i) (insert e (⋃ i, I i)), 
    { have h' := (M.cl_subset) (subset_Union _ _) (he i₀),
      rwa [h.cl_eq_set_of_basis] at h' },
    
    obtain ⟨I', hI', hssI', hI'ss⟩ := 
      hei.exists_basis_subset_union_basis (insert_subset_insert hiu) hb, 
    
    rw [insert_union, union_eq_right_iff_subset.mpr hiu] at hI'ss, 
    
    have hI'I : I' \ (⋃ i, I i) = {e}, 
    { refine subset.antisymm _ (singleton_subset_iff.mpr ⟨hssI' (mem_insert _ _),heu⟩),
      rwa [diff_subset_iff, union_singleton] }, 
    
    obtain ⟨f, hfI, hf⟩ := hI'.eq_exchange_of_diff_eq_singleton hb hI'I, 

    have hf' : ∀ i, f ∈ I i, 
    { refine λ i, by_contra (λ hfi, (hd_all i (hI'.indep.subset (insert_subset.mpr ⟨_,_⟩)))), 
      { exact hssI' (mem_insert _ _) },
      rw [←diff_singleton_eq_self hfi, diff_subset_iff, singleton_union], 
      exact ((subset_Union _ i).trans_eq hf).trans (diff_subset _ _) },   

    exact hfI.2 (hssI' (or.inr (by rwa mem_Inter))),
  },
end 
/- added the assumption `(hι : nonempty ι)`, for otherwise
   `is_empty ι` leads to a contradiction -/

lemma bInter_cl_eq_cl_sInter_of_sUnion_indep (Is : set (set α)) (hIs : Is.nonempty) (h : M.indep (⋃₀ Is)) :
  (⋂ I ∈ Is, M.cl I) = M.cl (⋂₀ Is) :=
begin
  rw [sUnion_eq_Union] at h, 
  rw [bInter_eq_Inter, sInter_eq_Inter],
  haveI := hIs.to_subtype,
  exact Inter_cl_eq_cl_Inter_of_Union_indep (λ (x : Is), coe x) h, 
end 
/- as in the previous lemma, added the assumption `(hIs : nonempty Is)` -/

lemma inter_cl_eq_cl_inter_of_union_indep (h : M.indep (I ∪ J)) : M.cl I ∩ M.cl J = M.cl (I ∩ J) :=
begin
  rw [inter_eq_Inter, inter_eq_Inter], rw [union_eq_Union] at h,
  convert Inter_cl_eq_cl_Inter_of_Union_indep (λ b, cond b I J) (by simpa), 
  ext, cases x; simp, 
end

lemma basis.cl (hIX : M.basis I X) : M.cl I = M.cl X := 
(M.cl_subset hIX.subset).antisymm (cl_subset_cl 
  (λ x hx, hIX.indep.mem_cl_iff.mpr (λ h, hIX.mem_of_insert_indep hx h)))

lemma basis.mem_cl_iff (hIX : M.basis I X) (he : e ∈ M.E . ssE) : 
  e ∈ M.cl X ↔ (M.indep (insert e I) → e ∈ I) :=
by rw [←hIX.cl, hIX.indep.mem_cl_iff]
/- added the assumption `(he : e ∈ M.E . ssE)`
   as in indep.mem_cl_iff
  -/

lemma basis.mem_cl_iff' (hIX : M.basis I X): 
  e ∈ M.cl X ↔ (e ∈ M.E ∧ (M.indep (insert e I) → e ∈ I)) :=
by rw [←hIX.cl, hIX.indep.mem_cl_iff']
/- only added the assumption `(he : e ∈ M.E)`
   to the RHS, as in indep.mem_cl_iff' -/

lemma basis.mem_cl_iff_of_not_mem (hIX : M.basis I X) (heX : e ∉ X)  : 
  e ∈ M.cl X ↔ M.dep (insert e I) :=
begin
  by_cases he : e ∈ M.E, 
  { rw [hIX.mem_cl_iff, iff_false_intro (not_mem_subset hIX.subset heX), imp_false, 
      not_indep_iff] }, 
  exact iff_of_false (not_mem_subset (M.cl_subset_ground _) he)
    (λ hD, he (hD.subset_ground (mem_insert _ _))), 
end 

lemma basis.mem_cl_iff_of_not_mem' (hIX : M.basis I X) (heX : e ∉ X) : 
  e ∈ M.cl X ↔ (e ∈ M.E ∧ ¬M.indep (insert e I)) :=
begin
  rw [hIX.mem_cl_iff'],
  refine ⟨_, _⟩,
  { rintros ⟨he, h⟩,
    refine ⟨he, λ h', heX (hIX.subset (h h'))⟩, },
  { rintros ⟨he, _⟩,
    use he }
end
/- only added the assumption `(he : e ∈ M.E . ssE)`
   to the RHS, as in indep.mem_cl_iff' -/

lemma basis.subset_cl (hI : M.basis I X) : X ⊆ M.cl I :=
by { rw hI.cl, exact M.subset_cl X hI.subset_ground }

lemma indep.basis_cl (hI : M.indep I) : M.basis I (M.cl I) :=
begin
  refine hI.basis_of_forall_insert (M.subset_cl I hI.subset_ground) (λ e he heI, he.2 _), 
  rw [mem_diff, hI.mem_cl_iff] at he,
  obtain ⟨he, he'⟩ := he,
  rw hI.mem_cl_iff_of_not_mem he' at he,
  exact (he.not_indep heI).elim, 
end 

lemma cl_eq_set_of_indep_not_indep (M : matroid_in α) (X : set α) (hX : X ⊆ M.E) : 
  M.cl X = X ∪ {e | ∃ I ⊆ X, M.indep I ∧ M.dep (insert e I)} := 
begin
  refine subset_antisymm (λ e he, ((em (e ∈ X)).elim or.inl (λ heX, or.inr _ ))) 
      (union_subset (M.subset_cl X hX) _),
  { obtain ⟨I, hI⟩ := M.exists_basis X, 
    refine ⟨I, hI.subset, hI.indep, _⟩,
    refine hI.indep.basis_cl.dep_of_ssubset (ssubset_insert (not_mem_subset hI.subset heX)) 
      (insert_subset.mpr ⟨by rwa hI.cl, M.subset_cl I (hI.subset_ground_left)⟩) },  
  rintro e ⟨I, hIX, hI, hIe⟩,
  refine (M.cl_subset hIX) _, 
  rw [hI.mem_cl_iff'], 
  refine ⟨hIe.subset_ground (mem_insert e I), _⟩,
  { intro h, rw dep at hIe,
    have := hIe.1, contradiction }
end     

lemma indep.basis_of_subset_cl (hI : M.indep I) (hIX : I ⊆ X) (h : X ⊆ M.cl I) : M.basis I X :=
hI.basis_cl.basis_subset hIX h
 
lemma indep.base_of_cl_eq_ground (hI : M.indep I) (h : M.cl I = M.E) : M.base I :=
by { rw base_iff_basis_ground, exact hI.basis_of_subset_cl hI.subset_ground (by rw h) }

lemma basis.basis_cl (hI : M.basis I X) : M.basis I (M.cl X) :=
by { rw [←hI.cl], exact hI.indep.basis_cl }

lemma basis_iff_basis_cl_of_subset (hIX : I ⊆ X) (hX : X ⊆ M.E . ssE) : 
  M.basis I X ↔ M.basis I (M.cl X) :=
⟨λ h, h.basis_cl, λ h, h.basis_subset hIX (M.subset_cl X hX)⟩

lemma basis_iff_basis_cl_of_subset' (hIX : I ⊆ X) : M.basis I X ↔ (X ⊆ M.E ∧ M.basis I (M.cl X)) :=
⟨λ h, ⟨h.subset_ground, h.basis_cl⟩, λ h, (h.2).basis_subset hIX (M.subset_cl X h.1)⟩

lemma basis.basis_of_cl_eq_cl (hI : M.basis I X) (hY : I ⊆ Y) (hY' : Y ⊆ M.E . ssE) 
  (h : M.cl X = M.cl Y) : M.basis I Y :=
by { rw [basis_iff_basis_cl_of_subset hY, ←h], exact hI.basis_cl }

lemma base.cl (hB : M.base B) : M.cl B = M.E :=
by { rw [(base_iff_basis_ground.mp hB).cl], exact M.cl_ground }

lemma base.mem_cl (hB : M.base B) (e : α) (he : e ∈ M.E . ssE) : e ∈ M.cl B :=
by rwa [base.cl hB]

lemma base.cl_of_supset (hB : M.base B) (hBX : B ⊆ X) : M.cl X = M.E :=
subset_antisymm (M.cl_subset_ground _) (by { rw ← hB.cl, exact M.cl_subset hBX, })
  
lemma base_subset_iff_cl_eq_ground : (∃ B ⊆ X, M.base B) ↔ M.cl X = M.E :=
begin
  refine ⟨λ ⟨B, hBX, hB⟩, hB.cl_of_supset hBX, λ h, _⟩,
  obtain ⟨B, hBX⟩ :=  M.exists_basis (X ∩ M.E),
  use [B,  (basis.subset hBX).trans (inter_subset_left X M.E)],
  rw [base_iff_basis_ground, ←h],
  have := hBX.cl,
  rw ←cl_eq_cl_inter_ground at this,
  rw ←this, exact hBX.indep.basis_cl
end

lemma mem_cl_insert (he : e ∉ M.cl X) (hef : e ∈ M.cl (insert f X)) : 
  f ∈ M.cl (insert e X) :=
begin
  rw cl_eq_cl_inter_ground at *, 
  have hfE : f ∈ M.E, 
  { by_contra' hfE, rw [insert_inter_of_not_mem hfE] at hef, exact he hef },
  have heE : e ∈ M.E, ssE,
  rw [insert_inter_of_mem hfE] at hef,
  rw [insert_inter_of_mem heE], 
  have hf : f ∉ M.cl (X ∩ M.E), 
  { exact λ hf, he (by rwa ←cl_insert_eq_of_mem_cl hf) }, 
  
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E), 
  rw [←hI.cl, hI.indep.not_mem_cl_iff heE] at he,
  rw [←hI.cl, hI.indep.not_mem_cl_iff hfE] at hf,  
  have he' := hI.insert_basis_insert he.2, 
  rw [←he'.cl, he'.indep.mem_cl_iff, mem_insert_iff], 
  have hf' := hI.insert_basis_insert hf.2, 
  rw [←hf'.cl, hf'.indep.mem_cl_iff heE, insert_comm, mem_insert_iff] at hef, 
  intro h', 
  obtain (rfl | heI) := hef h', 
  { exact or.inl rfl },
  exact (he.1 heI).elim, 
end

lemma cl_exchange (he : e ∈ M.cl (insert f X) \ M.cl X ) : f ∈ M.cl (insert e X) \ M.cl X :=
begin
  refine ⟨mem_cl_insert he.2 he.1, λ hf, _ ⟩,
  rw [cl_insert_eq_of_mem_cl hf, diff_self] at he,
  exact not_mem_empty _ he,
end

lemma cl_exchange_iff : e ∈ M.cl (insert f X) \ M.cl X ↔ f ∈ M.cl (insert e X) \ M.cl X :=
⟨cl_exchange, cl_exchange⟩

lemma cl_insert_eq_cl_insert_of_mem (he : e ∈ M.cl (insert f X) \ M.cl X) : 
  M.cl (insert e X) = M.cl (insert f X) :=
begin
  have hf := cl_exchange he, 
  have heE : e ∈ M.E := (M.cl_subset_ground _) he.1, 
  have hfE : f ∈ M.E := (M.cl_subset_ground _) hf.1, 
  rw [M.cl_eq_cl_inter_ground (insert f X), insert_inter_of_mem hfE] at ⊢ he, 
  rw [M.cl_eq_cl_inter_ground, insert_inter_of_mem heE] at ⊢ hf,
  rw [M.cl_eq_cl_inter_ground X] at he hf,  

  rw [subset_antisymm_iff, cl_subset_cl_iff_subset_cl, insert_subset],
  { refine ⟨⟨he.1, M.subset_cl_of_subset (subset_insert _ _) (insert_subset.mpr ⟨hfE,by ssE⟩)⟩, _⟩, 
    exact cl_subset_cl (insert_subset.mpr ⟨hf.1,
      M.subset_cl_of_subset (subset_insert _ _) (insert_subset.mpr ⟨heE, by ssE⟩)⟩) },
  exact insert_subset.mpr ⟨heE, by ssE⟩, 
end 

lemma cl_diff_singleton_eq_cl (h : e ∈ M.cl (X \ {e})) : M.cl (X \ {e}) = M.cl X :=
begin
  rw [cl_eq_cl_inter_ground, diff_eq, inter_right_comm, ←diff_eq] at *, 
  rw [M.cl_eq_cl_inter_ground X], 
  set X' := X ∩ M.E with hX',
  refine (M.cl_mono (diff_subset _ _)).antisymm _,
  
  have : (X' \ { e } ⊆ M.cl (X' \ { e })),
    { refine M.subset_cl (X' \ { e }) _,
      have g := inter_subset_right X M.E,
      have : X' \ {e} ⊆ X' := by simp only [diff_singleton_subset_iff, subset_insert],
      rw ←hX' at g, exact this.trans g, },
  have h' := M.cl_mono (insert_subset.mpr ⟨h, this⟩),
  rw [insert_diff_singleton, cl_cl] at h',
  exact (M.cl_mono (subset_insert _ _)).trans h',
end

lemma mem_cl_diff_singleton_iff_cl (he : e ∈ X) (heE : e ∈ M.E . ssE):
  e ∈ M.cl (X \ {e}) ↔ M.cl (X \ {e}) = M.cl X :=
begin
  rw [cl_eq_cl_inter_ground, M.cl_eq_cl_inter_ground X, diff_eq, inter_right_comm, ←diff_eq], 
  refine ⟨cl_diff_singleton_eq_cl, λ h, _⟩,
  rw [h], 
  exact M.mem_cl_of_mem' ⟨he, heE⟩, 
end 

lemma indep_iff_cl_diff_ne_forall : M.indep I ↔ (∀ e ∈ I, M.cl (I \ {e}) ≠ M.cl I) :=
begin
  refine ⟨λ hI e heI h_eq, _, λ h, _⟩,
  { have hecl : e ∈ M.cl I := M.subset_cl I (hI.subset_ground) heI, 
    rw [←h_eq] at hecl, 
    simpa only [(hI.diff {e}).mem_cl_iff, insert_diff_singleton, not_mem_diff_singleton, 
      insert_eq_of_mem heI, imp_iff_right hI] using hecl },
  have hIE : I ⊆ M.E, 
  { refine λ e he, by_contra (λ heE, h e he _), 
    rw [M.cl_eq_cl_inter_ground I, M.cl_eq_cl_inter_ground, diff_eq, inter_right_comm, 
      inter_assoc, ←diff_eq, diff_singleton_eq_self heE] },
  obtain ⟨J, hJ⟩ := M.exists_basis I, 
  convert hJ.indep,
  refine hJ.subset.antisymm' (λ e he, by_contra (λ heJ, _)), 
  have hJIe : J ⊆ I \ {e}, from subset_diff_singleton hJ.subset heJ, 
  have hcl := h e he, 
  rw [ne.def, ←mem_cl_diff_singleton_iff_cl he] at hcl, 
  have hcl' := not_mem_subset (M.cl_mono hJIe) hcl, 
  rw [hJ.cl] at hcl', 
  refine hcl' (M.subset_cl _ hJ.subset_ground he),   
end

lemma indep_iff_not_mem_cl_diff_forall (hI : I ⊆ M.E . ssE) : 
  M.indep I ↔ ∀ e ∈ I, e ∉ M.cl (I \ {e}) :=
begin
  rw indep_iff_cl_diff_ne_forall,
  { refine ⟨λ h x hxI, by { rw mem_cl_diff_singleton_iff_cl hxI, exact h x hxI },
            λ h x hxI, by { rw [ne.def, ←mem_cl_diff_singleton_iff_cl hxI], exact h x hxI }⟩, },
end

lemma indep_iff_not_mem_cl_diff_forall' : M.indep I ↔ (I ⊆ M.E ∧ ∀ e ∈ I, e ∉ M.cl (I \ {e})) :=
⟨λ h, ⟨h.subset_ground, (indep_iff_not_mem_cl_diff_forall h.subset_ground).mp h⟩,
 λ h, (indep_iff_not_mem_cl_diff_forall h.1).mpr h.2⟩
/- question: would it be better to have `e ∈ I ∩ M.E`? -/

-- lemma indep_iff_cl_ssubset_ssubset_forall (hI : I ⊆ M.E . ssE) : M.indep I ↔ ∀ J ⊂ I, M.cl J ⊂ M.cl I :=
-- begin
--   refine ⟨λ hI' J hJI, _, λ h, (indep_iff_cl_diff_ne_forall hI).mpr (λ x hx, (h _ $ diff_singleton_ssubset.2 hx).ne)⟩,
--   { obtain ⟨e,heI,heJ⟩ := exists_of_ssubset hJI,
--     exact (M.cl_subset (subset_diff_singleton hJI.subset heJ)).trans_ssubset
--       ((M.cl_subset (diff_subset I {e})).ssubset_of_ne
--       ((indep_iff_cl_diff_ne_forall hI).mp hI' e heI)) }
-- end
-- /- added `I ⊆ M.E`-/

-- lemma indep_iff_cl_ssubset_ssubset_forall' : M.indep I ↔ (I ⊆ M.E ∧ ∀ J ⊂ I, M.cl J ⊂ M.cl I) :=
-- ⟨ λ h, ⟨h.subset_ground, (indep_iff_cl_ssubset_ssubset_forall h.subset_ground).mp h⟩,
--            λ h, (indep_iff_cl_ssubset_ssubset_forall h.1).mpr h.2 ⟩
-- /- added `I ⊆ M.E` to RHS -/

lemma indep.insert_indep_iff_of_not_mem (hI : M.indep I) (he : e ∉ I) (he' : e ∈ M.E . ssE):
  M.indep (insert e I) ↔ e ∉ M.cl I :=
⟨λ h, (hI.not_mem_cl_iff he').mpr ⟨he, h⟩, λ h, ((hI.not_mem_cl_iff he').mp h).2⟩
/- added `e ∈ M.E` -/

lemma indep.insert_indep_iff_of_not_mem' (hI : M.indep I) (he : e ∉ I):
  M.indep (insert e I) ↔ (e ∈ M.E ∧ e ∉ M.cl I) :=
⟨λ h, ⟨h.subset_ground (mem_insert e I), (hI.insert_indep_iff_of_not_mem he (h.subset_ground (mem_insert e I))).mp h⟩,
 λ h, (hI.insert_indep_iff_of_not_mem he h.1).mpr h.2 ⟩
/- added `e ∈ M.E` to RHS -/

lemma indep.cl_diff_singleton_ssubset (hI : M.indep I) (he : e ∈ I) : M.cl (I \ {e}) ⊂  M.cl I :=
ssubset_of_subset_of_ne (M.cl_mono (diff_subset _ _)) (indep_iff_cl_diff_ne_forall.mp hI _ he)

-- lemma indep.cl_ssubset_ssubset (hI : M.indep I) (hJI : J ⊂ I) : M.cl J ⊂ M.cl I :=
-- indep_iff_cl_ssubset_ssubset_forall.mp hI J hJI

lemma basis_iff_cl : M.basis I X ↔ I ⊆ X ∧ X ⊆ M.cl I ∧ ∀ J ⊆ I, X ⊆ M.cl J → J = I :=
begin
  split, 
  { refine λ h, ⟨h.subset, h.subset_cl, λ J hJI hXJ, hJI.antisymm (λ e heI, _)⟩, 
    rw [(h.indep.subset hJI).cl_eq_set_of_basis] at hXJ, 
    exact (h.subset.trans hXJ heI : M.basis _ _).mem_of_insert_indep (mem_insert _ _) 
      (h.indep.subset (insert_subset.mpr ⟨heI, hJI⟩)) },
  rintro ⟨hIX, hXI, hmin⟩,  
  refine indep.basis_of_forall_insert _ hIX _ _,

  { rw indep_iff_cl_diff_ne_forall,
    intros e he hecl,
    rw ← hmin _ (diff_subset _ _) (hXI.trans_eq hecl.symm) at he, 
    exact he.2 (mem_singleton e) },
  
  exact λ e he hi, he.2 
    (((hi.subset (subset_insert _ _)).basis_cl).mem_of_insert_indep (hXI (he.1)) hi),
  exact hXI.trans (M.cl_subset_ground I),
end

lemma basis_union_iff_indep_cl : M.basis I (I ∪ X) ↔ M.indep I ∧ X ⊆ M.cl I :=
begin
  refine ⟨λ h, ⟨h.indep, (subset_union_right _ _).trans h.subset_cl⟩, _⟩,
  rw basis_iff_cl,
  rintros ⟨hI, hXI⟩,
  refine ⟨subset_union_left _ _, union_subset (M.subset_cl I hI.subset_ground) hXI,
    λ J hJI hJ, by_contra (λ h', _)⟩,
  obtain ⟨e,heI,heJ⟩ := exists_of_ssubset (hJI.ssubset_of_ne h'),
  have heJ' : e ∈ M.cl J,
    from hJ (or.inl heI),
  refine indep_iff_not_mem_cl_diff_forall.mp hI e heI (mem_of_mem_of_subset heJ' _),
  exact M.cl_subset (subset_diff_singleton hJI heJ),
end

lemma basis_iff_indep_cl : M.basis I X ↔ M.indep I ∧ X ⊆ M.cl I ∧ I ⊆ X :=
⟨λ h, ⟨h.indep, h.subset_cl, h.subset⟩,
  λ h, (basis_union_iff_indep_cl.mpr ⟨h.1,h.2.1⟩).basis_subset h.2.2 (subset_union_right _ _)⟩

lemma basis.eq_of_cl_subset (hI : M.basis I X) (hJI : J ⊆ I) (hJ : X ⊆ M.cl J) : J = I :=
(basis_iff_cl.mp hI).2.2 J hJI hJ

lemma empty_basis_iff : M.basis ∅ X ↔ X ⊆ M.cl ∅ :=
begin
  simp only [basis_iff_cl, empty_subset, true_and, and_iff_left_iff_imp],
  exact λ h J hJ hXJ, subset_empty_iff.mp hJ,
end

lemma eq_of_cl_eq_cl_forall {M₁ M₂ : matroid_in α} (h : ∀ X, M₁.cl X = M₂.cl X) : M₁ = M₂ :=
begin
  have h' := h univ,
  repeat { rw cl_univ at h' },
  refine eq_of_indep_iff_indep_forall h' (λ I hI, _),
  have hI' := hI, rw h' at hI',
  refine ⟨_, _⟩,
  { intro hIi,
    rw indep_iff_cl_diff_ne_forall,
    intros e he,
    have := indep_iff_cl_diff_ne_forall.mp hIi e he, 
    rwa [h (I \ {e}), h I] at this, },
  intro g,
  rw indep_iff_cl_diff_ne_forall,
  intros e he,
  have := ((indep_iff_cl_diff_ne_forall).mp g e) he,
  rwa [←h (I \ {e}), ←h I] at this,
end


section spanning

variables {S T : set α}

/-- A set is `spanning` in `M` if its closure is equal to `M.E`, or equivalently if it contains 
  a base of `M`. -/
def spanning (M : matroid_in α) (S : set α) := M.cl S = M.E ∧ S ⊆ M.E 

@[ssE_finish_rules] lemma spanning.subset_ground (hS : M.spanning S) : S ⊆ M.E := 
hS.2 

lemma spanning.cl (hS : M.spanning S) : M.cl S = M.E := 
hS.1

lemma spanning_iff_cl (hS : S ⊆ M.E . ssE) : M.spanning S ↔ M.cl S = M.E := 
⟨and.left, λ h, ⟨h,hS⟩⟩

lemma not_spanning_iff_cl (hS : S ⊆ M.E . ssE) : ¬ M.spanning S ↔ M.cl S ⊂ M.E :=
begin
  rw [spanning_iff_cl, ssubset_iff_subset_ne, ne.def, iff_and_self, 
    iff_true_intro (M.cl_subset_ground _)], 
  refine λ _, trivial,  
end  

lemma spanning.supset (hS : M.spanning S) (hST : S ⊆ T) (hT : T ⊆ M.E . ssE) : M.spanning T :=
begin
  refine ⟨(M.cl_subset_ground _).antisymm _, hT⟩, 
  rw ←hS.cl, 
  exact M.cl_subset hST, 
end 

lemma spanning.union_left (hS : M.spanning S) (hX : X ⊆ M.E . ssE) : M.spanning (S ∪ X) :=
hS.supset (subset_union_left _ _) 

lemma spanning.union_right (hS : M.spanning S) (hX : X ⊆ M.E . ssE) : M.spanning (X ∪ S) :=
hS.supset (subset_union_right _ _) 

lemma base.spanning (hB : M.base B) : M.spanning B := 
⟨hB.cl, hB.subset_ground⟩ 

lemma ground_spanning (M : matroid_in α) : M.spanning M.E := 
⟨M.cl_ground, rfl.subset⟩ 

lemma base.supset_spanning (hB : M.base B) (hBX : B ⊆ X) (hX : X ⊆ M.E . ssE) : M.spanning X := 
hB.spanning.supset hBX 

lemma spanning_iff_supset_base' : M.spanning S ↔ (∃ B, M.base B ∧ B ⊆ S) ∧ S ⊆ M.E := 
begin
  rw [spanning, and.congr_left_iff], 
  refine λ hSE, ⟨λ h, _, _⟩,
  { obtain ⟨B, hB⟩ := M.exists_basis S,
    refine ⟨B, hB.indep.base_of_cl_eq_ground _, hB.subset⟩, 
    rwa [hB.cl] },
  rintro ⟨B, hB, hBS⟩, 
  rw [subset_antisymm_iff, and_iff_right (M.cl_subset_ground _), ←hB.cl], 
  exact M.cl_subset hBS, 
end 

lemma spanning_iff_supset_base (hS : S ⊆ M.E . ssE) : M.spanning S ↔ ∃ B, M.base B ∧ B ⊆ S := 
by rw [spanning_iff_supset_base', and_iff_left hS]

lemma coindep_iff_compl_spanning (hI : I ⊆ M.E . ssE) : M.coindep I ↔ M.spanning (M.E \ I) :=
begin
  simp_rw [coindep_iff_exists, spanning_iff_supset_base, subset_diff, disjoint.comm],  
  exact ⟨Exists.imp (λ B hB, ⟨hB.1, hB.1.subset_ground, hB.2⟩), 
    Exists.imp (λ B hB, ⟨hB.1, hB.2.2⟩)⟩, 
end 

lemma spanning_iff_compl_coindep (hI : S ⊆ M.E . ssE) : M.spanning S ↔ M.coindep (M.E \ S) :=
by simp [coindep_iff_compl_spanning]

lemma coindep.compl_spanning (hI : M.coindep I) : M.spanning (M.E \ I) := 
coindep_iff_compl_spanning.mp hI 

lemma spanning.compl_coindep (hS : M.spanning S) : M.coindep (M.E \ S) := 
spanning_iff_compl_coindep.mp hS 

lemma coindep_iff_cl_compl_eq_ground (hK : X ⊆ M.E . ssE) : M.coindep X ↔ M.cl (M.E \ X) = M.E :=
by rw [coindep_iff_compl_spanning, spanning_iff_cl]

lemma coindep.cl_compl (hX : M.coindep X) : M.cl (M.E \ X) = M.E := 
(coindep_iff_cl_compl_eq_ground hX.subset_ground).mp hX 


end spanning

-- section from_axioms

-- lemma cl_diff_singleton_eq_cl' (cl : set α → set α) (M.subset_cl : ∀ X, X ⊆ cl X)
-- (cl_mono : ∀ X Y, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X )
-- {x : α} {I : set α} (h : x ∈ cl (I \ {x})) :
--   cl (I \ {x}) = cl I :=
-- begin
--   refine (cl_mono _ _ (diff_subset _ _)).antisymm _,
--   have h' := cl_mono _ _ (insert_subset.mpr ⟨h, (M.subset_cl _ )⟩),
--   rw [insert_diff_singleton, cl_idem] at h',
--   exact (cl_mono _ _ (subset_insert _ _)).trans h',
-- end

-- /-- A set is independent relative to a closure function if none of its elements are contained in 
--   the closure of their removal -/
-- def cl_indep (cl : set α → set α) (I : set α) : Prop := ∀ e ∈ I, e ∉ cl (I \ {e})   

-- lemma cl_indep_mono {cl : set α → set α} (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) {I J : set α} 
-- (hJ : cl_indep cl J) (hIJ : I ⊆ J) :
--   cl_indep cl I :=
-- (λ e heI hecl, hJ e (hIJ heI) (cl_mono (diff_subset_diff_left hIJ) hecl))

-- lemma cl_indep_aux {e : α} {I : set α} {cl : set α → set α} 
-- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X ) 
-- (h : cl_indep cl I) (heI : ¬cl_indep cl (insert e I)) : 
-- e ∈ cl I :=
-- begin
--   have he : α ∉ I, by { intro he, rw [insert_eq_of_mem he] at heI, exact heI h },
--   rw [cl_indep] at heI, push_neg at heI, 
--   obtain ⟨f, ⟨(rfl | hfI), hfcl⟩⟩ := heI, 
--   { rwa [insert_diff_self_of_not_mem he] at hfcl },
--   have hne : α ≠ f, by { rintro rfl, exact he hfI }, 
--   rw [←insert_diff_singleton_comm hne] at hfcl, 
--   convert (cl_exchange (I \ {f}) e f ⟨hfcl,h f hfI⟩).1, 
--   rw [insert_diff_singleton, insert_eq_of_mem hfI],  
-- end   

-- /-- If the closure axioms hold, then `cl`-independence gives rise to a matroid -/
-- def matroid_of_cl (cl : set α → set α) (M.subset_cl : ∀ X, X ⊆ cl X)
-- (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X )
-- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X ) 
-- (cl_indep_maximal : ∀ ⦃I X⦄, cl_indep cl I → I ⊆ X  → 
--     (maximals (⊆) {J | cl_indep cl J ∧ I ⊆ J ∧ J ⊆ X }).nonempty) :
-- matroid_in α := 
-- matroid_of_indep (cl_indep cl) 
-- (λ e he _, not_mem_empty _ he) (λ I J hJ hIJ, cl_indep_mono cl_mono hJ hIJ)
-- (begin
--   refine λ I I' hI hIn hI'm, _, 
--   obtain ⟨B, hB⟩ := cl_indep_maximal hI (subset_union_left I I'), 
--   have hB' : B ∈ maximals (⊆) {J | cl_indep cl J},  
--   { refine ⟨hB.1.1,(λ B' hB' hBB' e heB', by_contra (λ heB, _) )⟩,
--     have he' : α ∈ cl I', 
--     { refine (em (e ∈ I')).elim (λ heI', (M.subset_cl I') heI') 
--         (λ heI', cl_indep_aux cl_exchange hI'm.1 (λ hi, _)), 
--       exact heI' (hI'm.2 hi (subset_insert e _) (mem_insert e _)) },
--       have hI'B : I' ⊆ cl B, 
--     { refine λ f hf, (em (f ∈ B)).elim (λ h', M.subset_cl B h') 
--         (λ hfB', cl_indep_aux cl_exchange hB.1.1 (λ hi, hfB' _)),  
      
--       refine hB.2 ⟨hi,hB.1.2.1.trans (subset_insert _ _),_⟩ (subset_insert _ _) (mem_insert _ _), 
--       exact insert_subset.mpr ⟨or.inr hf,hB.1.2.2⟩ }, 
--     have heBcl := (cl_idem B).subset ((cl_mono hI'B) he'), 
--     refine cl_indep_mono cl_mono hB' (insert_subset.mpr ⟨heB', hBB'⟩) e (mem_insert _ _) _,
--     rwa [insert_diff_of_mem _ (mem_singleton e), diff_singleton_eq_self heB] },
--   obtain ⟨f,hfB,hfI⟩ := exists_of_ssubset 
--     (hB.1.2.1.ssubset_of_ne (by { rintro rfl, exact hIn hB' })), 
--   refine ⟨f, ⟨_, hfI⟩, cl_indep_mono cl_mono hB.1.1 (insert_subset.mpr ⟨hfB,hB.1.2.1⟩)⟩,    
--   exact or.elim (hB.1.2.2 hfB) (false.elim ∘ hfI) id, 
-- end)
-- (λ I X hI hIX, cl_indep_maximal hI hIX)
 
-- lemma cl_indep_cl_eq {cl : set α → set α }
--   (M.subset_cl : ∀ X, X ⊆ cl X )
--   (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y )
--   (cl_idem : ∀ X, cl (cl X) = cl X )
--   (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X ) 
--   (cl_indep_maximal : ∀ ⦃I X⦄, cl_indep cl I → I ⊆ X →  
--     (maximals (⊆) {J | cl_indep cl J ∧ I ⊆ J ∧ J ⊆ X }).nonempty ) (X : set α) :
-- cl X = X ∪ {e | ∃ I ⊆ X, cl_indep cl I ∧ ¬cl_indep cl (insert e I) }  :=
-- begin
--   ext f, 
--   refine ⟨λ h, (em (f ∈ X)).elim or.inl (λ hf, or.inr _), 
--     λ h, or.elim h (λ g, M.subset_cl X g) _⟩, 
--   { have hd : ¬ (cl_indep cl (insert f X)), 
--     { refine λ hi, hi f (mem_insert _ _) _, convert h, 
--       rw [insert_diff_of_mem _ (mem_singleton f), diff_singleton_eq_self hf] },
--     obtain ⟨I, hI⟩ := cl_indep_maximal (λ e he h', not_mem_empty _ he) (empty_subset X), 
--     have hXI : X ⊆ cl I,  
--     { refine λ x hx, (em (x ∈ I)).elim (λ h', M.subset_cl _ h') (λ hxI, _),
--       refine cl_indep_aux cl_exchange hI.1.1 (λ hi, hxI _),  
--       refine hI.2 ⟨hi, empty_subset (insert x I), _⟩ (subset_insert x _) (mem_insert _ _), 
--       exact insert_subset.mpr ⟨hx, hI.1.2.2⟩ },
--     have hfI : f ∈ cl I, from (cl_mono (hXI)).trans_eq (cl_idem I) h,
--     refine ⟨I, hI.1.2.2, hI.1.1, λ hi, hf (hi f (mem_insert f _) _).elim⟩,
--     rwa [insert_diff_of_mem _ (mem_singleton f), diff_singleton_eq_self],  
--     exact not_mem_subset hI.1.2.2 hf },
--   rintro ⟨I, hIX, hI, hfI⟩, 
--   exact (cl_mono hIX) (cl_indep_aux cl_exchange hI hfI), 
-- end 

-- @[simp] lemma matroid_of_cl_apply {cl : set α → set α} (M.subset_cl : ∀ X, X ⊆ cl X)
-- (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
-- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X) 
-- (cl_indep_maximal : ∀ ⦃I X⦄, cl_indep cl I → I ⊆ X →   
--     (maximals (⊆) {J | cl_indep cl J ∧ I ⊆ J ∧ J ⊆ X }).nonempty) :
-- (matroid_of_cl cl M.subset_cl cl_mono cl_idem cl_exchange cl_indep_maximal).cl = cl :=
-- begin
--   ext1 X,
--   rw [(cl_indep_cl_eq M.subset_cl cl_mono cl_idem cl_exchange cl_indep_maximal X : cl X = _), 
--     matroid_of_cl, matroid.cl_eq_set_of_indep_not_indep], 
--   simp, 
-- end 

-- @[simp] lemma matroid_of_cl_indep_iff {cl : set α → set α} (M.subset_cl : ∀ X, X ⊆ cl X)
-- (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
-- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X) 
-- (cl_indep_maximal : ∀ ⦃I X⦄, cl_indep cl I → I ⊆ X →   
--     (maximals (⊆) {J | cl_indep cl J ∧ I ⊆ J ∧ J ⊆ X }).nonempty) {I : set α}:
-- (matroid_of_cl cl M.subset_cl cl_mono cl_idem cl_exchange cl_indep_maximal).indep I ↔ cl_indep cl I :=
-- by rw [matroid_of_cl, matroid_of_indep_apply]

-- /-- The maximality axiom isn't needed if all independent sets are at most some fixed size. -/
-- def matroid_of_cl_of_indep_bounded (cl : set α → set α)
--   (M.subset_cl : ∀ X, X ⊆ cl X )
--   (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y )
--   (cl_idem : ∀ X, cl (cl X) = cl X )
--   (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X )  
--   (n : ℕ) (hn : ∀ I, cl_indep cl I → I.finite ∧ I.ncard ≤ n) :
-- matroid_in α := matroid_of_cl cl M.subset_cl cl_mono cl_idem cl_exchange
-- (exists_maximal_subset_property_of_bounded ⟨n, hn⟩)

-- @[simp] lemma matroid_of_cl_of_indep_bounded_apply (cl : set α → set α) (M.subset_cl : ∀ X, X ⊆ cl X )
-- (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X )
-- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X )  
-- (n : ℕ) (hn : ∀ I, cl_indep cl I → I.finite ∧ I.ncard ≤ n) : 
-- (matroid_of_cl_of_indep_bounded cl M.subset_cl cl_mono cl_idem cl_exchange n hn).cl = cl := 
-- by simp [matroid_of_cl_of_indep_bounded]

-- instance (cl : set α → set α) (M.subset_cl : ∀ X, X ⊆ cl X )
-- (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X )
-- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X )  
-- (n : ℕ) (hn : ∀ I, cl_indep cl I → I.finite ∧ I.ncard ≤ n) :
-- matroid.finite_rk (matroid_of_cl_of_indep_bounded cl M.subset_cl cl_mono cl_idem cl_exchange n hn) 
-- := 
-- begin
--   obtain ⟨B, h⟩ := 
--     (matroid_of_cl_of_indep_bounded cl M.subset_cl cl_mono cl_idem cl_exchange n hn).exists_base, 
--   refine h.finite_rk_of_finite (hn _ _).1, 
--   simp_rw [matroid_of_cl_of_indep_bounded, matroid_of_cl, matroid.base_iff_maximal_indep, 
--     matroid_of_indep_apply] at h, 
--   exact h.1, 
-- end 

-- /-- A finite matroid as defined by the closure axioms. -/
-- def matroid_of_cl_of_finite [finite E] (cl : set α → set α) (M.subset_cl : ∀ X, X ⊆ cl X )
-- (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
-- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X) : 
-- matroid_in α   :=
-- matroid_of_cl_of_indep_bounded cl M.subset_cl cl_mono cl_idem cl_exchange (nat.card E)
-- (λ I hI, ⟨to_finite _, by { rw [←ncard_univ], exact ncard_le_of_subset (subset_univ _) }⟩) 
 
-- @[simp] lemma matroid_of_cl_of_finite_apply [finite E] (cl : set α → set α) 
-- (M.subset_cl : ∀ X, X ⊆ cl X )
-- (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
-- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X) :
-- (matroid_of_cl_of_finite cl M.subset_cl cl_mono cl_idem cl_exchange).cl = cl :=
-- by simp [matroid_of_cl_of_finite] 

-- end from_axioms

end matroid_in

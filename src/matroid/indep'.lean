import mathlib.data.set.finite
import .basic

variables {E : Type*} {M : matroid E} {I J I' J' I₁ I₂ B B' X Y : set E} {e f : E}

open set
namespace matroid

section general

lemma indep_iff_subset_base : M.indep I ↔ ∃ B, M.base B ∧ I ⊆ B := iff.rfl

lemma indep_mono {M : matroid E} {I J : set E} (hIJ : I ⊆ J) (hJ : M.indep J) : M.indep I :=
by {obtain ⟨B, hB, hJB⟩ := hJ, exact ⟨B, hB, hIJ.trans hJB⟩}

lemma indep.exists_base_supset (hI : M.indep I) : ∃ B, M.base B ∧ I ⊆ B := hI

lemma indep.subset (hJ : M.indep J) (hIJ : I ⊆ J) : M.indep I :=
by {obtain ⟨B, hB, hJB⟩ := hJ, exact ⟨B, hB, hIJ.trans hJB⟩}

lemma empty_indep (M : matroid E) : M.indep ∅ :=
exists.elim M.exists_base (λ B hB, ⟨_, hB, B.empty_subset⟩)

lemma indep.finite [finite_rk M] (hI : M.indep I) : I.finite := 
let ⟨B, hB, hIB⟩ := hI in hB.finite.subset hIB  

lemma indep.inter_right (hI : M.indep I) (X : set E) : M.indep (I ∩ X) :=
hI.subset (inter_subset_left _ _)

lemma indep.inter_left (hI : M.indep I) (X : set E) : M.indep (X ∩ I) :=
hI.subset (inter_subset_right _ _)

lemma indep.diff (hI : M.indep I) (X : set E) : M.indep (I \ X) := hI.subset (diff_subset _ _)

lemma base.indep (hB : M.base B) : M.indep B := ⟨B, hB, subset_rfl⟩

lemma base.eq_of_subset_indep (hB : M.base B) (hI : M.indep I) (hBI : B ⊆ I) : B = I :=
begin
  obtain ⟨B', hB', hB'I⟩ := hI, 
  exact hBI.antisymm (by rwa hB.eq_of_subset_base hB' (hBI.trans hB'I)), 
end

lemma base_iff_maximal_indep : M.base B ↔ M.indep B ∧ ∀ I, M.indep I → B ⊆ I → B = I :=
begin
  refine ⟨λ h, ⟨h.indep, λ _, h.eq_of_subset_indep ⟩,λ h, _⟩,
  obtain ⟨⟨B', hB', hBB'⟩, h⟩ := h,
  rwa h _ hB'.indep hBB',
end

/-- The RHS of this lemma is definitionally `B ∈ maximals (⊆) M.indep`, which can be convenient -/
lemma base_iff_maximal_indep' : M.base B ↔ M.indep B ∧ ∀ I, M.indep I → B ⊆ I → I ⊆ B  :=
begin
  rw [base_iff_maximal_indep], 
  exact ⟨λ h, ⟨h.1,λ I hI hBI, (h.2 I hI hBI).symm.subset⟩, 
    λ h, ⟨h.1, λ I hI hBI, (h.2 I hI hBI).antisymm' hBI⟩⟩,
end 

lemma base.dep_of_ssubset (hB : M.base B) (h : B ⊂ X) : ¬M.indep X :=
λ hX, h.ne (hB.eq_of_subset_indep hX h.subset)

lemma base.dep_of_insert (hB : M.base B) (he : e ∉ B) : ¬M.indep (insert e B) :=
hB.dep_of_ssubset (ssubset_insert he)

lemma base.exchange_base_of_indep (hB : M.base B) (he : e ∈ B) (hf : f ∉ B)
(hI : M.indep (insert f (B \ {e}))) :
  M.base (insert f (B \ {e})) :=
begin
  obtain ⟨B', hB', hIB'⟩ := hI,
  have hBeB' := (subset_insert _ _).trans hIB',
  have heB' : e ∉ B',
  { intro heB',
    have hBB' : B ⊆ B',
    { refine subset_trans _ (insert_subset.mpr ⟨heB',hIB'⟩),
      rw [insert_comm, insert_diff_singleton],
      refine (subset_insert _ _).trans (subset_insert _ _)},
    rw ←hB.eq_of_subset_indep hB'.indep hBB' at hIB',
    exact hf (hIB' (mem_insert _ _))},
  obtain ⟨y,hy,hy'⟩ := hB.exchange hB' ⟨he,heB'⟩,
  rw ←hy'.eq_of_subset_base hB' (insert_subset.mpr ⟨hy.1, hBeB'⟩) at hIB',
  have : f = y,
  { exact (mem_insert_iff.mp (hIB' (mem_insert _ _))).elim id
      (λ h', (hf (diff_subset _ _ h')).elim)},
  rwa this,
end

/-- If the difference of two bases is a singleton, then they differ by an insertion/removal -/
lemma base.eq_exchange_of_diff_eq_singleton (hI : M.base B) (hJ : M.base B') (h : B \ B' = {e}) : 
  ∃ f ∈ B' \ B, B' = (insert f B) \ {e} :=
begin
  have hcard := hJ.card_diff_eq_card_diff hI, 
  rw [h, ncard_singleton, ncard_eq_one] at hcard, 
  obtain ⟨f, hf⟩ := hcard, 
  refine ⟨f, _, _⟩, 
  { rw [←singleton_subset_iff], exact hf.symm.subset },
  rw [←inter_union_diff B' B, hf, union_singleton],  
  nth_rewrite 1 [←inter_union_diff B B'], 
  rw [h, union_singleton, insert_comm], 
  simp only [insert_diff_of_mem, mem_singleton],
  rw [inter_comm, diff_singleton_eq_self], 
  rintro (rfl | ⟨-,heJ⟩),
  { exact (hf.symm.subset rfl).2 (h.symm.subset rfl).1 },
  exact (h.symm.subset rfl).2 heJ, 
end  

lemma basis.indep (hI : M.basis I X) : M.indep I := hI.1.1

lemma basis.subset (hI : M.basis I X) : I ⊆ X := hI.1.2

lemma basis.eq_of_subset_indep (hI : M.basis I X) (hJ : M.indep J) (hIJ : I ⊆ J) (hJX : J ⊆ X) :
  I = J :=
hIJ.antisymm (hI.2 ⟨hJ, hJX⟩ hIJ)

lemma basis.finite (hI : M.basis I X) [finite_rk M] : I.finite := hI.indep.finite 

lemma basis_iff : M.basis I X ↔ M.indep I ∧ I ⊆ X ∧ ∀ J, M.indep J → I ⊆ J → J ⊆ X → I = J :=
⟨λ h, ⟨h.indep, h.subset, λ _, h.eq_of_subset_indep⟩, 
  λ h, ⟨⟨h.1,h.2.1⟩, λ J hJ hIJ, (h.2.2 _ hJ.1 hIJ hJ.2).symm.subset⟩⟩ 

lemma indep.basis_of_maximal_subset (hI : M.indep I) (hIX : I ⊆ X) 
(hmax : ∀ ⦃J⦄, M.indep J → I ⊆ J → J ⊆ X → J ⊆ I) : M.basis I X :=
⟨⟨hI, hIX⟩, λ J hJ hIJ, hmax hJ.1 hIJ hJ.2⟩

@[simp] lemma basis_empty_iff (M : matroid E) :
  M.basis I ∅ ↔ I = ∅ :=
begin
  refine ⟨λ h, subset_empty_iff.mp h.subset, _⟩,
  rintro rfl,
  exact ⟨⟨M.empty_indep, empty_subset _⟩, λ J h h', h.2⟩, 
end

lemma empty_basis_empty (M : matroid E) :
  M.basis ∅ ∅ :=
M.basis_empty_iff.mpr rfl

lemma basis.basis_subset (hI : M.basis I X) (hIY : I ⊆ Y) (hYX : Y ⊆ X) : M.basis I Y :=
⟨⟨hI.indep, hIY⟩, λ J hJ hIJ, hI.2 ⟨hJ.1, hJ.2.trans hYX⟩ hIJ⟩

lemma basis.dep_of_ssubset (hI : M.basis I X) {Y : set E} (hIY : I ⊂ Y) (hYX : Y ⊆ X) :
  ¬ M.indep Y :=
λ hY, hIY.ne (hI.eq_of_subset_indep hY hIY.subset hYX)

lemma basis.insert_dep (hI : M.basis I X) (he : e ∈ X \ I) :
  ¬M.indep (insert e I) :=
hI.dep_of_ssubset (ssubset_insert he.2) (insert_subset.mpr ⟨he.1,hI.subset⟩)

lemma basis.mem_of_insert_indep (hI : M.basis I X) (he : e ∈ X) (hIe : M.indep (insert e I)) : 
  e ∈ I :=
by_contra (λ heI, hI.insert_dep ⟨he, heI⟩ hIe) 

lemma basis.not_basis_of_ssubset (hI : M.basis I X) (hJI : J ⊂ I) : ¬ M.basis J X :=
λ h, hJI.ne (h.eq_of_subset_indep hI.indep hJI.subset hI.subset)

lemma indep.subset_basis_of_subset (hI : M.indep I) (hIX : I ⊆ X) :
  ∃ J, I ⊆ J ∧ M.basis J X :=
begin
  obtain ⟨J, ⟨(hJ : M.indep J),hIJ,hJX⟩, hJmax⟩ := M.maximality I X hI hIX, 
  exact ⟨J, hIJ, ⟨⟨hJ, hJX⟩,λ K hK hJK, hJmax ⟨hK.1,hIJ.trans hJK,hK.2⟩ hJK⟩⟩,
end

lemma indep.eq_of_basis (hI : M.indep I) (hJ : M.basis J I) : J = I :=
hJ.eq_of_subset_indep hI hJ.subset subset.rfl

lemma indep.basis_self (hI : M.indep I) : M.basis I I := ⟨⟨hI, rfl.subset⟩, λ J hJ _, hJ.2⟩

@[simp] lemma basis_self_iff_indep : M.basis I I ↔ M.indep I :=
⟨basis.indep, indep.basis_self⟩

lemma exists_basis (M : matroid E) (X : set E) : ∃ I, M.basis I X :=
by {obtain ⟨I, -, hI⟩ := M.empty_indep.subset_basis_of_subset (empty_subset X), exact ⟨_,hI⟩, }

lemma basis.exists_base (hI : M.basis I X) : ∃ B, M.base B ∧ I = B ∩ X :=
begin
  obtain ⟨B,hB, hIB⟩ := hI.indep,
  refine ⟨B, hB, subset_antisymm (subset_inter hIB hI.subset) _⟩,
  rw hI.eq_of_subset_indep (hB.indep.inter_right X) (subset_inter hIB hI.subset)
    (inter_subset_right _ _),
end

-- lemma basis_iff_base_inter :
--   M.basis I X ↔ ∃ B, M.base B ∧ I = B ∩ X ∧
--     ∀ B', M.base B' → B ∩ X ⊆ B' ∩ X → B ∩ X = B' ∩ X :=
-- begin
--   refine ⟨λ h, _,_⟩,
--   { obtain ⟨B,hB,rfl⟩ := h.exists_base,
--     refine ⟨B,hB,rfl,λ B' hB' hss,
--       h.eq_of_subset_indep (hB'.indep.inter_right X) hss (inter_subset_right _ _)⟩},
--   rintros ⟨B,hB,rfl,hBmax⟩,
--   refine ⟨hB.indep.inter_right X, inter_subset_right _ _, _⟩,
--   rintros J ⟨B',hB',hB'J⟩ hBXJ hJX ,
--   refine hBXJ.antisymm _,
--   rw hBmax B' hB' (subset_inter (hBXJ.trans hB'J) (inter_subset_right _ _)),
--   exact subset_inter hB'J hJX,
-- end

lemma base_iff_basis_univ :
  M.base B ↔ M.basis B univ :=
by {rw [base_iff_maximal_indep, basis_iff], simp}

lemma base.basis_univ (hB : M.base B) :
  M.basis B univ :=
base_iff_basis_univ.mp hB

lemma indep.basis_of_forall_insert (hI : M.indep I) (hIX : I ⊆ X) 
(he : ∀ e ∈ X \ I, ¬ M.indep (insert e I)) : M.basis I X :=
⟨⟨hI, hIX⟩, λ J hJ hIJ e heJ, (by_contra (λ heI, he _ ⟨hJ.2 heJ,heI⟩ 
  (hJ.1.subset (insert_subset.mpr ⟨heJ, hIJ⟩))))⟩  

lemma basis.Union_basis_Union {ι : Type*} (X I : ι → set E) (hI : ∀ i, M.basis (I i) (X i)) 
(h_ind : M.indep (⋃ i, I i)) : M.basis (⋃ i, I i) (⋃ i, X i) :=
begin
  refine h_ind.basis_of_forall_insert 
    (Union_subset_iff.mpr (λ i, (hI i).subset.trans (subset_Union _ _))) (λ e he hi, _), 
  simp only [mem_diff, mem_Union, not_exists] at he, 
  obtain ⟨i, heXi⟩ := he.1, 
  exact he.2 i ((hI i).mem_of_insert_indep heXi 
    (hi.subset (insert_subset_insert (subset_Union _ _)))), 
end 

lemma basis.basis_Union {ι : Type*} [nonempty ι] (X : ι → set E) (hI : ∀ i, M.basis I (X i)) : 
  M.basis I (⋃ i, X i) :=
begin
  convert basis.Union_basis_Union X (λ _, I) (λ i, hI i) _, 
  all_goals { rw Union_const },
  exact (hI (‹nonempty ι›.some)).indep, 
end 

lemma basis.union_basis_union (hIX : M.basis I X) (hJY : M.basis J Y) (h : M.indep (I ∪ J)) : 
  M.basis (I ∪ J) (X ∪ Y) :=
begin 
  rw [union_eq_Union, union_eq_Union], 
  refine basis.Union_basis_Union _ _ _ _,   
  { simp only [bool.forall_bool, bool.cond_ff, bool.cond_tt], exact ⟨hJY, hIX⟩ }, 
  rwa [←union_eq_Union], 
end 

lemma basis.basis_union (hIX : M.basis I X) (hIY : M.basis I Y) : M.basis I (X ∪ Y) :=
by { convert hIX.union_basis_union hIY _; rw union_self, exact hIX.indep }

lemma basis.basis_union_of_subset (hI : M.basis I X) (hJ : M.indep J) (hIJ : I ⊆ J) : 
  M.basis J (J ∪ X) :=
begin
  convert hJ.basis_self.union_basis_union hI (by rwa union_eq_left_iff_subset.mpr hIJ), 
  rw union_eq_left_iff_subset.mpr hIJ, 
end 

lemma basis.insert_basis_insert (hI : M.basis I X) (h : M.indep (insert e I)) : 
  M.basis (insert e I) (insert e X) :=
begin
  convert hI.union_basis_union 
    (indep.basis_self (h.subset (singleton_subset_iff.mpr (mem_insert _ _)))) _, 
  simp, simp, simpa, 
end 

lemma base.insert_dep (hB : M.base B) (h : e ∉ B) : ¬ M.indep (insert e B) :=
  λ h', (insert_ne_self.mpr h).symm ((base_iff_maximal_indep.mp hB).2 _ h' (subset_insert _ _))

lemma base.ssubset_dep (hB : M.base B) (h : B ⊂ X) : ¬ M.indep X :=
  λ h', h.ne ((base_iff_maximal_indep.mp hB).2 _ h' h.subset)

lemma indep.exists_insert_of_not_base (hI : M.indep I) (hI' : ¬M.base I) (hB : M.base B) : 
  ∃ e ∈ B \ I, M.indep (insert e I) :=
begin
  obtain ⟨B', hB', hIB'⟩ := hI, 
  obtain ⟨x, hxB', hx⟩ := exists_of_ssubset (hIB'.ssubset_of_ne (by { rintro rfl, exact hI' hB' })), 
  obtain (hxB | hxB) := em (x ∈ B), 
  { exact ⟨x, ⟨hxB, hx⟩ , ⟨B', hB', insert_subset.mpr ⟨hxB',hIB'⟩⟩⟩ },
  obtain ⟨e,he, hbase⟩ := hB'.exchange hB ⟨hxB',hxB⟩,    
  exact ⟨e, ⟨he.1, not_mem_subset hIB' he.2⟩, 
    ⟨_, hbase, insert_subset_insert (subset_diff_singleton hIB' hx)⟩⟩,  
end  

lemma base.exists_insert_of_ssubset (hB : M.base B) (hIB : I ⊂ B) (hB' : M.base B') : 
  ∃ e ∈ B' \ I, M.indep (insert e I) :=
(hB.indep.subset hIB.subset).exists_insert_of_not_base 
    (λ hI, hIB.ne (hI.eq_of_subset_base hB hIB.subset)) hB'

lemma base.base_of_basis_supset (hB : M.base B) (hBX : B ⊆ X) (hIX : M.basis I X) : M.base I :=
begin
  by_contra h, 
  obtain ⟨e,heBI,he⟩ := hIX.indep.exists_insert_of_not_base h hB, 
  exact heBI.2 (hIX.mem_of_insert_indep (hBX heBI.1) he), 
end 

lemma base.basis_of_subset (hB : M.base B) (hBX : B ⊆ X) : M.basis B X :=
⟨⟨hB.indep, hBX⟩, λ J hJ hBJ, by rw hB.eq_of_subset_indep hJ.1 hBJ⟩

lemma indep.exists_base_subset_union_base (hI : M.indep I) (hB : M.base B) : 
  ∃ B', M.base B' ∧ I ⊆ B' ∧ B' ⊆ I ∪ B :=
begin
  obtain ⟨B', hIB', hB'⟩ := hI.subset_basis_of_subset (subset_union_left I B), 
  exact ⟨B', hB.base_of_basis_supset (subset_union_right _ _) hB', hIB', hB'.subset⟩, 
end  

lemma eq_of_indep_iff_indep_forall {M₁ M₂ : matroid E} (h : ∀ I, (M₁.indep I ↔ M₂.indep I)) :
  M₁ = M₂ :=
begin
  ext B,
  have hI : M₁.indep = M₂.indep, by { ext ,apply h},
  simp_rw [base_iff_maximal_indep, hI],
end

end general

section dual

/-- This is really an order-theory lemma. Not clear where to put it, though.  -/
lemma base_compl_iff_mem_maximals_disjoint_base : 
  M.base Bᶜ ↔ B ∈ maximals (⊆) {I | ∃ B, M.base B ∧ disjoint I B} :=
begin
  simp_rw ←subset_compl_iff_disjoint_left, 
  refine ⟨λ h, ⟨⟨Bᶜ,h,subset.rfl⟩, _⟩, _⟩,
  { rintro X ⟨B', hB', hXB'⟩ hBX, 
    rw [←compl_subset_compl] at ⊢ hBX,
    rwa ←hB'.eq_of_subset_base h (hXB'.trans hBX) },
  rintro ⟨⟨B',hB',hBB'⟩,h⟩, 
  rw subset_compl_comm at hBB', 
  rwa [hBB'.antisymm (h ⟨_, hB', _⟩ hBB'), compl_compl],   
  rw compl_compl, 
end 

/-- The dual of a matroid `M`; its bases are the complements of bases in `M`. 
  The proofs here are messier than they need to be. -/
def dual (M : matroid E) : matroid E := 
matroid_of_indep (λ I, ∃ B, M.base B ∧ disjoint I B) 
(M.exists_base.imp (λ B hB, ⟨hB, empty_disjoint B⟩))
(λ I J ⟨B, hB, hJB⟩ hIJ, ⟨B, hB, disjoint_of_subset_left hIJ hJB⟩) 
(begin
  rintro I X ⟨B, hB, hIB⟩ hI_not_max hX_max,  
  have hB' := base_compl_iff_mem_maximals_disjoint_base.mpr hX_max,
  set B' := Xᶜ with hX, 
  have hI := (not_iff_not.mpr base_compl_iff_mem_maximals_disjoint_base).mpr hI_not_max, 
  obtain ⟨B'', hB'', hB''₁, hB''₂⟩ := (hB'.indep.diff I).exists_base_subset_union_base hB, 
  rw [←compl_subset_compl, ←hIB.sdiff_eq_right, ←union_diff_distrib, diff_eq, compl_inter, 
    compl_compl, union_subset_iff, compl_subset_compl] at hB''₂, 
  obtain ⟨e,⟨heB'',heI⟩⟩ := exists_of_ssubset (hB''₂.2.ssubset_of_ne 
    (by { rintro rfl, rw compl_compl at hI, exact hI hB'' })),
  refine ⟨e, ⟨by_contra (λ heB', heB'' (hB''₁ ⟨heB', heI⟩)), heI⟩, ⟨B'', hB'', _⟩⟩, 
  rw [←union_singleton, disjoint_union_left, disjoint_singleton_left, 
    ←subset_compl_iff_disjoint_right], 
  exact ⟨hB''₂.2, heB''⟩, 
end) 
(begin
  rintro I' X ⟨B, hB, hI'B⟩ hI'X, 
  obtain ⟨I, hI⟩ :=  M.exists_basis Xᶜ ,
  obtain ⟨B', hB', hIB', hB'IB⟩ := hI.indep.exists_base_subset_union_base hB, 
  refine ⟨X \ B', ⟨⟨_,hB',disjoint_sdiff_left⟩, subset_diff.mpr ⟨hI'X, _⟩,diff_subset _ _⟩, _⟩, 
  { refine disjoint_of_subset_right hB'IB (disjoint_union_right.mpr ⟨_,hI'B⟩), 
    rw [←subset_compl_iff_disjoint_left], 
    exact hI.subset.trans (compl_subset_compl.mpr hI'X) },
  rintro J ⟨⟨B'',hB'', hJB''⟩, hI'J, hJX⟩ hXB'J, 

  have hI' : (B'' ∩ X) ∪ (B' \ X) ⊆ B', 
  { refine (union_subset _ (diff_subset _ _)),
    refine (inter_subset_inter_right _ (diff_subset_iff.mp hXB'J)).trans _, 
    rw [inter_distrib_left, inter_comm _ J, disjoint_iff_inter_eq_empty.mp hJB'', union_empty],
    exact inter_subset_right _ _ },

  obtain ⟨B₁,hB₁,hI'B₁,hB₁I⟩ := (hB'.indep.subset hI').exists_base_subset_union_base hB'', 
  rw [union_comm, ←union_assoc, union_eq_self_of_subset_right (inter_subset_left _ _)] at hB₁I, 

  have : B₁ = B', 
  { refine hB₁.eq_of_subset_indep hB'.indep (λ e he, _), 
    refine (hB₁I he).elim (λ heB'',_) (λ h, h.1), 
    refine (em (e ∈ X)).elim (λ heX, hI' (or.inl ⟨heB'', heX⟩)) (λ heX, hIB' _), 
    refine hI.mem_of_insert_indep heX (hB₁.indep.subset (insert_subset.mpr ⟨he, _⟩)), 
    refine (subset_union_of_subset_right (subset_diff.mpr ⟨hIB',_⟩) _).trans hI'B₁, 
    exact subset_compl_iff_disjoint_right.mp hI.subset }, 
  
  subst this, 

  refine subset_diff.mpr ⟨hJX, by_contra (λ hne, _)⟩, 
  obtain ⟨e, heJ, heB'⟩ := not_disjoint_iff.mp hne,
  obtain (heB'' | ⟨heB₁,heX⟩ ) := hB₁I heB', 
  { exact hJB''.ne_of_mem heJ heB'' rfl },
  exact heX (hJX heJ), 
end)

lemma base_dual_iff' : M.dual.base B ↔ M.base Bᶜ :=
base_compl_iff_mem_maximals_disjoint_base.symm

lemma dual_dual' (M : matroid E) : M.dual.dual = M := 
by { ext, simp_rw [base_dual_iff', compl_compl] }

lemma dual_indep_iff_coindep' : M.dual.indep X ↔ M.coindep X := by simp [dual, coindep] 

lemma base.compl_base_dual' (hB : M.base B) : M.dual.base Bᶜ := by rwa [base_dual_iff', compl_compl]  

lemma base.compl_inter_basis_of_inter_basis' (hB : M.base B) (hBX : M.basis (B ∩ X) X) :
  M.dual.basis (Bᶜ ∩ Xᶜ) Xᶜ := 
begin
  rw basis_iff, 
  refine ⟨(hB.compl_base_dual'.indep.subset (inter_subset_left _ _)), inter_subset_right _ _, 
    λ J hJ hBCJ hJX, hBCJ.antisymm (subset_inter (λ e heJ heB, _) hJX)⟩, 
  obtain ⟨B', hB', hJB'⟩ := dual_indep_iff_coindep'.mp hJ,  
  obtain ⟨B'', hB'', hsB'', hB''s⟩  := hBX.indep.exists_base_subset_union_base hB', 
  have hB'ss : B' ⊆ B ∪ X, 
  { rw [←compl_subset_compl, compl_union, subset_compl_iff_disjoint_right],
    exact disjoint_of_subset_left hBCJ hJB' },
  have hB''ss : B'' ⊆ B, 
  { refine λ e he, (hB''s he).elim and.left (λ heB', (hB'ss heB').elim id (λ heX, _)),   
    exact (hBX.mem_of_insert_indep heX (hB''.indep.subset (insert_subset.mpr ⟨he,hsB''⟩))).1 },
  have := (hB''.eq_of_subset_indep hB.indep hB''ss).symm, subst this, 
  exact (hB''s heB).elim (λ heBX, hJX heJ heBX.2) (λ heB', hJB'.ne_of_mem heJ heB' rfl), 
end 

lemma base.inter_basis_iff_compl_inter_basis_dual' (hB : M.base B) : 
  M.basis (B ∩ X) X ↔ M.dual.basis (Bᶜ ∩ Xᶜ) Xᶜ :=
begin
  refine ⟨hB.compl_inter_basis_of_inter_basis', λ h, _⟩, 
  rw [←dual_dual' M], 
  simpa using hB.compl_base_dual'.compl_inter_basis_of_inter_basis' h, 
end  

end dual 

section minor 

def restrict_to (M : matroid E) (X : set E) : matroid X := 
matroid_of_indep (λ I, M.indep (coe '' I)) 
(by { rw image_empty, exact M.empty_indep, })
(λ I J hJ hIJ, hJ.subset (image_subset _ hIJ)) 
(begin
  rintro I I' hI hIn hI', 
  
  have hInb : ¬M.basis (coe '' I) X, 
  { refine λ hb, hIn ⟨hb.indep,λ J hJ hIJ e h, _⟩,
    have := hb.2 ⟨hJ, subtype.coe_image_subset X J⟩ (image_subset _ hIJ), 
    exact (image_subset_image_iff subtype.coe_injective).mp this h }, 
  have hI'b : M.basis (coe '' I') X, 
  { refine ⟨⟨hI'.1,subtype.coe_image_subset X _⟩,λ J hJ hIJ, _ ⟩, 
    have hJi : M.indep (coe '' (coe ⁻¹' J)), 
    { convert hJ.1, rw image_preimage_eq_iff, convert hJ.2, rw subtype.range_coe },
    have hss := hI'.2 hJi (by simpa using hIJ), 
    convert image_subset coe hss, 
    rw [eq_comm, image_preimage_eq_iff], 
    convert hJ.2, 
    exact subtype.range_coe },

  obtain ⟨B', hB', hI'B⟩ := hI'b.exists_base, 
  obtain ⟨B, hB, hIB, hBIB'⟩ := hI.exists_base_subset_union_base hB', 
  rw [hI'B, hB'.inter_basis_iff_compl_inter_basis_dual'] at hI'b, 

  have hss : B'ᶜ ∩ Xᶜ ⊆ Bᶜ ∩ Xᶜ, 
  { rw [←compl_union, ←compl_union, compl_subset_compl],
    exact union_subset (hBIB'.trans 
      (union_subset (subset_trans (subtype.coe_image_subset X I) (subset_union_right _ _))   
      (subset_union_left _ _))) (subset_union_right _ _) },  

  have h_eq := hI'b.eq_of_subset_indep _ hss (inter_subset_right _ _), 
  { rw [h_eq, ←hB.inter_basis_iff_compl_inter_basis_dual'] at hI'b, 
    have hssu : coe '' I ⊂ (B ∩ X) := 
    (subset_inter hIB (subtype.coe_image_subset X I)).ssubset_of_ne 
      (λ h, hInb (by rwa [←h] at hI'b)), 
    obtain ⟨e,he, heI⟩ := exists_of_ssubset hssu,
  

    refine ⟨⟨e, (inter_subset_right _ _) he⟩ , ⟨_,_⟩, _⟩,
    { rw [←preimage_image_eq I' subtype.coe_injective, mem_preimage, subtype.coe_mk], 
      refine (hBIB' he.1).elim (λ heI' , (heI heI').elim) (λ heB', _), 
      rw [hI'B], 
      exact ⟨heB', he.2⟩ }, 
    { rwa [←preimage_image_eq I subtype.coe_injective, mem_preimage] }, 
    refine hI'b.indep.subset _, 
    rw [image_insert_eq, subtype.coe_mk, insert_subset], 
    exact ⟨he, hssu.subset⟩ },

    rw [dual_indep_iff_coindep', coindep], 
    refine ⟨B,hB, disjoint_of_subset_left (inter_subset_left _ _) disjoint_compl_left⟩,
end)
(begin
  intros I A hI hIA,
  obtain ⟨J, hIJ, hJ⟩ := hI.subset_basis_of_subset (image_subset coe hIA), 
  have hJcoe : coe '' (coe ⁻¹' J) = J, 
  { rw image_preimage_eq_iff, exact (hJ.subset.trans (image_subset_range _ _)) },
  refine ⟨coe ⁻¹' J, ⟨_,_,_⟩ , _⟩, 
  { dsimp only, convert hJ.indep },
  { rwa [←image_subset_image_iff subtype.coe_injective, hJcoe] },
  { rw [←image_subset_image_iff subtype.coe_injective, hJcoe], exact hJ.subset },
  rintro K ⟨hK, hIK, hKA⟩ hJK, 
  rw hJ.eq_of_subset_indep hK 
    (by rwa [←image_subset_image_iff subtype.coe_injective, hJcoe] at hJK) (image_subset coe hKA), 
  rw [preimage_image_eq _ subtype.coe_injective], 
end)

@[simp] lemma restrict_to.indep_iff {I : set X} : (M.restrict_to X).indep I ↔ M.indep (coe '' I) := 
by simp [restrict_to]

@[simp] lemma restrict_to.base_iff {B : set X} : (M.restrict_to X).base B ↔ M.basis (coe '' B) X :=
begin
  simp_rw [base_iff_maximal_indep, restrict_to.indep_iff, basis_iff], 
  sorry 
end 

-- lemma restrict_to.preimage_basis_of_base {B : set X} (h : (M.restrict_to X).base B) : 
--   M.base (coe ⁻¹' B : set E) := 

@[simp] lemma restrict_to.basis_iff {I A : set X} : 
  (M.restrict_to X).basis I A ↔ M.basis (coe '' I) (coe '' A) := sorry 

lemma basis.base_restrict_to (h : M.basis I X) : (M.restrict_to X).base (coe ⁻¹' I) := sorry 

lemma indep.indep_restrict_to (X : set E) (hI : M.indep I) : (M.restrict_to X).indep (coe ⁻¹' I) := sorry 

lemma basis.basis_restrict_to {A X : set E} (hI : M.basis I A) (hIX : I ⊆ X) : 
  (M.restrict_to X).basis (coe ⁻¹' I) (coe ⁻¹' A) := sorry 


-- lemma restrict_to.restrict_to_subset (M : matroid E) (hXY : X ⊆ Y) : 
--   (M.restrict_to Y).restrict_to X = M.restrict_to X :=
-- begin

-- end 
--   (M.restrict X).restrict Y = M.restrict (X ∩ Y)


-- /-- Turn all elements of the matroid outside `X` into loops -/
-- def lrestrict (M : matroid E) (X : set E) : matroid E :=
-- matroid_of_indep (λ I, M.indep I ∧ I ⊆ X) ⟨M.empty_indep, empty_subset _⟩ 
-- (λ I J hJ hIJ, ⟨hJ.1.subset hIJ, hIJ.trans hJ.2⟩)
-- (begin
--   rintro I I' ⟨hI, hIX⟩ (hIn : ¬M.basis I X) (hI' : M.basis I' X),
--   obtain ⟨B', hB', rfl⟩ := hI'.exists_base, 
--   obtain ⟨B, hB, hIB, hBIB'⟩ := hI.exists_base_subset_union_base hB',
--   rw hB'.inter_basis_iff_compl_inter_basis_dual' at hI', 
--   have hss : B'ᶜ ∩ Xᶜ ⊆ Bᶜ ∩ Xᶜ, 
--   { rw [←compl_union, ←compl_union, compl_subset_compl],
--     exact union_subset 
--       (hBIB'.trans (union_subset (hIX.trans (subset_union_right _ _)) (subset_union_left _ _))) 
--       (subset_union_right _ _) },  
--   have h_eq := hI'.eq_of_subset_indep _ hss (inter_subset_right _ _), 
--   { rw [h_eq, ←hB.inter_basis_iff_compl_inter_basis_dual'] at hI', 
--     have hssu : I ⊂ (B ∩ X) := (subset_inter hIB hIX).ssubset_of_ne 
--       (by { rintro rfl, exact hIn hI' }), 
--     obtain ⟨e,he, heI⟩ := exists_of_ssubset hssu, 
    
--     refine ⟨e, ⟨⟨_,he.2⟩,heI⟩, hI'.indep.subset (insert_subset.mpr ⟨he,hssu.subset⟩), 
--       insert_subset.mpr ⟨he.2, hIX⟩⟩,  
--     exact (hBIB' he.1).elim (λ heI', (heI heI').elim) id },
--   exact dual_indep_iff_coindep'.mpr ⟨B,hB, 
--     disjoint_of_subset_left (inter_subset_left _ _) disjoint_compl_left⟩, 
-- end)
-- (begin
--   rintro I A ⟨hI, hIX⟩ hIA, 
--   obtain ⟨J, hIJ, hJ⟩ := hI.subset_basis_of_subset (subset_inter hIX hIA), 
--   refine ⟨J, ⟨⟨hJ.indep,hJ.subset.trans (inter_subset_left _ _)⟩,hIJ,
--     hJ.subset.trans (inter_subset_right _ _)⟩, λ K hK hJK, _⟩, 
--   rw hJ.eq_of_subset_indep hK.1.1 hJK (subset_inter hK.1.2 hK.2.2), 
-- end)


-- @[simp] lemma lrestrict_indep_iff : (M.lrestrict X).indep I ↔ (M.indep I ∧ I ⊆ X) := 
-- by simp [lrestrict]

-- @[simp] lemma lrestrict_lrestrict : (M.lrestrict X).lrestrict Y = M.lrestrict (X ∩ Y) :=
-- eq_of_indep_iff_indep_forall (λ I, by simp only [and_assoc, lrestrict_indep_iff, subset_inter_iff]) 

-- lemma lrestrict_lrestrict_subset (hXY : X ⊆ Y) : (M.lrestrict Y).lrestrict X = M.lrestrict X :=
-- by rw [lrestrict_lrestrict, inter_eq_right_iff_subset.mpr hXY]
 
-- lemma indep.indep_lrestrict_of_subset (hI : M.indep I) (hIX : I ⊆ X) : (M.lrestrict X).indep I :=
-- lrestrict_indep_iff.mpr ⟨hI, hIX⟩ 

-- @[simp] lemma lrestrict_base_iff : (M.lrestrict X).base I ↔ M.basis I X :=
-- by { simp_rw [base_iff_maximal_indep', lrestrict_indep_iff], refl }

-- lemma basis.base_lrestrict (h : M.basis I X) : (M.lrestrict X).base I := lrestrict_base_iff.mpr h

-- lemma basis.basis_lrestrict_of_subset (hI : M.basis I X) (hXY : X ⊆ Y) :
--   (M.lrestrict Y).basis I X :=
-- by rwa [←lrestrict_base_iff, lrestrict_lrestrict_subset hXY, lrestrict_base_iff]

end minor 


lemma basis.transfer (hIX : M.basis I X) (hJX : M.basis J X) (hXY : X ⊆ Y) (hJY : M.basis J Y) : 
  M.basis I Y :=
begin
  
  -- refine restrict_to.base_iff.mp _, 
  have := hJY.base_restrict_to.base_of_basis_supset, 
  
  -- rw [←restrict_to.basis_iff] at ⊢, 
  rw [←lrestrict_base_iff] at ⊢ hJY, 
  exact hJY.base_of_basis_supset hJX.subset (hIX.basis_lrestrict_of_subset hXY),  
end 

lemma basis.transfer' (hI : M.basis I X) (hJ : M.basis J Y) (hJX : J ⊆ X) (hIY : I ⊆ Y) : 
  M.basis I Y :=
begin
  have hI' := hI.basis_subset (subset_inter hI.subset hIY) (inter_subset_left _ _), 
  have hJ' := hJ.basis_subset (subset_inter hJX hJ.subset) (inter_subset_right _ _), 
  exact hI'.transfer hJ' (inter_subset_right _ _) hJ, 
end 

lemma basis.transfer'' (hI : M.basis I X) (hJ : M.basis J Y) (hJX : J ⊆ X) : M.basis I (I ∪ Y) :=
begin
  obtain ⟨J', hJJ', hJ'⟩  := hJ.indep.subset_basis_of_subset hJX, 
  have hJ'Y := (hJ.basis_union_of_subset hJ'.indep hJJ').basis_union hJ', 
  refine (hI.transfer' hJ'Y hJ'.subset _).basis_subset _ _,  
  { exact subset_union_of_subset_right hI.subset _ },
  { exact subset_union_left _ _ }, 
  refine union_subset (subset_union_of_subset_right hI.subset _) _,
  rw union_right_comm, 
  exact subset_union_right _ _, 
end 

lemma indep.exists_basis_subset_union_basis (hI : M.indep I) (hIX : I ⊆ X) (hJ : M.basis J X) : 
  ∃ I', M.basis I' X ∧ I ⊆ I' ∧ I' ⊆ I ∪ J :=
begin
  obtain ⟨I', hI', hII', hI'IJ⟩ := 
    (hI.indep_lrestrict_of_subset hIX).exists_base_subset_union_base hJ.base_lrestrict, 
  exact ⟨I', lrestrict_base_iff.mp hI', hII', hI'IJ⟩, 
end 

lemma basis.exchange (hIX : M.basis I X) (hJX : M.basis J X) (he : e ∈ I \ J) : 
  ∃ f ∈ J \ I, M.basis (insert f (I \ {e})) X :=
by { simp_rw ←lrestrict_base_iff at *, exact hIX.exchange hJX he }

lemma basis.eq_exchange_of_diff_eq_singleton (hI : M.basis I X) (hJ : M.basis J X) 
(hIJ : I \ J = {e}) : 
  ∃ f ∈ J \ I, J = (insert f I) \ {e} :=
by { rw [←lrestrict_base_iff] at hI hJ, exact hI.eq_exchange_of_diff_eq_singleton hJ hIJ }

section finite

lemma basis.card_eq_card_of_basis (hIX : M.basis I X) (hJX : M.basis J X) : I.ncard = J.ncard :=
by { rw [←lrestrict_base_iff] at hIX hJX, exact hIX.card_eq_card_of_base hJX }

lemma basis.finite_of_finite (hIX : M.basis I X) (hI : I.finite) (hJX : M.basis J X)  : J.finite := 
by { rw [←lrestrict_base_iff] at hIX hJX, exact hIX.finite_of_finite hI hJX }

lemma basis.infinite_of_infinite (hIX : M.basis I X) (hI : I.infinite) (hJX : M.basis J X) : 
  J.infinite := 
by { rw [←lrestrict_base_iff] at hIX hJX, exact hIX.infinite_of_infinite hI hJX }

lemma basis.card_diff_eq_card_diff (hIX : M.basis I X) (hJX : M.basis J X) : 
  (I \ J).ncard = (J \ I).ncard :=
by { rw [←lrestrict_base_iff] at hIX hJX, rw hJX.card_diff_eq_card_diff hIX }

lemma basis.diff_finite_comm (hIX : M.basis I X) (hJX : M.basis J X) :
  (I \ J).finite ↔ (J \ I).finite := 
by { rw [←lrestrict_base_iff] at hIX hJX, exact hIX.diff_finite_comm hJX }

lemma basis.diff_infinite_comm (hIX : M.basis I X) (hJX : M.basis J X) :
  (I \ J).infinite ↔ (J \ I).infinite := 
by { rw [←lrestrict_base_iff] at hIX hJX, exact hIX.diff_infinite_comm hJX }

/-- `M.r_fin X` means that `X` has a finite basis in `M`-/
def r_fin (M : matroid E) (X : set E) : Prop := ∃ I, M.basis I X ∧ I.finite  

lemma to_r_fin (M : matroid E) [finite_rk M] (X : set E) : M.r_fin X :=  
by { obtain ⟨I,hI⟩ := M.exists_basis X, exact ⟨I, hI, hI.finite⟩ }

lemma basis.finite_of_r_fin (h : M.basis I X) (hX : M.r_fin X) : I.finite :=
by { obtain ⟨J, hJ, hJfin⟩ := hX, exact hJ.finite_of_finite hJfin h }

lemma basis.r_fin_of_finite (hIX : M.basis I X) (h : I.finite) : M.r_fin X := ⟨I, hIX, h⟩ 

lemma r_fin.subset (h : M.r_fin Y) (hXY : X ⊆ Y) : M.r_fin X := 
begin
  obtain ⟨I, hI⟩ := M.exists_basis X, 
  obtain ⟨J, hIJ, hJ⟩ := hI.indep.subset_basis_of_subset (hI.subset.trans hXY),    
  exact hI.r_fin_of_finite ((hJ.finite_of_r_fin h).subset hIJ), 
end 

lemma indep.augment_of_finite (hI : M.indep I) (hJ : M.indep J) (hIfin : I.finite) 
(hIJ : I.ncard < J.ncard) :
  ∃ x ∈ J, x ∉ I ∧ M.indep (insert x I) :=
begin
  obtain ⟨K, hK, hIK⟩ :=  
    (hI.indep_lrestrict_of_subset (subset_union_left I J)).exists_base_supset, 
  obtain ⟨K', hK', hJK'⟩ :=
    (hJ.indep_lrestrict_of_subset (subset_union_right I J)).exists_base_supset, 
  have hJfin := finite_of_ncard_pos ((nat.zero_le _).trans_lt hIJ), 
  rw lrestrict_base_iff at hK hK', 
  have hK'fin := (hIfin.union hJfin).subset hK'.subset, 
  have hlt := 
    hIJ.trans_le ((ncard_le_of_subset hJK' hK'fin).trans_eq (hK'.card_eq_card_of_basis hK)), 
  obtain ⟨e,he⟩ := exists_mem_not_mem_of_ncard_lt_ncard hlt hIfin, 
  exact ⟨e, (hK.subset he.1).elim (false.elim ∘ he.2) id, 
    he.2, hK.indep.subset (insert_subset.mpr ⟨he.1,hIK⟩)⟩, 
end 


/-- The independence augmentation axiom; given independent sets `I,J` with `I` smaller than `J`,
  there is an element `e` of `J \ I` whose insertion into `e` is an independent set.  -/
lemma indep.augment [finite_rk M] (hI : M.indep I) (hJ : M.indep J) (hIJ : I.ncard < J.ncard) :
  ∃ x ∈ J, x ∉ I ∧ M.indep (insert x I) :=
hI.augment_of_finite hJ hI.finite hIJ

/-- The independence augmentation axiom in a form that finds a strict superset -/
lemma indep.ssubset_indep_of_card_lt_of_finite (hI : M.indep I) (hI_fin : I.finite) (hJ : M.indep J) 
(hIJ : I.ncard < J.ncard) :
  ∃ I', M.indep I' ∧ I ⊂ I' ∧ I' ⊆ I ∪ J :=
begin
  obtain ⟨e, heJ, heI, hI'⟩ := hI.augment_of_finite hJ hI_fin hIJ ,
  exact ⟨_, hI', ssubset_insert heI, insert_subset.mpr ⟨or.inr heJ,subset_union_left _ _⟩⟩,
end

lemma indep.ssubset_indep_of_card_lt [finite_rk M] (hI : M.indep I) (hJ : M.indep J) 
(hIJ : I.ncard < J.ncard) :
  ∃ I', M.indep I' ∧ I ⊂ I' ∧ I' ⊆ I ∪ J :=
hI.ssubset_indep_of_card_lt_of_finite hI.finite hJ hIJ

lemma indep.le_card_basis_of_r_fin (hI : M.indep I) (hIX : I ⊆ X) (hX : M.r_fin X) 
(hXJ : M.basis J X) : I.ncard ≤ J.ncard :=
begin
  obtain ⟨I', hI'⟩ := hI.subset_basis_of_subset hIX, 
  rw hXJ.card_eq_card_of_basis hI'.2, 
  exact ncard_le_of_subset hI'.1 (hI'.2.finite_of_r_fin hX), 
end 

lemma indep.le_card_basis [finite_rk M] (hI : M.indep I) (hIX : I ⊆ X) (hJX : M.basis J X) :
  I.ncard ≤ J.ncard :=
begin
  refine le_of_not_lt (λ hlt, _),
  obtain ⟨I', hI'⟩ := hJX.indep.ssubset_indep_of_card_lt hI hlt,
  have := hJX.eq_of_subset_indep hI'.1 hI'.2.1.subset (hI'.2.2.trans (union_subset hJX.subset hIX)),
  subst this,
  exact hI'.2.1.ne rfl,
end

end finite

end matroid

section from_axioms

/-- A collection of sets satisfying the independence axioms determines a matroid -/
def matroid_of_indep [finite E] (indep : set E → Prop)
(exists_ind : ∃ I, indep I)
(ind_mono : ∀ I J, I ⊆ J → indep J → indep I)
(ind_aug : ∀ I J, indep I → indep J → I.ncard < J.ncard →
  ∃ e ∈ J, e ∉ I ∧ indep (insert e I)) :
  matroid E := matroid.matroid_of_base_of_finite
  (λ B, indep B ∧ ∀ X, indep X → B ⊆ X → X = B)
  ( by exact
      (@set.finite.exists_maximal_wrt (set E) (set E) _ id indep (to_finite _) exists_ind).imp
      (λ B hB, exists.elim hB (λ hB h, ⟨hB, λ X hX hBX, (h X hX hBX).symm⟩)))
  (begin
    set is_base := λ (B : set E), indep B ∧ ∀ X, indep X → B ⊆ X → X = B with hbase,
    rintro B₁ B₂ hB₁ hB₂ x ⟨hxB₁,hxB₂⟩,

    have h_base_iff : ∀ B B' (hB' : is_base B'),
      is_base B ↔ indep B ∧ B'.ncard ≤ B.ncard,
    { intros B B' hB', split,
      { refine λ hB, ⟨hB.1, le_of_not_lt (λ hlt, _)⟩,
        obtain ⟨e,heB,heB',he⟩ := ind_aug B B' hB.1 hB'.1 hlt,
        exact heB' (by simpa using hB.2 _ he (subset_insert _ _))},
      rintros ⟨hBI, hB'B⟩ ,
      refine ⟨hBI, λ J hJ hBJ, (hBJ.antisymm (by_contra (λhJB, _))).symm⟩,
      have hss := ssubset_of_subset_not_subset hBJ hJB,
      obtain ⟨e,heJ,heB',he⟩ :=
        ind_aug B' J hB'.1 hJ (hB'B.trans_lt (ncard_lt_ncard hss)),
      exact heB' (by simpa using hB'.2 _ he (subset_insert _ _))},

    simp_rw [h_base_iff _ _ hB₁, mem_diff],
    have hcard : (B₁ \ {x}).ncard < B₂.ncard,
    { rw [nat.lt_iff_add_one_le, ncard_diff_singleton_add_one hxB₁],
      exact ((h_base_iff _ _ hB₁).mp hB₂).2},

    obtain ⟨e,heB₂,heB₁x,he⟩ :=
      ind_aug (B₁ \ {x}) B₂ (ind_mono _ _ (diff_subset _ _) hB₁.1) hB₂.1 hcard,
    have hex : e ≠ x := by {rintro rfl, exact hxB₂ heB₂},
    have heB₁ : e ∉ B₁,
    { simp only [mem_diff, mem_singleton_iff, not_and, not_not] at heB₁x,
      exact λ h', hex (heB₁x h')},

    refine ⟨e,⟨heB₂,heB₁⟩,he,_⟩,
    rwa [ncard_insert_of_not_mem heB₁x, ncard_diff_singleton_add_one],
  end )

@[simp] lemma matroid_of_indep_base_iff [finite E] {indep : set E → Prop}
  (exists_ind : ∃ I, indep I)
  (ind_mono : ∀ I J, I ⊆ J → indep J → indep I)
  (ind_aug : ∀ I J, indep I → indep J → I.ncard < J.ncard →
    ∃ e ∈ J, e ∉ I ∧ indep (insert e I)) {B : set E }:
(matroid_of_indep indep exists_ind ind_mono ind_aug).base B ↔
  indep B ∧ ∀ X, indep X → B ⊆ X → X = B :=
iff.rfl

@[simp] lemma matroid_of_indep_apply [finite E] {indep : set E → Prop}
  (exists_ind : ∃ I, indep I)
  (ind_mono : ∀ I J, I ⊆ J → indep J → indep I)
  (ind_aug : ∀ I J, indep I → indep J → I.ncard < J.ncard →
    ∃ e ∈ J, e ∉ I ∧ indep (insert e I)) :
  (matroid_of_indep indep exists_ind ind_mono ind_aug).indep = indep :=
begin
  ext I,
  simp_rw [matroid.indep_iff_subset_base, matroid_of_indep],
  split,
  { rintro ⟨B, ⟨hBi,hB⟩, hIB⟩,
    exact ind_mono _ _ hIB hBi},
  intro hI,
  obtain ⟨B,hBi, hB⟩ :=
    @set.finite.exists_maximal_wrt (set E) (set E) _ id {J | I ⊆ J ∧ indep J} (to_finite _)
    ⟨I, subset_refl I, hI⟩,
  simp only [mem_set_of_eq, id.def, le_eq_subset, and_imp] at hB hBi,
  exact ⟨B, ⟨hBi.2, λ X hX hBX, (hB _ (hBi.1.trans hBX) hX hBX).symm⟩, hBi.1⟩,
end

end from_axioms




/- Another version of the independence axioms that doesn't mention cardinality. TODO -/
-- def matroid_of_indep' (indep : set E → Prop) (exists_ind : ∃ I, indep I)
-- (ind_mono : ∀ I J, I ⊆ J → indep J → indep I)
-- (ind_aug : ∀ I J, indep I → indep J → (∃ I', I ⊂ I' ∧ indep I') → (∀ J', J ⊂ J' → ¬indep J')
--   → (∃ x ∈ J \ I, indep (insert x I))) :
--   matroid E :=
-- { base := λ B, indep B ∧ ∀ I, B ⊆ I → indep I → I = B,
--   exists_base' :=
--   begin
--     obtain ⟨B,hB,hBmax⟩ := finite.exists_maximal indep exists_ind,
--     exact ⟨B, hB, λ I hBI hI, (hBmax _ hI hBI).symm⟩,
--   end,
--   base_exchange' :=
--   begin
--     rintro B₁ B₂ ⟨hB₁,hB₁max⟩ ⟨hB₂,hB₂max⟩ x hx,
--     obtain ⟨y,hy,hyI⟩ := ind_aug (B₁ \ {x}) B₂ (ind_mono _ _ (diff_subset _ _) hB₁) hB₂
--       ⟨B₁, diff_singleton_ssubset.2 hx.1, hB₁⟩
--       (λ J hB₂J hJ, hB₂J.ne ((hB₂max _ hB₂J.subset hJ).symm)),
--     refine ⟨y, mem_of_mem_of_subset hy _, hyI, λ I hyI hI, _⟩  ,
--     { rw [diff_diff_right, inter_singleton_eq_empty.mpr hx.2, union_empty]},


--     -- rintro I J hI hJ hImax ⟨J',hJJ',hJ'⟩,

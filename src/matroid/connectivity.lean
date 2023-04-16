import .dual 

open_locale classical 
open_locale big_operators
open set 

namespace matroid

variables {E ι : Type*} {X Y X' Y'  I J C : set E} {e f : E} {M : matroid E}

/-- Two sets are `skew` if any pair of their independent subsets are disjoint with independent union (equivalently, the sum of their ranks is the rank of their union) -/
def skew (M : matroid E) (X Y : set E) : Prop :=
  ∀ (I ⊆ X) (J ⊆ Y), M.indep I → M.indep J → disjoint I J ∧ M.indep (I ∪ J) 

lemma skew.symm (h : M.skew X Y) : M.skew Y X := 
λ J hJY I hIX hJ hI, let s := h I hIX J hJY hI hJ in ⟨s.1.symm, by { rw union_comm, exact s.2 }⟩  

lemma skew.comm : M.skew X Y ↔ M.skew Y X := ⟨skew.symm, skew.symm⟩ 

lemma empty_skew (M : matroid E) (X : set E) : M.skew ∅ X := 
λ I hIe J hJY hI hJ, ⟨disjoint_of_subset_left hIe (empty_disjoint _), 
  by rwa [subset_empty_iff.mp hIe, empty_union]⟩   

lemma skew_empty (M : matroid E) (X : set E) : M.skew X ∅ := (M.empty_skew X).symm 

lemma skew.subset_left (h : M.skew X Y) (hX'X : X' ⊆ X) : M.skew X' Y :=
λ I hIX' J hJY hI hJ, h I (hIX'.trans hX'X) J hJY hI hJ 

lemma skew.subset_right (h : M.skew X Y) (hY'Y : Y' ⊆ Y) : M.skew X Y' :=
(h.symm.subset_left hY'Y).symm 

lemma skew.loop_of_inter (h : M.skew X Y) (he : e ∈ X ∩ Y) : M.loop e :=
begin
  rw [loop_iff_dep], intro hi, 
  rw [←singleton_subset_iff, subset_inter_iff] at he, 
  exact (h _ he.1 _ he.2 hi hi).1.ne_of_mem (mem_singleton _) (mem_singleton _) rfl, 
end 

lemma skew_of_subset_loops (h : X ⊆ M.cl ∅) (Y : set E) : M.skew X Y := 
λ I hIX J hJY hI hJ, by { rw hI.eq_empty_of_subset_loops (hIX.trans h), simpa } 

lemma subset_loops_skew (X : set E) (h : Y ⊆ M.cl ∅) : M.skew X Y := (skew_of_subset_loops h X).symm 

lemma loop.singleton_skew (he : M.loop e) (X : set E) : M.skew {e} X := 
skew_of_subset_loops (singleton_subset_iff.mpr he) X 

lemma loop.skew_singleton (he : M.loop e) (X : set E) : M.skew X {e} := 
subset_loops_skew X (singleton_subset_iff.mpr he)

lemma basis.skew (hI : M.basis I X) (hJ : M.basis J Y) (hdj : disjoint I J) (hi : M.indep (I ∪ J)) :
  M.skew X Y :=
begin
  refine λ I' hI'X J' hJ'Y hI' hJ', _,
  obtain ⟨I₁, hII₁, hI₁⟩ := hI'.subset_basis_of_subset (subset_union_left I' I), 
  obtain ⟨J₁, hJJ₁, hJ₁⟩ := hJ'.subset_basis_of_subset (subset_union_left J' J),  
  
  have hdj' : disjoint I₁ J₁, 
  { rw disjoint_iff_forall_ne, 
    rintro e heI₁ f hfJ₁ rfl,
    
    -- have hb : M.basis (I₁ ∪ J₁)
      },
  -- ⟨disjoint_iff_forall_ne.mpr _,_⟩, 
  { 
     },

   
end 


lemma indep.skew_of_exists (hI : M.indep I) (hIXY : I ⊆ X ∪ Y) (hdj : disjoint (I ∩ X) (I ∩ Y))
(hIX : M.basis (I ∩ X) X) (hIY : M.basis (I ∩ Y) Y) : M.skew X Y :=
begin
  intros I' hI' J' hJ' hI' hJ', 
end 

lemma skew_iff_r [finite_rk M] :
  M.skew X Y ↔ M.r X + M.r Y = M.r (X ∪ Y) :=
begin
  refine ⟨λ h, _, λ hXY, λ I hIX J hJY hI hJ, _⟩,
  { obtain ⟨⟨I,hI⟩,⟨J,hJ⟩⟩ := ⟨M.exists_basis X, M.exists_basis Y⟩, 
    obtain ⟨hdj, hIJ⟩ := h I hI.subset J hJ.subset hI.indep hJ.indep,  
    rw [hI.r_eq_card, hJ.r_eq_card, ←ncard_union_eq hdj hI.finite hJ.finite, ←hIJ.r], 
    refine (M.r_mono (union_subset_union hI.subset hJ.subset)).antisymm _, 
    rw [←M.r_union_cl_left_eq_r_union I J, hI.cl, ←M.r_union_cl_right_eq_r_union _ J, 
      hJ.cl, r_union_cl_left_eq_r_union, r_union_cl_right_eq_r_union]},

  obtain ⟨J', hJJ', hJ'⟩ := hJ.subset_basis_of_subset hJY,
  obtain ⟨I', hII', hI'⟩ := hI.subset_basis_of_subset hIX,   
  
  rw [hI'.r_eq_card, hJ'.r_eq_card, ←r_union_cl_left_eq_r_union, ←hI'.cl, 
    r_union_cl_left_eq_r_union, ←r_union_cl_right_eq_r_union, ←hJ'.cl, 
    r_union_cl_right_eq_r_union, ←ncard_union_add_ncard_inter _ _ hI'.finite hJ'.finite ] at hXY, 

  have hle := (M.r_le_card_of_finite (hI'.finite.union hJ'.finite)), 
    
  refine ⟨disjoint_of_subset hII' hJJ' _, indep.subset _ (union_subset_union hII' hJJ')⟩, 
  { rw [disjoint_iff_inter_eq_empty, ←ncard_eq_zero (hI'.finite.subset (inter_subset_left _ _))], 
    linarith },
  rw [indep_iff_r_eq_card_of_finite (hI'.finite.union hJ'.finite)], 
  linarith,
end 

lemma skew.r_add [finite_rk M] (h : M.skew X Y) : M.r X + M.r Y = M.r (X ∪ Y) := skew_iff_r.mp h 

/- these proofs doesn't need to use rank, but are much easier that way for now  -/
lemma skew.cl_left [finite_rk M] (h : M.skew X Y) : M.skew (M.cl X) Y := 
by rwa [skew_iff_r, r_union_cl_left_eq_r_union, r_cl, ←skew_iff_r]

lemma skew.cl_left' (h : M.skew X Y) : M.skew (M.cl X) Y :=
begin
  intros I hIX J hJY hI hJ, 
  
end 

lemma skew.cl_left_iff [finite_rk M] : M.skew X Y ↔ M.skew (M.cl X) Y := 
⟨skew.cl_left, λ h, h.subset_left (M.subset_cl X)⟩ 

lemma skew.cl_right [finite_rk M] (h : M.skew X Y) : M.skew X (M.cl Y) := 
by rwa [skew_iff_r, r_union_cl_right_eq_r_union, r_cl, ←skew_iff_r]

lemma skew.cl_right_iff [finite_rk M] : M.skew X Y ↔ M.skew X (M.cl Y) := 
⟨skew.cl_right, λ h, h.subset_right (M.subset_cl Y)⟩ 

lemma nonloop.skew_singleton_iff [finite_rk M] (he : M.nonloop e) : M.skew X {e} ↔ e ∉ M.cl X :=
begin
  refine ⟨λ h hl, he (h.cl_left.loop_of_inter ⟨hl, mem_singleton _⟩), λ h I hIX J hJe hI hJ, _⟩, 
  obtain (rfl | rfl) := subset_singleton_iff_eq.mp hJe, 
  { simpa },
  simp only [disjoint_singleton_right, union_singleton],  
  refine ⟨not_mem_subset (hIX.trans (M.subset_cl X)) h, (hI.insert_indep_iff_of_not_mem _).mpr _⟩, 
  all_goals {refine not_mem_subset _ h }, 
  { exact hIX.trans (subset_cl _ _) },
  exact M.cl_mono hIX,
end 

lemma nonloop.singleton_skew_iff [finite_rk M] (he : M.nonloop e) : M.skew {e} X ↔ e ∉ M.cl X := 
by rw [←he.skew_singleton_iff, skew.comm]

end matroid
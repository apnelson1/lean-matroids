
import matroid.rankfun set_tactic.solver matroid.submatroid.order

open set 
open matroid 

namespace matroid 
variables {U : Type}[nonempty (fintype U)]

/-- contract C and replace it with a set of loops to get a matroid on the same ground set.  
Often more convenient than just contracting C  -/
def project (M : matroid U) (C : set U) : matroid U := 
{ 
  r := λ X, M.r (X ∪ C) - M.r C,
  R0 := λ X, by {simp only, linarith [M.rank_mono (subset_union_right X C)]},
  R1 := λ X, by {simp only, linarith [M.R0 (X ∩ C), M.R3 X C, M.R1 X]},
  R2 := λ X Y hXY, by {simp only, linarith [M.rank_mono (subset_union_subset_left _ _ C hXY)]},
  R3 := λ X Y, by {simp_rw [union_comm _ C], linarith [submod_three_sets M C X Y]} 
}
/-- Replace D with loops to get a matroid on the same ground set. Often more 
convenient than deleting D -/
def loopify (M : matroid U)(D : set U) : matroid U := 
{
  r := λ X, M.r (X \ D), 
  R0 := λ X, M.R0 _, 
  R1 := λ X, by linarith [M.R1 (X \ D), size_diff_le_size X D], 
  R2 := λ X Y hXY, M.rank_mono (diff_subset_diff D hXY), 
  R3 := λ X Y, by {simp only [diff_eq], rw [inter_distrib_right, inter_distrib_inter_left], 
                    linarith [M.rank_submod (X ∩ Dᶜ) (Y ∩ Dᶜ)],  }
}


infix ` ⟋ ` :75 :=  matroid.project  

infix ` ⟍ ` :75 :=  matroid.loopify 
   
@[simp] lemma loopify_r (M : matroid U)(D X : set U):
  (M ⟍ D).r X = M.r (X \ D) := 
rfl 

@[simp] lemma project_r (M : matroid U)(C X : set U):
  (M ⟋ C).r X = M.r (X ∪ C) - M.r C := 
rfl 

lemma project_rank (M : matroid U)(C : set U):
  (M ⟋ C).r univ = M.r univ - M.r C := 
by rw [project_r, univ_union]

def loopify_project (M : matroid U)(C D : set U) : matroid U := 
  project (loopify M D) C 

lemma project_is_weak_image (M : matroid U)(C : set U):
  M ⟋ C ≤ M := 
λ X, by {rw project_r, linarith [M.rank_subadditive X C]}

lemma project_project (M : matroid U)(C C' : set U): 
  M ⟋ C ⟋ C' = M ⟋ (C ∪ C') :=
by {rw union_comm, ext X, simp only [project_r, ←union_assoc], linarith, }

lemma project_is_quotient (M : matroid U)(C : set U):
  M ⟋ C ≼ M := 
begin
  intros X Y hXY, simp_rw project_r, 
  have hY := (union_diff_cancel hXY).symm, 
  have hle : (M ⟋ Y) ≤ (M ⟋ X) := by {rw [hY, ←project_project],apply project_is_weak_image },
  specialize hle C, 
  simp only [project_r, union_comm C] at hle, 
  linarith, 
end

lemma project_makes_loops (M : matroid U)(C : set U):
  loops M ∪ C ⊆ loops (M ⟋ C)  := 
by rw [←rank_zero_iff_subset_loops, project_r, union_assoc, union_self, 
        union_comm, rank_eq_rank_union_rank_zero C (rank_loops M), sub_self]

lemma projected_set_rank_zero (M : matroid U)(C : set U):
  (M ⟋ C).r C = 0 := 
by rw [project_r, union_self, sub_self] 

lemma projected_set_union_rank_zero (M : matroid U)(C : set U){X : set U}(hX : M.r X = 0):
  (M ⟋ C).r (X ∪ C) = 0 :=
by rwa [project_r, union_comm X, union_left_absorb, rank_eq_rank_union_rank_zero, sub_self]
  
lemma loopify_is_weak_image (M : matroid U)(D : set U):  
  M ⟍ D ≤ M :=
λ X, rank_mono_diff _ _ _ 

lemma project_rank_zero_eq {M : matroid U}{C : set U}(h : M.r C = 0):
  M ⟋ C = M := 
by {ext X, rw [project_r, rank_eq_rank_union_rank_zero X h, h, sub_zero]}

lemma project_rank_zero_of_rank_zero {M : matroid U}(C : set U){X : set U}(hX : M.r X = 0):
  (M ⟋ C).r X = 0 := 
by {apply rank_eq_zero_of_le_zero, rw ←hX, apply project_is_weak_image}

lemma loopify_loopify (M : matroid U)(D D' : set U):
   M ⟍ D ⟍ D' = M ⟍ (D ∪ D') :=
by {ext X, simp [diff_eq, ←inter_assoc, inter_right_comm]}

lemma loopify_makes_loops (M : matroid U)(D : set U): 
  loops M ∪ D ⊆ loops (M ⟍ D) := 
by {rw [←rank_zero_iff_subset_loops, loopify_r, rank_zero_iff_subset_loops], tidy,}

lemma loopify_rank_zero_eq {M : matroid U}{D : set U}(h : M.r D = 0):
  M ⟍ D = M := 
by {ext X, rw [loopify_r, rank_eq_rank_diff_rank_zero X h]}


lemma loopified_set_rank_zero (M : matroid U)(D : set U):
  (M ⟍ D).r D = 0 :=
by rw [loopify_r, set.diff_self, rank_empty] 

lemma loopified_set_union_rank_zero (M : matroid U)(D : set U){X : set U}(h: M.r X = 0):
  (M ⟍ D).r (X ∪ D) = 0 :=
by {simp only [loopify_r, union_left_absorb, union_comm X], 
    exact rank_zero_of_subset_rank_zero (by {intro x, simp, tauto}) h}

lemma loopify_rank_zero_of_rank_zero {M : matroid U}(D : set U){X : set U}(hX : M.r X = 0):
  (M ⟍ D).r X = 0 := 
by {apply rank_eq_zero_of_le_zero, rw ←hX, apply loopify_is_weak_image}

lemma loopify_rank_of_disjoint (M : matroid U){D X : set U}(h : D ∩ X = ∅):
  (M ⟍ D).r X = M.r X := 
by {rw loopify_r, congr, rwa [inter_comm, disjoint_iff_diff_eq_left] at h}

lemma indep_of_loopify_indep {M : matroid U}{D X : set U}(hX : is_indep (M ⟍ D) X) : 
  is_indep M X := 
indep_of_weak_image_indep (loopify_is_weak_image M D) hX

lemma indep_of_project_indep {M : matroid U}{C X : set U}(h: is_indep (M ⟋ C) X): 
   is_indep M X :=
indep_of_weak_image_indep (project_is_weak_image M C) h

lemma indep_union_project_set_of_project_indep {M : matroid U}{C X : set U}
(hX : is_indep (M ⟋ C) X)(hC : is_indep M C):
is_indep M (X ∪ C) :=
by {simp_rw [indep_iff_r, project_r] at *, 
    linarith [M.R1 (X ∪ C), size_modular X C, size_nonneg (X ∩ C)]}

/-- loopify all elements of M outside R -/
def loopify_to (M : matroid U)(R : set U) : matroid U := M ⟍ (Rᶜ)

reserve infixl ` ‖ `:75
infix ` ‖ ` :=  matroid.loopify_to

lemma loopify_as_loopify_to (M : matroid U)(D : set U): 
  (M ⟍ D) = (M ‖ Dᶜ) := 
by rw [loopify_to, compl_compl]

/-- project all elements of M outside R -/
def project_to (M : matroid U)(R : set U) : matroid U := M ⟋ (Rᶜ)

lemma project_as_project_to (M : matroid U)(C : set U): 
  (M ⟋ C) = M.project_to Cᶜ := 
by rw [project_to, compl_compl]

lemma rank_loopify_to (M : matroid U)(R X : set U) : 
  (M ‖ R).r X = M.r (X ∩ R) := 
by simp [diff_eq, loopify_to, loopify_r]

lemma rank_project_to (M : matroid U)(R X : set U):
  (M.project_to R).r X = M.r (X ∪ Rᶜ) - M.r Rᶜ := 
by rw [project_to, project_r]

lemma indep_loopify_to_iff {M : matroid U}{R I : set U} : 
  (M ‖ R).is_indep I ↔ M.is_indep I ∧ I ⊆ R := 
begin
  rw [indep_iff_r, rank_loopify_to, indep_iff_r],
  refine ⟨λ h, _, λ h, by {cases h with h h', rwa subset_iff_inter_eq_left.mp h'}⟩,
  have h' : I ∩ R = I, 
  { apply eq_of_eq_size_subset (inter_subset_left _ _), 
    refine le_antisymm (size_mono_inter_left _ _) _,
    rw ←h, apply rank_le_size },
  rw [←h, h', subset_iff_inter_eq_left],
  simpa, 
end

lemma indep_loopify_iff {M : matroid U}{X D : set U}: 
  (M ⟍ D).is_indep X ↔ M.is_indep X ∧ X ∩ D = ∅ := 
by rw [loopify_as_loopify_to, indep_loopify_to_iff, subset_compl_iff_disjoint]

lemma indep_of_indep_loopify_to {M : matroid U}{R I : set U}(hI : (M ‖ R).is_indep I):
  M.is_indep I := 
(indep_loopify_to_iff.mp hI).1

lemma indep_loopify_to_subset_is_indep {M : matroid U}{S R I : set U}
(hSR: S ⊆ R)(hI: (M ‖ S).is_indep I ):
  (M ‖ R).is_indep I := 
by {simp_rw [indep_loopify_to_iff] at *, exact ⟨hI.1, subset.trans hI.2 hSR⟩} 

lemma indep_project_iff {M : matroid U}{X C : set U}:
  (M ⟋ C).is_indep X ↔ M.is_indep X ∧ M.r (X ∪ C) = M.r X + M.r C := 
begin
  rw [indep_iff_r,project_r, indep_iff_r], 
  refine ⟨λ h, ⟨_,_⟩, λ h, _⟩, 
  { refine le_antisymm (M.rank_le_size _) _, rw ←h, linarith [rank_subadditive M X C]},
  { refine le_antisymm (M.rank_subadditive X C) _, 
    rw (by linarith : M.r (X ∪ C) = M.r C + size X), 
    linarith [M.rank_le_size X], },
  rw [←h.1, h.2], simp, 
end

lemma flat_of_flat_project {M : matroid U}{F C : set U}(h : (M ⟋ C).is_flat F): 
   M.is_flat F := 
flat_of_quotient_flat (project_is_quotient _ _) h 

lemma flat_project_iff {M : matroid U}{F C : set U}: 
  (M ⟋ C).is_flat F ↔ M.is_flat F ∧ C ⊆ F :=
begin
  refine ⟨λ h, ⟨flat_of_flat_project h,_⟩, λ h, _⟩, 
  { refine subset.trans _ (loops_subset_flat _ h),  
    rw ←rank_zero_iff_subset_loops,
    apply projected_set_rank_zero, },
  simp_rw [flat_iff_r, project_r, union_comm F C, subset_iff_union_eq_left.mp h.2], 
  intros Y hFY, 
  suffices : M.r F < M.r Y, linarith [rank_mono_union_left M Y C], 
  exact h.1 _ hFY, 
end

section pminor

/-- a pminor (pseudominor) of a matroid M is a matroid on the same ground set arising from loopifications and/or
projections of M  -/
def is_pminor_of (N M : matroid U) := 
  ∃ C D, N = M ⟋ C ⟍ D 

lemma pr_lp_eq_lp_pr (M : matroid U)(C D : set U):
  M ⟋ C ⟍ D = M ⟍ (D \ C) ⟋ C :=
by {ext X, simp only [loopify_r, project_r], convert rfl; {ext, simp, tauto! }}
  
lemma lp_pr_eq_pr_lp (M : matroid U)(C D : set U):
  M ⟍ D ⟋ C = M ⟋ (C \ D) ⟍ D :=
by {ext X, simp only [loopify_r, project_r], convert rfl; {ext, simp, tauto! }}

lemma rank_zero_of_lp_pr (M : matroid U)(C D : set U):
  (M ⟍ D ⟋ C).r (C ∪ D) = 0 := 
begin
  apply rank_zero_of_union_rank_zero, apply projected_set_rank_zero, 
  apply project_rank_zero_of_rank_zero, apply loopified_set_rank_zero, 
end

lemma rank_zero_of_pr_lp (M : matroid U)(C D : set U):
  (M ⟋ C ⟍ D).r (C ∪ D) = 0 := 
begin
  apply rank_zero_of_union_rank_zero, 
  apply loopify_rank_zero_of_rank_zero, apply projected_set_rank_zero, 
  apply loopified_set_rank_zero,
end

lemma pminor_iff_exists_lp_pr_disjoint {N M : matroid U} :
  N.is_pminor_of M ↔ ∃ C D, C ∩ D = ∅ ∧ N = M ⟍ D ⟋ C :=
begin
  split, rintros ⟨C,D,h⟩, refine ⟨C,D \ C, ⟨by simp ,_⟩ ⟩, rwa ←pr_lp_eq_lp_pr, 
  rintros ⟨C,D,hCD,h⟩, refine ⟨C \ D, D, _⟩, rwa ←lp_pr_eq_pr_lp, 
end

lemma pminor_iff_exists_pr_lp_disjoint {N M : matroid U} :
  N.is_pminor_of M ↔ ∃ C D, C ∩ D = ∅ ∧ N = M ⟋ C ⟍ D :=
begin
  split, swap, rintros ⟨C,D,hCD,h⟩, exact ⟨C, D, h⟩,
  rintros ⟨C,D,h⟩, refine ⟨C,D \ C, ⟨by simp ,_⟩ ⟩, 
  rw [h, ←loopify_rank_zero_eq (_ : (M ⟋ C ⟍ (D \ C)).r (C ∩ D) = 0), loopify_loopify],
  { congr, ext, simp, tauto!, }, 
  refine rank_zero_of_subset_rank_zero _ (rank_zero_of_pr_lp _ _ _), 
  intro x, simp, tauto,
end

end pminor 

end matroid 

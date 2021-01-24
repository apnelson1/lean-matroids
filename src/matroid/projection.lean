
import .constructions

open ftype 
open matroid 

section pseudominor 
namespace matroid 
variables {U : ftype}

/-- contract C and replace it with a set of loops to get a matroid on the same ground set.  
Often more convenient than taking a minor -/
def project (M : matroid U) (C : set U) : matroid U := 
{ 
  r := λ X, M.r (X ∪ C) - M.r C,
  R0 := λ X, by {simp only, linarith [M.rank_mono (subset_union_right X C)]},
  R1 := λ X, by {simp only, linarith [M.R0 (X ∩ C), M.R3 X C, M.R1 X]},
  R2 := λ X Y hXY, by {simp only, linarith [M.rank_mono (subset_union_subset_left _ _ C hXY)]},
  R3 := λ X Y, by {simp_rw [union_comm _ C], linarith [submod_three_sets M C X Y]} 
}
/-- delete D and replace it with loops to get a matroid on the same ground set. Often more 
convenient than taking a minor -/
def loopify (M : matroid U)(D : set U) : matroid U := 
{
  r := λ X, M.r (X \ D), 
  R0 := λ X, M.R0 _, 
  R1 := λ X, by linarith [M.R1 (X \ D), size_diff_le_size X D], 
  R2 := λ X Y hXY, M.rank_mono (diff_subset_diff D hXY), 
  R3 := λ X Y, by {simp only [diff_def], rw [inter_distrib_right, inter_distrib_inter_left], 
                                                            linarith [M.rank_submod (X ∩ Dᶜ) (Y ∩ Dᶜ)],  }
}

lemma loopify_r (M : matroid U)(D X : set U):
  (loopify M D).r X = M.r (X \ D) := 
  rfl 

lemma project_r (M : matroid U)(C X : set U):
  (project M C).r X = M.r (X ∪ C) - M.r C := 
  rfl 

def loopify_project (M : matroid U)(C D : set U) : matroid U := 
  project (loopify M D) C 

lemma project_makes_loops (M : matroid U)(C : set U):
  loops M ∪ C ⊆ loops (project M C)  := 
by rw [←rank_zero_iff_subset_loops, project_r, union_assoc, union_self, 
        union_comm, rank_eq_rank_union_rank_zero C (rank_loops M), sub_self]

lemma projected_set_rank_zero (M : matroid U)(C : set U):
  (project M C).r C = 0 := 
by rw [project_r, union_self, sub_self] 

lemma loopify_makes_loops (M : matroid U)(D : set U):
  loops M ∪ D ⊆ loops (loopify M D) := 
by {rw [←rank_zero_iff_subset_loops, loopify_r, rank_zero_iff_subset_loops], tidy,}

lemma loopified_set_rank_zero (M : matroid U)(D : set U):
  (loopify M D).r D = 0 :=
by rw [loopify_r, set.diff_self, rank_empty] 

lemma indep_of_loopify_indep {M : matroid U}{D X : set U} : 
  is_indep (loopify M D) X → is_indep M X := 
begin
  simp_rw [indep_iff_r, loopify_r], 
  refine λ h, (le_antisymm (M.R1 _) _), 
  rw ←h, 
  from M.rank_mono (diff_subset _ _),  
end

lemma indep_of_project_indep {M : matroid U}{C X : set U}: 
  is_indep (project M C) X → is_indep M C → is_indep M (X ∪ C) :=
begin
  simp_rw [indep_iff_r, project_r], 
  intros hXC hC,
  linarith [M.R1 (X ∪ C), size_modular X C, size_nonneg (X ∩ C)],
end 

/-- loopify all elements of M outside R -/
def loopify_to (M : matroid U)(R : set U) : matroid U := M.loopify (Rᶜ)

/-- project all elements of M outside R -/
def project_to (M : matroid U)(R : set U) : matroid U := M.project (Rᶜ)

lemma rank_loopify_to (M : matroid U)(R X : set U) : 
  (M.loopify_to R).r X = M.r (X ∩ R) := 
by {rw [loopify_to, loopify_r], simp}

lemma rank_project_to (M : matroid U)(R X : set U):
  (M.project_to R).r X = M.r (X ∪ Rᶜ) - M.r Rᶜ := 
by rw [project_to, project_r]




lemma indep_loopify_to_iff {M : matroid U}{R I : set U} : 
  (M.loopify_to R).is_indep I ↔ M.is_indep I ∧ I ⊆ R := 
begin
  rw [indep_iff_r, rank_loopify_to, indep_iff_r, subset_iff_diff_empty, ←size_zero_iff_empty],
  have h₀ := size_induced_partition I R, 
  refine ⟨λ h, _, λ h, _⟩, 
  have h₁ := M.rank_mono_inter_left I R , 
  have h₂ := M.rank_le_size (I ∩ R), 
  rw h at h₁ h₂, 
  split; 
  linarith [M.rank_le_size I, size_monotone (inter_subset_left I R)], 
  rw h.2 at h₀, simp_rw h₀, rw [add_zero], 
  rw ←indep_iff_r at *, 
  from matroid.I2 (inter_subset_left I R) h.1, 
  -- linarith seems to be failing here for reasons I don't quite understand, hence the ugly proof. 
end

lemma indep_loopify_to_is_indep {M : matroid U}{R I : set U}:
  (M.loopify_to R).is_indep I → M.is_indep I := 
by {rw indep_loopify_to_iff, from λ h, h.1}

lemma indep_loopify_to_subset_is_indep {M : matroid U}{S R I : set U}:
  S ⊆ R → (M.loopify_to S).is_indep I → (M.loopify_to R).is_indep I := 
begin
  intro hSR, simp_rw [indep_loopify_to_iff], 
  from λ h, ⟨h.1, subset_trans h.2 hSR⟩, 
end


end matroid 
end pseudominor

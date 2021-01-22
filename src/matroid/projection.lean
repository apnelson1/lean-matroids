
import .constructions

open ftype 
open matroid 

section pseudominor 

variables {U : ftype}

def project (M : matroid U) (C : set U) : matroid U := 
{ 
  r := λ X, M.r (X ∪ C) - M.r C,
  R0 := λ X, by {simp only, linarith [R2 M (subset_union_right X C)]},
  R1 := λ X, by {simp only, linarith [M.R0 (X ∩ C), M.R3 X C, M.R1 X]},
  R2 := λ X Y hXY, by {simp only, linarith [R2 M (subset_union_subset_left _ _ C hXY)]},
  R3 := λ X Y, by {simp_rw [union_comm _ C], linarith [submod_three_sets M C X Y]} 
}

def loopify (M : matroid U)(D : set U) : matroid U := 
{
  r := λ X, M.r (X \ D), 
  R0 := λ X, M.R0 _, 
  R1 := λ X, by linarith [M.R1 (X \ D), size_diff_le_size X D], 
  R2 := λ X Y hXY, R2 M (diff_subset_diff D hXY), 
  R3 := λ X Y, by {simp only [diff_def], rw [inter_distrib_right, inter_distrib_inter_left], linarith [R3 M (X ∩ Dᶜ) (Y ∩ Dᶜ)],  }
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
  from R2 M (diff_subset _ _),  
end

lemma indep_of_project_indep {M : matroid U}{C X : set U}: 
  is_indep (project M C) X → is_indep M C → is_indep M (X ∪ C) :=
begin
  simp_rw [indep_iff_r, project_r], 
  intros hXC hC,
  linarith [M.R1 (X ∪ C), size_modular X C, size_nonneg (X ∩ C)],
end 

end pseudominor

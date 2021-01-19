
import .constructions

namespace ftype 


section pseudominor 

variables {U : ftype}

def project (M : rankfun U) (C : set U) : rankfun U := 
{ 
  r := λ X, M.r (X ∪ C) - M.r C,
  R0 := λ X, by {simp only, linarith [R2 M (subset_union_right X C)]},
  R1 := λ X, by {simp only, linarith [M.R0 (X ∩ C), M.R3 X C, M.R1 X]},
  R2 := λ X Y hXY, by {simp only, linarith [R2 M (subset_union_subset_left _ _ C hXY)]},
  R3 := λ X Y, by {simp_rw [union_comm _ C], linarith [submod_three_sets M C X Y]} 
}

def loopify (M : rankfun U)(D : set U) : rankfun U := 
{
  r := λ X, M.r (X \ D), 
  R0 := λ X, M.R0 _, 
  R1 := λ X, by linarith [M.R1 (X \ D), size_diff_le_size X D], 
  R2 := λ X Y hXY, R2 M (diff_subset_diff D hXY), 
  R3 := λ X Y, by {simp only [diff_def], rw [inter_distrib_right, inter_distrib_inter_left], linarith [R3 M (X ∩ Dᶜ) (Y ∩ Dᶜ)],  }
}

lemma loopify_r (M : rankfun U)(D X : set U):
  (loopify M D).r X = M.r (X \ D) := 
  rfl 

lemma project_r (M : rankfun U)(C X : set U):
  (project M C).r X = M.r (X ∪ C) - M.r C := 
  rfl 

def loopify_project (M : rankfun U)(C D : set U) : rankfun U := 
  project (loopify M D) C 

lemma project_makes_loops (M : rankfun U)(C : set U):
  loops M ∪ C ⊆ loops (project M C)  := 
  sorry 

lemma projected_set_rank_zero (M : rankfun U)(C : set U):
  (project M C).r C = 0 := 
  sorry

lemma loopify_makes_loops (M : rankfun U)(D : set U):
  loops M ∪ D ⊆ loops (loopify M D) := 
  sorry

lemma loopified_set_rank_zero (M : rankfun U)(D : set U):
  (loopify M D).r D = 0 :=
  sorry 


lemma indep_of_loopify_indep {M : rankfun U}{D X : set U} : 
  is_indep (loopify M D) X → is_indep M X := 
  sorry 

lemma indep_of_project_indep {M : rankfun U}{C X : set U}: 
  is_indep (project M C) X → is_indep M C → is_indep M (X ∪ C) :=
  sorry 

end pseudominor

end ftype 
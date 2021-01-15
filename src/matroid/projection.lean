
import .constructions

namespace boolalg 


section pseudominor 

variables {U : boolalg}

def project (M : rankfun U) (C : U) : rankfun U := 
{ 
  r := λ X, M.r (X ∪ C) - M.r C,
  R0 := λ X, by {simp only, linarith [R2 M (subset_union_right X C)]},
  R1 := λ X, by {simp only, linarith [M.R0 (X ∩ C), M.R3 X C, M.R1 X]},
  R2 := λ X Y hXY, by {simp only, linarith [R2 M (subset_union_subset_left _ _ C hXY)]},
  R3 := λ X Y, by {simp_rw [union_comm _ C], linarith [submod_three_sets M C X Y]} 
}

def loopify (M : rankfun U)(D : U) : rankfun U := 
{
  r := λ X, M.r (X \ D), 
  R0 := λ X, M.R0 _, 
  R1 := λ X, by linarith [M.R1 (X \ D), size_diff_le_size X D], 
  R2 := λ X Y hXY, R2 M (diff_subset_diff D hXY), 
  R3 := λ X Y, by {simp only [diff_def], rw [inter_distrib_right, inter_distrib_inter_left], linarith [R3 M (X ∩ Dᶜ) (Y ∩ Dᶜ)],  }
}

def loopify_project (M : rankfun U)(C D : U) : rankfun U := 
  project (loopify M D) C 

def is_pseudominor (N M : rankfun U) := 
  ∃ C D, N = loopify_project M C D 

def is_proper_pseudominor (N M : rankfun U) := 
  is_pseudominor N M ∧ ∃ e, is_loop N e ∧ ¬is_loop M e 

lemma project_nonloop_is_proper_pseudominor (M : rankfun U)(e : nonloop M) :
  is_proper_pseudominor (project M e) M :=
  sorry  

lemma loopify_nonloop_is_proper_pseudominor (M : rankfun U)(e : nonloop M) :
  is_proper_pseudominor (loopify M e) M := 
  sorry 


end pseudominor

section induction 

variables {U : boolalg}

def lp_induction (P : rankfun U → Prop)(M₀ : rankfun U):
  P (loopy_matroid_on U) → (∀ M, (∀ N, is_proper_pseudominor N M → P N) → P M) → P M₀ :=
begin
  intros hloopy hind, 
  set Q : U → Prop := λ X, (∀ (M : rankfun U), M.r Xᶜ = 0 → P M) with hQ, 
  have hQbot : Q ⊥ := λ M hM, by 
    {rw [compl_bot, ←loopy_iff_top_rank_zero] at hM, rw hM, assumption},
  rcases maximal_example_from_bot Q hQbot with ⟨W, ⟨hQW, hWmax⟩⟩, 
  rw hQ at hQW, 
  by_cases hW : W = ⊤, 
  rw [hW, compl_top] at hQW, 
  refine hQW M₀ (rank_bot _), 
  sorry -- took a wrong turn - induction is annoying. 
end

def lp_induction_single (P : rankfun U → Prop)(M₀ : rankfun U): 
  P (loopy_matroid_on U) → (∀ M, (∀ e: nonloop M, P (project M e) ∧ P (loopify M e)) → P M) → P M₀ :=
begin
  intros h hind, apply lp_induction _ _ h, 
  intros M hind', refine hind _ (λ e, ⟨_,_⟩), 
  apply hind', apply project_nonloop_is_proper_pseudominor, 
  apply hind', apply loopify_nonloop_is_proper_pseudominor, 
end

end induction 
end boolalg 
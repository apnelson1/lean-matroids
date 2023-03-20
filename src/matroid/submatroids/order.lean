
import ..loop

open_locale classical 
noncomputable theory

universes u v w 

open set list 

namespace matroid 

variables {E : Type*} [finite E] {X Y I C B : set E} {N M : matroid E} {e f : E}

section weak_image 
/- `M` is a weak image of `N` if independence in `N` implies independence in `M` -/
def is_weak_image (N M : matroid E) := 
  ∀ I, N.indep I → M.indep I 

instance weak_image_le : has_le (matroid E) := 
⟨λ N M, is_weak_image N M⟩

lemma weak_image_def :
  N ≤ M ↔ ∀ I, N.indep I → M.indep I :=
iff.rfl 

lemma indep.weak_image (hI : N.indep I) (h : N ≤ M)  :
  M.indep I := 
h _ hI

lemma weak_image_iff_r:
  N ≤ M ↔ ∀ X, N.r X ≤ M.r X := 
begin
  simp_rw [r_le_iff, le_r_iff], 
  refine ⟨λ h X I hIN hIX, ⟨I,h _ hIN, hIX, rfl⟩, λ h I hI, _⟩, 
  obtain ⟨J,hJ,hJI,hJ'⟩ := h I I hI subset.rfl, 
  rwa [←eq_of_subset_of_ncard_le hJI hJ'.symm.le], 
end

lemma weak_image.r_le (h : N ≤ M) (X : set E) : 
  N.r X ≤ M.r X :=
weak_image_iff_r.mp h X  

lemma weak_image_iff_dep:
  N ≤ M ↔ ∀ X, ¬M.indep X → ¬N.indep X := 
by simp_rw [weak_image_def, not_imp_not]

lemma weak_image.dep (h : N ≤ M) (hX : ¬M.indep X) : 
  ¬ N.indep X := 
weak_image_iff_dep.mp h _ hX 

lemma weak_image_iff_circuit:
  N ≤ M ↔ ∀ C, M.circuit C → ∃ C' ⊆ C, N.circuit C' := 
begin
  simp_rw [weak_image_iff_dep, dep_iff_supset_circuit],  
  refine ⟨λ h, λ C hC, _, λ h, λ X hX, _⟩, 
  {  apply h, exact ⟨C,subset_refl _, hC⟩,},
  rcases hX with ⟨C, ⟨h', h''⟩⟩, 
  rcases h C h'' with ⟨C',h1,h2⟩, 
  refine ⟨C', h1.trans h', h2⟩,  
end 

lemma circuit.supset_circuit_of_weak_image (hC : M.circuit C) (h : N ≤ M) :
  ∃ C' ⊆ C, N.circuit C' :=
weak_image_iff_circuit.mp h _ hC   

lemma weak_image_tfae: 
  tfae
[ N ≤ M, 
  ∀ X, N.r X ≤ M.r X, 
  ∀ X, N.indep X → M.indep X, 
  ∀ X, ¬M.indep X → ¬N.indep X,
  ∀ C, M.circuit C → ∃ C' ⊆ C, N.circuit C'] :=
begin
  tfae_have : 1 ↔ 2, apply weak_image_iff_r, 
  tfae_have : 1 ↔ 3, apply weak_image_def, 
  tfae_have : 1 ↔ 4, apply weak_image_iff_dep,  
  tfae_have : 1 ↔ 5, apply weak_image_iff_circuit, 
  tfae_finish, 
end

lemma weak_image.rank_zero_of_rank_zero (h : N ≤ M) (hX : M.r X = 0) :
  N.r X = 0 :=
nat.eq_zero_of_le_zero ((weak_image.r_le h X).trans_eq hX)

lemma loop.loop_of_weak_image (he : M.loop e) (h : N ≤ M) :
  N.loop e :=
begin
  obtain ⟨C,hCe,hC⟩ :=  he.circuit.supset_circuit_of_weak_image h, 
  rw [loop_def], 
  convert hC,  
  by_contra h', 
  rw ssubset_singleton_iff.mp (hCe.ssubset_of_ne (ne.symm h')) at hC, 
  simpa using hC.nonempty, 
end

lemma nonloop_of_weak_image_nonloop (h : N ≤ M) {e : E} (he : ¬ N.loop e) :
  ¬ M.loop e :=
λ he', he (he'.loop_of_weak_image h) 

end weak_image

section quotient 
/-- a quotient of M is a matroid N for which rank differences of nested pairs in N are at most
the corresponding rank differences in M. This is equivalent to the existence of a matroid P for 
which M is a deletion of P and N is a contraction of P, but we do not show this equivalence here.

/- TODO : define this in terms of something other than `r` -/
-/
def is_quotient (N M : matroid E) := 
  ∀ X, M.cl X ⊆ N.cl X
  --∀ X Y, X ⊆ Y → N.r Y - N.r X ≤ M.r Y - M.r X

reserve infixl ` ≼ `:75
infix ` ≼ ` :=  is_quotient 

lemma is_quotient.cl_subset (h : N ≼ M) (X : set E) : 
  M.cl X ⊆ N.cl X := 
h X  

lemma is_quotient.r_le_r_of_subset (h : N ≼ M) (hXY : X ⊆ Y) :
  (N.r Y : ℤ)  - N.r X ≤ M.r Y - M.r X :=
begin
  by_contra' hlt, 
  set P : set E → Prop := λ Z, X ⊆ Z ∧ Z ⊆ Y ∧ (M.r Y : ℤ) - M.r Z < N.r Y - N.r Z,
  obtain ⟨Z,⟨hXZ,hZY,hlt'⟩,hmax⟩ := finite.exists_maximal P ⟨X, subset.rfl, hXY, hlt⟩,  
  have hss := hZY.ssubset_of_ne (by {rintro rfl, simpa using hlt'}),
  rw [int.lt_iff_add_one_le, ←le_sub_iff_add_le] at hlt', 
  obtain ⟨e,heY,heZ⟩ := exists_of_ssubset hss, 

  refine (insert_ne_self.mpr (heZ)).symm
      (hmax (insert e Z) ⟨hXZ.trans (set.subset_insert _ _),
      insert_subset.mpr ⟨heY,hZY⟩, lt_of_not_le (λ hle, _)⟩ (subset_insert _ _)), 
  
  by_cases h₁ : e ∈ M.cl Z, 
  { rw [mem_cl.mp h₁, mem_cl.mp (h Z h₁)] at hle,  linarith},
  
  rw [not_mem_cl.mp h₁, nat.cast_add, nat.cast_one] at hle, 
  linarith [N.r_insert_le_add_one Z e],
end 

lemma is_quotient_iff_r : 
  N ≼ M ↔ ∀ X Y, X ⊆ Y → (N.r Y : ℤ)  - N.r X ≤ M.r Y - M.r X := 
begin
  refine ⟨λ h X Y hXY, h.r_le_r_of_subset hXY, λ h Z e he, _⟩,  
  have hle := h _ _ (subset_insert e Z), 
  rw [mem_cl.mp he, sub_self, sub_le_iff_le_add, zero_add, nat.cast_le] at hle, 
  apply mem_cl_of_r_insert_le hle, 
end 

lemma is_quotient.weak_image (h : N ≼ M) :
   N ≤ M :=
begin
  refine λ X hX, by_contra (λ h', _),
  obtain ⟨C,hCX,hC⟩ := dep_iff_supset_circuit.mp h', 
  obtain ⟨e,heC⟩ := hC.nonempty,  
  
  have he := (hC.subset_cl_diff_singleton e).trans (h (C \ {e})), 
  rw indep_iff_cl_diff_ne_forall at hX, 
  -- rw hC.cl_diff_singleton at hss, 

  
end 

-- lemma quotient_of_cl (h : ∀ X, M.cl X ⊆ N.cl X) : 
--    N ≼ M := 
-- begin
--   set P : set E × set E → Prop :=  
--   (λ p, p.1 ⊆ p.2 → N.r p.2 - N.r p.1 ≤ M.r p.2 - M.r p.1 ) with hP, 
--   suffices : ∀ p, P p, exact λ X Y, this ⟨X,Y⟩, 
--   apply nonneg_int_strong_induction_param P (λ p, size (p.2 \ p.1)), 
--   { rintros ⟨X,Y⟩, apply size_nonneg}, 
--   { rintros ⟨X,Y⟩ hs hXY, dsimp only at *, 
--     rw [size_zero_iff_empty, diff_empty_iff_subset] at hs, 
--     rw [subset.antisymm hXY hs, sub_self, sub_self],  }, 
--   rintros ⟨X,Y⟩ h_size h' hXY, dsimp only at *,   
--   cases exists_mem_of_size_pos h_size with e he,
--   specialize h' ⟨X, Y \ {e}⟩ _ _, 
--   { dsimp only, rw [diff_right_comm, size_remove_mem he], linarith}, 
--   { dsimp only, apply subset_of_remove_mem_diff; assumption,},
--   dsimp only at h', 
--   suffices : N.r Y - N.r (Y \ {e}) ≤ M.r Y - M.r (Y \ {e}), by linarith, 
--   by_cases hY : M.r Y = M.r (Y \ {e}), swap, 
--   { rw [rank_eq_sub_one_of_ne_remove _ _ _ hY], linarith [rank_remove_single_lb N Y e]  },
--   rw [hY, sub_self], 
--   rw [eq_comm, rank_removal_iff_closure _ _ he.1]  at hY, 
--   have hN := mem_of_subset (h _) hY, rw [←rank_removal_iff_closure _ _ he.1] at hN, 
--   linarith, 
-- end

lemma quotient_iff_dual_quotient : 
  N ≼ M ↔ M.dual ≼ N.dual :=
begin
  suffices h' : ∀ (N M : matroid E), N ≼ M → M.dual ≼ N.dual, 
  exact ⟨λ h, h' _ _ h, λ h, by {convert h' _ _ h; rw dual_dual, }⟩, 
  intros N M h X Y hXY, 
  simp_rw [dual_r], 
  rw compl_subset_compl.symm at hXY, 
  linarith [h _ _ hXY],
end

lemma quotient_tfae : 
  tfae 
[N ≼ M,
 ∀ F, N.is_flat F → M.is_flat F, 
 ∀ X Y, X ⊆ Y → N.r Y - N.r X ≤ M.r Y - M.r X,
 ∀ X, M.cl X ⊆ N.cl X,
 M.dual ≼ N.dual] :=
begin
  tfae_have : 1 ↔ 3, unfold is_quotient,
  tfae_have : 3 → 2, 
  {exact λ h, λ F hF Y hFY, by linarith [hF _ hFY, h _ _ hFY.1],}, 
  tfae_have : 2 → 4, 
  {exact λ h X, subset_flat X _ (subset_cl N X) (h _ (N.cl_is_flat X))}, 
  tfae_have: 4 → 1, apply quotient_of_cl, 
  tfae_have : 1 ↔ 5, apply quotient_iff_dual_quotient, 
  tfae_finish, 
end

lemma quotient_iff_flat :
  N ≼ M ↔ ∀ F, N.is_flat F → M.is_flat F :=
by apply @tfae.out _ quotient_tfae 0 1 

lemma flat_of_quotient_flat (h : N ≼ M){F : set E} (hF : N.is_flat F) :
  M.is_flat F :=
(quotient_iff_flat.mp h) F hF 

lemma indep_of_quotient_indep (h : N ≼ M){I : set E} (hI : N.indep I) :
  M.indep I := 
indep_of_weak_image_indep (weak_image_of_quotient h) hI 

lemma quotient_iff_cl :
  N ≼ M ↔ ∀ X, M.cl X ⊆ N.cl X :=
by apply @tfae.out _ quotient_tfae 0 3 

lemma quotient_rank_zero_of_rank_zero (h : N ≼ M){X : set E} (hX : M.r X = 0) :
  N.r X = 0 :=
weak_image_rank_zero_of_rank_zero (weak_image_of_quotient h) hX 

lemma quotient_loop_of_loop (h : N ≼ M){e : E} (he : M.is_loop e) :
  N.is_loop e :=
weak_image_loop_of_loop (weak_image_of_quotient h) he

lemma nonloop_of_quotient_nonloop (h : N ≼ M){e : E} (he : N.is_nonloop e) :
  M.is_nonloop e :=
nonloop_of_weak_image_nonloop (weak_image_of_quotient h) he

lemma loops_quotient (h : N ≼ M) : 
  loops M ⊆ loops N := 
loops_weak_image (weak_image_of_quotient h)

lemma eq_of_eq_rank_quotient (h : N ≼ M) (hr : N.r univ = M.r univ) :
  N = M :=
begin
  ext X, by_contra hn,
  /- take a maximal set on which the ranks of N and M differ. -/
  rcases maximal_example_aug (λ X, ¬N.r X = M.r X) hn with ⟨Y, hXY, h',h''⟩, 
  dsimp only at h'', simp_rw [not_not] at h'', clear hXY hn X, 
  have hY : Y ≠ univ := λ hY, by {rw ←hY at hr, exact h' hr },
  cases ne_univ_iff_has_nonmem.mp hY with e heY,  
  specialize h'' e heY, 
  have hle := weak_image_of_quotient h, 
  rw quotient_iff_cl at h, 
  by_cases hM : e ∈ M.cl Y, 
  { rw [(mem_cl_iff_r.mp hM)] at h'',
    rw [←h'', eq_comm, ←mem_cl_iff_r] at h', 
    exact h' (mem_of_mem_of_subset hM (h _))}, 
  rw nonmem_cl_iff_r at hM,  
  linarith [int.le_sub_one_of_le_of_ne (hle _) h', rank_augment_single_ub N Y e], 
end

end quotient 

end matroid 
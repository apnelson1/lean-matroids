import ..dual

open_locale classical

open set list

namespace matroid

variables {E : Type*} [finite E] {X Y I C B F : set E} {N M : matroid E} {e f : E}

section weak_image
/- `M` is a weak image of `N` if independence in `N` implies independence in `M` -/
def weak_image (N M : matroid E) :=
  ∀ I, N.indep I → M.indep I

-- instance weak_image_le : has_le (matroid E) :=
-- ⟨λ N M, is_weak_image N M⟩

reserve infixl ` ≤w `:75
infix ` ≤w ` := weak_image

lemma weak_image_def :
  N ≤w M ↔ ∀ I, N.indep I → M.indep I :=
iff.rfl

lemma indep.weak_image (hI : N.indep I) (h : N ≤w M)  :
  M.indep I :=
h _ hI

lemma weak_image_iff_r:
  N ≤w M ↔ ∀ X, N.r X ≤ M.r X :=
begin
  simp_rw [r_le_iff, le_r_iff],
  refine ⟨λ h X I hIN hIX, ⟨I,h _ hIN, hIX, rfl⟩, λ h I hI, _⟩,
  obtain ⟨J,hJ,hJI,hJ'⟩ := h I I hI subset.rfl,
  rwa [←eq_of_subset_of_ncard_le hJI hJ'.symm.le],
end

lemma weak_image.r_le (h : N ≤w M) (X : set E) :
  N.r X ≤ M.r X :=
weak_image_iff_r.mp h X

lemma weak_image_iff_dep:
  N ≤w M ↔ ∀ X, ¬M.indep X → ¬N.indep X :=
by simp_rw [weak_image_def, not_imp_not]

lemma weak_image.dep (h : N ≤w M) (hX : ¬M.indep X) :
  ¬ N.indep X :=
weak_image_iff_dep.mp h _ hX

lemma weak_image_iff_circuit:
  N ≤w M ↔ ∀ C, M.circuit C → ∃ C' ⊆ C, N.circuit C' :=
begin
  simp_rw [weak_image_iff_dep, dep_iff_supset_circuit],
  refine ⟨λ h, λ C hC, _, λ h, λ X hX, _⟩,
  {  apply h, exact ⟨C,subset_refl _, hC⟩,},
  rcases hX with ⟨C, ⟨h', h''⟩⟩,
  rcases h C h'' with ⟨C',h1,h2⟩,
  refine ⟨C', h1.trans h', h2⟩,
end

lemma circuit.supset_circuit_of_weak_image (hC : M.circuit C) (h : N ≤w M) :
  ∃ C' ⊆ C, N.circuit C' :=
weak_image_iff_circuit.mp h _ hC

lemma weak_image_tfae:
  tfae
[ N ≤w M,
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

lemma weak_image.rank_zero_of_rank_zero (h : N ≤w M) (hX : M.r X = 0) :
  N.r X = 0 :=
nat.eq_zero_of_le_zero ((weak_image.r_le h X).trans_eq hX)

lemma loop.weak_image (he : M.loop e) (h : N ≤w M) :
  N.loop e :=
begin
  obtain ⟨C,hCe,hC⟩ :=  he.circuit.supset_circuit_of_weak_image h,
  rw [loop_def],
  convert hC,
  by_contra h',
  rw ssubset_singleton_iff.mp (hCe.ssubset_of_ne (ne.symm h')) at hC,
  simpa using hC.nonempty,
end

lemma nonloop_of_weak_image_nonloop (h : N ≤w M) {e : E} (he : ¬ N.loop e) :
  ¬ M.loop e :=
λ he', he (he'.weak_image h)

lemma weak_image.trans {M₀ M₁ M₂ : matroid E} (h₀₁ : M₀ ≤w M₁) (h₁₂ : M₁ ≤w M₂) :
  M₀ ≤w M₂ :=
λ I hI, h₁₂ I (h₀₁ I hI)

lemma weak_image.antisymm (h : M ≤w N) (h' : N ≤w M) :
  M = N :=
eq_of_indep_iff_indep_forall (λ I, ⟨λ hI, h I hI, λ hI, h' I hI⟩)

end weak_image

section quotient
/-- a quotient of M is a matroid N for which rank differences of nested pairs in N are at most
the corresponding rank differences in M. This is equivalent to the existence of a matroid P for
which M is a deletion of P and N is a contraction of P, but we do not show this equivalence here.
-/
def is_quotient (N M : matroid E) :=
  ∀ X, M.cl X ⊆ N.cl X

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
   N ≤w M :=
begin
  refine λ X hX, by_contra (λ h', _),
  obtain ⟨C,hCX,hC⟩ := dep_iff_supset_circuit.mp h',
  obtain ⟨e,heC⟩ := hC.nonempty,
  have he := (hC.subset_cl_diff_singleton e).trans (h (C \ {e})),
  exact ((cl_subset_cl_of_subset_cl he).trans_ssubset
    ((hX.subset hCX).cl_diff_singleton_ssubset heC)).ne rfl,
end

lemma indep.quotient (hI : N.indep I) (h : N ≼ M) :
  M.indep I :=
hI.weak_image h.weak_image

/- TODO : prove without rank (or with relative rank)-/
lemma quotient_iff_dual_quotient :
  N ≼ M ↔ M.dual ≼ N.dual :=
begin
  suffices h' : ∀ (N M : matroid E), N ≼ M → M.dual ≼ N.dual,
  exact ⟨λ h, h' _ _ h, λ h, by {convert h' _ _ h; rw dual_dual, }⟩,
  simp_rw [is_quotient_iff_r, dual_rank_cast_eq],
  intros N M h X Y hXY,
  have := h _ _ (compl_subset_compl.mpr hXY),
  linarith,
end

lemma is_quotient_iff_flat :
  N ≼ M ↔ ∀ F, N.flat F → M.flat F :=
begin
  rw [is_quotient],
  refine ⟨λ h F hNF, _, λ h, _⟩,
  { refine flat_iff_cl_self.mpr ((M.subset_cl _).antisymm' _),
    have hcl := h F, rwa hNF.cl at hcl},
  simp_rw [N.cl_def, subset_sInter_iff, mem_set_of_eq, and_imp],
  exact λ X F hF hXF, (h _ hF).cl_subset_of_subset hXF,
end

lemma flat.quotient (hF : N.flat F) (h : N ≼ M) :
  M.flat F :=
(is_quotient_iff_flat.mp h) F hF

lemma quotient_tfae :
  tfae
[N ≼ M,
 ∀ F, N.flat F → M.flat F,
 ∀ X Y, X ⊆ Y → (N.r Y : ℤ)  - N.r X ≤ M.r Y - M.r X,
 ∀ X, M.cl X ⊆ N.cl X,
 M.dual ≼ N.dual] :=
begin
  tfae_have : 1 ↔ 3, exact is_quotient_iff_r,
  tfae_have : 1 ↔ 2, exact is_quotient_iff_flat,
  tfae_have : 1 ↔ 4, refl,
  tfae_have : 1 ↔ 5, exact quotient_iff_dual_quotient,
  tfae_finish,
end

lemma quotient_iff_cl :
  N ≼ M ↔ ∀ X, M.cl X ⊆ N.cl X :=
by apply @tfae.out _ quotient_tfae 0 3

lemma eq_of_quotient_of_rk_eq_rk (h : N ≼ M) (hr : N.rk = M.rk) :
  N = M :=
begin
  refine eq_of_r_eq_r_forall _,
  by_contra' h',
  obtain ⟨S, hS, hmax⟩ := finite.exists_maximal _ h',
  apply hS,
  obtain ⟨e,heS⟩ := (ne_univ_iff_exists_not_mem S).mp (by {rintro rfl, exact hS hr}),
  have hi : M.r (insert e S) = N.r (insert e S),
  { by_contra hi,
    exact (ssubset_insert heS).ne (hmax _ (ne.symm hi) (subset_insert _ _)), },
  rw is_quotient_iff_r at h,
  have h1 := h _ _ (subset_insert e S),
  have h2 := h _ _ (empty_subset S),
  rw [hi] at h1,
  simp_rw [r_empty, nat.cast_zero] at h2,
  zify,
  linarith,
end

end quotient

end matroid 
import linear_algebra.linear_independent
import data.zmod.basic
import ..constructions.basic
import ..dual 
--import .field_stuff

noncomputable theory 
open_locale classical

variables {E 𝔽 ι : Type*} [field 𝔽] [finite E] {M : matroid E}

namespace matroid 

structure rep (𝔽 : Type*) [field 𝔽] (M : matroid E) (ι : Type*):= 
(to_fun : E → (ι → 𝔽))
(valid : ∀ (I : set E), linear_independent 𝔽 (λ (e : I), to_fun (e : E)) ↔ M.indep I)
-- (valid' : ∀ (I : set E), linear_independent 𝔽 (to_fun ∘ (coe : I → E)) ↔ M.indep I)

def is_representable (M : matroid E) (𝔽 : Type*) [field 𝔽] : Prop := 
  ∃ ι, nonempty (rep 𝔽 M ι) 

/- A matroid is binary if it has a `GF(2)`-representation -/
def is_binary (M : matroid E) := is_representable M (zmod 2)

lemma of_base (φ : rep 𝔽 M ι) {B : set E} (hB : M.base B) (e : E) : 
  φ.to_fun e ∈ submodule.span 𝔽 (φ.to_fun '' B) := 
begin
  by_cases e ∈ B,
  { have h2 := @submodule.subset_span 𝔽 _ _ _ _ (φ.to_fun '' B),
    have h3 : φ.to_fun e ∈ (φ.to_fun '' B),
    apply (set.mem_image φ.to_fun B (φ.to_fun e)).2,
    use e,
    use h,
    have h4 := set.mem_of_subset_of_mem h2 h3,
    simp at h4,
    exact h4 },
  have h2 : ¬ linear_independent 𝔽 (λ f : insert e B, φ.to_fun (f : E)),
  { rw rep.valid,
    apply base.dep_of_insert hB h },
  by_contra h3,
  apply h2,
  rw linear_independent_insert' h,
  refine ⟨(φ.valid B).2 (base.indep hB), h3⟩,
end 

--noncomputable?
lemma foo (h : M.is_representable 𝔽) : 
  nonempty (rep 𝔽 M (fin M.rk))  := 
begin
  
  sorry,
end

/-lemma U24_nonbinary : ¬ (canonical_unif 2 4).is_binary :=
begin
  by_contra h2,
  rw is_binary at h2,
  have h3 := foo h2,
  /-have h1 := @num_subspaces_dim_one (zmod 2) V _ _ _ _ _ sorry _ sorry,
  simp at h1,
  have h3 := hV univ,
  rw canonical_unif_r at h3,
  rw ncard_univ at h3,
  simp at h3,
  have h4 : finrank (zmod 2) ↥V = 2,
  sorry,
  rw h4 at h1,
  have h5 := ncard_univ (fin 4),
  have h6 : univ.ncard ≤ fintype.card ↥{S : subspace (zmod 2) ↥V | finrank (zmod 2) ↥S = 1},-/
  
  sorry,
end-/


-- lemma foo (e f : E) (hne : e ≠ f) (h : M.r {e,f} = 1) : 


end matroid 



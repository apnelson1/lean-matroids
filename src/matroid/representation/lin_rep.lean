import linear_algebra.linear_independent
import ..dual 

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
  refine ⟨_, h3⟩,
  rw rep.valid,
  apply base.indep hB,
end 


lemma foo (h : M.is_representable 𝔽) : 
  nonempty (rep 𝔽 M (fin M.rk))  := 
sorry 




-- lemma foo (e f : E) (hne : e ≠ f) (h : M.r {e,f} = 1) : 


end matroid 



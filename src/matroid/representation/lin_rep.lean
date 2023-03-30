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
  
end 


lemma foo (h : M.is_representable 𝔽) : 
  nonempty (rep 𝔽 M (fin M.rk))  := 
sorry 




-- lemma foo (e f : E) (hne : e ≠ f) (h : M.r {e,f} = 1) : 


end matroid 



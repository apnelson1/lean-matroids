
import prelim.induction prelim.collections prelim.embed
import matroid.rankfun matroid.indep 

open matroid set 
open_locale classical big_operators 

noncomputable theory 

namespace idsum 

variables {U ι : Type}[fintype U](f : U → ι)
(Rs : ∀ (i : ι), matroid {x // f x = i})

/-- the rank of a set is the sum of the direct-summand ranks of its intersection with the cells of the partition -/
def r (X : set U) := 
∑ᶠ (i : ι), (Rs i).r (coe ⁻¹' X)

lemma size_coe_eq (i : ι)(X : set U): 
  size (coe ⁻¹' X : set {x // f x = i}) = size ({ x ∈ X | f x = i}) := 
by {rw size_preimage_coe, congr'}  

lemma size_finite_supp (X : set U):
  (function.support (λ (i : ι), size ({ x ∈ X | f x = i}))).finite := 
begin
  by_cases he : size X = 0,
  { rw size_zero_iff_empty at he, convert set.finite_empty, simp [ext_iff, he],   },
  apply finsupp_of_finsum_nonzero, convert he, apply sum_size_fiber_eq_size, 
end 

lemma rank_finite_supp (X : set U):
  (function.support (λ (i : ι), (Rs i).r (coe ⁻¹' X))).finite :=
begin
  by_cases he : size X = 0, 
  { rw size_zero_iff_empty at he, simp [r, he]},
  apply set.finite.subset (size_finite_supp f X), 
  intros x hx hn,
  simp_rw [← size_coe_eq, size_zero_iff_empty] at hn,  
  rw [function.mem_support, hn] at hx, 
  simpa using hx, 
end

lemma sum_finite_supp {α : Type}{f g : α → ℤ}
  (hf : (function.support f).finite) (hg : (function.support g).finite):
(function.support (f + g)).finite :=
begin
  apply @set.finite.subset _ ((function.support f) ∪ (function.support g)), 
    apply set.finite.union hf hg, 
  apply function.support_add, 
end


lemma R0: 
  satisfies_R0 (r f Rs) := 
λ X, nonneg_of_finsum_nonneg (λ i, (Rs i).rank_nonneg _)

lemma R1: 
  satisfies_R1 (r f Rs) := 
λ X, begin
  rw [r, ← sum_size_fiber_eq_size _ f], 
  refine finsum_le_finsum (λ i, has_le.le.trans_eq (rank_le_size _ _) _) _ _, 
    rw size_coe_eq, 
  apply rank_finite_supp, 
  apply size_finite_supp,
end 

lemma R2:
  satisfies_R2 (r f Rs) := 
λ X Y hXY, by 
{ refine finsum_le_finsum (λ i, (rank_mono _ (λ x, _))) _ _, 
  {rw [mem_preimage, mem_preimage],  apply hXY},
  all_goals {apply rank_finite_supp}, }

lemma R3:
  satisfies_R3 (r f Rs) :=
begin
  intros X Y, 
  simp_rw [r], 
  rw [← finsum_add_distrib, ← finsum_add_distrib], rotate,
  repeat {apply rank_finite_supp, },
  simp only [pi.add_apply], 
  refine finsum_le_finsum (λ i, rank_submod _ _ _) _ _;
  {apply sum_finite_supp; apply rank_finite_supp,  }, 
end

/-- the 'internal direct sum' of matroids whose ground sets partition U, indexed by f : U → ι -/
def M : matroid U := 
⟨idsum.r f Rs, idsum.R0 f Rs, idsum.R1 f Rs, idsum.R2 f Rs, idsum.R3 f Rs⟩ 

lemma r_eq (X : set U) : 
  (M f Rs).r X = ∑ᶠ (i : ι), (Rs i).r (coe ⁻¹' X) :=
rfl 


lemma indep_iff (X : set U): 
  (M f Rs).is_indep X ↔ ∀ i, (Rs i).is_indep (coe ⁻¹' X) :=
begin
  simp_rw [indep_iff_r, ← sum_size_fiber_eq_size X f, size_coe_eq, r_eq],
  rw [finsum_eq_finsum_iff_of_le (rank_finite_supp _ _ X) (size_finite_supp _ X)],  
  simp_rw [← size_coe_eq], 
  exact λ x, rank_le_size _ _, 
end

end idsum 
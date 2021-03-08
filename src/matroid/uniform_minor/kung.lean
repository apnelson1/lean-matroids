import prelim.collections prelim.embed prelim.size prelim.induction prelim.minmax finsum.fin_api
import .submatroid.projection .pointcount .submatroid.minor_iso 

noncomputable theory 
open_locale classical big_operators 

open set matroid 

def pg_size : ℤ → ℕ → ℤ 
| q 0     := 0
| q (n+1) := 1 + q * (pg_size q n)

@[simp] lemma pg_size_zero (q : ℤ) :
  pg_size q 0 = 0 := 
rfl 

@[simp] lemma pg_size_order_one (n : ℕ) : 
  pg_size 1 n = n := 
by {induction n with n ih, simp, simp [pg_size, ih, add_comm]  }


--theorem kung {q : ℤ}(hq : 1 ≤ q)
/-
figure this out later. annoying reindexing

lemma pg_size_eq_powsum (q : ℤ)(n : ℕ) : 
  pg_size q n = ∑ᶠ i in {i | i < n}, q^i  := 
begin
  induction n with n ih, simp, 
  rw [pg_size, ih, mul_distrib_finsum_in], 
  have := @finsum_in_image ℕ ℤ _ ℕ (λ x, q^x) {i | i < n} (λ n, n+1) sorry, 
  convert (congr_arg (λ x: ℤ, 1+x) this).symm, 
  
  
  /-have hni : {i | i < n.succ} = insert n {i | i < n}, 
  { ext, 
    simp only [mem_set_of_eq, mem_insert_iff], 
    refine ⟨λ h, _, _⟩, 
      exact eq_or_lt_of_le (nat.le_of_lt_succ h),
    rintros (rfl | hn), 
      exact lt_add_one _, 
    exact nat.lt_succ_of_lt hn},
  conv_rhs {congr, rw hni, },
  rw finsum_in_insert, -/
  --simp_rw [hni, fin.finsum_in_insert],  
  --simp_rw [pg_size, ih], 
  --have := @finsum_in_image ℕ ℤ _ ℕ 
  
  
end
-/ 



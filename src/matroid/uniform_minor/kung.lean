
import .basic 
import prelim.intervals 
import prelim.collections prelim.embed prelim.size prelim.induction prelim.minmax finsum.fin_api
import matroid.submatroid.projection matroid.pointcount matroid.submatroid.minor_iso 

noncomputable theory 
open_locale classical big_operators 

open set matroid 

def pg_size_nat : ℤ → ℕ → ℤ 
| q 0     := 0
| q (n+1) := 1 + q * (pg_size_nat q n)

@[simp] lemma pg_size_nat_zero (q : ℤ) :
  pg_size_nat q 0 = 0 := 
rfl 

@[simp] lemma pg_size_nat_order_one (n : ℕ) : 
  pg_size_nat 1 n = n := 
by {induction n with n ih, simp, simp [pg_size_nat, ih, add_comm]  }

lemma pg_size_nat_eq_powsum (q : ℤ)(n : ℕ) : 
  pg_size_nat q n = ∑ᶠ i in Ico 0 n , q^i  := 
begin
  induction n with n ih, 
    simp, 
  rw [pg_size_nat, ih, mul_distrib_finsum_in], 
  conv in (_ * _) {rw ← pow_succ}, 
  rw [← pow_zero q, finsum_Ico_shift, Ico_ℕ_eq_Ioo, nat.zero_add, nat.sub_self,
   ← finsum_in_insert, Ioo_insert_left_eq_Ico];
  simp [set.Ioo_ℕ_finite],  
end


lemma pg_size_rat (q : ℤ)(n : ℕ): 
  pg_size_nat 

def pg_size (q n : ℤ) : ℤ := pg_size_nat q n.to_nat 



-- pg_size_nat n q = 1 + q + q^2 + ... + q^{n-1}


theorem point_count (q : ℤ){α : Type*}[fintype α](M : matroid α):
  ¬ (canonical_unif 2 (q+2)).is_iminor_of M → ε M ≤ pg_size_nat q (M.r univ).to_nat := 
sorry 
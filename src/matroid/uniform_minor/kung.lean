
import .basic 
import prelim.intervals 
import prelim.collections prelim.embed prelim.size prelim.induction prelim.minmax finsum.fin_api
import matroid.submatroid.projection matroid.pointcount matroid.submatroid.minor_iso 

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

lemma pg_size_eq_powsum (q : ℤ) (n : ℕ) : 
  pg_size q n = ∑ᶠ i in Ico 0 n ,q^i  := 
begin
  induction n with n ih, 
    simp, 
  rw [pg_size, ih, mul_distrib_finsum_in], 
  conv in (_ * _) {rw ← pow_succ}, 
  rw [← pow_zero q, finsum_Ico_shift, Ico_ℕ_eq_Ioo, nat.zero_add, nat.sub_self,
   ← finsum_in_insert, Ioo_insert_left_eq_Ico];
  simp [set.Ioo_ℕ_finite],  
end

lemma pg_size_rat (q : ℤ) (n : ℕ) (hq : 2 ≤ q) : 
  (pg_size q n : ℚ) = (q^n - 1)/(q - 1) := 
begin
  induction n with n ih, 
    simp, 
  have hq : (q : ℚ) -1 ≠ 0 := by {norm_cast, linarith}, 
  rw [pg_size, int.cast_add, int.cast_mul, int.cast_one, ih, pow_succ, ← mul_div_assoc, 
  one_add_div hq, div_left_inj' hq],
  ring,
end

theorem point_count (q : ℤ){α : Type*} [fintype α] (M : matroid α) :
  ¬ (canonical_unif 2 (q+2)).is_iminor_of M → ε M ≤ pg_size q (M.rank_nat) := 
sorry 
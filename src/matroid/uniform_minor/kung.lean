
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


--theorem kung {q : ℤ}(hq : 1 ≤ q)

--figure this out later. annoying reindexing


lemma pg_size_eq_powsum (q : ℤ)(n : ℕ) : 
  pg_size q n = ∑ᶠ i in Ico 0 n , q^i  := 
begin
  induction n with n ih, simp, 
  rw [pg_size, ih, mul_distrib_finsum_in], 
  --conv in (_ * _) {rw ← pow_succ}, 
  let f : ℕ → ℤ := λ i, q * q^i, 
  have hf : ∀ i, f i = q * q^i := λ i, rfl, 
  let g : ℕ → ℤ := λ i, q^i, 
  have hg : ∀ i, g i = q^i := λ i, rfl, 
  have h1 := @finsum_in_eq_of_bij_on _ _ _ _ _ _ f g _ 
    (nat.Ico_add_bij 0 n 1) 
    (λ x hx, by {simp [hf,hg, pow_succ] }), 
  --rw hf at h1, 
  rw [h1, nat.zero_add, ←pow_zero q, ←hg 0, ← finsum_in_insert g, 
  nat.Ico_eq_Ioo, Ioo_insert_left_eq_Ico],  
  simp, simp, simp, apply set.Ico_ℕ_finite, 
end




import .basic 
import prelim.intervals 
import prelim.collections prelim.embed prelim.size prelim.induction prelim.minmax finsum.fin_api
import matroid.submatroid.projection matroid.pointcount matroid.submatroid.minor_iso 

noncomputable theory 
open_locale classical big_operators 

open set matroid 

/-- the size of a projective geometry over a `q`-element field. This is currently defined for 
integers `q`, but really `q` can live in any ring and it still makes sense. -/
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
  pg_size q n = ∑ᶠ i in Ico 0 n , q^i  := 
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

theorem kung {q : ℤ}(hq : 1 ≤ q){α : Type*} [fintype α] (M : matroid α) :
  M.has_no_line_minor (q+2) → M.ε univ ≤ pg_size q (M.rank_nat) := 
begin
  revert M, 
  by_contra hn, 
  obtain ⟨M,hM⟩ := min_counterexample_nonneg_int_param 
    _ (λ (M : matroid α), size (M.nonloops)) (λ s, size_nonneg _) hn, 
  push_neg at hM, rcases hM with ⟨⟨hMq, hMs⟩, hM_min⟩,  
  
  have no_parallel : ∀ (e f : α)(hne : e ≠ f), ¬ M.parallel e f, 
  { by_contra hn', push_neg at hn', obtain ⟨e,f,hne,hef⟩ := hn', 
    set M' := M ⟍ {f} with hM', 
    specialize hM_min M' 
      (size_strict_monotone (loopify_nonloop_fewer_nonloops hef.nonloop_right))
      (pseudominor_has_no_uniform_minor (by norm_num) (by linarith) (lp_is_pminor M {f}) hMq), 
    rw [rank_nat, r_nat] at hM_min hMs, 
    rw [hM', rank_eq_rank_loopify_parallel hef hne, 
          ε_loopify_parallel _ (ne.symm hne) (hef.symm)] at hM_min, 
    exact lt_irrefl _ (lt_of_le_of_lt hM_min hMs)},


  
  --rw [not_le] at hMs, 
  --dsimp only at hM hmin, 
  --obtain ⟨hMq, hMs⟩ := not_imp.mp hM , 
  


end
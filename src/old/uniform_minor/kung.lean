
import .basic
import prelim.intervals
import prelim.collections prelim.embed prelim.size prelim.induction prelim.minmax finsum.fin_api
import matroid.pointcount matroid.submatroid.minor_iso

noncomputable theory
open_locale classical big_operators

open set matroid

variables {α β : Type*} [fintype α] [comm_semiring β] [no_zero_divisors β]

/-- the size of a projective geometry over a `q`-element field; i.e `1 + q + q^2 + ... + q^{n-1}` -/
def pg_size' : β → ℕ → β
| q 0     := 0
| q (n+1) := 1 + q * (pg_size' q n)

@[simp] lemma pg_size'_zero (q : β) : pg_size' q 0 = 0 := rfl

@[simp] lemma pg_size'_succ {q : β}{n : ℕ}: pg_size' q n.succ = 1 + q * (pg_size' q n) := rfl

@[simp] lemma pg_size'_order_one (n : ℕ) : pg_size' (1 : ℤ) n = n :=
by {induction n with n ih, simp, simp [pg_size', ih, add_comm]  }

lemma pg_size'_eq_powsum (q : β) (n : ℕ) : pg_size' q n = ∑ᶠ i in Ico 0 n , q^i  :=
begin
  induction n with n ih,
    simp,
  rw [pg_size', ih], rw mul_distrib_finsum_in q,
  conv in (_ * _) {rw ← pow_succ},
  rw [← pow_zero q, finsum_Ico_shift, Ico_ℕ_eq_Ioo, nat.zero_add, nat.sub_self,
   ← finsum_in_insert, Ioo_insert_left_eq_Ico];
  simp [set.Ioo_ℕ_finite], 
end

lemma pg_size'_rat (q : ℤ) (n : ℕ) (hq : 2 ≤ q) : (pg_size' q n : ℚ) = (q^n - 1)/(q - 1) :=
begin
  induction n with n ih,
    simp,
  replace hq : (q : ℚ) -1 ≠ 0 := by {norm_cast, linarith},
  rw [pg_size', ih, ← mul_div_assoc, one_add_div hq, div_left_inj' hq, pow_succ],
  ring,
end

/- the size of a rank-`n` projective geometry over `GF(q)`, or equivalently the value of the sum
`1 + q + q² + q³ + ... + q^{n-1}` For convenience, this is defined for all integers `n`, taking
the value `0` if `n ≤ 0`.  -/
def pg_size (q n : ℤ) := pg_size' q n.to_nat

lemma pg_size_eq_zero (q n : ℤ)(hn : n ≤ 0) : pg_size q n = 0 :=
by {rw pg_size, convert pg_size'_zero q, rw int.to_nat_zero_of_nonpos hn, }

lemma pg_size_rec (q : ℤ) {n : ℤ} (hn : 1 ≤ n) : pg_size q n = 1 + q * (pg_size q (n-1)) :=
begin
  rw [pg_size, pg_size],
  obtain ⟨m,rfl⟩ := int.eq_coe_of_zero_le (by linarith : 0 ≤ n),
  norm_num,
  cases m, exfalso, norm_num at hn, refl,
end

lemma pg_size_eq_powsum (q n : ℤ) : pg_size q n = ∑ᶠ i in Ico 0 n.to_nat, q^i  :=
begin
  cases le_or_lt n 0 with hn hn',
  { convert finsum_in_empty.symm,
    exact pg_size_eq_zero q n hn,
    apply Ico_eq_empty,
    rw int.to_nat_zero_of_nonpos hn,  },
  convert pg_size'_eq_powsum q n.to_nat,
end

lemma pg_size_nonneg (q n : ℤ)(hq : 0 ≤ q): 0 ≤ pg_size q n :=
by {rw pg_size_eq_powsum, exact nonneg_of_finsum_in_nonneg (λ i hi, pow_nonneg hq i)}

/- Kung's lemma - the number of points in a rank-`r` matroid with no `U_{2,q+2}`-minor is at most
`1 + q + q^2 + ... + q^{n-1}`. -/
theorem rank_le_rank_pg_of_no_line {q : ℤ} (hq : 1 ≤ q) {M : matroid α} :
  M.has_no_line_minor (q+2) → M.ε univ ≤ pg_size q (M.rank) :=
begin
  /- If the result fails, we can choose M to be a minimal counterexample-/
  rw rank, revert M,
  by_contra hn,
  obtain ⟨M,hM⟩ := min_counterexample_nonneg_int_param
    _ (λ (M : matroid α), size (M.nonloops)) (λ s, size_nonneg _) hn,
  push_neg at hM,
  rcases hM with ⟨⟨hMq, hMs⟩, hM_min⟩, 
 
  /- The counterexample doesn't have rank zero, so it has a nonloop e-/
  by_cases hr : M.r univ ≤ 0,
  { linarith [pg_size_nonneg q (M.r univ) (by linarith : 0 ≤ q),
              ε_eq_r_of_r_le_one (by linarith: M.r univ ≤ 1)]},
  obtain ⟨e,-,he⟩ := contains_nonloop_of_one_le_rank (lt_of_not_ge' hr),

  /- Write ε M in terms of the sum of lengths of lines through e-/
  rw ε_as_ε_proj_nonloop he at hMs,

  /- These lines all contain at most q points other than e... -/
  set lines := {L : set α | M.is_line L ∧ e ∈ L} with hlines,
  have h_L_ub : ∀ L ∈ lines, M.ε L -1 ≤ q,
  { rintros L ⟨hL,-⟩, exact int.sub_right_le_of_le_add (line_restr_ub_ε (by linarith) hMq hL)},

  /- ... so we can get an upper bound on the sum of their lengths, which then translates to an
  upper bound in terms of `ε (M ⟋ e)`.  . -/
  have h_le : ∑ᶠ (L : set α) in lines, (M.ε L - 1) ≤  q * ((M ⟋ {e}).ε univ),
  { convert fin.finsum_in_le_finsum_in h_L_ub,
    rw [int.finsum_in_const_eq_mul_size, hlines, ε_proj_nonloop _ he]},
 
  /- Since `M ⟋ e` isn't a counterexample, it doesn't have too many points  -/
  specialize hM_min (M ⟋ {e})
    (size_strict_monotone (project_nonloop_fewer_nonloops he))
    (pminor_has_no_uniform_minor (by norm_num) (by linarith) (pr_is_pminor M {e}) hMq),
 
  /- Now `M`, being a counterexample, has lots of points, whereas `M ⟋ e` doesn't have too many.
  This is a contradiction. -/
  have hlt := calc
    pg_size q (M.r univ)  < 1 + ∑ᶠ (L : set α) in lines, (M.ε L - 1)
                        : hMs
                      ... ≤ 1 + q * (M ⟋ {e}).ε univ                
                        : add_le_add_left h_le 1
                      ... ≤ 1 + q * (pg_size q ((M ⟋ {e}).r univ))  
                        : add_le_add_left ((mul_le_mul_left (by linarith : 0 < q)).mpr hM_min) 1,

  rw [project_r, univ_union, rank_nonloop he, ← pg_size_rec q (by linarith : 1 ≤ M.r univ)] at hlt,
  exact lt_irrefl _ hlt,
end



theorem rank_set_le_rank_pg_of_no_line {q : ℤ}(hq : 1 ≤ q){α : Type*} [fintype α] {M : matroid α}
(X : set α) (h : M.has_no_line_minor (q+2)):
  M.ε X ≤ pg_size q (M.r X) :=
begin
  rw ← ε_loopify_to_eq_ε,
  convert rank_le_rank_pg_of_no_line hq _ using 1,
  { rw [loopify_to_r, univ_inter]},
  exact pminor_has_no_uniform_minor (by norm_num : (1 : ℤ) ≤ 2) (by linarith : 2 ≤ q + 2)
    (lp_is_pminor _ _) h,
end
 



/-
  This is (almost) boilerplate for the fact that a minimal counterexample has no parallel pairs.
  Not needed for the proof above, as it turned out, but may be useful later.

  have no_parallel : ∀ e f, M.parallel e f → e = f,
  { by_contra hn', push_neg at hn', obtain ⟨e,f,hef,hne⟩ := hn',
    set M' := M ⟍ {f} with hM',
    specialize hM_min M'
      (size_strict_monotone (loopify_nonloop_fewer_nonloops hef.nonloop_right))
      (pminor_has_no_uniform_minor (by norm_num) (by linarith) (lp_is_pminor M {f}) hMq),
    rw [rank_nat, r_nat] at hM_min hMs,
    rw [hM', rank_eq_rank_loopify_parallel hef hne,
          ε_loopify_parallel _ (ne.symm hne) (hef.symm)] at hM_min,
    exact lt_irrefl _ (lt_of_le_of_lt hM_min hMs)},

  have h' : M.is_simple_set (M.nonloops),
  { rw [simple_set_iff_no_loops_or_parallel_pairs, loopless_set_iff_subset_nonloops],
     refine ⟨subset.refl _, λ e f _ _ hef, no_parallel e f hef⟩},

  clear no_parallel hn,


-/
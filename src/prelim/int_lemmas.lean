import data.set.intervals 
import tactic 

-- some very mild additions to the int API in mathlib  

open_locale classical 

open set 

namespace int 

lemma le_sub_one_of_le_of_ne {x y : ℤ} : 
  x ≤ y → x ≠ y → x ≤ y - 1 :=
  λ h h', int.le_sub_one_of_lt (lt_of_le_of_ne h h')


lemma le_of_not_gt' {x y : ℤ} : 
  ¬ (y < x) → x ≤ y := 
  not_lt.mp

lemma nonneg_le_one_iff {x : ℤ}(h0 : 0 ≤ x)(h1 : x ≤ 1):
  x = 0 ∨ x = 1 :=
by {by_cases h : x ≤ 0, left, apply le_antisymm h h0, 
    push_neg at h, rw int.le_sub_one_iff.symm at h, 
    right, linarith, }


lemma nat_le_two_iff {x : ℕ}(h2 : x ≤ 2): 
  x = 0 ∨ x = 1 ∨ x = 2 :=
by {cases x, tauto, cases x, tauto, cases x, tauto, repeat {rw nat.succ_eq_add_one at h2}, linarith} 


lemma nonneg_le_two_iff {x : ℤ}(h0 : 0 ≤ x)(h2 : x ≤ 2):
  x = 0 ∨ x = 1 ∨ x = 2 :=
begin
  by_cases h2' : 2 ≤ x, right, right, apply le_antisymm h2 h2', 
  push_neg at h2', rw int.le_sub_one_iff.symm at h2', 
  cases nonneg_le_one_iff h0 h2', {left, exact h}, {right, left, exact h},
end 

lemma Ioo_add_bij (a b d : ℤ): 
  bij_on (+d) (Ioo a b) (Ioo (a+d) (b+d)) :=
begin
  refine ⟨λ x h, _, λ x hx y hy h, _, λ x h, _⟩, 
  { simpa using h, },
  { simpa using h, },
  simpa [add_comm] using h, 
end

lemma Ico_add_bij (a b d : ℤ): 
  bij_on (+d) (Ico a b) (Ico (a+d) (b+d)) :=
begin
  refine ⟨λ x h, _, λ x hx y hy h, _, λ x h, _⟩, 
  { simpa using h, },
  { simpa using h, },
  simpa [add_comm] using h, 
end

lemma Ioc_add_bij (a b d : ℤ): 
  bij_on (+d) (Ioc a b) (Ioc (a+d) (b+d)) :=
begin
  refine ⟨λ x h, _, λ x hx y hy h, _, λ x h, _⟩, 
  { simpa using h, },
  { simpa using h, },
  simpa [add_comm] using h, 
end


lemma Icc_add_bij (a b d : ℤ): 
  bij_on (+d) (Icc a b) (Icc (a+d) (b+d)) :=
begin
  refine ⟨λ x h, _, λ x hx y hy h, _, λ x h, _⟩, 
  { simpa using h, },
  { simpa using h, },
  simpa [add_comm] using h, 
end

end int 

namespace nat

lemma Ioo_eq_Ioc (a b : ℕ):
  Ioo a b = Ioc a (b-1) :=
by {cases b; {ext, simp [nat.lt_succ_iff]}} 

lemma Ioc_eq_Ioo (a b : ℕ):
  Ioc a b = Ioo a (b+1) := 
by simp [Ioo_eq_Ioc]

lemma Ioo_eq_Ico (a b : ℕ):
  Ioo a b = Ico (a+1) b := 
by {ext, simp [nat.succ_le_iff]}

lemma Ioc_eq_Icc (a b : ℕ):
  Ioc a b = Icc (a+1) b := 
by {ext, simp [nat.succ_le_iff]}

lemma Ioo_eq_Icc (a b : ℕ):
  Ioo a b = Icc (a+1) (b-1) :=
by rw [Ioo_eq_Ioc, Ioc_eq_Icc]

lemma Ico_eq_Icc (a b : ℕ)(h : a < b): 
  Ico a b = Icc a (b-1) :=
by {cases b, {ext, simp, rintros - rfl, exact not_lt_zero a h,  }, 
    ext, simp [nat.lt_succ_iff],  }

lemma Ico_elim {a b : ℕ}(hab : ¬(a < b)): 
  Ico a b = ∅ :=
by {push_neg at hab, ext, simp, exact λ h, le_trans hab h,   }

lemma Ioo_elim {a b : ℕ}(hab : b < a): 
  Ioo a b = ∅ :=
by {rw Ioo_eq_Ico, apply Ico_elim, simp,   }


lemma Icc_add_bij (a b d : ℕ): 
  bij_on (+d) (Icc a b) (Icc (a+d) (b+d)) :=
begin
  refine ⟨λ x h, _, λ x hx y hy h, _, λ x h, _⟩, 
  { simpa using h, },
  { simpa using h, },
  simp only [mem_image, mem_Ioo] at h ⊢, 
  refine ⟨x-d, ⟨_,_⟩ ,_⟩, 
  { have := le_trans (nat.le_add_left d a) h.1, sorry, },sorry, sorry,  
end

lemma Ioo_add_bij (a b d : ℕ): 
  bij_on (+d) (Ioo a b) (Ioo (a+d) (b+d)) :=
begin
  simp_rw Ioo_eq_Icc, convert Icc_add_bij _ _ _ using 2, apply nat.add_right_comm, 
end

lemma Ico_add_bij (a b d : ℕ): 
  bij_on (+d) (Ico a b) (Ico (a+d) (b+d)) :=
begin
  by_cases h : a < b, 
  { rw [Ico_eq_Icc a b h, Ico_eq_Icc _ _ (add_lt_add_right h d) ], 
    convert Icc_add_bij _ _ _, 
    cases b, exact false.elim (nat.not_lt_zero _ h), 
    cases d; 
    simp, }, 
  have h' : ¬ (a+d < b+d), { simpa using h, }, 
  rw [Ico_elim h, Ico_elim h'], 
  apply bij_on_empty, 
end

lemma Ioc_add_bij (a b d : ℕ):
  bij_on (+d) (Ioc a b) (Ioc (a+d) (b+d)) :=
by {simp_rw Ioc_eq_Icc, convert Icc_add_bij _ _ _ using 2, apply nat.add_right_comm} 



end nat 
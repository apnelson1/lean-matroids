import tactic .int_lemmas 
import data.set.intervals algebra.ordered_monoid


universe u 


/-- an add_comm_monoid with one-sided 'subtraction' in the sense that if a ≤ b, 
there is some c for which a + c = b -/
class ordered_cancel_add_comm_exists_sub_monoid (α : Type u)
  extends ordered_cancel_add_comm_monoid α := 
(exists_add_of_le : ∀ (a b : α), a ≤ b → ∃ (c : α), b = a + c)
--(add_right_cancel : ∀ (a b c : α), a + c = b + c → a = b)

instance ordered_add_comm_group.ordered_cancel_add_comm_exists_sub_monoid
(α : Type u)[ordered_add_comm_group α]: 
  ordered_cancel_add_comm_exists_sub_monoid α := 
{ exists_add_of_le := λ a b hab, ⟨b - a, (add_sub_cancel'_right a b).symm⟩,
  add_right_cancel := λ a b c, (add_left_inj _).mp, }

instance nat.ordered_cancel_add_comm_exists_sub_monoid :
  ordered_cancel_add_comm_exists_sub_monoid ℕ := 
{ exists_add_of_le := λ a b hab, ⟨_, (nat.add_sub_of_le hab).symm⟩, 
  add_right_cancel := λ a b c h, nat.add_right_cancel h}




lemma set.bij_on.self {α : Type*}(s : set α):
  set.bij_on id s s :=
by {refine ⟨λ x h, _, λ x hx y hy h, _, λ x h, _⟩; simpa using h} 


lemma Ioo_add_bij {α : Type}[ordered_cancel_add_comm_exists_sub_monoid α](a b d : α): 
  set.bij_on (+d) (set.Icc a b) (set.Icc (a+d) (b+d)) :=
begin
  refine ⟨λ x h, _, λ x hx y hy h, _, λ x h, _⟩, 
  { rw [set.mem_Icc] at ⊢ h, 
    exact ⟨add_le_add_right h.1 _, add_le_add_right h.2 _⟩},
  { exact ordered_cancel_add_comm_exists_sub_monoid.add_right_cancel _ _ _ h},
  rw set.mem_image, 
  simp_rw set.mem_Icc at h ⊢, 
  have : 
  --obtain ⟨x, hx⟩ := ordered_cancel_add_comm_exists_sub_monoid.exists_add_of_le
end




open set 

namespace int

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

lemma Ico_eq_Ioo (a b : ℕ)(h : 0 < a): 
  Ico a b = Ioo (a-1) b :=
begin
  ext, 
  cases a, 
  { exfalso, exact lt_irrefl 0 h}, 
  simp only [mem_Ioo, and.congr_left_iff, nat.sub_zero, succ_sub_succ_eq_sub, mem_Ico, lt_iff_succ_le], 
  tauto,   
end 

lemma Ico_eq_Icc (a b : ℕ)(h : a < b): 
  Ico a b = Icc a (b-1) :=
by {cases b, {ext, simp, rintros - rfl, exact not_lt_zero a h,  }, 
    ext, simp [nat.lt_succ_iff],  }

lemma Ico_elim {a b : ℕ}(hab : ¬(a < b)): 
  Ico a b = ∅ :=
by {push_neg at hab, ext, simp, exact λ h, le_trans hab h,   }

lemma Ioo_elim {a b : ℕ}(hab : b ≤ a + 1): 
  Ioo a b = ∅ :=
by {rw Ioo_eq_Ico, apply Ico_elim, simpa,   }


lemma Icc_add_bij (a b d : ℕ): 
  bij_on (+d) (Icc a b) (Icc (a+d) (b+d)) :=
begin
  refine ⟨λ x h, _, λ x hx y hy h, _, λ x h, _⟩, 
  { simpa using h, },
  { simpa using h, },
  simp only [mem_image, mem_Icc] at h ⊢, 
  rcases h with ⟨ha,hb⟩, 
  have hxd := le_trans (nat.le_add_left d a) ha, 
  refine ⟨x-d, ⟨_,_⟩ ,_⟩, 
  { exact (add_le_to_le_sub a hxd).mp ha, },
  { exact nat.sub_le_right_of_le_add hb, }, 
  exact nat.sub_
  add_cancel hxd, 
end

lemma Ioo_add_bij (a b d : ℕ): 
  bij_on (+d) (Ioo a b) (Ioo (a+d) (b+d)) :=
begin
  cases d, exact bij_on.self _,
  cases b, 
  { convert bij_on_empty _, {apply Ioo_elim, simp}, 
    exact Ioo_elim (le_trans (nat.add_le_add_right (nat.zero_le _) _) (nat.le_add_right _ _))},
  simp_rw Ioo_eq_Icc, convert Icc_add_bij _ _ _ using 2, 
  apply nat.add_right_comm, 
  simp, 
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

lemma set.Icc_ℕ_bij_Icc_ℤ (a b : ℕ): 
  bij_on coe (Icc a b) (Icc (a : ℤ) (b : ℤ)) := 
begin
  refine ⟨λ _ h, by {simpa using h}, λ _ _ _ _ h, by {simpa using h}, λ x h, _⟩, 
  rw mem_Icc at h, 
  simp_rw [mem_image, mem_Icc, ← int.coe_nat_le], 
  use int.to_nat x, 
  simp_rw int.to_nat_of_nonneg (le_trans (int.coe_nat_nonneg a) h.1), 
  exact ⟨h,rfl⟩, 
end

theorem set.Icc_ℕ_finite (l u : ℕ): 
  (Icc l u).finite := 
begin
  convert (set.finite_image_iff 
            (inj_on_of_injective (λ n m h, int.coe_nat_inj h) 
            (Icc l u))).mp _, 
  convert set.Icc_ℤ_finite l u, 
  ext, 
  simp_rw [mem_image, mem_Icc, ← int.coe_nat_le], 
  split, 
  { rintros ⟨y, h, rfl⟩, assumption, },
  rintros ⟨hl, hu⟩, 
  refine ⟨int.to_nat x, _⟩, 
  simp_rw int.to_nat_of_nonneg (le_trans (int.coe_nat_nonneg l) hl),
  tauto, 
end 

theorem set.Ico_ℕ_finite (l u : ℕ): 
  (Ico l u).finite :=
begin
  by_cases h: l < u, 
  { rw nat.Ico_eq_Icc _ _ h, apply set.Icc_ℕ_finite _ _},  
  rw Ico_eq_empty, simp, simpa using h,
end

theorem set.Ioc_ℕ_finite (l u : ℕ): 
  (Ioc l u).finite :=
by {rw nat.Ioc_eq_Icc, apply set.Icc_ℕ_finite}

theorem set.Ioo_ℕ_finite (l u : ℕ): 
  (Ioo l u).finite :=
by {rw nat.Ioo_eq_Icc, apply set.Icc_ℕ_finite}





section insert 

variables {α : Type*}[partial_order α]{a b : α}


@[simp] lemma Ioc_insert_left_eq_Icc (hab : a ≤ b): 
  insert a (Ioc a b) = Icc a b :=
begin
  ext x, 
  rcases em (x = a) with (rfl | ha), 
    simp [hab], 
  simp [eq_false_intro ha, ne.le_iff_lt (ne.symm ha)], 
end 

@[simp] lemma Ioo_insert_right_eq_Ioc (hab : a < b): 
  insert b (Ioo a b) = Ioc a b :=
begin
  ext x, 
  rcases em (x = b) with (rfl | hb), 
  { simp [le_refl x, hab], },
  simp [eq_false_intro hb, false_or, ne.le_iff_lt hb], 
end

@[simp] lemma Ioo_insert_left_eq_Ico (hab : a < b): 
  insert a (Ioo a b) = Ico a b := 
begin
  ext x, 
  rcases em (x = a) with (rfl | ha), 
    simpa [lt_irrefl, le_refl], 
  simp [eq_false_intro ha, ne.le_iff_lt (ne.symm ha)],   
end

@[simp] lemma Ico_insert_right_eq_Icc (hab : a ≤ b): 
  insert b (Ico a b) = Icc a b :=
begin
  ext x, 
  rcases em (x = b) with (rfl | hb), 
    simp [hab], 
  simp [eq_false_intro hb, ne.le_iff_lt hb], 
end



end insert 

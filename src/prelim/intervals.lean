import tactic .num_lemmas 
import data.set.intervals data.real.nnreal 

universe u 


open set 


section nat

open nat 

lemma Ioo_ℕ_eq_Ioc (a b : ℕ) :
  Ioo a b = Ioc a (b-1) :=
by {cases b; {ext, simp [lt_succ_iff]}} 

lemma Ioo_ℕ_eq_Ico (a b : ℕ) :
  Ioo a b = Ico (a+1) b := 
by {ext, simp [succ_le_iff]}

lemma Ioc_ℕ_eq_Ioo (a b : ℕ) :
  Ioc a b = Ioo a (b+1) := 
by simp [Ioo_ℕ_eq_Ioc]

lemma Ioc_ℕ_eq_Icc (a b : ℕ) :
  Ioc a b = Icc (a+1) b := 
by {ext, simp [succ_le_iff]}

lemma Ioo_ℕ_eq_Icc (a b : ℕ) :
  Ioo a b = Icc (a+1) (b-1) :=
by rw [Ioo_ℕ_eq_Ioc, Ioc_ℕ_eq_Icc]

lemma Ico_ℕ_eq_Ioo (a b : ℕ) (h : 0 < a) : 
  Ico a b = Ioo (a-1) b :=
begin
  ext, 
  cases a, 
  { exfalso, exact lt_irrefl 0 h}, 
  simp only [mem_Ioo, and.congr_left_iff, sub_zero, succ_sub_succ_eq_sub, mem_Ico, nat.lt_iff_succ_le], 
  tauto,   
end 

lemma Ico_ℕ_eq_Icc (a b : ℕ) (h : a < b) : 
  Ico a b = Icc a (b-1) :=
by {cases b, {ext, simp, rintros - rfl, exact not_lt_zero a h,  }, 
    ext, simp [nat.lt_succ_iff],  }



lemma set.Icc_ℕ_bij_Icc_ℤ (a b : ℕ) : 
  bij_on coe (Icc a b) (Icc (a : ℤ) (b : ℤ)) := 
begin
  refine ⟨λ _ h, by {simpa using h}, λ _ _ _ _ h, by {simpa using h}, λ x h, _⟩, 
  rw mem_Icc at h, 
  simp_rw [mem_image, mem_Icc, ← int.coe_nat_le], 
  use int.to_nat x, 
  simp_rw int.to_nat_of_nonneg (le_trans (int.coe_nat_nonneg a) h.1), 
  exact ⟨h,rfl⟩, 
end

theorem set.Icc_ℕ_finite (l u : ℕ) : 
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

theorem set.Ico_ℕ_finite (l u : ℕ) : 
  (Ico l u).finite :=
begin
  by_cases h: l < u, 
  { rw Ico_ℕ_eq_Icc _ _ h, apply set.Icc_ℕ_finite _ _},  
  rw Ico_eq_empty, simp, simpa using h,
end

theorem set.Ioc_ℕ_finite (l u : ℕ) : 
  (Ioc l u).finite :=
by {rw Ioc_ℕ_eq_Icc, apply set.Icc_ℕ_finite}

theorem set.Ioo_ℕ_finite (l u : ℕ) : 
  (Ioo l u).finite :=
by {rw Ioo_ℕ_eq_Icc, apply set.Icc_ℕ_finite}


end nat 

section int 
open int 

lemma Ioo_ℤ_eq_Ioc (a b : ℤ) :
  Ioo a b = Ioc a (b-1) :=
ext_iff.mpr (λ x, ⟨λ h, ⟨h.1, le_sub_one_iff.mpr h.2⟩ , λ h, ⟨h.1, le_sub_one_iff.mp h.2⟩⟩)

lemma Ioo_ℤ_eq_Ico (a b : ℤ) :
  Ioo a b = Ico (a+1) b := 
rfl 

lemma Ioo_ℤ_eq_Icc (a b : ℤ) :
  Ioo a b = Icc (a+1) (b-1) :=
eq.trans (Ioo_ℤ_eq_Ioc a b) rfl 

lemma Ioc_ℤ_eq_Ioo (a b : ℤ) :
  Ioc a b = Ioo a (b+1) := 
ext_iff.mpr (λ x, ⟨λ h, ⟨h.1, lt_add_one_iff.mpr h.2⟩ , λ h, ⟨h.1, lt_add_one_iff.mp h.2⟩⟩)

lemma Ioc_ℤ_eq_Icc (a b : ℤ) :
  Ioc a b = Icc (a+1) b := 
rfl 



end int



section insert 

variables {α : Type*} [partial_order α] {l u : α}


@[simp] lemma Ioc_insert_left_eq_Icc (hle : l ≤ u) : 
  insert l (Ioc l u) = Icc l u :=
begin
  ext x, 
  rcases em (x = l) with (rfl | hl), 
    simp [hle], 
  simp [eq_false_intro hl, ne.le_iff_lt (ne.symm hl)], 
end 

@[simp] lemma Ioo_insert_right_eq_Ioc (hlt : l < u) : 
  insert u (Ioo l u) = Ioc l u :=
begin
  ext x, 
  rcases em (x = u) with (rfl | hu), 
  { simp [le_refl x, hlt], },
  simp [eq_false_intro hu, false_or, ne.le_iff_lt hu], 
end

@[simp] lemma Ioo_insert_left_eq_Ico (hab : l < u) : 
  insert l (Ioo l u) = Ico l u := 
begin
  ext x, 
  rcases em (x = l) with (rfl | hl), 
    simpa [lt_irrefl, le_refl], 
  simp [eq_false_intro hl, ne.le_iff_lt (ne.symm hl)],   
end

@[simp] lemma Ico_insert_right_eq_Icc (hab : l ≤ u) : 
  insert u (Ico l u) = Icc l u :=
begin
  ext x, 
  rcases em (x = u) with (rfl | hu), 
    simp [hab], 
  simp [eq_false_intro hu, ne.le_iff_lt hu], 
end

end insert 

import finsum.fincard 

noncomputable theory
open_locale classical big_operators 

variables {α : Type*}

open set 

section incl_excl 
  
variables {M : Type*} [add_comm_group M]

def signed_convolution' (f : set α → M) (s : set α) : M :=
  ((-1)^(fincard s)) •ℤ ∑ᶠ a in s.powerset, (f a)

def signed_convolution (f : set α → M) (s : set α) : M :=
  ∑ᶠ a in s.powerset, ((-1)^(fincard a)) •ℤ (f a)

lemma twice (f : set α → M) {s : set α} (hs : s.finite): 
  signed_convolution (signed_convolution f) s = f s :=
begin
 
  unfold signed_convolution, 
  have hs' : s.powerset.finite := set.finite.finite_subsets hs,
  have ha_fin : ∀ (a : set α), a ∈ s.powerset → a.powerset.finite, 
    from λ a ha, hs'.subset (set.powerset_mono.mpr ha), 

  convert @finsum_in_eq_of_eq _ _ _ _ _ _ 
    (λ (a : set α) ha, @gsmul_distrib_finsum_in _ _ _ 
      (λ x, ((-1)^(fincard x)) •ℤ (f x)) 
      (a.powerset) 
      ((-1)^(fincard a)) 
      (set.finite.subset (ha_fin _ ha) (inter_subset_left _ _))), 
  
  rw finsum_comm_dep, 
  rotate, 
  { apply hs'.subset, rintros x ⟨hx, hx'⟩, assumption},
  { exact λ a ha, set.finite.subset (ha_fin _ ha) (inter_subset_left _ _)},

  convert (finsum_ite_singleton_eq s).symm, 
  funext, 
  split_ifs with h, 
  { convert (finsum_ite_singleton_eq y), 
    { change _ = {y}, ext x, simp [h, subset.antisymm_iff]}, 
    simp only [←gsmul_mul, ← pow_add, ← two_mul, nat.neg_one_pow_of_even ⟨_,rfl⟩, one_gsmul]}, 

  by_cases hsy : s ⊆ y, 
  { convert finsum_in_empty, 
    ext, 
    simp only [mem_sep_eq, mem_empty_eq, not_and, mem_powerset_iff, iff_false], 
    exact λ hxs hyx, h (subset.antisymm (subset.trans hyx hxs) hsy)},

  rw [subset_def] at hsy, push_neg at hsy, 
  obtain ⟨e, hes, hey⟩ := hsy, 

  apply finsum_in_involution (λ (x : set α), x.symm_diff {e}), 
  { rintros a ⟨has, hya⟩, 
    rw ←  add_gsmul, 
    convert zero_gsmul _,
    apply nat.neg_one_pow_sum_eq_zero_of_sum_odd,    
    rw [← zmod.eq_one_iff_odd, nat.cast_add, 
      set.finite.fincard_symm_diff_mod2 (hs.subset has) (set.finite_singleton _), 
      add_comm, ← add_assoc, ← two_mul], 
    convert zero_add _, 
      convert zero_mul _, 
    simp},
  { exact λ a ⟨has, hya⟩, ⟨subset.trans (symm_diff_subset_union _ _) 
                                        (union_subset has (singleton_subset_iff.mpr hes)), 
                           subset.trans (subset_diff_singleton hya hey)
                                        (diff_subset_symm_diff _ _ )⟩},
  { simp},
  refine λ a _ ha, false.elim _,
  simp only [symm_diff_eq_self_iff] at ha, 
  exact singleton_ne_empty _ ha, 
end

lemma twice' {f : set α → M} {s : set α} (hs : s.finite): 
  signed_convolution' (signed_convolution' f) s = f s:=
begin
  unfold signed_convolution', sorry, 
end

lemma ie_size [fintype α] (s : set (set α)): 
  (fincard (⋃₀ s) : ℤ) = ∑ᶠ t in s.powerset \ {∅}, (-1)^(fincard t +1) * fincard (⋂₀ t)  :=
begin
  suffices : (fincard (⋃₀ s)ᶜ : ℤ) = ∑ᶠ t in s.powerset, (-1)^(fincard t) * fincard (⋂₀ t), 
  { rw [finsum_in_sdiff_neg_of_fintype (by simp : {∅} ⊆ s.powerset)], 
    simp_rw [pow_add, mul_comm _ ((-1 : ℤ )^1 : ℤ), mul_assoc, ← mul_distrib_finsum_in],
    simp only [neg_mul_eq_neg_mul_symm, finsum_singleton, one_mul, neg_sub_neg, 
      sInter_empty, fincard_empty, pow_one, pow_zero],   
    rw [compl_fincard] at this,  
    linarith}, 
  
  set f : set (set α) → ℤ := λ t, fincard (⋂₀t) with hf, 
  set s' := (λ x, xᶜ) '' s with hs', 

  have := (twice f (set.finite.of_fintype _ : s'.finite)).symm, 
  simp_rw [hf, hs', signed_convolution, gsmul_int_int] at this,
  convert this using 1, 
  {congr', ext, simp},
  
  clear this, 
  have : ∀ x : set (set α), 
    ((-1 : ℤ) ^ fincard x) * (∑ᶠ (y : α) in ⋂₀ x, 1) = (∑ᶠ (y : α) in ⋂₀ x, ((-1 : ℤ) ^ fincard x), 
  { rw mul_distrib_finsum_in, },
  --conv in (_ * _) {congr, skip, rw fincard_eq_sum_ones, congr, congr, funext, skip, },
  --conv in (_ * _) 
  --{ change (-1 : ℤ) ^ fincard x * ↑∑ᶠ (y : α) in ⋂₀ x, (λ y, 1) y,
  --  rw mul_distrib_finsum_in ((-1 : ℤ)^(fincard x))},
  --ext t, 
  --rw signed_convolution, 
  --simp only [gsmul_int_int, mul_eq_mul_left_iff, or_false, int.neg_one_pow_ne_zero], 


  


end





end incl_excl 

  

    

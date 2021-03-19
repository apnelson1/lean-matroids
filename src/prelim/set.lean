
import tactic 
import .num_lemmas 
import data.set.basic 

open_locale classical 
noncomputable theory 

universes u v w

namespace set 

variables {α : Type*} {s s' t t' r r': set α}

/-- the symmetric difference of two sets -/
def symm_diff (s t : set α) : set α := (s \ t) ∪ (t \ s)

@[simp] lemma absorb_union_inter (s t : set α) : s ∪ (s ∩ t) = s := 
by calc s ∪ (s ∩ t) = (s ∩ univ) ∪ (s ∩ t) : by rw inter_univ  
                ... = s : by rw [←inter_distrib_left, union_comm, union_univ, inter_univ ]

@[simp] lemma absorb_inter_union (s t : set α) : s ∩ (s ∪ t) = s := 
by {rw [inter_comm, union_inter_cancel_left], }

lemma inter_distrib_inter_left (s t r : set α) : (s ∩ t) ∩ r = (s ∩ r) ∩ (t ∩ r) := 
by rw [inter_assoc s r, inter_comm r, inter_assoc t, inter_self, inter_assoc] 

lemma union_distrib_union_left (s t r : set α) : (s ∪ t) ∪ r = (s ∪ r) ∪ (t ∪ r) := 
by rw [union_assoc s r, union_comm r, union_assoc t, union_self, union_assoc]

lemma union_distrib_union_right (s t r : set α) : s ∪ (t ∪ r) = (s ∪ t) ∪ (s ∪ r) := 
by rw [union_comm s, union_distrib_union_left t r s, union_comm s, union_comm s]   

@[simp] lemma inter_right_self (s t : set α) : s ∩ t ∩ t = s ∩ t :=
by rw [inter_assoc, inter_self] 

@[simp] lemma union_right_self (s t : set α) : s ∪ t ∪ t = s ∪ t :=
by rw [union_assoc, union_self] 

lemma subset_iff_union_eq_left : (s ⊆ t) ↔ (s ∪ t = t) := 
by rw [←compl_subset_compl, subset_iff_inter_eq_left, ←compl_union, 
            compl_inj_iff, union_comm t s]

lemma subset_iff_union_eq_right : (t ⊆ s) ↔ (s ∪ t = s) := 
by rw [subset_iff_union_eq_left, union_comm]

lemma subset_refl (s : set α) : s ⊆ s :=
by rw [subset_iff_inter_eq_left, inter_self]

lemma subset_ssubset_or_eq : (s ⊆ t) → (s ⊂ t) ∨ s = t :=
λ hst, by {rw or_comm, apply eq_or_ssubset_of_subset hst}

lemma subset_iff_ssubset_or_eq : (s ⊆ t) ↔ (s ⊂ t) ∨ s = t :=
⟨λ h, subset_ssubset_or_eq h, λ h, by {cases h, from h.1, rw h}⟩

lemma ssubset_iff_subset_not_supset : s ⊂ t ↔ s ⊆ t ∧ ¬(t ⊆ s) :=
iff.rfl

lemma ssubset_of_subset_ne : s ⊆ t → s ≠ t → s ⊂ t := 
@lt_of_le_of_ne _ _ s t 

lemma ne_of_ssubset : s ⊂ t → s ≠ t := 
ne_of_irrefl

lemma ssubset_irrefl (s : set α) : ¬(s ⊂ s) :=
λ h, by {rw ssubset_iff_subset_ne at h, from h.2 rfl}

lemma univ_subset  (hs : univ ⊆ s) : s = univ := 
subset.antisymm (subset_univ s) hs
 
instance subset_subtype_nonempty : nonempty {t : set α // t ⊆ s} := 
by {apply nonempty_subtype.mpr, from ⟨_,empty_subset _⟩,  }

instance subtype_coe : has_coe {t : set α // t ⊆ s} (set α) := coe_subtype

lemma subset_empty : s ⊆ ∅ → s = ∅ := 
λ hs, subset.antisymm hs (empty_subset s)  

lemma ssubset_empty (s : set α) : ¬ s ⊂ ∅ := 
λ h, by {rw ssubset_iff_subset_ne at h, from h.2 (subset_empty h.1)}

lemma empty_of_subset_compl (h : s ⊆ sᶜ) : s = ∅ := 
by rwa [subset_iff_inter_eq_left, inter_compl_self, eq_comm] at h

lemma disjoint_compl_subset (h : s ∩ t = ∅) : s ⊆ tᶜ := 
by rw [subset_iff_inter_eq_left, ← empty_union (s ∩ tᶜ), ←h, 
            ←inter_distrib_left, union_compl_self, inter_univ]

lemma subset_compl_disjoint (h : s ⊆ tᶜ) : s ∩ t = ∅ := 
by {rw subset_iff_inter_eq_left at h, rw [←h, inter_assoc], simp}

lemma disjoint_iff_subset_compl : s ∩ t = ∅ ↔ s ⊆ tᶜ := 
⟨λ h, disjoint_compl_subset h, λ h, subset_compl_disjoint h⟩   

lemma disjoint_iff_inter_compl_eq_left : s ∩ t = ∅ ↔ s ∩ tᶜ = s := 
by rw [disjoint_iff_subset_compl, subset_iff_inter_eq_left]

lemma disjoint_iff_inter_compl_eq_right : s ∩ t = ∅ ↔ sᶜ ∩ t = t := 
by rw [inter_comm, disjoint_iff_inter_compl_eq_left, inter_comm]

lemma disjoint_iff_diff_eq_left : s ∩ t = ∅ ↔ s \ t = s := 
disjoint_iff_inter_compl_eq_left

lemma subset_iff_diff_empty (s t : set α) : s ⊆ t ↔ s \ t = ∅ :=
by {rw [←compl_compl t, ←disjoint_iff_subset_compl], simp [diff_eq],}

lemma subset_iff_partition (s t : set α) : s ⊆ t ↔ t = s ∪ (t \ s) := 
begin
  refine ⟨λ h, _, λ h, _⟩, 
  { nth_rewrite 0 ←(subset_iff_union_eq_left.mp h),
    rw [diff_eq, union_distrib_left], simp,},
  rw h, simp,  
end 

lemma subset_iff_disjoint_compl : s ⊆ t ↔ s ∩ tᶜ = ∅ :=
by rw [subset_iff_diff_empty, diff_eq]

lemma disjoint_of_subset_left' (hst : s ⊆ t) (htr : t ∩ r = ∅) : s ∩ r = ∅ :=
by {rw ←disjoint_iff_inter_eq_empty at *, exact disjoint_of_subset_left hst htr}

lemma disjoint_of_subset_right' (hst : s ⊆ t) (hrt : r ∩ t = ∅) : r ∩ s = ∅ :=
by {rw ←disjoint_iff_inter_eq_empty at *, exact disjoint_of_subset_right hst hrt, }

lemma disjoint_of_subsets (hss' : s ⊆ s') (htt' : t ⊆ t') (hst : s' ∩ t' = ∅) :
  s ∩ t = ∅ :=
by {rw ←disjoint_iff_inter_eq_empty at *, exact disjoint_of_subset hss' htt' hst, }

lemma cover_compl_subset :  s ∪ t = univ → sᶜ ⊆ t := 
λ h, by rw [subset_iff_union_eq_left, ←univ_inter (sᶜ ∪ t), ←h, 
              ←union_distrib_right, inter_compl_self, empty_union]

lemma compl_inj (h : sᶜ = tᶜ) : s = t := 
by rw [←compl_compl s, ←compl_compl t, h]

lemma compl_compl_inter_left (s t : set α) : (sᶜ ∩ t)ᶜ = s ∪ tᶜ := 
by {nth_rewrite 0 ←(compl_compl t), rw [compl_inter, compl_compl, compl_compl] }

lemma compl_compl_inter_right (s t : set α) : (s ∩ tᶜ)ᶜ = sᶜ ∪ t := 
by {nth_rewrite 0 ←(compl_compl s), rw [compl_inter, compl_compl, compl_compl] }

lemma compl_compl_union_left (s t : set α) : (sᶜ ∪ t)ᶜ = s ∩ tᶜ := 
by {nth_rewrite 0 ←(compl_compl t), rw [compl_union, compl_compl, compl_compl] }

lemma compl_compl_union_right (s t : set α) : (s ∪ tᶜ)ᶜ = sᶜ ∩ t := 
by {nth_rewrite 0 ←(compl_compl s), rw [compl_union, compl_compl, compl_compl] }


lemma compl_partition (s t : set α) : (s ∩ t) ∪ (sᶜ ∩ t) = t := 
by rw [←inter_distrib_right, union_compl_self, univ_inter]

lemma compl_partition_subset  (hst : s ⊆ t) : s ∪ (sᶜ ∩ t) = t := 
by {nth_rewrite 0 ←(subset_iff_inter_eq_left.mp hst), exact compl_partition s t}

lemma compl_pair (h : sᶜ = t) : (s = tᶜ) := 
by rw [←h, compl_compl]

lemma compl_pair_iff : (sᶜ = t) ↔ (s = tᶜ) := 
⟨λ h, compl_pair h, λ h, by {rw eq_comm at h, from (compl_pair h).symm}⟩

lemma compl_diff (s t : set α) : (s \ t)ᶜ = sᶜ ∪ t := 
by rw [diff_eq, compl_inter, compl_compl]

@[simp] lemma union_union_compl_self (s t : set α) : (s ∪ t) ∪ tᶜ = univ := 
by rw [union_assoc, union_compl_self, union_univ]

@[simp] lemma inter_inter_compl_self (s t : set α) : (s ∩ t) ∩ tᶜ = ∅ := 
by rw [inter_assoc, inter_compl_self, inter_empty]

@[simp] lemma union_union_compl_right (s t : set α) : s ∪ (t ∪ sᶜ) = univ := 
by rw [←union_assoc, union_comm s, union_union_compl_self]

@[simp] lemma inter_inter_compl_right (s t : set α) : s ∩ (t ∩ sᶜ) = ∅ := 
by rw [←inter_assoc, inter_comm s, inter_inter_compl_self]

lemma inter_union_compl_self (s t : set α) : s ∩ (t ∪ tᶜ) = s :=
by rw [union_compl_self, inter_univ]

lemma subset_own_compl : s ⊆ sᶜ → s = ∅ := 
  λ h, by {rw [subset_iff_union_eq_left,union_compl_self, ←compl_empty, compl_inj_iff] at h, 
                rw ←h }

lemma inter_subset_union (s t : set α) : s ∩ t ⊆ s ∪ t := 
  subset.trans (inter_subset_left s t) (subset_union_left s t)

lemma subset_of_inter_mp : s ⊆ t ∩ r → s ⊆ t ∧ s ⊆ r := 
  λ h, ⟨subset.trans h (inter_subset_left _ _), subset.trans h (inter_subset_right _ _)⟩  

lemma subset_of_set_and_compl : s ⊆ t → s ⊆ tᶜ → s = ∅ :=
  λ h1 h2, by {have := subset_inter h1 h2, rw inter_compl_self at this, 
  exact subset_empty this}

@[trans] lemma subset.lt_of_le_of_lt (_ : s ⊆ t) (_ : t ⊂ r) : s ⊂ r := 
lt_of_le_of_lt ‹s ≤ t› ‹t < r› 

@[trans] lemma subset.lt_of_lt_of_le (_ : s ⊂ t) (_ : t ⊆ r) : s ⊂ r := 
lt_of_lt_of_le ‹s < t› ‹t ≤ r›

lemma ssubset_not_supset (h : s ⊂ t) : ¬(t ⊆ s) :=
λ h', ssubset_irrefl _ (subset.lt_of_lt_of_le h h') 

lemma subset_not_ssupset (h: s ⊆ t) : ¬(t ⊂ s) := 
λ h', ssubset_irrefl _ (subset.lt_of_le_of_lt h h')

lemma eq_of_subset_not_ssubset  : s ⊆ t → ¬(s ⊂ t) → s = t := 
λ h h', by {simp only [not_and, not_not, ssubset_iff_subset_ne] at h', exact h' h}

@[trans] lemma ssubset.trans {s t r : set α} : s ⊂ t → t ⊂ r → s ⊂ r := 
λ hst htr, subset.lt_of_le_of_lt hst.1 htr

lemma ssubset_inter : s ≠ t → s ∩ t ⊂ s ∨ s ∩ t ⊂ t :=
begin
  intro h, 
  by_contra a, push_neg at a, simp_rw [ssubset_iff_subset_ne, not_and', not_imp_not] at a, 
  exact h (eq.trans (a.1 (inter_subset_left s t)).symm (a.2 (inter_subset_right s t)) ),
end 

lemma union_union_diff (s t r : set α) : (s ∪ r) ∪ (t \ r) = s ∪ t ∪ r :=
by {rw [diff_eq, union_distrib_left, union_right_comm, union_assoc _ r], simp,}

lemma union_diff_absorb (s t : set α) : s ∪ (t \ s) = s ∪ t :=
by {nth_rewrite 0 ←union_self s, rw [union_union_diff, union_right_comm, union_self]}

@[simp] lemma union_union_inter_compl_self (s t r : set α) : (s ∪ r) ∪ (t ∩ rᶜ) = s ∪ t ∪ r :=
by rw [←diff_eq, union_union_diff] 

lemma union_inter_diff (s t r : set α) : (s ∪ r) ∩ (t \ r) = (s ∩ t) \ r :=
by {rw [diff_eq, diff_eq, inter_distrib_right], simp [←inter_assoc, inter_right_comm r t rᶜ] }

lemma subset_of_subset_diff (h : s ⊆ t \ r) : s ⊆ t :=
λ x hx, by {have := h hx, rw mem_diff at this, exact this.1,  }

lemma eq_of_union_eq_inter : s ∪ t = s ∩ t → s = t := 
begin
  intro h, apply subset.antisymm, 
  calc s ⊆ (s ∪ t) : subset_union_left _ _ ... = s ∩ t : h ... ⊆ t : inter_subset_right _ _,  
  calc t ⊆ (s ∪ t) : subset_union_right _ _ ... = s ∩ t : h ... ⊆ s : inter_subset_left _ _,  
end 

lemma union_of_disjoint : s ∩ t = ∅ → s ∩ r = ∅ → s ∩ (t ∪ r) = ∅ :=
  λ ht hr, by {rw [inter_distrib_left, ht, hr], simp }

@[simp] lemma diff_union (s t : set α) : (s ∩ t) ∪ (s \ t) = s := 
by rw [diff_eq, ←inter_distrib_left, union_compl_self, inter_univ]

@[simp] lemma inter_diff (s t : set α) : s ∩ (t \ s)  = ∅ := 
by rw [diff_eq, ←inter_assoc, inter_right_comm, inter_compl_self, empty_inter]

@[simp] lemma partition_inter (s t : set α) : (s ∩ t) ∩ (s \ t) = ∅ := 
by rw [inter_assoc, inter_diff, inter_empty]

@[simp] lemma inter_diffs_eq_empty (s t : set α) : (s \ t) ∩ (t \ s) = ∅ := 
by {simp only [diff_eq], rw [inter_assoc, ←inter_assoc tᶜ], simp}

lemma pair_move {s r : set α} (t : set α) (hst : r ⊆ s) : (s \ r) ∪ (t ∪ r) = s ∪ t := 
by {ext, simp, tauto, }

lemma diff_empty_subset (s t : set α) : s \ t = ∅ → s ⊆ t := 
λ hst, by {rw [←diff_union s t, hst, union_empty], apply inter_subset_right}

lemma subset_diff_empty (s t : set α) : s ⊆ t → s \ t = ∅ := 
λ hst, by {rw diff_eq, rw subset_iff_inter_eq_left at hst, 
           rw [←hst, inter_assoc, inter_compl_self, inter_empty]}

lemma diff_empty_iff_subset (s t : set α) : s \ t = ∅ ↔ s ⊆ t := 
by {split, apply diff_empty_subset, apply subset_diff_empty}

lemma subset_diff_disjoint (s t r : set α) : s ⊆ t → s ∩ r = ∅ → s ⊆ t \ r := 
λ hst hsr, by {rw [disjoint_iff_subset_compl, subset_iff_inter_eq_left] at hsr, 
                rw [diff_eq, subset_iff_inter_eq_left, inter_comm t, ←inter_assoc, hsr, 
                      subset_iff_inter_eq_left.mp hst], }

lemma ssubset_diff_nonempty : s ⊂ t → (t \ s).nonempty :=
λ hst, set.nonempty_of_ssubset hst

lemma union_diff_of_subset  : s ⊆ t → s ∪ (t \ s) = t := 
λ h, by {rw [subset_iff_inter_eq_left, inter_comm] at h, have := diff_union t s, rwa h at this}

lemma diff_eq_self_of_subset_diff (h : s ⊆ r \ t) : s \ t = s :=
by {rw [←disjoint_iff_diff_eq_left, disjoint_iff_subset_compl], 
        refine subset.trans h _, simp [diff_eq],  }

@[simp] lemma diff_inter_right_eq_empty (s t : set α) : (t \ s) ∩ s = ∅ := 
by rw [inter_comm, inter_diff]

@[simp] lemma union_diff (s t : set α) : s ∪ (t \ s) = s ∪ t := 
by {rw [diff_eq, union_distrib_left, union_compl_self, inter_univ]}

@[simp] lemma union_diff_diff (s t : set α) : (s ∪ t) \ (t \ s) = s := 
by rw [diff_eq, diff_eq, compl_inter,compl_compl,union_comm, 
          ←union_distrib_right, inter_compl_self, empty_union]

lemma diff_self_diff (s t : set α) : s \ (s \ t) = s ∩ t := 
by rw [diff_eq, compl_diff, inter_distrib_left, inter_compl_self, empty_union]

lemma inter_distrib_diff (s t r : set α) : s ∩ (t \ r) = (s ∩ t) \ (s ∩ r) := 
by {rw [diff_eq, diff_eq, compl_inter, inter_distrib_left, inter_right_comm, 
                        inter_compl_self, empty_inter, empty_union, ←inter_assoc]}

lemma diff_inter_diff_right (s t r : set α) : (s \ r) ∩ (t \ r) = (s ∩ t) \ r := 
by {ext, tidy,  }

lemma diff_right_comm (s t r : set α) : s \ t \ r = s \ r \ t := 
by simp [diff_eq, inter_right_comm]



@[simp] lemma univ_diff (s : set α) : univ \ s = sᶜ := 
  (compl_eq_univ_diff s).symm

@[simp] lemma symm_diff_self (s : set α) : symm_diff s s = ∅ :=
by {unfold symm_diff, rw [diff_self, empty_union]}

lemma symm_diff_alt (s t : set α) : symm_diff s t = (s ∪ t) \ (s ∩ t) := 
begin
   unfold symm_diff, 
   repeat {rw [diff_eq]}, 
   rw [compl_inter, inter_distrib_right, inter_distrib_left, inter_distrib_left],
   simp,   
end  

lemma empty_ssubset_nonempty : s.nonempty → ∅ ⊂ s := 
λ h, by {rw ←set.ne_empty_iff_nonempty at h, 
          exact ssubset_of_subset_ne (empty_subset s) (ne.symm h)}

lemma nonempty_iff_empty_subset: s.nonempty ↔ ∅ ⊂ s := 
⟨ λ h, empty_ssubset_nonempty h, 
  λ h, by {rw ←set.ne_empty_iff_nonempty, exact (ne_of_ssubset h).symm, }⟩

lemma scompl_subset_compl.mpr : s ⊂ t → tᶜ ⊂ sᶜ := 
λ h, ssubset_of_subset_ne (compl_subset_compl.mpr h.1) 
      (λ h', by {rw (compl_inj h') at h, from ssubset_irrefl _ h}) 

lemma compl_to_ssubset : sᶜ ⊂ tᶜ → t ⊂ s := 
λ h, by {have := scompl_subset_compl.mpr h, repeat {rw compl_compl at this}, exact this }

lemma compl_iff_ssubset_compl : sᶜ ⊂ tᶜ ↔ t ⊂ s := 
by tidy 

lemma scompl_subset_comm : s ⊂ tᶜ ↔ t ⊂ sᶜ := 
by {convert compl_iff_ssubset_compl, rw compl_compl}

lemma ssubset_univ_of_ne_univ: s ≠ univ → s ⊂ univ := 
λ h, ssubset_of_subset_ne (subset_univ _) h

lemma pairwise_disjoint_inter_sUnion {S S₁ S₂: set (set α)} 
(hdj : pairwise_disjoint S) (h₁ : S₁ ⊆ S) (h₂ : S₂ ⊆ S) :
  sUnion (S₁ ∩ S₂) = sUnion S₁ ∩ sUnion S₂ := 
begin
  ext, simp only [mem_inter_iff, mem_sUnion], split, 
  { rintros ⟨t,hT,hxt⟩, rw mem_inter_iff at hT, refine ⟨⟨t,hT.1,hxt⟩,⟨t,hT.2,hxt⟩⟩, },
  rintros ⟨⟨t,h,hxt⟩,⟨t',h',hxt'⟩⟩,
  have := (pairwise_disjoint.elim hdj 
    (mem_of_mem_of_subset h h₁) 
    ((mem_of_mem_of_subset h' h₂)) x hxt hxt'), 
  subst this, use t, tidy, 
end

lemma infinite_of_finite_diff (hs : s.finite) (ht : t.infinite) :
  (t \ s).infinite := 
λ h, ht (by {refine (hs.union h).subset _, rw set.union_diff_self, apply set.subset_union_right, })

lemma infinite_of_union (hs : s.infinite) (t : set α) : 
  (s ∪ t).infinite := 
set.infinite_mono (set.subset_union_left _ _) hs 

lemma finite.diff (hs : s.finite) (t : set α) : (s \ t).finite :=  
  set.finite.subset hs (set.diff_subset _ _)

lemma finite.inter_left (hs : s.finite) (t : set α) : (s ∩ t).finite := 
  set.finite.subset hs (set.inter_subset_left _ _)

lemma finite.inter_right (ht : t.finite) (s : set α ) : (s ∩ t).finite := 
  set.finite.subset ht (set.inter_subset_right _ _)

end set 
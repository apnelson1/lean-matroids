
import algebra.big_operators.finprod
import mathlib.data.set.basic
import mathlib.data.set.sigma
import data.set.ncard
import data.setoid.partition 

noncomputable theory
open_locale big_operators classical

/-!
A few helper lemmas for a separate PR
-/

open set

section sigma
variables {ι : Type*} {α : ι → Type*} [finite ι] {x y : set (Σ i, α i)} {f : Π i, set (α i)}
  {i j : ι}

@[simp] lemma finsum_mem_one {α : Type*} (s : set α) : ∑ᶠ a ∈ s, 1 = s.ncard :=
begin
  have hsupp := @function.support_const α _ _ _ (nat.one_ne_zero),
  obtain h | h := s.finite_or_infinite,
  { have h' := h,
    rw [←inter_univ s, ← hsupp] at h',
    convert finsum_mem_eq_sum _ h',
    rw [←finset.card_eq_sum_ones, ncard_eq_to_finset_card _ h],
    congr',
    rw [hsupp, inter_univ]},
  rw [h.ncard, finsum_mem_eq_zero_of_infinite],
  rwa [hsupp, inter_univ],
end

@[simp] lemma finsum_one (α : Sort*) : ∑ᶠ (a : α), 1 = nat.card α :=
by rw [←finsum_mem_univ, finsum_mem_one, ncard_univ]

lemma sigma.ncard_eq_finsum_ncard_image_preimage_mk (x : set (Σ i, α i)) (hx : x.finite) :
  x.ncard = ∑ᶠ i, (sigma.mk i '' (sigma.mk i ⁻¹' x)).ncard :=
begin
  rw [←finsum_mem_one,  sigma.eq_Union_image_preimage_mk x,
    finsum_mem_Union (sigma.image_preimage_mk_pairwise_disjoint x)],
  { simp [←finsum_mem_one]},
  exact λ i, hx.subset (by simp),
end

lemma min_one_ncard_eq_ite {α : Type*} {s : set α} (hs : s.finite) :
  min 1 s.ncard = ite s.nonempty 1 0 :=
begin
  obtain (rfl | h) := s.eq_empty_or_nonempty, simp,
  rwa [if_pos h, min_eq_left_iff, nat.add_one_le_iff, ncard_pos hs],
end

@[simp] lemma sigma.ncard_preimage_mk (x : set (Σ i, α i)) (i : ι) :
  (sigma.mk i ⁻¹' x).ncard = (x ∩ sigma.fst ⁻¹' {i}).ncard :=
begin
  rw [←range_sigma_mk, ←preimage_inter_range,
    ncard_preimage_of_injective_subset_range sigma_mk_injective],
  apply inter_subset_right,
end

end sigma

section finsum

lemma finsum_mem_le_finsum_mem  {ι N : Type*} [ordered_add_comm_monoid N] {f g : ι → N} {s : set ι}
  (hf : (s ∩ function.support f).finite) (hg : (s ∩ function.support g).finite)
  (h : ∀ (i : ι), i ∈ s → f i ≤ g i) :
  ∑ᶠ (i ∈ s), f i ≤ ∑ᶠ (i ∈ s), g i :=
begin
  set hs' := hf.union hg,
  rw [← inter_distrib_left] at hs',
  rw [@finsum_mem_eq_sum_of_inter_support_eq _ _ _ f _ hs'.to_finset,
    @finsum_mem_eq_sum_of_inter_support_eq _ _ _ g _ hs'.to_finset],
  { apply finset.sum_le_sum,
    simp only [finite.mem_to_finset, mem_inter_iff, mem_union, function.mem_support, and_imp],
    exact λ i hi h', h i hi},
  { rw [finite.coe_to_finset, inter_assoc, inter_eq_self_of_subset_right (subset_union_right _ _)]},
  rw [finite.coe_to_finset, inter_assoc, inter_eq_self_of_subset_right (subset_union_left _ _)],
end

lemma finsum_le_finsum {ι N : Type*} [ordered_add_comm_monoid N] {f g : ι → N}
  (hf : f.support.finite) (hg : g.support.finite) (h : ∀ i, f i ≤ g i) :
  ∑ᶠ i, f i ≤ ∑ᶠ i, g i :=
begin
  rw [←finsum_mem_univ],
  nth_rewrite 1 ←finsum_mem_univ,
  apply finsum_mem_le_finsum_mem;
  simpa,
end

/-- If `f ≤ g` pointwise on `s`, but the sum of `g` is at most the sum of `f`, then `f = g` on `s`-/
lemma eq_of_finsum_mem_ge_finsum_mem_of_forall_le {ι N : Type*} [ordered_cancel_add_comm_monoid N]
  {f g : ι → N} {s : set ι} (hf : (s ∩ f.support).finite) (hg : (s ∩ g.support).finite)
  (h_le : ∀ i ∈ s, f i ≤ g i) (h_ge : ∑ᶠ i ∈ s, g i ≤ ∑ᶠ i ∈ s, f i) {a : ι} (ha : a ∈ s) :
  f a = g a :=
begin
  refine (h_le a ha).antisymm _,
  set s' := s \ {a} with hs',
  have hs'f : ((s \ {a}) ∩ f.support).finite, from
    hf.subset (inter_subset_inter_left _ (diff_subset _ _)),
  have hs'g : ((s \ {a}) ∩ g.support).finite, from
    hg.subset (inter_subset_inter_left _ (diff_subset _ _)),
  rw [←insert_eq_of_mem ha, ←insert_diff_singleton,
    finsum_mem_insert' _ (not_mem_diff_singleton _ _) hs'f,
    finsum_mem_insert' _ (not_mem_diff_singleton _ _) hs'g] at h_ge,
  exact le_of_add_le_add_right
    ((add_le_add_left (finsum_mem_le_finsum_mem hs'f hs'g (λ i hi, h_le _ hi.1)) (g a)).trans h_ge),
end

lemma eq_of_finsum_ge_finsum_of_forall_le {ι N : Type*} [ordered_cancel_add_comm_monoid N]
  {f g : ι → N} (hf : f.support.finite) (hg : g.support.finite) (h_le : ∀ i, f i ≤ g i)
  (h_ge : ∑ᶠ i, g i ≤ ∑ᶠ i, f i) (a : ι) :
  f a = g a :=
begin
  rw [←finsum_mem_univ f, ←finsum_mem_univ g] at h_ge,
  exact eq_of_finsum_mem_ge_finsum_mem_of_forall_le (by rwa univ_inter) (by rwa univ_inter)
    (λ i _, h_le i) h_ge (mem_univ a),
end

lemma finsum_le_finsum_of_subset  {ι M : Type*} [canonically_ordered_add_monoid M]  {f : ι → M}
  {s t : set ι}  (h : s ⊆ t) (ht : t.finite) :
  ∑ᶠ x ∈ s, f x ≤ ∑ᶠ x ∈ t, f x :=
begin
  rw [←inter_union_diff t s, inter_eq_right_iff_subset.mpr h,
    finsum_mem_union (@disjoint_sdiff_self_right _ s t _) (ht.subset h) (ht.diff _)],
  exact le_add_right rfl.le,
end

lemma finsum_le_finsum_of_subset'  {ι M : Type*} [canonically_ordered_add_monoid M]  {f : ι → M}
  {s t : set ι}  (h : s ⊆ t) (ht : (t ∩ f.support).finite) :
  ∑ᶠ x ∈ s, f x ≤ ∑ᶠ x ∈ t, f x :=
begin
  rw ←finsum_mem_inter_support,
  nth_rewrite 1 [←finsum_mem_inter_support],
  apply finsum_le_finsum_of_subset (inter_subset_inter_left _ h) ht,
end

lemma mem_le_finsum {ι M : Type*} [canonically_ordered_add_monoid M]  {f : ι → M} {x : ι}
{t : set ι}  (h : x ∈ t) (ht : t.finite) :
  f x ≤ ∑ᶠ x ∈ t, f x :=
begin
  rw ←@finsum_mem_singleton _ _ _ f x,
  exact finsum_le_finsum_of_subset (singleton_subset_iff.mpr h) ht,
end

lemma mem_le_finsum' {ι M : Type*} [canonically_ordered_add_monoid M]  {f : ι → M} {x : ι}
{t : set ι}  (h : x ∈ t) (ht : (t ∩ f.support).finite) :
  f x ≤ ∑ᶠ x ∈ t, f x :=
begin
  rw ←@finsum_mem_singleton _ _ _ f x,
  exact finsum_le_finsum_of_subset' (singleton_subset_iff.mpr h) ht,
end

lemma ncard_sUnion_le {α : Type*} (s : set (set α)) (hs : s.finite) (hs' : ∀ x ∈ s, set.finite x):
  (⋃₀ s).ncard ≤ ∑ᶠ x ∈ s, ncard x :=
begin
  refine set.finite.induction_on hs (by simp) (λ a t hat ht h, _),
  rw [sUnion_insert, finsum_mem_insert _ hat ht],
  exact (ncard_union_le _ _).trans (add_le_add rfl.le h),
end

lemma ncard_Union_le {ι α : Type*} [finite ι] (s : ι → set α) (h : ∀ i, (s i).finite) :
  (⋃ i, s i).ncard ≤ ∑ᶠ i, (s i).ncard :=
begin
   suffices h' : ∀ (t : set ι), (⋃ i ∈ t, s i).ncard ≤ ∑ᶠ (i ∈ t), (s i).ncard,
   { convert h' univ; simp},
  refine λ t, (to_finite t).induction_on (by simp) _,
  intros a t₀ hat₀ ht₀ IH,
  rw [bUnion_insert, finsum_mem_insert _ hat₀ ht₀],
  exact (ncard_union_le _ _).trans (add_le_add rfl.le IH),
end

@[simp] lemma finsum_mem_boole  {α : Type*} (s : set α) (p : α → Prop) :
  ∑ᶠ x ∈ s, ite (p x) 1 0 = (s ∩ set_of p).ncard :=
begin
  have hsupp : s ∩ set_of p = (s ∩ function.support (λ x, ite (p x) 1 0)), by {ext, simp},
  cases (s ∩ set_of p).finite_or_infinite,
  { have h' : (s ∩ function.support (λ x, ite (p x) 1 0)).finite,  by rwa ←hsupp,
    rw [finsum_mem_eq_sum _ h', ncard_eq_to_finset_card _ h],
    simp only [finset.sum_boole, finset.filter_true_of_mem, finite.mem_to_finset, mem_inter_iff,
      function.mem_support, ne.def, ite_eq_right_iff, nat.one_ne_zero, not_forall, not_false_iff,
      exists_prop, and_true, and_imp, imp_self, implies_true_iff, nat.cast_id],
    convert rfl },
  rw [finsum_mem_eq_zero_of_infinite, h.ncard],
  rwa ←hsupp,
end

@[simp] lemma finsum_boole {α : Type*} (p : α → Prop) :
  ∑ᶠ x, ite (p x) 1 0 = (set_of p).ncard :=
by rw [←finsum_mem_univ, finsum_mem_boole, univ_inter]

lemma ncard_eq_finsum_fiber {α ι : Type*} {s : set α} (hs : s.finite) (f : α → ι) :
  s.ncard = ∑ᶠ (i : ι), (s ∩ f ⁻¹' {i}).ncard :=
begin
  have h' : (function.support (λ i, (s ∩ f ⁻¹' {i}).ncard)).finite,
  { apply (hs.image f).subset,
    rintro i (h : ¬ (_ = 0)),
    rw [(ncard_eq_zero (hs.subset (inter_subset_left _ _))), ←ne.def, ←nonempty_iff_ne_empty] at h,
     obtain ⟨x, hxs, hx⟩ := h,
     exact ⟨x, hxs, by simpa using hx⟩ },

  rw [ncard_eq_to_finset_card _ hs,
    @finset.card_eq_sum_card_fiberwise _ _ _ f (hs.to_finset) ((hs.image f).to_finset)],
  { rw [←finsum_mem_univ, ←finsum_mem_inter_support, univ_inter,
     finsum_mem_eq_finite_to_finset_sum _ h', finset.sum_congr],
    { ext,
      simp_rw [finite.mem_to_finset, mem_image, function.mem_support, ne.def,
          ncard_eq_zero (hs.subset (inter_subset_left _ _)), eq_empty_iff_forall_not_mem,
        not_forall, mem_inter_iff, not_not, mem_preimage, mem_singleton_iff]},

    intros x hx,
    rw [ncard_eq_to_finset_card _ (hs.subset (inter_subset_left _ _))] ,
    convert rfl,
    ext,
    simp },
  simp only [finite.mem_to_finset, mem_image],
  exact λ x hx, ⟨x, hx, rfl⟩,
end

lemma card_eq_finsum_fiber {α ι : Type*} [finite α] (f : α → ι) : 
  nat.card α = ∑ᶠ (i : ι), (f ⁻¹' {i}).ncard := 
begin
  rw [←ncard_univ], 
  convert ncard_eq_finsum_fiber (to_finite univ) f using 1,  
  exact finsum_congr (λ _, by rw univ_inter), 
end 

lemma finsum_indexed_partition_ncard_eq {α ι : Type*} [finite α] {s : ι → set α} 
(h : indexed_partition s) : 
  ∑ᶠ i, set.ncard (s i) = nat.card α :=
by { simp_rw [h.eq], convert (card_eq_finsum_fiber h.index).symm }
  
/-- A `setoid` partition noncomputably gives rise to an indexed partition -/
noncomputable def setoid.is_partition.indexed_partition 
{α : Type*} {c : set (set α)} (h : setoid.is_partition c) : 
  @indexed_partition c α coe := 
indexed_partition.mk' coe 
  (by { rintro ⟨a,ha⟩ ⟨b,hb⟩ hne, exact h.pairwise_disjoint ha hb (by simpa using hne) })
  (by { rintro ⟨a,ha⟩, exact setoid.nonempty_of_mem_partition h ha } )
  (by { intro x, have hu := mem_univ x, rw [←h.sUnion_eq_univ, mem_sUnion] at hu, 
    obtain ⟨t, htc, htx⟩ := hu, exact ⟨⟨t, htc⟩, htx⟩ })

lemma finsum_partition_eq {α : Type*} [finite α] {c : set (set α)} (h : setoid.is_partition c) : 
  ∑ᶠ s ∈ c, set.ncard s = nat.card α :=  
begin
  convert finsum_indexed_partition_ncard_eq h.indexed_partition using 1,
  rw [finsum_set_coe_eq_finsum_mem], 
end 

end finsum

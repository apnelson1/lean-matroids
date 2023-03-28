
import tactic 
import order.complete_lattice
import set_theory.cardinal.finite
import ..aux.ncard
import algebra.big_operators.finprod

noncomputable theory 
open_locale classical 
open_locale big_operators

/-! 
A few helper lemmas for a separate PR 
-/

section finset 

variables {α : Type*} {X Y : finset α}

lemma finset.exists_mem_sdiff_of_card_lt_card (h : X.card < Y.card) : 
  ∃ e, e ∈ Y ∧ e ∉ X :=
begin
  refine by_contra (λ h', h.not_le (finset.card_mono (λ x hx, _))), 
  push_neg at h', 
  exact h' _ hx, 
end  

@[simp] lemma finset.card_inter_add_card_sdiff_eq_card (X Y : finset α) : 
  (X ∩ Y).card + (X \ Y).card = X.card :=
by {convert @finset.card_sdiff_add_card_eq_card _ _ _ _ _; simp}

lemma finset.card_sdiff_eq_card_sdiff_iff_card_eq_card {X Y : finset α} : 
  X.card = Y.card ↔ (X \ Y).card = (Y \ X).card :=
by rw [←finset.card_inter_add_card_sdiff_eq_card X Y, ←finset.card_inter_add_card_sdiff_eq_card Y X, 
    finset.inter_comm, add_right_inj]
 
lemma finset.card_le_card_iff_card_sdiff_le_card_sdiff {X Y : finset α} : 
  X.card ≤ Y.card ↔ (X \ Y).card ≤ (Y \ X).card := 
by rw [←finset.card_inter_add_card_sdiff_eq_card X Y, ←finset.card_inter_add_card_sdiff_eq_card Y X, 
  finset.inter_comm, add_le_add_iff_left]

lemma finset.card_lt_card_iff_card_sdiff_lt_card_sdiff {X Y : finset α} : 
  X.card < Y.card ↔ (X \ Y).card < (Y \ X).card := 
by rw [←finset.card_inter_add_card_sdiff_eq_card X Y, ←finset.card_inter_add_card_sdiff_eq_card Y X, 
    finset.inter_comm, add_lt_add_iff_left]

lemma nat.card_eq_to_finset_card [fintype α] (S : set α) : 
  nat.card S = S.to_finset.card :=
by simp [nat.card_eq_fintype_card] 

end finset

open set 

theorem set.finite.exists_minimal_wrt {α β : Type*} [partial_order β] (f : α → β) (s : set α) 
  (h : s.finite) :
s.nonempty → (∃ (a : α) (H : a ∈ s), ∀ (a' : α), a' ∈ s → f a' ≤ f a → f a = f a') :=
@set.finite.exists_maximal_wrt α (order_dual β) _ f s h  

lemma set.finite.exists_maximal {α : Type*} [finite α] [partial_order α] (P : α → Prop) 
(h : ∃ x, P x) : 
  ∃ m, P m ∧ ∀ x, P x → m ≤ x → m = x :=
begin
  obtain ⟨m,⟨hm : P m,hm'⟩⟩ := set.finite.exists_maximal_wrt (@id α) (set_of P) (to_finite _) h, 
  exact ⟨m, hm, hm'⟩, 
end    

lemma set.finite.exists_minimal {α : Type*} [finite α] [partial_order α] (P : α → Prop) 
(h : ∃ x, P x) : ∃ m, P m ∧ ∀ x, P x → x ≤ m → m = x :=
@set.finite.exists_maximal (order_dual α) _ _ P h

lemma set.finite.exists_minimal_subset {α : Type*} {s : set α} {P : set α → Prop} (hs : s.finite) 
(hsP : P s) : 
  ∃ t ⊆ s, P t ∧ ∀ t' ⊂ t, ¬ P t' := 
begin
  obtain ⟨t₀,ht₀,ht₀min⟩ := @set.finite.exists_minimal (set s) (@set.finite' _ (hs.to_subtype)) _ 
    (P ∘ (set.image coe)) ⟨univ, by simpa⟩,
  refine ⟨coe '' t₀, by simp, ht₀, λ t' ht' hPt', ht'.ne _⟩, 
  have ht's : t' ⊆ s, from ht'.subset.trans (by simp),
  have ht'' := subtype.coe_image_of_subset ht's,          
  simp_rw function.comp_app at ht₀ ht₀min,

  rw [ht₀min {x : ↥s | ↑x ∈ t'} (by rwa ht'') _, ht''],  
  convert @preimage_mono _ _ (coe : s → α)   _ _ ht'.subset, 
  rw preimage_image_eq _ subtype.coe_injective, 
end     

lemma set.diff_singleton_ssubset_iff {α : Type*} {e : α} {S : set α} : 
  S \ {e} ⊂ S ↔ e ∈ S :=
⟨ λ h, by_contra (λ he, h.ne (by rwa [sdiff_eq_left, disjoint_singleton_right])), 
  λ h, ssubset_of_ne_of_subset 
    (by rwa [ne.def, sdiff_eq_left, disjoint_singleton_right, not_not_mem]) (diff_subset _ _)⟩

lemma set.diff_singleton_ssubset {α : Type*} {e : α} {S : set α} (heS : e ∈ S) : 
  S \ {e} ⊂ S :=
set.diff_singleton_ssubset_iff.mpr heS 

lemma insert_diff_singleton_comm {α : Type*} {X : set α} {e f : α} (hef : e ≠ f) : 
  insert e (X \ {f}) = (insert e X) \ {f} :=
by rw [←union_singleton, ←union_singleton, union_diff_distrib, 
  diff_singleton_eq_self (by simpa using hef.symm : f ∉ {e})]

lemma function.injective.compl_image {α β : Type*} {f : α → β} (hf : f.injective) (X : set α) :
  (f '' X)ᶜ = f '' (Xᶜ) ∪ (range f)ᶜ := 
begin
  apply compl_injective, 
  simp_rw [compl_union, compl_compl], 
  refine (subset_inter _ (image_subset_range _ _)).antisymm _, 
  { rintro x ⟨y, hy, rfl⟩ ⟨z,hz, hzy⟩,
    rw [hf hzy] at hz, 
    exact hz hy},
  rintro x ⟨hx, ⟨y, rfl⟩⟩, 
  exact ⟨y, by_contra (λ (hy : y ∈ Xᶜ), hx (mem_image_of_mem _ hy)), rfl⟩,    
end   

lemma singleton_inter_eq_of_mem {α : Type*} {x : α} {s : set α} (hx : x ∈ s) : 
  {x} ∩ s = {x} := 
(inter_subset_left _ _).antisymm (subset_inter subset_rfl (singleton_subset_iff.mpr hx))

lemma inter_singleton_eq_of_mem {α : Type*} {x : α} {s : set α} (hx : x ∈ s) : 
  s ∩ {x} = {x} := 
(inter_subset_right _ _).antisymm (subset_inter (singleton_subset_iff.mpr hx) subset_rfl)

@[simp] lemma diff_diff_cancel_right {α : Type*} (s t : set α) : 
  s \ (t \ s) = s :=  
(diff_subset _ _).antisymm (λ x hx, ⟨hx, λ h, h.2 hx⟩)

@[simp] lemma not_mem_diff_singleton {α : Type*} (x : α) (s : set α) :
  x ∉ s \ {x} :=
by simp only [mem_diff, mem_singleton, not_true, and_false, not_false_iff]

section sigma

/- Some lemmas about sets in sigma types -/

variables {ι : Type*} {α : ι → Type*} {x y : set (Σ i, α i)} {f : ∀ i, set (α i)} {i j : ι}

lemma sigma.subset_iff :
  x ⊆ y ↔ ∀ i, (sigma.mk i ⁻¹' x) ⊆ (sigma.mk i ⁻¹' y) := 
⟨λ h i a ha, h ha, λ h ⟨i,a⟩ ha, h i ha⟩

lemma sigma.eq_iff_forall_preimage_mk_eq :
  x = y ↔ ∀ i, (sigma.mk i ⁻¹' x) = (sigma.mk i ⁻¹' y) := 
⟨by {rintro rfl, exact λ _, rfl}, λ h, (sigma.subset_iff.mpr (λ i, (h i).subset)).antisymm 
  (sigma.subset_iff.mpr (λ i, (h i).symm.subset))⟩

@[simp] lemma sigma.preimage_mk_Union_image_mk : 
  sigma.mk j ⁻¹' (⋃ (i : ι), sigma.mk i '' f i) = f j:= 
begin
  rw [preimage_Union, subset_antisymm_iff, Union_subset_iff], 
  refine ⟨λ k, _, subset_Union_of_subset j (by rw preimage_image_eq _ sigma_mk_injective)⟩,
  obtain (rfl | hjk) := eq_or_ne j k, 
  { rw preimage_image_eq _ sigma_mk_injective},
  rw preimage_image_sigma_mk_of_ne hjk, 
  exact empty_subset _,
end  

lemma sigma.eq_Union_image_preimage_mk (x : set (Σ i, α i)) : 
  x = ⋃ (i : ι), sigma.mk i '' (sigma.mk i ⁻¹' x) := 
by simp [sigma.eq_iff_forall_preimage_mk_eq]

lemma sigma.image_preimage_mk_pairwise_disjoint (x : set (Σ i, α i)) : 
  pairwise (disjoint on (λ i, sigma.mk i '' (sigma.mk i ⁻¹' x))) := 
begin
  refine λ i j hij s hs hs' a ha, hij _, 
  simp only [bot_eq_empty, le_eq_subset, mem_empty_iff_false] at hs hs' ⊢,  
  obtain ⟨t,ht,rfl⟩ := hs ha,  
  obtain ⟨t', ht', h'⟩ := hs' ha, 
  simp only at h', 
  rw h'.1, 
end 

variables [finite ι]

lemma sigma.ncard_eq_finsum_ncard_image_preimage_mk (x : set (Σ i, α i)) (hx : x.finite) :
  x.ncard = ∑ᶠ i, (sigma.mk i '' (sigma.mk i ⁻¹' x)).ncard :=
begin
  rw [←finsum_mem_one,  sigma.eq_Union_image_preimage_mk x, 
    finsum_mem_Union (sigma.image_preimage_mk_pairwise_disjoint x)], 
  { simp [←finsum_mem_one]},
  exact λ i, hx.subset (by simp), 
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

lemma finsum_mem_le_finsum_mem  {ι N : Type*} [ordered_add_comm_monoid N] {f g : ι → N} 
{s : set ι} (hf : (s ∩ function.support f).finite) (hg : (s ∩ function.support g).finite) 
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

/- I wasn't able to prove either of the following lemmas by reducing to their corresponding finset
  versions - it gave a horrible mess. But induction works fine. -/
lemma ncard_sUnion_le {α : Type*} (s : set (set α)) (hs : s.finite) (hs' : ∀ x ∈ s, set.finite x):
  (⋃₀ s).ncard ≤ ∑ᶠ x ∈ s, ncard x := 
begin
  by_contra' h', 
  obtain ⟨t,hts,ht,hmin⟩ := set.finite.exists_minimal_subset hs h', 
  have ht_ne : t.nonempty, by { rw nonempty_iff_ne_empty, rintro rfl, simpa using ht},
  obtain ⟨x,hxt⟩ := ht_ne,
  apply hmin (t \ {x}) (set.diff_singleton_ssubset hxt), 

  have ht_eq : insert x (t \ {x}) = t, by simpa using insert_eq_of_mem hxt,
  
  rw [← ht_eq, sUnion_insert, finsum_mem_insert _ (not_mem_diff_singleton _ _) 
    (hs.subset ((diff_subset _ _).trans hts))] at ht, 
  exact (add_lt_add_iff_left _).mp (ht.trans_le (ncard_union_le _ _)), 
end 

lemma ncard_Union_le {ι α : Type*} [finite ι] (s : ι → set α) (h : ∀ i, (s i).finite) :
  (⋃ i, s i).ncard ≤ ∑ᶠ i, (s i).ncard := 
begin
  rw [←finsum_mem_univ, ←bUnion_univ], 
  by_contra' h', 
  set P : set ι → Prop := λ t, ∑ᶠ i ∈ t, (s i).ncard < (⋃ (x ∈ t), s x).ncard with hP,  
  have h_univ : P univ := h', 
  obtain ⟨t,-,hPt,hmin⟩ :=  set.finite.exists_minimal_subset (to_finite _) h_univ,   
  simp_rw [hP] at hPt hmin, 
  have hne : t.nonempty, by { rw nonempty_iff_ne_empty, rintro rfl, simpa using hPt},
  obtain ⟨x,hxt⟩ := hne,   
  apply hmin (t \ {x}) (set.diff_singleton_ssubset hxt), 

  have ht_eq : insert x (t \ {x}) = t, by simpa using insert_eq_of_mem hxt,
  rw [←ht_eq, finsum_mem_insert _ (not_mem_diff_singleton _ _) (@to_finite _ (t \ {x}) _), 
    bUnion_insert] at hPt, 
  exact (add_lt_add_iff_left _).mp (hPt.trans_le (ncard_union_le _ _)), 
end  


end finsum


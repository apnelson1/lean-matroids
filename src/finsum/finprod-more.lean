
import algebra.big_operators.finprod
import group_theory.group_action.defs

open function set

open_locale classical big_operators

section main

variables {α β M : Type*} [comm_monoid M] {f g : α → M} {s t : set α} {x y : α}


/-- A set `s` has finite intersection with `mul_support f` if the product of `f` over `s`
   is not equal to one. -/
@[to_additive] lemma finite_mul_support_of_finprod_mem_ne_one (h : ∏ᶠ i ∈ s, f i ≠ 1) :
  (s ∩ mul_support f).finite :=
by_contra (λ hn, h (finprod_mem_eq_one_of_infinite hn))

/-- `mul_support f` is finite if the product of `f` over `s` is not equal to one. -/
@[to_additive] lemma finite_mul_support_of_finprod_ne_one (h : ∏ᶠ i, f i ≠ 1) :
  (mul_support f).finite :=
by {rw ← finprod_mem_univ at h, convert finite_mul_support_of_finprod_mem_ne_one h, simp}

/-- Given a function `g` that is involutive on `s` for which `(f a) * (f g a) = 1` and `f` is
one on every fixed point of `g`, the product of `f` on `s` is one. -/
@[to_additive] lemma finprod_mem_of_involution (f : α → M) (g : α → α)
(h_cancel : ∀ a ∈ s, (f a) * f (g a) = 1)
(h_mem : ∀ a ∈ s, g a ∈ s)
(h_inv : ∀ a ∈ s, g (g a) = a)
(h_ne : ∀ a ∈ s, g a = a → f a = 1):
  ∏ᶠ a ∈ s, f a = 1 :=
begin
  by_cases hs : (s ∩ mul_support f).finite, swap, rw finprod_mem_eq_one_of_infinite hs,
  rw [finprod_mem_eq_prod _ hs],
  refine finset.prod_involution (λ a _, g a) _ _ _ _,
  any_goals {simp_rw [finite.mem_to_finset, mem_inter_iff, mem_mul_support]},
  any_goals {tauto},
    exact λ a h hne hg, hne (h_ne a h.1 hg),
  refine λ a h, ⟨h_mem a h.1, (λ hg, _)⟩,
  specialize h_cancel a h.1,
  rw [hg, mul_one] at h_cancel,
  exact h.2 h_cancel,
end

end main

section hom

variables {α β M A : Type*} {f g : α → M} {s t : set α} {x y : α}

lemma finsum_mem_smul_distrib' [monoid M] [add_comm_monoid A] [distrib_mul_action M A]
{f : α → A} (c : M) (hf : (s ∩ support f).finite) : c • (∑ᶠ i ∈ s, f i) = ∑ᶠ i ∈ s, (c • (f i)) :=
add_monoid_hom.map_finsum_mem' (const_smul_hom A c) hf

lemma finsum_mem_smul_distrib [monoid M] [add_comm_monoid A] [distrib_mul_action M A]
{f : α → A} (c : M) (hs : s.finite) : c • (∑ᶠ i ∈ s, f i) = ∑ᶠ i ∈ s, (c • (f i)) :=
add_monoid_hom.map_finsum_mem _ (const_smul_hom A c) hs

end hom

section group

variables {α β M : Type*} [comm_group M] {f g : α → M} {s t : set α} {x y : α}

@[to_additive] lemma finprod_mem_inv_distrib' (hs : (s ∩ mul_support f).finite):
  ∏ᶠ i ∈ s, (f i)⁻¹ = (∏ᶠ i ∈ s, f i)⁻¹ :=
(monoid_hom.map_finprod_mem' (monoid_hom.id M)⁻¹ hs).symm

@[to_additive] lemma finprod_mem_inv_distrib (hs : s.finite):
  ∏ᶠ i ∈ s, (f i)⁻¹ = (∏ᶠ i ∈ s, f i)⁻¹ :=
(monoid_hom.map_finprod_mem f (monoid_hom.id M)⁻¹ hs).symm

@[to_additive] lemma finprod_mem_div_distrib' (hf : (s ∩ (mul_support f)).finite)
  (hg : (s ∩ (mul_support g)).finite):
  ∏ᶠ i ∈ s, (f i)/(g i) = (∏ᶠ i ∈ s, f i) / (∏ᶠ i ∈ s, g i) :=
begin
  simp_rw [div_eq_mul_inv],
  rw [finprod_mem_mul_distrib' hf (by rwa mul_support_inv g), finprod_mem_inv_distrib' hg],
end

@[to_additive] lemma finprod_mem_div_distrib (hs : s.finite) :
  ∏ᶠ i ∈ s, (f i)/(g i) = (∏ᶠ i ∈ s, f i) / (∏ᶠ i ∈ s, g i) :=
finprod_mem_div_distrib' (hs.inter_of_left _) (hs.inter_of_left _)

@[to_additive] lemma finprod_in_diff_subset' (hst : s ⊆ t) (ht : (t ∩ mul_support f).finite):
  ∏ᶠ i ∈ (s \ t), f i = ∏ᶠ i ∈ s, f i / ∏ᶠ i ∈ t, f i :=
by {have := finprod_mem_mul_diff' ht hst, }
end group

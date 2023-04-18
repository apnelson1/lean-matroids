import mathlib.ncard
import mathlib.data.set.finite
import order.minimal 

open_locale classical
open_locale big_operators

open set

variables {E : Type*} 

section prelim 

variables {B B' B₁ B₂ : set E}

/-- A predicate `P` on sets satisfies the exchange property if, for all `X` and `Y` satisfying `P`
  and all `a ∈ X \ Y`, there exists `b ∈ Y \ X` so that swapping `a` for `b` in `X` maintains `P`.-/
def exchange_property (P : set E → Prop) : Prop :=
  ∀ X Y, P X → P Y → ∀ a ∈ X \ Y, ∃ b ∈ Y \ X, P (insert b (X \ {a}))

def exists_maximal_subset_property (P : set E → Prop) : Prop := 
  ∀ I X, P I → I ⊆ X → (maximals (⊆) {Y | P Y ∧ I ⊆ Y ∧ Y ⊆ X}).nonempty 

private lemma antichain_of_exch {base : set E → Prop} (exch : exchange_property base) 
(hB : base B) (hB' : base B') (h : B ⊆ B') : B = B' :=
begin
  refine h.antisymm (diff_eq_empty.mp (eq_empty_iff_forall_not_mem.mpr (λ x hx, _))), 
  obtain ⟨e,he,-⟩ :=  exch _ _ hB' hB _ hx, 
  exact he.2 (h he.1), 
end 

private lemma diff_aux_of_exch {base : set E → Prop} (exch : exchange_property base) 
(hB₁ : base B₁) (hB₂ : base B₂) (hfin : (B₁ \ B₂).finite) :
(B₂ \ B₁).finite ∧ (B₂ \ B₁).ncard = (B₁ \ B₂).ncard :=
begin
  suffices : ∀ {k B B'}, base B → base B' → (B \ B').finite → ncard (B \ B') = k → 
    (B' \ B).finite ∧ (B' \ B).ncard = k, from this hB₁ hB₂ hfin rfl,  
  intro k, induction k with k IH, 
  { intros B B' hB hB' hfin h0, 
    rw [ncard_eq_zero hfin, diff_eq_empty] at h0, 
    rw [antichain_of_exch exch hB hB' h0, diff_self], 
    simp },
  intros B B' hB hB' hfin hcard, 
  obtain ⟨e,he⟩ := nonempty_of_ncard_ne_zero (by { rw hcard, simp } : (B \ B').ncard ≠ 0), 
  obtain ⟨f,hf,hB0⟩ := exch _ _ hB hB' _ he, 
  have hef : f ≠ e, by { rintro rfl, exact hf.2 he.1 }, 
  
  obtain ⟨hfin',hcard'⟩ := IH hB0 hB' _ _,
  { rw [insert_diff_singleton_comm hef, diff_diff_right, 
      inter_singleton_eq_empty.mpr he.2, union_empty, ←union_singleton, ←diff_diff] at hfin' hcard',
    have hfin'' := hfin'.insert f, 
    rw [insert_diff_singleton, insert_eq_of_mem hf] at hfin'', 
    apply_fun (λ x, x+1) at hcard', 
    rw [ncard_diff_singleton_add_one hf hfin'', ←nat.succ_eq_add_one] at hcard', 
    refine ⟨hfin'', hcard'⟩},
  { rw [insert_diff_of_mem _ hf.1, diff_diff_comm], exact hfin.diff _,  },
  rw [insert_diff_of_mem _ hf.1, diff_diff_comm, ncard_diff_singleton_of_mem he hfin, hcard, 
    nat.succ_sub_one], 
end  

private lemma finite_of_finite_of_exch {base : set E → Prop} (exch : exchange_property base) 
(hB : base B) (hB' : base B') (h : B.finite) : 
  B'.finite :=
begin
  rw [←inter_union_diff B' B], 
  exact finite.union (h.subset (inter_subset_right _ _)) 
    (diff_aux_of_exch exch hB hB' (h.diff _)).1, 
end 

private lemma card_eq_card_of_exchange {base : set E → Prop} (exch : exchange_property base)
(hB₁ : base B₁) (hB₂ : base B₂) :
  B₁.ncard = B₂.ncard :=
begin 
  obtain (hB₁' | hB₁') := B₁.finite_or_infinite.symm,
  { rw [hB₁'.ncard, infinite.ncard (λ h, hB₁' (finite_of_finite_of_exch exch hB₂ hB₁ h))] },
  have hdcard := (diff_aux_of_exch exch hB₁ hB₂ (hB₁'.diff _)).2,
  have hB₂' := finite_of_finite_of_exch exch hB₁ hB₂ hB₁', 
  rw [←ncard_inter_add_ncard_diff_eq_ncard B₁ B₂ hB₁', ←hdcard, inter_comm, 
    ncard_inter_add_ncard_diff_eq_ncard B₂ B₁ hB₂'],
end

end prelim

/-- A `matroid` is a nonempty collection of sets satisfying the exchange property and the maximal
  subset property. Each such set is called a `base` of the matroid. -/

@[ext] structure matroid (E : Type*) :=
  (base : set E → Prop)
  (exists_base' : ∃ B, base B)
  (base_exchange' : exchange_property base)
  (maximality : exists_maximal_subset_property (λ I, ∃ B, base B ∧ I ⊆ B))

instance {E : Type*} [finite E] : finite (matroid E) :=
finite.of_injective (λ M, M.base) (λ M₁ M₂ h, (by {ext, dsimp only at h, rw h}))

instance {E : Type*} : nonempty (matroid E) :=
  ⟨⟨ λ B, B = ∅, 
     ⟨_,rfl⟩, 
     λ B B' hB hB' a ha, by { rw hB at ha, exact (not_mem_empty a ha.1).elim }, 
     by { rintro I X ⟨B, rfl, hIB⟩ hI, 
      use ∅, 
      simp only [maximals, exists_eq_left, mem_set_of_eq, and_imp, sep_set_of, 
        empty_subset, and_true, true_and, forall_true_left], 
      exact ⟨hIB, λ b hb _ _, hb⟩ }⟩⟩

namespace matroid

section defs

class finite_rk (M : matroid E) : Prop := (exists_finite_base : ∃ B, M.base B ∧ B.finite) 

/-- A set is independent if it is contained in a base.  -/
def indep (M : matroid E) (I : set E) : Prop :=
  ∃ B, M.base B ∧ I ⊆ B

/-- A basis for a set `X` is a maximal independent subset of `X`
  (Often in the literature, the word 'basis' is used to refer to what we call a 'base'). -/
def basis (M : matroid E) (I X : set E) : Prop :=
  I ∈ maximals (⊆) {A | M.indep A ∧ A ⊆ X}

/-- A circuit is a minimal dependent set -/
def circuit (M : matroid E) (C : set E) : Prop :=
  C ∈ minimals (⊆) {X | ¬M.indep X}

/-- A flat is a maximal set having a given basis  -/
def flat (M : matroid E) (F : set E) : Prop :=
  ∀ ⦃I X⦄, M.basis I F → M.basis I X → X ⊆ F

/-- The closure of a set is the intersection of the flats containing it -/
def cl (M : matroid E) (X : set E) : set E :=
  ⋂₀ {F | M.flat F ∧ X ⊆ F}

/-- A hyperplane is a maximal proper subflat -/
def hyperplane (M : matroid E) (H : set E) : Prop :=
  M.flat H ∧ H ⊂ univ ∧ ∀ ⦃F⦄, H ⊂ F → M.flat F → F = univ

/-- A cocircuit is the complement of a hyperplane -/
def cocircuit (M : matroid E) (K : set E) : Prop :=
  M.hyperplane Kᶜ

/-- A coindependent set is one that is disjoint from some base -/
def coindep (M : matroid E) (I : set E) : Prop :=
  ∃ B, M.base B ∧ disjoint I B

/-- A loop is a member of the closure of the empty set -/
def loop (M : matroid E) (e : E) : Prop :=
  e ∈ M.cl ∅

/-- A `nonloop` is an element that is not a loop -/
def nonloop (M : matroid E) (e : E) : Prop :=
  ¬ M.loop e 

def nonloops (M : matroid E) : set E :=
  {e | M.nonloop e}

/-- A coloop is an element contained in every basis -/
def coloop (M : matroid E) (e : E) : Prop :=
  ∀ ⦃B⦄, M.base B → e ∈ B

class finitary (M : matroid E) : Prop := (cct_finite : ∀ (C : set E), M.circuit C → C.finite) 

end defs

section base

variables {B B' B₁ B₂ I : set E} {M : matroid E} {e f x y : E}

lemma exists_base (M : matroid E) : ∃ B, M.base B := M.exists_base'

lemma base.exchange (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hx : x ∈ B₁ \ B₂) :
  ∃ y ∈ B₂ \ B₁, M.base (insert y (B₁ \ {x}))  :=
M.base_exchange' B₁ B₂ hB₁ hB₂ _ hx

lemma base.exchange_mem (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hxB₁ : x ∈ B₁) (hxB₂ : x ∉ B₂) :
  ∃ y, (y ∈ B₂ ∧ y ∉ B₁) ∧ M.base (insert y (B₁ \ {x})) :=
by simpa using hB₁.exchange hB₂ ⟨hxB₁, hxB₂⟩

lemma base.eq_of_subset_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hB₁B₂ : B₁ ⊆ B₂) :
  B₁ = B₂ :=
antichain_of_exch M.base_exchange' hB₁ hB₂ hB₁B₂

lemma base.finite_of_finite (hB : M.base B) (h : B.finite) (hB' : M.base B') : B'.finite :=
finite_of_finite_of_exch M.base_exchange' hB hB' h

lemma base.infinite_of_infinite (hB : M.base B) (h : B.infinite) (hB₁ : M.base B₁) :
  B₁.infinite :=
by_contra (λ hB_inf, (hB₁.finite_of_finite (not_infinite.mp hB_inf) hB).not_infinite h)

lemma base.finite [finite_rk M] (hB : M.base B) : B.finite := 
let ⟨B₀,hB₀⟩ := ‹finite_rk M›.exists_finite_base in hB₀.1.finite_of_finite hB₀.2 hB

lemma base.finite_rk_of_finite (hB : M.base B) (hfin : B.finite) : finite_rk M := ⟨⟨B, hB, hfin⟩⟩   

instance finite_rk_of_finite [finite E] {M : matroid E} : finite_rk M := 
let ⟨B, hB⟩ := M.exists_base in ⟨⟨B, hB, to_finite _⟩⟩ 

lemma finite_rk_of_finite_base (hB : M.base B) (h : B.finite) : finite_rk M := ⟨⟨B, hB, h⟩⟩ 

instance finitary_of_finite_rk {M : matroid E} [finite_rk M] : finitary M := 
⟨λ C hC, 
begin
  obtain (rfl | ⟨e,heC⟩) := C.eq_empty_or_nonempty, exact finite_empty, 
  have hi : M.indep (C \ {e}), from by_contra (λ h', (hC.2 h' (diff_subset _ _) heC).2 rfl), 
  obtain ⟨B, hB, hCB⟩ := hi, 
  convert (hB.finite.subset hCB).insert e, 
  rw [insert_diff_singleton, insert_eq_of_mem heC],
end ⟩  

lemma base.card_eq_card_of_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) : B₁.ncard = B₂.ncard :=
card_eq_card_of_exchange M.base_exchange' hB₁ hB₂ 

lemma base.diff_finite_comm (hB₁ : M.base B₁) (hB₂ : M.base B₂) :
  (B₁ \ B₂).finite ↔ (B₂ \ B₁).finite := 
⟨λ h, (diff_aux_of_exch M.base_exchange' hB₁ hB₂ h).1, 
  λ h, (diff_aux_of_exch M.base_exchange' hB₂ hB₁ h).1⟩

lemma base.diff_infinite_comm (hB₁ : M.base B₁) (hB₂ : M.base B₂) : 
  (B₁ \ B₂).infinite ↔ (B₂ \ B₁).infinite := 
not_iff_not.mpr (hB₁.diff_finite_comm hB₂)

lemma base.card_diff_eq_card_diff (hB₁ : M.base B₁) (hB₂ : M.base B₂) : 
  (B₁ \ B₂).ncard = (B₂ \ B₁).ncard :=
begin
  obtain (h | h) := (B₁ \ B₂).finite_or_infinite, 
  { rw (diff_aux_of_exch M.base_exchange' hB₁ hB₂ h).2 },
  rw [h.ncard, infinite.ncard (λ h', h (diff_aux_of_exch M.base_exchange' hB₂ hB₁ h').1)], 
end 
  
end base

end matroid 

section from_axioms

/-- A collection of bases with the exchange property and at least one finite member is a matroid -/
def matroid_of_exists_finite_base {E : Type*} (base : set E → Prop) 
  (exists_finite_base : ∃ B, base B ∧ B.finite)
  (base_exchange' : exchange_property base) : 
matroid E := 
{ base := base,
  exists_base' := let ⟨B,h⟩ := exists_finite_base in ⟨B,h.1⟩,
  base_exchange' := base_exchange',
  maximality := 
  begin
    rintro I X ⟨B, hB, hIB⟩ hIX, 
    have hfin : ∀ {B'}, base B' → B'.finite, 
    { obtain ⟨Bfin, hBfin, hfin⟩ := exists_finite_base, 
      exact λ B' hB', finite_of_finite_of_exch base_exchange' hBfin hB' hfin },
    set W := {Y : set E | (λ (I : set E), ∃ (B : set E), base B ∧ I ⊆ B) Y ∧ I ⊆ Y ∧ Y ⊆ X}, 
    
    have hW : ∀ {S : set E}, S ∈ W → S.finite ∧ S.ncard ≤ B.ncard, 
    { rintro S ⟨⟨BS,hBS,hSBS⟩,-⟩,  
      rw [←card_eq_card_of_exchange base_exchange' hBS hB], 
      exact ⟨(hfin hBS).subset hSBS, ncard_le_of_subset hSBS (hfin hBS)⟩},

    have hW' : (ncard '' W).finite, 
    { refine (set.finite_le_nat (B.ncard)).subset _, rintro i ⟨S,hS,rfl⟩, exact (hW hS).2 },

    obtain ⟨n, ⟨S, hS, rfl⟩, h⟩ :=  finite.exists_maximal_wrt id _ hW' 
      (set.nonempty.image _ ⟨I, ⟨⟨B, hB, hIB⟩,subset.rfl, hIX⟩⟩), 
    
    refine ⟨S, hS, λ S' (hS' : S' ∈ W) hSS', _⟩, 
    have hSfin := (hW hS').1, 
    rw eq_of_subset_of_ncard_le hSS' _ hSfin,  
    exact (h _ (mem_image_of_mem _ hS') (ncard_le_of_subset hSS' hSfin)).symm.le,
  end }

@[simp] lemma matroid_of_exists_finite_base_apply {E : Type*} (base : set E → Prop) 
  (exists_finite_base : ∃ B, base B ∧ B.finite) (base_exchange' : exchange_property base) : 
(matroid_of_exists_finite_base base exists_finite_base base_exchange').base = base := rfl 

/-- A matroid constructed with a finite base is `finite_rk` -/
instance {E : Type*} {base : set E → Prop} {exists_finite_base : ∃ B, base B ∧ B.finite} 
{base_exchange' : exchange_property base} : 
  matroid.finite_rk (matroid_of_exists_finite_base base exists_finite_base base_exchange') := 
⟨exists_finite_base⟩  

def matroid_of_base_of_finite {E : Type*} [finite E] (base : set E → Prop)
(exists_base : ∃ B, base B) (base_exchange' : exchange_property base) : matroid E :=
matroid_of_exists_finite_base base (let ⟨B,hB⟩ := exists_base in ⟨B,hB,to_finite _⟩) base_exchange'

@[simp] lemma matroid_of_base_of_finite_apply {E : Type*} [finite E] (base : set E → Prop) 
(exists_base : ∃ B, base B) (base_exchange' : exchange_property base) : 
(matroid_of_base_of_finite base exists_base base_exchange').base = base := rfl 

/-- A version of the independence axioms that avoids cardinality -/
def matroid_of_indep {E : Type*} (indep : set E → Prop) (h_empty : indep ∅) 
(h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I) 
(h_aug : ∀⦃I B⦄, indep I → I ∉ maximals (⊆) indep → B ∈ maximals (⊆) indep → 
  ∃ x ∈ B \ I, indep (insert x I))
(h_maximal : exists_maximal_subset_property indep) : matroid E :=
{ base := λ B, B ∈ maximals (⊆) indep,
  exists_base' := 
  begin
    obtain ⟨B, ⟨hB,-,-⟩, hB₁⟩ :=  h_maximal ∅ univ h_empty (subset_univ _),  
    exact ⟨B, ⟨hB,λ B' hB' hBB', hB₁ ⟨hB', empty_subset _,subset_univ _⟩ hBB'⟩⟩,  
  end,
  base_exchange' := 
  begin
    rintros B B' ⟨hB,hBmax⟩ ⟨hB',hB'max⟩ e he, 
    obtain ⟨f,hf,hfB⟩ :=  h_aug (h_subset hB (diff_subset B {e})) _ ⟨hB',hB'max⟩, 
    simp only [mem_diff, mem_singleton_iff, not_and, not_not] at hf, 
    have hfB' : f ∉ B, 
    { intro hfB, have := hf.2 hfB, subst this, exact he.2 hf.1 }, 
    { refine ⟨f, ⟨hf.1, hfB'⟩, by_contra (λ hnot, _)⟩,
      obtain ⟨x,hxB, hind⟩ :=  h_aug hfB hnot ⟨hB, hBmax⟩, 
      simp only [mem_diff, mem_insert_iff, mem_singleton_iff, not_or_distrib, not_and, not_not] 
        at hxB, 
      have := hxB.2.2 hxB.1, subst this, 
      rw [insert_comm, insert_diff_singleton, insert_eq_of_mem he.1] at hind, 
      exact not_mem_subset (hBmax hind (subset_insert _ _)) hfB' (mem_insert _ _) },
    simp only [maximals, mem_sep_iff, diff_singleton_subset_iff, not_and, not_forall, exists_prop],
    exact λ _, ⟨B, hB, subset_insert _ _, λ hss, (hss he.1).2 rfl⟩, 
  end,
  maximality := 
  begin
    rintro I X ⟨B, hB,  hIB⟩ hIX, 
    obtain ⟨J, ⟨hJ, hIJ, hJX⟩, hJmax⟩ := h_maximal I X (h_subset hB.1 hIB) hIX, 
    obtain ⟨BJ, hBJ⟩ := h_maximal J univ hJ (subset_univ _), 
    refine ⟨J, ⟨⟨BJ,_, hBJ.1.2.1⟩ ,hIJ,hJX⟩, _⟩,  
    { exact ⟨hBJ.1.1, λ B' hB' hBJB', hBJ.2 ⟨hB',hBJ.1.2.1.trans hBJB', subset_univ _⟩ hBJB'⟩ },
    simp only [mem_set_of_eq, and_imp, forall_exists_index], 
    refine λ  A B' hB' hAB' hIA hAX hJA, hJmax ⟨h_subset hB'.1 hAB',hIA,hAX⟩ hJA, 
  end  }

@[simp] lemma matroid_of_indep_apply {E : Type*} (indep : set E → Prop) (h_empty : indep ∅) 
(h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I) 
(h_aug : ∀⦃I B⦄, indep I → I ∉ maximals (⊆) indep → B ∈ maximals (⊆) indep → 
  ∃ x ∈ B \ I, indep (insert x I))
(h_maximal : exists_maximal_subset_property indep) : 
(matroid_of_indep indep h_empty h_subset h_aug h_maximal).indep = indep :=
begin
  ext I, 
  simp only [matroid.indep, matroid_of_indep], 
  refine ⟨λ ⟨B, hB, hIB⟩, h_subset hB.1 hIB, λ hI, _⟩, 
  obtain ⟨B, ⟨hB, hIB, -⟩, hBmax⟩ :=  h_maximal I univ hI (subset_univ _), 
  exact ⟨B, ⟨hB, λ B' hB' hBB', hBmax ⟨hB', hIB.trans hBB', subset_univ _⟩ hBB'⟩, hIB⟩, 
end 

end from_axioms 


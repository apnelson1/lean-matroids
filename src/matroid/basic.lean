import mathlib.ncard
import mathlib.data.set.finite
import order.minimal 

-- noncomputable theory
open_locale classical
open_locale big_operators

open set

variables {E : Type*}

/-- A predicate `P` on sets satisfies the exchange property if, for all `X` and `Y` satisfying `P`
  and all `a ∈ X \ Y`, there exists `b ∈ Y \ X` so that swapping `a` for `b` in `X` maintains `P`.-/
def exchange_property (P : set E → Prop) : Prop :=
  ∀ X Y, P X → P Y → ∀ a ∈ X \ Y, ∃ b ∈ Y \ X, P (insert b (X \ {a}))

def exists_maximal_subset_property (P : set E → Prop) : Prop := 
  ∀ I X, P I → I ⊆ X → (maximals (⊆) {Y | P Y ∧ I ⊆ Y ∧ Y ⊆ X}).nonempty 

lemma antichain_of_exch {base : set E → Prop} (exch : exchange_property base) {B B' : set E} 
(hB : base B) (hB' : base B') (h : B ⊆ B') : B = B' :=
begin
  refine h.antisymm (diff_eq_empty.mp (eq_empty_iff_forall_not_mem.mpr (λ x hx, _))), 
  obtain ⟨e,he,-⟩ :=  exch _ _ hB' hB _ hx, 
  exact he.2 (h he.1), 
end 

lemma finite_of_finite_of_exch {B B' : set E} {base : set E → Prop} (exch : exchange_property base) 
(hB : base B) (h : B.finite) (hB' : base B') : 
  B'.finite :=
begin
  suffices h_win : ∀ (X ⊆ B) (B' : set E), B \ B' ⊆ X → base B' → B'.finite,   
    from h_win _ (diff_subset _ _) _ subset.rfl hB', 
  clear hB' B', 
  
  refine λ X hX, (h.subset hX).strong_induction_on (λ Y hYX hY B' hBB' hB', _),
  obtain (rfl | hne) := Y.eq_empty_or_nonempty, 
  { rw [diff_subset_iff, union_empty] at hBB', 
    rwa ←antichain_of_exch exch hB hB' hBB' },
  by_contra' h_inf, 
  rw [←not_infinite, not_not] at h_inf, 
  obtain ⟨f,hf⟩ := (h_inf.diff h).nonempty, 
  obtain ⟨e,heBB', hB₀⟩ := exch _ _ hB' hB _ hf, 

  refine ((hY _ _ _ subset.rfl hB₀).subset (subset_insert _ _)).not_infinite  
    (h_inf.diff (set.to_finite {f})), 
  refine ssubset_of_subset_of_ne (subset_trans _ hBB') _, 
  { nth_rewrite 0 ←inter_union_diff B B',  
    rw [diff_subset_iff],
    refine union_subset_union_left _ (subset_trans _ (subset_insert _ _)), 
    exact subset_diff_singleton (inter_subset_right _ _) 
      (not_mem_subset (inter_subset_left _ _) hf.2) },
  rintro rfl, 
  exact (hBB' heBB').2 (mem_insert _ _), 
end 

lemma card_eq_card_of_exchange {B₁ B₂ : set E} {base : set E → Prop} (exch : exchange_property base)
(hB₁ : base B₁) (hB₂ : base B₂) :
  B₁.ncard = B₂.ncard :=
begin 
  obtain (h_fin | h_inf) := B₁.finite_or_infinite, 
  
  { suffices h_win : ∀ (X ⊆ B₁) (B' : set E), B₁ \ B' ⊆ X → base B' → B₁.ncard = B'.ncard,   
    from h_win _ (diff_subset _ _) _ subset.rfl hB₂, 
    refine λ X hX, (h_fin.subset hX).strong_induction_on (λ Y hYX hY B' hBB' hB', _),
    
    obtain (h_empt | ⟨f, hf⟩) := (B' \ B₁).eq_empty_or_nonempty, 
    { rw antichain_of_exch exch hB' hB₁ (diff_eq_empty.mp h_empt) }, 
      
    obtain ⟨e,he,hB₀⟩ := exch _ _ hB' hB₁ _ hf, 

    rw [hY _ (ssubset_of_ne_of_subset _ (subset_trans _ hBB')) _ subset.rfl hB₀, 
      ncard_exchange he.2 hf.1], 
    { rintro rfl, exact (hBB' he).2 (mem_insert _ _) },
    nth_rewrite 0 ←inter_union_diff B₁ B', 
    rw [diff_subset_iff], 
    refine union_subset_union_left _ (subset_trans _ (subset_insert _ _)), 
    exact subset_diff_singleton (inter_subset_right _ _) 
        (not_mem_subset (inter_subset_left _ _) hf.2) },
    rw [h_inf.ncard, set.infinite.ncard], 
    by_contra h_fin', 
    exact (finite_of_finite_of_exch exch hB₂ (not_infinite.mp h_fin') hB₁).not_infinite h_inf, 
end


/-- A `matroid` is a nonempty collection of sets satisfying the exchange property. Each such set
  is called a `base` of the matroid. -/

@[ext] structure matroid (E : Type*) :=
  (base : set E → Prop)
  (exists_base' : ∃ B, base B)
  (base_exchange' : exchange_property base)
  (maximality : exists_maximal_subset_property (λ I, ∃ B, base B ∧ I ⊆ B))

instance {E : Type*} [finite E] :
  finite (matroid E) :=
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
/- None of these definitions require finiteness -/

section defs

class finite_rk (M : matroid E) : Prop := (exists_finite_base : ∃ B, M.base B ∧ B.finite) 

/-- A set is independent if it is contained in a base.  -/
def indep (M : matroid E) (I : set E) : Prop :=
  ∃ B, M.base B ∧ I ⊆ B

/-- A basis for a set `X` is a maximal independent subset of `X`
  (Often in the literature, the word 'basis' is used to refer to what we call a 'base')-/
def basis (M : matroid E) (I X : set E) : Prop :=
  M.indep I ∧ I ⊆ X ∧ ∀ J, M.indep J → I ⊆ J → J ⊆ X → I = J

/-- A circuit is a minimal dependent set -/
def circuit (M : matroid E) (C : set E) : Prop :=
  ¬M.indep C ∧ ∀ I ⊂ C, M.indep I

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

/-- A coindependent set is one that contains no cocircuit -/
def coindep (M : matroid E) (I : set E) : Prop :=
  ∀ ⦃K⦄, K ⊆ I → ¬ M.cocircuit K

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
finite_of_finite_of_exch M.base_exchange' hB h hB' 

lemma base.infinite_of_infinite (hB : M.base B) (h : B.infinite) (hB₁ : M.base B₁) :
  B₁.infinite :=
by_contra (λ hB_inf, (hB₁.finite_of_finite (not_infinite.mp hB_inf) hB).not_infinite h)

lemma base.finite [finite_rk M] (hB : M.base B) : B.finite := 
let ⟨B₀,hB₀⟩ := ‹finite_rk M›.exists_finite_base in hB₀.1.finite_of_finite hB₀.2 hB

instance finite_rk_of_finite [finite E] {M : matroid E} : finite_rk M := 
let ⟨B, hB⟩ := M.exists_base in ⟨⟨B, hB, to_finite _⟩⟩ 

lemma finite_rk_of_finite_base (hB : M.base B) (h : B.finite) : finite_rk M := ⟨⟨B, hB, h⟩⟩   

lemma base.card_eq_card_of_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) : B₁.ncard = B₂.ncard :=
card_eq_card_of_exchange M.base_exchange' hB₁ hB₂ 

end base

section of_finite_rk 

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
      exact λ B' hB', finite_of_finite_of_exch base_exchange' hBfin hfin hB' },
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
  finite_rk (matroid_of_exists_finite_base base exists_finite_base base_exchange') := 
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

end of_finite_rk 

variables {I B B' X B₁ B₂ : set E} {M : matroid E}

lemma indep.exists_insert_of_not_base (hI : M.indep I) (hI' : ¬M.base I) (hB : M.base B) : 
  ∃ e ∈ B \ I, M.indep (insert e I) :=
begin
  obtain ⟨B', hB', hIB'⟩ := hI, 
  obtain ⟨x, hxB', hx⟩ := exists_of_ssubset (hIB'.ssubset_of_ne (by { rintro rfl, exact hI' hB' })), 
  obtain (hxB | hxB) := em (x ∈ B), 
  { exact ⟨x, ⟨hxB, hx⟩ , ⟨B', hB', insert_subset.mpr ⟨hxB',hIB'⟩⟩⟩ },
  obtain ⟨e,he, hbase⟩ := hB'.exchange hB ⟨hxB',hxB⟩,    
  exact ⟨e, ⟨he.1, not_mem_subset hIB' he.2⟩, 
    ⟨_, hbase, insert_subset_insert (subset_diff_singleton hIB' hx)⟩⟩,  
end  

-- lemma indep 

def dual (M : matroid E) : matroid E := 
matroid_of_indep (λ I, ∃ B, M.base B ∧ disjoint I B) 
(M.exists_base.imp (λ B hB, ⟨hB, empty_disjoint B⟩))
(λ I J ⟨B, hB, hJB⟩ hIJ, ⟨B, hB, disjoint_of_subset_left hIJ hJB⟩) 
(begin
  rintro I B' ⟨B, hB, hIB⟩ hI hB',   
  -- have := M.maximality (B' \ I) (B' \ I ∪ B) ⟨B', hB', _⟩, 
end) 
 sorry 



end matroid

-- lemma ind_aug {I B : set E} ()

-- TODO : prove strong basis exchange (and hence define duality) in this file.

-- lemma base.indep (hB : M.base B) :
--   M.indep B :=
-- sorry

-- lemma base.insert_dep (hB : M.base B) (h : e ∉ B) :
--   ¬M.indep (insert e B) := sorry

-- lemma base_iff_maximal_indep :
--   M.base B ↔ M.indep B ∧ ∀ I, M.indep I → B ⊆ I → B = I :=
-- sorry

-- lemma indep.unique_circuit_of_insert {e : E} (hI : M.indep I) (hI' : ¬M.indep (insert e I)) :
--   ∃! C, C ⊆ insert e I ∧ M.circuit C ∧ e ∈ C := sorry

-- lemma subset_cl (M : matroid E) (X : set E) :
--   X ⊆ M.cl X := sorry

-- -- lemma base_iff_indep_card :
-- --   M.base B ↔ M.indep B ∧ B.ncard =

import mathlib.ncard
import mathlib.data.set.finite
import order.minimal 

open_locale classical
open_locale big_operators

open set

variables {E : Type*} {I J B B' B₁ B₂ X Y : set E} {e f : E}

section prelim 

/-- A predicate `P` on sets satisfies the exchange property if, for all `X` and `Y` satisfying `P`
  and all `a ∈ X \ Y`, there exists `b ∈ Y \ X` so that swapping `a` for `b` in `X` maintains `P`.-/
def exchange_property (P : set E → Prop) : Prop :=
  ∀ X Y, P X → P Y → ∀ a ∈ X \ Y, ∃ b ∈ Y \ X, P (insert b (X \ {a}))

/-- A predicate `P` on sets satisfies the maximal subset property if, for all `X` containing some 
  `I` satisfying `P`, there is a maximal subset of `X` satisfying `P`. -/
def exists_maximal_subset_property (P : set E → Prop) : Prop := 
  ∀ I X, P I → I ⊆ X → (maximals (⊆) {Y | P Y ∧ I ⊆ Y ∧ Y ⊆ X}).nonempty 

lemma exists_maximal_subset_property_of_bounded {P : set E → Prop} 
(h : ∃ n, ∀ I, P I → (I.finite ∧ I.ncard ≤ n)) : 
  exists_maximal_subset_property P :=
begin
  obtain ⟨n,h⟩ := h, 
  intros I₀ X hI₀ hI₀X,
  set S := {I | P I ∧ I₀ ⊆ I ∧ I ⊆ X} with hS,
  haveI : nonempty S, from ⟨⟨I₀, hI₀, subset.rfl, hI₀X⟩⟩,  
  set f : {I | P I ∧ I₀ ⊆ I ∧ I ⊆ X} → fin (n+1) := 
    λ I, ⟨ncard (I : set E), nat.lt_succ_of_le (h I I.2.1).2⟩ with hf,
  
  obtain ⟨m, ⟨⟨J,hJ⟩,rfl⟩, hJmax⟩ :=  set.finite.exists_maximal (range f) (range_nonempty _),
  refine ⟨J, hJ, λ K hK hJK, (eq_of_subset_of_ncard_le hJK _ (h _ hK.1).1).symm.subset⟩,
  exact (hJmax _ ⟨⟨K,hK⟩, rfl⟩ (ncard_le_of_subset hJK (h _ hK.1).1)).symm.le,  
end 

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
finite.of_injective (λ M, M.base) (λ M₁ M₂ h, (by { ext, dsimp only at h, rw h }))

instance {E : Type*} : nonempty (matroid E) :=
  ⟨⟨@eq (set E) ∅, ⟨_,rfl⟩, by { rintro _ _ rfl rfl a h, exfalso, exact not_mem_empty a h.1 }, 
    exists_maximal_subset_property_of_bounded 
    ⟨0, by { rintro I ⟨B, rfl, hIB⟩, rw subset_empty_iff.mp hIB, simp }⟩⟩⟩

namespace matroid

section defs

/-- A set is independent if it is contained in a base.  -/
def indep (M : matroid E) (I : set E) : Prop := ∃ B, M.base B ∧ I ⊆ B

/-- A basis for a set `X` is a maximal independent subset of `X`
  (Often in the literature, the word 'basis' is used to refer to what we call a 'base'). -/
def basis (M : matroid E) (I X : set E) : Prop := I ∈ maximals (⊆) {A | M.indep A ∧ A ⊆ X}

/-- A circuit is a minimal dependent set -/
def circuit (M : matroid E) (C : set E) : Prop := C ∈ minimals (⊆) {X | ¬M.indep X}

/-- A coindependent set is one that is disjoint from some base -/
def coindep (M : matroid E) (I : set E) : Prop := ∃ B, M.base B ∧ disjoint I B


class finite_rk (M : matroid E) : Prop := (exists_finite_base : ∃ B, M.base B ∧ B.finite) 

class infinite_rk (M : matroid E) : Prop := (exists_infinite_base : ∃ B, M.base B ∧ B.infinite)

class finitary (M : matroid E) : Prop := (cct_finite : ∀ (C : set E), M.circuit C → C.finite) 

end defs

variables {M : matroid E}

section base

lemma exists_base (M : matroid E) : ∃ B, M.base B := M.exists_base'

lemma base.exchange (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hx : e ∈ B₁ \ B₂) :
  ∃ y ∈ B₂ \ B₁, M.base (insert y (B₁ \ {e}))  :=
M.base_exchange' B₁ B₂ hB₁ hB₂ _ hx

lemma base.exchange_mem (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hxB₁ : e ∈ B₁) (hxB₂ : e ∉ B₂) :
  ∃ y, (y ∈ B₂ ∧ y ∉ B₁) ∧ M.base (insert y (B₁ \ {e})) :=
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

lemma base.infinite [infinite_rk M] (hB : M.base B) : B.infinite :=
let ⟨B₀,hB₀⟩ := ‹infinite_rk M›.exists_infinite_base in hB₀.1.infinite_of_infinite hB₀.2 hB

lemma base.finite_rk_of_finite (hB : M.base B) (hfin : B.finite) : finite_rk M := ⟨⟨B, hB, hfin⟩⟩   

lemma base.infinite_rk_of_infinite (hB : M.base B) (h : B.infinite) : infinite_rk M := ⟨⟨B, hB, h⟩⟩ 

lemma not_finite_rk (M : matroid E) [infinite_rk M] : ¬ finite_rk M := 
by { introI h, obtain ⟨B,hB⟩ := M.exists_base, exact hB.infinite hB.finite }

lemma not_infinite_rk (M : matroid E) [finite_rk M] : ¬ infinite_rk M := 
by { introI h, obtain ⟨B,hB⟩ := M.exists_base, exact hB.infinite hB.finite }

lemma finite_or_infinite_rk (M : matroid E) : finite_rk M ∨ infinite_rk M :=
let ⟨B, hB⟩ := M.exists_base in B.finite_or_infinite.elim 
  (or.inl ∘ hB.finite_rk_of_finite) (or.inr ∘ hB.infinite_rk_of_infinite)

instance finite_rk_of_finite [finite E] {M : matroid E} : finite_rk M := 
let ⟨B, hB⟩ := M.exists_base in ⟨⟨B, hB, to_finite _⟩⟩ 

instance finitary_of_finite_rk {M : matroid E} [finite_rk M] : finitary M := 
⟨ begin
  intros C hC, 
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

section indep

lemma indep_iff_subset_base : M.indep I ↔ ∃ B, M.base B ∧ I ⊆ B := iff.rfl

lemma indep_mono {M : matroid E} {I J : set E} (hIJ : I ⊆ J) (hJ : M.indep J) : M.indep I :=
by {obtain ⟨B, hB, hJB⟩ := hJ, exact ⟨B, hB, hIJ.trans hJB⟩}

lemma indep.exists_base_supset (hI : M.indep I) : ∃ B, M.base B ∧ I ⊆ B := hI

lemma indep.subset (hJ : M.indep J) (hIJ : I ⊆ J) : M.indep I :=
by {obtain ⟨B, hB, hJB⟩ := hJ, exact ⟨B, hB, hIJ.trans hJB⟩}

@[simp] lemma empty_indep (M : matroid E) : M.indep ∅ :=
exists.elim M.exists_base (λ B hB, ⟨_, hB, B.empty_subset⟩)

lemma indep.finite [finite_rk M] (hI : M.indep I) : I.finite := 
let ⟨B, hB, hIB⟩ := hI in hB.finite.subset hIB  

lemma indep.inter_right (hI : M.indep I) (X : set E) : M.indep (I ∩ X) :=
hI.subset (inter_subset_left _ _)

lemma indep.inter_left (hI : M.indep I) (X : set E) : M.indep (X ∩ I) :=
hI.subset (inter_subset_right _ _)

lemma indep.diff (hI : M.indep I) (X : set E) : M.indep (I \ X) := hI.subset (diff_subset _ _)

lemma base.indep (hB : M.base B) : M.indep B := ⟨B, hB, subset_rfl⟩

lemma base.eq_of_subset_indep (hB : M.base B) (hI : M.indep I) (hBI : B ⊆ I) : B = I :=
begin
  obtain ⟨B', hB', hB'I⟩ := hI, 
  exact hBI.antisymm (by rwa hB.eq_of_subset_base hB' (hBI.trans hB'I)), 
end

lemma base_iff_maximal_indep : M.base B ↔ M.indep B ∧ ∀ I, M.indep I → B ⊆ I → B = I :=
begin
  refine ⟨λ h, ⟨h.indep, λ _, h.eq_of_subset_indep ⟩,λ h, _⟩,
  obtain ⟨⟨B', hB', hBB'⟩, h⟩ := h,
  rwa h _ hB'.indep hBB',
end

lemma base_iff_mem_maximals : M.base B ↔ B ∈ maximals (⊆) {I | M.indep I} := 
begin
  rw [base_iff_maximal_indep, maximals], 
  exact ⟨λ h, ⟨h.1,λ I hI hBI, (h.2 I hI hBI).symm.subset⟩,
    λ h, ⟨h.1, λ I hI hBI, hBI.antisymm (h.2 hI hBI)⟩⟩,  
end  

lemma indep.base_of_maximal (hI : M.indep I) (h : ∀ J, M.indep J → I ⊆ J → I = J) : M.base I := 
base_iff_maximal_indep.mpr ⟨hI,h⟩

lemma base.dep_of_ssubset (hB : M.base B) (h : B ⊂ X) : ¬M.indep X :=
λ hX, h.ne (hB.eq_of_subset_indep hX h.subset)

lemma base.dep_of_insert (hB : M.base B) (he : e ∉ B) : ¬M.indep (insert e B) :=
hB.dep_of_ssubset (ssubset_insert he)

lemma base.exchange_base_of_indep (hB : M.base B) (he : e ∈ B) (hf : f ∉ B)
(hI : M.indep (insert f (B \ {e}))) :
  M.base (insert f (B \ {e})) :=
begin
  obtain ⟨B', hB', hIB'⟩ := hI,
  have hBeB' := (subset_insert _ _).trans hIB',
  have heB' : e ∉ B',
  { intro heB',
    have hBB' : B ⊆ B',
    { refine subset_trans _ (insert_subset.mpr ⟨heB',hIB'⟩),
      rw [insert_comm, insert_diff_singleton],
      refine (subset_insert _ _).trans (subset_insert _ _)},
    rw ←hB.eq_of_subset_indep hB'.indep hBB' at hIB',
    exact hf (hIB' (mem_insert _ _))},
  obtain ⟨y,hy,hy'⟩ := hB.exchange hB' ⟨he,heB'⟩,
  rw ←hy'.eq_of_subset_base hB' (insert_subset.mpr ⟨hy.1, hBeB'⟩) at hIB',
  have : f = y,
  { exact (mem_insert_iff.mp (hIB' (mem_insert _ _))).elim id
      (λ h', (hf (diff_subset _ _ h')).elim)},
  rwa this,
end

lemma base.exchange_base_of_indep' (hB : M.base B) (he : e ∈ B) (hf : f ∉ B) 
(hI : M.indep (insert f B \ {e})) : 
  M.base (insert f B \ {e}) := 
begin
  have hfe : f ≠ e, { rintro rfl, exact hf he }, 
  rw [←insert_diff_singleton_comm hfe] at *, 
  exact hB.exchange_base_of_indep he hf hI, 
end 

/-- If the difference of two bases is a singleton, then they differ by an insertion/removal -/
lemma base.eq_exchange_of_diff_eq_singleton (hI : M.base B) (hJ : M.base B') (h : B \ B' = {e}) : 
  ∃ f ∈ B' \ B, B' = (insert f B) \ {e} :=
begin
  have hcard := hJ.card_diff_eq_card_diff hI, 
  rw [h, ncard_singleton, ncard_eq_one] at hcard, 
  obtain ⟨f, hf⟩ := hcard, 
  refine ⟨f, _, _⟩, 
  { rw [←singleton_subset_iff], exact hf.symm.subset },
  rw [←inter_union_diff B' B, hf, union_singleton],  
  nth_rewrite 1 [←inter_union_diff B B'], 
  rw [h, union_singleton, insert_comm], 
  simp only [insert_diff_of_mem, mem_singleton],
  rw [inter_comm, diff_singleton_eq_self], 
  rintro (rfl | ⟨-,heJ⟩),
  { exact (hf.symm.subset rfl).2 (h.symm.subset rfl).1 },
  exact (h.symm.subset rfl).2 heJ, 
end  

lemma basis.indep (hI : M.basis I X) : M.indep I := hI.1.1

lemma basis.subset (hI : M.basis I X) : I ⊆ X := hI.1.2

lemma basis.eq_of_subset_indep (hI : M.basis I X) (hJ : M.indep J) (hIJ : I ⊆ J) (hJX : J ⊆ X) :
  I = J :=
hIJ.antisymm (hI.2 ⟨hJ, hJX⟩ hIJ)

lemma basis.finite (hI : M.basis I X) [finite_rk M] : I.finite := hI.indep.finite 

lemma basis_iff : M.basis I X ↔ M.indep I ∧ I ⊆ X ∧ ∀ J, M.indep J → I ⊆ J → J ⊆ X → I = J :=
⟨λ h, ⟨h.indep, h.subset, λ _, h.eq_of_subset_indep⟩, 
  λ h, ⟨⟨h.1,h.2.1⟩, λ J hJ hIJ, (h.2.2 _ hJ.1 hIJ hJ.2).symm.subset⟩⟩ 

lemma indep.basis_of_maximal_subset (hI : M.indep I) (hIX : I ⊆ X) 
(hmax : ∀ ⦃J⦄, M.indep J → I ⊆ J → J ⊆ X → J ⊆ I) : M.basis I X :=
⟨⟨hI, hIX⟩, λ J hJ hIJ, hmax hJ.1 hIJ hJ.2⟩

@[simp] lemma basis_empty_iff (M : matroid E) :
  M.basis I ∅ ↔ I = ∅ :=
begin
  refine ⟨λ h, subset_empty_iff.mp h.subset, _⟩,
  rintro rfl,
  exact ⟨⟨M.empty_indep, empty_subset _⟩, λ J h h', h.2⟩, 
end

lemma basis.basis_subset (hI : M.basis I X) (hIY : I ⊆ Y) (hYX : Y ⊆ X) : M.basis I Y :=
⟨⟨hI.indep, hIY⟩, λ J hJ hIJ, hI.2 ⟨hJ.1, hJ.2.trans hYX⟩ hIJ⟩

lemma basis.dep_of_ssubset (hI : M.basis I X) {Y : set E} (hIY : I ⊂ Y) (hYX : Y ⊆ X) :
  ¬ M.indep Y :=
λ hY, hIY.ne (hI.eq_of_subset_indep hY hIY.subset hYX)

lemma basis.insert_dep (hI : M.basis I X) (he : e ∈ X \ I) : ¬M.indep (insert e I) :=
hI.dep_of_ssubset (ssubset_insert he.2) (insert_subset.mpr ⟨he.1,hI.subset⟩)

lemma basis.mem_of_insert_indep (hI : M.basis I X) (he : e ∈ X) (hIe : M.indep (insert e I)) : 
  e ∈ I :=
by_contra (λ heI, hI.insert_dep ⟨he, heI⟩ hIe) 

lemma basis.not_basis_of_ssubset (hI : M.basis I X) (hJI : J ⊂ I) : ¬ M.basis J X :=
λ h, hJI.ne (h.eq_of_subset_indep hI.indep hJI.subset hI.subset)

lemma indep.subset_basis_of_subset (hI : M.indep I) (hIX : I ⊆ X) : ∃ J, I ⊆ J ∧ M.basis J X :=
begin
  obtain ⟨J, ⟨(hJ : M.indep J),hIJ,hJX⟩, hJmax⟩ := M.maximality I X hI hIX, 
  exact ⟨J, hIJ, ⟨⟨hJ, hJX⟩,λ K hK hJK, hJmax ⟨hK.1,hIJ.trans hJK,hK.2⟩ hJK⟩⟩,
end

lemma indep.eq_of_basis (hI : M.indep I) (hJ : M.basis J I) : J = I :=
hJ.eq_of_subset_indep hI hJ.subset subset.rfl

lemma indep.basis_self (hI : M.indep I) : M.basis I I := ⟨⟨hI, rfl.subset⟩, λ J hJ _, hJ.2⟩

@[simp] lemma basis_self_iff_indep : M.basis I I ↔ M.indep I := ⟨basis.indep, indep.basis_self⟩

lemma exists_basis (M : matroid E) (X : set E) : ∃ I, M.basis I X :=
by {obtain ⟨I, -, hI⟩ := M.empty_indep.subset_basis_of_subset (empty_subset X), exact ⟨_,hI⟩, }

lemma basis.exists_base (hI : M.basis I X) : ∃ B, M.base B ∧ I = B ∩ X :=
begin
  obtain ⟨B,hB, hIB⟩ := hI.indep,
  refine ⟨B, hB, subset_antisymm (subset_inter hIB hI.subset) _⟩,
  rw hI.eq_of_subset_indep (hB.indep.inter_right X) (subset_inter hIB hI.subset)
    (inter_subset_right _ _),
end

lemma base_iff_basis_univ : M.base B ↔ M.basis B univ :=
by {rw [base_iff_maximal_indep, basis_iff], simp}

lemma base.basis_univ (hB : M.base B) : M.basis B univ := base_iff_basis_univ.mp hB

lemma indep.basis_of_forall_insert (hI : M.indep I) (hIX : I ⊆ X) 
(he : ∀ e ∈ X \ I, ¬ M.indep (insert e I)) : M.basis I X :=
⟨⟨hI, hIX⟩, λ J hJ hIJ e heJ, (by_contra (λ heI, he _ ⟨hJ.2 heJ,heI⟩ 
  (hJ.1.subset (insert_subset.mpr ⟨heJ, hIJ⟩))))⟩  

lemma basis.Union_basis_Union {ι : Type*} (X I : ι → set E) (hI : ∀ i, M.basis (I i) (X i)) 
(h_ind : M.indep (⋃ i, I i)) : M.basis (⋃ i, I i) (⋃ i, X i) :=
begin
  refine h_ind.basis_of_forall_insert 
    (Union_subset_iff.mpr (λ i, (hI i).subset.trans (subset_Union _ _))) (λ e he hi, _), 
  simp only [mem_diff, mem_Union, not_exists] at he, 
  obtain ⟨i, heXi⟩ := he.1, 
  exact he.2 i ((hI i).mem_of_insert_indep heXi 
    (hi.subset (insert_subset_insert (subset_Union _ _)))), 
end 

lemma basis.basis_Union {ι : Type*} [nonempty ι] (X : ι → set E) (hI : ∀ i, M.basis I (X i)) : 
  M.basis I (⋃ i, X i) :=
begin
  convert basis.Union_basis_Union X (λ _, I) (λ i, hI i) _, 
  all_goals { rw Union_const },
  exact (hI (‹nonempty ι›.some)).indep, 
end 

lemma basis.union_basis_union (hIX : M.basis I X) (hJY : M.basis J Y) (h : M.indep (I ∪ J)) : 
  M.basis (I ∪ J) (X ∪ Y) :=
begin 
  rw [union_eq_Union, union_eq_Union], 
  refine basis.Union_basis_Union _ _ _ _,   
  { simp only [bool.forall_bool, bool.cond_ff, bool.cond_tt], exact ⟨hJY, hIX⟩ }, 
  rwa [←union_eq_Union], 
end 

lemma basis.basis_union (hIX : M.basis I X) (hIY : M.basis I Y) : M.basis I (X ∪ Y) :=
by { convert hIX.union_basis_union hIY _; rw union_self, exact hIX.indep }

lemma basis.basis_union_of_subset (hI : M.basis I X) (hJ : M.indep J) (hIJ : I ⊆ J) : 
  M.basis J (J ∪ X) :=
begin
  convert hJ.basis_self.union_basis_union hI (by rwa union_eq_left_iff_subset.mpr hIJ), 
  rw union_eq_left_iff_subset.mpr hIJ, 
end 

lemma basis.insert_basis_insert (hI : M.basis I X) (h : M.indep (insert e I)) : 
  M.basis (insert e I) (insert e X) :=
begin
  convert hI.union_basis_union 
    (indep.basis_self (h.subset (singleton_subset_iff.mpr (mem_insert _ _)))) _, 
  simp, simp, simpa, 
end 

lemma base.insert_dep (hB : M.base B) (h : e ∉ B) : ¬ M.indep (insert e B) :=
  λ h', (insert_ne_self.mpr h).symm ((base_iff_maximal_indep.mp hB).2 _ h' (subset_insert _ _))

lemma base.ssubset_dep (hB : M.base B) (h : B ⊂ X) : ¬ M.indep X :=
  λ h', h.ne ((base_iff_maximal_indep.mp hB).2 _ h' h.subset)

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

lemma base.exists_insert_of_ssubset (hB : M.base B) (hIB : I ⊂ B) (hB' : M.base B') : 
  ∃ e ∈ B' \ I, M.indep (insert e I) :=
(hB.indep.subset hIB.subset).exists_insert_of_not_base 
    (λ hI, hIB.ne (hI.eq_of_subset_base hB hIB.subset)) hB'

lemma base.base_of_basis_supset (hB : M.base B) (hBX : B ⊆ X) (hIX : M.basis I X) : M.base I :=
begin
  by_contra h, 
  obtain ⟨e,heBI,he⟩ := hIX.indep.exists_insert_of_not_base h hB, 
  exact heBI.2 (hIX.mem_of_insert_indep (hBX heBI.1) he), 
end 

lemma base.basis_of_subset (hB : M.base B) (hBX : B ⊆ X) : M.basis B X :=
⟨⟨hB.indep, hBX⟩, λ J hJ hBJ, by rw hB.eq_of_subset_indep hJ.1 hBJ⟩

lemma indep.exists_base_subset_union_base (hI : M.indep I) (hB : M.base B) : 
  ∃ B', M.base B' ∧ I ⊆ B' ∧ B' ⊆ I ∪ B :=
begin
  obtain ⟨B', hIB', hB'⟩ := hI.subset_basis_of_subset (subset_union_left I B), 
  exact ⟨B', hB.base_of_basis_supset (subset_union_right _ _) hB', hIB', hB'.subset⟩, 
end  

lemma eq_of_indep_iff_indep_forall {M₁ M₂ : matroid E} (h : ∀ I, (M₁.indep I ↔ M₂.indep I)) :
  M₁ = M₂ :=
begin
  ext B,
  have hI : M₁.indep = M₂.indep, by { ext ,apply h},
  simp_rw [base_iff_maximal_indep, hI],
end

lemma eq_iff_indep_iff_indep_forall {M₁ M₂ : matroid E} : M₁ = M₂ ↔ ∀ I, M₁.indep I ↔ M₂.indep I :=  
⟨λ h I, by rw h,  eq_of_indep_iff_indep_forall⟩  

lemma eq_iff_set_of_indep_eq_set_of_indep {M₁ M₂ : matroid E} : 
  M₁ = M₂ ↔ {I | M₁.indep I} = {I | M₂.indep I} :=
by { rw [eq_iff_indep_iff_indep_forall, set.ext_iff], refl }

end indep

section from_axioms

def matroid_of_base {E : Type*} (base : set E → Prop) 
(exists_base : ∃ B, base B) (base_exchange : exchange_property base) 
(maximality : exists_maximal_subset_property {I | ∃ B, base B ∧ I ⊆ B}) : matroid E := 
⟨base, exists_base, base_exchange, maximality⟩

@[simp] lemma matroid_of_base_apply {E : Type*} (base : set E → Prop) (exists_base : ∃ B, base B) 
(base_exchange : exchange_property base) 
(maximality : exists_maximal_subset_property {I | ∃ B, base B ∧ I ⊆ B}) :
(matroid_of_base base exists_base base_exchange maximality).base = base := rfl 

/-- A collection of bases with the exchange property and at least one finite member is a matroid -/
def matroid_of_exists_finite_base {E : Type*} (base : set E → Prop) 
(exists_finite_base : ∃ B, base B ∧ B.finite) (base_exchange : exchange_property base) : 
  matroid E := 
matroid_of_base base (let ⟨B,h⟩ := exists_finite_base in ⟨B,h.1⟩) base_exchange
(begin
  obtain ⟨B, hB, hfin⟩ := exists_finite_base,  
  apply exists_maximal_subset_property_of_bounded ⟨B.ncard, _⟩,
  rintro I ⟨B', hB', hIB'⟩,   
  have hB'fin : B'.finite, from finite_of_finite_of_exch base_exchange hB hB' hfin, 
  rw card_eq_card_of_exchange base_exchange hB hB', 
  exact ⟨hB'fin.subset hIB', ncard_le_of_subset hIB' hB'fin⟩, 
end)

@[simp] lemma matroid_of_exists_finite_base_apply {E : Type*} (base : set E → Prop) 
(exists_finite_base : ∃ B, base B ∧ B.finite) (base_exchange : exchange_property base) : 
(matroid_of_exists_finite_base base exists_finite_base base_exchange).base = base := rfl 

/-- A matroid constructed with a finite base is `finite_rk` -/
instance {E : Type*} {base : set E → Prop} {exists_finite_base : ∃ B, base B ∧ B.finite} 
{base_exchange : exchange_property base} : 
  matroid.finite_rk (matroid_of_exists_finite_base base exists_finite_base base_exchange) := 
⟨exists_finite_base⟩  

def matroid_of_base_of_finite {E : Type*} [finite E] (base : set E → Prop)
(exists_base : ∃ B, base B) (base_exchange : exchange_property base) : matroid E :=
matroid_of_exists_finite_base base (let ⟨B,hB⟩ := exists_base in ⟨B,hB,to_finite _⟩) base_exchange

@[simp] lemma matroid_of_base_of_finite_apply {E : Type*} [finite E] (base : set E → Prop) 
(exists_base : ∃ B, base B) (base_exchange : exchange_property base) : 
(matroid_of_base_of_finite base exists_base base_exchange).base = base := rfl 

/-- A version of the independence axioms that avoids cardinality -/
def matroid_of_indep {E : Type*} (indep : set E → Prop) (h_empty : indep ∅) 
(h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I) 
(h_aug : ∀⦃I B⦄, indep I → I ∉ maximals (⊆) indep → B ∈ maximals (⊆) indep → 
  ∃ x ∈ B \ I, indep (insert x I))
(h_maximal : exists_maximal_subset_property indep) : matroid E :=
matroid_of_base (λ B, B ∈ maximals (⊆) indep)
(begin
  obtain ⟨B, ⟨hB,-,-⟩, hB₁⟩ :=  h_maximal ∅ univ h_empty (subset_univ _),  
  exact ⟨B, ⟨hB,λ B' hB' hBB', hB₁ ⟨hB', empty_subset _,subset_univ _⟩ hBB'⟩⟩,  
end)
(begin
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
end)
(begin
  rintro I X ⟨B, hB,  hIB⟩ hIX, 
  obtain ⟨J, ⟨hJ, hIJ, hJX⟩, hJmax⟩ := h_maximal I X (h_subset hB.1 hIB) hIX, 
  obtain ⟨BJ, hBJ⟩ := h_maximal J univ hJ (subset_univ _), 
  refine ⟨J, ⟨⟨BJ,_, hBJ.1.2.1⟩ ,hIJ,hJX⟩, _⟩,  
  { exact ⟨hBJ.1.1, λ B' hB' hBJB', hBJ.2 ⟨hB',hBJ.1.2.1.trans hBJB', subset_univ _⟩ hBJB'⟩ },
  simp only [mem_set_of_eq, and_imp, forall_exists_index], 
  rintro A ⟨B', ⟨(hB'i : indep _), hB'max⟩, hB''⟩ hIA hAX hJA, 
  exact hJmax ⟨h_subset hB'i hB'', hIA, hAX⟩ hJA 
end )

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

/-- If there is an absolute upper bound on the size of an independent set, then the maximality 
  axiom isn't needed to define a matroid by independent sets. -/
def matroid_of_indep_of_bdd {E : Type*} (indep : set E → Prop) (h_empty : indep ∅) 
(h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I) 
(h_aug : ∀⦃I B⦄, indep I → I ∉ maximals (⊆) indep → B ∈ maximals (⊆) indep → 
  ∃ x ∈ B \ I, indep (insert x I))
(h_bdd : ∃ n, ∀ I, indep I → I.finite ∧ I.ncard ≤ n ) : matroid E :=
matroid_of_indep indep h_empty h_subset h_aug (exists_maximal_subset_property_of_bounded h_bdd)

@[simp] lemma matroid_of_indep_of_bdd_apply (indep : set E → Prop) (h_empty : indep ∅) 
(h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I) 
(h_aug : ∀⦃I B⦄, indep I → I ∉ maximals (⊆) indep → B ∈ maximals (⊆) indep → 
  ∃ x ∈ B \ I, indep (insert x I))
(h_bdd : ∃ n, ∀ I, indep I → I.finite ∧ I.ncard ≤ n ) : 
(matroid_of_indep_of_bdd indep h_empty h_subset h_aug h_bdd).indep = indep := 
by simp [matroid_of_indep_of_bdd]

instance (indep : set E → Prop) (h_empty : indep ∅) (h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I) 
(h_aug : ∀⦃I B⦄, indep I → I ∉ maximals (⊆) indep → B ∈ maximals (⊆) indep → 
  ∃ x ∈ B \ I, indep (insert x I)) (h_bdd : ∃ n, ∀ I, indep I → I.finite ∧ I.ncard ≤ n ) : 
matroid.finite_rk (matroid_of_indep_of_bdd indep h_empty h_subset h_aug h_bdd) := 
begin
  obtain ⟨B, hB⟩ := (matroid_of_indep_of_bdd indep h_empty h_subset h_aug h_bdd).exists_base, 
  obtain ⟨h, h_bdd⟩ := h_bdd,  
  refine hB.finite_rk_of_finite (h_bdd B _).1,
  rw [←matroid_of_indep_of_bdd_apply indep, matroid.indep], 
  exact ⟨_, hB, subset.rfl⟩,  
end 

/-- A collection of sets in a finite type satisfying the usual independence axioms determines a 
  matroid -/
def matroid_of_indep_of_finite [finite E] (indep : set E → Prop)
(exists_ind : ∃ I, indep I)
(ind_mono : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I)
(ind_aug : ∀ ⦃I J⦄, indep I → indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ indep (insert e I)) :
  matroid E := 
  matroid_of_indep indep (exists.elim exists_ind (λ I hI, ind_mono hI (empty_subset _))) ind_mono 
  (begin
    intros I J hI hIn hJ, 
    by_contra' h', 
    obtain (hlt | hle) := lt_or_le I.ncard J.ncard, 
    { obtain ⟨e,heJ,heI, hi⟩ :=  ind_aug hI hJ.1 hlt, 
      exact h' e ⟨heJ,heI⟩ hi },
    obtain (h_eq | hlt) := hle.eq_or_lt, 
    { refine hIn ⟨hI, λ K (hK : indep K) hIK, hIK.ssubset_or_eq.elim (λ hss, _) 
        (λ h, h.symm.subset)⟩,
      obtain ⟨f, hfK, hfJ, hi⟩ := ind_aug hJ.1 hK (h_eq.trans_lt (ncard_lt_ncard hss)), 
      exact (hfJ (hJ.2 hi (subset_insert _ _) (mem_insert f _))).elim },
    obtain ⟨e,heI, heJ, hi⟩ := ind_aug hJ.1 hI hlt, 
      exact heJ (hJ.2 hi (subset_insert _ _) (mem_insert e _)), 
  end) 
  ( exists_maximal_subset_property_of_bounded ⟨(univ : set E).ncard ,
    (λ I hI, ⟨to_finite I, ncard_le_of_subset (subset_univ _)⟩)⟩ )

@[simp] lemma matroid_of_indep_of_finite_apply [finite E] {indep : set E → Prop}
(exists_ind : ∃ I, indep I) (ind_mono : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I)
(ind_aug : ∀ ⦃I J⦄, indep I → indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ indep (insert e I)) :
  (matroid_of_indep_of_finite indep exists_ind ind_mono ind_aug).indep = indep :=
by simp [matroid_of_indep_of_finite]

end from_axioms 

section dual

/-- This is really an order-theory lemma. Not clear where to put it, though.  -/
lemma base_compl_iff_mem_maximals_disjoint_base : 
  M.base Bᶜ ↔ B ∈ maximals (⊆) {I | ∃ B, M.base B ∧ disjoint I B} :=
begin
  simp_rw ←subset_compl_iff_disjoint_left, 
  refine ⟨λ h, ⟨⟨Bᶜ,h,subset.rfl⟩, _⟩, _⟩,
  { rintro X ⟨B', hB', hXB'⟩ hBX, 
    rw [←compl_subset_compl] at ⊢ hBX,
    rwa ←hB'.eq_of_subset_base h (hXB'.trans hBX) },
  rintro ⟨⟨B',hB',hBB'⟩,h⟩, 
  rw subset_compl_comm at hBB', 
  rwa [hBB'.antisymm (h ⟨_, hB', _⟩ hBB'), compl_compl],   
  rw compl_compl, 
end 

/-- The dual of a matroid `M`; its bases are the complements of bases in `M`. 
  The proofs here are messier than they need to be. -/
def dual (M : matroid E) : matroid E := 
matroid_of_indep (λ I, ∃ B, M.base B ∧ disjoint I B) 
(M.exists_base.imp (λ B hB, ⟨hB, empty_disjoint B⟩))
(λ I J ⟨B, hB, hJB⟩ hIJ, ⟨B, hB, disjoint_of_subset_left hIJ hJB⟩) 
(begin
  rintro I X ⟨B, hB, hIB⟩ hI_not_max hX_max,  
  have hB' := base_compl_iff_mem_maximals_disjoint_base.mpr hX_max,
  set B' := Xᶜ with hX, 
  have hI := (not_iff_not.mpr base_compl_iff_mem_maximals_disjoint_base).mpr hI_not_max, 
  obtain ⟨B'', hB'', hB''₁, hB''₂⟩ := (hB'.indep.diff I).exists_base_subset_union_base hB, 
  rw [←compl_subset_compl, ←hIB.sdiff_eq_right, ←union_diff_distrib, diff_eq, compl_inter, 
    compl_compl, union_subset_iff, compl_subset_compl] at hB''₂, 
  obtain ⟨e,⟨heB'',heI⟩⟩ := exists_of_ssubset (hB''₂.2.ssubset_of_ne 
    (by { rintro rfl, rw compl_compl at hI, exact hI hB'' })),
  refine ⟨e, ⟨by_contra (λ heB', heB'' (hB''₁ ⟨heB', heI⟩)), heI⟩, ⟨B'', hB'', _⟩⟩, 
  rw [←union_singleton, disjoint_union_left, disjoint_singleton_left, 
    ←subset_compl_iff_disjoint_right], 
  exact ⟨hB''₂.2, heB''⟩, 
end) 
(begin
  rintro I' X ⟨B, hB, hI'B⟩ hI'X, 
  obtain ⟨I, hI⟩ :=  M.exists_basis Xᶜ ,
  obtain ⟨B', hB', hIB', hB'IB⟩ := hI.indep.exists_base_subset_union_base hB, 
  refine ⟨X \ B', ⟨⟨_,hB',disjoint_sdiff_left⟩, subset_diff.mpr ⟨hI'X, _⟩,diff_subset _ _⟩, _⟩, 
  { refine disjoint_of_subset_right hB'IB (disjoint_union_right.mpr ⟨_,hI'B⟩), 
    rw [←subset_compl_iff_disjoint_left], 
    exact hI.subset.trans (compl_subset_compl.mpr hI'X) },
  rintro J ⟨⟨B'',hB'', hJB''⟩, hI'J, hJX⟩ hXB'J, 

  have hI' : (B'' ∩ X) ∪ (B' \ X) ⊆ B', 
  { refine (union_subset _ (diff_subset _ _)),
    refine (inter_subset_inter_right _ (diff_subset_iff.mp hXB'J)).trans _, 
    rw [inter_distrib_left, inter_comm _ J, disjoint_iff_inter_eq_empty.mp hJB'', union_empty],
    exact inter_subset_right _ _ },

  obtain ⟨B₁,hB₁,hI'B₁,hB₁I⟩ := (hB'.indep.subset hI').exists_base_subset_union_base hB'', 
  rw [union_comm, ←union_assoc, union_eq_self_of_subset_right (inter_subset_left _ _)] at hB₁I, 

  have : B₁ = B', 
  { refine hB₁.eq_of_subset_indep hB'.indep (λ e he, _), 
    refine (hB₁I he).elim (λ heB'',_) (λ h, h.1), 
    refine (em (e ∈ X)).elim (λ heX, hI' (or.inl ⟨heB'', heX⟩)) (λ heX, hIB' _), 
    refine hI.mem_of_insert_indep heX (hB₁.indep.subset (insert_subset.mpr ⟨he, _⟩)), 
    refine (subset_union_of_subset_right (subset_diff.mpr ⟨hIB',_⟩) _).trans hI'B₁, 
    exact subset_compl_iff_disjoint_right.mp hI.subset }, 
  
  subst this, 

  refine subset_diff.mpr ⟨hJX, by_contra (λ hne, _)⟩, 
  obtain ⟨e, heJ, heB'⟩ := not_disjoint_iff.mp hne,
  obtain (heB'' | ⟨heB₁,heX⟩ ) := hB₁I heB', 
  { exact hJB''.ne_of_mem heJ heB'' rfl },
  exact heX (hJX heJ), 
end)

@[class] structure has_matroid_dual (α : Type*) := (dual : α → α)

postfix `﹡`:(max+1) := has_matroid_dual.dual 

instance matroid_dual {E : Type*} : has_matroid_dual (matroid E) := ⟨matroid.dual⟩ 

lemma dual.base_iff : M﹡.base B ↔ M.base Bᶜ := base_compl_iff_mem_maximals_disjoint_base.symm

@[simp] lemma dual_dual (M : matroid E) : M﹡﹡ = M := 
by { ext, simp_rw [dual.base_iff, compl_compl] }

lemma dual_indep_iff_coindep : M﹡.indep X ↔ M.coindep X := 
by { simp [has_matroid_dual.dual, dual, coindep] }

lemma base.compl_base_dual (hB : M.base B) : M﹡.base Bᶜ := by rwa [dual.base_iff, compl_compl]  

lemma base.compl_inter_basis_of_inter_basis (hB : M.base B) (hBX : M.basis (B ∩ X) X) :
  M﹡.basis (Bᶜ ∩ Xᶜ) Xᶜ := 
begin
  rw basis_iff, 
  refine ⟨(hB.compl_base_dual.indep.subset (inter_subset_left _ _)), inter_subset_right _ _, 
    λ J hJ hBCJ hJX, hBCJ.antisymm (subset_inter (λ e heJ heB, _) hJX)⟩, 
  obtain ⟨B', hB', hJB'⟩ := dual_indep_iff_coindep.mp hJ,  
  obtain ⟨B'', hB'', hsB'', hB''s⟩  := hBX.indep.exists_base_subset_union_base hB', 
  have hB'ss : B' ⊆ B ∪ X, 
  { rw [←compl_subset_compl, compl_union, subset_compl_iff_disjoint_right],
    exact disjoint_of_subset_left hBCJ hJB' },
  have hB''ss : B'' ⊆ B, 
  { refine λ e he, (hB''s he).elim and.left (λ heB', (hB'ss heB').elim id (λ heX, _)),   
    exact (hBX.mem_of_insert_indep heX (hB''.indep.subset (insert_subset.mpr ⟨he,hsB''⟩))).1 },
  have := (hB''.eq_of_subset_indep hB.indep hB''ss).symm, subst this, 
  exact (hB''s heB).elim (λ heBX, hJX heJ heBX.2) (λ heB', hJB'.ne_of_mem heJ heB' rfl), 
end 

lemma base.inter_basis_iff_compl_inter_basis_dual (hB : M.base B) : 
  M.basis (B ∩ X) X ↔ M﹡.basis (Bᶜ ∩ Xᶜ) Xᶜ :=
⟨hB.compl_inter_basis_of_inter_basis, λ h, 
  by simpa using hB.compl_base_dual.compl_inter_basis_of_inter_basis h⟩ 
  
lemma dual_inj {M₁ M₂ : matroid E} (h : M₁﹡ = M₂﹡) : M₁ = M₂ :=
by { ext B, rw [←compl_compl B, ←dual.base_iff, h, dual.base_iff] }

@[simp] lemma dual_inj_iff {M₁ M₂ : matroid E} : M₁﹡ = M₂﹡ ↔ M₁ = M₂ := ⟨dual_inj, congr_arg _⟩

lemma coindep_iff_disjoint_base : M.coindep X ↔ ∃ B, M.base B ∧ disjoint X B := iff.rfl 

lemma coindep.exists_disjoint_base (hX : M.coindep X) : ∃ B, M.base B ∧ disjoint X B := hX  

lemma coindep.base_of_basis_compl (hX : M.coindep X) (hB : M.basis B Xᶜ) : M.base B :=
begin
  obtain ⟨B',hB'⟩ := hX.exists_disjoint_base, 
  exact hB'.1.base_of_basis_supset (subset_compl_iff_disjoint_left.mpr hB'.2) hB, 
end 

lemma base_iff_dual_base_compl : M.base B ↔ M﹡.base Bᶜ :=
by rw [←compl_compl B, dual.base_iff, compl_compl, compl_compl]

end dual 

section lrestrict 

/-- Turn all elements of the matroid outside `X` into loops -/
def lrestrict (M : matroid E) (X : set E) : matroid E :=
matroid_of_indep (λ I, M.indep I ∧ I ⊆ X) ⟨M.empty_indep, empty_subset _⟩ 
(λ I J hJ hIJ, ⟨hJ.1.subset hIJ, hIJ.trans hJ.2⟩)
(begin
  rintro I I' ⟨hI, hIX⟩ (hIn : ¬M.basis I X) (hI' : M.basis I' X),
  obtain ⟨B', hB', rfl⟩ := hI'.exists_base, 
  obtain ⟨B, hB, hIB, hBIB'⟩ := hI.exists_base_subset_union_base hB',
  rw hB'.inter_basis_iff_compl_inter_basis_dual at hI', 
  have hss : B'ᶜ ∩ Xᶜ ⊆ Bᶜ ∩ Xᶜ, 
  { rw [←compl_union, ←compl_union, compl_subset_compl],
    exact union_subset 
      (hBIB'.trans (union_subset (hIX.trans (subset_union_right _ _)) (subset_union_left _ _))) 
      (subset_union_right _ _) },  
  have h_eq := hI'.eq_of_subset_indep _ hss (inter_subset_right _ _), 
  { rw [h_eq, ←hB.inter_basis_iff_compl_inter_basis_dual] at hI', 
    have hssu : I ⊂ (B ∩ X) := (subset_inter hIB hIX).ssubset_of_ne 
      (by { rintro rfl, exact hIn hI' }), 
    obtain ⟨e,he, heI⟩ := exists_of_ssubset hssu, 
    
    refine ⟨e, ⟨⟨_,he.2⟩,heI⟩, hI'.indep.subset (insert_subset.mpr ⟨he,hssu.subset⟩), 
      insert_subset.mpr ⟨he.2, hIX⟩⟩,  
    exact (hBIB' he.1).elim (λ heI', (heI heI').elim) id },
  exact dual_indep_iff_coindep.mpr ⟨B,hB, 
    disjoint_of_subset_left (inter_subset_left _ _) disjoint_compl_left⟩, 
end)
(begin
  rintro I A ⟨hI, hIX⟩ hIA, 
  obtain ⟨J, hIJ, hJ⟩ := hI.subset_basis_of_subset (subset_inter hIX hIA), 
  refine ⟨J, ⟨⟨hJ.indep,hJ.subset.trans (inter_subset_left _ _)⟩,hIJ,
    hJ.subset.trans (inter_subset_right _ _)⟩, λ K hK hJK, _⟩, 
  rw hJ.eq_of_subset_indep hK.1.1 hJK (subset_inter hK.1.2 hK.2.2), 
end)

/- The API below is private because it is later developed with appropriate notation in 
  `pseudominor.lean` -/

lemma lrestrict_indep_iff : (M.lrestrict X).indep I ↔ (M.indep I ∧ I ⊆ X) := 
by simp [lrestrict]

private lemma lrestrict_lrestrict : (M.lrestrict X).lrestrict Y = M.lrestrict (X ∩ Y) :=
eq_of_indep_iff_indep_forall (λ I, by simp only [and_assoc, lrestrict_indep_iff, subset_inter_iff]) 

private lemma lrestrict_lrestrict_subset (hXY : X ⊆ Y) : 
  (M.lrestrict Y).lrestrict X = M.lrestrict X :=
by rw [lrestrict_lrestrict, inter_eq_right_iff_subset.mpr hXY]
 
private lemma indep.indep_lrestrict_of_subset (hI : M.indep I) (hIX : I ⊆ X) : 
  (M.lrestrict X).indep I :=
lrestrict_indep_iff.mpr ⟨hI, hIX⟩ 

private lemma lrestrict_base_iff : (M.lrestrict X).base I ↔ M.basis I X := iff.rfl 

private lemma basis.base_lrestrict (h : M.basis I X) : (M.lrestrict X).base I := 
lrestrict_base_iff.mpr h

private lemma basis.basis_lrestrict_of_subset (hI : M.basis I X) (hXY : X ⊆ Y) :
  (M.lrestrict Y).basis I X :=
by rwa [←lrestrict_base_iff, lrestrict_lrestrict_subset hXY, lrestrict_base_iff]

end lrestrict 

section basis

lemma basis.transfer (hIX : M.basis I X) (hJX : M.basis J X) (hXY : X ⊆ Y) (hJY : M.basis J Y) : 
  M.basis I Y :=
begin
  rw [←lrestrict_base_iff] at ⊢ hJY, 
  exact hJY.base_of_basis_supset hJX.subset (basis.basis_lrestrict_of_subset hIX hXY),  
end 

lemma basis.transfer' (hI : M.basis I X) (hJ : M.basis J Y) (hJX : J ⊆ X) (hIY : I ⊆ Y) : 
  M.basis I Y :=
begin
  have hI' := hI.basis_subset (subset_inter hI.subset hIY) (inter_subset_left _ _), 
  have hJ' := hJ.basis_subset (subset_inter hJX hJ.subset) (inter_subset_right _ _), 
  exact hI'.transfer hJ' (inter_subset_right _ _) hJ, 
end 

lemma basis.transfer'' (hI : M.basis I X) (hJ : M.basis J Y) (hJX : J ⊆ X) : M.basis I (I ∪ Y) :=
begin
  obtain ⟨J', hJJ', hJ'⟩  := hJ.indep.subset_basis_of_subset hJX, 
  have hJ'Y := (hJ.basis_union_of_subset hJ'.indep hJJ').basis_union hJ', 
  refine (hI.transfer' hJ'Y hJ'.subset _).basis_subset _ _,  
  { exact subset_union_of_subset_right hI.subset _ },
  { exact subset_union_left _ _ }, 
  refine union_subset (subset_union_of_subset_right hI.subset _) _,
  rw union_right_comm, 
  exact subset_union_right _ _, 
end 

lemma indep.exists_basis_subset_union_basis (hI : M.indep I) (hIX : I ⊆ X) (hJ : M.basis J X) : 
  ∃ I', M.basis I' X ∧ I ⊆ I' ∧ I' ⊆ I ∪ J :=
begin
  obtain ⟨I', hI', hII', hI'IJ⟩ := 
    (indep.indep_lrestrict_of_subset hI hIX).exists_base_subset_union_base 
      (basis.base_lrestrict hJ), 
  exact ⟨I', lrestrict_base_iff.mp hI', hII', hI'IJ⟩, 
end 

lemma indep.exists_insert_of_not_basis (hI : M.indep I) (hIX : I ⊆ X) (hI' : ¬M.basis I X) 
(hJ : M.basis J X) : 
  ∃ e ∈ J \ I, M.indep (insert e I) :=
begin
  rw [←lrestrict_base_iff] at hI' hJ, 
  obtain ⟨e, he, hi⟩ := (indep.indep_lrestrict_of_subset hI hIX).exists_insert_of_not_base hI' hJ, 
  exact ⟨e, he, (lrestrict_indep_iff.mp hi).1⟩,
end 

lemma basis.base_of_base_subset (hIX : M.basis I X) (hB : M.base B) (hBX : B ⊆ X) : M.base I :=
hB.base_of_basis_supset hBX hIX

lemma basis.exchange (hIX : M.basis I X) (hJX : M.basis J X) (he : e ∈ I \ J) : 
  ∃ f ∈ J \ I, M.basis (insert f (I \ {e})) X :=
by { simp_rw ←lrestrict_base_iff at *, exact hIX.exchange hJX he }

lemma basis.eq_exchange_of_diff_eq_singleton (hI : M.basis I X) (hJ : M.basis J X) 
(hIJ : I \ J = {e}) : 
  ∃ f ∈ J \ I, J = (insert f I) \ {e} :=
by { rw [←lrestrict_base_iff] at hI hJ, exact hI.eq_exchange_of_diff_eq_singleton hJ hIJ }

end basis

section finite

lemma basis.card_eq_card_of_basis (hIX : M.basis I X) (hJX : M.basis J X) : I.ncard = J.ncard :=
by { rw [←lrestrict_base_iff] at hIX hJX, exact hIX.card_eq_card_of_base hJX }

lemma basis.finite_of_finite (hIX : M.basis I X) (hI : I.finite) (hJX : M.basis J X)  : J.finite := 
by { rw [←lrestrict_base_iff] at hIX hJX, exact hIX.finite_of_finite hI hJX }

lemma basis.infinite_of_infinite (hIX : M.basis I X) (hI : I.infinite) (hJX : M.basis J X) : 
  J.infinite := 
by { rw [←lrestrict_base_iff] at hIX hJX, exact hIX.infinite_of_infinite hI hJX }

lemma basis.card_diff_eq_card_diff (hIX : M.basis I X) (hJX : M.basis J X) : 
  (I \ J).ncard = (J \ I).ncard :=
by { rw [←lrestrict_base_iff] at hIX hJX, rw hJX.card_diff_eq_card_diff hIX }

lemma basis.diff_finite_comm (hIX : M.basis I X) (hJX : M.basis J X) :
  (I \ J).finite ↔ (J \ I).finite := 
by { rw [←lrestrict_base_iff] at hIX hJX, exact hIX.diff_finite_comm hJX }

lemma basis.diff_infinite_comm (hIX : M.basis I X) (hJX : M.basis J X) :
  (I \ J).infinite ↔ (J \ I).infinite := 
by { rw [←lrestrict_base_iff] at hIX hJX, exact hIX.diff_infinite_comm hJX }

/-- `M.r_fin X` means that `X` has a finite basis in `M`-/
def r_fin (M : matroid E) (X : set E) : Prop := ∃ I, M.basis I X ∧ I.finite  

lemma to_r_fin (M : matroid E) [finite_rk M] (X : set E) : M.r_fin X :=  
by { obtain ⟨I,hI⟩ := M.exists_basis X, exact ⟨I, hI, hI.finite⟩ }

lemma basis.finite_of_r_fin (h : M.basis I X) (hX : M.r_fin X) : I.finite :=
by { obtain ⟨J, hJ, hJfin⟩ := hX, exact hJ.finite_of_finite hJfin h }

lemma basis.r_fin_of_finite (hIX : M.basis I X) (h : I.finite) : M.r_fin X := ⟨I, hIX, h⟩ 

lemma basis.r_fin_iff_finite (hIX : M.basis I X) : M.r_fin X ↔ I.finite := 
⟨hIX.finite_of_r_fin, hIX.r_fin_of_finite⟩

lemma r_fin_of_finite (M : matroid E) (hX : X.finite) : M.r_fin X := 
exists.elim (M.exists_basis X) (λ I hI, hI.r_fin_of_finite (hX.subset hI.subset))

@[simp] lemma r_fin_empty (M : matroid E) : M.r_fin ∅ := M.r_fin_of_finite finite_empty

lemma r_fin.subset (h : M.r_fin Y) (hXY : X ⊆ Y) : M.r_fin X := 
begin
  obtain ⟨I, hI⟩ := M.exists_basis X, 
  obtain ⟨J, hIJ, hJ⟩ := hI.indep.subset_basis_of_subset (hI.subset.trans hXY),    
  exact hI.r_fin_of_finite ((hJ.finite_of_r_fin h).subset hIJ), 
end 

lemma indep.augment_of_finite (hI : M.indep I) (hJ : M.indep J) (hIfin : I.finite) 
(hIJ : I.ncard < J.ncard) :
  ∃ x ∈ J, x ∉ I ∧ M.indep (insert x I) :=
begin
  obtain ⟨K, hK, hIK⟩ :=  
    (indep.indep_lrestrict_of_subset hI (subset_union_left I J)).exists_base_supset, 
  obtain ⟨K', hK', hJK'⟩ :=
    (indep.indep_lrestrict_of_subset hJ (subset_union_right I J)).exists_base_supset, 
  have hJfin := finite_of_ncard_pos ((nat.zero_le _).trans_lt hIJ), 
  rw lrestrict_base_iff at hK hK', 
  have hK'fin := (hIfin.union hJfin).subset hK'.subset, 
  have hlt := 
    hIJ.trans_le ((ncard_le_of_subset hJK' hK'fin).trans_eq (hK'.card_eq_card_of_basis hK)), 
  obtain ⟨e,he⟩ := exists_mem_not_mem_of_ncard_lt_ncard hlt hIfin, 
  exact ⟨e, (hK.subset he.1).elim (false.elim ∘ he.2) id, 
    he.2, hK.indep.subset (insert_subset.mpr ⟨he.1,hIK⟩)⟩, 
end 

/-- The independence augmentation axiom; given independent sets `I,J` with `I` smaller than `J`,
  there is an element `e` of `J \ I` whose insertion into `e` is an independent set.  -/
lemma indep.augment [finite_rk M] (hI : M.indep I) (hJ : M.indep J) (hIJ : I.ncard < J.ncard) :
  ∃ x ∈ J, x ∉ I ∧ M.indep (insert x I) :=
hI.augment_of_finite hJ hI.finite hIJ

/-- The independence augmentation axiom in a form that finds a strict superset -/
lemma indep.ssubset_indep_of_card_lt_of_finite (hI : M.indep I) (hI_fin : I.finite) (hJ : M.indep J) 
(hIJ : I.ncard < J.ncard) :
  ∃ I', M.indep I' ∧ I ⊂ I' ∧ I' ⊆ I ∪ J :=
begin
  obtain ⟨e, heJ, heI, hI'⟩ := hI.augment_of_finite hJ hI_fin hIJ ,
  exact ⟨_, hI', ssubset_insert heI, insert_subset.mpr ⟨or.inr heJ,subset_union_left _ _⟩⟩,
end

lemma indep.ssubset_indep_of_card_lt [finite_rk M] (hI : M.indep I) (hJ : M.indep J) 
(hIJ : I.ncard < J.ncard) :
  ∃ I', M.indep I' ∧ I ⊂ I' ∧ I' ⊆ I ∪ J :=
hI.ssubset_indep_of_card_lt_of_finite hI.finite hJ hIJ

lemma indep.le_card_basis_of_r_fin (hI : M.indep I) (hIX : I ⊆ X) (hX : M.r_fin X) 
(hXJ : M.basis J X) : I.ncard ≤ J.ncard :=
begin
  obtain ⟨I', hI'⟩ := hI.subset_basis_of_subset hIX, 
  rw hXJ.card_eq_card_of_basis hI'.2, 
  exact ncard_le_of_subset hI'.1 (hI'.2.finite_of_r_fin hX), 
end 

lemma indep.le_card_basis [finite_rk M] (hI : M.indep I) (hIX : I ⊆ X) (hJX : M.basis J X) :
  I.ncard ≤ J.ncard :=
begin
  refine le_of_not_lt (λ hlt, _),
  obtain ⟨I', hI'⟩ := hJX.indep.ssubset_indep_of_card_lt hI hlt,
  have := hJX.eq_of_subset_indep hI'.1 hI'.2.1.subset (hI'.2.2.trans (union_subset hJX.subset hIX)),
  subst this,
  exact hI'.2.1.ne rfl,
end

end finite

end matroid 
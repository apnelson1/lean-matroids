import order.complete_lattice
import tactic 
import set_theory.cardinal.finite

-- import matroid.axioms

noncomputable theory 
open_locale classical 

section finset 

variables {α : Type*} {X Y : finset α}

lemma finset.exists_mem_diff_of_card_lt_card (h : X.card < Y.card) : 
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

variables {E : Type*}

def exchange_property (base : set E → Prop) : Prop :=
  ∀ B₁ B₂, base B₁ → base B₂ 
    → ∀ (b₁ : E), b₁ ∈ B₁ \ B₂ → ∃ b₂, (b₂ ∈ B₂ \ B₁) ∧ base (B₁ \ {b₁} ∪ {b₂}) 


/-- 
  A `matroid` is a collection of sets (each of which is a `base`) satisfying the exchange property.
-/
@[ext] structure matroid (E : Type*) :=
  (base : set E → Prop)
  (exists_base' : ∃ B, base B) 
  (base_exchange' : exchange_property base)

namespace matroid 

variables [fintype E] {B B' B₁ B₂ I I' J I₁ I₂ J' X Y Z : set E} {M M₁ M₂ : matroid E}

lemma exists_base (M : matroid E) : ∃ B, M.base B := M.exists_base'

lemma base_exchange {M : matroid E} {B₁ B₂ : set E} {x : E} 
(hB₁ : M.base B₁) (hB₂ : M.base B₂) (hxB₁ : x ∈ B₁) (hxB₂ : x ∉ B₂) : 
  ∃ y, (y ∈ B₂ ∧ y ∉ B₁) ∧ M.base (B₁ \ {x} ∪ {y})   := 
M.base_exchange' B₁ B₂ hB₁ hB₂ x ⟨hxB₁,hxB₂⟩
  
lemma base.card_eq_card_of_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) :
  B₁.to_finset.card = B₂.to_finset.card := 
begin
  suffices h : ∀ i (B B' : finset E), M.base B → M.base B' → (B' \ B).card ≤ i → 
    B'.card ≤ B.card, 
  { exact (h _ B₂.to_finset B₁.to_finset (by simpa) (by simpa) rfl.le).antisymm 
          (h _ B₁.to_finset B₂.to_finset (by simpa) (by simpa) rfl.le), }, 
  clear hB₁ B₁ hB₂ B₂, 
  intro i, 
  induction i with i IH, 
  { rintros B B' - - h, 
    simp only [le_zero_iff, finset.card_eq_zero, finset.sdiff_eq_empty_iff_subset] at h, 
    apply finset.card_mono, exact finset.le_iff_subset.mpr h},  
  refine λ B B' hB hB' hcard, le_of_not_lt (λ hlt, _ ) , 
  obtain ⟨x, hxB', hxB⟩ := finset.exists_mem_diff_of_card_lt_card hlt,  

  obtain ⟨y, ⟨(hyB : y ∈ B), (hyB' : y ∉ B')⟩, hB''⟩ := base_exchange hB' hB hxB' hxB, 

  have hcard := IH B (B' \ {x} ∪ {y})  hB (by simpa using hB'') _, 
  { apply hlt.not_le, 
    rwa [finset.union_comm, ← finset.insert_eq, finset.card_insert_of_not_mem, 
      finset.sdiff_singleton_eq_erase, finset.card_erase_add_one hxB'] at hcard,
    simpa using hyB'},
  
  suffices hss : (B' \ {x} ∪ {y}) \ B ⊂ B' \ B, 
  { exact nat.le_of_lt_succ ((finset.card_lt_card hss).trans_le hcard)},

  refine (finset.ssubset_iff_of_subset (λ a, _) ).mpr ⟨x,  _⟩, 
  { simp only [finset.mem_sdiff, finset.mem_union, finset.mem_singleton, and_imp],
    rintros (⟨haB',hax⟩ | rfl) haB,  tauto, tauto},
  
  simp only [finset.mem_sdiff, finset.mem_union, finset.mem_singleton, eq_self_iff_true, not_true, 
    and_false, false_or, not_and, not_not, exists_prop], 
  
  refine ⟨⟨hxB', hxB⟩, _⟩, 
  rintro rfl, exact hyB, 
end 

section indep 

/-- Independence in a matroid. Needs no `fintype` instance. -/
def indep {E : Type*} (M : matroid E) : set E → Prop := λ I, ∃ B, M.base B ∧ I ⊆ B   

lemma empty_indep (M : matroid E) : M.indep ∅ := 
  exists.elim M.exists_base (λ B hB, ⟨_, hB, B.empty_subset⟩)

lemma indep_mono {M : matroid E} {I J : set E} (hIJ : I ⊆ J) (hJ : M.indep J) : M.indep I :=
by {obtain ⟨B, hB, hJB⟩ := hJ, exact ⟨B, hB, hIJ.trans hJB⟩}

lemma indep.subset (hJ : M.indep J) (hIJ : I ⊆ J) : M.indep I :=
by {obtain ⟨B, hB, hJB⟩ := hJ, exact ⟨B, hB, hIJ.trans hJB⟩}

/--
The independence augmentation axiom
-/
lemma indep.augment (hI : M.indep I) (hJ : M.indep J) (hIJ : I.to_finset.card < J.to_finset.card) : 
  ∃ x ∈ J, x ∉ I ∧ M.indep (insert x I) :=
begin
  suffices h_mod : ∀ {p} {I₁ I₂ B₁ B₂}, M.base B₁ → M.base B₂ → I₁ ⊆ B₁ → I₂ ⊆ B₂ →
    I₁.to_finset.card < I₂.to_finset.card → (B₂ \ (I₂ ∪ B₁)).to_finset.card = p →  
      ∃ x ∈ I₂, x ∉ I₁ ∧ M.indep (insert x I₁), 
  { obtain ⟨⟨BI,hBI,hIBI⟩,⟨BJ, hBJ, hJBJ⟩⟩ := ⟨hI,hJ⟩,
    exact h_mod hBI hBJ hIBI hJBJ hIJ rfl },         
  clear hI hJ hIJ I J,
  intro p, induction p with p IH, 
  all_goals 
  { intros _ _ _ _ hB₁ hB₂ hI₁B₁ hI₂B₂ h_lt h_le} , 
  { simp only [to_finset_diff, finset.card_eq_zero, finset.sdiff_eq_empty_iff_subset, 
      to_finset_subset, coe_to_finset] at h_le, 
    
    by_contradiction h_con, push_neg at h_con, 

    have h₁₂ : B₂ \ B₁ = I₂ \ I₁, 
    { apply subset_antisymm, 
      {  calc _ ⊆ _  : diff_subset_diff_left h_le  
            ... = _  : union_diff_right
             ... ⊆ _ : diff_subset_diff_right hI₁B₁}, 
      rintros x ⟨hxI₂, hxI₁⟩,  
      exact ⟨mem_of_mem_of_subset hxI₂ hI₂B₂, 
        λ hxB₁, h_con _ hxI₂ hxI₁ ⟨B₁, hB₁, insert_subset.mpr ⟨ hxB₁,hI₁B₁⟩⟩⟩}, 

    have hB₁ss : B₁ ⊆ I₁ ∪ B₂,
    { intros y hyB₁, 
      rw [mem_union, or_iff_not_imp_right],   
      intro hyB₂, 
      obtain ⟨x,⟨hxB₂, hxB₁⟩, hB'⟩ := base_exchange hB₁ hB₂ hyB₁ hyB₂,  
      obtain (hxI₂ | hxB₁') := mem_of_mem_of_subset hxB₂ h_le, 
      swap, exact (hxB₁ hxB₁').elim,
      by_contradiction hyI₁, 
      refine h_con x hxI₂ (not_mem_subset hI₁B₁ hxB₁) 
        ⟨_, hB', insert_subset.mpr ⟨by simp, subset_union_of_subset_left _ _⟩⟩,  
      apply subset_diff_singleton hI₁B₁ hyI₁},
    have hss₁ := calc B₁ \ B₂ ⊆ _       : diff_subset_diff_left hB₁ss  
                          ... = _       : union_diff_right
                          ... ⊆ I₁ \ I₂ : diff_subset_diff_right hI₂B₂,   

    rw [← to_finset_subset_to_finset, to_finset_diff, to_finset_diff] at hss₁, 

    have hle₁ := finset.card_mono hss₁, 
    simp_rw [finset.card_sdiff_eq_card_sdiff_iff_card_eq_card.mp (hB₁.card_eq_card_of_base hB₂), 
      ← to_finset_diff, h₁₂, to_finset_diff, ← finset.card_le_card_iff_card_sdiff_le_card_sdiff] 
      at hle₁, 
    exact h_lt.not_le hle₁},
  have h_ne : (B₂ \ (I₂ ∪ B₁)).nonempty, 
  { rw [← set.to_finset_nonempty, ←finset.card_pos, h_le], apply nat.succ_pos _},
  obtain ⟨x, hxB₂, hx'⟩ := h_ne, 
  rw [set.mem_union, not_or_distrib] at hx', obtain ⟨hxI₂, hxB₁⟩:= hx',  
  obtain ⟨y, ⟨hyB₁, hyB₂⟩, hB'⟩ := base_exchange hB₂ hB₁ hxB₂ hxB₁,  
  have hI₂B' : I₂ ⊆ B₂ \ {x} ∪ {y}, 
  { apply set.subset_union_of_subset_left, apply subset_diff_singleton hI₂B₂ hxI₂},

  refine IH hB₁ hB' hI₁B₁ hI₂B' h_lt _, 
  suffices h_set_eq : (B₂ \ {x} ∪ {y}) \ (I₂ ∪ B₁) = (B₂ \ (I₂ ∪ B₁)) \ {x},   
  { simp_rw h_set_eq,  rw [to_finset_diff, finset.card_sdiff, h_le], 
    { simp},
    simp only [to_finset_subset, coe_to_finset, singleton_subset_iff, mem_diff, mem_union], 
    tauto},
  rw [union_singleton, insert_diff_of_mem _ (mem_union_right _ hyB₁)],
  rw [diff_diff_comm], 
end 

/--
The independence augmentation axiom in a form that finds a strict superset
-/
lemma indep.ssubset_indep_of_card_lt (hI : M.indep I) (hJ : M.indep J) 
(hIJ : I.to_finset.card < J.to_finset.card) : 
  ∃ I', M.indep I' ∧ I ⊂ I' ∧ I' ⊆ I ∪ J := 
begin
  obtain ⟨e, heJ, heI, hI'⟩ := hI.augment hJ hIJ, 
  exact ⟨_, hI', ssubset_insert heI, insert_subset.mpr ⟨or.inr heJ,subset_union_left _ _⟩⟩,  
end 

lemma base.indep (hB : M.base B) : M.indep B := ⟨B, hB, subset_rfl⟩ 

lemma base.eq_of_subset_indep (hB : M.base B) (hI : M.indep I) (hBI : B ⊆ I) : 
  B = I :=
begin
  refine to_finset_inj.mp (finset.eq_of_subset_of_card_le (by simpa) _), 
  obtain ⟨B', hB', hIB'⟩ := hI, 
  rw hB.card_eq_card_of_base hB', 
  apply finset.card_mono, 
  simpa, 
end 

lemma base.eq_of_subset_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hB₁B₂ : B₁ ⊆ B₂) : 
  B₁ = B₂ :=
hB₁.eq_of_subset_indep (hB₂.indep) hB₁B₂

lemma base_iff_maximal_indep : M.base B ↔ M.indep B ∧ ∀ I, M.indep I → B ⊆ I → B = I :=
begin
  refine ⟨λ h, ⟨h.indep, λ _, h.eq_of_subset_indep ⟩,λ h, _⟩, 
  obtain ⟨⟨B', hB', hBB'⟩, h⟩ := h, 
  rwa h _ hB'.indep hBB', 
end  

lemma indep_inj_iff : M₁ = M₂ ↔ ∀ I, (M₁.indep I ↔ M₂.indep I) := 
begin
  refine ⟨λ h _, by rw h,λ h, _⟩, 
  ext B,
  have hI : M₁.indep = M₂.indep, by { ext ,apply h},
  simp_rw [base_iff_maximal_indep, hI],  
end 

end indep 

section basis

/-- A `basis` of a set `X` is a maximal independent subset of `X` -/
def basis {E : Type*} (M : matroid E) (I X : set E) := 
M.indep I ∧ I ⊆ X ∧ ∀ J, M.indep J → I ⊆ J → J ⊆ X → I = J 

lemma basis.indep (hI : M.basis I X) : M.indep I := hI.1

lemma basis.subset (hI : M.basis I X) : I ⊆ X := hI.2.1

lemma basis.eq_of_subset_indep (hI : M.basis I X) {J : set E} (hJ : M.indep J) (hIJ : I ⊆ J) 
(hJX : J ⊆ X) : 
  I = J := 
hI.2.2 J hJ hIJ hJX

lemma indep.subset_basis_of_subset (hI₁ : M.indep I₁) (hI₁X : I₁ ⊆ X) : 
  ∃ I, I₁ ⊆ I ∧ M.basis I X := 
begin
  set inds_of : finset (set E) := {I | M.indep I ∧ I₁ ⊆ I ∧ I ⊆ X}.to_finset with hbdef,
  have hne : inds_of.nonempty, 
    from to_finset_nonempty.mp ⟨I₁,by {simp only [finset.mem_val, mem_to_finset, mem_set_of_eq],
      exact ⟨hI₁, subset_refl _, hI₁X⟩}⟩,
  have h' := inds_of.exists_max_image (λ I, I.to_finset.card) hne, 
  simp only [mem_to_finset, mem_set_of_eq, and_imp, exists_prop] at h', 
  obtain ⟨I, ⟨hI, hI₁I, hIX⟩,hJ⟩ := h',   
  refine ⟨I, hI₁I, hI, hIX, λ I' hI' hII' hI'X, _⟩,  
  simpa using finset.eq_of_subset_of_card_le _ (hJ _ hI' (hI₁I.trans hII') hI'X),
  simpa,  
end 

lemma indep.le_card_basis (hI : M.indep I) (hIX : I ⊆ X) (hJX : M.basis J X) : 
  I.to_finset.card ≤ J.to_finset.card :=
begin
  refine le_of_not_lt (λ hlt, _), 
  obtain ⟨I', hI'⟩ := hJX.indep.ssubset_indep_of_card_lt hI hlt, 
  have := hJX.eq_of_subset_indep hI'.1 hI'.2.1.subset (hI'.2.2.trans (union_subset hJX.subset hIX)),
  subst this, 
  exact hI'.2.1.ne rfl, 
end 

lemma exists_basis (M : matroid E) (X : set E) : 
  ∃ I, M.basis I X :=
by {obtain ⟨I, -, hI⟩ := M.empty_indep.subset_basis_of_subset (empty_subset X), exact ⟨_,hI⟩, }

lemma base_iff_basis_univ : 
  M.base B ↔ M.basis B univ := 
by {rw [base_iff_maximal_indep, basis], simp}

end basis

section rank 

/-- The rank function of a matroid. This is defined using `nat.card`, to avoid a fintype instance 
  so as not to carry around data (it is zero if `X` is infinite) -/
def r {E : Type*} (M : matroid E) : set E → ℕ := 
  λ X, nat.find_greatest (λ n, ∃ I, I ⊆ X ∧ M.indep I ∧ n = nat.card I) (nat.card X)

/-- The rank `M.rk` of a matroid `M` is the rank of its ground set -/
@[reducible] def rk (M : matroid E) := M.r univ  

/-- This is the useful definition of rank -/
lemma eq_r_iff {n : ℕ} : M.r X = n ↔ ∃ I, M.basis I X ∧ I.to_finset.card = n :=
begin
  simp_rw [matroid.r, nat.find_greatest_eq_iff, nat.card_eq_to_finset_card, ne.def, 
    ←or_iff_not_imp_left, not_exists], push_neg, 
  split, 
  { rintros ⟨hnX, rfl | ⟨I, hIX, hI, rfl⟩, h⟩, 
    { simp_rw [pos_iff_ne_zero, ←or_iff_not_imp_left] at h, 
      obtain ⟨I, hI⟩ := M.exists_basis X, 
      refine ⟨I, hI, (@h I.to_finset.card).elim id (λ h', _)⟩,   
      exact (h' (finset.card_mono (by simpa using hI.subset)) I hI.subset hI.indep rfl).elim}, 
    refine ⟨I, ⟨hI, hIX, λ J hJ hIJ hJX,  
      (eq_or_ssubset_of_subset hIJ).elim id (λ hIssJ, false.elim _)⟩, rfl⟩, 
    exact h (finset.card_lt_card (to_finset_ssubset_to_finset.mpr hIssJ))
      (finset.card_le_of_subset (to_finset_subset_to_finset.mpr hJX)) J hJX hJ rfl}, 
  rintros ⟨I, ⟨hIX, rfl⟩⟩,
  refine ⟨finset.card_mono (by simpa using hIX.subset),or.inr ⟨I,hIX.subset,hIX.indep,rfl⟩,_⟩,
  rintro n hIn hnX J hJX hJ rfl,    
  exact hIn.not_le (hJ.le_card_basis hJX hIX),
end 

lemma le_r_iff {X : set E} {n : ℕ} : n ≤ M.r X ↔ ∃ I, M.indep I ∧ I ⊆ X ∧ I.to_finset.card = n :=
begin
  obtain ⟨J, hJ⟩ := eq_r_iff.mp (@rfl _ (M.r X)), 
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨I', hI', rfl⟩ := finset.exists_smaller_set _ _ (h.trans_eq hJ.2.symm), 
    rw [subset_to_finset] at hI', 
    exact ⟨I', hJ.1.indep.subset hI', hI'.trans hJ.1.subset, by simp⟩},
  obtain ⟨I, hI, hIX, rfl⟩ := h,
  rw ←hJ.2, 
  exact hI.le_card_basis hIX hJ.1,  
end    

lemma r_le_iff {X : set E} {n : ℕ} : 
  M.r X ≤ n ↔ ∀ I, M.indep I → I ⊆ X → I.to_finset.card ≤ n :=
begin
  obtain ⟨I, hIX, hI⟩ := eq_r_iff.mp (@rfl _ (M.r X)), 
  refine ⟨λ h J hJ hJX, (hJ.le_card_basis hJX hIX).trans (by rwa hI), λ h, _⟩,
  have := h I hIX.indep hIX.subset, rwa ←hI, 
end 

lemma basis.card (hIX : M.basis I X) : 
  I.to_finset.card = M.r X := 
by {rw [eq_comm, eq_r_iff], exact ⟨_, hIX, rfl⟩}

lemma indep.r (hI : M.indep I) : 
  M.r I = I.to_finset.card := 
eq_r_iff.mpr ⟨I, ⟨hI, subset_refl _, λ _ _, subset_antisymm⟩, rfl⟩

lemma basis.r (hIX : M.basis I X) : 
  M.r I = M.r X := 
by rw [←hIX.card, hIX.indep.r]

lemma indep_iff_r_eq_card : M.indep I ↔ M.r I = I.to_finset.card := 
begin
  refine ⟨indep.r ,λ h, _⟩, 
  obtain ⟨J, hJ, hJI, hJcard⟩ := le_r_iff.mp h.symm.le, 
  suffices hIJ : J = I, rwa ←hIJ, 
  rw ← to_finset_inj, 
  exact finset.eq_of_subset_of_card_le (by simpa) hJcard.symm.le,
end 

lemma r_empty (M : matroid E) : 
  M.r ∅ = 0 :=
by rw [M.empty_indep.r, to_finset_empty, finset.card_empty] 

lemma r_le_card (M : matroid E) (X : set E) : 
  M.r X ≤ X.to_finset.card :=
r_le_iff.mpr (λ I hI hIX, finset.card_mono (by simpa))

lemma r_mono (M : matroid E) {X Y : set E} (hXY : X ⊆ Y) : 
  M.r X ≤ M.r Y :=
begin
  simp_rw [r_le_iff, le_r_iff], 
  exact λ I hI hIX, ⟨I,hI,hIX.trans hXY,rfl.le⟩, 
end  

lemma base.r (hB : M.base B) : 
  M.r B = M.rk := 
by {rw [base_iff_basis_univ] at hB, rw hB.r}

lemma base_iff_indep_r : 
  M.base B ↔ M.indep B ∧ M.r B = M.rk :=
begin
  refine ⟨λ h, ⟨h.indep, h.r⟩, λ h, base_iff_maximal_indep.mpr ⟨h.1, λ I hI hBI, _⟩⟩, 
  refine eq_of_le_of_not_lt hBI (λ hBI' : B ⊂ I, _), 
  cases h with hB hB', 
  rw [hB.r] at hB', 
  have := finset.card_lt_card (to_finset_ssubset_to_finset.mpr hBI'), 
  sorry, 
  -- this is easy but annoying apparently
  
end


lemma basis.r_eq_r_union (hIX : M.basis I X) (Y : set E) :
  M.r (I ∪ Y) = M.r (X ∪ Y) := 
begin
  refine (M.r_mono (union_subset_union_left _ hIX.subset)).antisymm _, 
  obtain ⟨I', hII', hI'⟩ := 
    hIX.indep.subset_basis_of_subset (hIX.subset.trans (subset_union_left _ Y)), 
  rw [←hI'.r], 
  refine M.r_mono (λ z hz, by_contra (λ hz', _)), 
  rw [mem_union, decidable.not_or_iff_and_not] at hz', 
  have hzX : z ∈ X, {cases (mem_of_mem_of_subset hz hI'.subset); tauto},
  
  have := hIX.eq_of_subset_indep 
    (hI'.indep.subset (insert_subset.mpr ⟨hz,hII'⟩)) 
    (subset_insert z I) (insert_subset.mpr ⟨hzX, hIX.subset⟩), 
  rw [eq_comm, insert_eq_self] at this, 
  exact hz'.1 this, 
end


/--
The submodularity axiom for the rank function
-/
lemma r_inter_add_r_union_le_r_add_r (M : matroid E) (X Y : set E) : 
  M.r (X ∩ Y) + M.r (X ∪ Y) ≤ M.r X + M.r Y :=
begin
  obtain ⟨Ii, hIi⟩ := M.exists_basis (X ∩ Y), 
  obtain ⟨IX, hIX, hIX'⟩ := 
    hIi.indep.subset_basis_of_subset (hIi.subset.trans (inter_subset_left _ _)),  
  obtain ⟨IY, hIY, hIY'⟩ := 
    hIi.indep.subset_basis_of_subset (hIi.subset.trans (inter_subset_right _ _)),  
  rw [←hIX'.r_eq_r_union, union_comm, ←hIY'.r_eq_r_union, ←hIi.card, ←hIX'.card, ←hIY'.card, 
    ←finset.card_inter_add_card_union, ←to_finset_inter, ←to_finset_union, union_comm], 
  refine add_le_add 
    (finset.card_mono (to_finset_subset_to_finset.mpr (subset_inter hIX hIY))) _, 
  convert M.r_le_card (IX ∪ IY), 
end  

lemma r_inj_iff : M₁ = M₂ ↔ ∀ X, M₁.r X = M₂.r X := 
begin
  refine ⟨λ h _, by rw h, λ h, _⟩,
  apply indep_inj_iff.mpr (λ I, _), 
  assumption, 
  simp_rw [indep_iff_r_eq_card,h I],  
end 

end rank 

end matroid 





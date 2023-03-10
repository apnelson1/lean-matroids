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

def exchange_property (basis : set E → Prop) : Prop :=
  ∀ B₁ B₂, basis B₁ → basis B₂ 
    → ∀ (b₁ : E), b₁ ∈ B₁ \ B₂ → ∃ b₂, (b₂ ∈ B₂ \ B₁) ∧ basis (B₁ \ {b₁} ∪ {b₂}) 

@[ext] structure matroid (E : Type*) :=
  (basis : set E → Prop)
  (exists_basis' : ∃ B, basis B) 
  (basis_exchange' : exchange_property basis)

namespace matroid 

lemma exists_basis (M : matroid E) : ∃ B, M.basis B := M.exists_basis'

lemma basis_exchange {M : matroid E} {B₁ B₂ : set E} {x : E} 
(hB₁ : M.basis B₁) (hB₂ : M.basis B₂) (hxB₁ : x ∈ B₁) (hxB₂ : x ∉ B₂) : 
  ∃ y, (y ∈ B₂ ∧ y ∉ B₁) ∧ M.basis (B₁ \ {x} ∪ {y})   := 
M.basis_exchange' B₁ B₂ hB₁ hB₂ x ⟨hxB₁,hxB₂⟩

-- def contains_basis_of (M : matroid E) (B X : set E) := 
--   M.basis B ∧ ∀ B', M.basis B' → B ∩ X ⊆ B' ∩ X → B ∩ X = B' ∩ X

-- def basis_of (M : matroid E) (I X : set E) :=
--   ∃ B, M.contains_basis_of B X ∧ B ∩ X = I

instance {M : matroid E} : nonempty {B // M.basis B} := 
by {obtain ⟨B,hB⟩ := M.exists_basis, exact ⟨⟨B,hB⟩⟩}

variables [fintype E] {B B' B₁ B₂ I I' J I₁ I₂ J' X Y Z : set E} {M M₁ M₂ : matroid E}

-- lemma basis_of_exchange {M : matroid E} {X I₁ I₂: set E} {e₁ : E}
--   (hI₁X : M.basis_of I₁ X) (hI₂X : M.basis_of I₂ X) (he₁ : e₁ ∈ I₁) (he₁' : e₁ ∉ I₂) :
-- ∃ e₂, e₂ ∈ I₂ ∧ e₂ ∉ I₁ ∧ M.basis_of (I₁ \ {e₁} ∪ {e₂}) X :=
-- begin
--   suffices h_mod : ∀ p B₁ B₂ e₁, M.contains_basis_of B₁ X → M.contains_basis_of B₂ X →
--     e₁ ∈ B₁ ∩ X → e₁ ∉ B₂ ∩ X → (B₁ \ B₂).to_finset.card = p → ∃ e₂ ∈ X, e₂ ∈ B₂ ∧ e₂ ∉ B₁ ∧ 
--       M.contains_basis_of (B₁ \ {e₁} ∪ {e₂}) X,
--   { obtain ⟨⟨B₁, hB₁, rfl⟩, ⟨B₂, hB₂, rfl⟩⟩  := ⟨hI₁X, hI₂X⟩, 
--     obtain ⟨e₂, he₂X, he₂B₂, he₂B₁, he₂⟩ := h_mod _ _ _ _ hB₁ hB₂ he₁ he₁' rfl,   
--     refine ⟨e₂, ⟨he₂B₂, he₂X⟩, by simpa using he₂B₁, _⟩,
--     refine ⟨(B₁ \ {e₁} ∪ {e₂}),he₂,_⟩, 
--     sorry},    
  
--   clear hI₁X hI₂X he₁ he₁' e₁ I₁ I₂, 
--   intro p, induction p with p IH, 
--   all_goals {rintros B₁ B₂ e₁ ⟨hB₁,hB₁X⟩ ⟨hB₂,hB₂X⟩ he₁B₁ he₂B₂ hp,},
--   { simp only [set.to_finset_diff, le_zero_iff, finset.card_eq_zero, 
--       finset.sdiff_eq_empty_iff_subset, set.to_finset_subset, set.coe_to_finset] at hp, 
--     exact false.elim (he₂B₂ ⟨set.mem_of_mem_of_subset he₁B₁.1 hp,he₁B₁.2⟩)},
  
  
--   -- obtain ⟨y, ⟨hyB₁, hyB₂⟩, hy⟩ := basis_exchange hB₁ hB₂ he₁B₁.1 sorry, 

--   -- have := IH (B₁ \ {e₁} ∪ {y}) B₂ y sorry ⟨hB₂, hB₂X⟩,  

  
lemma basis.card_eq_card_of_basis (hB₁ : M.basis B₁) (hB₂ : M.basis B₂) :
  B₁.to_finset.card = B₂.to_finset.card := 
begin
  suffices h : ∀ i (B B' : finset E), M.basis B → M.basis B' → (B' \ B).card ≤ i → 
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

  obtain ⟨y, ⟨(hyB : y ∈ B), (hyB' : y ∉ B')⟩, hB''⟩ := basis_exchange hB' hB hxB' hxB, 

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
def indep {E : Type*} (M : matroid E) : set E → Prop := λ I, ∃ B, M.basis B ∧ I ⊆ B   

lemma empty_indep (M : matroid E) : M.indep ∅ := 
  exists.elim M.exists_basis (λ B hB, ⟨_, hB, B.empty_subset⟩)

lemma indep_mono {M : matroid E} {I J : set E} (hIJ : I ⊆ J) (hJ : M.indep J) : M.indep I :=
by {obtain ⟨B, hB, hJB⟩ := hJ, exact ⟨B, hB, hIJ.trans hJB⟩}

lemma indep.subset (hJ : M.indep J) (hIJ : I ⊆ J) : M.indep I :=
by {obtain ⟨B, hB, hJB⟩ := hJ, exact ⟨B, hB, hIJ.trans hJB⟩}

lemma indep_augment (M : matroid E) {I J : set E} (hI : M.indep I) (hJ : M.indep J) 
(hIJ : I.to_finset.card < J.to_finset.card) : 
  ∃ x ∈ J, x ∉ I ∧ M.indep (insert x I) :=
begin
  suffices h_mod : ∀ {p} {I₁ I₂ B₁ B₂}, M.basis B₁ → M.basis B₂ → I₁ ⊆ B₁ → I₂ ⊆ B₂ →
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
      obtain ⟨x,⟨hxB₂, hxB₁⟩, hB'⟩ := basis_exchange hB₁ hB₂ hyB₁ hyB₂,  
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
    simp_rw [finset.card_sdiff_eq_card_sdiff_iff_card_eq_card.mp (hB₁.card_eq_card_of_basis hB₂), 
      ← to_finset_diff, h₁₂, to_finset_diff, ← finset.card_le_card_iff_card_sdiff_le_card_sdiff] 
      at hle₁, 
    exact h_lt.not_le hle₁},
  have h_ne : (B₂ \ (I₂ ∪ B₁)).nonempty, 
  { rw [← set.to_finset_nonempty, ←finset.card_pos, h_le], apply nat.succ_pos _},
  obtain ⟨x, hxB₂, hx'⟩ := h_ne, 
  rw [set.mem_union, not_or_distrib] at hx', obtain ⟨hxI₂, hxB₁⟩:= hx',  
  obtain ⟨y, ⟨hyB₁, hyB₂⟩, hB'⟩ := basis_exchange hB₂ hB₁ hxB₂ hxB₁,  
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

lemma basis.indep (hB : M.basis B) : M.indep B := ⟨B, hB, subset_rfl⟩ 

lemma basis.eq_of_subset_indep (hB : M.basis B) (hI : M.indep I) (hBI : B ⊆ I) : 
  B = I :=
begin
  refine to_finset_inj.mp (finset.eq_of_subset_of_card_le (by simpa) _), 
  obtain ⟨B', hB', hIB'⟩ := hI, 
  rw hB.card_eq_card_of_basis hB', 
  apply finset.card_mono, 
  simpa, 
end 

lemma basis.eq_of_subset_basis (hB₁ : M.basis B₁) (hB₂ : M.basis B₂) (hB₁B₂ : B₁ ⊆ B₂) : 
  B₁ = B₂ :=
hB₁.eq_of_subset_indep (hB₂.indep) hB₁B₂

lemma basis_iff_maximal_indep : M.basis B ↔ M.indep B ∧ ∀ I, M.indep I → B ⊆ I → B = I :=
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
  simp_rw [basis_iff_maximal_indep, hI],  
end 

end indep 

section basis_of

def basis_of {E : Type*} (M : matroid E) (I X : set E) := 
M.indep I ∧ I ⊆ X ∧ ∀ J, M.indep J → I ⊆ J → J ⊆ X → I = J 

lemma indep.subset_basis_of_of_subset (hI₁ : M.indep I₁) (hI₁X : I₁ ⊆ X) : 
  ∃ I, I₁ ⊆ I ∧ M.basis_of I X := 
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

lemma exists_basis_of (M : matroid E) (X : set E) : 
  ∃ I, M.basis_of I X :=
by {obtain ⟨I, -, hI⟩ := M.empty_indep.subset_basis_of_of_subset (empty_subset X), exact ⟨_,hI⟩, }

end basis_of


section rank 
/-- The rank function of a matroid. This is defined in a way that avoids a fintype instance (it is  
zero if `X` is infinite) so as not to carry around data -/
def r {E : Type*} (M : matroid E) : set E → ℕ := 
  λ X, nat.find_greatest (λ n, ∃ I, I ⊆ X ∧ M.indep I ∧ n ≤ nat.card I) (nat.card X)

/-- This is the useful definition of rank -/
lemma eq_r_iff {X : set E} {n : ℕ} : M.r X = n ↔ (∃ I, M.indep I ∧ I ⊆ X ∧ I.to_finset.card = n)
  ∧ (∀ J, M.indep J → J ⊆ X → J.to_finset.card ≤ n) := 
begin
  simp_rw [matroid.r, nat.find_greatest_eq_iff, nat.card_eq_to_finset_card], 
  split, 
  { rintros ⟨hn_le, h1, h2⟩,
    push_neg at h2, 
    cases n, 
    { refine ⟨⟨∅, ⟨M.empty_indep,empty_subset _,by simp⟩⟩,λ J hJ hJX, _ ⟩,  
      refine (nat.eq_zero_or_pos J.to_finset.card).elim (by simp) (λ hpos, false.elim _),
      have := h2 hpos (by {apply finset.card_mono, simpa using hJX }) _ hJX hJ,
      exact this.ne rfl}, 
    obtain ⟨I, hIX, hI, hnI⟩ := h1 (nat.succ_ne_zero _), 
    obtain ⟨I', hI'I, hI'⟩ :=  I.to_finset.exists_smaller_set _ hnI, 
    rw [subset_to_finset] at hI'I, 
    refine ⟨⟨I',hI.subset hI'I,hI'I.trans hIX, by simpa ⟩ , λ J hJ hJX, le_of_not_lt (λ hJ', _)⟩,
    have := h2 hJ' (by {apply finset.card_mono, simpa using hJX}) J hJX hJ,  
    simpa using this},
  rintros ⟨⟨ I, hI, hIX, rfl⟩, h⟩, 
  refine ⟨finset.card_mono (by simpa using hIX), λ hI0,⟨I, hIX, hI, rfl.le⟩, _ ⟩ ,  
  rintros n hIn hnle ⟨J,hJX, hJ, hnJ⟩,   
  exact hnJ.not_lt ((h J hJ hJX).trans_lt hIn), 
end 

lemma le_r_iff {X : set E} {n : ℕ} : n ≤ M.r X ↔ ∃ I, M.indep I ∧ I ⊆ X ∧ n ≤ I.to_finset.card :=
begin
  obtain ⟨⟨J, hJ, hJX, hJcard⟩, hmax⟩ := eq_r_iff.mp (@rfl ℕ (M.r X)), 
  refine ⟨λ h, _,λ h, _⟩, 
  {  exact ⟨J, hJ, hJX, h.trans_eq hJcard.symm⟩},
  obtain ⟨I, hI, hIX, hnI⟩ := h, 
  exact hnI.trans (hmax I hI hIX), 
end    

lemma r_le_iff {X : set E} {n : ℕ} : 
  M.r X ≤ n ↔ ∀ I, M.indep I → I ⊆ X → I.to_finset.card ≤ n :=
begin
  obtain ⟨⟨J, hJ, hJX, hJcard⟩, hmax⟩ := eq_r_iff.mp (@rfl ℕ (M.r X)), 
  refine ⟨λ h I hI hIX, (hmax I hI hIX).trans h,λ h, _⟩, 
  rw ← hJcard, 
  exact h J hJ hJX, 
end 

lemma r_indep (hI : M.indep I) : 
  M.r I = I.to_finset.card := 
eq_r_iff.mpr ⟨⟨_,hI,subset_refl _,rfl⟩,λ J hJ hJI, finset.card_mono (by simpa)⟩

lemma indep_iff_r_eq_card : M.indep I ↔ M.r I = I.to_finset.card := 
begin
  refine ⟨r_indep,λ h, _⟩, 
  obtain ⟨J, hJ, hJI, hJcard⟩ := le_r_iff.mp h.symm.le, 
  suffices hIJ : J = I, rwa ←hIJ, 
  rw ← to_finset_inj, 
  apply finset.eq_of_subset_of_card_le _ hJcard,
  simpa, 
end 

lemma r_empty (M : matroid E) : 
  M.r ∅ = 0 :=
by rw [r_indep M.empty_indep, to_finset_empty, finset.card_empty] 

lemma r_le_card (M : matroid E) (X : set E) : 
  M.r X ≤ X.to_finset.card :=
r_le_iff.mpr (λ I hI hIX, finset.card_mono (by simpa))

lemma r_mono (M : matroid E) {X Y : set E} (hXY : X ⊆ Y) : 
  M.r X ≤ M.r Y :=
begin
  simp_rw [r_le_iff, le_r_iff], 
  exact λ I hI hIX, ⟨I,hI,hIX.trans hXY,rfl.le⟩, 
end  

lemma r_inter_add_r_union_le_r_add_r (M : matroid E) (X Y : set E) : 
  M.r (X ∩ Y) + M.r (X ∪ Y) ≤ M.r X + M.r Y :=
begin
  
  sorry, 
end  


-- end 





end rank 

end matroid 





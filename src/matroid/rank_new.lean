import order.complete_lattice
import tactic 
import set_theory.cardinal.finite

-- import matroid.axioms

noncomputable theory 
open_locale classical 

variables {E : Type*}

-- def exists_basis (basis : set E → Prop) : Prop :=
--   ∃ B, basis B

def exchange_property (basis : set E → Prop) : Prop :=
  ∀ B₁ B₂, basis B₁ → basis B₂ 
    → ∀ (b₁ : E), b₁ ∈ B₁ \ B₂ → ∃ b₂, (b₂ ∈ B₂ \ B₁) ∧ basis (B₁ \ {b₁} ∪ {b₂}) 

@[ext] structure matroid (E : Type*) :=
  (basis : set E → Prop)
  (exists_basis' : ∃ B, basis B) 
  (basis_exchange' : exchange_property basis)

namespace matroid 

lemma exists_basis (M : matroid E) : ∃ B, M.basis B := M.exists_basis'

lemma basis_exchange (M : matroid E) {B₁ B₂ : set E} {x : E} (hB₁ : M.basis B₁) (hB₂ : M.basis B₂) 
(hxB₁ : x ∈ B₁) (hxB₂ : x ∉ B₂) : 
  ∃ y, (y ∈ B₂ ∧ y ∉ B₁) ∧ M.basis (B₁ \ {x} ∪ {y})   := 
M.basis_exchange' B₁ B₂ hB₁ hB₂ x ⟨hxB₁,hxB₂⟩

variables [fintype E]

lemma finset.exists_mem_diff_of_card_lt_card {A B : finset E} (h : A.card < B.card) : 
  ∃ e, e ∈ B ∧ e ∉ A :=
begin
  refine by_contra (λ h', h.not_le (finset.card_mono (λ x hx, _))), 
  push_neg at h', 
  exact h' _ hx, 
end  

lemma card_eq_card_of_basis (M : matroid E) {B₁ B₂ : set E} (hB₁ : M.basis B₁) (hB₂ : M.basis B₂) :
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

  obtain ⟨y, ⟨(hyB : y ∈ B), (hyB' : y ∉ B')⟩, hB''⟩ := M.basis_exchange hB' hB hxB' hxB, 

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


def indep (M : matroid E) : set E → Prop := λ I, ∃ B, M.basis B ∧ I ⊆ B   

lemma empty_indep (M : matroid E) : M.indep ∅ := 
  exists.elim M.exists_basis (λ B hB, ⟨_, hB, B.empty_subset⟩)

lemma indep_mono (M : matroid E) {I J : set E} (hIJ : I ⊆ J) (hJ : M.indep J) : M.indep I :=
by {obtain ⟨B, hB, hJB⟩ := hJ, exact ⟨B, hB, hIJ.trans hJB⟩}

lemma indep_augment (M : matroid E) {I J : set E} (hI : M.indep I) (hJ : M.indep J) 
(hIJ : nat.card I < nat.card J) : 
  ∃ x ∈ J, x ∉ I ∧ M.indep (insert x I) :=
begin
  obtain ⟨BI, hBI, hIBI⟩ := hI, 
  obtain ⟨BJ, hBJ, hIBJ⟩ := hJ, 
end 


-- def r (M : matroid E) : set E → ℕ := 
--   @supr ℕ _ {I // M.indep I} (λ I, nat.card (I : set E))
  






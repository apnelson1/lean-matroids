import order.complete_lattice
import tactic 
import set_theory.cardinal.finite

-- import matroid.axioms

noncomputable theory 
open_locale classical 

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



def contains_basis_of (M : matroid E) (B X : set E) := 
  M.basis B ∧ ∀ B', M.basis B' → B ∩ X ⊆ B' ∩ X → B ∩ X = B' ∩ X

def basis_of (M : matroid E) (I X : set E) :=
  ∃ B, M.contains_basis_of B X ∧ B ∩ X = I

instance {M : matroid E} : nonempty {B // M.basis B} := 
by {obtain ⟨B,hB⟩ := M.exists_basis, exact ⟨⟨B,hB⟩⟩}

variables [fintype E]

lemma exists_basis_of (M : matroid E) (X : set E) : 
  ∃ I, M.basis_of I X :=
begin
  set card_int :=  (λ B, (B ∩ X).to_finset.card) with hci, 
  set bases := {B : set E | M.basis B}.to_finset with h_bases, 
  obtain ⟨B, hB⟩ := M.exists_basis, 
  obtain ⟨B₀, hB₀, hmax⟩ := 
  finset.exists_mem_eq_sup bases
    (by {rw set.to_finset_nonempty, exact ⟨B,hB⟩}) card_int, 
  
  refine ⟨B₀ ∩ X, B₀, ⟨by simpa [h_bases] using hB₀,λ B' hB' hhB', _ ⟩, rfl⟩, 
  have hhB' := @finset.le_sup _ _ _ _ _ card_int B' (by simpa : B' ∈ bases) , 
  simp_rw [hmax, hci] at hhB', 
  have := finset.eq_of_subset_of_card_le (by rwa set.to_finset_subset_to_finset) hhB',
  apply set.to_finset_inj.mp this, 
end 

lemma basis_of_exchange {M : matroid E} {X I₁ I₂: set E} {e₁ : E}
  (hI₁X : M.basis_of I₁ X) (hI₂X : M.basis_of I₂ X) (he₁ : e₁ ∈ I₁) (he₁' : e₁ ∉ I₂) :
∃ e₂, e₂ ∈ I₂ ∧ e₂ ∉ I₁ ∧ M.basis_of (I₁ \ {e₁} ∪ {e₂}) X :=
begin
  suffices h_mod : ∀ p B₁ B₂ e₁, M.contains_basis_of B₁ X → M.contains_basis_of B₂ X →
    e₁ ∈ B₁ ∩ X → e₁ ∉ B₂ ∩ X → (B₁ \ B₂).to_finset.card = p → ∃ e₂ ∈ X, e₂ ∈ B₂ ∧ e₂ ∉ B₁ ∧ 
      M.contains_basis_of (B₁ \ {e₁} ∪ {e₂}) X,
  { obtain ⟨⟨B₁, hB₁, rfl⟩, ⟨B₂, hB₂, rfl⟩⟩  := ⟨hI₁X, hI₂X⟩, 
    obtain ⟨e₂, he₂X, he₂B₂, he₂B₁, he₂⟩ := h_mod _ _ _ _ hB₁ hB₂ he₁ he₁' rfl,   
    refine ⟨e₂, ⟨he₂B₂, he₂X⟩, by simpa using he₂B₁, _⟩,
    refine ⟨(B₁ \ {e₁} ∪ {e₂}),he₂,_⟩, 
    sorry},    
  
  clear hI₁X hI₂X he₁ he₁' e₁ I₁ I₂, 
  intro p, induction p with p IH, 
  all_goals {rintros B₁ B₂ e₁ ⟨hB₁,hB₁X⟩ ⟨hB₂,hB₂X⟩ he₁B₁ he₂B₂ hp,},
  { simp only [set.to_finset_diff, le_zero_iff, finset.card_eq_zero, 
      finset.sdiff_eq_empty_iff_subset, set.to_finset_subset, set.coe_to_finset] at hp, 
    exact false.elim (he₂B₂ ⟨set.mem_of_mem_of_subset he₁B₁.1 hp,he₁B₁.2⟩)},
  
  
  -- obtain ⟨y, ⟨hyB₁, hyB₂⟩, hy⟩ := basis_exchange hB₁ hB₂ he₁B₁.1 sorry, 

  -- have := IH (B₁ \ {e₁} ∪ {y}) B₂ y sorry ⟨hB₂, hB₂X⟩,  

  
end 

lemma finset.exists_mem_diff_of_card_lt_card {A B : finset E} (h : A.card < B.card) : 
  ∃ e, e ∈ B ∧ e ∉ A :=
begin
  refine by_contra (λ h', h.not_le (finset.card_mono (λ x hx, _))), 
  push_neg at h', 
  exact h' _ hx, 
end  

@[simp] lemma finset.card_inter_add_card_sdiff_eq_card (S T : finset E) : 
  (S ∩ T).card + (S \ T).card = S.card :=
by {convert @finset.card_sdiff_add_card_eq_card _ _ _ S _; simp}

lemma card_eq_card_of_basis {M : matroid E} {B₁ B₂ : set E} (hB₁ : M.basis B₁) (hB₂ : M.basis B₂) :
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









def indep (M : matroid E) : set E → Prop := λ I, ∃ B, M.basis B ∧ I ⊆ B   

lemma empty_indep (M : matroid E) : M.indep ∅ := 
  exists.elim M.exists_basis (λ B hB, ⟨_, hB, B.empty_subset⟩)

lemma indep_mono {M : matroid E} {I J : set E} (hIJ : I ⊆ J) (hJ : M.indep J) : M.indep I :=
by {obtain ⟨B, hB, hJB⟩ := hJ, exact ⟨B, hB, hIJ.trans hJB⟩}

lemma indep_augment (M : matroid E) {I J : set E} (hI : M.indep I) (hJ : M.indep J) 
(hIJ : I.to_finset.card < J.to_finset.card) : 
  ∃ x ∈ J, x ∉ I ∧ M.indep (insert x I) :=
begin
  
  suffices h_mod : ∀ p (I I' B B' : finset E), 
    M.basis B → M.basis B' → I ⊆ B → I' ⊆ B' → I.card < I'.card → (B \ B').card ≤ p 
    → ∃ y, y ∈ I' ∧ y ∉ I ∧ M.indep (insert y I), 
  { obtain ⟨BI, hBI, hIBI⟩ := hI, obtain ⟨BJ, hBJ, hJBJ⟩ := hJ, 
    simpa using h_mod _ I.to_finset J.to_finset BI.to_finset BJ.to_finset (by simpa)
      (by simpa) (by simpa) (by simpa) hIJ rfl.le},
  
  clear hI hJ hIJ I J, 

  intro p, induction p with p IH, 
  all_goals {intros I I' B B' hB hB' hIB hIB' hcard hp}, 
  { simp only [le_zero_iff, finset.card_eq_zero, 
      finset.sdiff_eq_empty_iff_subset] at hp,
    obtain ⟨y,hyI',hyI⟩ := finset.exists_mem_diff_of_card_lt_card hcard, 
    refine ⟨y, hyI', hyI, ⟨B', hB', set.insert_subset.mpr ⟨_,_⟩⟩⟩,  
    { exact set.mem_of_mem_of_subset hyI' hIB'},
    { exact hIB.trans hp, }},
  
  have : ∃ z, z ∈ B 
  -- have hI_lt_B : I.card < B.card, sorry, 
  -- obtain ⟨z, hz⟩ := finset.exists_mem_diff_of_card_lt_card hI_lt_B, 
  -- have := basis_exchange hB hB' hz.1, 

  

  
  -- suffices h_mod : ∀ p (I' J' : finset E) (hI' : M.indep I') (hJ' : M.indep J'),
  --   I'.card < J'.card → (J' \ I').card ≤ p → ∃ y, y ∈ J' ∧ y ∉ I' ∧ M.indep (insert y I'), 
  -- { simpa using h_mod _ I.to_finset J.to_finset (by simpa) (by simpa) hIJ rfl.le  },
  -- clear hI hJ hIJ I J, 
  -- intro p, induction p with p IH, 
  -- { exact λ _ _ _ _ hIJ hJI, 
  --   (hIJ.not_le (finset.card_mono (by simpa using hJI))).elim, }, 
  -- intros I J hI hJ hIJ hcard, 
  
  -- obtain ⟨BI, hBI, hIBI⟩ := hI, 
  -- obtain ⟨BJ, hBJ, hIBJ⟩ := hJ, 

  -- have hIB : I.card < BI.to_finset.card,
  -- { sorry },
  -- -- { linarith [card_eq_card_of_basis hBI hBJ, 
  -- --   finset.card_mono (set.to_finset_subset_to_finset.mpr hIBJ)]},

  -- obtain ⟨x,hxJ, hxI⟩ := finset.exists_mem_diff_of_card_lt_card hIB, 


  -- by_contradiction h_aug, push_neg at h_aug, 

  -- have hdj : disjoint (BI \ I) J, sorry, 
  -- have hdsd : BI \ I ⊆ BJ \ J, 
  -- { intros x hx, 
  --   by_contradiction hx', 
  --   simp only [set.mem_diff, not_and, set.not_not_mem] at hx hx', 
  --   have hxBJ : x ∉ BJ, from 
  --     λ h'', h_aug x (hx' h'') hx.2 ⟨BI, hBI, set.insert_subset.mpr ⟨hx.1,hIBI⟩⟩,
  --   obtain ⟨y, ⟨hyBJ,hyBI⟩, hB⟩  := basis_exchange hBI hBJ hx.1 hxBJ, 

       
  -- have hIB : I.to_finset.card < BI.to_finset.card,
  -- { linarith [card_eq_card_of_basis hBI hBJ, 
  --   finset.card_mono (set.to_finset_subset_to_finset.mpr hIBJ)]},
  

  -- have hy : ∃ y ∈ BI, y ∉ I ∧ y ∉ BJ, 
  -- { by_contradiction h, push_neg at h, 
    
  --   },
  -- -- obtain ⟨y, hyBI, hyI⟩ := finset.exists_mem_diff_of_card_lt_card hIB,
  
  -- rw [set.mem_to_finset] at hyBI hyI, 



  -- have := basis_exchange hBI hBJ (by simpa using hyBI : y ∈ BI), 
end 


-- def r (M : matroid E) : set E → ℕ := 
--   @supr ℕ _ {I // M.indep I} (λ I, nat.card (I : set E))
  






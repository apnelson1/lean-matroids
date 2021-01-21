/-
Question: is weak induction enough to prove strong induction?
Answer: yes!
-/

import order.bounded_lattice  -- For the has_empt / has_top notation classes.
import .basic .single .int_lemmas 
----------------------------------------------------------------
open_locale classical 
noncomputable theory 


namespace ftype 
-- The operations needed on the ftype A.

variables {A: ftype}

/-- P holds for all proper subsets of Y-/
def below (P : set A → Prop) (Y : set A) : Prop :=
  forall (X :  set A), X ⊂ Y → (P X)

/-- if P holds for all proper subsets of Y, it holds for Y-/
def augment (P : set A → Prop) : Prop :=
  forall (Y : set A), (below P Y) → (P Y)

lemma strong_induction (P : set A → Prop) :
  (augment P) → (forall (Z : set A), P Z) :=
begin
  intros h_augment, 
  let  Q : ℤ → Prop := λ n, ∀ Y : set A, size Y = n → P Y,
  suffices : ∀ n, 0 ≤ n → Q n,  
  from λ Z, this (size Z) (size_nonneg _)  Z rfl, 
  refine nonneg_int_strong_induction Q _ _,
  
  intros Y hY, rw [size_zero_iff_empty] at hY, rw hY, 
  refine h_augment _ _, 
  from λ X hX, false.elim (ssubset_empty _ hX), 
  intros n h0n hn X hXn, 
  refine h_augment _ _,
  intros Y hY, 
  refine hn (size Y) (size_nonneg Y) _ Y rfl, 
  rw ←hXn, 
  from size_strict_monotone hY, 
end

lemma minimal_example (P : set A → Prop){X : set A}: 
  (P X) → ∃ Y, Y ⊆ X ∧ P Y ∧ ∀ Z, Z ⊂ Y → ¬P Z := 
  begin
    set minimal_P := λ (Y : set A), P Y ∧ ∀ (Z : set A), Z ⊂ Y → ¬ P Z with hmin, 
    revert X, refine strong_induction _ _, intros T hT hPT, 
    by_cases ∀ Z, Z ⊂ T → ¬P Z, use T, exact ⟨subset_refl T, ⟨hPT, h⟩⟩, 
    push_neg at h, rcases h with ⟨Z, ⟨hZT, hPZ⟩⟩, 
    specialize hT Z hZT hPZ, rcases hT with ⟨Y, ⟨hYZ, hQY⟩⟩, 
    use Y, exact ⟨subset_trans hYZ hZT.1, hQY⟩, 
  end

lemma maximal_example (P : set A → Prop){X : set A}: 
  (P X) → ∃ Y, X ⊆ Y ∧ P Y ∧ ∀ Z, Y ⊂ Z → ¬P Z := 
  begin
    intro h, rw ←compl_compl X at h, 
    rcases minimal_example (λ S, P Sᶜ) h with ⟨Y,⟨hY₁, hY₂, hY₃⟩⟩, 
    use Yᶜ, refine ⟨subset_compl_right hY₁, hY₂,λ Z hZ, _⟩,  
    rw ←compl_compl Z, exact hY₃ Zᶜ (ssubset_compl_left hZ), 
  end

lemma maximal_example_from_empty (P : set A → Prop): 
  P ∅ → ∃ Y, P Y ∧ ∀ Z, Y ⊂ Z → ¬P Z := 
  λ h, by {rcases maximal_example P h with ⟨Y, ⟨_,h'⟩⟩, from ⟨Y,h'⟩  }

lemma maximal_example_aug (P : set A → Prop){X : set A}: 
  (P X) → ∃ Y, X ⊆ Y ∧ P Y ∧ ∀ (e : A), e ∉ Y → ¬P (Y ∪ e) := 
  begin
    intro hPX, 
    rcases maximal_example P hPX with ⟨Y, ⟨hXY, ⟨hPY, hmax⟩⟩⟩, 
    from ⟨Y, ⟨hXY, ⟨hPY, λ e he, hmax (Y ∪ e) (ssub_of_add_nonelem he) ⟩⟩⟩,  
  end 

lemma maximal_example_aug_from_empty (P : set A → Prop): 
  P ∅ → ∃ Y, P Y ∧ ∀ (e : A), e ∉ Y → ¬P (Y ∪ e) := 
  λ h, by {rcases maximal_example_aug P h with ⟨Y, ⟨_,h'⟩⟩, from ⟨Y,h'⟩}

lemma minimal_example_remove (P : set A → Prop){X : set A}: 
  (P X) → ∃ Y, Y ⊆ X ∧ P Y ∧ ∀ (e : A), e ∈ Y → ¬P (Y \ e) := 
  begin
    intro hPX, 
    rcases minimal_example P hPX with ⟨Y, ⟨hXY, ⟨hPY, hmin⟩⟩⟩, 
    from ⟨Y, ⟨hXY, ⟨hPY, λ e he, hmin (Y \ e) (remove_single_ssubset he) ⟩⟩⟩,  
  end 

/-lemma minimal_example_size (P : set A → Prop)(hP : set.nonempty P):
  ∃ X, P X ∧ ∀ Y, size Y < size X → ¬ P Y := 
begin
  by_contra h, push_neg at h, 
end-/




end ftype 
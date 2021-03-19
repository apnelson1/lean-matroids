import .induction .size 

universes u v w

variables {α : Type*} [fintype α]
open set 

lemma induction_set_size_remove (P : set α → Prop) : 
  (P ∅) → (∀ (X : set α) (e : X), P (X \ {e}) → P X) → (∀ X, P X) := 
begin
  intros h0 h, 
  refine nonneg_int_strong_induction_param P size (size_nonneg) (λ X hX, _) (λ X hX hX', _ ), 
  { convert h0, apply empty_of_size_zero hX}, 
  rcases size_pos_iff_has_mem.mp hX with ⟨e,he⟩, 
  exact h X ⟨e,he⟩ (hX' (X \ {e}) (by linarith [size_remove_mem he])), 
end

lemma induction_set_size_add (P : set α → Prop) : 
  (P ∅) → (∀ (X : set α) (e : α), e ∉ X → P X → P (X ∪ {e})) → (∀ X, P X) :=
begin
  intros h0 h, 
  refine nonneg_int_strong_induction_param P size 
    (size_nonneg) 
    (λ X hX, _) 
    (λ X hX hX', _ ), 
  { convert h0, apply empty_of_size_zero hX}, 
  rcases size_pos_iff_has_mem.mp hX with ⟨e,he⟩, 
  convert h (X \ {e}) e _ (hX' _ _);
  simp [remove_union_mem_singleton he, int.zero_lt_one,size_remove_mem he], 
end

lemma induction_set_size_insert (P : set α → Prop) : 
  (P ∅) → (∀ (X : set α) (e : α), e ∉ X → P X → P (insert e X)) → (∀ X, P X) :=
begin
  intros h0 h, 
  refine nonneg_int_strong_induction_param P size 
    (size_nonneg) 
    (λ X hX, _) 
    (λ X hX hX', _ ), 
  { convert h0, apply empty_of_size_zero hX}, 
  rcases size_pos_iff_has_mem.mp hX with ⟨e,he⟩, 
  convert h (X \ {e}) e _ (hX' _ _);
  simp [remove_union_mem_singleton he, int.zero_lt_one,size_remove_mem he, insert_eq_of_mem he], 
end


/-- P holds for all proper subsets of Y-/
def below (P : set α → Prop) (Y : set α) : Prop :=
  forall (X :  set α), X ⊂ Y → (P X)

/-- if P holds for all proper subsets of Y, it holds for Y-/
def augment (P : set α → Prop) : Prop :=
  forall (Y : set α), (below P Y) → (P Y)

lemma strong_induction (P : set α → Prop) :
  (augment P) → (forall (Z : set α), P Z) :=
begin
  intros h_augment, 
  let  Q : ℤ → Prop := λ n, ∀ Y : set α, size Y = n → P Y,
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

lemma minimal_example (P : set α → Prop){X : set α} : 
  (P X) → ∃ Y, Y ⊆ X ∧ P Y ∧ ∀ Z, Z ⊂ Y → ¬P Z := 
begin
  set minimal_P := λ (Y : set α), P Y ∧ ∀ (Z : set α), Z ⊂ Y → ¬ P Z with hmin, 
  revert X, refine strong_induction _ _, intros T hT hPT, 
  by_cases ∀ Z, Z ⊂ T → ¬P Z, use T, exact ⟨subset_refl T, ⟨hPT, h⟩⟩, 
  push_neg at h, rcases h with ⟨Z, ⟨hZT, hPZ⟩⟩, 
  specialize hT Z hZT hPZ, rcases hT with ⟨Y, ⟨hYZ, hQY⟩⟩, 
  use Y, exact ⟨subset.trans hYZ hZT.1, hQY⟩, 
end

lemma maximal_example (P : set α → Prop){X : set α} : 
  (P X) → ∃ Y, X ⊆ Y ∧ P Y ∧ ∀ Z, Y ⊂ Z → ¬P Z := 
begin
  intro h, rw ←compl_compl X at h, 
  rcases minimal_example (λ S, P Sᶜ) h with ⟨Y,⟨hY₁, hY₂, hY₃⟩⟩, 
  use Yᶜ, refine ⟨subset_compl_comm.mpr hY₁, hY₂,λ Z hZ, _⟩,  
  rw ←compl_compl Z, exact hY₃ Zᶜ (ssubset_compl_commm.mp hZ), 
end

lemma maximal_example_from_empty (P : set α → Prop) : 
  P ∅ → ∃ Y, P Y ∧ ∀ Z, Y ⊂ Z → ¬P Z := 
  λ h, by {rcases maximal_example P h with ⟨Y, ⟨_,h'⟩⟩, from ⟨Y,h'⟩  }

lemma maximal_example_aug (P : set α → Prop){X : set α} : 
  (P X) → ∃ Y, X ⊆ Y ∧ P Y ∧ ∀ (e : α), e ∉ Y → ¬P (Y ∪ {e}) := 
begin
  intro hPX, 
  rcases maximal_example P hPX with ⟨Y, ⟨hXY, ⟨hPY, hmax⟩⟩⟩, 
  from ⟨Y, ⟨hXY, ⟨hPY, λ e he, hmax (Y ∪ {e}) (ssub_of_add_nonmem he) ⟩⟩⟩,  
end 

lemma maximal_example_aug_from_empty (P : set α → Prop) : 
  P ∅ → ∃ Y, P Y ∧ ∀ (e : α), e ∉ Y → ¬P (Y ∪ {e}) := 
  λ h, by {rcases maximal_example_aug P h with ⟨Y, ⟨_,h'⟩⟩, from ⟨Y,h'⟩}

lemma minimal_example_remove (P : set α → Prop){X : set α} : 
  (P X) → ∃ Y, Y ⊆ X ∧ P Y ∧ ∀ (e : α), e ∈ Y → ¬P (Y \ {e}) := 
begin
  intro hPX, 
  rcases minimal_example P hPX with ⟨Y, ⟨hXY, ⟨hPY, hmin⟩⟩⟩, 
  from ⟨Y, ⟨hXY, ⟨hPY, λ e he, hmin (Y \ {e}) (ssubset_of_remove_mem he) ⟩⟩⟩,  
end 

/-lemma minimal_example_size (P : set α → Prop) (hP : set.nonempty P) :
  ∃ X, P X ∧ ∀ Y, size Y < size X → ¬ P Y := 
begin
  by_contra h, push_neg at h, 
end-/

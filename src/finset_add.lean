import tactic data.finset

namespace finset 
variables {α : Type*} {β : Type*} [decidable_eq α]



 def size (A: finset α) := (card A: ℤ)

 lemma union_subset_union_left {s₁ s₂ : finset α} (t) (h : s₁ ⊆ s₂): s₁ ∪ t ⊆ s₂ ∪ t := 
    begin
        intros x hx ,
        simp,
        simp at hx,
        cases hx,
        left,
        exact h hx,
        right,
        exact hx,
    end

    lemma eq_ss {A B E: finset α}: (A ⊆ E) → (A = B)  → (B ⊆ E) :=
    begin
        finish [finset.subset_iff],
    end

    lemma ss_eq {A E E': finset α}: (A ⊆ E) → (E = E') → (A ⊆ E') := 
    begin
        intros h h',
        rw ← h',
        exact h,
    end

    lemma comp_int (X E: finset α): (X ∩ (E \ X)) = ∅ := sorry

    lemma card_comp {X E: finset α}: (X ⊆ E) → (card X + card (E \ X) = card E) :=
    begin
      have := finset.card_union_add_card_inter X (E \ X),
      sorry,
    end

    lemma finset_eq {A B: finset α}: (A = B) ↔ ((∀ x ∈ A, x ∈ B) ∧ (∀ x ∈ B, x ∈ A)) := 
    begin
      split, 
      intros h,
      rw h,
      split,
      finish,
      finish,
      rintros ⟨h1, h2⟩,
      apply finset.subset.antisymm_iff.mpr,
      split,
      intros a ha,
      exact h1 a ha,
      intros b hb,
      exact h2 b hb,
    end
    
    lemma em_ss {E : finset α}: ∅ ⊆ E :=
    begin
        exact empty_subset E,
    end 

    def inter_subset {A B E: finset α} (hA : A ⊆ E) (hB : B ⊆ E) := subset.trans (inter_subset_left A B) hA

    lemma finset_card (A B : finset α): (card A: ℤ )  + (card B :ℤ )  = (card (A ∪ B) : ℤ )  + (card (A ∩ B) : ℤ ) :=
    begin
      sorry,
    end

    lemma sdiff_tel {E X Y : finset α} : (X ⊆ Y) → (Y ⊆ E) → (E \ Y ) ∪ (Y \ X) = (E \ X) := 
    begin
      intros hXY hYE,
      sorry,
    end

    lemma size_empt : size (∅ : finset α) = 0 := sorry

    
    lemma maximal_ss (S: finset α)(C ⊆ powerset S)(hempt: ∅ ∈ C): ∃ X ∈ C, (∀ Y ∈ powerset S, X ⊂ Y → ¬ Y ∈ C) := 
    begin
      sorry,
    end

    lemma minimal_ss (S: finset α)(C ⊆ powerset S)(h_full : S ∈ C): ∃ X ∈ C, (∀ Y ∈ powerset S, Y ⊂ X → ¬ Y ∈ C) := 
    begin
      sorry,
    end

    lemma maximal_ss_property (S: finset α){P: finset α → Prop}(hempt: P ∅): ∃ (X ⊆ S), P X ∧ (∀ Y ⊆ S, X ⊂ Y → ¬ (P Y)) := 
    begin
      sorry,
    end

    lemma minimal_ss_property (S: finset α){P: finset α → Prop}(hfull: P S): ∃ (X ⊆ S), P X ∧ (∀ Y ⊆ S, Y ⊂ X → ¬ (P Y)) := 
    begin
      sorry,
    end

    lemma extends_to_maximal_property (S: finset α){X₀ : finset α}{P: finset α → Prop}(hempt: P X₀): ∃ (X ⊆ S), (X₀ ⊆ X) ∧ (P X) ∧ (∀ Y ⊆ S, X ⊂ Y → ¬ (P Y)) := 
    begin
      sorry,
    end

    @[simp] lemma m0 {E: finset α}{e : α} : e ∈ E → {e} ⊆ E := (singleton_subset_iff.symm).mp 

    example {E: finset α}{e : α} : e ∈ E → {e} ⊆ E :=
    begin
      simp, 
    end


end finset 

/-namespace finset
/- For mathlib? -/
lemma inter_of_subset {A B : finset α} (h : A ⊆ B) : A ∩ B = A :=
    sorry

lemma subset_iff_sdiff_eq_empty {x y : finset α} : x ⊆ y ↔ x \ y = ∅ :=
by simp only [sdiff_eq_filter, eq_empty_iff_forall_not_mem, subset_iff, not_and,
  not_not, finset.mem_filter]

lemma empty_sdiff (E : finset α): E \ ∅ = E :=
    sorry

lemma sdiff_subset (A B : finset α): A \ B ⊆ A :=
(empty_sdiff A).subst $ sdiff_subset_sdiff (subset.refl A) $ empty_subset B

lemma sdiff_eq_sdiff_inter (A B : finset α) : A \ B = A \ (A ∩ B) :=
by { simp only [ext, not_and, mem_sdiff, mem_inter],
  exact λ a, iff.intro (λ h, ⟨h.1, λ x, h.2⟩) (λ h, ⟨h.1, h.2 h.1⟩) }

lemma card_eq_inter_sdiff (A B : finset α) : card A = card (A ∩ B) + card (A \ B) :=
begin
  have hA : A \ B ∪ A ∩ B = A := by { simp only [ext, mem_union, union_comm, mem_sdiff, mem_inter],
    exact λ a, iff.intro (λ ha, or.elim ha (λ H, H.1) (λ H, H.1))
      (by { intro ha, by_cases h : a ∈ B, { exact or.inl ⟨ha, h⟩ }, { exact or.inr ⟨ha, h⟩ } }) },
  have : disjoint (A \ B) (A ∩ B) := by simp only [disjoint, empty_subset, inf_eq_inter,
    inter_empty, sdiff_inter_self, inter_left_comm, le_iff_subset],
  replace this := card_disjoint_union this, rwa [hA, add_comm] at this
end

lemma card_sdiff_eq (A B : finset α) : card (A \ B) = card A - card (A ∩ B) :=
(nat.sub_eq_of_eq_add $ card_eq_inter_sdiff A B).symm

lemma card_union_inter (A B : finset α) : card A + card B = card (A ∪ B) + card (A ∩ B) :=
begin
  have hBA : card B = card (B \ A) + card (A ∩ B) := inter_comm B A ▸
    (add_comm (card (B ∩ A)) (card (B \ A))) ▸ (card_eq_inter_sdiff B A),
  have Hdis : disjoint A (B \ A) := by simp only [disjoint, empty_subset, inf_eq_inter,
    inter_sdiff_self, le_iff_subset],
  have H : card A + card (B \ A) = card (A ∪ B) :=
    (congr_arg card $ union_sdiff_self_eq_union.symm).substr (card_disjoint_union Hdis).symm,
  calc
  card A + card B = card A + card (B \ A) + card (A ∩ B) : by rw [add_assoc, hBA]
  ... = card (A ∪ B) + card (A ∩ B) : by rw H
end

/- proof by Kenny Lau https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/subject/choosing.20from.20difference.20of.20finsets/near/133624012 -/
lemma exists_sdiff_of_card_lt {x y : finset α} (hcard : card x < card y) : ∃ e : α, e ∈ y \ x :=
suffices ∃ e ∈ y, e ∉ x, by simpa only [exists_prop, finset.mem_sdiff],
by_contradiction $ λ H, not_le_of_lt hcard $ card_le_of_subset $ by simpa only [not_exists,
  exists_prop, not_and, not_not] using H

/- proof by chris hughes
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/subject/maximal.20finset.20in.20finset.20of.20finsets/near/133905271 -/
lemma max_fun_of_ne_empty {F : finset β} (func : β → ℕ) (h : F ≠ ∅) :
  ∃ x ∈ F, ∀ g ∈ F, func g ≤ func x :=
let ⟨n, hn⟩ := (max_of_ne_empty (mt image_eq_empty.1 h) : ∃ a, a ∈ finset.max (F.image func)) in
let ⟨x, hx₁, hx₂⟩ := mem_image.1 (mem_of_max hn) in
  ⟨x, hx₁, hx₂.symm ▸ λ g hg, le_max_of_mem (mem_image.2 ⟨g, hg, rfl⟩) hn⟩

lemma min_fun_of_ne_empty {F : finset β} (func : β → ℕ) (h : F ≠ ∅) :
  ∃ x ∈ F, ∀ g ∈ F, func x ≤ func g :=
let ⟨n, hn⟩ := (min_of_ne_empty $ mt image_eq_empty.1 h : ∃ a, a ∈ finset.min (F.image func)) in
let ⟨x, hx₁, hx₂⟩ := mem_image.1 (mem_of_min hn) in
  ⟨x, hx₁, hx₂.symm ▸ λ g hg, min_le_of_mem (mem_image.2 ⟨g, hg, rfl⟩) hn⟩

section inst

variables {F : finset α} {Q : finset α → Prop} [decidable_pred Q] {P : α → Prop} [decidable_pred P]

instance decidable_not_forall (c₁ : finset (finset α)) :
  decidable (∃ x : finset α, ¬(x ∈ c₁ → ¬Q x)) :=
decidable_of_iff (∃ x ∈ c₁, Q x) $ by simp only [exists_prop, not_forall_not]

instance decidable_exists_and_mem : decidable (∃ e, e ∈ F ∧ P e) :=
decidable_of_iff (∃ e ∈ F, P e) $ by simp only [exists_prop, not_forall_not]

end inst

end finset

open finset-/
--set_option pp.implicit true -/
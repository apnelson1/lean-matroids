import tactic data.finset
open_locale classical

namespace finset




variables {α : Type*} {β : Type*} [decidable_eq α]

def size{β : Type*} (X: finset β) := ((card X) : ℤ)

def subset_fintype{β: Type*} (hβ : fintype β) (X: finset β) := fintype


@[simp] lemma empt_size{β : Type*} : size (∅ : finset β) = 0 :=
begin
    sorry,
end

@[simp] lemma partition_univ {β : Type*} [fintype β] (X: finset β) : X ∪ Xᶜ = univ :=
begin
    apply subset.antisymm,
    exact subset_univ _,
    intros x hx,
    simp only [mem_union],
    by_cases x ∈ X,
    left,
    exact h,
    right,
    rw compl_eq_univ_sdiff,
    apply mem_sdiff.mpr,
    split,
    exact hx,
    exact h,
    --yuck....
end

@[simp] lemma size_subtype{β : Type*} {Y: set β} {X : finset Y} : size (X.image subtype.val)  = size X :=
begin
    unfold size,
    simp only [int.coe_nat_inj'],
    apply card_image_of_injective,
    exact subtype.val_injective
end


lemma union_subset_union_left{A B C : finset α} : (A ⊆ B) → ((A ∪ C) ⊆ (B ∪ C)) :=
begin
    intros hAB,
    intros x hx,
    simp only [mem_union],
    simp only [mem_union] at hx,
    cases hx,
    left,
    exact hAB hx,
    right,
    exact hx,
end

@[simp] lemma union_unions{X Y A: finset α} :(X ∪ A) ∪ (Y ∪ A) = (X ∪ Y ∪ A) :=
begin
    sorry,
end

@[simp] lemma inter_unions{X Y A: finset α} :(X ∪ A) ∩ (Y ∪ A) = (X ∩ Y) ∪ A :=
begin
    sorry,
end

end finset 
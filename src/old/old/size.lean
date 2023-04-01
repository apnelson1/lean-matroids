import data.fintype.basic
import data.set
import data.finset
import tactic

noncomputable theory
localized "attribute [instance, priority 100000] classical.prop_decidable
  noncomputable theory" in classical
open_locale classical
open finset

universes u
variables {γ : Type u}

def size (X : finset γ) := (coe X.card : ℤ)
def type_size (γ : Type u) [fintype γ] := (coe (fintype.card γ) : ℤ)

lemma size_empty : size (∅:finset γ) = 0 :=
begin
    unfold size, simp,
end
lemma size_le_of_subset {s t: finset γ} (h : s ⊆ t) : size(s) ≤ size(t) :=
begin
    unfold size, simp, exact card_le_of_subset h
end
lemma size_sdiff {s t : finset γ} (h : s ⊆ t) : size (t \ s) = size t - size s :=
begin
    sorry,
end
lemma size_modular (s t : finset γ) : size s + size t = size (s ∪ t) + size (s ∩ t) :=
begin
    sorry,
end
@[simp] lemma size_map {α β} (f : α ↪ β) {s : finset α} : size (s.map f) = size s :=
begin
    simp,
end
lemma size_compl [decidable_eq γ] [fintype γ] (s : finset γ) :
  size(sᶜ) = type_size γ - size s :=
begin
    sorry
end

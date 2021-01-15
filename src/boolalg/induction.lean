/-
Question: is weak induction enough to prove strong induction?
Answer: yes!
-/

import order.bounded_lattice  -- For the has_bot / has_top notation classes.
import .basic .single 
----------------------------------------------------------------
local attribute [instance] classical.prop_decidable

noncomputable theory 


namespace boolalg 
-- The operations needed on the boolalg A.

variables {A: boolalg}

def singlet (e : A) := (size e = 1)  -- The property of being a singleton.

/-
subset_singlet is the crucial property, and should be provable as a
consequence of the fact that singletons have size 1 and there are no
integers between 0 and 1.
-/

lemma subset_singlet (X e : A) : (singlet e) → (X ⊆ e) → (X = ⊥ ∨ X = e) := sorry

lemma subset_dec_eq (X Y : A) : (X ⊆ Y) → (X = Y) ∨ (X ≠ Y) := sorry

----------------------------------------------------------------

section weak_induction

/-
A formulation of weak induction, which crawls up the poset,
singleton by singleton. Provable from the axiom that every
nonempty subset of the boolalg contains a singleton.
-/
lemma weak_induction (P : A → Prop) :
  (P ⊥) →  -- Base case.
  (forall (e Y : A), (singlet e) → (P Y) → P (e ∪ Y)) →  -- Induction step.
  (forall (Z : A), P Z) :=
sorry

end /-section-/ weak_induction

----------------------------------------------------------------

section strong_induction

-- (below P Y) says that property P is true everywhere strictly below Y.
def below (P : A → Prop) (Y : A) : Prop :=
  forall (X : A), (X ⊂ Y) → (P X)

-- (augment P) says that (below P Y) can be upgraded to (P Y), for all Y.
def augment (P : A → Prop) : Prop :=
  forall (Y : A), (below P Y) → (P Y)

-- The statement of strong induction, specialized to a single position in the boolalg.
def strong_at (Y : A) : Prop :=
  forall (P : A → Prop), (augment P) → (P Y)

/-
The crucial part of the proof that weak induction implies strong induction.

Consider the subalg of elements below Y, and the subalg of elements below (e ∪ Y).
Because of subset_singlet, we know that (subalg (e ∪ Y)) is covered by two
copies of (subalg Y): the elements of the form X ⊆ Y, and the elements of
the form (e ∪ X) for X ⊆ Y.

So, we package up the pair of propositions (P X) and (P (e ∪ X)) as a new
proposition on (subalg Y), and call it (Q X).

This will allow us to use strong induction at position Y, for Q, to prove
that strong induction works at position (e ∪ Y), for P.
-/
lemma pair_up (P : A → Prop) (e : A) : (singlet e) →
  let Q : (A → Prop) := fun Y, (P Y) ∧ P (e ∪ Y) in
  (augment P) → (augment Q) :=
fun h_singlet h_augment Y h_below,
/-
First use (augment P) to upgrade (below P Y) to (P Y).
The fact that (below Q Y) implies (below P Y) is almost immediate.
-/
let h_Y : (P Y) := h_augment Y (fun X h_ssu , and.left (h_below X h_ssu)) in
and.intro h_Y
/-
Then use (augment P) to upgrade (below P (e ∪ Y)) to (P (e ∪ Y)).
The fact that (below Q Y) implies (below P (e ∪ Y)) is *not* immediate.
There are three cases to consider:

1. Elements of the form X ⊆ Y with X ≠ Y:
   (P X) is directly implied by (Q X).

2. The element Y:
   we proved above that (augment P) works to prove (P Y).

3. Elements of the form (e ∪ X) with X ⊆ Y and X ≠ Y:
   (P (e ∪ X)) is directly implied by (Q X).
-/
(h_augment (e ∪ Y) (fun X h_ssu,
-- Break up X ⊆ (e ∪ Y) into the part under e and the part under Y.
let h_union :=
  calc X = X ∩ (e ∪ Y)       : (subset_def_inter_mp h_ssu.1).symm 
  ...    = (X ∩ e) ∪ (X ∩ Y) : by rw ←inter_distrib_left
in or.elim (subset_dec_eq (X ∩ Y) Y (inter_subset_right X Y))
(or.elim (subset_singlet (X ∩ e) e h_singlet (inter_subset_right X e))
  -- Case 2 described above: X = Y.
  (fun (h₁ : X ∩ e = ⊥) (h₂ : X ∩ Y = Y),
    @eq.rec A Y P h_Y X (
    calc Y = X ∩ Y             : h₂.symm
    ...    = ⊥ ∪ (X ∩ Y)       : (bot_union (X ∩ Y)).symm
    ...    = (X ∩ e) ∪ (X ∩ Y) : by rw [h₁]
    ...    = X                 : h_union.symm))
  -- Case impossible, because X ≠ (e ∪ Y)
  (fun (h₁ : X ∩ e = e) (h₂ : X ∩ Y = Y),
    false.elim (h_ssu.2 (
    calc X = (X ∩ e) ∪ (X ∩ Y) : h_union
    ...    = e ∪ Y             : by rw [h₁, h₂]))))
(or.elim (subset_singlet (X ∩ e) e h_singlet (inter_subset_right X e))
  -- Case 1 described above: X ⊂ Y.
  (fun (h₁ : X ∩ e = ⊥) (h₂ : X ∩ Y ≠ Y),
    let h₃ :=
      calc X = (X ∩ e) ∪ (X ∩ Y) : h_union
      ...    = ⊥ ∪ (X ∩ Y)       : by rw [h₁]
      ...    = X ∩ Y             : bot_union (X ∩ Y)
    in and.left (h_below X ⟨(subset_def_inter_mpr h₃.symm),(by {rw h₃, exact h₂} : X ≠ Y)⟩))
  -- Case 3 described above: X = e ∪ X' with X' ⊂ Y.
  (fun (h₁ : X ∩ e = e) (h₂ : X ∩ Y ≠ Y),
    @eq.rec A (e ∪ (X ∩ Y)) P
    (and.right (h_below (X ∩ Y) (⟨(inter_subset_right X Y), h₂⟩)))
    X (
    calc e ∪ (X ∩ Y) = (X ∩ e) ∪ (X ∩ Y) : by rw [h₁]
    ...              = X                 : h_union.symm))))
)


/-
Strong induction works at position ⊥, vacuously.
-/
lemma strong_base :
  strong_at (⊥ :A) :=
fun P aug, aug ⊥ (fun X h_ssu, false.elim (h_ssu.2 (subset_bot h_ssu.1)))

/-
As explained above, strong induction at position Y
implies strong induction at position (e ∪ Y).
-/
lemma strong_step (e Y : A) :
  (singlet e) → (strong_at Y) → (strong_at (e ∪ Y)) :=
fun h_singlet h_strong P h_augment,
let Q : (A → Prop) := fun Y, (P Y) ∧ P (e ∪ Y) in
and.right (h_strong Q (pair_up P e h_singlet h_augment))

/-
So weak induction implies strong induction at every position.
-/
lemma strong_induction (P : A → Prop) :
  (augment P) → (forall (Z : A), P Z) :=
fun h_augment Z, weak_induction strong_at strong_base strong_step Z P h_augment

lemma minimal_example (P : A → Prop){X : A}: 
  (P X) → ∃ Y, Y ⊆ X ∧ P Y ∧ ∀ Z, Z ⊂ Y → ¬P Z := 
  begin
    set minimal_P := λ (Y : A), P Y ∧ ∀ (Z : A), Z ⊂ Y → ¬ P Z with hmin, 
    revert X, refine strong_induction _ _, intros T hT hPT, 
    by_cases ∀ Z, Z ⊂ T → ¬P Z, use T, exact ⟨subset_refl T, ⟨hPT, h⟩⟩, 
    push_neg at h, rcases h with ⟨Z, ⟨hZT, hPZ⟩⟩, 
    specialize hT Z hZT hPZ, rcases hT with ⟨Y, ⟨hYZ, hQY⟩⟩, 
    use Y, exact ⟨subset_trans hYZ hZT.1, hQY⟩, 
  end

lemma maximal_example (P : A → Prop){X : A}: 
  (P X) → ∃ Y, X ⊆ Y ∧ P Y ∧ ∀ Z, Y ⊂ Z → ¬P Z := 
  begin
    intro h, rw ←compl_compl X at h, 
    rcases minimal_example (λ S, P Sᶜ) h with ⟨Y,⟨hY₁, hY₂, hY₃⟩⟩, 
    use Yᶜ, refine ⟨subset_compl_right hY₁, hY₂,λ Z hZ, _⟩,  
    rw ←compl_compl Z, exact hY₃ Zᶜ (ssubset_compl_left hZ), 
  end

lemma maximal_example_from_bot (P : A → Prop): 
  P ⊥ → ∃ Y, P Y ∧ ∀ Z, Y ⊂ Z → ¬P Z := 
  λ h, by {rcases maximal_example P h with ⟨Y, ⟨_,h'⟩⟩, from ⟨Y,h'⟩  }

lemma maximal_example_aug (P : A → Prop){X : A}: 
  (P X) → ∃ Y, X ⊆ Y ∧ P Y ∧ ∀ e, e ∉ Y → ¬P (Y ∪ e) := 
  begin
    intro hPX, 
    rcases maximal_example P hPX with ⟨Y, ⟨hXY, ⟨hPY, hmax⟩⟩⟩, 
    from ⟨Y, ⟨hXY, ⟨hPY, λ e he, hmax (Y ∪ e) (ssub_of_add_nonelem he) ⟩⟩⟩,  
  end 

lemma maximal_example_aug_from_bot (P : A → Prop): 
  P ⊥ → ∃ Y, P Y ∧ ∀ e, e ∉ Y → ¬P (Y ∪ e) := 
  λ h, by {rcases maximal_example_aug P h with ⟨Y, ⟨_,h'⟩⟩, from ⟨Y,h'⟩}

lemma minimal_example_remove (P : A → Prop){X : A}: 
  (P X) → ∃ Y, Y ⊆ X ∧ P Y ∧ ∀ e, e ∈ Y → ¬P (Y \ e) := 
  begin
    intro hPX, 
    rcases minimal_example P hPX with ⟨Y, ⟨hXY, ⟨hPY, hmin⟩⟩⟩, 
    from ⟨Y, ⟨hXY, ⟨hPY, λ e he, hmin (Y \ e) (remove_single_ssubset he) ⟩⟩⟩,  
  end 

end /-section-/ strong_induction


section int_induction

lemma int_induction_strong (P : ℤ → Prop) : 
  P 0 → (∀ k, 0 ≤ k → (∀ k', 0 ≤ k' → k' < k → P k') → P k) → (∀ n, n ≥ 0 → P n) := 
begin
  intros h0 hk n hn, 
  set Q: ℕ → Prop := λ n, P n with hQ,
  suffices hQn : Q (n.to_nat), sorry, 
   
end

end int_induction



end boolalg 
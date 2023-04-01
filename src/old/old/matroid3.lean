import data.fintype.basic
import data.set
import data.finset
import tactic
import size

noncomputable theory
localized "attribute [instance, priority 100000] classical.prop_decidable
  noncomputable theory" in classical
open_locale classical
open finset

universes u v

@[ext]
structure matroid (γ : Type u) [fintype γ] :=
(r : finset γ → ℤ)
(R0 : ∀ (X : finset γ ), 0 ≤ r X)
(R1 : ∀ (X : finset γ), r X ≤ size X)
(R2 : ∀ {X Y : finset γ}, X ⊆ Y → r X ≤ r Y)
(R3 : ∀ (X Y : finset γ), r (X ∪ Y) + r (X ∩ Y) ≤ r X + r Y)

/-
type mismatch at application
  size X
term
  X
has type
  finset γ : Type u
but is expected to have type
  finset ?m_1 : Type
All Messages (115)
-/

namespace matroid
variables {γ : Type u} [fintype γ] (M : matroid γ)

abbreviation E (M : matroid γ) : finset γ := univ

@[simp]
lemma r_empty_eq_zero : M.r ∅ = 0 := 
by linarith [(M.R0 ∅), (M.R1 ∅), @size_empty γ]

@[simp]
lemma r_univ_compl_eq_zero : M.r M.Eᶜ = 0 :=
by { convert M.r_empty_eq_zero, convert_to ⊤ᶜ = _, simp only [compl_top], refl }

@[simp] lemma subset_E (X : finset γ) : X ⊆ M.E :=
subset_univ X

lemma r_subadditive (X Y : finset γ) : M.r (X ∪ Y) ≤ M.r X + M.r Y :=
by
  linarith [(M.R0 (X ∩ Y)), (M.R1 (X ∩ Y)), (M.R3 X Y)]

lemma r_le_union (X Y : finset γ) : M.r X ≤ M.r (X ∪ Y) :=
by { apply R2, apply subset_union_left }

lemma r_le_union_right (X Y : finset γ) : M.r Y ≤ M.r (X ∪ Y) :=
by { rw union_comm, apply r_le_union }

lemma r_compl (X : finset γ) : M.r M.E ≤ M.r X + M.r Xᶜ :=
begin
  convert M.R3 X Xᶜ,
  suffices h1 : X ∪ Xᶜ = univ,
  suffices h2 : X ∩ Xᶜ = ∅,
  rw [h1, h2, r_empty_eq_zero], simp,
  simp [compl_eq_univ_sdiff],
  simp [compl_eq_univ_sdiff, subset_univ],
end

lemma corank_le (M : matroid γ) (X : finset γ) : M.r M.E - M.r Xᶜ ≤ size X :=
begin
  have hxc := M.R2 (M.subset_E Xᶜ),
  have h1 := M.r_compl X,
  have h2 := M.R1 X,
  omega,
end

/--
The dual matroid
-/
def dual (M : matroid γ) : matroid γ :=
{ r := λ X, size X + M.r Xᶜ - M.r M.E,
  R0 := λ X, begin
    linarith [r_compl M X, M.R1 X],
  end,
  R1 := λ X,
  begin
    have h : M.r Xᶜ ≤ M.r M.E := M.R2 (subset_univ _),
    linarith,
  end,
 
  R2 := λ X Y hXY, begin
    -- want to show: |X| + r(E \ X) < |Y| + r(E \ Y)
    have YsetminusX : size (Y \ X) = size Y - size X,
    { exact size_sdiff hXY },
    have YC : Yᶜ ∪ (Y \ X) = Xᶜ ,
    { sorry },
    have rYC : M.r(Yᶜ ∪ (Y \ X)) = M.r(Xᶜ),
    { rw YC },
    linarith [(r_subadditive M Yᶜ (Y \ X)), M.R1 (Y \ X)],
  end,
  R3 := λ X Y, begin
    -- linarith [M.R3 Xᶜ Yᶜ, size_modular X Y],
    sorry,
  end }

end matroid
/--
A "submatroid" is the matroid restricted to a subset then contracted.
The rank function is then meant to be for subsets of `E` that contain
`F`.
-/


@[ext] structure minor {γ : Type u} [fintype γ] (M : matroid γ) :=
(C : finset γ)
(D : finset γ)
(H : C ∩ D = ∅)

namespace minor
variables {γ : Type u} [fintype γ] {M : matroid γ}
def r (M' : minor M) (X : finset γ) : ℤ := M.r (X ∪ M'.C) - M.r M'.C --This allows rank-evaluations of sets intersecting C ∪ D - maybe this is ok.

lemma R0 (M' : minor M) (X : finset γ) : 0 ≤ M'.r X :=
begin
  sorry
end

lemma R1 (M' : minor M) (X : finset γ) : M'.r X ≤ size X :=
begin
  sorry
end

lemma R2 (M' : minor M) {X Y : finset γ} (hX : X ⊆ Y) : M'.r X ≤ M'.r Y :=
begin
  sorry
end

lemma R3 (M' : minor M) (X Y : finset γ) : M'.r (X ∪ Y) + M'.r (X ∩ Y) ≤ M'.r X + M'.r Y :=
begin
  sorry
end


def to_matroid (M' : minor M) : matroid (↑(M.E \ M'.C \ M'.D) : set γ) :=
{ r := λ X, M'.r (X.map (function.embedding.subtype _)),
  R0 := λ X, M'.R0 (X.map (function.embedding.subtype _)),
  R1 := λ X, by { rw ← size_map, apply M'.R1 },
  R2 := λ X Y hs, M'.R2 (map_subset_map.mpr hs),
  R3 := λ X Y, by { rw [map_union, map_inter], apply M'.R3 } }
@[simp]
def delete (M' : minor M) (D' : finset γ) (H : D' ∩ (M'.C ∪ M'.D) = ∅) : minor M :=
{ C := M'.C , D := D' ∪ M'.D, H :=
begin
  have := M'.H,
  sorry,
end,
}
@[simp]
def contract (M' : minor M) (C': finset γ) (H: C' ∩ (M'.C ∪ M'.D) = ∅) : minor M :=
{ C := C' ∪ M'.C, D := M'.D, H := sorry,
}


def dual (M' : minor M) : minor M.dual :=
{ C := M'.D,
  D := M'.C,
  H := calc M'.D ∩ M'.C = M'.C ∩ M'.D : inter_comm M'.D M'.C ... = ∅ : M'.H,
}

instance : has_top (minor M) :=
{ top := { C := ∅, D := ∅, H := by tidy } }

end minor


@[ext]
structure submatroid {γ : Type u} [fintype γ] (M : matroid γ) :=
(E : finset γ)
(F : finset γ)
(F_sub : F ⊆ E . obviously)

namespace submatroid
variables {γ : Type u} [fintype γ] {M : matroid γ}


def r (M' : submatroid M) (X : finset γ) : ℤ := M.r (X ∪ M'.F) - M.r M'.F

lemma R1 (M' : submatroid M) (X : finset γ) : M'.r X ≤ size X :=
begin
  dunfold r,
  have h1 := M.R1 X,
  have h2 := M.r_subadditive X M'.F,
  omega,
end

lemma R2 (M' : submatroid M) {X Y : finset γ} (hX : X ⊆ Y) : M'.r X ≤ M'.r Y :=
begin
  dunfold r,
  have hX' : X ∪ M'.F ⊆ Y ∪ M'.F,
  { intro x, simp only [mem_union], intro h, cases h,
    left, exact hX h,
    right, exact h, },
  have h1 := M.R2 hX',
  omega,
end

lemma R3 (M' : submatroid M) (X Y : finset γ) : M'.r (X ∪ Y) + M'.r (X ∩ Y) ≤ M'.r X + M'.r Y :=
begin
  dunfold r,
  have h1 := M.R3 (X ∪ M'.F) (Y ∪ M'.F),
  have ha : X ∪ M'.F ∪ (Y ∪ M'.F) = X ∪ Y ∪ M'.F,
  { rw [union_assoc, union_assoc X Y], congr' 1,
    rw [union_comm, union_assoc], simp, },
  rw ha at h1,
  have hb : (X ∪ M'.F) ∩ (Y ∪ M'.F) = (X ∩ Y) ∪ M'.F,
  { rw union_distrib_right, },
  rw hb at h1,
  have h2 := M.r_le_union_right Y M'.F,
  have h3 := M.r_le_union_right X M'.F,
  have h4 := M.r_le_union_right (X ∪ Y) M'.F,
  have h5 := M.r_le_union_right (X ∩ Y) M'.F,
  omega,
end

def to_matroid (M' : submatroid M) : matroid (↑M'.E : set γ) :=
{ r := λ X, M'.r (X.map (function.embedding.subtype _)),
  R0 := sorry,
  R1 := λ X, by { rw ← size_map, apply M'.R1 },
  R2 := λ X Y hs, M'.R2 (map_subset_map.mpr hs),
  R3 := λ X Y, by { rw [map_union, map_inter], apply M'.R3 } }

instance : has_top (submatroid M) :=
{ top := { E := univ, F := ∅ } }

instance : has_bot (submatroid M) :=
{ bot := { E := ∅, F := ∅ } }

/--
Delete all of `D` from the given submatroid.
`D` is allowed have elements outside of `M'.E`.
To delete from a matroid `M`, there is also the definition `M.delete D`
to get a `submatroid M`.
-/
@[simp]
def delete (M' : submatroid M) (D : finset γ) : submatroid M :=
{ E := M'.E \ D, F := M'.F \ D,
  F_sub := begin
    intro x, simp only [and_imp, mem_sdiff],
    intros xel xnel, use M'.F_sub xel,
  end }

/--
Contract the elements of `C`.  `C` is allowed to have elements outside of `M'.E`.
-/
@[simp]
def contract (M' : submatroid M) (C : finset γ) : submatroid M :=
{ E := M'.E ∪ C, F := M'.F ∪ C,
  F_sub := begin
    intro x, simp only [mem_union], intro h',
    cases h', exact or.inl (M'.F_sub h'), exact or.inr h',
  end }

/--
This is a lemma that seems to be missing from mathlib. (Using a lazy proof for now.)
-/
lemma sdiff_sdiff_eq_sdiff_union (s t u : finset γ) : s \ t \ u = s \ (t ∪ u) :=
begin
  ext x, simp, push_neg, tidy,
end

lemma delete_delete_eq_delete (M' : submatroid M) (F F' : finset γ) :
  (M'.delete F).delete F' = M'.delete (F ∪ F') :=
begin
  ext1,
  repeat { dsimp [delete], apply sdiff_sdiff_eq_sdiff_union, },
end

lemma contract_contract_eq_contract (M' : submatroid M) (F F' : finset γ) :
  (M'.contract F).contract F' = M'.contract (F ∪ F') :=
begin
  ext, simp [contract], simp [contract],
end

def dual (M' : submatroid M) : submatroid M.dual :=
{ E := M.E \ M'.F,
  F := M.E \ M'.E,
  F_sub := begin
    intro x,
    simp only [true_and, mem_sdiff, mem_univ],
    contrapose, push_neg, intro h, exact M'.F_sub h,
  end }

lemma dual_contract (M' : submatroid M) (D : finset γ) :
  (M'.contract D).dual = M'.dual.delete D :=
begin
  ext, repeat { dsimp [contract, delete, dual], rw sdiff_sdiff_eq_sdiff_union, },
end

lemma dual_delete (M' : submatroid M) (D : finset γ) :
  (M'.delete D).dual = M'.dual.contract D :=
begin
  ext,
  dsimp [contract, delete, dual],
  simp only [true_and, mem_union, not_and, mem_sdiff, mem_univ, not_not],
  split,
  intro h', by_cases h'' : a ∈ M'.F, exact or.inr (h' h''), exact or.inl h'',
  intro h', cases h', cc, cc,
  dsimp [contract, delete, dual],
  simp only [true_and, mem_union, not_and, mem_sdiff, mem_univ, not_not],
  split,
  intro h', by_cases h'' : a ∈ M'.E, exact or.inr (h' h''), exact or.inl h'',
  intro h', cases h', cc, cc,
end

end submatroid

namespace matroid
variables {γ : Type u} [fintype γ]

/--
Deletion from a matroid, yielding a submatroid.
-/
def delete (M : matroid γ) (F : finset γ) : submatroid M :=
(⊤ : submatroid M).delete F

def contract (M : matroid γ) (F : finset γ) : submatroid M :=
(⊤ : submatroid M).contract F


@[simp] lemma dual_E_eq (M : matroid γ) : M.dual.E = M.E := rfl
@[simp] lemma dual_r_eq (M : matroid γ) (X : finset γ) : M.dual.r X = size X + M.r Xᶜ - M.r M.E := rfl

lemma dual_dual_eq (M : matroid γ) : M.dual.dual = M :=
begin
  ext X,
  change size X + M.dual.r Xᶜ - M.dual.r M.dual.E = M.r X,
  rw dual_E_eq, rw [dual_r_eq, dual_r_eq], simp [size_compl],
  have hh : type_size γ  = size M.E := begin sorry end,
  have h1 := M.R1 X, have h2 := M.R1 M.E,
  have h3 := M.subset_E X, have h4 := M.R2 h3,
  have h5 := size_le_of_subset h3,
  linarith,
end

@[simp]
def mdelete (M : matroid γ) (F : finset γ) : minor M :=
  { C := ∅, D := F, H := empty_inter F }

@[simp]
def mcontract (M : matroid γ) (F : finset γ) : minor M :=
  { C := F, D := ∅, H := inter_empty F }

lemma cd_rank_equal (M : matroid γ) (X : finset γ) : (delete M X).dual.r =
  (contract M.dual X).r :=
begin
  sorry,
end

lemma cd_matroid_equal (M : matroid γ) (X : finset γ) : (delete M X).dual== (contract M.dual X) :=
begin
  sorry,
end

--lemma something {C: finset γ} {D: finset γ} (h: C ∩ D = ∅) : D ∩ C = ∅ :=


def make_minor (M : matroid γ) (C D : finset γ) (h : C ∩ D = ∅) : minor M :=
  { C := C, D := D, H := h }

lemma mdelete_D (M : matroid γ) (D : finset γ) : (M.mdelete D).D = D := rfl

lemma clear_emptl {C D : finset γ} (h : C ∩ D = ∅) : C ∩ (∅ ∪ D) = ∅ := by tidy
lemma clear_emptr {C D : finset γ} (h : C ∩ D = ∅) : D ∩ (C ∪ ∅) = ∅ := sorry


lemma cd_eq_dc (M: matroid γ) (C: finset γ) (D: finset γ) (h: C ∩ D = ∅) :
  (minor.contract (mdelete M D) C (clear_emptl h)) =
  (minor.delete (mcontract M C) D (clear_emptr h)) :=
by apply minor.ext; simp


lemma cd_eq_dc_m (M: matroid γ) (C: finset γ) (D: finset γ) (h: C ∩ D = ∅) :
  minor.to_matroid (minor.contract (mdelete M D) C (clear_emptl h)) ==
  minor.to_matroid (minor.delete (mcontract M C) D (clear_emptr h)) := by rw cd_eq_dc

variables M : matroid γ
variables C D : finset γ
lemma cd_eq_dc_dual (M : matroid γ)  (C D : finset γ ) (h : C ∩ D = ∅) :
  (make_minor M C D h).dual = M.dual.make_minor D C (sorry : D ∩ C = ∅) :=
  begin
    unfold make_minor, tidy,
  end
lemma cd_eq_dc_dual_m (M : matroid γ)  (C D : finset γ ) (h : C ∩ D = ∅) :
(make_minor M C D h).dual.to_matroid = (M.dual.make_minor D C (sorry : D ∩ C = ∅)).to_matroid :=
begin
  unfold make_minor, tidy,
end

lemma dual_minors_r (M : matroid γ) (M' : minor M) :
  M'.dual.to_matroid.r == M'.to_matroid.dual.r :=
begin
  unfold minor.to_matroid,
  unfold minor.dual,
  unfold matroid.dual,
  simp,
  ext,
  tidy,
  have h: {x // x ∉ M'.C ∧ x ∉ M'.D} = {x // x ∉ M'.dual.C ∧ x ∉ M'.dual.D},
    apply congr_arg subtype,
    apply funext,
    intro x,
    apply propext,
    split,
    intro h,
    split,
    exact h.2,
    exact h.1,
    intro h,
    split,
    exact h.2,
    exact h.1,
rw h,   
-- we r here nao
   
end

lemma dual_minors (M : matroid γ) (M' : minor M) :
  M'.dual.to_matroid == M'.to_matroid.dual :=
begin
  unfold minor.to_matroid,
  unfold minor.dual,
  unfold matroid.dual,


end

  /- (M \ D /  C)* = M* / D \ C -/
/-
{C := ∅, D := D, H := _}.contract C _).C = ({C := C, D := ∅, H := _}.delete D _).C
-/
/-
⊢ a ∈ ((M.mdelete D).contract C _).C ↔ a ∈ ((M.mcontract C).delete D _).C
γ: Type u
_inst_1: fintype γ
M: matroid γ
CD: finset γ
h: C ∩ D = ∅
a: γ
⊢ a ∈ ((M.mdelete D).contract C _).D ↔ a ∈ ((M.mcontract C).delete D _).D
-/


end matroid

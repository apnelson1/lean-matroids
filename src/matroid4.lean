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

-- A concrete matroid
@[ext]
structure matroid_on (γ : Type u) (finite : fintype γ) :=
    (r : finset γ → ℤ)
    (R0 : ∀ (X : finset γ), 0 ≤ r X)
    (R1 : ∀ (X : finset γ), r X ≤ size X)
    (R2 : ∀ {X Y : finset γ}, X ⊆ Y → r X ≤ r Y)
    (R3 : ∀ (X Y : finset γ), r (X ∪ Y) + r (X ∩ Y) ≤ r X + r Y)

-- Packing the matroid with the ground type
structure matroid :=
    (γ : Type u)
    [class_finite : fintype γ]
    [class_compl : has_compl (finset γ)]
    [class_algebra : boolean_algebra (finset γ)]
    [class_top : has_top (finset γ)]
    (mat : matroid_on γ class_finite)

/--
Type with matroids interpretations (for example matroid minors) may implement
this to get access to the `↟` coercion arrow.  (Note: this is getting
around a problem with `has_coe` class resolution where universe
variables do not seem to be inferrable.)

See simple_graphs2 for where this came from.
-/
class has_coe_to_matroid (α : Type u) :=
(coe : α → matroid.{v})

/-
If only `has_coe` could infer the universe variables, this wouldn't be needed.
-/
notation `↟`:max x:max := has_coe_to_matroid.coe x

instance (γ: Type u) [finite : fintype γ]: 
    has_coe_to_matroid (matroid_on γ finite) :=
    ⟨λ G, ⟨γ, G⟩⟩

section accessor_functions
namespace matroid
variables (M : matroid)

abbreviation E (M : matroid) : finset M.γ := @univ M.γ M.class_finite
abbreviation r (M : matroid) : finset (γ M) → ℤ := M.mat.r 
abbreviation R0 (M : matroid) := M.mat.R0
abbreviation R1 (M : matroid) := M.mat.R1
abbreviation R2 (M : matroid) := M.mat.R2
abbreviation R3 (M : matroid) := M.mat.R3

@[simp]
lemma r_empty_eq_zero : M.r ∅ = 0 :=
by linarith [(M.R0 ∅), (M.R1 ∅), @size_empty M.γ]

#check has_top.top 
@[simp]
lemma r_univ_compl_eq_zero : M.r (@compl (finset M.γ) M.class_compl M.E) = 0 := 
begin
    have : (E M) = @has_top.top (finset M.γ) M.class_algebra, {
        
    }
end

@[simp] lemma subset_E (X : finset M.γ) : X ⊆ M.E := @subset_univ M.γ M.class_finite X

lemma r_subadditive (X Y : finset M.γ) : M.r (X ∪ Y) ≤ M.r X + M.r Y :=
by
  linarith [(M.R0 (X ∩ Y)), (M.R1 (X ∩ Y)), (M.R3 X Y)]

lemma r_le_union (X Y : finset M.γ) : M.r X ≤ M.r (X ∪ Y) :=
by { apply R2, apply subset_union_left }

lemma r_le_union_right (X Y : finset M.γ) : M.r Y ≤ M.r (X ∪ Y) :=
by { rw union_comm, apply r_le_union }

lemma r_compl (X : finset M.γ) : M.r M.E ≤ M.r X + M.r Xᶜ :=
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
end accessor_functions

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
  (mat : @matroid_on γ class_finite)

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

namespace matroid_on
variables {γ : Type u} [finite : fintype γ] (M : matroid_on γ finite)
abbreviation E (M : matroid_on γ finite) : finset γ := univ

@[simp]
lemma r_empty_eq_zero: M.r ∅ = 0 :=  
by linarith [(M.R0 ∅), (M.R1 ∅), @size_empty γ]

@[simp]
lemma r_univ_compl_eq_zero : M.r M.Eᶜ = 0 :=
by { convert M.r_empty_eq_zero, convert_to ⊤ᶜ = _, simp only [compl_top], refl }
end matroid_on

namespace matroid
variables (M : matroid)

abbreviation r := M.mat.r
abbreviation E := @matroid_on.E M.γ M.class_finite M.mat

@[simp] def r_eq_empty_zero :=
  let γ := M.γ,
      finite := M.class_finite in
    @matroid_on.r_empty_eq_zero γ finite M.mat
#check r_eq_empty_zero

/- note that the typechecking doesn't work here -/
@[simp] def r_univ_compl_eq_zero /- : M.mat.r M.mat.Eᶜ = 0 -/ :=
  let γ := M.γ,
    finite := M.class_finite in
    @matroid_on.r_univ_compl_eq_zero γ finite M.mat
#check r_univ_compl_eq_zero

/-- if we want a nicer type -/
structure struct_r_univ_compl_eq_zero :=
  (finite : fintype M.γ)
  (term : M.r M.Eᶜ = 0)
@[simp] def nice_r_univ_compl_eq_zero :=
  let γ := M.γ,
    finite := M.class_finite in  
  struct_r_univ_compl_eq_zero.term (struct_r_univ_compl_eq_zero.mk finite (r_univ_compl_eq_zero M))
#check nice_r_univ_compl_eq_zero

end matroid
import data.fintype.basic
import data.set
import data.finset
import tactic
import finset_extra

noncomputable theory
localized "attribute [instance, priority 100000] classical.prop_decidable
  noncomputable theory" in classical
open_locale classical
open finset


universes u v

structure matroid_on (γ : Type u) :=
(fin_cert: fintype γ)
(r : finset γ → ℤ)
(R1 : ∀ (X : finset γ), 0 ≤ r X ∧ r X ≤ size X)
(R2 : ∀ {X Y : finset γ}, X ⊆ Y → r X ≤ r Y)
(R3 : ∀ (X Y : finset γ), r (X ∪ Y) + r (X ∩ Y) ≤ r X + r Y)

class matroids (α : Type v)  :=
(γ : α → Type u)
(to_matroid : Π (M : α), matroid_on (γ M))


-- M is the name of the matroid and has type α.
-- (γ M) is the 'ground type' of the matroid M;
--the function to_matroid maps the name M to the structure of -- matroid M (i.e. a rank function and proofs of axioms).

instance matroid_on.matroids (γ : Type u)[fintype γ] : matroids (matroid_on γ) :=
{ γ := λ _, γ,
  to_matroid := id }

namespace matroid

local attribute [simp] image_union image_inter

variables {α : Type v} [matroids α]
-- Accessor functions for terms that have a matroid representation

--def finproof (M: α) := matroids.finproof M
def fin_cert (M: α) := (matroids.to_matroid M).fin_cert
def γ (M : α) := matroids.γ M -- matroid elements have type γ
def E (M: α) : (finset (γ M)) := (fin_cert M).elems -- E is the ground set viewed as a set, not a type.
def r (M : α) (X : finset (γ M) ) : ℤ := (matroids.to_matroid M).r X --@((matroids.to_matroid M).r) sorry sorry X
def R1 (M : α) (X : finset (γ M)) : 0 ≤ r M X ∧ r M X ≤ X.card := (matroids.to_matroid M).R1 X
def R2 (M : α) {X Y : finset (γ M)} (h : X ⊆ Y) : r M X ≤ r M Y := (matroids.to_matroid M).R2 h
def R3 (M : α) (X Y : finset (γ M)) : r M (X ∪ Y) + r M (X ∩ Y) ≤ r M X + r M Y := (matroids.to_matroid M).R3 X Y

@[simp] lemma r_empty_eq_zero (M : α) : r M (∅ : finset (γ M)) = 0 :=
begin
    have := R1 M ∅,
    simp only [card_empty, int.coe_nat_zero] at this,
    linarith,
end
--by { have h := R1 M ∅, rwa [card_empty, le_zero_iff_eq] at h }



--@[simp] lemma triv1 {M : α} [fintype (γ M)] {X : finset (γ M)} : X ⊆ E M := subset_univ X



lemma rank_subadditive (M : α) (X Y : finset (γ M)) : r M (X ∪ Y) ≤ r M X + r M Y := sorry
--le_trans (nat.le.intro rfl) (R3 M X Y)

lemma r_le_union (M : α) (X Y : finset (γ M)) : r M X ≤ r M (X ∪ Y) :=
by { apply R2 M, apply subset_union_left }

lemma r_le_union_right (M : α) (X Y : finset (γ M)) : r M Y ≤ r M (X ∪ Y) :=
by { rw union_comm, apply r_le_union }


--instance coe_subtype_finset {α : Type*} {Y: set α} :
--    has_coe (finset ↥Y) (finset α) := ⟨λ X, X.image subtype.val⟩

/-@[simp] lemma coe_subtype_size {α : Type*} {Y: set α} (X: finset Y) : size X = size (X: finset α) :=
begin
    sorry,
end

lemma coe_subtype_union {α: Type*} {Y: set α} (X₁ X₂ : finset Y) :
    (((X₁ ∪ X₂ : finset Y)) :finset α ) = (X₁ : finset α) ∪ (X₂ : finset α) :=
begin
    sorry,
    /-exact @image_union (↥Y) α
    (subtype.decidable_eq)
    _
    (λ (a : (↥Y)), (a : α)) X₁ X₂,-/

end
--set_option pp.all true
#print coe_subtype_union
#check @subtype.decidable_eq


@[simp] lemma coe_subtype_inter {α: Type*} {Y: set α} (X₁ X₂ : finset Y) :
    (((X₁ ∩ X₂ : finset Y)) :finset α) = (X₁ : finset α) ∩ (X₂ : finset α) :=
begin
    apply image_inter,
    apply subtype.ext,
end -/



structure submatroid (M : α) :=
(F : finset (γ M))

--set_option pp.beta true
--set_option pp.universes true
--set_option pp.notation false
--set_option pp.implicit true
set_option pp.proofs true

instance submatroid.matroid (M : α) : matroids (submatroid M) :=
{ γ := λ (M' : submatroid M), ↥(↑(M'.F) : set (γ M)),
  to_matroid := λ (M' : submatroid M),
  {
    fin_cert := @fintype.subtype (γ M) (λ x, (x ∈ M'.F)) M'.F (by simp),
    r := λ X, r M (X.image subtype.val),
    R1 := λ X,
    begin
        split,
        apply (R1 M (X.image subtype.val)).1,
        --have := (R1 M (X.image subtype.val)).2,

        sorry,
        --simp,
        --apply (R1 M (X.image subtype.val)).2,
    end,
    R2 := λ X₁ X₂ h, R2 M ((image_subset_image h)),
    R3 := λ X₁ X₂,
    begin
        --r M ↑(X₁ ∪ X₂) + r M ↑(X₁ ∩ X₂) ≤ r M ↑X₁ + r M ↑X₂
        convert (R3 M (X₁.image subtype.val) (X₂.image subtype.val)),
        apply image_union,
        apply image_inter,
        apply subtype.ext,
        --rw ← coe_subtype_union,
        --congr,
        --rw ← coe_subtype_inter,
        --congr,
    end, }}

def delete (M: α) (D: finset (γ M)) : submatroid M :=
submatroid.mk ((E M) \ D)


structure matroid_contraction (M : α) :=
(C : finset (γ M))



def contract (M : α) (C : finset (γ M)) : matroid_contraction M :=
matroid_contraction.mk C

instance matroid_contraction.matroid (M : α) : matroids (matroid_contraction M) :=
{ γ := λ M', ↥((↑M'.C : set (γ M))ᶜ),
  to_matroid := λ M',
  { fin_cert := @fintype.subtype (γ M) (λ x, (x ∉ M'.C)) ((E M) \ (M'.C))
  begin
     intros g,
     split,
     simp,
     simp,
     intros hg,
     split,
     apply (fin_cert M).complete,
     exact hg,
  end,

    r := sorry, --λ X, r M (X ∪ M'.C) - r M M'.C,

    R1 := λ X,
    begin
      sorry,
      /-split,
      linarith [R2 M (subset_union_right ↑X M'.C)],

      have h1 := rank_subadditive M X M'.C,
      have := (R1 M X).2,
      rw coe_subtype_size X,
      unfold size,
      linarith-/
    end,
    R2 := λ X,
    begin
         sorry,
         /-
        intros Y hXY,
        have hXYC: (X ∪ M'.C: finset (γ M)) ⊆ (Y ∪ M'.C: finset (γ M)),
        {
            apply union_subset_union_left,
            apply image_subset_image,
            exact hXY,
        },
        linarith [R2 M hXYC], -/
    end,
    R3 :=
    begin

        sorry,
        --intros X Y,
        /-
        α: Type v
        _inst_1: matroids α
        M: α
        M': matroid_contraction M
        XY: finset ↥(↑(M'.C))ᶜ
        ⊢ r M (↑(X ∪ Y) ∪ M'.C) - r M M'.C + (r M (↑(X ∩ Y) ∪ M'.C) - r M M'.C)
           ≤ r M (↑X ∪ M'.C) - r M M'.C + (r M (↑Y ∪ M'.C) - r M M'.C)
        -/

        /-suffices: r M (↑(X ∪ Y) ∪ M'.C) + r M (↑(X ∩ Y) ∪ M'.C) ≤ r M (↑X ∪ M'.C) + r M (↑Y ∪ M'.C),
        {
            linarith,
        },-/

        --sorry,

        --rw ← coe_subtype_union,


        --calc r M (↑(X ∪ Y) ∪ M'.C) - r M M'.C + (r M (↑(X ∩ Y) ∪ M'.C) - r M M'.C) ≤ r M (↑(X ∪ Y) ∪ M'.C) + (r M (↑(X ∩ Y) ∪ M'.C) - 2*(r M M'.C) : by linarith
        --... = r M (↑X ∪ M'.C) - r M M'.C + (r M (↑Y ∪ M'.C) - r M M'.C) : sorry,
        --... =

        --sorry,
        --exact this,

        --{linarith,},
        --rw @image_union (finset (↑(M'.C))ᶜ) () _ _ _ X Y ,
        --sorry,

        /-intros X Y,
        let X' := X.image subtype.val,
        let Y' := Y.image subtype.val,
        rw [image_union, image_inter],
        have := R3 M (X' ∪ M'.C) (Y' ∪ M'.C),
        simp only [@union_unions _ _ X' Y' _, inter_unions]  at this,

        linarith,
        intros x y,
        exact subtype.eq,-/
    end,
    }
 }

def dual (M : α) : matroid_on (γ M) :=
{
   fin_cert :=
    begin
       sorry,
    end,
    r := λ X, size X - r M (E M) + r M (Xᶜ),
  R1 :=
  begin
    sorry,
    /-intros X,
    split,
    have h1 : r X ≤ size X := (R1 M X).2,
    have h2 := rank_subadditive M X (Xᶜ),
    have h3 := lambda_conn_nonegative M X,
    --unfold lambda_conn at h3,

    calc size X - r (E M) + r Xᶜ = size X - r X + (r X + r Xᶜ - r (E M)) : by linarith
                        ...      ≥ size X - r X                          : by linarith [lambda_conn_nonegative M X]
                        ...      ≥ 0                                     : by linarith [(R1 M X).2],

    linarith[ R2 M ((by simp) :(Xᶜ ⊆ E M))], -/
  end,
  R2 := sorry,
  R3 := sorry }


instance matroid_on.matroids (M : α) : matroids (matroid_on (γ M)) :=
{ γ := λ _, γ M,
  to_matroid := id }

variable (M : α)
variable (X : finset (γ M))
#check matroids.to_matroid (dual (delete M X))
#check matroids.to_matroid (contract (dual M) X)
#check (matroids.γ (dual (delete M X)))
#check (matroids.γ (contract (dual M) X))

def dual_equiv (M : α) : matroid_contraction M ≃ submatroid (dual M) :=
begin

end
lemma dual_types (M: α) (X: finset (γ M)) : (matroids.γ (dual (delete M X))) = (matroids.γ (contract (dual M) X)) :=
begin
    sorry,
end
lemma contract_delete_dual (M: α) (X: finset (γ M)) : (matroids.to_matroid (dual (delete M X))) = (matroids.to_matroid (contract (dual M) X)) :=
begin
   sorry,
end


end matroid

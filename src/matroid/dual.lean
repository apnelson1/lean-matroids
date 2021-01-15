import matroid.axioms  
import boolalg.basic boolalg.collections boolalg.examples

----------------------------------------------------------------
namespace boolalg 


section dual
variables {U : boolalg}

lemma rank_bot {B : boolalg} (M : rankfun B) :
  M.r ⊥ = 0 :=
le_antisymm (calc M.r ⊥ ≤ size (⊥ : B) : M.R1 ⊥ ... = 0 : size_bot B) (M.R0 ⊥)

-- Every matroid has a dual.
def dual :
  rankfun U → rankfun U :=
fun M, {
  r := (fun X, size X + M.r Xᶜ - M.r ⊤),
  R0 := (fun X,
    calc 0 ≤ M.r X  + M.r Xᶜ - M.r (X ∪ Xᶜ) - M.r (X ∩ Xᶜ) : by linarith [M.R3 X Xᶜ]
    ...    = M.r X  + M.r Xᶜ - M.r ⊤        - M.r ⊥        : by rw [union_compl X, inter_compl X]
    ...    ≤ size X + M.r Xᶜ - M.r ⊤                       : by linarith [M.R1 X, rank_bot M]),
  R1 := (fun X, by {simp only, linarith [M.R2 _ _ (subset_top Xᶜ)]}),
  R2 := (fun X Y h, let
    Z := Xᶜ ∩ Y,
    h₁ :=
      calc Yᶜ ∪ Z = (Xᶜ ∩ Y) ∪ Yᶜ        : by apply union_comm
      ...         = (Xᶜ ∪ Yᶜ) ∩ (Y ∪ Yᶜ) : by apply union_distrib_right
      ...         = (X ∩ Y)ᶜ ∩ ⊤         : by rw [compl_inter X Y, union_compl Y]
      ...         = (X ∩ Y)ᶜ             : by apply inter_top
      ...         = Xᶜ                   : by rw [subset_def_inter_mp h],
    h₂ :=
      calc Yᶜ ∩ Z = (Xᶜ ∩ Y) ∩ Yᶜ : by apply inter_comm
      ...         = Xᶜ ∩ (Y ∩ Yᶜ) : by apply inter_assoc
      ...         = Xᶜ ∩ ⊥        : by rw [inter_compl Y]
      ...         = ⊥             : by apply inter_bot,
    h₃ :=
      calc M.r Xᶜ = M.r Xᶜ + M.r ⊥              : by linarith [rank_bot M]
      ...         = M.r (Yᶜ ∪ Z) + M.r (Yᶜ ∩ Z) : by rw [h₁, h₂]
      ...         ≤ M.r Yᶜ + M.r Z              : by apply M.R3
      ...         ≤ M.r Yᶜ + size Z             : by linarith [M.R1 Z]
      ...         = M.r Yᶜ + size (Xᶜ ∩ Y)      : by refl
      ...         = M.r Yᶜ + size Y - size X    : by linarith [compl_inter_size_subset h]
    in by {simp only, linarith}),
  R3 := (fun X Y,
    calc  size (X ∪ Y) + M.r (X ∪ Y)ᶜ  - M.r ⊤ + (size (X ∩ Y) + M.r (X ∩ Y)ᶜ  - M.r ⊤)
        = size (X ∪ Y) + M.r (Xᶜ ∩ Yᶜ) - M.r ⊤ + (size (X ∩ Y) + M.r (Xᶜ ∪ Yᶜ) - M.r ⊤) : by rw [compl_union X Y, compl_inter X Y]
    ... ≤ size X       + M.r Xᶜ        - M.r ⊤ + (size Y       + M.r Yᶜ        - M.r ⊤) : by linarith [size_modular X Y, M.R3 Xᶜ Yᶜ]),
}

-- The double dual of a matroid is itself.
lemma dual_dual (M : rankfun U) :
  dual (dual M) = M :=
begin
  apply rankfun.ext, apply funext, intro X, calc
  (dual (dual M)).r X = size X + (size Xᶜ + M.r Xᶜᶜ - M.r ⊤) - (size (⊤ : U) + M.r ⊤ᶜ - M.r ⊤) : rfl
  ...                 = size X + (size Xᶜ + M.r X   - M.r ⊤) - (size (⊤ : U) + M.r ⊥  - M.r ⊤) : by rw [compl_compl, boolalg.compl_top]
  ...                 = M.r X                                                                  : by linarith [size_compl X, rank_bot M]
end

lemma dual_inj {M₁ M₂ : rankfun U} :
  dual M₁ = dual M₂ → M₁ = M₂ := 
  λ h, by rw [←dual_dual M₁, ←dual_dual M₂, h]

lemma dual_r (M : rankfun U)(X : U):
   (dual M).r X = size X + M.r Xᶜ - M.r ⊤ := 
   rfl 

end /-section-/ dual

end boolalg 
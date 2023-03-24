import data.fintype.basic
import data.finset data.set data.equiv.list tactic 
--import topology.basic
-- import tactic.interactive
-- noncomputable theory 

---open classical
--local attribute [instance] prop_decidable

-- variables {α : Type*} [decidable_eq α]
variables (E: Type*) [decidable_eq E] [fintype E]
variables (α : Type*) [decidable_eq α]

-- variables (F : Type*) [decidable_eq F] [fintype F]
-- variables 


open finset 
open fintype 

namespace matroid

--def foo (X : set E) [decidable_pred X] : fintype (subtype X) := by apply_instance

--def size (X: set E) [decidable_pred X] : ℕ  := fintype.card (subtype X)
def size (X: set E) : ℕ := 0

--#check size

--example (F : set E) [decidable_pred F] : fintype (subtype F) := subtype.fintype F --finset.​subtype.​fintype F,,

structure matroid := 
(r : finset E → ℕ) 
(R1 : ∀ (X : finset E), 0 ≤ r X ∧ r X ≤ card X )
(R2 : ∀ (X Y: finset E), X ⊆ Y → r X ≤ r Y) 
(R3 : ∀ (X Y: finset  E), r (X ∪ Y) + r (X ∩ Y) ≤ r X + r Y)




def curry {α β γ : Type*} (f : α × β → γ) : α → β → γ := λ a, λ b, f (a,b)
def uncurry {α β γ : Type*} (f : α → β → γ) : α × β → γ := λ p, f p.1 p.2 

def f: (ℕ × ℕ) → ℕ := λ p, p.1 + p.2

#check f 
#check (curry f)
#eval ((curry f 3) 5)
    
/-def submatroid' (M : matroid E) (F : finset E) : matroid ( ??? ) := 
{ r := sorry,
R1 := sorry,
R2 := sorry,
R3 := sorry,
}-/

--def E_type (E: finset α) := (sorry) :()

--def sigma_matroid : Σ E : (finset α) , (r : finset E → ℕ)

/-
def submatroid (M : matroid E) (F : set E) [decidable_pred F] : matroid (subtype F) :=
{ r := λ X: set F , M.r ((coe : subtype F → E) '' X), --(λ (X : set F), M.r (coe '' X: set E)),
  R1 := 
  begin
      intros X X_decid, 
      have dec : decidable_pred (coe '' X), refine dec_pred (coe '' X),
      have :=  M.R1 dec (coe '' X) ,  --(coe '' X) ,
  end,
  R2 := 
  begin
      intros X Y,
      have := M.R2 (coe '' X) (coe '' Y),
      intros hXY,
      have coe_something : coe '' X ⊆ coe '' Y := image_subset (coe : subtype F → E) hXY,
      exact this coe_something,
  end,
  R3 := 
  begin
      intros X Y, 
      have coe_u := image_union (coe: subtype F → E) X Y,
      have inj : function.injective (coe: subtype F → E), exact subtype.coe_injective,
      have coe_i := image_inter inj,
      rw coe_u, 
      rw ← coe_i,
      exact M.R3 (coe '' X) (coe '' Y),
  end 
}


@[simp] lemma sdflkas (M : matroid E) (F : set E) [decidable_pred F] (s : set F) :
  (submatroid E M F).r s = M.r (coe '' s : set E) := rfl
-- begin 

-- end

lemma easy (M : matroid E) (F: set E)[decidable_pred F] : (submatroid E M F).r (univ) ≤ M.r (univ) := 
begin
  -- convert M.R2 F univ (subset_univ F),
    -- sorry,
    -- calc (submatroid E M F).r univ = M.r F              : _  
    --                     ...        ≤ M.r univ           : M.R2 F univ (subset_univ F),
    simp,
    exact M.R2 F univ (subset_univ F),
    
end




-- C ⊆ E   N = M / C           N.r (X) := M.r (X ∪ C) - M.r (C) 


--def restriction (M: matroid E) (X: set E) : matroid (set_fintype X) := ⟨sorry,sorry,sorry,sorry,⟩ 


--variables {M: Type*} [matroid M]

/-lemma empty_rank_zero (M : matroid E) : M.r ∅ = 0 := 
begin
    
    cases (M.R1 ∅),
    
    have : size ∅ = 0, sorry,
    --unfold size at right,

    --rw (by library_search : size ∅ = 0) at right,
    linarith 

end-/ 
-/





end matroid 
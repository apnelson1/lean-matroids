import prelim.size

universes u u₁ u₂ u₃

section axiom_sets 

variable {α : Type*}

section rank 

def satisfies_R0 (r : set α → ℤ) : Prop := 
  ∀ X, 0 ≤ r X 

def satisfies_R1 (r : set α → ℤ) : Prop := 
  ∀ X, r X ≤ size X

def satisfies_R2 (r : set α → ℤ) : Prop := 
  ∀ X Y, X ⊆ Y → r X ≤ r Y 

def satisfies_R3 (r : set α → ℤ) : Prop := 
  ∀ X Y, r (X ∪ Y) + r (X ∩ Y) ≤ r X + r Y

@[ext] structure rankfun (α : Type*) :=
  (r : set α → ℤ)
  (R0 : satisfies_R0 r)
  (R1 : satisfies_R1 r)
  (R2 : satisfies_R2 r)
  (R3 : satisfies_R3 r)

end rank 

section indep 

def satisfies_I1 (indep : set α → Prop) : Prop := 
  indep ∅ 

def satisfies_I2 (indep : set α → Prop) : Prop := 
  ∀ I J, I ⊆ J → indep J → indep I

def satisfies_I3 (indep : set α → Prop) : Prop := 
  ∀ I J, size I < size J → indep I → indep J → ∃ (e : α), e ∈ J \ I ∧ indep (I ∪ {e})

--def satisfies_I3' : (set α → Prop) → Prop := 
--  λ indep, ∀ X, ∃ r, ∀ B, (B ⊆ X ∧ indep B ∧ (∀ Y, B ⊂ Y → Y ⊆ X → ¬indep Y) → size B = r

@[ext] structure indep_family (α : Type*) := 
  (indep : set α → Prop)
  (I1 : satisfies_I1 indep)
  (I2 : satisfies_I2 indep)
  (I3 : satisfies_I3 indep)

/-@[ext] structure indep_family' (α : Type*) := 
  (indep : set α → Prop)
  (I1 : satisfies_I1 indep)
  (I2 : satisfies_I2 indep)
  (I3' : satisfies_I3' indep)-/

end indep 

section cct 

def satisfies_C1 (cct : set α → Prop) : Prop := 
  ¬ cct ∅ 

def satisfies_C2 (cct : set α → Prop) : Prop:= 
  ∀ C₁ C₂, cct C₁ → cct C₂ → ¬(C₁ ⊂ C₂)

def satisfies_C3 (cct : set α → Prop) : Prop:= 
  ∀ C₁ C₂ (e : α), C₁ ≠ C₂ → cct C₁ → cct C₂ 
    → e ∈ (C₁ ∩ C₂) → ∃ C₀ , cct C₀ ∧ C₀ ⊆ (C₁ ∪ C₂) \ {e}

@[ext] structure cct_family (α : Type*) :=
  (cct : set α → Prop)
  (C1 : satisfies_C1 cct)
  (C2 : satisfies_C2 cct)
  (C3 : satisfies_C3 cct)

end cct

section basis

def satisfies_B1 (basis : set α → Prop) : Prop :=
  ∃ B, basis B.

def satisfies_B2 (basis : set α → Prop) : Prop :=
  ∀ B₁ B₂, basis B₁ → basis B₂ 
    → ∀ (b₁ : α), b₁ ∈ B₁ \ B₂ → ∃ b₂, (b₂ ∈ B₂ \ B₁) ∧ basis (B₁ \ {b₁} ∪ {b₂}) 

@[ext] structure basis_family (α : Type*) :=
  (basis : set α → Prop)
  (B1 : satisfies_B1 basis)
  (B2 : satisfies_B2 basis)

end basis 

section cl 

def satisfies_cl1 : (set α → set α) → Prop := 
  λ cl, ∀ X, X ⊆ cl X

def satisfies_cl2 : (set α → set α) → Prop := 
  λ cl, ∀ X, cl (cl X) = cl X

def satisfies_cl3 : (set α → set α) → Prop := 
  λ cl, ∀ X Y : set α , X ⊆ Y → cl X ⊆ cl Y 

def satisfies_cl4 : (set α → set α) → Prop :=
  λ cl, ∀ X (e f : α), (e ∈ cl (X ∪ {f}) \ X) → (f ∈ cl (X ∪ {e}) \ X)

structure clfun (α : Type*) := 
  (cl : set α → set α)
  (cl1 : satisfies_cl1 cl)
  (cl2 : satisfies_cl2 cl)
  (cl3 : satisfies_cl3 cl)
  (cl4 : satisfies_cl4 cl)

end cl 

end axiom_sets 

def matroid (α : Type*) := rankfun α 

variables {α₁ : Type* }{α₂ : Type* }{α₃ : Type*}

namespace matroid

structure isom (M₁ : matroid α₁) (M₂ : matroid α₂) := 
(equiv : α₁ ≃ α₂)
(on_rank : ∀ X, M₂.r (equiv '' X) = M₁.r X)

instance coe_to_equiv {M₁ : matroid α₁} {M₂ : matroid α₂} : has_coe_to_fun (M₁.isom M₂) := 
{ F := _,
  coe := λ i, i.equiv } 

def isom.refl (M₁ : matroid α₁) : 
M₁.isom M₁ := 
{ equiv := equiv.refl α₁,
  on_rank := by simp  }

def isom.trans {M₁ : matroid α₁} {M₂ : matroid α₂} {M₃ : matroid α₃} 
(I12 : M₁.isom M₂) (I23 : M₂.isom M₃) : 
M₁.isom M₃ :=
{ equiv := I12.equiv.trans I23.equiv ,
  on_rank := λ X, by {rw [←I12.on_rank, ←I23.on_rank], apply congr_arg, ext, simp  }  } 

def isom.symm {M₁ : matroid α₁} {M₂ : matroid α₂} (i : M₁.isom M₂) : M₂.isom M₁ := 
{ equiv := i.equiv.symm,
  on_rank := λ X, by {rw ←i.on_rank, apply congr_arg, ext, simp,  } }

def is_isom (M₁ : matroid α₁) (M₂ : matroid α₂) := 
  nonempty (M₁.isom M₂)

lemma isom.inv_on_rank {M₁ : matroid α₁} {M₂ : matroid α₂} (i : isom M₁ M₂) (X : set α₂) :
  M₂.r X = M₁.r (i.equiv.symm '' X) :=
by {rw ←i.symm.on_rank X, refl} 

def isom_equiv {M₁ N₁ : matroid α₁} {M₂ N₂ : matroid α₂} 
(h₁ : M₁ = N₁) (h₂ : M₂ = N₂) (i : isom M₁ M₂) : 
  isom N₁ N₂ := 
{ equiv := i.equiv,
  on_rank := λ X, by {rw [←h₁,←h₂], apply i.on_rank, } }
 
end matroid 


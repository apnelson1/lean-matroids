import prelim.size

section axiom_sets 

variable {U : Type}

section rank 

variable [fintype U]

def satisfies_R0 (r : set U → ℤ) : Prop := 
  ∀ X, 0 ≤ r X 

def satisfies_R1 (r : set U → ℤ) : Prop := 
  ∀ X, r X ≤ size X

def satisfies_R2 (r : set U → ℤ) : Prop := 
  ∀ X Y, X ⊆ Y → r X ≤ r Y 

def satisfies_R3 (r : set U → ℤ) : Prop := 
  ∀ X Y, r (X ∪ Y) + r (X ∩ Y) ≤ r X + r Y

@[ext] structure rankfun (U : Type)[fintype U] :=
  (r : set U → ℤ)
  (R0 : satisfies_R0 r)
  (R1 : satisfies_R1 r)
  (R2 : satisfies_R2 r)
  (R3 : satisfies_R3 r)

end rank 

section indep 

variable [fintype U]

def satisfies_I1 (indep : set U → Prop) : Prop := 
  indep ∅ 

def satisfies_I2 (indep : set U → Prop) : Prop := 
  ∀ I J, I ⊆ J → indep J → indep I

def satisfies_I3 (indep : set U → Prop) : Prop := 
  ∀ I J, size I < size J → indep I → indep J → ∃ (e : U), e ∈ J \ I ∧ indep (I ∪ {e})

--def satisfies_I3' : (set U → Prop) → Prop := 
--  λ indep, ∀ X, ∃ r, ∀ B, (B ⊆ X ∧ indep B ∧ (∀ Y, B ⊂ Y → Y ⊆ X → ¬indep Y) → size B = r

@[ext] structure indep_family (U : Type)[fintype U] := 
  (indep : set U → Prop)
  (I1 : satisfies_I1 indep)
  (I2 : satisfies_I2 indep)
  (I3 : satisfies_I3 indep)

/-@[ext] structure indep_family' (U : Type) := 
  (indep : set U → Prop)
  (I1 : satisfies_I1 indep)
  (I2 : satisfies_I2 indep)
  (I3' : satisfies_I3' indep)-/


end indep 

section cct 


def satisfies_C1 (cct : set U → Prop) : Prop := 
  ¬ cct ∅ 

def satisfies_C2 (cct : set U → Prop) : Prop:= 
  ∀ C₁ C₂, cct C₁ → cct C₂ → ¬(C₁ ⊂ C₂)

def satisfies_C3 (cct : set U → Prop) : Prop:= 
  ∀ C₁ C₂ (e : U), C₁ ≠ C₂ → cct C₁ → cct C₂ 
    → e ∈ (C₁ ∩ C₂) → ∃ C₀ , cct C₀ ∧ C₀ ⊆ (C₁ ∪ C₂) \ {e}

@[ext] structure cct_family (U : Type) :=
  (cct : set U → Prop)
  (C1 : satisfies_C1 cct)
  (C2 : satisfies_C2 cct)
  (C3 : satisfies_C3 cct)

end cct

section basis

def satisfies_B1 (basis : set U → Prop) : Prop :=
  ∃ B, basis B.

def satisfies_B2 (basis : set U → Prop) : Prop :=
  ∀ B₁ B₂, basis B₁ → basis B₂ 
    → ∀ (b₁ : U), b₁ ∈ B₁ \ B₂ → ∃ b₂, (b₂ ∈ B₂ \ B₁) ∧ basis (B₁ \ {b₁} ∪ {b₂}) 

@[ext] structure basis_family (U : Type) :=
  (basis : set U → Prop)
  (B1 : satisfies_B1 basis)
  (B2 : satisfies_B2 basis)

end basis 

section cl 

def satisfies_cl1 : (set U → set U) → Prop := 
  λ cl, ∀ X, X ⊆ cl X

def satisfies_cl2 : (set U → set U) → Prop := 
  λ cl, ∀ X, cl (cl X) = cl X

def satisfies_cl3 : (set U → set U) → Prop := 
  λ cl, ∀ X Y : set U , X ⊆ Y → cl X ⊆ cl Y 

def satisfies_cl4 : (set U → set U) → Prop :=
  λ cl, ∀ X (e f : U), (e ∈ cl (X ∪ {f}) \ X) → (f ∈ cl (X ∪ {e}) \ X)

structure clfun (U : Type) := 
  (cl : set U → set U)
  (cl1 : satisfies_cl1 cl)
  (cl2 : satisfies_cl2 cl)
  (cl3 : satisfies_cl3 cl)
  (cl4 : satisfies_cl4 cl)

end cl 

end axiom_sets 

def matroid (U : Type)[fintype U] := rankfun U 


variables {U₁ U₂ U₃ : Type}[fintype U₁][fintype U₂][fintype U₃]

structure matroid.isom (M₁ : matroid U₁)(M₂ : matroid U₂) := 
(equiv : U₁ ≃ U₂)
(on_rank : ∀ X, M₂.r (equiv '' X) = M₁.r X)

instance coe_to_equiv {M₁ : matroid U₁}{M₂ : matroid U₂}: has_coe_to_fun (M₁.isom M₂) := 
{ F := _,
  coe := λ i, i.equiv } 

def isom.refl (M₁ : matroid U₁): 
M₁.isom M₁ := 
{ equiv := equiv.refl U₁,
  on_rank := by simp  }

def isom.trans {M₁ : matroid U₁}{M₂ : matroid U₂}{M₃ : matroid U₃}(i12 : M₁.isom M₂)(i23 : M₂.isom M₃): 
M₁.isom M₃ :=
{ equiv := i12.equiv.trans i23.equiv ,
  on_rank := λ X, by {rw [←i12.on_rank, ←i23.on_rank], apply congr_arg, ext, simp  }  } 

def isom.symm {M₁ : matroid U₁}{M₂ : matroid U₂}(i : M₁.isom M₂) : M₂.isom M₁ := 
{ equiv := i.equiv.symm,
  on_rank := λ X, by {rw ←i.on_rank, apply congr_arg, ext, simp,  } }

def is_isom (M₁ : matroid U₁)(M₂ : matroid U₂) := 
  nonempty (M₁.isom M₂)





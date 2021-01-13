



variables {U : boolalg}

def collection (U : boolalg) := U → Prop

def satisfies_B1 (basis : collection U) :=
  ∃ B, basis B.
def satisfies_B2 (basis : collection U) :=
  ∀ B₁ B₂, basis B₁ → basis B₂ →
    ∀ b₁, b₁ ∈ B₁ \ B₂ →
          ∃ b₂, (b₂ ∈ B₂ \ B₁) ∧ basis (B₁ \ b₁ ∪ b₂) 

@[ext] structure basis_family (U : boolalg) :=
  (basis : collection U)
  (B1 : satisfies_B1 basis)
  (B2 : satisfies_B2 basis)



section cl /- closure -/ 

variables {U : boolalg}

def satisfies_cl1 : (U → U) → Prop := 
  λ cl, ∀ X, X ⊆ cl X

def satisfies_cl2 : (U → U) → Prop := 
  λ cl, ∀ X, cl (cl X) = cl X

def satisfies_cl3 : (U → U) → Prop := 
  λ cl, ∀ X Y, X ⊆ Y → cl X ⊆ cl Y 

def satisfies_cl4 : (U → U) → Prop :=
  λ cl, ∀ (X : U) (e f : single U), (e ∈ cl (X ∪ f) \ X) → (f ∈ cl (X ∪ e) \ X)

structure clfun (U : boolalg) := 
  (cl : U → U)
  (cl1 : satisfies_cl1 cl)
  (cl2 : satisfies_cl2 cl)
  (cl3 : satisfies_cl3 cl)
  (cl4 : satisfies_cl4 cl)


end cl

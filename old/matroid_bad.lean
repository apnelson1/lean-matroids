

import data.finset

noncomputable theory 
open_locale classical
open finset
universe u


-- Coercion stuff

instance coe_subtype_finset {α : Type*} {Y: set α} :
    has_coe (finset Y) (finset α) := ⟨λ X, X.image subtype.val⟩ 

lemma union_lemma {α : Type*} {Y: set α} (S T : finset Y) :
    (((S ∪ T) : finset Y) : finset α) = S ∪ T := by apply image_union

-- Structure 

structure subadditive_fn_on (γ : Type u) := 
(f : finset γ → ℕ )
(hf : ∀ (S T : finset γ), f (S ∪ T) ≤ f S + f T) 


def restr {γ : Type u} (F : subadditive_fn_on γ) (Y: set γ) : subadditive_fn_on (↥Y) :=
{
    f := λ S, F.f (S: finset γ), 
    hf := λ S T,
    begin
        convert F.hf S T, 
        rw ← union_lemma, 
        congr, 
    end, 
} 


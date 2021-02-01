
import tactic 

noncomputable theory 
open_locale classical 

/-- Given an embedding from α to β and a set E equal to its range, gives an equivalence between α and the 
subtype of β corresponding to E -/
def subtype_inv_inj {α β: Type}(emb : α ↪ β){E : set β}(hE : E = set.range emb) : E ≃ α :=   
let h : Π (y : E), (∃ x : α, emb x = y) := 
  by {rintros ⟨y,hy⟩, rw [hE, set.mem_range] at hy, cases hy with x hx, from ⟨x, by simp [hx]⟩},
 desc : Π (y : E), {x : α  // emb x = y} :=   
  λ y, classical.indefinite_description _ (h y) in 
{ 
  to_fun    := λ y, (desc y).val, 
  inv_fun   := λ x, ⟨emb x, by {rw [hE, set.mem_range], from ⟨x, rfl⟩} ⟩, 
  left_inv  := λ y, by {simp_rw (desc y).property, simp}, 
  right_inv := λ x, by {cases emb with f h_inj, from h_inj (desc ⟨f x,_⟩).property},
}

/-- given a function on the subsets of α, and an embedding f from α to β, returns the corresponding function 
on subsets of the range of the embedding  -/
def pullback_r {α β: Type}(emb : α ↪ β)(f : set α → ℤ) : set (set.range emb) → ℤ := 
  λ X, f ((subtype_inv_inj emb rfl) '' X)
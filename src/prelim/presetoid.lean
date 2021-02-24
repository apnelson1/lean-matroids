import tactic 

open_locale classical 
noncomputable theory 

open set function 

variables {α : Type}

class presetoid (α : Type) := 
(r : α → α → Prop)
(r_transitive : transitive r)
(r_symmetric : symmetric r)

variable [presetoid α]

namespace presetoid 

def kernel : set α := 
  {x : α | ¬r x x}

def nontriv (α : Type)[presetoid α] := {a : α // r a a}

instance coe_val : has_coe (nontriv α) α := ⟨subtype.val⟩  

def class_of (a : α) : set α :=
  { x : α | r x a }

def is_class (X : set α) : Prop := 
  ∃ a, X = class_of a 

@[trans] lemma trans {a b c : α}(hab : r a b)(hbc : r b c) : 
  r a c :=
r_transitive hab hbc

@[symm] lemma symm {a b : α}(hab : r a b):
  r b a :=
r_symmetric hab 

lemma mem_class_of_iff {a b : α}: 
  a ∈ class_of b ↔ r a b := 
by rw [class_of, mem_set_of_eq]

lemma class_of_eq_class_of_iff {a b :  α}(ha : r a a)(hb : r b b):
  class_of a = class_of b ↔ r a b := 
begin
  simp_rw [class_of, ext_iff, mem_set_of_eq],
  refine ⟨λ h, by rwa ←h a, λ h, λ x, _⟩,
  have := symm h, split; 
  {intro h, transitivity, assumption, assumption}, 
end




end presetoid 

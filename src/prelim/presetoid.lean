import tactic 

/- WIP - the idea here is to clean up the definition of parallel in simple.lean using the fact 
that it is transitive and symmetric -/

open_locale classical 
noncomputable theory 

open set function 

class presetoid (α : Type) := 
(r : α → α → Prop)
(r_transitive : transitive r)
(r_symmetric : symmetric r)

variables {α : Type}[presetoid α]

namespace presetoid 

def kernel : set α := 
  {x : α | ¬r x x}

--def nontriv (α : Type)[presetoid α] := {a : α // r a a}

--instance coe_val : has_coe (nontriv α) α := ⟨subtype.val⟩  

--instance setoid_of_presetoid : setoid {x : α // r x x} := 

def class_of (a : α) : set α :=
  { x : α | r x a }

def is_class (X : set α) : Prop := 
  ∃ a, r a a ∧ X = class_of a 

--def classes : set (set α) := 
--  { S : set α | is_class S }

def eqv_class (α : Type)[presetoid α]: Type := 
  { S : set α // is_class S}

def eqv_classes (α : Type)[presetoid α] : set (set α) := 
  { S : set α | is_class S }

instance coe_set : has_coe (eqv_class α) (set α) := coe_subtype 

@[trans] lemma trans {a b c : α}(hab : r a b)(hbc : r b c) : 
  r a c :=
r_transitive hab hbc

@[symm] lemma symm {a b : α}(hab : r a b):
  r b a :=
r_symmetric hab 

lemma rel_comm {a b : α}: 
  r a b ↔ r b a := 
by {split; {intro, symmetry, assumption}} 

lemma mem_class_of_iff {a b : α}: 
  a ∈ class_of b ↔ r a b := 
by rw [class_of, mem_set_of_eq]

lemma class_of_eq_class_of_iff {a b :  α}(ha : r a a):
  class_of a = class_of b ↔ r a b := 
begin
  simp_rw [class_of, ext_iff, mem_set_of_eq],
  refine ⟨λ h, by rwa ←h a, λ h, λ x, _⟩,
  have := symm h, 
  split; {intro, transitivity; assumption}, 
end

lemma classes_eq_of_nonempty_inter {C₁ C₂ : eqv_class α}(hC₁C₂ : (C₁ ∩ C₂ : set α).nonempty): 
  C₁ = C₂ := 
begin
  cases C₁ with C₁ hC₁, cases C₂ with C₂ hC₂, 
  obtain ⟨x₁, hx₁, rfl⟩ := hC₁, obtain ⟨x₂, hx₂, rfl⟩ := hC₂,  
  obtain ⟨ ⟨x,h₁⟩,h₂⟩ := nonempty_inter_iff_exists_left.mp hC₁C₂,
  dsimp only [subtype.coe_mk] at *,  
  rw [subtype.mk_eq_mk, class_of_eq_class_of_iff hx₁], 
  rw mem_class_of_iff at h₁ h₂, 
  transitivity, exact symm h₁, assumption, 
end

lemma eqv_classes_pairwise_disj : 
  pairwise_disjoint (eqv_classes α) :=
begin
  intros C₁ hC₁ C₂ hC₂ hC₁C₂, 
  by_contra hn, rw [disjoint_iff_inter_eq_empty] at hn,  
  refine hC₁C₂ _,
  have := @classes_eq_of_nonempty_inter _ _ ⟨C₁,hC₁⟩ ⟨C₂, hC₂⟩, 
  simp_rw [subtype.coe_mk, subtype.mk_eq_mk] at this, 
  exact this (ne_empty_iff_nonempty.mp hn), 
end












end presetoid 

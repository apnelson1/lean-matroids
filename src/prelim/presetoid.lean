import tactic .single .size

/- WIP - the idea here is to clean up the definition of parallel in simple.lean using the fact 
that it is transitive and symmetric -/
universes u v w

open_locale classical 
noncomputable theory 

open set function 

structure presetoid (α : Type*) := 
(rel : α → α → Prop)
(rel_transitive : transitive rel)
(rel_symmetric : symmetric rel)

variables {α : Type*} {a b c : α} {s X : set α} (S : presetoid α) 

namespace presetoid 

def kernel : set α := 
  {x : α | ¬S.rel x x}

lemma mem_kernel_iff : 
  a ∈ S.kernel ↔ ¬S.rel a a := 
by simp [kernel]

def cl (a : α) : set α :=
  { x : α | S.rel x a }

def is_class (s : set α) : Prop := 
  nonempty s ∧ ∃ a, s = S.cl a 

lemma is_class_def {s : set α} : 
  S.is_class s ↔ (nonempty s ∧ ∃ a, s = S.cl a) :=
iff.rfl 

def classes : set (set α) := 
  { X | S.is_class X }

lemma mem_classes_iff_is_class {X : set α} : 
  X ∈ S.classes ↔ S.is_class X :=
by simp [classes]

@[trans] lemma trans (hab : S.rel a b) (hbc : S.rel b c) : 
  S.rel a c :=
S.rel_transitive hab hbc

@[symm] lemma symm (hab : S.rel a b) :
  S.rel b a :=
S.rel_symmetric hab 

def rel_self_of_rel (ha : S.rel a b) : 
  S.rel a a := 
S.trans ha (S.symm ha)

@[simp] lemma cl_eq_empty_iff: 
  S.cl a = ∅ ↔ ¬S.rel a a := 
begin
  rw [cl, sep_eq_empty_iff, ← not_iff_not],
  push_neg, 
  exact ⟨λ h, let ⟨x,hx⟩ := h in S.rel_self_of_rel (S.symm hx), λ h, ⟨_,h⟩⟩, 
end

@[simp] lemma cl_nonempty_iff: 
  (S.cl a).nonempty ↔ S.rel a a := 
by {rw [← ne_empty_iff_nonempty, ← @not_not (S.rel a a), not_iff_not], apply cl_eq_empty_iff}

lemma rel_comm: 
  S.rel a b ↔ S.rel b a := 
by {split; {intro, symmetry, assumption}} 

lemma mem_cl_iff: 
  a ∈ S.cl b ↔ S.rel a b := 
by rw [cl, mem_set_of_eq]

lemma rel_of_mems_cl (ha : a ∈ S.cl c) (hb : b ∈ S.cl c) :
  S.rel a b :=
S.trans (S.mem_cl_iff.mp ha) (S.symm (S.mem_cl_iff.mp hb))

lemma rel_self_of_mem_class {s : set α} (hs : S.is_class s) (ha : a ∈ s) :
  S.rel a a :=
by {obtain ⟨hb, ⟨b,rfl⟩⟩ := hs, exact S.rel_self_of_rel (S.mem_cl_iff.mp ha), }

lemma rel_of_mems_class {s : set α} (hs : S.is_class s) (ha : a ∈ s) (hb : b ∈ s) :
  S.rel a b :=
by {obtain ⟨-, x, rfl⟩ := hs, exact S.rel_of_mems_cl ha hb}

lemma mem_cl_self_iff: 
  a ∈ S.cl a ↔ S.rel a a := 
by rw mem_cl_iff 

lemma is_class_iff_rep {X : set α} : 
  S.is_class X ↔ (∃ a, (S.rel a a) ∧ X = S.cl a) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨⟨b⟩, ⟨a,rfl⟩⟩ := h, 
    exact ⟨a, S.rel_self_of_rel (S.mem_cl_iff.mp (S.symm b.2)), rfl⟩}, 
  obtain ⟨a, ⟨ha,rfl⟩⟩ := h, 
  exact ⟨⟨⟨a,S.mem_cl_iff.mpr ha⟩⟩,a,rfl⟩,
end

lemma class_has_rep {X : set α} : 
  S.is_class X → (∃ a, (S.rel a a) ∧ X = S.cl a) :=
S.is_class_iff_rep.mp 

lemma class_nonempty (hX : S.is_class X):
  X.nonempty := 
by {obtain ⟨a,h₁,rfl⟩ := S.class_has_rep hX, exact ⟨a, S.mem_cl_self_iff.mp h₁⟩,  }

lemma cl_is_class (ha : S.rel a a) :
  S.is_class (S.cl a) :=
S.is_class_iff_rep.mpr ⟨a, ha, rfl⟩ 

@[simp] lemma mem_classes_iff {X : set α} : 
  X ∈ S.classes ↔ (∃ a, (S.rel a a) ∧ X = S.cl a) :=
by rw [classes, mem_set_of_eq, is_class_iff_rep]

lemma cl_eq_cl_iff (ha : S.rel a a) :
  S.cl a = S.cl b ↔ S.rel a b := 
begin
  simp_rw [cl, ext_iff, mem_set_of_eq],
  refine ⟨λ h, by rwa ←h a, λ h, λ x, _⟩,
  have := S.symm h, 
  split; {intro, transitivity; assumption}, 
end

def cl_eq_cl_of_rel (h : S.rel a b) : 
  S.cl a = S.cl b :=
begin
  have := S.symm h, 
  refine ext_iff.mpr (λ x, ⟨λ h, _, λ h, _⟩);
  {rw mem_cl_iff at *, transitivity; assumption}, 
end 

lemma class_eq_cl_mem (hs : S.is_class s) (ha : a ∈ s) :
  s = S.cl a := 
begin
  obtain ⟨b, hb, rfl⟩ := S.is_class_iff_rep.mp hs, 
  exact (S.cl_eq_cl_of_rel (S.mem_cl_iff.mp ha)).symm, 
end

lemma eqv_classes_pairwise_disj : 
  S.classes.pairwise_disjoint :=
begin
  intros C₁ hC₁ C₂ hC₂ hC₁C₂, 
  refine disjoint_left.mpr (λ a ha₁ ha₂, hC₁C₂ _), 
  obtain ⟨⟨x₁,h₁,rfl⟩,⟨x₂,h₂,rfl⟩⟩ := ⟨S.mem_classes_iff.mp hC₁, S.mem_classes_iff.mp hC₂⟩, 
  rw mem_cl_iff at ha₁ ha₂, 
  rw (S.cl_eq_cl_iff h₁),  
  transitivity, symmetry, exact ha₁, assumption, 
end

lemma sUnion_classes_eq_compl_kernel : 
  ⋃₀ S.classes = S.kernelᶜ :=
begin
  ext x, 
  simp only [kernel, exists_prop, not_not, mem_set_of_eq, mem_classes_iff, mem_compl_eq],  
  split, 
  { rintro ⟨P, ⟨a, ha, rfl⟩, haP⟩, 
    exact S.rel_self_of_rel (S.mem_cl_iff.mp haP), },
  exact λ hx, ⟨S.cl x, ⟨_, hx,rfl⟩ , S.mem_cl_iff.mp hx⟩, 
end

section simple

/-- X is simple if it contains no kernel elements of S and no related pairs of S -/
def is_simple_set (S : presetoid α) (X : set α) :=
  ∀ x y ∈ X, S.rel x y ↔ x = y 

lemma simple_set_iff {S : presetoid α} {X : set α} : 
  S.is_simple_set X ↔ disjoint X S.kernel ∧ ∀ P, S.is_class P → size (X ∩ P) ≤ 1 :=
begin
  refine ⟨λ h, _, λ h, _⟩, 
  { by_contra hn, rw [not_and_distrib, not_disjoint_iff, not_forall] at hn, 
    obtain (⟨x, hxX, hxK⟩ | ⟨P, hP⟩) := hn, 
    { rw mem_kernel_iff at hxK, exact hxK ((h x x hxX hxX).mpr rfl),  },
    rw [not_imp] at hP, 
    
     }, 
end

end simple

section size 

variables [fintype α]

lemma size_classes_le_type_size:
  size (S.classes) ≤ type_size α := 
size_disjoint_collection_le_type_size 
  (λ s hs, S.class_nonempty (S.mem_classes_iff_is_class.mpr hs))
  (S.eqv_classes_pairwise_disj)

--lemma size_classes_eq_type_size_i


end size 






end presetoid 

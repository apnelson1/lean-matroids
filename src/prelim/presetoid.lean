import tactic .single 

/- γIP - the idea here is to clean up the definition of parallel in simple.lean using the fact 
that it is transitive and symmetric -/

open_locale classical 
noncomputable theory 

open set function 

structure presetoid (α : Type) := 
(rel : α → α → Prop)
(rel_transitive : transitive rel)
(rel_symmetric : symmetric rel)

variables {α : Type}{a b c : α}{s : set α}(S : presetoid α) 

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

lemma is_class_def {s : set α}: 
  S.is_class s ↔ (nonempty s ∧ ∃ a, s = S.cl a) :=
iff.rfl 

def classes : set (set α) := 
  { X | S.is_class X }


lemma mem_classes_iff_is_class {X : set α}: 
  X ∈ S.classes ↔ S.is_class X :=
by simp [classes]

@[trans] lemma trans (hab : S.rel a b)(hbc : S.rel b c) : 
  S.rel a c :=
S.rel_transitive hab hbc

@[symm] lemma symm (hab : S.rel a b):
  S.rel b a :=
S.rel_symmetric hab 

def rel_self_of_rel (ha : S.rel a b): 
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

lemma rel_of_mems_cl (ha : a ∈ S.cl c)(hb : b ∈ S.cl c):
  S.rel a b :=
S.trans (S.mem_cl_iff.mp ha) (S.symm (S.mem_cl_iff.mp hb))

lemma rel_self_of_mem_class {s : set α}(hs : S.is_class s)(ha : a ∈ s):
  S.rel a a :=
by {obtain ⟨hb, ⟨b,rfl⟩⟩ := hs, exact S.rel_self_of_rel (S.mem_cl_iff.mp ha), }

lemma rel_of_mems_class {s : set α}(hs : S.is_class s)(ha : a ∈ s)(hb : b ∈ s):
  S.rel a b :=
by {obtain ⟨-, x, rfl⟩ := hs, exact S.rel_of_mems_cl ha hb}

lemma mem_cl_self_iff: 
  a ∈ S.cl a ↔ S.rel a a := 
by rw mem_cl_iff 

lemma is_class_iff_rep {X : set α}: 
  S.is_class X ↔ (∃ a, (S.rel a a) ∧ X = S.cl a) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨⟨b⟩, ⟨a,rfl⟩⟩ := h, 
    exact ⟨a, S.rel_self_of_rel (S.mem_cl_iff.mp (S.symm b.2)), rfl⟩}, 
  obtain ⟨a, ⟨ha,rfl⟩⟩ := h, 
  exact ⟨⟨⟨a,S.mem_cl_iff.mpr ha⟩⟩,a,rfl⟩,
end

lemma cl_is_class (ha : S.rel a a):
  S.is_class (S.cl a) :=
S.is_class_iff_rep.mpr ⟨a, ha, rfl⟩ 


@[simp] lemma mem_classes_iff {X : set α}: 
  X ∈ S.classes ↔ (∃ a, (S.rel a a) ∧ X = S.cl a) :=
by rw [classes, mem_set_of_eq, is_class_iff_rep]

lemma cl_eq_cl_iff (ha : S.rel a a):
  S.cl a = S.cl b ↔ S.rel a b := 
begin
  simp_rw [cl, ext_iff, mem_set_of_eq],
  refine ⟨λ h, by rwa ←h a, λ h, λ x, _⟩,
  have := S.symm h, 
  split; {intro, transitivity; assumption}, 
end

def cl_eq_cl_of_rel (h : S.rel a b): 
  S.cl a = S.cl b :=
begin
  have := S.symm h, 
  refine ext_iff.mpr (λ x, ⟨λ h, _, λ h, _⟩);
  {rw mem_cl_iff at *, transitivity; assumption}, 
end 

/-lemma classes_eq_of_nonempty_inter {C₁ C₂ : eqv_class α}(hC₁C₂ : (C₁ ∩ C₂ : set α).nonempty): 
  C₁ = C₂ := 
begin
  cases C₁ with C₁ hC₁, cases C₂ with C₂ hC₂, 
  obtain ⟨x₁, hx₁, rfl⟩ := hC₁, obtain ⟨x₂, hx₂, rfl⟩ := hC₂,  
  obtain ⟨ ⟨x,h₁⟩,h₂⟩ := nonempty_inter_iff_exists_left.mp hC₁C₂,
  dsimp only [subtype.coe_mk] at *,  
  rw [subtype.mk_eq_mk, class_of_eq_class_of_iff hx₁], 
  rw mem_class_of_iff at h₁ h₂, 
  transitivity, exact symm h₁, assumption, 
end-/

lemma eqv_classes_pairwise_disj : 
  pairwise_disjoint (S.classes) :=
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












end presetoid 

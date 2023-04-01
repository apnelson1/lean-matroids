import tactic .single .size

/-!
This file contains an API for a `presetoid`, which is a symmetric, transitive relation. This is
essentially an equivalence relation, together with a 'kernel' of singletons that are not related
to any elements, even themselves. This describes the 'parallel' relation in the edges of a graph,
or on the elements of the matroids; in both cases the kernel consists of loops.

The API contains basic lemmas and definitions for objects like equivalence classes, as well as
definitions of `simple` sets that are disjoint from the kernel and contain at most one element of
each equivalence class.
-/

open_locale classical
noncomputable theory

open set function

structure presetoid (α : Type*) :=
(rel : α → α → Prop)
(rel_transitive : transitive rel)
(rel_symmetric : symmetric rel)

variables {α : Type*} {a b c : α} {s X : set α} {S : presetoid α}

namespace presetoid

def kernel (S : presetoid α): set α :=
  {x : α | ¬S.rel x x}

lemma mem_kernel_iff :
  a ∈ S.kernel ↔ ¬S.rel a a :=
by simp [kernel]

def cl (S : presetoid α)(a : α) : set α :=
  { x : α | S.rel x a }

def is_class (S : presetoid α)(s : set α) : Prop :=
  nonempty s ∧ ∃ a, s = S.cl a

lemma is_class_def {s : set α} :
  S.is_class s ↔ (nonempty s ∧ ∃ a, s = S.cl a) :=
iff.rfl

def classes (S : presetoid α) : set (set α) :=
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
trans ha (symm ha)

@[simp] lemma cl_eq_empty_iff:
  S.cl a = ∅ ↔ ¬S.rel a a :=
begin
  rw [cl, sep_eq_empty_iff, ← not_iff_not],
  push_neg,
  exact ⟨λ h, let ⟨x,hx⟩ := h in rel_self_of_rel (symm hx), λ h, ⟨_,h⟩⟩,
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
trans (mem_cl_iff.mp ha) (symm (mem_cl_iff.mp hb))

lemma rel_self_of_mem_class {s : set α} (hs : S.is_class s) (ha : a ∈ s) :
  S.rel a a :=
by {obtain ⟨hb, ⟨b,rfl⟩⟩ := hs, exact rel_self_of_rel (mem_cl_iff.mp ha), }

lemma rel_of_mems_class {s : set α} (hs : S.is_class s) (ha : a ∈ s) (hb : b ∈ s) :
  S.rel a b :=
by {obtain ⟨-, x, rfl⟩ := hs, exact rel_of_mems_cl ha hb}

lemma mem_cl_self_iff:
  a ∈ S.cl a ↔ S.rel a a :=
by rw mem_cl_iff

lemma is_class_iff_rep {X : set α} :
  S.is_class X ↔ (∃ a, (S.rel a a) ∧ X = S.cl a) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨⟨b⟩, ⟨a,rfl⟩⟩ := h,
    exact ⟨a, rel_self_of_rel (mem_cl_iff.mp (symm b.2)), rfl⟩},
  obtain ⟨a, ⟨ha,rfl⟩⟩ := h,
  exact ⟨⟨⟨a,mem_cl_iff.mpr ha⟩⟩,a,rfl⟩,
end

lemma class_has_rep {X : set α} :
  S.is_class X → (∃ a, (S.rel a a) ∧ X = S.cl a) :=
is_class_iff_rep.mp

lemma class_nonempty (hX : S.is_class X):
  X.nonempty :=
by {obtain ⟨a,h₁,rfl⟩ := class_has_rep hX, exact ⟨a, mem_cl_self_iff.mp h₁⟩,  }

lemma cl_is_class (ha : S.rel a a) :
  S.is_class (S.cl a) :=
is_class_iff_rep.mpr ⟨a, ha, rfl⟩

@[simp] lemma mem_classes_iff {X : set α} :
  X ∈ S.classes ↔ (∃ a, (S.rel a a) ∧ X = S.cl a) :=
by rw [classes, mem_set_of_eq, is_class_iff_rep]

lemma cl_eq_cl_iff (ha : S.rel a a) :
  S.cl a = S.cl b ↔ S.rel a b :=
begin
  simp_rw [cl, ext_iff, mem_set_of_eq],
  refine ⟨λ h, by rwa ←h a, λ h, λ x, _⟩,
  have := symm h,
  split; {intro, transitivity; assumption},
end

def cl_eq_cl_of_rel (h : S.rel a b) :
  S.cl a = S.cl b :=
begin
  have := symm h,
  refine ext_iff.mpr (λ x, ⟨λ h, _, λ h, _⟩);
  {rw mem_cl_iff at *, transitivity; assumption},
end

lemma class_eq_cl_mem (hs : S.is_class s) (ha : a ∈ s) :
  s = S.cl a :=
begin
  obtain ⟨b, hb, rfl⟩ := is_class_iff_rep.mp hs,
  exact (cl_eq_cl_of_rel (mem_cl_iff.mp ha)).symm,
end

lemma eqv_classes_pairwise_disj (S : presetoid α):
  S.classes.pairwise_disjoint :=
begin
  intros C₁ hC₁ C₂ hC₂ hC₁C₂,
  refine disjoint_left.mpr (λ a ha₁ ha₂, hC₁C₂ _),
  obtain ⟨⟨x₁,h₁,rfl⟩,⟨x₂,h₂,rfl⟩⟩ := ⟨mem_classes_iff.mp hC₁, mem_classes_iff.mp hC₂⟩,
  rw mem_cl_iff at ha₁ ha₂,
  rw (cl_eq_cl_iff h₁), 
  transitivity, symmetry, exact ha₁, assumption,
end

lemma sUnion_classes_eq_compl_kernel :
  ⋃₀ S.classes = S.kernelᶜ :=
begin
  ext x,
  simp only [kernel, exists_prop, not_not, mem_set_of_eq, mem_classes_iff, mem_compl_eq], 
  split,
  { rintro ⟨P, ⟨a, ha, rfl⟩, haP⟩,
    exact rel_self_of_rel (mem_cl_iff.mp haP), },
  exact λ hx, ⟨S.cl x, ⟨_, hx,rfl⟩ , mem_cl_iff.mp hx⟩,
end

section simple

/-- X is simple if it contains no kernel elements of S and no related pairs of S -/
def is_simple_set (S : presetoid α) (X : set α) :=
  ∀ x y ∈ X, S.rel x y ↔ x = y

lemma simple_set_iff {S : presetoid α} {X : set α} :
  S.is_simple_set X ↔ disjoint X S.kernel ∧ ∀ P, S.is_class P → (∀ e f ∈ X ∩ P, e = f) :=
begin
  refine ⟨λ h, by_contra (λ hn, _), λ h, by_contra (λ hn, _)⟩,
  { rw [not_and_distrib, not_disjoint_iff, not_forall] at hn,
    obtain (⟨x, hxX, hxK⟩ | ⟨P, hP⟩) := hn,
    { rw mem_kernel_iff at hxK, exact hxK ((h x x hxX hxX).mpr rfl),  },
    push_neg at hP,
    obtain ⟨e,f,⟨heX, heP⟩,⟨hfX,hfP⟩,hef⟩ := hP.2,
    exact hef ((h e f heX hfX).mp (rel_of_mems_class hP.1 heP hfP ))},
  rw [is_simple_set] at hn, 
  push_neg at hn,

  obtain ⟨e,f,he,hf,hef⟩ := hn,
  rw [not_iff] at hef,
  rcases em (e = f) with (rfl | hef'),
  { simp only [eq_self_iff_true, iff_true] at hef,
    rw disjoint_right at h,
    exact (h.1 (mem_kernel_iff.mpr hef)) he},
  rw [iff_false_intro hef', iff_false, not_not] at hef,
  have her := rel_self_of_rel hef,
  exact hef' (h.2 (S.cl e) (cl_is_class her) _ _
    ⟨he, mem_cl_self_iff.mpr her⟩
    ⟨hf, mem_cl_iff.mpr (symm hef)⟩ ),
end

lemma simple_set_iff_of_fintype [fintype α] { X : set α }:
  S.is_simple_set X ↔ disjoint X S.kernel ∧ ∀ P, S.is_class P → size (X ∩ P) ≤ 1 :=
by {conv in (_ ≤ _) {rw size_le_one_iff_mem_unique}, exact simple_set_iff}

/-- a presetoid is simple if its kernel is empty and its equivalence classes are singletons -/
def is_simple (S : presetoid α) :=
  S.is_simple_set univ

lemma simple_iff :
  S.is_simple ↔ S.kernel = ∅ ∧ ∀ P, S.is_class P → size P = 1 :=
begin
  rw [is_simple, simple_set_iff], convert iff.rfl, simp,
  simp_rw [univ_inter],
  refine iff_iff_eq.mp ⟨λ h P hP e f he hf, eq_of_mems_size_one (h P hP) he hf, λ h P hP, _⟩,
  rw size_eq_one_iff_nonempty_unique_mem,
  exact ⟨class_nonempty hP, h P hP⟩,
end

lemma simple_iff_rel :
  S.is_simple ↔ ∀ x y, S.rel x y ↔ x = y :=
by {rw [is_simple, is_simple_set], finish}

lemma simple_iff_cl :
  S.is_simple ↔ ∀ x, S.cl x = {x} :=
begin
  simp_rw [simple_iff_rel, cl],
  refine ⟨λ h x, by {ext, finish}, λ h x y, _⟩,
  specialize h y,
  simp only [ext_iff, mem_singleton_iff, mem_set_of_eq] at h,
  apply h,  
end

end simple

section size

variables [fintype α]

lemma size_classes_le_type_size (S : presetoid α):
  size (S.classes) ≤ type_size α :=
size_disjoint_collection_le_type_size
  (λ s hs, class_nonempty (mem_classes_iff_is_class.mpr hs))
  (S.eqv_classes_pairwise_disj)

/- this proof is a nasty hack and should be improvable -/
lemma size_classes_eq_type_size_iff_simple (S : presetoid α):
  size S.classes = type_size α ↔ S.is_simple :=
begin
  convert size_disjoint_collection_eq_type_size_iff
    (λ s hs, class_nonempty (mem_classes_iff_is_class.mpr hs))
    (S.eqv_classes_pairwise_disj),
  rw [simple_iff, ← iff_iff_eq], 
  congr' 2,
 
  refine iff_iff_eq.mp ⟨λ h, _, λ h, _⟩, 
  { ext x, simp only [exists_prop, mem_univ, mem_set_of_eq, iff_true],
    refine ⟨S.cl x, mem_sep (mem_def.mp (nonempty.to_subtype ⟨x, mem_cl_self_iff.mpr _⟩)) _ , _⟩, 
    { apply not_not.mp, rw [← mem_kernel_iff, h], apply not_mem_empty },
    { exact ⟨x,rfl⟩},
    { rw mem_cl_self_iff, apply not_not.mp, rw [← mem_kernel_iff, h], apply not_mem_empty }},
  simp only [kernel, not_not, sep_eq_empty_iff],
  intro x,
  rw sUnion_eq_univ_iff at h,
  obtain ⟨X, h₁, h₂⟩ := h x,
  rw mem_def at h₁,
  obtain ⟨a, rfl⟩ := h₁.2,
  apply rel_of_mems_cl h₂ h₂,    
end


end size






end presetoid

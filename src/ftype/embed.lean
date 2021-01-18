
import .basic --.single
namespace ftype 
-- Embedding and subftypeebras

local attribute [instance] classical.prop_decidable




def subftype {A : ftype}(ground : set A) : ftype :=  
  ⟨{x : A // x ∈ ground}, by {letI := fintype_of A, from ⟨by apply_instance,trivial⟩}⟩

@[ext] structure embed (A B : ftype) :=
  (f     : A → B )
  (f_inj : function.injective f)

instance emb_to_fn {A B : ftype} : has_coe_to_fun (embed A B) := {F := λ _, A → B.E, coe := embed.f}

def embed.img {A B : ftype}(emb : embed A B): set A → set B := 
  λ X, (X.image emb)

--instance emb_to_set_fn {A B : ftype} : has_coe (embed A B) (set A → set B.E):= ⟨embed.img⟩

lemma embed.on_subset {A B : ftype} (emb : embed A B) {X Y : set A} :
  (X ⊆ Y) → (emb.img X) ⊆ (emb.img Y) := 
  λ h, by tidy

lemma embed.on_size {A B : ftype} (emb : embed A B) (X : set A):
  size (emb.img X) = size X := 
begin
  simp only [size, size_nat, int.coe_nat_inj'], 
  rw (by {simp [as_finset], tidy,} : (as_finset B (emb.img X)) = finset.image emb.f (as_finset A X)),
  apply finset.card_image_of_injective, apply emb.f_inj,
end

lemma embed.on_inter {A B : ftype} (emb : embed A B) {X Y : set A} : 
  emb.img (X ∩ Y) = emb.img X ∩ emb.img Y := 
  (set.image_inter emb.f_inj).symm

lemma embed.on_union {A B : ftype} (emb : embed A B) {X Y : set A} : 
  emb.img (X ∪ Y) = emb.img X ∪ emb.img Y := 
  set.image_union _ _ _


def embed.id {A : ftype}: embed A A := 
  ⟨id, function.injective_id⟩

def embed.compose {A B C: ftype} : (embed A B) → (embed B C) → (embed A C) := λ e1 e2,
  ⟨e2.f ∘ e1.f, λ x x' h, e1.f_inj (e2.f_inj h)⟩

def embed.from_subftype {A : ftype}(X : set A) : embed (subftype X) A := 
  ⟨λ e, e.val, by tidy⟩
 
def embed.from_nested_pair {A : ftype}{X₁ X₂ : set A} (hX₁X₂ : X₁ ⊆ X₂) : embed (subftype X₁) (subftype X₂) := 
  ⟨λ X, ⟨X.1, by tidy⟩, by tidy⟩

lemma embed.compose_subset_nested_pair {A : ftype}(X₁ X₂ : set A) (hX₁X₂ : X₁ ⊆ X₂) :
 (embed.compose (embed.from_nested_pair hX₁X₂) (embed.from_subftype X₂)) = embed.from_subftype X₁ := rfl 

lemma embed.compose_nested_triple {A : ftype}(X₁ X₂ X₃ : set A) (h₁₂ : X₁ ⊆ X₂) (h₂₃ : X₂ ⊆ X₃) :
  (embed.compose (embed.from_nested_pair h₁₂) (embed.from_nested_pair h₂₃)) = embed.from_nested_pair (subset_trans h₁₂ h₂₃) := rfl


--Subalgebra coercion 

instance coe_elem_from_subftype {A : ftype} {S : set A} : has_coe (subftype S).E A := ⟨embed.from_subftype S⟩

instance coe_set_from_subftype {A : ftype} {S : set A} : has_coe (set (subftype S).E) (set A) := ⟨λ X, coe '' X⟩ 


--instance coe_single_from_subftype {A : ftype} {S : set A} : has_coe (single (subftype S)) (single A) := ⟨(embed.from_subset S).single_emb⟩ 

--@[simp] lemma coe_single_subftype_compose {A : ftype} {S : set A} (e : single (subftype S)) : ((e: single A): set A) = (e : set A) := rfl  
--lemma coe_subftype_single_compose {A : ftype} {S : set A} (e : single (subftype S)) : ((e: subftype S): set A) = (e : set A) := rfl  

@[simp] lemma subftype_coe_size {A : ftype} {S : set A} (X : set (subftype S)) : size X = size (X : set A) := 
  ((embed.from_subftype S).on_size X).symm 


@[simp] lemma subftype_coe_subset {A : ftype} {S : set A} {X Y : set (subftype S)}: (X ⊆ Y) ↔ ((X: set A) ⊆ (Y: set A)) :=
begin
  refine ⟨λ h, (embed.from_subftype S).on_subset h, λ h, _⟩,
  have h1 : ∀ (Z : set (subftype S)), (Z : set A) = (coe '' Z) := λ Z, rfl, 
  rw [h1 X, h1 Y, subtype.coe_image, subtype.coe_image] at h, 
  intros x hx, cases x, 
  cases @h x_val ⟨x_property, hx⟩,
  assumption, 
end

@[simp] lemma subftype_coe_union {A : ftype} {S : set A} {X Y : set (subftype S)}: (((X ∪ Y) : set (subftype S)) : set A) = ((X: set A) ∪ (Y:set A)) := 
  (embed.from_subftype S).on_union
 
@[simp] lemma subftype_coe_inter {A : ftype} {S : set A} {X Y : set (subftype S)}: (((X ∩ Y) : set (subftype S)) : set A) = ((X: set A) ∩ (Y:set A)) := 
  (embed.from_subftype S).on_inter

lemma coe_top {A : ftype} (S : set A) : ((⊤ : set (subftype S)) : set A) = S := by tidy 

-- This next coe doesn't seem to work in practice, even when a P ⊆ Q proof term is in the local context 
--instance coe_from_nested_pair {A : ftype} {P Q: set A} {hPQ : P ⊆ Q} : has_coe (subftype P) (subftype Q) := ⟨(embed.from_nested_pair hPQ).f⟩ 

/-instance embed.coe_to_fun {A B : ftype.ftype} : has_coe_to_fun (ftype.embed A B) := {
  F := (λ _, A → B),
  coe := λ emb, emb.f,
}-/
--def subftype.embed {E : set A} : ftype.embed (subftype E) A := sorry



---- Isomorphisms 

structure iso (A B : ftype) := 
  (fwd : embed A B)
  (bwd : embed B A)
  (fwd_then_bwd : embed.compose fwd bwd = embed.id)
  (bwd_then_fwd : embed.compose bwd fwd = embed.id)

--def ftype.canonical (size : ℤ) :
--  (0 ≤ size) → ftype := sorry

-- Construct a ftype from a finite set S (probably deprecated)
def powersetalg (γ : Type)[fintype γ] : ftype := 
{ 
  E       := γ, 
  is_fin  := ⟨by apply_instance, trivial⟩,
}

end ftype 
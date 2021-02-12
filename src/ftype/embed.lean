
import .basic --.single
namespace ftype 
-- Embedding and subftypeebras

open_locale classical 
noncomputable theory 


def subftype {A : ftype} (ground : set A) : ftype :=  
  {E := {x : A // x ∈ ground}, ft := by {apply_instance}} 

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
  ⟨λ x, ⟨x.1, by tidy⟩, by tidy⟩

lemma embed.compose_subset_nested_pair {A : ftype}(X₁ X₂ : set A) (hX₁X₂ : X₁ ⊆ X₂) :
 (embed.compose (embed.from_nested_pair hX₁X₂) (embed.from_subftype X₂)) = embed.from_subftype X₁ := rfl 

lemma embed.compose_nested_triple {A : ftype}(X₁ X₂ X₃ : set A) (h₁₂ : X₁ ⊆ X₂) (h₂₃ : X₂ ⊆ X₃) :
  (embed.compose (embed.from_nested_pair h₁₂) (embed.from_nested_pair h₂₃)) = embed.from_nested_pair (subset_trans h₁₂ h₂₃) := rfl


--Subalgebra coercion 
mk_simp_attribute coe_up "upwards coercion simp lemmas"

instance coe_elem_from_subftype {A : ftype} {S : set A} : has_coe (subftype S).E A := ⟨embed.from_subftype S⟩

instance coe_set_from_subftype {A : ftype} {S : set A} : has_coe (set (subftype S).E) (set A) := ⟨λ X, coe '' X⟩ 

@[coe_up] lemma subftype_coe_size {A : ftype} {S : set A} (X : set (subftype S)) : size X = size (X : set A) := 
  ((embed.from_subftype S).on_size X).symm 

@[coe_up] lemma subftype_coe_subset {A : ftype} {S : set A} {X Y : set (subftype S)}: (X ⊆ Y) ↔ ((X: set A) ⊆ (Y: set A)) :=
begin
  refine ⟨λ h, (embed.from_subftype S).on_subset h, λ h, _⟩,
  have h1 : ∀ (Z : set (subftype S)), (Z : set A) = (coe '' Z) := λ Z, rfl, 
  rw [h1 X, h1 Y, subtype.coe_image, subtype.coe_image] at h, 
  intros x hx, cases x, 
  cases @h x_val ⟨x_property, hx⟩,
  assumption, 
end


@[coe_up] lemma subftype_coe_union {A : ftype} {S : set A} {X Y : set (subftype S)}: 
  (((X ∪ Y) : set (subftype S)) : set A) = ((X: set A) ∪ (Y:set A)) := 
  (embed.from_subftype S).on_union
 
@[coe_up] lemma subftype_coe_inter {A : ftype} {S : set A} {X Y : set (subftype S)}:
  (((X ∩ Y) : set (subftype S)) : set A) = ((X: set A) ∩ (Y:set A)) := 
  (embed.from_subftype S).on_inter

@[coe_up] lemma subftype_coe_compl {A : ftype} {S : set A} {X : set (subftype S)}:
  (((Xᶜ : set (subftype S))) : set A) = S \ (X : set A)  := 
begin
  -- Fix this garbage! 
  unfold_coes, ext, refine ⟨λ h, ⟨_,_⟩, λ h,_⟩, 
  rcases h with ⟨_,⟨_,_⟩⟩, rw ←h_h_right, tidy, apply h_h_left, 
  have := (embed.from_subftype S).f_inj h_h_right, 
  rw this, assumption, 
  -- No really, fix it! 
end 

@[coe_up] lemma coe_univ {A : ftype} (S : set A) : 
  ((univ : set (subftype S)) : set A) = S := 
by tidy 

@[coe_up] lemma coe_empty {A : ftype} (S : set A) : 
  ((∅ : set (subftype S)) : set A) = ∅ :=
by tidy 

@[coe_up] lemma coe_set_is_subset {A : ftype} {S : set A} (X : set (subftype S)):
  (X : set A) ⊆ S := 
by tidy

@[coe_up] lemma coe_img_set {A : ftype} {Y Y' : set A}(hYY' : Y ⊆ Y')(X : set (subftype Y)) :
  (((embed.from_nested_pair hYY').img X) : set A) = (X : set A) := 
by {simp only [embed.img], unfold_coes, tidy}

@[coe_up] lemma coe_img_elem {A : ftype} {Y Y' : set A}(hYY' : Y ⊆ Y')(x : subftype Y) :
  (((embed.from_nested_pair hYY') x ) : A) = (x : A) := 
by {unfold_coes, tidy}

section inter_subtype

variables {A : ftype}(E : set A)

/-- the intersection X ∩ E, viewed as a set E -/
def inter_subtype (X : set A): set (subftype E) := {e : subftype E | e.val ∈ X}

@[coe_up] lemma size_inter_subtype (X E : set A) : size (inter_subtype E X) = size (E ∩ X) := 
begin
  let f : (⟨E⟩ : ftype) ↪ A := ⟨subtype.val, λ x y hxy, by {cases x, cases y, simp only [subtype.mk_eq_mk], exact hxy}⟩, 
  suffices h : f '' (inter_subtype E X) = E ∩ X, 
  { rw [←size_img_inj f (inter_subtype E X), h]},
  ext x, simp only [set.image_congr, set.mem_image, set.mem_inter_eq, function.embedding.coe_fn_mk, subtype.val_eq_coe], 
  refine ⟨λ h, _, λ h, _⟩, 
  { rcases h with ⟨x',h,rfl⟩, simp only [inter_subtype, set.mem_set_of_eq] at h, exact ⟨x'.property, h⟩,  },
  refine ⟨⟨x,h.1⟩,⟨_, by simp⟩⟩,
  simp [inter_subtype], exact h.2, 
end

@[coe_up] lemma coe_inter_subtype (X : set A): ((inter_subtype E X) : set A) = X ∩ E := 
begin
  ext x, simp only [inter_subtype, set.mem_image, set.mem_inter_eq],  
  refine ⟨λ h, _, λ h, _⟩, 
  { rcases h with ⟨⟨y,hy⟩,h,rfl⟩, simp only [subtype.coe_mk], exact ⟨h,hy⟩},
  exact ⟨⟨x,h.2⟩,⟨h.1,by simp⟩⟩,
end

end inter_subtype

end ftype 
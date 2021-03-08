
import .size --.single
open set 
-- Embedding and subftypes

open_locale classical 
noncomputable theory 
mk_simp_attribute coe_up "upwards coercion simp lemmas"

section size_lemmas 
variables {A B : Type}[fintype A][fintype B]

lemma size_img_emb (f : A ↪ B)(X : set A): 
  size (f '' X) = size X := 
by {simp_rw [size], norm_cast, apply fincard_img_emb, }

lemma type_size_le_type_size_inj (f : A ↪ B): 
  type_size A ≤ type_size B := 
by {rw [type_size, type_size, ← size_img_emb f], apply size_monotone, apply subset_univ, }

lemma size_img_inj {f : A → B}(hf : function.injective f)(X : set A): 
  size (f '' X) = size X := 
size_img_emb ⟨f , hf⟩ X

lemma size_img_equiv (f : A ≃ B)(X : set A):
  size (f '' X) = size X :=
size_img_emb (f.to_embedding) X 

lemma type_size_eq_type_size_equiv (f : A ≃ B): 
  type_size A = type_size B := 
by rw [type_size, type_size, ← size_img_equiv f, ← f.range_eq_univ, image_univ]


@[simp] lemma equiv.image_mem_image_iff_mem {f : A ≃ B}{x : A}{X : set A}: 
  f x ∈ f '' X ↔ x ∈ X := 
begin
  rw mem_image, split, 
  { rintros ⟨y, hy, hyx⟩, rw equiv.apply_eq_iff_eq at hyx, rwa ←hyx},
  exact λ hx, ⟨x, hx, rfl⟩, 
end

lemma size_preimg_equiv (f : A ≃ B)(X : set B):
  size (f ⁻¹' X) = size X :=
begin
  unfold_coes, 
  rw ←set.image_eq_preimage_of_inverse f.right_inv f.left_inv, 
  convert size_img_emb (f.symm.to_embedding) X, 
end

lemma size_subtype_img {E : set A}(X : set E): 
  size (subtype.val '' X) = size X :=
begin
  let f : E ↪ A := ⟨subtype.val, λ x y hxy, by {cases x, cases y, simp only [subtype.mk_eq_mk], exact hxy}⟩, 
  apply size_img_emb f, 
end


@[simp] lemma size_image_coe {E : set A}(X : set E): 
  size (coe '' X : set A) = size X := 
size_subtype_img X 

@[simp] lemma size_preimage_coe {E : set A}(X : set A): 
  size (coe ⁻¹' X : set E) = size (X ∩ E) := 
by {rw ← size_image_coe (coe ⁻¹' X : set E), simp, }


end size_lemmas 

instance coe_set_from_subtype {B : Type}{S : set B}: has_coe (set S) (set B) := ⟨λ X, coe '' X⟩ 
/-- the intersection X ∩ S, viewed as a (set S) -/
def inter_subtype {B : Type}(S X : set B): (set S) := coe ⁻¹' X 

variables {A : Type}[fintype A]{S : set A}

@[coe_up] lemma subtype_coe_singleton (e : S): 
  (({(e : S)} : set S) : set A) = {(e : A)} :=
image_singleton 

@[coe_up] lemma subtype_coe_size (X : set S) : size X = size (X : set A) := 
(size_subtype_img X).symm

@[coe_up] lemma subtype_coe_subset {X Y : set S}: 
  (X ⊆ Y) ↔ ((X: set A) ⊆ (Y: set A)) :=
(image_subset_image_iff subtype.coe_injective).symm

@[coe_up] lemma subtype_set_coe_inj {X Y : set S}: 
  ((X: set A) = (Y: set A)) ↔ (X = Y) :=
image_eq_image subtype.coe_injective

@[coe_up] lemma subtype_coe_ssubset  {X Y : set S}: 
  (X ⊂ Y) ↔ ((X : set A) ⊂ (Y : set A)) :=
by simp_rw [ssubset_iff_subset_not_supset, subtype_coe_subset]
  
@[coe_up] lemma subtype_coe_union {X Y : set S}: 
  (((X ∪ Y) : set S) : set A) = (X ∪ Y ) := 
image_union subtype.val X Y
 
@[coe_up] lemma subtype_coe_inter  {X Y : set S}:
  (((X ∩ Y) : set S) : set A) = (X ∩ Y) := 
(image_inter subtype.coe_injective).symm 

lemma subtype_coe_diff {X Y : set S}:
  ((X \ Y : set S) : set A) = X \ Y := 
image_diff (subtype.coe_injective) X Y 

@[coe_up] lemma coe_univ : 
  ((univ : set S) : set A) = S := 
by tidy 

@[coe_up] lemma coe_empty : 
  ((∅ : set  S) : set A) = ∅ :=
by tidy 

@[coe_up] lemma coe_set_is_subset (X : set S):
  (X : set A) ⊆ S := 
by tidy 

@[coe_up] lemma subtype_coe_compl {X : set S}:
  (((Xᶜ : set S)) : set A) = S \ (X : set A)  := 
by rw [compl_eq_univ_diff, subtype_coe_diff, coe_univ]

@[coe_up] lemma coNE_inter_subtype (X : set A): 
  ((inter_subtype S X) : set A) = X ∩ S := 
begin
  ext x, simp only [inter_subtype, set.mem_image, set.mem_inter_eq],  
  refine ⟨λ h, _, λ h, _⟩, 
  { rcases h with ⟨⟨y,hy⟩,h,rfl⟩, simp only [subtype.coe_mk], exact ⟨h,hy⟩},
  exact ⟨⟨x,h.2⟩,⟨h.1,by simp⟩⟩,
end

@[coe_up] lemma sizNE_inter_subtype (X : set A) : 
  size (inter_subtype S X) = size (X ∩ S) := 
by rw [subtype_coe_size, coNE_inter_subtype]

@[coe_up] lemma inter_subtype_eq_iff (X Y : set A):
  inter_subtype S X = inter_subtype S Y ↔ (X ∩ S = Y ∩ S):=
by rw [←subtype_set_coe_inj, coNE_inter_subtype, coNE_inter_subtype]
 
@[simp] lemma function.embedding.image_trans {A B C : Type}(e₁ : A ↪ B)(e₂ : B ↪ C)(X : set A):
  (e₁.trans e₂) '' X = e₂ '' (e₁ '' X) := 
by {unfold function.embedding.trans, rw ← image_comp, refl,   }

@[simp] lemma equiv.image_trans {A B C : Type}(e₁ : A ≃ B)(e₂ : B ≃ C)(X : set A):
  (e₁.trans e₂) '' X = e₂ '' (e₁ '' X) := 
by {unfold equiv.trans, rw ← image_comp, refl,   }
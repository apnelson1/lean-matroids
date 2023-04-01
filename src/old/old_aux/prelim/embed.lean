
import .size --.single
open set
-- Embedding and subftypes

open_locale classical
noncomputable theory
mk_simp_attribute coe_up "upwards coercion simp lemmas"

universes u v w

instance coe_set_from_subtype {β : Type*} {S : set β} : has_coe (set S) (set β) := ⟨λ X, coe '' X⟩
/-- the intersection X ∩ S, viewed as a (set S) -/
def inter_subtype {β : Type*} (S X : set β) : (set S) := coe ⁻¹' X

variables {α : Type*} [fintype α] {S : set α}

@[coe_up] lemma subtype_coe_singleton (e : S) :
  (({(e : S)} : set S) : set α) = {(e : α)} :=
image_singleton

@[coe_up] lemma subtype_coe_size (X : set S) : size X = size (X : set α) :=
(size_subtype_image X).symm

@[coe_up] lemma subtype_coe_subset {X Y : set S} :
  (X ⊆ Y) ↔ ((X: set α) ⊆ (Y: set α)) :=
(image_subset_image_iff subtype.coe_injective).symm

@[coe_up] lemma subtype_set_coe_inj {X Y : set S} :
  ((X: set α) = (Y: set α)) ↔ (X = Y) :=
image_eq_image subtype.coe_injective

@[coe_up] lemma subtype_coe_ssubset  {X Y : set S} :
  (X ⊂ Y) ↔ ((X : set α) ⊂ (Y : set α)) :=
by simp_rw [ssubset_iff_subset_not_supset, subtype_coe_subset]
 
@[coe_up] lemma subtype_coe_union {X Y : set S} :
  (((X ∪ Y) : set S) : set α) = (X ∪ Y ) :=
image_union subtype.val X Y

@[coe_up] lemma subtype_coe_inter  {X Y : set S} :
  (((X ∩ Y) : set S) : set α) = (X ∩ Y) :=
(image_inter subtype.coe_injective).symm

lemma subtype_coe_diff {X Y : set S} :
  ((X \ Y : set S) : set α) = X \ Y :=
image_diff (subtype.coe_injective) X Y

@[coe_up] lemma coe_univ :
  ((univ : set S) : set α) = S :=
by tidy

@[coe_up] lemma coe_empty :
  ((∅ : set  S) : set α) = ∅ :=
by tidy

@[coe_up] lemma coe_set_is_subset (X : set S) :
  (X : set α) ⊆ S :=
by tidy

@[coe_up] lemma subtype_coe_compl {X : set S} :
  (((Xᶜ : set S)) : set α) = S \ (X : set α)  :=
by rw [compl_eq_univ_diff, subtype_coe_diff, coe_univ]

@[coe_up] lemma coNE_inter_subtype (X : set α) :
  ((inter_subtype S X) : set α) = X ∩ S :=
begin
  ext x, simp only [inter_subtype, set.mem_image, set.mem_inter_eq], 
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨⟨y,hy⟩,h,rfl⟩, simp only [subtype.coe_mk], exact ⟨h,hy⟩},
  exact ⟨⟨x,h.2⟩,⟨h.1,by simp⟩⟩,
end

@[coe_up] lemma sizNE_inter_subtype (X : set α) :
  size (inter_subtype S X) = size (X ∩ S) :=
by rw [subtype_coe_size, coNE_inter_subtype]

@[coe_up] lemma inter_subtype_eq_iff (X Y : set α) :
  inter_subtype S X = inter_subtype S Y ↔ (X ∩ S = Y ∩ S) :=
by rw [←subtype_set_coe_inj, coNE_inter_subtype, coNE_inter_subtype]

@[simp] lemma function.embedding.image_trans {α β C : Type*} (e₁ : α ↪ β) (e₂ : β ↪ C) (X : set α) :
  (e₁.trans e₂) '' X = e₂ '' (e₁ '' X) :=
by {unfold function.embedding.trans, rw ← image_comp, refl,   }

@[simp] lemma equiv.image_trans {α β γ : Type*} (e₁ : α ≃ β) (e₂ : β ≃ γ) (X : set α) :
  (e₁.trans e₂) '' X = e₂ '' (e₁ '' X) :=
by {unfold equiv.trans, rw ← image_comp, refl,   }
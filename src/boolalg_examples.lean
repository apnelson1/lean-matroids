
import boolalg boolalg_single
namespace boolalg 
-- Embedding and subalgebras

local attribute [instance] classical.prop_decidable

variables {A : boolalg}

@[ext] structure embed (A B : boolalg) :=
  (f : A → B)
  (on_bot : f ⊥ = ⊥)
  -- note : top is not respected by embedding
  (on_inter (X Y) : f (X ∩ Y) = (f X) ∩ (f Y))
  (on_union (X Y) : f (X ∪ Y) = (f X) ∪ (f Y))
  -- note : compl is not respected by embedding
  (on_size (X : A) : size X = size (f X))

lemma embed.on_subset {A B : boolalg} (emb : embed A B) {X Y : A} :
  (X ⊆ Y) → (emb.f X) ⊆ (emb.f Y) := 
  λ h, by {rw inter_subset at *, rw [←emb.on_inter, h]}

def embed.single_emb {A B : boolalg} (emb : embed A B) : single A → single B := 
  λ e, ⟨emb.f e.val, (eq.trans (emb.on_size e.val).symm e.property :size (emb.f e.val) = 1 )⟩  
  

def embed.id : embed A A := 
{ 
  f        := id,
  on_bot   := rfl,
  on_inter := by intros X Y; refl,
  on_union := by intros X Y; refl,
  on_size  := by intros X; refl,
}

def embed.compose {A B C: boolalg} : (embed A B) → (embed B C) → (embed A C) := λ e1 e2,
{ 
  f        := e2.f ∘ e1.f,
  on_bot   := by simp only [function.comp_app]; rw [e1.on_bot, e2.on_bot],
  on_inter := λ X Y, by simp only [function.comp_app]; rw [e1.on_inter, e2.on_inter],
  on_union := λ X Y, by simp only [function.comp_app]; rw [e1.on_union, e2.on_union],
  on_size  := λ X, (e1.on_size X).trans (e2.on_size (e1.f X)),
}

def subalg {A : boolalg}(ground : A) : boolalg :=  
{ 
  member := {X : A | X ⊆ ground},
  bot := ⟨⊥, bot_subset ground⟩,
  top := ⟨ground, subset_refl ground⟩,
  subset := λ X Y, X.val ⊆ Y.val,  
  inter := λ X Y, ⟨X.val ∩ Y.val, inter_of_subsets X.val Y.val ground X.property⟩,
  union := λ X Y, ⟨X.val ∪ Y.val, union_of_subsets X.property Y.property⟩,
  compl := λ X, ⟨ground \ X.val, diff_subset ground X.val⟩,
  size := λ X, size X.val, 
  size_bot_ax := @size_bot A, 
  size_nonneg_ax := λ X, size_nonneg X.val,
  size_modular_ax := λ X Y, size_modular X.val Y.val, 
  contains_single_ax := λ X hX, by {rcases contains_single X.val _ with ⟨Y,⟨hs,h1⟩⟩, 
                                    use ⟨Y, subset_trans hs X.property⟩, exact ⟨hs,h1⟩, 
                                      exact λ hne, by {cases X, apply hX, simp only [subtype.mk_eq_mk] at *, 
                                      assumption}},
  inter_comm_ax := λ X Y, subtype.eq (inter_comm X.val Y.val), 
  union_comm_ax := λ X Y, subtype.eq (union_comm X.val Y.val),
  union_distrib_right_ax := λ X Y Z, subtype.eq (union_distrib_right X Y Z),
  inter_distrib_right_ax := λ X Y Z, subtype.eq (inter_distrib_right X Y Z),
  union_subset_ax := λ X Y, by {refine ⟨ λ h, _,λ h, _⟩, rw union_subset at h, simp_rw h, 
                                simp only [subtype.coe_eta, subtype.val_eq_coe], rw union_subset,  
                                cases Y, cases X, simp only [subtype.mk_eq_mk] at *, assumption},
  inter_top_ax := λ X, by {cases X, simp only [subtype.mk_eq_mk], exact inter_subset_mp X_property},
  union_bot_ax := λ X, by {cases X, simp only [subtype.mk_eq_mk], apply union_bot},
  union_compl_ax := λ X, by {simp only [subtype.mk_eq_mk, subtype.val_eq_coe], 
                                exact union_diff_of_subset X.property},
  inter_compl_ax := λ X, by {simp only [subtype.mk_eq_mk, subtype.val_eq_coe], apply inter_diff},
  inter_assoc_ax := λ X Y Z, subtype.eq (inter_assoc X.1 Y.1 Z.1),
  union_assoc_ax := λ X Y Z, subtype.eq (union_assoc X.1 Y.1 Z.1),
}

def embed.from_subset (X : A) : embed (subalg X) A := 
⟨(λ X,X.val),rfl,(λ X Y,rfl),(λ X Y,rfl),(λ X,rfl)⟩ 

def embed.from_nested_pair {X₁ X₂ : A} : (X₁ ⊆ X₂) → embed (subalg X₁) (subalg X₂) := fun hX₁X₂, 
⟨λ X, ⟨X.val, subset_trans X.property hX₁X₂⟩,rfl, (λ X Y, rfl), (λ X Y, rfl), (λ X, rfl)⟩ 

lemma embed.compose_subset_nested_pair (X₁ X₂ : A) (hX₁X₂ : X₁ ⊆ X₂) :
  (embed.compose (embed.from_nested_pair hX₁X₂) (embed.from_subset X₂)) = embed.from_subset X₁ := rfl 

lemma embed.compose_nested_triple (X₁ X₂ X₃ : A) (h₁₂ : X₁ ⊆ X₂) (h₂₃ : X₂ ⊆ X₃) :
  (embed.compose (embed.from_nested_pair h₁₂) (embed.from_nested_pair h₂₃)) = embed.from_nested_pair (subset_trans h₁₂ h₂₃) := rfl

def embed.to_subalg (X Y : A) (h: X ⊆ Y) : subalg Y := ⟨X,h⟩ 

--Subalgebra coercion 

instance coe_set_from_subalg {A : boolalg} {S : A} : has_coe (subalg S) A := ⟨(embed.from_subset S).f⟩ 

instance coe_single_from_subalg {A : boolalg} {S : A} : has_coe (single (subalg S)) (single A) := ⟨(embed.from_subset S).single_emb⟩ 

@[simp] lemma coe_single_subalg_compose {A : boolalg} {S : A} (e : single (subalg S)) : ((e: single A): A) = (e : A) := rfl  
lemma coe_subalg_single_compose {A : boolalg} {S : A} (e : single (subalg S)) : ((e: subalg S): A) = (e : A) := rfl  

lemma subalg_coe_size {A : boolalg} {S : A} (X : subalg S) : size (X : A) = size X := 
  (embed.from_subset S).on_size X

lemma subalg_coe_subset {A : boolalg} {S : A} {X Y : subalg S}: (X ⊆ Y) → ((X:A) ⊆ (Y:A)) :=
  (embed.from_subset S).on_subset 

lemma subalg_coe_union {A : boolalg} {S : A} {X Y : subalg S}: ((X ∪ Y) : A) = ((X:A) ∪ (Y:A)) := rfl 
lemma subalg_coe_inter {A : boolalg} {S : A} {X Y : subalg S}: ((X ∩ Y) : A) = ((X:A) ∩ (Y:A)) := rfl 
  
lemma coe_top {A : boolalg} (S : A) : ((⊤ : subalg S) : A) = S := rfl 

  --λ X Y, (embed.from_subset S).on_union X Y


-- This next coe doesn't seem to work in practice, even when a P ⊆ Q proof term is in the local context 
instance coe_from_nested_pair {A : boolalg} {P Q: A} {hPQ : P ⊆ Q} : has_coe (subalg P) (subalg Q) := ⟨(embed.from_nested_pair hPQ).f⟩ 


/-instance embed.coe_to_fun {A B : boolalg.boolalg} : has_coe_to_fun (boolalg.embed A B) := {
  F := (λ _, A → B),
  coe := λ emb, emb.f,
}-/
--def subalg.embed {E : A} : boolalg.embed (subalg E) A := sorry



---- Isomorphisms 

structure iso (A B : boolalg) := 
  (fwd : embed A B)
  (bwd : embed B A)
  (fwd_then_bwd : embed.compose fwd bwd = embed.id)
  (bwd_then_fwd : embed.compose bwd fwd = embed.id)

--def boolalg.canonical (size : ℤ) :
--  (0 ≤ size) → boolalg := sorry

-- Construct a boolalg from a finite set S 
def powersetalg (γ : Type)[fintype γ][decidable_eq γ] : boolalg := 
{ 
  member := finset γ,
  bot := ∅,
  top := finset.univ,
  inter := λ X Y, X ∩ Y,
  union := λ X Y, X ∪ Y,
  compl := λ X, Xᶜ,
  subset := λ X Y, X ⊆ Y, 
  size := λ X, (X.card : ℤ),
  size_bot_ax := by simp only [finset.card_empty, int.coe_nat_zero],
  size_nonneg_ax := by simp only [forall_const, int.coe_nat_nonneg],
  size_modular_ax := λ X Y, by linarith [finset.card_union_add_card_inter X Y],
  contains_single_ax := λ X hX, by {cases finset.nonempty.bex (finset.nonempty_iff_ne_empty.mpr hX) 
                                    with e he, use {e}, split, exact finset.singleton_subset_iff.mpr he, 
                                    rw finset.card_singleton, refl},
  inter_comm_ax := finset.inter_comm,
  union_comm_ax := finset.union_comm,
  inter_distrib_right_ax := finset.inter_distrib_right,
  union_distrib_right_ax := finset.union_distrib_right, 
  inter_assoc_ax := finset.inter_assoc,
  union_assoc_ax := finset.union_assoc,
  inter_top_ax := finset.inter_univ, 
  union_bot_ax := finset.union_empty, 
  union_compl_ax := λ X, by {rw finset.compl_eq_univ_sdiff; simp only [finset.union_eq_right_iff_subset, 
                            finset.union_sdiff_self_eq_union], intros a a_1, simp only [finset.mem_univ]},  
  inter_compl_ax := λ X, by {ext1, simp only [finset.not_mem_empty, finset.mem_compl, 
                                and_not_self, finset.mem_inter]},
  union_subset_ax := λ X Y, finset.union_eq_right_iff_subset.symm
}

end boolalg 
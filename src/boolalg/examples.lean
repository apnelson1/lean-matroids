
import .basic .single
namespace boolalg 
-- Embedding and subalgebras

local attribute [instance] classical.prop_decidable

variables {A : boolalg}

@[ext] structure embed (A B : boolalg) :=
  (f     : A.E → B.E )
  (f_inj : ∀ {x x' : A.E}, f x = f x' → x = x')
  
/-lemma embed.on_subset {A B : boolalg} (emb : embed A B) {X Y : A} :
  (X ⊆ Y) → (emb.f X) ⊆ (emb.f Y) := 
  λ h, by {rw subset_def_inter at *, rw [←emb.on_inter, h]}

def embed.single_emb {A B : boolalg} (emb : embed A B) : single A → single B := 
  λ e, ⟨emb.f e.val, (eq.trans (emb.on_size e.val).symm e.property :size (emb.f e.val) = 1 )⟩  
-/

def embed.id : embed A A := 
{ 
  f        := λ x, x,
  f_inj    := by simp only [imp_self, forall_2_true_iff],
}

def embed.compose {A B C: boolalg} : (embed A B) → (embed B C) → (embed A C) := λ e1 e2,
{ 
  f        := e2.f ∘ e1.f,
  f_inj    := λ x x' h, e1.f_inj (e2.f_inj h), 
}

def subalg {A : boolalg}(ground : A) : boolalg :=  
let new_E  := {x : A.E // x ∈ ground} in  
   --img     := λ (X : set (new_E)) (u : A.E), ∃ (h : u ∈ ground), (⟨u,h⟩ : new_E) ∈ X  in 
{ 
  E := new_E, 
  is_fin := 
  begin
    let ft := as_finset A ground, 
    refine ⟨⟨_,_⟩,trivial⟩,
    from finset.subtype.fintype ft, 
  end, 
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
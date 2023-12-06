import data.zmod.basic
import mathlib.data.set.finite
import mathlib.data.set.basic
import analysis.inner_product_space.gram_schmidt_ortho
import linear_algebra.basis
import linear_algebra.linear_independent
import order.minimal 
import mathlib.order.minimal

universe u
variables {α γ : Type} {β 𝔽 : Type*} {I B : set α} {x : α}
variables {W W' : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] [add_comm_group W'] [module 𝔽 W']

open function set submodule finite_dimensional

/-- A predicate `P` on sets satisfies the exchange property if, for all `X` and `Y` satisfying `P`
  and all `a ∈ X \ Y`, there exists `b ∈ Y \ X` so that swapping `a` for `b` in `X` maintains `P`.-/
def exchange_property (P : set α → Prop) : Prop :=
  ∀ X Y, P X → P Y → ∀ a ∈ X \ Y, ∃ b ∈ Y \ X, P (insert b (X \ {a}))

def exists_maximal_subset_property (P : set α → Prop) (X : set α) : Prop := 
  ∀ I, P I → I ⊆ X → (maximals (⊆) {Y | P Y ∧ I ⊆ Y ∧ Y ⊆ X}).nonempty 

lemma set.injective_iff_forall_inj_on_pair {f : α → β} : injective f ↔ ∀ a b, inj_on f {a, b} :=
⟨λ h a b, h.inj_on _, λ h a b hab,
  h _ _ (mem_insert _ _) (mem_insert_of_mem _ $ mem_singleton _) hab⟩

@[ext] structure matroid_in (α : Type*) :=
  (ground : set α)
  (base : set α → Prop)
  (exists_base' : ∃ B, base B)
  (base_exchange' : exchange_property base)
  (maximality : ∀ X ⊆ ground, exists_maximal_subset_property (λ I, ∃ B, base B ∧ I ⊆ B) X)
  (subset_ground' : ∀ B, base B → B ⊆ ground)

noncomputable theory


open_locale classical

namespace matroid_in

def E (M : matroid_in α) : set α := M.ground

@[simp] lemma ground_eq_E (M : matroid_in α) : M.ground = M.E := rfl

section tac

@[user_attribute]
meta def ssE_rules : user_attribute :=
{ name := `ssE_rules,
  descr := "lemmas usable to prove subset of ground set" }

@[user_attribute]
meta def ssE_finish_rules : user_attribute :=
{ name := `ssE_finish_rules,
  descr := "finishing lemmas usable to prove subset of ground set" }

meta def ssE_finish : tactic unit := `[solve_by_elim with ssE_finish_rules {max_depth := 2}] 

meta def ssE : tactic unit := `[solve_by_elim with ssE_rules 
  {max_depth := 3, discharger := ssE_finish}]

@[ssE_rules] private lemma insert_subset_ground {e : α} {X : set α} {M : matroid_in α} 
(he : e ∈ M.E) (hX : X ⊆ M.E) : insert e X ⊆ M.E := insert_subset.mpr ⟨he, hX⟩

@[ssE_rules] private lemma inter_right_subset_ground {X Y : set α} {M : matroid_in α} 
(hX : X ⊆ M.E) : X ∩ Y ⊆ M.E := (inter_subset_left _ _).trans hX 

@[ssE_rules] private lemma inter_left_subset_ground {X Y : set α} {M : matroid_in α}
(hX : X ⊆ M.E) : Y ∩ X ⊆ M.E := (inter_subset_right _ _).trans hX 

@[ssE_rules] private lemma diff_subset_ground {X Y : set α} {M : matroid_in α}
(hX : X ⊆ M.E) : X \ Y ⊆ M.E := (diff_subset _ _).trans hX 

attribute [ssE_rules] mem_of_mem_of_subset empty_subset subset.rfl union_subset

end tac

variables {M : matroid_in α}

@[simp] lemma ground_inter_right {X : set α} {M : matroid_in α} (hXE : X ⊆ M.E . ssE) : M.E ∩ X = X :=
inter_eq_self_of_subset_right hXE 

@[simp] lemma ground_inter_left {X : set α} {M : matroid_in α} (hXE : X ⊆ M.E . ssE) : X ∩ M.E = X :=
inter_eq_self_of_subset_left hXE 

@[ssE_finish_rules] lemma base.subset_ground (hB : M.base B) : B ⊆ M.E :=
M.subset_ground' B hB  

lemma exists_base (M : matroid_in α) : ∃ B, M.base B := M.exists_base'

lemma base.exchange {B₁ B₂ : set α} {e : α} (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hx : e ∈ B₁ \ B₂) :
  ∃ y ∈ B₂ \ B₁, M.base (insert y (B₁ \ {e}))  :=
M.base_exchange' B₁ B₂ hB₁ hB₂ _ hx

/-- A set is independent if it is contained in a base.  -/
def indep (M : matroid_in α) (I : set α) : Prop := ∃ B, M.base B ∧ I ⊆ B

/-- A subset of `M.E` is dependent if it is not independent . -/
def dep (M : matroid_in α) (D : set α) : Prop := ¬M.indep D ∧ D ⊆ M.E   

@[simp] lemma not_indep_iff {X : set α} (hX : X ⊆ M.E . ssE) : ¬ M.indep X ↔ M.dep X := 
by rw [dep, and_iff_left hX]  

lemma dep.not_indep {D : set α} (hD : M.dep D) : ¬ M.indep D := 
hD.1  

lemma indep_iff_subset_base : M.indep I ↔ ∃ B, M.base B ∧ I ⊆ B := iff.rfl

@[ssE_finish_rules] lemma indep.subset_ground (hI : M.indep I) : I ⊆ M.E := 
by { obtain ⟨B, hB, hIB⟩ := hI, exact hIB.trans hB.subset_ground } 

/-- A basis for a set `X ⊆ M.E` is a maximal independent subset of `X`
  (Often in the literature, the word 'basis' is used to refer to what we call a 'base'). -/
def basis (M : matroid_in α) (I X : set α) : Prop := 
  I ∈ maximals (⊆) {A | M.indep A ∧ A ⊆ X} ∧ X ⊆ M.E  

/-- A coindependent set is a subset of `M.E` that is disjoint from some base -/
def coindep (M : matroid_in α) (I : set α) : Prop := I ⊆ M.E ∧ (∃ B, M.base B ∧ disjoint I B)  

lemma basis.indep {X : set α} (hI : M.basis I X) : M.indep I := hI.1.1.1

lemma basis.subset {X : set α} (hI : M.basis I X) : I ⊆ X := hI.1.1.2

lemma basis.eq_of_subset_indep {X J : set α} (hI : M.basis I X) (hJ : M.indep J) (hIJ : I ⊆ J) 
  (hJX : J ⊆ X) : I = J :=
hIJ.antisymm (hI.1.2 ⟨hJ, hJX⟩ hIJ)

@[ssE_finish_rules] lemma basis.subset_ground {X : set α} (hI : M.basis I X) : X ⊆ M.E :=
hI.2 

@[ssE_finish_rules] lemma basis.subset_ground_left {X : set α} (hI : M.basis I X) : I ⊆ M.E := 
hI.indep.subset_ground

lemma basis_iff' {X : set α} : 
  M.basis I X ↔ (M.indep I ∧ I ⊆ X ∧ ∀ J, M.indep J → I ⊆ J → J ⊆ X → I = J) ∧ X ⊆ M.E :=
begin
  simp_rw [basis, and.congr_left_iff, maximals, mem_set_of_eq, and_imp, sep_set_of, 
    mem_set_of_eq, and_assoc, and.congr_right_iff],   
  intros hXE hI hIX, 
  exact ⟨λ h J hJ hIJ hJX, hIJ.antisymm (h hJ hJX hIJ), 
    λ h J hJ hIJ hJX, (h J hJ hJX hIJ).symm.subset⟩,
end 

lemma basis_iff {X : set α} (hX : X ⊆ M.E . ssE) : 
  M.basis I X ↔ (M.indep I ∧ I ⊆ X ∧ ∀ J, M.indep J → I ⊆ J → J ⊆ X → I = J) :=
by rw [basis_iff', and_iff_left hX]

private lemma antichain_of_exch {B B' : set α} {base : set α → Prop} (exch : exchange_property base) 
(hB : base B) (hB' : base B') (h : B ⊆ B') : B = B' :=
begin
  refine h.antisymm (diff_eq_empty.mp (eq_empty_iff_forall_not_mem.mpr (λ x hx, _))), 
  obtain ⟨e,he,-⟩ :=  exch _ _ hB' hB _ hx, 
  exact he.2 (h he.1), 
end 

lemma base.eq_of_subset_base {B₁ B₂ : set α} (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hB₁B₂ : B₁ ⊆ B₂) :
  B₁ = B₂ :=
antichain_of_exch M.base_exchange' hB₁ hB₂ hB₁B₂

lemma base.eq_of_subset_indep (hB : M.base B) (hI : M.indep I) (hBI : B ⊆ I) : B = I :=
let ⟨B', hB', hB'I⟩ := hI in hBI.antisymm (by rwa hB.eq_of_subset_base hB' (hBI.trans hB'I))

lemma base.dep_of_ssubset {X : set α} (hB : M.base B) (h : B ⊂ X) (hX : X ⊆ M.E . ssE) : M.dep X :=
⟨λ hX, h.ne (hB.eq_of_subset_indep hX h.subset), hX⟩

lemma basis.dep_of_ssubset {X : set α} (hI : M.basis I X) {Y : set α} (hIY : I ⊂ Y) (hYX : Y ⊆ X) : 
  M.dep Y :=
begin
  rw [←not_indep_iff (hYX.trans hI.subset_ground)], 
  exact λ hY, hIY.ne (hI.eq_of_subset_indep hY hIY.subset hYX), 
end 

lemma basis.insert_dep {X : set α} {e : α} (hI : M.basis I X) (he : e ∈ X \ I) : 
  M.dep (insert e I) :=
hI.dep_of_ssubset (ssubset_insert he.2) (insert_subset.mpr ⟨he.1,hI.subset⟩)

lemma basis.mem_of_insert_indep {X : set α} {e : α} (hI : M.basis I X) (he : e ∈ X) 
  (hIe : M.indep (insert e I)) : e ∈ I :=
by_contra (λ heI, (hI.insert_dep ⟨he, heI⟩).not_indep hIe) 

lemma base.indep (hB : M.base B) : M.indep B := ⟨B, hB, subset_rfl⟩

lemma indep.subset {J : set α} (hJ : M.indep J) (hIJ : I ⊆ J) : M.indep I :=
by {obtain ⟨B, hB, hJB⟩ := hJ, exact ⟨B, hB, hIJ.trans hJB⟩}

lemma indep.inter_right (hI : M.indep I) (X : set α) : M.indep (I ∩ X) :=
hI.subset (inter_subset_left _ _)

lemma basis.exists_base {X : set α} (hI : M.basis I X) : ∃ B, M.base B ∧ I = B ∩ X :=
begin
  obtain ⟨B,hB, hIB⟩ := hI.indep,
  refine ⟨B, hB, subset_antisymm (subset_inter hIB hI.subset) _⟩,
  rw hI.eq_of_subset_indep (hB.indep.inter_right X) (subset_inter hIB hI.subset)
    (inter_subset_right _ _),
end

lemma indep.diff (hI : M.indep I) (X : set α) : M.indep (I \ X) := hI.subset (diff_subset _ _)

lemma indep.subset_basis_of_subset {X : set α} (hI : M.indep I) (hIX : I ⊆ X) (hX : X ⊆ M.E . ssE) : 
  ∃ J, M.basis J X ∧ I ⊆ J :=
begin
  obtain ⟨J, ⟨(hJ : M.indep J),hIJ,hJX⟩, hJmax⟩ := M.maximality X hX I hI hIX,
  use J, 
  rw [and_iff_left hIJ, basis_iff, and_iff_right hJ, and_iff_right hJX], 
  exact λ K hK hJK hKX, hJK.antisymm (hJmax ⟨hK, hIJ.trans hJK, hKX⟩ hJK),  
end

@[simp] lemma empty_indep (M : matroid_in α) : M.indep ∅ :=
exists.elim M.exists_base (λ B hB, ⟨_, hB, B.empty_subset⟩)

lemma exists_basis (M : matroid_in α) (X : set α) (hX : X ⊆ M.E . ssE) : 
  ∃ I, M.basis I X := let ⟨I, hI, _⟩ := M.empty_indep.subset_basis_of_subset (empty_subset X) in ⟨_,hI⟩

lemma basis_iff_mem_maximals {X : set α} (hX : X ⊆ M.E . ssE): 
  M.basis I X ↔ I ∈ maximals (⊆) (λ (I : set α), M.indep I ∧ I ⊆ X) :=
begin
  simp_rw [basis_iff, mem_maximals_prop_iff, and_assoc, and_imp, and.congr_right_iff], 
  exact λ hI hIX, ⟨λ h J hJ hJX hIJ, h J hJ hIJ hJX, λ h J hJ hJX hIJ, h hJ hIJ hJX⟩, 
end 

lemma indep.exists_insert_of_not_base (hI : M.indep I) (hI' : ¬M.base I) (hB : M.base B) : 
  ∃ e ∈ B \ I, M.indep (insert e I) :=
begin
  obtain ⟨B', hB', hIB'⟩ := hI, 
  obtain ⟨x, hxB', hx⟩ := exists_of_ssubset (hIB'.ssubset_of_ne (by { rintro rfl, exact hI' hB' })), 
  obtain (hxB | hxB) := em (x ∈ B), 
  { exact ⟨x, ⟨hxB, hx⟩ , ⟨B', hB', insert_subset.mpr ⟨hxB',hIB'⟩⟩⟩ },
  obtain ⟨e,he, hbase⟩ := hB'.exchange hB ⟨hxB',hxB⟩,    
  exact ⟨e, ⟨he.1, not_mem_subset hIB' he.2⟩, 
    ⟨_, hbase, insert_subset_insert (subset_diff_singleton hIB' hx)⟩⟩,  
end  


lemma base.base_of_basis_supset {X : set α} (hB : M.base B) (hBX : B ⊆ X) (hIX : M.basis I X) : 
M.base I :=
begin
  by_contra h, 
  obtain ⟨e,heBI,he⟩ := hIX.indep.exists_insert_of_not_base h hB, 
  exact heBI.2 (hIX.mem_of_insert_indep (hBX heBI.1) he), 
end 

lemma indep.exists_base_subset_union_base (hI : M.indep I) (hB : M.base B) : 
  ∃ B', M.base B' ∧ I ⊆ B' ∧ B' ⊆ I ∪ B :=
begin
  obtain ⟨B', hB', hIB'⟩ := hI.subset_basis_of_subset (subset_union_left I B),  
  exact ⟨B', hB.base_of_basis_supset (subset_union_right _ _) hB', hIB', hB'.subset⟩, 
end  

def matroid_of_base {α : Type*} (E : set α) (base : set α → Prop) 
(exists_base : ∃ B, base B) (base_exchange : exchange_property base) 
(maximality : ∀ X ⊆ E, exists_maximal_subset_property (λ I, ∃ B, base B ∧ I ⊆ B) X)
(support : ∀ B, base B → B ⊆ E) : matroid_in α := 
⟨E, base, exists_base, base_exchange, maximality, support⟩

def matroid_of_indep (E : set α) (indep : set α → Prop) (h_empty : indep ∅) 
(h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I) 
(h_aug : ∀⦃I B⦄, indep I → I ∉ maximals (⊆) indep → B ∈ maximals (⊆) indep → 
  ∃ x ∈ B \ I, indep (insert x I))
(h_maximal : ∀ X ⊆ E, exists_maximal_subset_property indep X) 
(h_support : ∀ I, indep I → I ⊆ E) : 
  matroid_in α :=
matroid_of_base E (λ B, B ∈ maximals (⊆) indep)
(begin
  obtain ⟨B, ⟨hB,-,-⟩, hB₁⟩ := h_maximal E subset.rfl ∅ h_empty (empty_subset _), 
  exact ⟨B, hB, λ B' hB' hBB', hB₁ ⟨hB',empty_subset _,h_support B' hB'⟩ hBB'⟩, 
end)
(begin
  rintros B B' ⟨hB,hBmax⟩ ⟨hB',hB'max⟩ e he, 
  obtain ⟨f,hf,hfB⟩ :=  h_aug (h_subset hB (diff_subset B {e})) _ ⟨hB',hB'max⟩, 
  simp only [mem_diff, mem_singleton_iff, not_and, not_not] at hf, 
  have hfB' : f ∉ B, 
  { intro hfB, have := hf.2 hfB, subst this, exact he.2 hf.1 }, 
  { refine ⟨f, ⟨hf.1, hfB'⟩, by_contra (λ hnot, _)⟩,
    obtain ⟨x,hxB, hind⟩ :=  h_aug hfB hnot ⟨hB, hBmax⟩, 
    simp only [mem_diff, mem_insert_iff, mem_singleton_iff, not_or_distrib, not_and, not_not] 
      at hxB, 
    have := hxB.2.2 hxB.1, subst this, 
    rw [insert_comm, insert_diff_singleton, insert_eq_of_mem he.1] at hind, 
    exact not_mem_subset (hBmax hind (subset_insert _ _)) hfB' (mem_insert _ _) },
  simp only [maximals, mem_sep_iff, diff_singleton_subset_iff, not_and, not_forall, exists_prop],
  exact λ _, ⟨B, hB, subset_insert _ _, λ hss, (hss he.1).2 rfl⟩, 
end)
(begin
  rintro X hXE I ⟨B, hB, hIB⟩ hIX, 
  -- rintro I X ⟨B, hB,  hIB⟩ hIX, 
  obtain ⟨J, ⟨hJ, hIJ, hJX⟩, hJmax⟩ := h_maximal X hXE I (h_subset hB.1 hIB) hIX, 
  obtain ⟨BJ, hBJ⟩ := h_maximal E subset.rfl J hJ (h_support J hJ), 
  refine ⟨J, ⟨⟨BJ,_, hBJ.1.2.1⟩ ,hIJ,hJX⟩, _⟩,  
  { exact ⟨hBJ.1.1, λ B' hB' hBJB', hBJ.2 ⟨hB',hBJ.1.2.1.trans hBJB', h_support B' hB'⟩ hBJB'⟩ },
  simp only [mem_set_of_eq, and_imp, forall_exists_index], 
  rintro A B' ⟨(hB'i : indep _), hB'max⟩ hB'' hIA hAX hJA, 
  exact hJmax ⟨h_subset hB'i hB'', hIA, hAX⟩ hJA,
end )
(λ B hB, h_support B hB.1)

@[simp] lemma matroid_of_indep_apply (E : set α) (indep : set α → Prop) (h_empty : indep ∅) 
(h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I) 
(h_aug : ∀⦃I B⦄, indep I → I ∉ maximals (⊆) indep → B ∈ maximals (⊆) indep → 
  ∃ x ∈ B \ I, indep (insert x I))
(h_maximal : ∀ X ⊆ E, exists_maximal_subset_property indep X) 
(h_support : ∀ I, indep I → I ⊆ E)  : 
(matroid_of_indep E indep h_empty h_subset h_aug h_maximal h_support).indep = indep :=
begin
  ext I, 
  simp only [matroid_in.indep, matroid_of_indep], 
  refine ⟨λ ⟨B, hB, hIB⟩, h_subset hB.1 hIB, λ hI, _⟩, 
  obtain ⟨B, ⟨hB, hIB, -⟩, hBmax⟩ :=  h_maximal E subset.rfl I hI (h_support _ hI), 
  exact ⟨B, ⟨hB, λ B' hB' hBB', hBmax ⟨hB', hIB.trans hBB', h_support _ hB'⟩ hBB'⟩, hIB⟩, 
end 

lemma eq_of_base_iff_base_forall {M₁ M₂ : matroid_in α} (hE : M₁.E = M₂.E) 
(h : ∀ B ⊆ M₁.E, (M₁.base B ↔ M₂.base B)) : M₁ = M₂ :=
begin
  apply matroid_in.ext _ _ hE, 
  ext B, 
  refine ⟨λ h', (h _ h'.subset_ground).mp h', 
    λ h', (h _ (h'.subset_ground.trans_eq hE.symm)).mpr h'⟩,
end 

section dual

/-- This is really an order-theory lemma. Not clear where to put it, though.  -/
lemma base_compl_iff_mem_maximals_disjoint_base : 
  M.base Bᶜ ↔ B ∈ maximals (⊆) {I | ∃ B, M.base B ∧ disjoint I B} :=
begin
  simp_rw ←subset_compl_iff_disjoint_left, 
  refine ⟨λ h, ⟨⟨Bᶜ,h,subset.rfl⟩, _⟩, _⟩,
  { rintro X ⟨B', hB', hXB'⟩ hBX, 
    rw [←compl_subset_compl] at ⊢ hBX,
    rwa ←hB'.eq_of_subset_base h (hXB'.trans hBX) },
  rintro ⟨⟨B',hB',hBB'⟩,h⟩, 
  rw subset_compl_comm at hBB', 
  rwa [hBB'.antisymm (h ⟨_, hB', _⟩ hBB'), compl_compl],   
  rw compl_compl, 
end 

lemma base_compl_iff_mem_maximals_disjoint_base' (hB : B ⊆ M.E . ssE) : 
  M.base (M.E \ B) ↔ B ∈ maximals (⊆) {I | I ⊆ M.E ∧ ∃ B, M.base B ∧ disjoint I B} := 
begin
  refine ⟨λ h, ⟨⟨hB,_,h,disjoint_sdiff_right⟩,_⟩, λ h, _⟩, 
  { rintro X ⟨hXE,B', hB', hXB'⟩ hBX,
    rw [hB'.eq_of_subset_base h (subset_diff.mpr ⟨hB'.subset_ground,_⟩), 
      ←subset_compl_iff_disjoint_right, diff_eq, compl_inter, compl_compl] at hXB', 
    { refine (subset_inter hXE hXB').trans _, 
      rw [inter_distrib_left, inter_compl_self, empty_union],
      exact inter_subset_right _ _ },
    exact (disjoint_of_subset_left hBX hXB').symm },
  obtain ⟨⟨-, B', hB', hIB'⟩, h⟩ := h, 
  suffices : B' = M.E \ B, rwa ←this, 
  rw [subset_antisymm_iff, subset_diff, disjoint.comm, and_iff_left hIB', 
    and_iff_right hB'.subset_ground, diff_subset_iff], 

  intros e he, 
  rw [mem_union, or_iff_not_imp_right], 
  intros heB', 
  refine h ⟨insert_subset.mpr ⟨he, hB⟩, ⟨B', hB', _⟩⟩ 
    (subset_insert _ _) (mem_insert e B), 
  rw [←union_singleton, disjoint_union_left, disjoint_singleton_left], 
  exact ⟨hIB', heB'⟩, 
end 

def dual (M : matroid_in α) : matroid_in α := 
matroid_of_indep M.E (λ I, I ⊆ M.E ∧ ∃ B, M.base B ∧ disjoint I B) 
⟨empty_subset M.E, M.exists_base.imp (λ B hB, ⟨hB, empty_disjoint _⟩)⟩ 
(begin
  rintro I J ⟨hJE, B, hB, hJB⟩ hIJ, 
  exact ⟨hIJ.trans hJE, ⟨B, hB, disjoint_of_subset_left hIJ hJB⟩⟩, 
end) 
(begin
  rintro I X ⟨hIE, B, hB, hIB⟩ hI_not_max hX_max,  
  have hXE := hX_max.1.1, 
  have hB' := (base_compl_iff_mem_maximals_disjoint_base' hXE).mpr hX_max,
  
  set B' := M.E \ X with hX, 
  have hI := (not_iff_not.mpr (base_compl_iff_mem_maximals_disjoint_base')).mpr hI_not_max, 
  obtain ⟨B'', hB'', hB''₁, hB''₂⟩ := (hB'.indep.diff I).exists_base_subset_union_base hB, 
  rw [←compl_subset_compl, ←hIB.sdiff_eq_right, ←union_diff_distrib, diff_eq, compl_inter, 
    compl_compl, union_subset_iff, compl_subset_compl] at hB''₂, 
  
  have hssu := (subset_inter (hB''₂.2) hIE).ssubset_of_ne 
    (by { rintro rfl, apply hI, convert hB'', simp }),
  obtain ⟨e, ⟨(heB'' : e ∉ _), heE⟩, heI⟩ := exists_of_ssubset hssu, 
  use e, 
  rw [mem_diff, insert_subset, and_iff_left heI, and_iff_right heE, and_iff_right hIE], 
  refine ⟨by_contra (λ heX, heB'' (hB''₁ ⟨_, heI⟩)), ⟨B'', hB'', _⟩⟩, 
  { rw [hX], exact ⟨heE, heX⟩ },
  rw [←union_singleton, disjoint_union_left, disjoint_singleton_left, and_iff_left heB''], 
  exact disjoint_of_subset_left hB''₂.2 disjoint_compl_left,
end) 
(begin
  rintro X hX I' ⟨hI'E, B, hB, hI'B⟩ hI'X, 
  obtain ⟨I, hI⟩ :=  M.exists_basis (M.E \ X) ,
  obtain ⟨B', hB', hIB', hB'IB⟩ := hI.indep.exists_base_subset_union_base hB, 
  refine ⟨(X \ B') ∩ M.E, 
    ⟨_,subset_inter (subset_diff.mpr _) hI'E, (inter_subset_left _ _).trans (diff_subset _ _)⟩, _⟩, 
  { simp only [inter_subset_right, true_and], 
    exact ⟨B', hB', disjoint_of_subset_left (inter_subset_left _ _) disjoint_sdiff_left⟩ },
  { rw [and_iff_right hI'X],
    refine disjoint_of_subset_right hB'IB _, 
    rw [disjoint_union_right, and_iff_left hI'B], 
    exact disjoint_of_subset hI'X hI.subset disjoint_sdiff_right },
  simp only [mem_set_of_eq, subset_inter_iff, and_imp, forall_exists_index], 
  intros J hJE B'' hB'' hdj hI'J hJX hssJ,
  rw [and_iff_left hJE],  
  rw [diff_eq, inter_right_comm, ←diff_eq, diff_subset_iff] at hssJ, 
  
  have hI' : (B'' ∩ X) ∪ (B' \ X) ⊆ B',
  { rw [union_subset_iff, and_iff_left (diff_subset _ _),
     ←inter_eq_self_of_subset_left hB''.subset_ground, inter_right_comm, inter_assoc],
    calc _ ⊆ _ : inter_subset_inter_right _ hssJ 
       ... ⊆ _ : by rw [inter_distrib_left, hdj.symm.inter_eq, union_empty] 
       ... ⊆ _ : inter_subset_right _ _ },
  
  obtain ⟨B₁,hB₁,hI'B₁,hB₁I⟩ := (hB'.indep.subset hI').exists_base_subset_union_base hB'',
  rw [union_comm, ←union_assoc, union_eq_self_of_subset_right (inter_subset_left _ _)] at hB₁I, 
  
  have : B₁ = B', 
  { refine hB₁.eq_of_subset_indep hB'.indep (λ e he, _), 
    refine (hB₁I he).elim (λ heB'',_) (λ h, h.1), 
    refine (em (e ∈ X)).elim (λ heX, hI' (or.inl ⟨heB'', heX⟩)) (λ heX, hIB' _), 
    refine hI.mem_of_insert_indep ⟨hB₁.subset_ground he, heX⟩ 
      (hB₁.indep.subset (insert_subset.mpr ⟨he, _⟩)), 
    refine (subset_union_of_subset_right (subset_diff.mpr ⟨hIB',_⟩) _).trans hI'B₁, 
    refine disjoint_of_subset_left hI.subset disjoint_sdiff_left }, 

  subst this, 

  refine subset_diff.mpr ⟨hJX, by_contra (λ hne, _)⟩, 
  obtain ⟨e, heJ, heB'⟩ := not_disjoint_iff.mp hne,
  obtain (heB'' | ⟨heB₁,heX⟩ ) := hB₁I heB', 
  { exact hdj.ne_of_mem heJ heB'' rfl },
  exact heX (hJX heJ), 
end) 
(by tauto)

/-- A notation typeclass for matroid duality, denoted by the `﹡` symbol. -/
@[class] structure has_matroid_dual (β : Type*) := (dual : β → β)

postfix `﹡`:(max+1) := has_matroid_dual.dual 

instance matroid_in_dual {α : Type*} : has_matroid_dual (matroid_in α) := ⟨matroid_in.dual⟩ 

@[simp] lemma dual_ground : M﹡.E = M.E := rfl 

lemma dual_indep_iff_exists' : (M﹡.indep I) ↔ I ⊆ M.E ∧ (∃ B, M.base B ∧ disjoint I B) := 
sorry
--by simp [has_matroid_dual.dual, dual]
-- don't know why this is broken

end dual

structure rep (𝔽 W : Type*) [field 𝔽] [add_comm_group W] [module 𝔽 W] (M : matroid_in α) :=
(to_fun : α → W)
(valid' : ∀ (I ⊆ M.E), linear_independent 𝔽 (to_fun ∘ coe : I → W) ↔ M.indep I)
(support : ∀ (e : α), e ∉ M.E → to_fun e = 0)

instance fun_like {𝔽 W : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W] {M : matroid_in α } :
  fun_like (rep 𝔽 W M) α (λ _, W) :=
{ coe := λ φ e, φ.to_fun e,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

instance : has_coe_to_fun (rep 𝔽 W M) (λ _, α → W) := fun_like.has_coe_to_fun

section iso

structure iso {α₁ α₂ : Type*} (M₁ : matroid_in α₁) (M₂ : matroid_in α₂) extends equiv M₁.E M₂.E :=
  (on_base' : ∀ (B : set M₁.E), M₁.base (coe '' B) ↔ M₂.base (coe '' (to_fun '' B))) 

infix ` ≃i `:75 := matroid_in.iso 

instance iso.equiv_like {α β : Type*} {M₁ : matroid_in α} {M₂ : matroid_in β} : 
  equiv_like (M₁ ≃i M₂) M₁.E M₂.E := 
{ coe := λ e, e.to_equiv.to_fun,
  inv := λ e, e.to_equiv.inv_fun,
  left_inv := λ e, e.to_equiv.left_inv, 
  right_inv := λ e, e.to_equiv.right_inv,
  coe_injective' := λ e e' h h', by { cases e, cases e', simpa using h }   }

def iso.symm {β : Type*} {N : matroid_in β} (e : M ≃i N) : N ≃i M := 
{ to_equiv := e.symm, 
  on_base' := begin
    intro B, 
    rw [e.on_base'], 
    congr', 
    exact (e.to_equiv.image_symm_image B).symm, 
  end }

@[simp] lemma coe_symm {β : Type*} {N : matroid_in β} (e : M ≃i N) : (e.symm : N.E → M.E) = 
  e.to_equiv.symm := rfl 

def iso.image {β : Type*} {N : matroid_in β} (e : M ≃i N) (B : set α) : set β := coe '' 
  (e '' (coe ⁻¹' B))

def iso.preimage {β : Type*} {N : matroid_in β} (e : M ≃i N) (B : set β) : set α := 
  coe '' (e ⁻¹' (coe ⁻¹' B))

@[ssE_finish_rules] lemma iso.image_subset_ground {β : Type*} {N : matroid_in β} (e : M ≃i N) 
  (X : set α) : e.image X ⊆ N.E := subtype.coe_image_subset _ _

@[ssE_finish_rules] lemma iso.preimage_subset_ground {β : Type*} {N : matroid_in β} (e : M ≃i N) 
  (X : set β) : e.preimage X ⊆ M.E :=
subtype.coe_image_subset _ _

@[simp] lemma iso.image_ground {β : Type*} {N : matroid_in β} (e : M ≃i N) : e.image M.E = N.E := 
begin
  rw [←@subtype.range_coe _ M.E, ←@subtype.range_coe _ N.E, iso.image], 
  simp only [subtype.range_coe_subtype, set_of_mem_eq, subtype.coe_preimage_self, image_univ],  
  convert image_univ, 
  { exact e.to_equiv.range_eq_univ }, 
  simp, 
end 

lemma iso.preimage_eq_image_symm {β : Type*} {N : matroid_in β} (e : M ≃i N) {X : set β} : 
  e.preimage X = e.symm.image X := 
begin
  rw [iso.image, coe_symm, iso.preimage, image_eq_image subtype.coe_injective, 
    ←preimage_equiv_eq_image_symm], 
  refl, 
end 

@[simp] lemma iso.preimage_ground {β : Type*} {N : matroid_in β} (e : M ≃i N) : e.preimage N.E = M.E :=
by rw [iso.preimage_eq_image_symm, iso.image_ground]

@[simp] lemma iso.preimage_image {β : Type*} {N : matroid_in β} 
  (e : M ≃i N) {X : set α} (hX : X ⊆ M.E . ssE) : e.preimage (e.image X) = X :=
begin
  rw ←@subtype.range_coe _ M.E at hX, 
  obtain ⟨X, rfl⟩ := subset_range_iff_exists_image_eq.mp hX, 
  rw [iso.image, iso.preimage], 
  -- don't know what's wrong, for some reason here it says coe '' X ⊆ M.E but in equiv.lean it's
  -- just X ⊆ M.E
  --simp only [subtype.preimage_image_coe, subtype.image_coe_eq_image_coe_iff], 
  --exact e.to_equiv.preimage_image X, 
  sorry
end 

@[simp] lemma iso.image_preimage {β : Type*} {N : matroid_in β} (e : M ≃i N) {X : set β} (hX : X ⊆ N.E . ssE) :
  e.image (e.preimage X) = X := 
begin
  rw [auto_param_eq, ←@subtype.range_coe _ N.E] at hX, 
  obtain ⟨X, rfl⟩ := subset_range_iff_exists_image_eq.mp hX, 
  rw [iso.image, iso.preimage], 
  --simp_rw [subtype.preimage_image_coe, subtype.image_coe_eq_image_coe_iff], 
  --exact e.to_equiv.image_preimage X,
  sorry, 
end 
 

lemma iso.on_base {β : Type*} {N : matroid_in β} (e : M ≃i N) {B : set α} 
(hI : B ⊆ M.E) : M.base B ↔ N.base (e.image B) := 
begin
  rw ←@subtype.range_coe _ M.E at hI, 
  obtain ⟨B, rfl⟩ := subset_range_iff_exists_image_eq.mp hI,  
  rw [iso.image, e.on_base', equiv.to_fun_as_coe], 
  convert iff.rfl using 1, 
  --simp only [subtype.preimage_image_coe, eq_iff_iff], 
  --refl, 
  sorry,
end 

lemma iso.image_eq_image_inter_ground {β : Type*} {N : matroid_in β} (e : M ≃i N) (X : set α) : 
  e.image X = e.image (X ∩ M.E) :=
by rw [iso.image, iso.image, ←preimage_inter_range, subtype.range_coe]

lemma iso.image_inter {β : Type*} {N : matroid_in β} (e : M ≃i N) (X Y : set α) : e.image (X ∩ Y) = e.image X ∩ e.image Y :=
by rw [e.image_eq_image_inter_ground, inter_inter_distrib_right, iso.image, 
    preimage_inter, image_inter (equiv_like.injective e), image_inter subtype.coe_injective, 
    ← iso.image, ←iso.image, ←e.image_eq_image_inter_ground, ←e.image_eq_image_inter_ground ]

lemma iso.preimage_compl {β : Type*} {N : matroid_in β} (e : M ≃i N) (X : set β) : e.preimage Xᶜ = M.E \ e.preimage X :=
by rw [iso.preimage, preimage_compl, preimage_compl, compl_eq_univ_diff, 
    image_diff subtype.coe_injective, image_univ, subtype.range_coe, iso.preimage] 

lemma iso.image_eq_preimage_symm {β : Type*} {N : matroid_in β} (e : M ≃i N) {X : set α} : 
  e.image X = e.symm.preimage X :=
begin
  rw [iso.preimage, coe_symm, iso.image, image_eq_image subtype.coe_injective, 
    ←image_equiv_eq_preimage_symm], refl, 
end 
  
lemma iso.image_compl {β : Type*} {N : matroid_in β} (e : M ≃i N) (X : set α) : 
  e.image Xᶜ = N.E \ e.image X :=
by rw [iso.image_eq_preimage_symm, iso.preimage_compl, ←iso.image_eq_preimage_symm]

lemma iso.image_diff {β : Type*} {N : matroid_in β} (e : M ≃i N) (X Y : set α) : 
  e.image (X \ Y) = e.image X \ e.image Y :=
by rw [diff_eq, e.image_inter, e.image_compl, diff_eq, ←inter_assoc, diff_eq, 
  inter_eq_self_of_subset_left (e.image_subset_ground _) ]

@[simp] lemma iso.image_empty {β : Type*} {N : matroid_in β} (e : M ≃i N) : e.image ∅ = ∅ := 
by simp [iso.image]

lemma iso.image_subset_image {β : Type*} {N : matroid_in β} (e : M ≃i N) {X Y : set α} (hXY : X ⊆ Y) 
  : e.image X ⊆ e.image Y :=
by rw [←diff_eq_empty, ←e.image_diff, diff_eq_empty.mpr hXY, e.image_empty]

lemma iso.on_indep {β : Type*} {N : matroid_in β} (e : M ≃i N) {I : set α} (hI : I ⊆ M.E) : 
  M.indep I ↔ N.indep (e.image I) :=
begin
  rw [indep_iff_subset_base, indep_iff_subset_base], 
  split, 
  { rintro ⟨B, hB, hIB⟩,
    exact ⟨e.image B, (e.on_base hB.subset_ground).mp hB, e.image_subset_image hIB⟩ },
  rintro ⟨B, hB, hIB⟩, 
  refine ⟨e.preimage B, _, _⟩, 
  { rwa [iso.preimage_eq_image_symm, ←e.symm.on_base hB.subset_ground] },
  rw [←e.preimage_image hI, e.preimage_eq_image_symm, e.preimage_eq_image_symm],
  apply e.symm.image_subset_image hIB, 
end 

end iso

lemma rep.valid (φ : rep 𝔽 W M) {I : set α} : linear_independent 𝔽 (λ e : I, φ e) ↔ M.indep I :=
begin
  refine (em (I ⊆ M.E)).elim (φ.valid' _) (fun hIE, _),
  obtain ⟨e, heI, heE⟩ := not_subset.1 hIE,
  exact iff_of_false (fun hli, hli.ne_zero ⟨e, heI⟩ (φ.support _ heE))
    (fun hI, hIE hI.subset_ground),
end

def is_representable (𝔽 : Type*) [field 𝔽] (M : matroid_in α) : Prop :=
  ∃ (B : set α) (hB : M.base B), nonempty (rep 𝔽 (B →₀ 𝔽) M)

def iso.rep (M : matroid_in α) (M' : matroid_in γ) (ψ : M' ≃i M) (v : rep 𝔽 W M) : rep 𝔽 W M' :=
{ to_fun := function.extend coe (fun (x : M'.E), v (ψ x)) 0,
  valid' := λ I hI,
    begin
      set eI : I → ψ.image I := λ x, ⟨ψ ⟨x,hI x.2⟩, ⟨_,mem_image_of_mem _ (by simp), rfl⟩⟩ with heI,
      have hbij : bijective eI,
      { refine ⟨fun x y hxy, _, fun x, _⟩,
        { rwa [heI, subtype.mk_eq_mk, subtype.coe_inj, (equiv_like.injective ψ).eq_iff,
            subtype.mk_eq_mk, subtype.coe_inj] at hxy },
        obtain ⟨_, ⟨_, ⟨z,hz,rfl⟩, rfl⟩⟩ := x,
        exact ⟨⟨z,hz⟩, by simp⟩ },
      rw [ψ.on_indep hI, ← v.valid ],
      refine linear_independent_equiv' (equiv.of_bijective _ hbij) _,
      ext,
      simp only [comp_app, equiv.of_bijective_apply, subtype.coe_mk],
      exact ((@subtype.coe_injective _ M'.E).extend_apply (λ x, v (ψ x)) 0 (inclusion hI x)).symm,
    end,
  support :=
    begin
      rintro e he,
      rw [extend_apply', pi.zero_apply],
      rintro ⟨a,rfl⟩,
      exact he a.2,
    end }

lemma base_iff_maximal_indep : M.base B ↔ M.indep B ∧ ∀ I, M.indep I → B ⊆ I → B = I :=
begin
  refine ⟨λ h, ⟨h.indep, λ _, h.eq_of_subset_indep ⟩,λ h, _⟩,
  obtain ⟨⟨B', hB', hBB'⟩, h⟩ := h,
  rwa h _ hB'.indep hBB',
end

lemma set.subset_ground_dual {X : set α} (hX : X ⊆ M.E) : X ⊆ M﹡.E := hX 

lemma dual_base_iff (hB : B ⊆ M.E . ssE) : M﹡.base B ↔ M.base (M.E \ B) := 
begin
  rw [base_compl_iff_mem_maximals_disjoint_base', base_iff_maximal_indep, dual_indep_iff_exists', 
    mem_maximals_set_of_iff],
  simp [dual_indep_iff_exists'],
end 

@[simp] lemma dual_dual (M : matroid_in α) : M﹡﹡ = M := 
begin
  refine eq_of_base_iff_base_forall rfl (λ B hB, _), 
  rw [dual_base_iff, dual_base_iff], 
  rw [dual_ground] at *, 
  simp only [sdiff_sdiff_right_self, inf_eq_inter, ground_inter_right], 
end 

lemma base.compl_base_dual (hB : M.base B) : M﹡.base (M.E \ B) := 
by { haveI := fact.mk hB.subset_ground, simpa [dual_base_iff], }

lemma dual_indep_iff_coindep {X : set α}: M﹡.indep X ↔ M.coindep X := dual_indep_iff_exists'

lemma base.compl_inter_basis_of_inter_basis {X : set α} (hB : M.base B) (hBX : M.basis (B ∩ X) X) :
  M﹡.basis ((M.E \ B) ∩ (M.E \ X)) (M.E \ X) := 
begin
  rw basis_iff, 
  refine ⟨(hB.compl_base_dual.indep.subset (inter_subset_left _ _)), inter_subset_right _ _, 
    λ J hJ hBCJ hJX, hBCJ.antisymm (subset_inter _ hJX)⟩, 
  
  obtain ⟨-, B', hB', hJB'⟩ := dual_indep_iff_coindep.mp hJ, 

  obtain ⟨B'', hB'', hsB'', hB''s⟩  := hBX.indep.exists_base_subset_union_base hB', 
  have hB'ss : B' ⊆ B ∪ X, 
  { rw [←diff_subset_diff_iff M.E (by ssE : B ∪ X ⊆ M.E) hB'.subset_ground, subset_diff,
      and_iff_right (diff_subset _ _)],
    rw [diff_inter_diff] at hBCJ, 
    exact disjoint_of_subset_left hBCJ hJB' },
  
  have hB''ss : B'' ⊆ B, 
  { refine λ e he, (hB''s he).elim and.left (λ heB', (hB'ss heB').elim id (λ heX, _)), 
     exact (hBX.mem_of_insert_indep heX (hB''.indep.subset (insert_subset.mpr ⟨he,hsB''⟩))).1 }, 
  
  have := (hB''.eq_of_subset_indep hB.indep hB''ss).symm, subst this,
  rw subset_diff at *, 
  exact ⟨hJX.1, disjoint_of_subset_right hB''s (disjoint_union_right.mpr 
    ⟨disjoint_of_subset_right (inter_subset_right _ _) hJX.2, hJB'⟩)⟩, 
end 

lemma base.inter_basis_iff_compl_inter_basis_dual {X : set α} (hB : M.base B) (hX : X ⊆ M.E . ssE): 
  M.basis (B ∩ X) X ↔ M﹡.basis ((M.E \ B) ∩ (M.E \ X)) (M.E \ X) :=
begin
  refine ⟨hB.compl_inter_basis_of_inter_basis, λ h, _⟩, 
  simpa using hB.compl_base_dual.compl_inter_basis_of_inter_basis h, 
end 

lemma coindep_iff_exists {X : set α} (hX : X ⊆ M.E . ssE) : M.coindep X ↔ ∃ B, M.base B ∧ disjoint X B := 
by rw [coindep, and_iff_right hX]

def restrict' (M : matroid_in α) (X : set α) : matroid_in α :=
matroid_of_indep X (λ I, M.indep I ∧ I ⊆ X ∩ M.E) ⟨M.empty_indep, empty_subset _⟩ 
(λ I J hJ hIJ, ⟨hJ.1.subset hIJ, hIJ.trans hJ.2⟩)
(begin
  set Y := X ∩ M.E with hY_def, 
  have hY : Y ⊆ M.E := inter_subset_right _ _, 
  rintro I I' ⟨hI, hIY⟩ hIn hI',
  rw ←basis_iff_mem_maximals at hIn hI', 
  obtain ⟨B', hB', rfl⟩ := hI'.exists_base, 
  obtain ⟨B, hB, hIB, hBIB'⟩ := hI.exists_base_subset_union_base hB',
  
  rw [hB'.inter_basis_iff_compl_inter_basis_dual hY, diff_inter_diff] at hI', 
  
  have hss : M.E \ (B' ∪ Y) ⊆ M.E \ (B ∪ Y), 
  { rw [subset_diff, and_iff_right (diff_subset _ _), ←subset_compl_iff_disjoint_left, 
      diff_eq, compl_inter, compl_compl, ←union_assoc, union_subset_iff, 
      and_iff_left (subset_union_right _ _)],
    refine hBIB'.trans (union_subset (hIY.trans _) 
      (subset_union_of_subset_left (subset_union_right _ _) _)), 
    apply subset_union_right },

  have hi : M﹡.indep (M.E \ (B ∪ Y)), 
  { rw [dual_indep_iff_coindep, coindep_iff_exists], 
    exact ⟨B, hB, disjoint_of_subset_right (subset_union_left _ _) disjoint_sdiff_left⟩ }, 
  have h_eq := hI'.eq_of_subset_indep hi hss 
    (by {rw [diff_subset_iff, union_assoc, union_diff_self, ←union_assoc], simp }), 
  
  rw [h_eq, ←diff_inter_diff, ←hB.inter_basis_iff_compl_inter_basis_dual hY] at hI', 

  have hssu : I ⊂ (B ∩ Y) := (subset_inter hIB hIY).ssubset_of_ne 
    (by { rintro rfl, exact hIn hI' }), 

  obtain ⟨e, heBY, heI⟩ := exists_of_ssubset hssu, 
  exact ⟨e, ⟨⟨(hBIB' heBY.1).elim (λ h', (heI h').elim) id ,heBY.2⟩,heI⟩, 
    (hB.indep.inter_right Y).subset (insert_subset.mpr ⟨heBY,hssu.subset⟩), 
    insert_subset.mpr ⟨heBY.2,hssu.subset.trans (inter_subset_right _ _)⟩⟩, 
end)
(begin
  rintro X hX I ⟨hI, hIX⟩ hIA, 
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset (subset_inter hIA hIX), 
  refine ⟨J, ⟨⟨hJ.indep,hJ.subset.trans (inter_subset_right _ _)⟩,hIJ,
    hJ.subset.trans (inter_subset_left _ _)⟩, λ B hB hJB, _⟩, 
  rw hJ.eq_of_subset_indep hB.1.1 hJB (subset_inter hB.2.2 hB.1.2), 
end)
(fun I hI, hI.2.trans (inter_subset_left _ _))   

/-- Restrict the matroid `M` to `X : set α`.  -/
def restrict (M : matroid_in α) (X : set α) : matroid_in α :=
matroid_of_indep (X ∩ M.E) (λ I, M.indep I ∧ I ⊆ X ∩ M.E) ⟨M.empty_indep, empty_subset _⟩ 
(λ I J hJ hIJ, ⟨hJ.1.subset hIJ, hIJ.trans hJ.2⟩)
(begin
  set Y := X ∩ M.E with hY_def, 
  have hY : Y ⊆ M.E := inter_subset_right _ _, 
  rintro I I' ⟨hI, hIY⟩ hIn hI',
  rw ←basis_iff_mem_maximals at hIn hI', 
  obtain ⟨B', hB', rfl⟩ := hI'.exists_base, 
  obtain ⟨B, hB, hIB, hBIB'⟩ := hI.exists_base_subset_union_base hB',
  
  rw [hB'.inter_basis_iff_compl_inter_basis_dual hY, diff_inter_diff] at hI', 
  
  have hss : M.E \ (B' ∪ Y) ⊆ M.E \ (B ∪ Y), 
  { rw [subset_diff, and_iff_right (diff_subset _ _), ←subset_compl_iff_disjoint_left, 
      diff_eq, compl_inter, compl_compl, ←union_assoc, union_subset_iff, 
      and_iff_left (subset_union_right _ _)],
    refine hBIB'.trans (union_subset (hIY.trans _) 
      (subset_union_of_subset_left (subset_union_right _ _) _)), 
    apply subset_union_right },

  have hi : M﹡.indep (M.E \ (B ∪ Y)), 
  { rw [dual_indep_iff_coindep, coindep_iff_exists], 
    exact ⟨B, hB, disjoint_of_subset_right (subset_union_left _ _) disjoint_sdiff_left⟩ }, 
  have h_eq := hI'.eq_of_subset_indep hi hss 
    (by {rw [diff_subset_iff, union_assoc, union_diff_self, ←union_assoc], simp }), 
  
  rw [h_eq, ←diff_inter_diff, ←hB.inter_basis_iff_compl_inter_basis_dual hY] at hI', 

  have hssu : I ⊂ (B ∩ Y) := (subset_inter hIB hIY).ssubset_of_ne 
    (by { rintro rfl, exact hIn hI' }), 

  obtain ⟨e, heBY, heI⟩ := exists_of_ssubset hssu, 
  exact ⟨e, ⟨⟨(hBIB' heBY.1).elim (λ h', (heI h').elim) id ,heBY.2⟩,heI⟩, 
    (hB.indep.inter_right Y).subset (insert_subset.mpr ⟨heBY,hssu.subset⟩), 
    insert_subset.mpr ⟨heBY.2,hssu.subset.trans (inter_subset_right _ _)⟩⟩, 
end)
(begin
  rintro X hX I ⟨hI, hIX⟩ hIA, 
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset (subset_inter hIA hIX), 
  refine ⟨J, ⟨⟨hJ.indep,hJ.subset.trans (inter_subset_right _ _)⟩,hIJ,
    hJ.subset.trans (inter_subset_left _ _)⟩, λ B hB hJB, _⟩, 
  rw hJ.eq_of_subset_indep hB.1.1 hJB (subset_inter hB.2.2 hB.1.2), 
end)
( by tauto )   

@[class] structure has_restrict (α β : Type*) := (restrict : α → β → α)

infix ` ‖ ` :75 :=  has_restrict.restrict 

instance : has_restrict (matroid_in α) (set α) := ⟨λ M E, M.restrict E⟩  

class has_delete (α β : Type*) := (del : α → β → α)

infix ` ⟍ ` :75 :=  has_delete.del 

def delete (M : matroid_in α) (D : set α) : matroid_in α := M ‖ Dᶜ 

instance del_elem {α : Type*} : has_delete (matroid_in α) α := ⟨λ M e, M.delete {e}⟩  

/-- A flat is a maximal set having a given basis  -/
def flat (M : matroid_in α) (F : set α) : Prop := 
(∀ ⦃I X⦄, M.basis I F → M.basis I X → X ⊆ F) ∧ F ⊆ M.E  

/-- The closure of a subset of the ground set is the intersection of the flats containing it. 
  A set `X` that doesn't satisfy `X ⊆ M.E` has the junk value `M.cl X := M.cl (X ∩ M.E)`. -/
def cl (M : matroid_in α) (X : set α) : set α := ⋂₀ {F | M.flat F ∧ X ∩ M.E ⊆ F} 

/-- A loop is a member of the closure of the empty set -/
def loop (M : matroid_in α) (e : α) : Prop := e ∈ M.cl ∅

/-- A coloop is a loop of the dual  -/
def coloop (M : matroid_in α) (e : α) : Prop := M﹡.loop e   

lemma dual_inj {M₁ M₂ : matroid_in α} (h : M₁﹡ = M₂﹡) : M₁ = M₂ :=
by rw [←dual_dual M₁, h, dual_dual]

@[simp] lemma dual_inj_iff {M₁ M₂ : matroid_in α} : M₁﹡ = M₂﹡ ↔ M₁ = M₂ := ⟨dual_inj, congr_arg _⟩

lemma eq_dual_comm {M₁ M₂ : matroid_in α} : M₁ = M₂﹡ ↔ M₂ = M₁﹡ := 
by rw [←dual_inj_iff, dual_dual, eq_comm]

def add_loop (M : matroid_in α) (f : α) : matroid_in α := M.restrict' (insert f M.E)

lemma loop_iff_mem_cl_empty {e : α} : M.loop e ↔ e ∈ M.cl ∅ := iff.rfl 

@[simp] lemma add_loop_ground (M : matroid_in α) (f : α) : (M.add_loop f).E = insert f M.E := rfl

@[simp] lemma restrict'_indep_iff {M : matroid_in α} {X I : set α} : 
  (M.restrict' X).indep I ↔ M.indep I ∧ I ⊆ X := 
begin
  simp only [restrict', subset_inter_iff, matroid_of_indep_apply, and.congr_right_iff, 
    and_iff_left_iff_imp], 
  exact fun h _, h.subset_ground 
end 

@[simp] lemma add_loop_indep_iff {f : α} : (M.add_loop f).indep I ↔ M.indep I := 
begin
  rw [add_loop, restrict'_indep_iff, and_iff_left_iff_imp],
  exact fun hI, hI.subset_ground.trans (subset_insert _ _), 
end 

lemma indep.basis_self (hI : M.indep I) : M.basis I I := 
begin
  rw [basis_iff', and_iff_left hI.subset_ground, and_iff_right hI, and_iff_right subset.rfl], 
  exact λ _ _, subset_antisymm, 
end 

lemma indep.cl_eq_set_of_basis (hI : M.indep I) : M.cl I = {x | M.basis I (insert x I)} :=
begin
  set F := {x | M.basis I (insert x I)} with hF, 
  have hIF : M.basis I F,
  { rw basis_iff, 
    refine ⟨hI, (λ e he, by { rw [hF, mem_set_of, insert_eq_of_mem he], exact hI.basis_self }), 
      λ J hJ hIJ hJF, hIJ.antisymm (λ e he, _)⟩,
    rw basis.eq_of_subset_indep (hJF he) (hJ.subset (insert_subset.mpr ⟨he, hIJ⟩)) 
      (subset_insert _ _) subset.rfl, 
    exact mem_insert _ _ },
  
  have hF : M.flat F, 
  { refine λ J Y hJ hJY y hy, (indep.basis_of_forall_insert hI (subset_insert _ _) (λ e he heI, _)), 
    refine (hIF.transfer hJ (subset_union_right _ _) (hJY.basis_union hJ)).insert_dep
      (mem_of_mem_of_subset he _) heI, 
    rw [diff_subset_iff, union_diff_self, insert_subset], 
    exact ⟨or.inr (or.inl hy), subset_union_left _ _⟩ },
  
  rw [subset_antisymm_iff, cl, subset_sInter_iff], 
  refine ⟨sInter_subset_of_mem ⟨hF, hIF.subset⟩, _⟩, 

  rintro F' ⟨hF',hIF'⟩ e (he : M.basis I (insert e I)), 
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset hIF', 
  exact (hF' hJ (he.basis_union_of_subset hJ.indep hIJ)) (or.inr (mem_insert _ _)), 
end

lemma indep.mem_cl_iff' (hI : M.indep I) : 
  x ∈ M.cl I ↔ (x ∈ M.E ∧ (M.indep (insert x I) → x ∈ I)) :=
begin
  simp_rw [hI.cl_eq_set_of_basis, mem_set_of_eq],
  refine ⟨λ h, ⟨h.subset_ground (mem_insert _ _), λ h', h.mem_of_insert_indep (mem_insert _ _) h'⟩, 
    λ h, _⟩, 
  refine hI.basis_of_forall_insert (subset_insert x I) (λ e he hei, he.2  _) 
    (insert_subset.mpr ⟨h.1, hI.subset_ground⟩), 
  rw [←singleton_union, union_diff_right, mem_diff, mem_singleton_iff] at he,
  rw [he.1] at ⊢ hei, 
  exact h.2 hei,
end

lemma indep.mem_cl_iff_of_not_mem {e : α} (hI : M.indep I) (heI : e ∉ I) : 
  e ∈ M.cl I ↔ M.dep (insert e I) :=
by { rw [hI.mem_cl_iff', dep_iff, insert_subset, and_iff_left hI.subset_ground], tauto }

lemma loop_iff_dep {e : α} : M.loop e ↔ M.dep {e} := 
by rw [loop_iff_mem_cl_empty, 
  M.empty_indep.mem_cl_iff_of_not_mem (not_mem_empty e), insert_emptyc_eq]

lemma eq_add_loop_iff {f : α} (M M' : matroid_in α) (hf : f ∉ M.E) : 
    M' = add_loop M f ↔ M'.loop f ∧ M' ⟍ f = M :=
begin
  rw [loop_iff_dep, dep_iff, singleton_subset_iff], 
  split, 
  { rintro rfl, 
    rw [add_loop_indep_iff, add_loop_ground, and_iff_left (mem_insert _ _), indep_singleton, 
      and_iff_right (show ¬M.nonloop f, from fun h, hf h.mem_ground), 
      eq_iff_indep_iff_indep_forall, delete_elem, delete_ground, add_loop_ground], 
    simp only [insert_diff_of_mem, mem_singleton, sdiff_eq_left, disjoint_singleton_right,  
      delete_indep_iff, add_loop_indep_iff, and_iff_left_iff_imp, and_iff_right hf],
    rintro I hI - hfI,
    exact (hI hfI).2 rfl },
  rintro ⟨hfl,rfl⟩,  
  apply eq_of_indep_iff_indep_forall _ (fun I hI, _), 
  { simp only [delete_elem, add_loop_ground, delete_ground, insert_diff_singleton],
    rw [insert_eq_of_mem hfl.2] },
  simp only [delete_elem, add_loop_indep_iff, delete_indep_iff, disjoint_singleton_right, 
    iff_self_and], 
  exact fun hI' hfI, hfl.1 (hI'.subset (singleton_subset_iff.2 hfI)), 
end 

def add_coloop (M : matroid_in α) (f : α) : matroid_in α := (M﹡.add_loop f)﹡  

@[simp] lemma add_coloop_ground (M : matroid_in α) (f : α) : (M.add_coloop f).E = insert f M.E := rfl

lemma add_coloop_eq {f : α} (M M' : matroid_in α) (hf : f ∉ M.E) : 
    M' = add_coloop M f ↔ M'.coloop f ∧ M' ⟍ f = M := 
begin
  rw [add_coloop, eq_dual_comm, eq_comm, eq_add_loop_iff _ _ (show f ∉ M﹡.E, from hf), 
    dual_loop_iff_coloop, eq_dual_comm, delete_elem, dual_delete_dual_eq_contract, 
    delete_elem, and.congr_right_iff, eq_comm], 
  intro hf', 
  rw [contract_eq_delete_of_subset_coloops], 
  rwa [singleton_subset_iff, ← coloop_iff_mem_cl_empty ], 
end 

lemma add_coloop_del_eq (M : matroid_in α) (hf : f ∉ M.E) : add_coloop M f ⟍ f = M := 
  (((M.add_coloop_eq _) hf).1 rfl).2

lemma series_pair_mem_circuit (x y : α) (C : set α) (hMC : M.circuit C)
  (hMxy : M.cocircuit {x, y}) : x ∈ C ↔ y ∈ C :=
begin
  suffices h : ∀ (M' : matroid_in α) {x' y' C'},
    M'.cocircuit C' → M'.circuit {x',y'} → x' ∈ C' → y' ∈ C',
  { rw [← dual_circuit_iff_cocircuit] at hMxy,
    rw [ ←dual_dual M, dual_circuit_iff_cocircuit] at hMC,
    exact ⟨h M﹡ hMC hMxy, h M﹡ hMC (by rwa [pair_comm])⟩ },
  clear hMC C hMxy x y M,
  refine fun M e f C hC hef heC, by_contra (fun hfC, _),
  obtain (rfl | hne) := eq_or_ne e f, exact hfC heC,
  rw [← compl_hyperplane_iff_cocircuit] at hC,
  have hss : {e,f} \ {e} ⊆ M.E \ C,
  { simp only [insert_diff_of_mem, mem_singleton, diff_singleton_subset_iff, singleton_subset_iff,
      mem_insert_iff, mem_diff],
    exact or.inr ⟨hef.subset_ground (or.inr rfl), hfC⟩ },

  have hcon := (hef.subset_cl_diff_singleton e).trans (M.cl_subset hss) (or.inl rfl),
  rw [hC.flat.cl] at hcon,
  exact hcon.2 heC,
end

lemma unif_simple (a b : ℕ) (ha : 2 ≤ a) : (unif a b).simple :=
begin
  rintro e - f -,
  simp only [unif_indep_iff', nat.cast_bit0, enat.coe_one],
  have hfin : ({e,f} : set (fin b)).finite := ((finite_singleton _).insert _),
  rw [encard_le_coe_iff, and_iff_right hfin],
  refine le_trans _ ha,
  obtain (rfl | hne) := eq_or_ne e f, simp,
  rw [ncard_pair hne],
end

lemma U24_simple : (unif 2 4).simple :=
  unif_simple 2 4 rfl.le

lemma unif_iso_minor {n m k : ℕ} (hjk : m ≤ n) : unif k m ≤i unif k n :=
begin
  set D : set (fin n) := (range (fin.cast_le hjk))ᶜ with hD,

  have hecard : (range (fin.cast_le hjk)).encard = m,
  { rw [←image_univ,  encard_image_of_injective],
    { rw [encard_eq_coe_iff, ncard_univ, nat.card_eq_fintype_card,
        and_iff_left (fintype.card_fin _)],
      exact univ.to_finite },
    exact rel_embedding.injective (fin.cast_le hjk) },

  refine ⟨(unif k n) ⟍  D, delete_minor _ _, ⟨iso.symm (nonempty.some _)⟩⟩,
  rw [iso_unif_iff, delete_ground, unif_ground_eq, ← compl_eq_univ_diff, hD, compl_compl,
    and_iff_left hecard, eq_iff_indep_iff_indep_forall],
  simp [restrict_ground_eq', encard_le_coe_iff, and_assoc],
end


namespace rep

-- to do : matroid_of_module_fun.base ↔ module.basis
def matroid_of_module_fun (𝔽 W : Type*) {ι : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W]
  [finite_dimensional 𝔽 W] (v : ι → W) (ground : set ι) :
  matroid_in ι := matroid_of_indep_of_bdd' ground
  (λ (I : set ι), (linear_independent 𝔽 (λ x : I, v x)) ∧ I ⊆ ground)
  begin
    rw [linear_independent_image (inj_on_empty _), image_empty],
    refine ⟨linear_independent_empty 𝔽 W, empty_subset ground⟩,
  end
  begin
    intros I J hJ hIJ,
    have hIJ3 := linear_independent.injective hJ.1,
    rw [← set.restrict, ← inj_on_iff_injective] at hIJ3,
    rw linear_independent_image hIJ3 at hJ,
    rw linear_independent_image (inj_on.mono hIJ hIJ3),
    refine ⟨linear_independent.mono (image_subset v hIJ) hJ.1, subset_trans hIJ hJ.2⟩,
  end
  begin
    intros I J hI hJ hIJ,
    have h3 : ∃ x ∈ J, v x ∉ span 𝔽 (v '' I),
    { have hJ2 := linear_independent.injective hJ.1,
      rw [← set.restrict, ← inj_on_iff_injective] at hJ2,
      rw linear_independent_image hJ2 at hJ,
      have hI2 := linear_independent.injective hI.1,
      rw [← set.restrict, ← inj_on_iff_injective] at hI2,
      rw linear_independent_image hI2 at hI,
      haveI := finite.fintype (_root_.linear_independent.finite hI.1),
      haveI := finite.fintype (_root_.linear_independent.finite hJ.1),
      by_contra,
      push_neg at h,
      have h8 : ((v '' J).to_finite.to_finset) = (v '' J).to_finset,
        ext,
        simp only [finite.mem_to_finset, mem_to_finset],
      have h9 : ((v '' I).to_finite.to_finset) = (v '' I).to_finset,
        ext,
        simp only [finite.mem_to_finset, mem_to_finset],
      have h5 : (v '' I).ncard < (v '' J).ncard,
      { rwa [ncard_image_of_inj_on hJ2, ncard_image_of_inj_on hI2] },
      apply not_le_of_lt h5,
      rw [ncard_eq_to_finset_card, ncard_eq_to_finset_card, h8, h9,
      ← finrank_span_set_eq_card (v '' I) hI.1, ← finrank_span_set_eq_card (v '' J) hJ.1],
      have h2 := (@span_le 𝔽 W _ _ _ (v '' J) (span 𝔽 (v '' I))).2 (λ j hj, _),
      swap,
      { obtain ⟨x, ⟨hx, rfl⟩⟩ := hj,
        apply h x hx },
      apply submodule.finrank_le_finrank_of_le h2 },
    obtain ⟨x, ⟨hx1, hx2⟩⟩ := h3,
    refine ⟨x, ⟨hx1, ⟨(mem_image_of_mem v).mt (not_mem_subset (subset_span) hx2), _⟩⟩⟩,
    refine ⟨(linear_independent_insert' ((mem_image_of_mem v).mt
      (not_mem_subset (subset_span) hx2))).2 ⟨hI.1, hx2⟩, insert_subset.2
        ⟨(mem_of_subset_of_mem hJ.2 hx1), hI.2⟩⟩,
  end
  begin
    refine ⟨finite_dimensional.finrank 𝔽 W, λ I hI, _⟩,
    have hI2 := linear_independent.injective hI.1,
      rw [← set.restrict, ← inj_on_iff_injective] at hI2,
      rw linear_independent_image hI2 at hI,
    haveI := finite.fintype (_root_.linear_independent.finite hI.1),
    rw ← linear_independent_image hI2 at hI,
    haveI := ((v '' I).to_finite.of_finite_image hI2).fintype,

    rw [ncard, nat.card_eq_fintype_card],
    refine ⟨to_finite I, fintype_card_le_finrank_of_linear_independent hI.1⟩,

  end
  (by { tauto })

lemma matroid_of_module_fun.ground (𝔽 W : Type*) {ι : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W]
  [finite_dimensional 𝔽 W] (v : ι → W) (ground : set ι) :
    (matroid_of_module_fun 𝔽 W v ground).E = ground :=
begin
  rw [matroid_of_module_fun, matroid_of_indep_of_bdd', matroid_of_indep_of_bdd,
    matroid_of_indep, matroid_of_base, ← ground_eq_E],
end

def rep_of_matroid_of_module_fun (𝔽 W : Type*) {ι : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W]
  [finite_dimensional 𝔽 W] (v : ι → W) (ground : set ι) : rep 𝔽 W (matroid_of_module_fun 𝔽 W v ground) :=
{ to_fun := λ x, if x ∈ ground then v x else 0,
  valid' := λ I hI, by {simp only [matroid_of_module_fun, matroid_of_indep_of_bdd'_apply],
    rw matroid_of_module_fun.ground at hI,
    have h2 : (λ (x : ι), if (x ∈ ground) then (v x) else 0) ∘ (coe : I → ι) = λ x : I, v x,
      ext;
      simp only [ite_eq_left_iff],
      contrapose,
      intros h,
      push_neg,
      apply mem_of_subset_of_mem hI x.2,
    rw h2,
    simp,
    intros h,
    apply hI },
  support := λ e he,
    begin
      simp only [ite_eq_iff],
      right,
      refine ⟨he, rfl⟩,
    end }

lemma delete_matroid_of_module_fun (𝔽 W : Type*) {ι : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W]
  [finite_dimensional 𝔽 W] (v : ι → W) (ground : set ι) (D : set ι) :
    matroid_of_module_fun 𝔽 W v (ground \ D) = (matroid_of_module_fun 𝔽 W v ground) ⟍ D :=
begin
  apply eq_of_indep_iff_indep_forall,
  simp only [delete_ground, matroid_of_module_fun.ground],
  intros I hI,
  simp only [delete_indep_iff, matroid_of_module_fun, matroid_of_indep_of_bdd', subset_diff,
    matroid_of_indep_of_bdd_apply, and_assoc],
end

lemma matroid_of_module_fun_congr (𝔽 W : Type*) {ι : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W]
  [finite_dimensional 𝔽 W] (v w : ι → W) (ground : set ι) (hvw : ∀ (e : ι), e ∈ ground → v e = w e) :
  matroid_of_module_fun 𝔽 W v ground = matroid_of_module_fun 𝔽 W w ground :=
begin
  apply eq_of_indep_iff_indep_forall,
  simp only [matroid_of_module_fun.ground],
  intros I hI,
  simp only [matroid_of_module_fun, matroid_of_indep_of_bdd', matroid_of_indep_of_bdd_apply,
    λ e : I, hvw e (mem_of_mem_of_subset e.2 hI)],
end


lemma matroid_of_module_fun_rep_eq (M : matroid_in α) (𝔽 W : Type*) [field 𝔽] [add_comm_group W]
  [module 𝔽 W] [finite_dimensional 𝔽 W] (φ : rep 𝔽 W M) :
  M = matroid_of_module_fun 𝔽 W φ M.E :=
begin
  apply eq_of_indep_iff_indep_forall _ (λ I hI, _),
  refl,
  have hsigh : (λ (x : ↥I), φ x) = (φ.to_fun ∘ coe),
  { ext,
    simp only [comp_app],
    refl },
  rw [matroid_of_module_fun, matroid_of_indep_of_bdd'_apply, hsigh, φ.valid'],
  refine ⟨λ h, ⟨h, hI⟩, λ h, h.1⟩,
  apply hI,
end

lemma inj_on_of_indep (φ : rep 𝔽 W M) (hI : M.indep I) : inj_on φ I :=
inj_on_iff_injective.2 ((φ.valid' I hI.subset_ground).2 hI).injective

@[simp] lemma to_fun_eq_coe (φ : rep 𝔽 W M) : φ.to_fun = (φ : α → W)  := by { ext, refl }

lemma support' {φ : rep 𝔽 W M} {e : α} (he : e ∉ M.E) : φ e = 0 :=
by { rw ← to_fun_eq_coe, apply φ.support _ he }

lemma linear_independent_iff_coe (φ : rep 𝔽 W M) (hI : M.indep I) :
  linear_independent 𝔽 (λ e : I, φ e) ↔ linear_independent 𝔽 (coe : φ '' I → W) :=
linear_independent_image $ inj_on_of_indep _ hI

def to_submodule (φ : rep 𝔽 W M) : submodule 𝔽 W := span 𝔽 (range φ)

def to_submodule' (φ : rep 𝔽 W M) : submodule 𝔽 W := span 𝔽 (φ '' M.E)

lemma mem_to_submodule (φ : rep 𝔽 W M) (x : α) : φ x ∈ φ.to_submodule :=
by { rw [rep.to_submodule], refine subset_span _, rw mem_range, use x }

lemma mem_to_submodule' (φ : rep 𝔽 W M) (x : α) (hx : x ∈ M.E) : φ x ∈ φ.to_submodule' :=
by { rw [rep.to_submodule'], refine subset_span _, rw mem_image, use ⟨x, ⟨hx, rfl⟩⟩ }

def rep_submodule (φ : rep 𝔽 W M) : rep 𝔽 (φ.to_submodule') M :=
{ to_fun := λ a, if h : a ∈ M.E then ⟨φ a, φ.mem_to_submodule' a h⟩ else 0,
  valid' := λ I hI,
    begin
       have h2 : ((λ (a : α), dite (a ∈ M.E) (λ (h : a ∈ M.E),
        (⟨φ a, φ.mem_to_submodule' a h⟩ : φ.to_submodule')) (λ (h : a ∉ M.E), 0)) ∘
           coe : I → φ.to_submodule') = λ a : I, (⟨φ a, φ.mem_to_submodule' a (mem_of_subset_of_mem
           hI (by { simp only [subtype.val_eq_coe, subtype.coe_prop]}))⟩ : φ.to_submodule'),
        ext;
        simp only [comp_app],
        have h3 : ↑x ∈ I,
          simp only [subtype.val_eq_coe, subtype.coe_prop],
        rw (@dite_eq_iff _ (↑x ∈ M.E) _ (⟨φ x, φ.mem_to_submodule' x (mem_of_subset_of_mem hI h3)⟩ :
          φ.to_submodule') _ _).2 _,
        left,
        use (mem_of_subset_of_mem hI h3),
      rw h2,
      have h8 : (λ (x : ↥I), φ x) =
        (λ (x : ↥I), ↑(⟨φ x, φ.mem_to_submodule' x
        (mem_of_subset_of_mem hI (by { simp only [subtype.val_eq_coe, subtype.coe_prop]}))⟩ :
          φ.to_submodule')),
      { simp only [subtype.coe_mk] },
      have h4 : linear_independent 𝔽 (λ (x : ↥I), (⟨φ x, φ.mem_to_submodule' x
        (mem_of_subset_of_mem hI (by { simp only [subtype.val_eq_coe, subtype.coe_prop]}))⟩ :
          φ.to_submodule')) = linear_independent 𝔽 (λ (a : I), φ a),
        simp_rw [h8, ← submodule.coe_subtype],
        rw linear_map.linear_independent_iff
          (φ.to_submodule'.subtype) (ker_subtype φ.to_submodule'),
      rw h4,
      apply φ.valid' I hI,
    end,
    support := λ e he,
    begin
      simp only [dite_eq_iff],
      right,
      use he,
    end }

def rep.compose (φ : rep 𝔽 W M) (e : W ≃ₗ[𝔽] W') : rep 𝔽 W' M :=
{ to_fun := e ∘ φ.to_fun,
  valid' := λ I,
    begin
      rw comp.assoc,
      have h2 := linear_map.linear_independent_iff e.to_linear_map e.ker,
      simp only [linear_equiv.coe_to_linear_map] at h2,
      rw h2,
      apply φ.valid',
    end,
  support := λ x hx, by { rw [comp_app, φ.support x hx, _root_.map_zero] } }

def rep.compose' (φ : rep 𝔽 W M) (e : φ.to_submodule' ≃ₗ[𝔽] W') : rep 𝔽 W' M :=
  (rep.compose (φ.rep_submodule) e)

lemma ne_zero_of_nonloop (φ : rep 𝔽 W M) (hx : M.nonloop x) : φ x ≠ 0 :=
((φ.valid' {x} (indep_singleton.2 hx).subset_ground).2 hx.indep).ne_zero
(⟨x, mem_singleton _⟩ : ({x} : set α))

lemma ne_zero_of_loopless (φ : rep 𝔽 W M) (hl : loopless M) (x : α) (hx : x ∈ M.E) : φ x ≠ 0 :=
 φ.ne_zero_of_nonloop (hl x hx)

lemma inj_on_ground_of_simple (φ : rep 𝔽 W M) (hs : simple M) : inj_on φ M.E :=
λ a ha b hb,
begin
  apply φ.inj_on_of_indep (hs a ha b hb),
  simp only [mem_insert_iff, eq_self_iff_true, true_or],
  simp only [mem_insert_iff, eq_self_iff_true, mem_singleton, or_true],
end

lemma span_disj_of_simple (φ : rep 𝔽 W M) (hs : simple M) {x y : α} (hx : x ∈ M.E) (hy : y ∈ M.E)
(hxy : x ≠ y) : disjoint (𝔽 ∙ (φ x)) (𝔽 ∙ (φ y)) :=
begin
  have h5 : x ∈ ({x, y} : set α),
    rw [insert_eq, union_comm, ← insert_eq],
    simp only [mem_insert_iff, mem_singleton, or_true],
  have h6 : y ∈ ({x, y} : set α),
    simp only [mem_insert_iff, mem_singleton, or_true],
  have h7 : (⟨x, h5⟩ : ({x, y} : set α)) ≠ ⟨y, h6⟩,
    simp only [ne.def],
    apply hxy,
  have h3 := (φ.valid.2 (hs x hx y hy)).disjoint_span_image (disjoint_singleton.2 h7),
  simp only [image_singleton, subtype.coe_mk] at h3,
  apply h3,
end

lemma span_inj_of_simple (φ : rep 𝔽 W M) (hs : simple M) : inj_on (λ x : α, 𝔽 ∙ (φ x)) M.E :=
begin
  rw inj_on,
  intros x hx y hy hxy,
  by_contra,
  have h2 := span_disj_of_simple φ hs hx hy h,
  rw [hxy, disjoint_self, span_singleton_eq_bot] at h2,
  apply (φ.ne_zero_of_loopless hs.loopless y hy) h2,
end

lemma subset_nonzero_of_simple (φ : rep 𝔽 W M) (hs : simple M) :
  φ '' M.E ⊆ span 𝔽 (φ '' M.E) \ {0} :=
begin
  refine subset_diff.2 ⟨subset_span, disjoint_left.2 _⟩,
  rintro x ⟨y, ⟨hy1, rfl⟩⟩,
  apply ne_zero_of_loopless _ hs.loopless _ hy1,
end

lemma of_basis (φ : rep 𝔽 W M) {X I : set α} (hI : M.basis I X) {e : α} (he : e ∈ X):
  φ e ∈ span 𝔽 (φ '' I) :=
begin
  by_cases e ∈ I,
  { apply subset_span (mem_image_of_mem _ h) },
  have h2 : ¬ linear_independent 𝔽 (λ x : insert e I, φ x) := (φ.valid' (insert e I)
  (insert_subset.2 ⟨(mem_of_mem_of_subset he hI.subset_ground), hI.subset_ground_left⟩)).not.2
  (dep_iff.1 (hI.insert_dep (mem_diff_of_mem he h))).1,
  contrapose! h2,
  apply (linear_independent_insert' h).2 ⟨(φ.valid' I hI.subset_ground_left).2 hI.indep, h2⟩,
end

lemma of_base (φ : rep 𝔽 W M) {B : set α} (hB : M.base B) (e : α) (he : e ∈ M.E) :
  φ e ∈ span 𝔽 (φ '' B) :=
of_basis φ (base.basis_ground hB) he

lemma span_basis (φ : rep 𝔽 W M) {X I : set α} (hI : M.basis I X) :
  span 𝔽 (φ '' I) = span 𝔽 (φ '' X) :=
begin
  refine (span_mono $ image_subset _ (basis.subset hI)).antisymm (span_le.2 _),
  rintros _ ⟨y, ⟨hy1, rfl⟩⟩,
  apply of_basis φ hI hy1,
end

lemma span_base (φ : rep 𝔽 W M) (hB : M.base B) : span 𝔽 (φ '' B) = span 𝔽 (φ '' M.E) :=
  by { rw [span_basis φ (base.basis_ground hB)] }

/-lemma matroid_of_module_fun.base (𝔽 W : Type*) {ι : Type*} [field 𝔽] [add_comm_group W] [module 𝔽 W]
  [finite_dimensional 𝔽 W] (v : ι → W) (ground : set ι) {B : set ι}
  (hMB : (matroid_of_module_fun 𝔽 W v ground).base B) :
    linear_independent 𝔽 (λ x : B, v x) ∧ span 𝔽 (v '' B) = span 𝔽 (v '' ground) :=
begin
  have hMBi := hMB.indep,
  rw [matroid_of_module_fun, matroid_of_indep_of_bdd', matroid_of_indep_of_bdd,
    matroid_of_indep_apply] at hMBi,
  refine ⟨hMBi.1, _⟩,
  have φ := rep_of_matroid_of_module_fun 𝔽 W v ground,
  have hφ := φ.span_base hMB,
  sorry,
end-/

lemma basis_of_base (φ : rep 𝔽 W M) {B : set α} (hB : M.base B) :
  _root_.basis B 𝔽 (span 𝔽 (φ '' M.E)) := by {
rw [←span_base _ hB, image_eq_range], exact basis.span ((φ.valid' B hB.subset_ground).2 hB.indep) }

instance fin_dim_rep (φ : rep 𝔽 W M) [M.finite_rk] [fintype 𝔽] :
  finite_dimensional 𝔽 (span 𝔽 (φ '' M.E)) :=
begin
  cases M.exists_base with B hB,
  apply finite_dimensional.of_finite_basis (basis_of_base φ hB) (base.finite hB),
end

instance fin_dim_rep' (φ : rep 𝔽 W M) [M.finite_rk] [fintype 𝔽] :
  finite_dimensional 𝔽 φ.to_submodule' :=
begin
  cases M.exists_base with B hB,
  apply finite_dimensional.of_finite_basis (basis_of_base φ hB) (base.finite hB),
end

@[simp] lemma mem_span_rep_range (φ : rep 𝔽 W M) : ∀ (x : α), φ x ∈ (span 𝔽 (range ⇑φ)) :=
  λ x, by { apply mem_of_subset_of_mem (@subset_span 𝔽 _ _ _ _ (range ⇑φ)) (mem_range_self x) }

@[simp] lemma mem_span_rep (φ : rep 𝔽 W M) : ∀ (x : α) , φ x ∈ (span 𝔽 (φ '' M.E)) :=
  λ x, by { by_cases x ∈ M.E,
apply mem_of_subset_of_mem (@subset_span 𝔽 _ _ _ _ (φ '' M.E)) (mem_image_of_mem φ h),
simp only [support' h, submodule.zero_mem] }

@[simp]
lemma span_range_eq_span_image (φ : rep 𝔽 W M) : span 𝔽 (φ '' M.E) = span 𝔽 (range ⇑φ) :=
span_eq_span (λ x ⟨y, ⟨hx1, hx2⟩⟩, by {rw ← hx2, apply mem_span_rep_range φ y})
  (λ x ⟨y, hx⟩, by {rw ← hx, apply mem_span_rep φ y })

lemma span_range_base (φ : rep 𝔽 W M) (hB: M.base B) :
  span 𝔽 (range (λ (e : ↥B), φ ↑e)) = span 𝔽 (range φ)  :=
begin
  rw [← span_range_eq_span_image, ← φ.span_base hB],
  have h2 : range (λ (e : ↥B), φ ↑e) = (⇑φ '' B),
    ext;
    refine ⟨λ ⟨y, hy⟩, by { simp only at hy, rw ← hy, apply mem_image_of_mem φ y.2}, λ hx, _⟩,
    obtain ⟨y, ⟨hy1, rfl⟩⟩ := hx,
    simp only [mem_range, set_coe.exists, subtype.coe_mk, exists_prop],
    refine ⟨y, ⟨hy1, rfl⟩⟩,
  rw h2,
end

lemma mem_span_cl (φ : rep 𝔽 W M) {x : α} {X : set α} (hX : X ⊆ M.E) (hx : x ∈ M.cl X) :
  φ x ∈ span 𝔽 (φ '' X) :=
begin
  by_cases x ∈ X,
  { apply mem_of_subset_of_mem (@subset_span 𝔽 _ _ _ _ (φ '' X)) (mem_image_of_mem φ h) },
  obtain ⟨I, hI⟩ := M.exists_basis X,
  rw [← span_basis φ hI, span_basis φ (indep.basis_cl (basis.indep hI)), basis.cl hI],
  apply mem_of_subset_of_mem (@subset_span 𝔽 _ _ _ _ (φ '' M.cl X)) (mem_image_of_mem φ hx),
end

lemma linear_independent.map'' {ι : Type*} {v : ι → W} (hv : linear_independent 𝔽 v) (f : W →ₗ[𝔽] W')
   (hfv : linear_independent 𝔽 (f ∘ v)) : disjoint (span 𝔽 (range v)) f.ker :=
begin
  rw [disjoint_iff_inf_le, ← set.image_univ, finsupp.span_image_eq_map_total,
    map_inf_eq_map_inf_comap,
    map_le_iff_le_comap, comap_bot, finsupp.supported_univ, top_inf_eq],
  unfold linear_independent at hv hfv,
  rw [hv, le_bot_iff],
  haveI : inhabited W := ⟨0⟩,
  rw [finsupp.total_comp, @finsupp.lmap_domain_total _ _ 𝔽 _ _ _ _ _ _ _ _ _ _ f,
    linear_map.ker_comp (finsupp.total ι W 𝔽 v) f] at hfv,
  rw ← hfv,
  exact λ _, rfl,
end

/-- If `f` is an injective linear map, then the family `f ∘ v` is linearly independent
if and only if the family `v` is linearly independent. -/
protected lemma linear_map.linear_independent_iff {ι : Type*} {v : ι → W} (f : W →ₗ[𝔽] W') :
  linear_independent 𝔽 (f ∘ v) ↔ linear_independent 𝔽 v ∧ disjoint (f.ker) (span 𝔽 (range v)) :=
⟨λ h, ⟨@linear_independent.of_comp _ _ _ W' _ _ _
  (@add_comm_group.to_add_comm_monoid W' _inst_4) _ _inst_5 f h,
  disjoint.comm.1 (linear_independent.map'' (@linear_independent.of_comp _ _ _ W' _ _ _
  (@add_comm_group.to_add_comm_monoid W' _inst_4) _ _inst_5 f h) _ h)⟩,
  λ h, linear_independent.map h.1 (disjoint.comm.1 h.2)⟩

lemma linear_independent.union' {s t : set W}
  (hs : linear_independent 𝔽 (λ x, x : s → W)) (ht : linear_independent 𝔽 (λ x, x : t → W))
  (hst : disjoint (span 𝔽 s) (span 𝔽 t)) (hst2 : linear_independent 𝔽 (λ x, x : (s ∪ t) → W))
    : disjoint s t :=
begin
  rw disjoint_def at hst,
  rw [set.disjoint_iff, subset_empty_iff, eq_empty_iff_forall_not_mem],
  intros x,
  by_contra,
  -- for some reason, it doesn't let me specialize directly here.
  have h20 := mem_of_subset_of_mem (subset_span) ((mem_inter_iff _ _ _).1 h).1,
  have h21 := mem_of_subset_of_mem (subset_span) ((mem_inter_iff _ _ _).1 h).2,
  specialize hst x h20 h21,
  apply @linear_independent.ne_zero _ 𝔽 W ((λ (x : (s ∪ t)), x)) _ _ _ _
    ⟨x, (mem_of_subset_of_mem (inter_subset_union s t) h)⟩ hst2,
  simp only [← hst, subtype.coe_mk],
end

lemma linear_independent.union'' {s t : set W}
  (hs : linear_independent 𝔽 (λ x, x : s → W)) (ht : linear_independent 𝔽 (λ x, x : t → W))
  (hst : disjoint s t) (hst2 : linear_independent 𝔽 (λ x, x : (s ∪ t) → W))
    :  disjoint (span 𝔽 s) (span 𝔽 t) :=
begin
  convert hst2.disjoint_span_image (show disjoint (coe ⁻¹' s) (coe ⁻¹' t), from _),
  { rw [eq_comm, image_preimage_eq_iff, subtype.range_coe], apply subset_union_left },
  { rw [eq_comm, image_preimage_eq_iff, subtype.range_coe], apply subset_union_right },
  rw [set.disjoint_iff, subset_empty_iff] at ⊢ hst,
  rw [← preimage_inter, hst, preimage_empty],
end

theorem finrank_span_set_eq_ncard {K V : Type*} [division_ring K] [add_comm_group V]
  [module K V] (s : set V) (hs : linear_independent K (coe : s → V)) :
finite_dimensional.finrank K (submodule.span K s) = s.ncard :=
begin
  by_cases s.finite,
  { haveI := (finite.fintype h),
    rw [finrank_span_set_eq_card s hs, to_finset_card,
      ncard_eq_to_finset_card, finite.card_to_finset] },
  { rw infinite.ncard h,
    apply finrank_of_infinite_dimensional,
    by_contra h3,
    apply h,
    have h8 : span K (range (coe : s → V)) = span K s,
    simp only [subtype.range_coe_subtype, set_of_mem_eq],
    apply _root_.basis.finite_index_of_rank_lt_aleph_0 (basis.span hs),
    rw [← is_noetherian.iff_rank_lt_aleph_0, is_noetherian.iff_fg, h8],
    apply h3 },
end


lemma of_r (φ : rep 𝔽 W M) (X : set α) (hX : X ⊆ M.E . ssE) :
  finite_dimensional.finrank 𝔽 (span 𝔽 (φ '' X)) = M.r X :=
begin
  obtain ⟨I, hI⟩ := M.exists_basis X,
  rw [←hI.card, ←φ.span_basis hI, finrank_span_set_eq_ncard,
    ncard_image_of_inj_on (inj_on_of_indep _ hI.indep) ],
  exact linear_independent.image ((φ.valid' I hI.subset_ground_left).mpr hI.indep),
end

lemma of_rank (φ : rep 𝔽 W M) : finite_dimensional.finrank 𝔽 (span 𝔽 (φ '' M.E)) = M.rk :=
by { convert of_r φ M.E; simp }

lemma cl_subset_span_range (φ : rep 𝔽 W M) (X : set α) (hX : X ⊆ M.E . ssE) :
  φ '' M.cl X ⊆ span 𝔽 (φ '' M.E) := by { rintros _ ⟨x, ⟨hx, rfl⟩⟩,
  apply mem_span_rep φ x }

/-lemma cl_subset_span_set (φ : rep 𝔽 W M) {X : set α} (hX : X ⊆ M.E) :
  φ '' M.cl X ⊆ span 𝔽 (φ '' X) :=
by { rintros _ ⟨x, ⟨hx, rfl⟩⟩, apply mem_span_cl φ hX hx, }-/

--lemma rep_of_minor (φ : rep 𝔽 W M) (N : matroid_in α) (hNM : N ≤ matroid_in.to_matroid_in M) :

-- make version of standard_rep that uses is_representable instead of explicit φ
-- to avoid using casesI a lot
/-- The representation for `M` whose rows are indexed by a base `B` -/
def standard_rep (φ' : rep 𝔽 W M) {B : set α} (hB : M.base B) :
  rep 𝔽 (B →₀ 𝔽) M :=
{ to_fun := λ e : α, ((valid φ').2 hB.indep).repr ⟨φ' e, by
    { have h4 := φ'.mem_span_rep_range, rw ← span_range_base φ' hB at h4, exact h4 e}⟩,
  valid' := by
  { intros I hI,
    rw [← @valid _ _ _ _ _ _ _ φ' I,
      linear_map.linear_independent_iff ((valid φ').2 hB.indep).repr,
      ←(submodule.subtype (span 𝔽 (range (λ (e : B), φ' ↑e)))).linear_independent_iff,
         submodule.coe_subtype, and_iff_left],
    { refl },
    { simp only [linear_independent.repr_ker, disjoint_bot_left] },
    simp only [ker_subtype] },
  support := by
  { intros e he, simp_rw [support' he], convert _root_.map_zero _} }

/-- A representation over *any* module certifies representability-/
lemma is_representable_of_rep {W : Type*} [add_comm_group W] [module 𝔽 W] (φ : rep 𝔽 W M) :
    is_representable 𝔽 M :=
  begin
    obtain ⟨B, hB⟩ := M.exists_base,
    exact ⟨B, hB, ⟨standard_rep φ hB⟩⟩,
  end

@[simp]
lemma id_matrix_of_base (φ : rep 𝔽 W M) {B : set α} (e : B) (hB : M.base B) :
  standard_rep φ hB e e = 1 :=
begin
  rw ← to_fun_eq_coe,
  simp [standard_rep],
  rw [((valid φ).2 hB.indep).repr_eq_single e ⟨φ e, by
    { have h4 := φ.mem_span_rep_range, rw ← span_range_base φ hB at h4, exact h4 e}⟩ rfl],
  simp only [finsupp.single_eq_same],
end

lemma id_matrix_of_base' (φ : rep 𝔽 W M) {B : set α} (e f : B) (hB : M.base B) (hne : e ≠ f) :
  standard_rep φ hB e f = 0 :=
begin
  rw ← to_fun_eq_coe,
  simp [standard_rep],
  rw [(φ.valid.2 hB.indep).repr_eq_single e ⟨φ e, by
    { have h4 := φ.mem_span_rep_range, rw ← span_range_base φ hB at h4, exact h4 e}⟩ rfl],
  apply finsupp.single_eq_of_ne hne,
end

lemma standard_rep_base_eq {M' : matroid_in α} (φ : rep 𝔽 W M) (φ' : rep 𝔽 W' M') {B : set α} (hB : M.base B)
(hB' : M'.base B) (e : B) : standard_rep φ hB e = standard_rep φ' hB' e :=
begin
  ext;
  by_cases e = a,
  simp_rw [h, id_matrix_of_base],
  simp_rw [id_matrix_of_base' φ e a hB h, id_matrix_of_base' φ' e a hB' h],
end

open_locale big_operators

lemma fund_circuit_inter_eq_diff_of_not_mem (e : α) (he : e ∈ M.cl I) (h2 : e ∉ I) :
  (M.fund_circuit e I ∩ I) = (M.fund_circuit e I \ {e}) :=
begin
  apply eq_of_subset_of_subset,
  rw [diff_eq, compl_eq_univ_diff],
  apply inter_subset_inter (subset.refl _) (subset_diff_singleton (subset_univ I) h2),
  apply subset_inter (diff_subset _ _),
  apply (@insert_subset_insert_iff _ _ ((M.fund_circuit e I) \ {e}) I
    (not_mem_diff_singleton e (M.fund_circuit e I))).1,
  rw [insert_diff_singleton, insert_eq_of_mem (mem_fund_circuit _ _ _)],
  apply fund_circuit_subset_insert he,
end

-- modify to disjoint union of circuits for iff?
lemma rep.circuit (φ : rep 𝔽 W M) {C : set α} (hMC : M.circuit C) :
  ∃ f : α →₀ 𝔽, (f.support : set α) = C ∧ finsupp.total α W 𝔽 φ f = 0 ∧ f ≠ 0 :=
begin
  obtain ⟨f, ⟨hfssup, ⟨hftot, hfne0⟩⟩⟩ :=
    linear_dependent_comp_subtype'.1 (φ.valid.1.mt (not_indep_iff.2 hMC.dep)),
  refine ⟨f, ⟨_, ⟨hftot, hfne0⟩⟩⟩,
  apply subset.antisymm_iff.2 ⟨hfssup, λ x hx, _⟩,
  by_contra,
  apply φ.valid.2.mt
    (linear_dependent_comp_subtype'.2 ⟨f, ⟨subset_diff_singleton hfssup h, ⟨hftot, hfne0⟩⟩⟩),
  apply hMC.diff_singleton_indep hx,
end

--lemma mem_span_of_mem_cl
-- we need he2 because we are deleting {e} from the funamental circuit for this
lemma mem_span_set_rep_of_not_mem (φ : rep 𝔽 W M) {I : set α} (hI : M.indep I)
(e : α) (he : e ∈ M.cl I) (he2 : e ∉ I) :
 ∃ c : W →₀ 𝔽, (c.support : set W) = φ '' (M.fund_circuit e I \ {e}) ∧
  c.sum (λ mi r, r • mi) = φ e :=
begin
  obtain ⟨c, ⟨hc1, hc2⟩⟩ := mem_span_set.1 (of_basis φ (circuit.diff_singleton_basis
    (indep.fund_circuit_circuit hI ((mem_diff e).2 ⟨he, he2⟩)) (M.mem_fund_circuit e I))
    (M.mem_fund_circuit e I)),
  refine ⟨c, ⟨subset.antisymm_iff.2 ⟨hc1, λ x hx, _⟩, hc2⟩⟩,
  obtain ⟨y, ⟨⟨hy1, hy2⟩, rfl⟩⟩ := hx,
  by_contra,
  have h5 : ∃ (c : W →₀ 𝔽), ↑(c.support) ⊆ ⇑φ '' (M.fund_circuit e I \ {e}) \ {φ y} ∧
    c.sum (λ (mi : W) (r : 𝔽), r • mi) = φ e,
  refine ⟨c, ⟨subset_diff_singleton hc1 h, hc2⟩⟩,
  have h8 : e ∈ ((M.fund_circuit e I) \ {y}),
  { simp only [mem_diff, mem_singleton_iff],
    refine ⟨(M.mem_fund_circuit e I), ne.symm hy2⟩ },
  have h7 := (linear_independent_iff_not_mem_span.1 ((φ.valid' (M.fund_circuit e I \ {y})
    (subset.trans (diff_subset _ _) (fund_circuit_subset_ground he))).2
    (circuit.diff_singleton_indep
    (indep.fund_circuit_circuit hI ((mem_diff e).2 ⟨he, he2⟩)) hy1))) ⟨e, h8⟩,
  simp only [subtype.coe_mk, to_fun_eq_coe] at h7,
  rw [set.image_eta] at h7,
  have h9 : ((λ (a : ↥(M.fund_circuit e I \ {y})), φ ↑a) '' (univ \ {⟨e, h8⟩})) =
    (⇑φ '' (M.fund_circuit e I \ {e}) \ {φ y}),
  { ext;
    refine ⟨λ h, _, λ h20, _⟩,
    { simp only [mem_image, mem_diff, mem_univ, mem_singleton_iff, true_and, set_coe.exists,
        subtype.mk_eq_mk, subtype.coe_mk, exists_prop] at h,
      obtain ⟨a, ⟨⟨ha1, ha2⟩, ⟨ha3, rfl⟩⟩⟩ := h,
      simp only [mem_diff, mem_image, mem_singleton_iff],
      use ⟨a, ⟨⟨ha1, ha3⟩, rfl⟩⟩,
      have h11 : (insert y {a}) ⊂ M.fund_circuit e I,
      rw ssubset_iff_subset_diff_singleton,
      refine ⟨e, ⟨(M.mem_fund_circuit e I), λ x hx, _⟩⟩,
      obtain ⟨rfl, rfl⟩ := hx,
      rw mem_diff_singleton,
      simp only [mem_singleton_iff] at hy2,
      refine ⟨hy1, hy2⟩,
      rw mem_diff_singleton,
      simp only [mem_singleton_iff] at hx,
      rw hx,
      refine ⟨ha1, ha3⟩,
      have h10 := inj_on_of_indep φ
        (circuit.ssubset_indep (indep.fund_circuit_circuit hI ((mem_diff e).2 ⟨he, he2⟩)) h11),
      apply (inj_on.ne_iff h10 _ _).2 ha2,
      simp only [mem_insert_iff, mem_singleton, or_true],
      simp only [mem_insert_iff, eq_self_iff_true, true_or]},
    { obtain ⟨⟨a, ⟨⟨ha1, ha2⟩, rfl⟩⟩, ha3⟩ := h20,
      use a,
      apply mem_diff_singleton.2 ⟨ha1, _⟩,
      simp only [mem_singleton_iff] at ha3,
      by_contra,
      rw h at ha3,
      apply ha3,
      refl,
      refine ⟨(mem_diff _).2 ⟨mem_univ _, mem_singleton_iff.1.mt (subtype.mk_eq_mk.1.mt ha2)⟩, _⟩,
      simp only [subtype.coe_mk]} },
  rw h9 at h7,
  apply h7,
  exact mem_span_set.2 h5,
end

lemma mem_span_set_rep (φ : rep 𝔽 W M) {I : set α} (hI : M.indep I) (e : α) (he : e ∈ M.cl I) :
 ∃ c : W →₀ 𝔽, (c.support : set W) = φ '' (M.fund_circuit e I ∩ I) ∧
  c.sum (λ mi r, r • mi) = φ e :=
begin
  by_cases e ∈ I,
  rw [hI.fund_circuit_eq_of_mem h, singleton_inter_eq_of_mem h],
  simp only [image_singleton, finset.coe_eq_singleton],
  use finsupp.single (φ e) (1 : 𝔽),
  simp only [finsupp.sum_single_index, smul_eq_zero, eq_self_iff_true, true_or, one_smul, and_true],
  apply finsupp.support_single_ne_zero,
  simp only [ne.def, one_ne_zero, not_false_iff],
  rw fund_circuit_inter_eq_diff_of_not_mem _ he h,
  apply mem_span_set_rep_of_not_mem φ hI e he h,
end

-- use finsum instead of finset.sum
lemma mem_sum_basis_zmod2_of_not_mem [fintype α] [module (zmod 2) W] (φ : rep (zmod 2) W M)
{I : set α} (hI : M.indep I) (e : α) (he : e ∈ M.cl I) (heI : e ∉ I) :
  ∑ i in (M.fund_circuit e I \ {e}).to_finset, φ i = φ e :=
begin
  have h3 := subset_insert e (M.fund_circuit e I),
  obtain ⟨c, ⟨hc1, hc2⟩⟩ := mem_span_set_rep_of_not_mem φ hI e he heI,
  rw ← hc2,
  have h4 : c.support = (φ '' (M.fund_circuit e I \ {e})).to_finset :=
    by { simp_rw [← hc1, finset.to_finset_coe] },
  have h7 : (∀ (i : W), i ∈ (⇑φ '' (M.fund_circuit e I \ {e})).to_finset →
    (λ (mi : W) (r : zmod 2), r • mi) i 0 = 0),
  intros x hx,
  simp only [zero_smul],
  rw [finsupp.sum_of_support_subset c (finset.subset_of_eq h4) (λ mi r, r • mi) h7,
    to_finset_image, to_finset_diff, finset.sum_image, finset.sum_congr],
  simp only [eq_self_iff_true],
  { intros x hx,
    simp only,
    haveI := (@add_comm_group.to_add_comm_monoid W _inst_2),
    -- for some reason i have to do this roundabout way of using one_smul because
    -- i can't figure out how to make my monoid instance work for it
    have hc : c (φ x) = 1,
    cases le_iff_lt_or_eq.1 (nat.le_of_lt_succ (zmod.val_lt (c (φ x)))) with h0 h1,
    { by_contra,
      simp only [nat.lt_one_iff, zmod.val_eq_zero] at h0,
      rw ← to_finset_diff at hx,
      have hφ := finset.mem_image_of_mem φ hx,
      rw [← to_finset_image, ← h4, finsupp.mem_support_iff, ne.def] at hφ,
      apply hφ,
      exact h0 },
    { rw [← zmod.nat_cast_zmod_val (c (φ x)), h1, algebra_map.coe_one] },
    rw hc,
    simp only [one_smul] },
  { simp_rw [←set.to_finset_diff, mem_to_finset],
    apply inj_on_of_indep φ (circuit.diff_singleton_indep
      (indep.fund_circuit_circuit hI ((mem_diff e).2 ⟨he, heI⟩)) (M.mem_fund_circuit e I)) },
end

lemma mem_sum_basis_zmod2 [fintype α] [module (zmod 2) W] (φ : rep (zmod 2) W M) {I : set α}
(hI : M.indep I) (e : α) (he : e ∈ M.cl I) :
  φ e = ∑ i in (M.fund_circuit e I ∩ I).to_finset, φ i :=
begin
  by_cases e ∈ I,
  rw [hI.fund_circuit_eq_of_mem h, @to_finset_congr _ ({e}∩I) {e} _ _ (singleton_inter_eq_of_mem h),
     to_finset_singleton, finset.sum_singleton],
  rw to_finset_congr (fund_circuit_inter_eq_diff_of_not_mem _ he h),
  apply eq.symm (mem_sum_basis_zmod2_of_not_mem φ hI e he h),
end

/- A matroid_in is binary if it has a `GF(2)`-representation -/
@[reducible, inline] def matroid_in.is_binary (M : matroid_in α) := M.is_representable (zmod 2)

-- change to is_binary instead of having reps
lemma eq_of_forall_fund_circuit_eq [fintype α] {M M' : matroid_in α} [module (zmod 2) W]
[module (zmod 2) W'] (φM : rep (zmod 2) W M) (φM' : rep (zmod 2) W' M')
(hE : M.E = M'.E) (hB : M.base B) (hB' : M'.base B)
(he : ∀ e ∈ M.E, M.fund_circuit e B = M'.fund_circuit e B) :
  M = M' :=
begin
  have φM := standard_rep φM hB,
  have φM' := standard_rep φM' hB',
  apply eq_of_indep_iff_indep_forall hE,
  intros I hI,
  have hI' := hI,
  rw hE at hI',
  rw [← (standard_rep φM hB).valid' _ hI, ← (standard_rep φM' hB').valid' _ hI'],
  have h2 : (standard_rep φM hB).to_fun ∘ coe = λ i : I, (standard_rep φM hB).to_fun i,
    simp only [eq_self_iff_true],
  have h3 : (standard_rep φM' hB').to_fun ∘ coe = λ i : I, (standard_rep φM' hB').to_fun i,
    simp only [eq_self_iff_true],
  rw [h2, h3],
  simp only [to_fun_eq_coe],
  simp_rw [λ (e : I), (standard_rep φM hB).mem_sum_basis_zmod2 hB.indep _ (@base.mem_cl _ M B hB e (hI e.2)),
    λ (e : I), (standard_rep φM' hB').mem_sum_basis_zmod2 hB'.indep _ (@base.mem_cl _ M' B hB' e (hI' e.2))],
  simp_rw λ (e : I), he e (hI e.2),
  have h6 : (λ (i : ↥I), ∑ (x : α) in (M'.fund_circuit ↑i B ∩ B).to_finset, (standard_rep φM hB) x)
    = (λ (i : ↥I), ∑ (x : α) in (M'.fund_circuit ↑i B ∩ B).to_finset, (standard_rep φM' hB') x),
    simp only,
    have h10 :=  λ (i : ↥I), @finset.sum_congr _ _ (M'.fund_circuit i B ∩ B).to_finset
      (M'.fund_circuit i B ∩ B).to_finset (standard_rep φM hB) (standard_rep φM' hB') _ rfl _,
    simp_rw  [λ (i : I), h10 i],
    intros x hx,
    rw mem_to_finset at hx,
    have h12 := standard_rep_base_eq φM φM' hB hB' ⟨x, (mem_of_mem_inter_right hx)⟩,
    simp at h12,
    rw h12,
  simp_rw h6,
end

lemma contract_circuit_of_insert_circuit (e : α) (C : set α) (he : M.nonloop e) (heC : e ∉ C)
  (hMCe : M.circuit (insert e C)) : (M ⟋ e).circuit C :=
begin
  simp_rw [circuit_iff_forall_ssubset, contract_elem] at *,
  refine ⟨_, λ I hI, _⟩,
  rw [he.indep.contract_dep_iff, union_singleton],
  refine ⟨disjoint_singleton_right.2 heC, hMCe.1⟩,
  rw he.indep.contract_indep_iff,
  refine ⟨disjoint_singleton_right.2 (not_mem_subset (subset_of_ssubset hI) heC), _⟩,
  have h8 : insert e I ⊂ insert e C,
    obtain ⟨a, ⟨haI, haIC⟩⟩ := ssubset_iff_insert.1 hI,
    have ha : ¬(a = e ∨ a ∈ I),
    { push_neg,
      refine ⟨ne_of_mem_of_not_mem (mem_of_mem_of_subset (mem_insert _ I) haIC) heC, haI⟩ },
    apply ssubset_iff_insert.2 ⟨a, ⟨mem_insert_iff.1.mt ha, _⟩⟩,
    rw insert_comm,
    apply insert_subset_insert haIC,
  rw union_singleton,
  apply hMCe.2 _ h8,
end

-- might need something that says if two matroids are rep. over the same field, then we can put them
-- in the same module

-- part (iii) in the proof of theorem 6.5.4
lemma indep_eq_doubleton_of_subset [fintype α] (MI MC : matroid_in α) [finite_rk MI] [finite_rk MC]
  (hrk : MI.rk = MC.rk) (hIC : MI.E = MC.E) (x y : α) (hxy : x ≠ y)
  (hiIC : MI.coindep {x,y} ∨ MC.coindep {x,y}) (hMx : MI ⟍ x = MC ⟍ x) (hMy : MI ⟍ y = MC ⟍ y)
  {Z J : set α} (hxZ : x ∈ Z) (hyZ : y ∈ Z) (hMIZ : MI.indep Z) (hMCZ : ¬ MC.indep Z)
  (hZJ : Z ⊆ J) (hMIJ : MI.indep J) [module (zmod 2) W] [module (zmod 2) W']
  (φI : rep (zmod 2) W (MI ⟋ (J \ {x, y})))
  (φC : rep (zmod 2) W' (MC ⟋ (J \ {x, y}))) : J = {x, y} :=
begin
  apply subset_antisymm _ (insert_subset.2 ⟨hZJ hxZ, singleton_subset_iff.2 (hZJ hyZ)⟩),
  rw ← diff_eq_empty,
  by_contra,
  --have hMIxy : (MI ⟍ {x, y}).indep (J \ {x, y}),
  rw [MI.delete_elem x, MC.delete_elem x] at hMx, --← delete_delete,
  rw [MI.delete_elem y, MC.delete_elem y] at hMy,
  have hMIxyJ := delete_indep_iff.2 ⟨hMIJ.subset (diff_subset J {x, y}),
    @disjoint_sdiff_left _ {x, y} J⟩,
  have hMIxyJ2 := hMIxyJ,
  rw [← union_singleton, ← delete_delete, hMy,
    delete_delete, union_singleton] at hMIxyJ2,
  -- i need something that tells me the rank of a matroid when you contract an independent set
  have hNIC : (MI ⟋ (J \ {x, y})).rk = (MC ⟋ (J \ {x, y})).rk,
    { -- this is due to M and M' having the same rank
      have h2 := MI.er_contract_add_er_eq_er_union (J \ {x, y}) (MI.E \ (J \ {x, y})),
      have h3 := MC.er_contract_add_er_eq_er_union (J \ {x, y}) (MC.E \ (J \ {x, y})),
      rw [union_comm, union_diff_cancel (subset_trans (diff_subset _ _) (hMIJ.subset_ground))] at h2,
      rw [union_comm, union_diff_cancel] at h3,
      have h4 : MI.er (J \ {x, y}) = MC.er (J \ {x, y}),
      { rw [← union_singleton, ← diff_diff, ← MI.delete_er_eq', ← MC.delete_er_eq', hMx] },
      rw [rk_def, rk_def, ← er_eq_coe_iff, eq_comm] at hrk,
      simp only [contract_ground, coe_r_eq_er] at hrk,
      rw [hrk, ← h2, h4] at h3,
      simp only [← coe_r_eq_er] at h3,
      simp only [← enat.coe_add] at h3,
      have h7 : ((MC ⟋ (J \ {x, y})).r (MC.E \ (J \ {x, y})) + MC.r (J \ {x, y})) =
        ((MI ⟋ (J \ {x, y})).r (MI.E \ (J \ {x, y})) + MC.r (J \ {x, y})),
      { rwa [enat.coe_inj] at h3 },
      simp only [rk_def],
      rw eq_comm,
      simp only [contract_ground],
      apply nat.add_right_cancel h7,
      rw ← hIC,
      apply subset_trans (diff_subset _ _) (hMIJ.subset_ground) },
  have hNIneNC : (MI ⟋ (J \ {x, y})) ≠ (MC ⟋ (J \ {x, y})),
  { simp only [ne.def, eq_iff_indep_iff_indep_forall, contract_ground, hIC, eq_self_iff_true,
      true_and, not_forall, exists_prop],
    refine ⟨{x, y}, ⟨_, _⟩⟩,
    { rw subset_diff,
      refine ⟨_, @disjoint_sdiff_right _ {x, y} J⟩,
      rw ← hIC,
      apply (insert_subset.2 ⟨(hMIZ.subset_ground) hxZ, singleton_subset_iff.2
        ((hMIZ.subset_ground) hyZ)⟩) },
    { rw [iff_def, not_and_distrib],
      left,
      push_neg,
      refine ⟨(indep.contract_indep_iff (hMIJ.subset (diff_subset J {x, y}))).2
        ⟨@disjoint_sdiff_right _ {x, y} J, _⟩, _⟩,
      rw union_diff_cancel (insert_subset.2 ⟨hZJ hxZ, singleton_subset_iff.2 (hZJ hyZ)⟩),
      apply hMIJ,
      rw [indep.contract_indep_iff (hMIxyJ2.of_delete), not_and_distrib],
      right,
      rw union_diff_cancel (insert_subset.2 ⟨hZJ hxZ, singleton_subset_iff.2 (hZJ hyZ)⟩),
      apply indep.subset.mt (not_imp.2 ⟨hZJ, hMCZ⟩) } },
  obtain ⟨B, hNIxyB⟩ := (MI ⟋ (J \ {x, y}) ⟍ ({x, y} : set α)).exists_base,
    have hNCxyB := hNIxyB,
    rw [contract_delete_comm _ (@disjoint_sdiff_left _ {x, y} J), ← union_singleton,
      ← delete_delete, hMy, delete_delete, union_singleton,
      ← contract_delete_comm _ (@disjoint_sdiff_left _ {x, y} J)] at hNCxyB,
  have hB : (MI ⟋ (J \ {x, y})).base B ↔ (MC ⟋ (J \ {x, y})).base B,
  { refine ⟨λ hI, _, λ hC, _⟩,
    -- duplicate code, turn into lemma
    { by_contra h2,
      have hCB := hNCxyB.indep.of_delete,
      obtain ⟨B', hB'⟩ := (MC ⟋ (J \ ({x, y} : set α))).exists_base,
      rw [← hI.card] at hNIC,
      apply h2,
      apply hCB.base_of_rk_le_card,
      rw hNIC },
    { by_contra h2,
      have hIB := hNIxyB.indep.of_delete,
      obtain ⟨B', hB'⟩ := (MI ⟋ (J \ ({x, y} : set α))).exists_base,
      rw [← hC.card] at hNIC,
      apply h2,
      apply hIB.base_of_rk_le_card,
      rw hNIC } },
  by_cases (MI ⟋ (J \ {x, y})).base B,
  { apply hNIneNC,
    have hfund : ∀ e ∈ (MI ⟋ (J \ {x, y})).E, (MI ⟋ (J \ {x, y})).fund_circuit e B
      = (MC ⟋ (J \ {x, y})).fund_circuit e B,
      intros e he,
      by_cases h2 : e = y,
      { rw h2 at *,
        have h3 : disjoint (insert y B) {x},
          apply disjoint_singleton_right.2 (mem_insert_iff.1.mt _),
          push_neg,
          refine ⟨hxy, _⟩,
          have h10 := hNIxyB.subset_ground,
          rw [delete_ground, ← union_singleton, ← diff_diff] at h10,
          apply not_mem_subset h10 (not_mem_diff_of_mem (mem_singleton x)),
        have h5 : disjoint (J \ {x, y}) {x},
          rw [← union_singleton, ← diff_diff],
          apply disjoint_sdiff_left,
        rw [← fund_circuit_delete h.indep (h.mem_cl y) h3, MI.contract_delete_comm h5, hMx,
            ← MC.contract_delete_comm h5],
        rw [contract_ground, hIC, ← contract_ground] at he,
        rw fund_circuit_delete (hB.1 h).indep ((hB.1 h).mem_cl y) h3 },
      { have h3 : disjoint (insert e B) {y},
          apply disjoint_singleton_right.2 (mem_insert_iff.1.mt _),
          push_neg,
          refine ⟨ne.symm h2, _⟩,
          have h10 := hNIxyB.subset_ground,
          rw [delete_ground, ← union_singleton, union_comm, ← diff_diff] at h10,
          apply not_mem_subset h10 (not_mem_diff_of_mem (mem_singleton y)),
        have h5 : disjoint (J \ {x, y}) {y},
          rw [← union_singleton, union_comm, ← diff_diff],
          apply disjoint_sdiff_left,
        rw [← fund_circuit_delete h.indep (h.mem_cl e) h3, MI.contract_delete_comm h5, hMy,
            ← MC.contract_delete_comm h5],
        rw [contract_ground, hIC, ← contract_ground] at he,
        rw fund_circuit_delete (hB.1 h).indep ((hB.1 h).mem_cl e) h3 },
      apply eq_of_forall_fund_circuit_eq φI φC _ h (hB.1 h) hfund,
      simp_rw [contract_ground, hIC] },
  { apply h,
    rw delete_base_iff at hNIxyB hNCxyB,
    cases hiIC with hIc hCc,
    { have h3 := (coindep_contract_iff.2 ⟨hIc, @disjoint_sdiff_right _ {x, y} J⟩).cl_compl,
      rw ← hNIxyB.cl at h3,
      apply hNIxyB.indep.base_of_cl_eq_ground h3 },
    { have h3 := (coindep_contract_iff.2 ⟨hCc, @disjoint_sdiff_right _ {x, y} J⟩).cl_compl,
      rw ← hNCxyB.cl at h3,
      apply hB.2,
      apply hNCxyB.indep.base_of_cl_eq_ground h3 } },
end

lemma coindep.base_of_basis_del {X : set α} (hX : M.coindep X) (hB : M.basis B (M.E \ X)) :
  M.base B :=
begin
  obtain ⟨B',hB'⟩ := hX.exists_disjoint_base,
  apply hB'.1.base_of_basis_supset (subset_diff.2 ⟨hB'.1.subset_ground, disjoint.symm hB'.2⟩) hB,
end

lemma delete_elem_eq_of_binary {B : set α} {x y : α} (hBxy : (M ⟍ ({x, y} : set α)).base B)
  (hBx : (M ⟍ x).base B) (hB : M.base B) [fintype α]
  [module (zmod 2) W] (φ : rep (zmod 2) W (M ⟍ ({x, y} : set α))) {Wx : Type*} [add_comm_group Wx]
  [module (zmod 2) Wx]
  (φx : rep (zmod 2) Wx (M ⟍ x)) : (M ⟍ x) =
  (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
    (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E) ⟍ x :=
begin
  apply eq_of_indep_iff_indep_forall,
    simp_rw [delete_elem, delete_ground],
    rw matroid_of_module_fun.ground,
    intros I hI,
    rw [(matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E).delete_elem x,
      delete_indep_iff, ← (standard_rep φx hBx).valid' I hI],
    rw ← (rep_of_matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E).valid' I _,
    simp [rep_of_matroid_of_module_fun],
    have h12 : (λ (x_1 : α), ite (x_1 ∈ M.E) (∑ (x_1 : α) in (M.fund_circuit x_1 B).to_finset
      ∩ B.to_finset, (φ.standard_rep hBxy) x_1) 0) ∘ (coe : I → α) =
      (λ (x_1 : I), ite (x_1.1 ∈ M.E) (∑ (x_1 : α) in (M.fund_circuit x_1 B).to_finset
      ∩ B.to_finset, (φ.standard_rep hBxy) x_1) 0),
      simp only [eq_self_iff_true],
      simp only [subtype.val_eq_coe],
    have h10 : ∀ (x_1 : I), ite (x_1.1 ∈ M.E) (∑ (x_1 : α) in (M.fund_circuit x_1 B).to_finset
      ∩ B.to_finset, (φ.standard_rep hBxy) x_1) 0 = (∑ (x_1 : α) in
      (M.fund_circuit x_1 B).to_finset ∩ B.to_finset, (φ.standard_rep hBxy) x_1),
      { simp only,
        simp only [subtype.val_eq_coe],
        intros e,
        simp_rw [ite_eq_iff],
        left,
        rw delete_elem at hI,
        refine ⟨(M.delete_ground_subset_ground {x}) (hI e.2), rfl⟩ },
    simp_rw [h12, h10],
    have h3 : ((φx.standard_rep hBx) ∘ (coe : I → α)) = λ (e : I), ((φx.standard_rep hBx) e),
      simp only [eq_self_iff_true],
    rw [h3],
    simp_rw λ (e : I), (standard_rep φx hBx).mem_sum_basis_zmod2 hBx.indep _
      (@base.mem_cl _ (M ⟍ x) B hBx e (hI e.2)),
    have hBxs := hBx.subset_ground,
    simp_rw [delete_elem, delete_ground] at *,
    have h5 := diff_subset M.E {x},
    simp_rw λ (e : I), fund_circuit_delete hB.indep (@base.mem_cl _ M B hB e ((diff_subset M.E {x})
      (hI e.2))) (disjoint_singleton_right.2 (mem_insert_iff.1.mt (not_or (ne.symm
      (mem_diff_singleton.1 (hI e.2)).2) (not_mem_subset hBxs
      (not_mem_diff_of_mem (mem_singleton x)))))),
    have h6 : (λ (e : ↥I), ∑ (x : α) in (M.fund_circuit ↑e B ∩ B).to_finset, (standard_rep φx hBx) x) =
      (λ (e : ↥I), ∑ (x : α) in (M.fund_circuit ↑e B ∩ B).to_finset, (standard_rep φ hBxy) x),
      simp only,
      have h10 :=  λ (i : ↥I), @finset.sum_congr _ _ (M.fund_circuit i B ∩ B).to_finset
        (M.fund_circuit i B ∩ B).to_finset (standard_rep φx hBx) (standard_rep φ hBxy) _ rfl _,
      simp_rw  [λ (i : I), h10 i],
      intros x hx,
      rw mem_to_finset at hx,
      have h12 := standard_rep_base_eq φx φ hBx hBxy ⟨x, (mem_of_mem_inter_right hx)⟩,
      simp at h12,
      rw h12,
    simp_rw [h6, to_finset_inter, iff_self_and],
    apply λ h, not_mem_subset hI (not_mem_diff_singleton x M.E),
    rw [delete_elem, delete_ground] at hI,
    rw matroid_of_module_fun.ground,
    apply subset_trans hI (diff_subset M.E {x}),
end

-- write congr lemma
def rep_of_congr {M M' : matroid_in α} (φ : rep 𝔽 W M) (h : M = M') : rep 𝔽 W M' :=
{ to_fun := φ.to_fun,
  valid' := λ I hI, by { rw ← (eq_iff_indep_iff_indep_forall.1 h).1 at hI,
    rw ← (eq_iff_indep_iff_indep_forall.1 h).2, apply φ.valid' I hI, apply hI },
  support := λ e he, by { rw ← (eq_iff_indep_iff_indep_forall.1 h).1 at he, apply φ.support e he } }

-- write refl lemma for the above
lemma rep_eq_of_congr {M M' : matroid_in α} (φ : rep 𝔽 W M) (h : M = M') :
  (φ : α → W) = (rep_of_congr φ h) := rfl

lemma standard_rep_eq_of_congr {M M' : matroid_in α} (φ : rep 𝔽 W M) (h : M = M') {B : set α}
  (hMB : M.base B) (hMB' : M'.base B) :
  ((standard_rep φ hMB) : α → B →₀ 𝔽) = (standard_rep (rep_of_congr φ h) hMB' :  α → B →₀ 𝔽)  := rfl

lemma delete_elem_eq_of_binary_right {B : set α} {x y : α} (hBxy : (M ⟍ ({x, y} : set α)).base B)
  (hBx : (M ⟍ y).base B) (hB : M.base B) [fintype α]
  [module (zmod 2) W] (φ : rep (zmod 2) W (M ⟍ ({x, y} : set α))) {Wy : Type*} [add_comm_group Wy]
  [module (zmod 2) Wy]
  (φx : rep (zmod 2) Wy (M ⟍ y)) : (M ⟍ y) =
  (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
    (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E) ⟍ y :=
begin
  have hMxyyx : M ⟍ ({x, y} : set α) = M ⟍ ({y, x} : set α),
    rw [← union_singleton, union_comm, union_singleton],
  have hByx := hBxy,
  rw [← union_singleton, union_comm, union_singleton] at hByx,
  rw standard_rep_eq_of_congr φ hMxyyx hBxy hByx,
  apply delete_elem_eq_of_binary hByx hBx hB (rep_of_congr φ hMxyyx) φx,
end

def rep_of_del (N : matroid_in α) (φ : rep 𝔽 W N) (D : set α) :
rep 𝔽 W (N ⟍ D) :=
{ to_fun := λ x, if x ∈ D then 0 else φ.to_fun x,
  valid' := λ I hI, by { rw delete_ground at hI,
    have h2 : ∀ x : I, ite ((x : α) ∈ D) 0 (φ.to_fun x) = φ.to_fun x,
      intros x,
      rw ite_eq_iff,
      right,
      refine ⟨((mem_diff x.1).1 (mem_of_subset_of_mem hI x.2)).2, rfl⟩,
    have h8 : ((λ (e : α), ite ((e : α) ∈ D) 0 (φ.to_fun e)) ∘ coe) =
          (λ (e : I), ite ((e : α) ∈ D) 0 (φ.to_fun e)),
      simp only [eq_self_iff_true],
    rw h8,
    simp_rw [λ (e : I), h2 e],
    refine ⟨λ h, delete_indep_iff.2 ⟨((φ.valid' I (subset_trans hI (diff_subset N.E D))).1 h),
    (subset_diff.1 hI).2⟩, λ h, (φ.valid' I (subset_trans hI (diff_subset N.E D))).2
      (matroid_in.delete_indep_iff.1 h).1⟩ },
  support := λ e he,
    begin
      simp only [ite_eq_iff],
      by_cases e ∈ D,
      left,
      refine ⟨h, rfl⟩,
      right,
      have h2 : e ∉ N.E,
        rw delete_ground at he,
        have h3 : N.E ⊆ (N.E \ D) ∪ D,
          simp only [diff_union_self, subset_union_left],
        apply not_mem_subset h3,
        rw mem_union,
        push_neg,
        refine ⟨he, h⟩,
      refine ⟨h, φ.support e h2⟩,
    end  }

def rep_of_contr (N : matroid_in α) (φ : rep 𝔽 W N) (C : set α) (hC : C ⊆ N.E):
  rep 𝔽 (W ⧸ span 𝔽 (φ.to_fun '' C)) (N ⟋ C) :=
{ to_fun := λ x, submodule.quotient.mk (φ.to_fun x),
  valid' := λ I hI,
    begin
      rw contract_ground at hI,
      have h21 : (λ (x : ↥I), φ.to_fun ↑x) '' univ = φ.to_fun '' I,
        { simp only [to_fun_eq_coe, image_univ],
          ext;
          simp only [mem_range, set_coe.exists, subtype.coe_mk, exists_prop, mem_image] },
      obtain ⟨J, hJ⟩ := exists_basis N C hC,
      rw [basis.contract_eq_contract_delete hJ, delete_indep_iff,
        indep.contract_indep_iff hJ.indep],
      have h10 := span_basis φ hJ,
      refine ⟨λ h, _, λ h, _⟩,
      simp only at h,
      simp_rw [← mkq_apply _] at h,
      rw ← φ.valid' _ (union_subset (subset_trans hI (diff_subset _ _)) hJ.subset_ground_left),
      have h30 : disjoint (span 𝔽 (φ.to_fun '' I)) (span 𝔽 (φ.to_fun '' J)),
      { simp_rw [← to_fun_eq_coe] at h10,
        rw h10,
        simp_rw [← to_fun_eq_coe],
        rw ← ker_mkq (span 𝔽 (φ.to_fun '' C)),
        rw [linear_map.linear_independent_iff, ← image_univ, h21, disjoint.comm] at h,
        exact h.2 },
      have h7 := linear_independent.image
        (linear_independent.of_comp ((span 𝔽 (φ '' C)).mkq) h),
      have h8 := linear_independent.image ((φ.valid' J hJ.subset_ground_left).2 (hJ.indep)),
      have h6 := linear_independent.union h7 h8 h30,
      rw [linear_independent_image, image_union],
      refine ⟨⟨_root_.disjoint.of_image (linear_independent.union' h7 h8 h30 h6), h6⟩, _⟩,
      apply @_root_.disjoint.of_image _ _ φ,
      rw disjoint_iff_forall_ne,
      intros x hxI y hyC,
      by_contra h2,
      rw ← h2 at *,
      rw [submodule.disjoint_def, to_fun_eq_coe, h10] at h30,
      specialize h30 x (set_like.mem_coe.1 (mem_of_subset_of_mem subset_span hxI))
        (set_like.mem_coe.1 (mem_of_subset_of_mem
        (subset_trans (image_subset _ (diff_subset _ _)) subset_span) hyC)),
      have h31 := mem_of_subset_of_mem
        (image_subset _ (diff_subset _ _)) hyC,
      obtain ⟨e, ⟨he, rfl⟩⟩ := (mem_image φ I x).1 hxI,
      rw to_fun_eq_coe at h7,
      apply @linear_independent.ne_zero _ 𝔽 W _ _ _ _ _ (⟨φ e, hxI⟩ : φ '' I) h7,
      simp_rw h30,
      simp only [subtype.coe_mk],
      rw inj_on_union (_root_.disjoint.of_image (linear_independent.union' h7 h8 h30 h6)),
      refine ⟨φ.inj_on_of_indep ((φ.valid' I (subset_trans hI (diff_subset _ _))).1
        (linear_independent.of_comp ((span 𝔽 (φ '' C)).mkq) h)),
        ⟨φ.inj_on_of_indep (hJ.indep), λ x hx y hy, set.disjoint_iff_forall_ne.1
        (linear_independent.union' h7 h8 h30 h6) (φ x) (mem_image_of_mem φ hx)
        (φ y) (mem_image_of_mem φ hy)⟩⟩,
      simp_rw [← mkq_apply _],
      rw linear_map.linear_independent_iff,
      refine ⟨(φ.valid' I (indep.subset h.1.2 (subset_union_left I J)).subset_ground).2
        (indep.subset h.1.2 (subset_union_left I J)), _⟩,
      rw ker_mkq (span 𝔽 (φ.to_fun '' C)),
      have h60 := linear_independent.image ((φ.valid' _ h.1.2.subset_ground).2 h.1.2),
      rw image_union at h60,
      rw [← image_univ, h21],
      simp_rw [to_fun_eq_coe],
      simp only [← h10],
      apply linear_independent.union'',
      { apply linear_independent.image
          ((φ.valid' J (indep.subset h.1.2 (subset_union_right I J)).subset_ground).2
            (indep.subset h.1.2 (subset_union_right I J))) },
      { apply linear_independent.image
          ((φ.valid' I (indep.subset h.1.2 (subset_union_left I J)).subset_ground).2
          (indep.subset h.1.2 (subset_union_left I J))) },
      { rw disjoint.comm,
        apply disjoint_image_image,
        have h200 := inj_on_of_indep φ h.1.2,
        rw inj_on at h200,
        intros x hx y hy,
        specialize h200 (mem_of_subset_of_mem (subset_union_left I J) hx)
          (mem_of_subset_of_mem (subset_union_right I J) hy),
        apply mt h200,
        apply disjoint_iff_forall_ne.1 h.1.1 x hx y hy },
      rw [to_fun_eq_coe, union_comm _ _] at h60,
      apply h60,
    end,
  support := λ e he,
    begin
      rw contract_ground at he,
      by_cases e ∈ C,
      rw quotient.mk_eq_zero,
      apply mem_of_subset_of_mem subset_span (mem_image_of_mem _ h),
      rw [φ.support, quotient.mk_zero],
      rw ← union_diff_cancel hC,
      apply (mem_union _ _ _).1.mt (not_or_distrib.2 ⟨h, he⟩),
    end }

/-def rep_of_dual {𝔽 W : Type*} [is_R_or_C 𝔽] [normed_add_comm_group W] [inner_product_space 𝔽 W]
  (M : matroid_in α) (φ : rep 𝔽 W M) : rep 𝔽 (φ.to_submodule)ᗮ M﹡ :=
{ to_fun := λ e, _,
  valid' := _,
  support := _ }-/

def is_rep_of_minor_of_is_rep (N : matroid_in α) (hNM : N ≤m M) (hM : M.is_representable 𝔽) :
  N.is_representable 𝔽 :=
begin
  obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := hM,
  obtain ⟨C, ⟨D, ⟨hC, ⟨hD, ⟨hCD, rfl⟩⟩⟩⟩⟩ := minor.exists_contract_indep_delete_coindep hNM,
  apply is_representable_of_rep (rep_of_del (M ⟋ C) (rep_of_contr M φ C hC.subset_ground) D),
end

lemma minor_closed_rep : minor_closed (matroid_in.is_representable 𝔽 : matroid_in α → Prop) :=
  λ M N hNM hM, is_rep_of_minor_of_is_rep N hNM hM

def is_rep_of_iso_minor_of_is_rep (N : matroid_in γ) (hNM : N ≤i M) (hM : M.is_representable 𝔽) :
  N.is_representable 𝔽 :=
begin
  obtain ⟨M', ⟨hM'M, ⟨ψ⟩⟩⟩ := hNM,
  obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := is_rep_of_minor_of_is_rep M' hM'M hM,
  apply is_representable_of_rep (iso.rep M' N ψ φ),
end

variables [fintype α]


open_locale big_operators

def add_coloop_rep (φ : rep 𝔽 W M) {f : α} (hf : f ∉ M.E) :
  rep 𝔽 (W × 𝔽) (add_coloop M f) :=
{ to_fun := λ (e : α), if e ∈ ({f} : set α) then linear_map.inr 𝔽 W 𝔽 ((λ e : α, 1) e) else
    linear_map.inl 𝔽 W 𝔽 (φ e),
  valid' := λ I hI,
    begin
      by_cases f ∈ I,
      { rw [← union_diff_cancel (singleton_subset_iff.2 h), union_comm],
        simp only [← ite_apply _ (linear_map.inr 𝔽 W 𝔽 ∘ (λ e : α, 1)) (linear_map.inl 𝔽 W 𝔽 ∘ φ)],
        refine ⟨λ h2, _, λ h2, _⟩,
        { have h11 := linear_independent.image h2,
          rw image_union at h11,
          have hM : M.indep (I \ {f} : set α),
            { have h10 := linear_independent.mono (subset_union_left _ _) h11,
                rw ← linear_independent_image at h10,
                have h12 : ∀ e : ((I \ {f}) : set α), (ite ((e : α) ∈ ({f} : set α))
                  ((linear_map.inr 𝔽 W 𝔽) ↑1) ((linear_map.inl 𝔽 W 𝔽) (φ e))
                  = ((linear_map.inl 𝔽 W 𝔽) ∘ φ) e),
                { intros e,
                  rw ite_eq_iff,
                  right,
                  refine ⟨not_mem_of_mem_diff e.2, rfl⟩ },
              simp_rw [λ (e : (I \ {f} : set α)), h12 e,
                @_root_.linear_map.linear_independent_iff _ _ _ _ _ _ _ _ _ _ (linear_map.inl 𝔽 W 𝔽)
                (linear_map.ker_eq_bot_of_injective linear_map.inl_injective)] at h10,
              rw φ.valid at h10,
              apply h10,
             { intros a ha b hb hab,
                have h13 := h2.injective,
                rw [← restrict_eq, ← inj_on_iff_injective] at h13,
                apply h13 (mem_union_left {f} ha) (mem_union_left {f} hb) hab } },
            obtain ⟨B2, hB2⟩ := hM,
            rw [← add_coloop_del_eq M hf, delete_elem, delete_base_iff, add_coloop_ground] at hB2,
            refine ⟨B2 ∪ {f}, ⟨_,
              union_subset_union hB2.2 (subset_refl _)⟩⟩,
            simp only [insert_diff_of_mem, mem_singleton] at hB2,
            rw base_iff_basis_ground,
            have h3 := basis.insert_basis_insert hB2.1 (((add_coloop_eq M (add_coloop M f) hf).1
              rfl).1.insert_indep_of_indep hB2.1.indep),
            simp only [insert_diff_singleton] at h3,
            rw [add_coloop_ground, union_singleton],
            apply h3 },
        { rw [linear_independent_image, image_union],
          have h12 : (λ (e : α), ite (e ∈ ({f} : set α)) ((linear_map.inr 𝔽 W 𝔽) ↑1)
            ((linear_map.inl 𝔽 W 𝔽) (φ e))) '' (I \ {f}) =
            (linear_map.inl 𝔽 W 𝔽) '' (φ '' (I \ {f})),
            { ext;
              simp only [mem_image, mem_diff, mem_singleton_iff, comp_app],
              refine ⟨λ h, _, λ h, _⟩,
              { obtain ⟨x, ⟨⟨hx1, hx3⟩, hx2⟩⟩ := h,
                refine ⟨φ x, ⟨⟨x, ⟨⟨hx1, hx3⟩, rfl⟩⟩, _⟩⟩,
                rw [← hx2, eq_comm, ite_eq_iff],
                right,
                refine ⟨hx3, rfl⟩ },
              { obtain ⟨x, ⟨⟨x2, ⟨⟨hx3, hx4⟩, rfl⟩⟩, hx2⟩⟩ := h,
                refine ⟨x2, ⟨⟨hx3, hx4⟩, _⟩⟩,
                rw [← hx2, ite_eq_iff],
                right,
                refine ⟨hx4, rfl⟩ } },
          have h13 : (λ (e : α), ite (e ∈ ({f} : set α)) ((linear_map.inr 𝔽 W 𝔽) ↑1)
            ((linear_map.inl 𝔽 W 𝔽) (φ e))) '' {f} = (linear_map.inr 𝔽 W 𝔽) '' (↑1 '' ({f} : set α)),
            { simp_rw [image_singleton, singleton_eq_singleton_iff, ite_eq_iff],
              left,
              refine ⟨mem_singleton _, rfl⟩ },
          rw [h12, h13],
          apply linear_independent.inl_union_inr,
          { have h6 := (h2.subset (subset_union_left _ _)).indep_delete_of_disjoint
              (disjoint_sdiff_left),
            rw [← delete_elem, add_coloop_del_eq M hf, ← φ.valid] at h6,
            apply h6.image },
          { rw image_singleton,
            apply linear_independent_singleton,
            simp only [algebra_map.coe_one, pi.one_apply, ne.def, one_ne_zero, not_false_iff] },
          rw inj_on_union (disjoint_sdiff_left),
          refine ⟨_, ⟨inj_on_singleton _ _, _⟩⟩,
          { intros a ha b hb hab,
            simp only [if_neg (not_mem_of_mem_diff ha), if_neg (not_mem_of_mem_diff hb)] at hab,
            have hab2 := linear_map.inl_injective hab,
            have h4 := (h2.subset (subset_union_left _ _)).indep_delete_of_disjoint
              (disjoint_sdiff_left),
            rw [← delete_elem, add_coloop_del_eq M hf] at h4,
            apply (inj_on_of_indep φ h4) ha hb (linear_map.inl_injective hab) },
          intros a ha b hb,
          simp only [if_pos hb, if_neg (not_mem_of_mem_diff ha)],
          simp only [linear_map.coe_inl, linear_map.coe_inr, ne.def, prod.mk.inj_iff, not_and],
          intros hc,
          by_contra,
          have h6 := (h2.subset (subset_union_left _ _)).indep_delete_of_disjoint
              (disjoint_sdiff_left),
          rw [← delete_elem, add_coloop_del_eq M hf] at h6,
          apply φ.ne_zero_of_nonloop (h6.nonloop_of_mem ha),
          rw hc } },
      { have h8 : ((λ (e : α), ite (e ∈ ({f} : set α)) ((linear_map.inr 𝔽 W 𝔽) ↑((λ (e : α), 1) e))
          ((linear_map.inl 𝔽 W 𝔽) (φ e))) ∘ coe) =
          (λ (e : I), ite ((e : α) ∈ ({f} : set α)) ((linear_map.inr 𝔽 W 𝔽) ↑((λ (e : α), 1) e))
          ((linear_map.inl 𝔽 W 𝔽) (φ e))),
          simp only [eq_self_iff_true],
        rw h8,
        have h3 : ∀ (e : I), (ite ((e : α) ∈ ({f} : set α))
          ((linear_map.inr 𝔽 W 𝔽) ↑((λ (e : α), 1) e)) ((linear_map.inl 𝔽 W 𝔽) (φ e))) =
              ((linear_map.inl 𝔽 W 𝔽) ∘ φ) e,
        { intros,
          simp_rw [ite_eq_iff],
          right,
          refine ⟨mem_singleton_iff.1.mt (ne_of_mem_of_not_mem e.2 h), rfl⟩ },
        simp_rw [λ (e : I), h3 e],
        rw [@_root_.linear_map.linear_independent_iff _ _ _ _ _ _ _ _ _ _
          (linear_map.inl 𝔽 W 𝔽)
          (linear_map.ker_eq_bot_of_injective linear_map.inl_injective), φ.valid],
        refine ⟨λ h2, _, λ h2, _⟩,
        { rw [← add_coloop_del_eq M hf, delete_elem, delete_indep_iff] at h2,
          apply h2.1 },
        { rw [← add_coloop_del_eq M hf, delete_elem, delete_indep_iff],
          refine ⟨h2, disjoint_singleton_right.2 h⟩ } },
    end,
  support := λ e he,
    begin
      by_cases e ∈ {f},
      { by_contra h2,
        apply he,
        rw [add_coloop_ground, mem_singleton_iff.1 h],
        apply mem_insert },
      { have he2 := not_mem_subset (subset_union_left _ _) he,
        rw ite_eq_iff,
        right,
        refine ⟨h, _⟩,
        simp only [linear_map.coe_inl, prod.mk_eq_zero, eq_self_iff_true,
          and_true],
        rw [add_coloop_ground, mem_insert_iff, not_or_distrib] at he,
        apply φ.support e he.2 },
    end }

lemma U1k_representable (k : ℕ) (hk : 1 ≤ k) [nontrivial 𝔽] : (unif 1 k).is_representable 𝔽 :=
begin
  have φ := @rep.mk _ 𝔽 _ _ _ _ (unif 1 k) (λ x, (1 : 𝔽)) (λ I hI, _)
    (by { intros e he,
          by_contra,
          apply he,
          simp only [unif_ground_eq, mem_univ] }),
  { rw [is_representable],
    apply is_representable_of_rep φ },
  rw [unif_indep_iff],
  refine ⟨λ h, _, λ h, _⟩,
  { rw [ncard, nat.card_eq_fintype_card, ← finrank_self 𝔽],
    apply fintype_card_le_finrank_of_linear_independent h },
  { cases le_iff_lt_or_eq.1 h with h0 h1,
    { rw [ncard_eq_zero.1 (nat.lt_one_iff.1 h0), linear_independent_image (λ x hx y hy hxy,
        (inj_on_empty (λ x, (1 : 𝔽))) hx hy rfl), image_empty],
      apply linear_independent_empty 𝔽 _ },
    { obtain ⟨a, rfl⟩ := ncard_eq_one.1 h1,
      rw [linear_independent_image (λ x hx y hy hxy, (inj_on_singleton (λ x, (1 : 𝔽)) a) hx hy rfl),
        image_singleton],
      apply linear_independent_singleton,
      simp only [ne.def, one_ne_zero, not_false_iff] } },
end

lemma U23_binary : matroid_in.is_binary (unif 2 3) :=
begin
  have hcard3 : fintype.card ((set.univ \ {0}) : set (fin 2 → zmod 2)) = 3,
  { rw [← to_finset_card, to_finset_diff, finset.card_sdiff, to_finset_univ, finset.card_univ,
      to_finset_card, card_singleton, @fintype.card_fun (fin 2) (zmod 2) _ _ _, zmod.card 2,
      fintype.card_fin, pow_two, nat.sub_one, nat.pred_eq_succ_iff, two_mul],
    simp only [to_finset_univ, to_finset_subset, finset.coe_univ, singleton_subset_iff] },
  have f := equiv.symm (fintype.equiv_fin_of_card_eq hcard3),
  have φ := @rep.mk _ (zmod 2) (fin 2 → zmod 2) _ _ _ (unif 2 3) (λ x, (f x)) (λ I hI, _)
    (by { simp only [unif_ground_eq, mem_univ, not_true, is_empty.forall_iff, forall_const]}),
  { rw [matroid_in.is_binary, is_representable],
    apply is_representable_of_rep φ },
  rw [unif_indep_iff],
  refine ⟨λ h, _, λ h, _⟩,
  -- now the possible sizes of vector families for h are 0, 1, 2.
  { rw [ncard, nat.card_eq_fintype_card, ← @finrank_fin_fun (zmod 2) _ _ 2],
    apply fintype_card_le_finrank_of_linear_independent h },
  rw [linear_independent_image (λ x hx y hy hxy,
    (f.injective.inj_on I) hx hy (subtype.coe_inj.1 hxy))],
  cases le_iff_lt_or_eq.1 h with h1 h2,
  cases le_iff_lt_or_eq.1 (nat.le_of_lt_succ h1) with h0 h1,
  { rw [ncard_eq_zero.1 (nat.lt_one_iff.1 h0), image_empty],
    apply linear_independent_empty (zmod 2) _ },

  { obtain ⟨a, rfl⟩ := ncard_eq_one.1 h1,
    rw [image_singleton],
    apply linear_independent_singleton,
    -- if i plug this in directly it wants me to provide a nontrivial (zmod 2) instance
    apply (mem_diff_singleton.1 (f a).2).2 },

  { obtain ⟨x, ⟨y, ⟨hxy, rfl⟩⟩⟩ := ncard_eq_two.1 h2,
    rw [image_insert_eq, image_singleton, linear_independent_insert, mem_span_singleton, not_exists],
    refine ⟨linear_independent_singleton ((mem_diff_singleton.1 (f y).2).2), λ a, _⟩,
    cases le_iff_lt_or_eq.1 (nat.le_of_lt_succ (zmod.val_lt a)) with h0 h1,
    { rw [(zmod.val_eq_zero a).1 (nat.lt_one_iff.1 h0), zero_smul],
      apply ne.symm (mem_diff_singleton.1 (f x).2).2 },
      rw [← zmod.nat_cast_zmod_val a, h1, algebra_map.coe_one, one_smul],
      by_contra,
      apply hxy (f.injective (subtype.coe_inj.1 (eq.symm h))),
      by_contra,
      apply hxy (mem_singleton_iff.2 (f.injective (subtype.coe_inj.1 (h)))) },
end

lemma U22_binary : matroid_in.is_binary (unif 2 2) :=
begin
  have h23 : 2 ≤ 3,
    simp only [nat.bit0_le_bit1_iff],
  apply is_rep_of_iso_minor_of_is_rep (unif 2 2) (unif_iso_minor h23) U23_binary,
end

lemma U24_nonbinary : ¬ matroid_in.is_binary (unif 2 4) :=
begin
  by_contra h2,
  rw [matroid_in.is_binary, is_representable] at h2,
  obtain ⟨B, ⟨hB, ⟨φ'⟩⟩⟩ := h2,
  { have h8 := (φ'.subset_nonzero_of_simple U24_simple),
    have h50 := @span_mono (zmod 2) _ _ _ _ _ _ (subset_univ (φ' '' (unif 2 4).E)),
    rw ← span_span at h50,
    have h70 := subset_trans h8 (@diff_subset_diff_left _ _ _
      ({0} : set (B →₀ zmod 2)) (span_le.1 h50)),
    -- need basis
    have h11 := ((φ'.valid' _ hB.subset_ground).2 hB.indep),
    have h20 : (finrank (zmod 2) (B →₀ zmod 2)) = 2,
      simp only [finrank_finsupp, fintype.card_of_finset, finset.filter_congr_decidable],
      rw unif_base_iff at hB,
      rw filter_mem_univ_eq_to_finset,
      simp_rw ← hB,
      rw [ncard_def, nat.card_eq_fintype_card, to_finset_card],
      simp only [bit0_le_bit0, nat.one_le_bit0_iff, nat.lt_one_iff],
    have h10 := finite_dimensional.fin_basis (zmod 2) (B →₀ zmod 2),
    rw h20 at h10,
    haveI : fintype (B →₀ zmod 2),
      apply finsupp.fintype,
    have h9 := @module.card_fintype _ (zmod 2) (B →₀ zmod 2) _ _ _ _ h10 _ _,
    simp only [zmod.card, fintype.card_fin] at h9,
    have h12 := fintype.card_le_of_embedding (embedding_of_subset _ _ h70),
    simp_rw [← to_finset_card, to_finset_diff] at h12,
    rw [finset.card_sdiff, span_univ, top_coe, to_finset_univ, finset.card_univ, h9,
      to_finset_card, to_finset_singleton, finset.card_singleton] at h12,
    have h80 : fintype.card (φ' '' (unif 2 4).E) = fintype.card (fin 4),
    { rw card_image_of_inj_on (φ'.inj_on_ground_of_simple U24_simple),
      simp only [unif_ground_eq, ← to_finset_card, to_finset_univ, finset.card_univ] },
    rw [h80, fintype.card_fin, pow_two, two_mul, nat.succ_add_sub_one] at h12,
    linarith,
    simp only [span_univ, top_coe, to_finset_univ, to_finset_subset,
      finset.coe_univ, singleton_subset_iff], },
end

def rep_of_loop (M : matroid_in α) [finite_rk M] {f : α} (hf : M.loop f)
  (φ : rep 𝔽 W (M ⟍ f)) : rep 𝔽 W M :=
{ to_fun := φ,
  valid' := λ I hI,
    begin
      by_cases f ∈ I,
      { rw ← not_iff_not,
        refine ⟨λ h2, _, λ h2, _⟩,
        { apply indep.nonloop_of_mem.mt,
          simp only [not_forall, exists_prop],
          refine ⟨h, not_nonloop_iff.2 hf⟩ },
        have hfφ := φ.support f,
        by_contra h3,
        have h4 : linear_independent 𝔽 (φ ∘ coe) = linear_independent 𝔽 (λ (i : I), φ i),
          simp only [eq_iff_iff],
        rw h4 at h3,
        apply @linear_independent.ne_zero _ 𝔽 W ((λ (i : I), φ i.1)) _ _ _ _ ⟨f, h⟩ h3,
        simp only,
        apply hfφ,
        rw [delete_elem, delete_ground],
        apply not_mem_diff_singleton },
      have hIf := subset_diff_singleton hI h,
      rw φ.valid,
      simp only [delete_elem, delete_indep_iff, disjoint_singleton_right, and_iff_left_iff_imp],
      intros hf2,
      apply h,
    end,
  support := λ e he,
    begin
      by_cases e = f,
      rw h,
      apply φ.support,
      simp only [delete_elem, delete_ground, not_mem_diff_singleton, not_false_iff],
      apply φ.support,
      simp only [delete_elem, delete_ground, mem_diff, mem_singleton_iff, not_and, not_not],
      contrapose,
      intros,
      apply he
    end }

-- matroid_of_module_fun requires finite_dimensional
lemma parallel_extend_rep (φ : rep 𝔽 W M) {x y : α} (hMx : M.nonloop x) (hy : y ∉ M.E)
[finite_dimensional 𝔽 W] :
  matroid_of_module_fun 𝔽 W (λ (e : α), if e = y then - φ x else φ e) (insert y M.E) =
  parallel_extend M x y :=
begin
  rw ← (eq_parallel_extend_iff hMx hy).2,
  rw circuit_iff_dep_forall_diff_singleton_indep,
    refine ⟨⟨_, λ e he, _⟩, _⟩,
    rw dep,
    refine ⟨_, _⟩,
    { simp only [matroid_of_module_fun, matroid_of_indep_of_bdd'_apply, not_and_distrib],
      left,
      --simp_rw [← ite_apply],
      rw not_linear_independent_iff,
      refine ⟨finset.univ, ⟨λ e, 1, _⟩⟩,
      simp only [one_smul, finset.mem_univ, ne.def, one_ne_zero, not_false_iff, set_coe.exists,
        mem_insert_iff, mem_singleton_iff, exists_prop, and_true, exists_or_eq_right],
      convert_to (∑ (x_1 : α) in {x, y}, ite (x_1 = y) (-φ x) (φ x_1) = 0),
      rw @finset.sum_subtype _ _ _ ({x, y} : set α) _ {x, y},
      refl,
      intros e,
      rw [← finset.mem_coe, finset.coe_insert, finset.coe_singleton],
      refl,
      rw [finset.sum_insert (finset.mem_singleton.1.mt (ne_of_mem_of_not_mem hMx.mem_ground hy)),
        finset.sum_singleton, if_pos rfl, if_neg (ne_of_mem_of_not_mem hMx.mem_ground hy)],
      simp only [add_right_neg] },
    rw [insert_eq, union_comm, ← insert_eq],
    apply insert_subset_insert (singleton_subset_iff.2 hMx.mem_ground),
    obtain ⟨rfl | _⟩ := mem_insert_iff.1 he,
    { simp only [insert_diff_of_mem, mem_singleton,
        diff_singleton_eq_self (mem_singleton_iff.1.mt (ne_of_mem_of_not_mem hMx.mem_ground hy)),
        matroid_of_module_fun, matroid_of_indep_of_bdd'_apply, not_and_distrib],
      refine ⟨_, singleton_subset_iff.2 (mem_insert y _)⟩,
      have h2 : ∀ e : ({y} : set α), ↑e = y,
        intros e,
        apply mem_singleton_iff.1 e.2,
      simp_rw [h2, eq_self_iff_true, if_true],
      rw [@linear_independent_image _ _ _ _ _ _ _ (λ (e : α), - φ x) (inj_on_singleton _ _),
        image_singleton],
      apply @linear_independent_singleton 𝔽 _ _ _ _ _ _ _
        (neg_ne_zero.2 (φ.ne_zero_of_nonloop hMx)) },
    rw [mem_singleton_iff.1 h, insert_eq x {y}, union_comm, ← insert_eq],
    simp only [insert_diff_of_mem, mem_singleton,
      diff_singleton_eq_self (mem_singleton_iff.1.mt (ne.symm
      (ne_of_mem_of_not_mem hMx.mem_ground hy))), matroid_of_module_fun,
      matroid_of_indep_of_bdd'_apply, not_and_distrib],
    refine ⟨_, singleton_subset_iff.2 (mem_of_mem_of_subset hMx.mem_ground (subset_insert y _))⟩,
    have h2 : ∀ e : ({x} : set α), ↑e ≠ y,
      intros e,
      have h3 := (ne_of_mem_of_not_mem hMx.mem_ground hy),
      rw ← mem_singleton_iff.1 e.2 at h3,
      apply h3,
    simp_rw [h2, if_false],
    rw [linear_independent_image (inj_on_singleton _ _), image_singleton],
    exact linear_independent_singleton (φ.ne_zero_of_nonloop hMx),
  simp only [delete_elem, ← delete_matroid_of_module_fun, insert_diff_of_mem, mem_singleton,
    diff_singleton_eq_self hy],
  have h10 : ∀ e : α, e ∈ M.E → ite (e = y) (-φ x) (φ e) = φ e,
    intros e he,
    rw if_neg (ne_of_mem_of_not_mem he hy),
  simp_rw [matroid_of_module_fun_congr 𝔽 W _ _ _ h10],
  rw ← matroid_of_module_fun_rep_eq,
end

-- use matroid_of_module_func and write parallel_extend_rep
def rep_of_parallel (M : matroid_in α) [finite_rk M] [finite_dimensional 𝔽 W] {x y : α}
  (hxy : x ≠ y) (hf : M.circuit {x, y}) (φ : rep 𝔽 W (M ⟍ y)) : rep 𝔽 W M :=
begin
  have hx : (M ⟍ y).nonloop x,
    have hyxy : y ∈ {x, y},
      rw [insert_eq, union_comm, ← insert_eq],
      -- squeeze_simp breaks
      simp,
    have h2 := hf.diff_singleton_indep hyxy,
    rw [insert_eq, union_comm, ← insert_eq] at h2,
    simp at h2,
    rw diff_singleton_eq_self (mem_singleton_iff.1.mt (ne.symm hxy)) at h2,
    have h3 := delete_indep_iff.2 ⟨h2, disjoint_singleton.2 hxy⟩,
    rw delete_elem,
    apply h3.nonloop,
  have hy : y ∉ (M ⟍ y).E,
    rw [delete_elem, delete_ground],
    simp only [not_mem_diff_singleton, not_false_iff],
  rw [(eq_parallel_extend_iff hx hy).2 ⟨hf, rfl⟩, ← parallel_extend_rep φ hx hy],
  apply rep_of_matroid_of_module_fun,
end

def series_extend_rep (φ : rep 𝔽 W M) {x y : α} (hx : x ∈ M.E)
  (hy : y ∉ M.E) (hMx : ¬ M.coloop x) : rep 𝔽 (W × 𝔽) (series_extend M x y) :=
{ to_fun := λ (e : α),
    if e = x
    then
      (linear_map.inl 𝔽 W 𝔽 ∘ φ + linear_map.inr 𝔽 W 𝔽 ∘ (λ e : α, 1)) e
    else
      if e = y then linear_map.inr 𝔽 W 𝔽 1 else (linear_map.inl 𝔽 W 𝔽 ∘ φ) e,
  valid' := λ I hI,
    begin
      refine ⟨_, λ h2, _⟩,
      { contrapose,
      intros h2,
      rw linear_dependent_comp_subtype',
      rw not_indep_iff at h2,
      obtain ⟨C, ⟨hCI, hCcct⟩⟩ := exists_circuit_subset_of_dep h2,
      by_cases hxC : x ∈ C,
      { have hyC := (series_pair_mem_circuit _ _ _ hCcct
          (series_extend_cocircuit hx hMx hy)).1 hxC,
        rw [← @union_diff_cancel _ {y} C (singleton_subset_iff.2 hyC), union_comm,
          union_singleton] at hCcct,
        have hMcct := contract_circuit_of_insert_circuit y (C \ {y})
          ((series_extend_cocircuit hx hMx hy).nonloop_of_mem
          (mem_insert_of_mem x (mem_singleton _))) (not_mem_diff_singleton _ _) hCcct,
        rw [series_extend_contract_eq M x y hy] at hMcct,
        obtain ⟨f, ⟨hC, ⟨hftot, hfne0⟩⟩⟩ := rep.circuit φ hMcct,
        rw ← hC at hCcct hMcct,
        refine ⟨(⟨(insert y f.support), (λ e : α, if e = y then - f x else f e), λ a,
          ⟨λ ha, _, λ ha, _⟩⟩ : α →₀ 𝔽), _⟩,
        { obtain ⟨rfl | ha⟩ := finset.mem_insert.1 ha,
          { simp only [eq_self_iff_true, if_true, ne.def, neg_eq_zero],
            rw [← ne.def, ← finsupp.mem_support_iff, ← finset.mem_coe, hC],
            apply mem_diff_of_mem hxC (mem_singleton_iff.1.mt (ne_of_mem_of_not_mem hx hy)) },
          { rw if_neg (ne_of_mem_of_not_mem (finset.mem_coe.2 h)
              (not_mem_subset (subset_of_eq hC) (not_mem_diff_singleton _ _))),
            apply finsupp.mem_support_iff.1 h } },
        { apply finset.mem_insert.2,
          by_cases hay : a = y,
          { apply or.intro_left _ hay },
          { rw if_neg hay at ha,
            apply or.intro_right _ (finsupp.mem_support_iff.2 ha) } },
        refine ⟨_, ⟨_, _⟩⟩,
        { rw finsupp.mem_supported,
          simp only [finset.coe_insert, hC],
          apply insert_subset.2 ⟨mem_of_subset_of_mem hCI hyC, subset_trans (diff_subset _ _) hCI⟩},
        { simp_rw finset.insert_eq y f.support,
          dsimp [finsupp.total_apply, finsupp.sum],
          dsimp [finsupp.total_apply, finsupp.sum] at hftot,
          simp_rw [ite_smul, smul_ite],
          simp only [prod.ext_iff, prod.smul_mk, zero_add, add_zero, algebra.id.smul_eq_mul,
            mul_one, smul_zero],
          rw [finset.sum_union, ← @finset.sdiff_union_of_subset _ _ ({x} : finset α) f.support _,
            finset.sum_union, finset.sum_singleton],
          simp only [if_pos rfl, if_neg (ne_of_mem_of_not_mem hx hy),
            if_neg (ne.symm (ne_of_mem_of_not_mem hx hy)), ← prod_mk_sum],
          have hx2 : ∀ (e : α), e ∈ ({x} : finset α) → e ≠ y,
            intros e he,
            rw [finset.mem_singleton.1 he],
            apply ne_of_mem_of_not_mem hx hy,
          have hx3 : ∀ (e : α), e ∈ ({x} : finset α) → e = x,
            intros e he,
            rw [finset.mem_singleton.1 he],

          rw [finset.sum_ite_of_false _ _ hx2, finset.sum_ite_of_true _ _ hx3],
          simp only [neg_smul, eq_self_iff_true, if_true, pi.add_apply,
            prod.mk_add_mk, add_zero, zero_add, prod.smul_mk, algebra.id.smul_eq_mul, mul_one,
            prod.neg_mk],

          simp only [prod.fst_add, zero_add, prod.fst_zero, prod.snd_add, prod.snd_zero],
          rw [finset.sum_ite_of_false _ _ (λ e he, _), finset.sum_ite_of_false _ _ (λ e he, _)],
          simp only [finset.sum_ite_of_false _ _ (λ e he, _), ← prod_mk_sum],
          rw finset.sum_ite_of_false _ _ (λ e he, _),
          rw [← prod_mk_sum, finset.sum_const_zero, zero_add],
          simp only,
          rw ← finset.sum_union, --(finset.sdiff_disjoint),
          simp only [finset.sdiff_union_self_eq_union, finset.sum_singleton, add_left_neg,
            eq_self_iff_true, and_true],
          rw [finset.union_comm, ← finset.insert_eq, finset.insert_eq_of_mem],
          apply hftot,
          rw [← finset.mem_coe, hC],
          apply mem_diff_singleton.2 ⟨hxC, ne_of_mem_of_not_mem hx hy⟩,
          simp only [finset.disjoint_singleton_right, finset.mem_sdiff, finset.mem_singleton,
            eq_self_iff_true, not_true, and_false, not_false_iff], -- avoiding decidable_eq instance
          rw [← finset.mem_coe, finset.coe_sdiff, hC, mem_diff, mem_diff] at he,
          apply mem_singleton_iff.2.mt he.1.2,
          rw [finset.mem_sdiff, finset.mem_singleton] at he,
          apply he.2,
          rw [← finset.mem_coe, finset.coe_sdiff, hC, mem_diff, mem_diff] at he,
          apply mem_singleton_iff.2.mt he.1.2,
          simp only [finset.disjoint_singleton_right, finset.mem_sdiff, finset.mem_singleton,
            eq_self_iff_true, not_true, and_false, not_false_iff],
          rw [finset.singleton_subset_iff, ← finset.mem_coe, hC],
          apply mem_diff_singleton.2 ⟨hxC, ne_of_mem_of_not_mem hx hy⟩,
          rw [← finset.disjoint_coe, hC],
          simp only [finset.coe_singleton, disjoint_singleton_left, not_mem_diff_singleton,
            not_false_iff] },
        rw ne.def,
        rw finsupp.ext_iff,
        push_neg,
        use x,
        simp only [ne.def, finsupp.coe_mk, finsupp.coe_zero, pi.zero_apply],
        rw if_neg (ne_of_mem_of_not_mem hx hy),
        apply finsupp.mem_support_iff.1,
        rw [← finset.mem_coe, hC],
        apply mem_diff_singleton.2 ⟨hxC, ne_of_mem_of_not_mem hx hy⟩ },
      { have hyC := (series_pair_mem_circuit _ _ _ hCcct
          (series_extend_cocircuit hx hMx hy)).2.mt hxC,
        have h4 := (@indep.of_contract _ _ {y} _).mt (not_indep_iff.2 hCcct.dep),
        rw [← contract_elem, series_extend_contract_eq M x y hy, ← φ.valid,
          linear_dependent_comp_subtype'] at h4,
        obtain ⟨f, ⟨hC, ⟨hftot, hfne0⟩⟩⟩ := h4,
        refine ⟨f, ⟨subset_trans hC hCI, ⟨_, hfne0⟩⟩⟩,
        dsimp [finsupp.total_apply, finsupp.sum],
        dsimp [finsupp.total_apply, finsupp.sum] at hftot,
        simp_rw smul_ite,
        rw [finset.sum_ite_of_false _ _ (λ e he, _),
          finset.sum_ite_of_false _ _ (λ e he, _)],
        simp only [prod.smul_mk, algebra.id.smul_eq_mul, mul_zero, ← prod_mk_sum, hftot,
          finset.sum_const_zero, prod.mk_eq_zero, eq_self_iff_true, and_self],
        { apply ne_of_mem_of_not_mem (finset.mem_coe.2 he)
            (not_mem_subset ((f.mem_supported _).1 hC) hyC) },
        { apply ne_of_mem_of_not_mem (finset.mem_coe.2 he)
            (not_mem_subset ((f.mem_supported _).1 hC) hxC) } } },
      { simp_rw [linear_independent_comp_subtype, finsupp.total_apply, smul_ite],
        dsimp [finsupp.sum],
        simp only [add_zero, zero_add, mul_one, smul_zero, mul_zero, finset.sum_ite, prod.ext_iff,
          finset.filter_congr_decidable, prod.fst_add, prod.fst_zero, prod.snd_add,
          prod.snd_zero, finset.filter_eq', finset.filter_ne', ← prod_mk_sum,
          finset.sum_const_zero, zero_add, add_zero],
        intros l hl hl0,
        by_cases hyI : (series_extend M x y).indep ({y} ∪ I : set α),
        { have hyI2 := (hyI.subset (subset_union_left _ _)).union_indep_iff_contract_indep.1 hyI,
          rw [← contract_elem, series_extend_contract_eq M x y hy, ← φ.valid,
            linear_independent_comp_subtype] at hyI2,
          simp_rw [finsupp.total_apply] at hyI2,
          have hxl : x ∉ l.support,
          { by_contra hxl,
            rw [if_pos hxl] at hl0,
            specialize hyI2 (l.filter (≠ y)) _ _,
            { rw [finsupp.mem_supported, finsupp.support_filter, finset.filter_ne',
                finset.coe_erase],
              apply diff_subset_diff_left ((l.mem_supported _).1 hl) },
            { rw [finsupp.sum_filter_index, finsupp.support_filter, finset.filter_ne',
                finset.sum_eq_add_sum_diff_singleton (finset.mem_erase.2
                ⟨ne_of_mem_of_not_mem hx hy, hxl⟩), ← finset.erase_eq],
              rw [finset.erase_right_comm, finset.sum_singleton] at hl0,
              apply hl0.1 },
            apply finsupp.mem_support_iff.1 hxl,
            rw [← l.filter_apply_pos (≠ y) (ne_of_mem_of_not_mem hx hy), hyI2],
            simp only [finsupp.coe_zero, pi.zero_apply] },
          simp only [if_neg hxl, finset.sum_empty, zero_add] at hl0,
          have hyl : y ∉ l.support,
          { by_contra hyl,
            rw [if_pos (finset.mem_erase.2 ⟨ne.symm (ne_of_mem_of_not_mem hx hy), hyl⟩),
              finset.sum_singleton] at hl0,
             apply finsupp.mem_support_iff.1 hyl,
             apply hl0.2 },
          specialize hyI2 l _ _,
          { rw [finsupp.mem_supported],
            apply subset_diff_singleton ((l.mem_supported 𝔽).2 hl) hyl },
          { dsimp [finsupp.sum],
            rw [finset.erase_eq_of_not_mem hxl, finset.erase_eq_of_not_mem hyl] at hl0,
            apply hl0.1 },
          apply hyI2 },
      { have hyl : y ∉ l.support,
        { by_contra,
          rw [singleton_union, insert_eq_of_mem (mem_of_subset_of_mem
            ((l.mem_supported _).1 hl) h)] at hyI,
          apply hyI h2 },
        rw [if_neg (finset.mem_erase.1.mt (not_and_distrib.2 (or.intro_right _ hyl))),
          finset.sum_empty, add_zero] at hl0,
        have hxl : x ∉ l.support,
        { by_contra hxl,
          simp only [if_pos hxl, finset.sum_singleton] at hl0,
          apply finsupp.mem_support_iff.1 hxl,
          apply hl0.2 },
        rw [if_neg hxl, finset.sum_empty, zero_add] at hl0,
        rw not_indep_iff _ at hyI,
        have hIxy : (series_extend M x y).indep ({y} ∪ (I \ {x}) : set α),
        { by_contra hIyxn,
          obtain ⟨C, ⟨hC, hC2⟩⟩ := exists_circuit_subset_of_dep ((not_indep_iff _).1 hIyxn),
          have hyC : y ∈ C,
          { by_contra hyC,
            rw [singleton_union, subset_insert_iff_of_not_mem hyC] at hC,
            apply hC2.dep.not_indep (h2.subset (subset_trans hC (diff_subset _ _))) },
          rw ← series_pair_mem_circuit _ _ _ hC2 (series_extend_cocircuit hx hMx hy) at hyC,
          apply (not_mem_subset hC ((mem_union _ _ _).1.mt
            (not_or_distrib.2 ⟨mem_singleton_iff.1.mt (ne_of_mem_of_not_mem hx hy),
            not_mem_diff_singleton _ _⟩))) hyC,
          apply subset_trans (union_subset_union_right _ (diff_subset I {x})) hyI.subset_ground },
        have hyx := (hIxy.subset (subset_union_left _ _)).union_indep_iff_contract_indep.1 hIxy,
        rw [← contract_elem, series_extend_contract_eq M x y hy, ← φ.valid,
          linear_independent_comp_subtype] at hyx,
        rw [finset.erase_eq_of_not_mem hxl, finset.erase_eq_of_not_mem hyl] at hl0,
        apply hyx l ((l.mem_supported _).2
          (subset_diff_singleton (subset_diff_singleton ((l.mem_supported _).1 hl) hxl) hyl)) hl0.1,
      --apply hyx.subset_ground,
      rw series_extend_ground hx at hI ⊢,
      simp only [singleton_union, auto_param_eq],
      apply insert_subset.2 ⟨mem_insert _ _, hI⟩ } },
    end,
  support := λ e he,
    begin
      rw series_extend_ground hx at he,
      rw [if_neg, if_neg],
      simp only [linear_map.coe_inl, prod.mk_eq_zero, eq_self_iff_true, and_true],
      apply φ.support _ (not_mem_subset (subset_insert _ _) he),
      apply ne.symm (ne_of_mem_of_not_mem (mem_insert y _) he),
      apply ne.symm (ne_of_mem_of_not_mem (mem_insert_of_mem _ hx) he),
    end }

def rep_empty (𝔽 : Type*) [field 𝔽] (M : matroid_in α)
  (hM : M.E = ∅) : rep 𝔽 𝔽 M :=
{ to_fun := λ e, 0,
  valid' := λ I hI,
    begin
      rw [hM, subset_empty_iff] at hI,
      rw [hI, @linear_independent_image _ _ _ _ _ _ (∅ : set α) _ (inj_on_empty _),
          image_empty],
        simp only [empty_indep, linear_independent_empty 𝔽 𝔽, iff_true]
    end,
  support := λ e he, rfl }

def rep_singleton (𝔽 : Type*) [field 𝔽] (M : matroid_in α) {x : α} (hMx : M.E = {x}) :
  rep 𝔽 𝔽 M :=
{ to_fun := λ e, if hMx : M.nonloop x ∧ e = x then (1 : 𝔽) else (0 : 𝔽),
  valid' := λ I hI,
    begin
      rw hMx at *,
      cases ssubset_or_eq_of_subset hI with hIempty hIsing,
      { rw ssubset_singleton_iff.1 hIempty,
        rw [@linear_independent_image _ _ _ _ _ _ (∅ : set α) _ (inj_on_empty _),
          image_empty],
        simp only [empty_indep, linear_independent_empty 𝔽 𝔽, iff_true] },
      rw hIsing,
      by_cases M.loop x,
      { have hd : (λ (e : α), dite (M.nonloop x ∧ e = x) (λ (hMx : M.nonloop x ∧ e = x), (1 : 𝔽))
        (λ (hMx : ¬(M.nonloop x ∧ e = x)), (0 : 𝔽))) ∘ (coe : ({x} : set α) → α)
        = λ x : ({x} : set α), (0 : 𝔽),
          ext;
          simp only [dite_eq_iff],
          right,
          simp_rw not_and_distrib,
          refine ⟨(or.intro_left (¬↑x_1 = x)) h.not_nonloop, rfl⟩,
        rw [hd, ← not_iff_not],
        refine ⟨λ h2, h.dep.not_indep, λ h2, _⟩,
        by_contra,
        apply @linear_independent.ne_zero _ 𝔽 _ ((λ (e : α), (0 : 𝔽)) ∘ (coe : ({x} : set α) → α))
          _ _ _ _ ⟨x, mem_singleton x⟩ h,
        simp only },
      { have hd : (λ (e : α), dite (M.nonloop x ∧ e = x) (λ (hMx : M.nonloop x ∧ e = x), (1 : 𝔽))
        (λ (hMx : ¬(M.nonloop x ∧ e = x)), (0 : 𝔽))) ∘ (coe : ({x} : set α) → α)
        = λ x : ({x} : set α), (1 : 𝔽),
          ext;
          simp only [dite_eq_iff],
          left,
          have h2 := mem_singleton_iff.1 x_1.2,
          simp only [subtype.val_eq_coe] at h2,
          refine ⟨⟨(not_loop_iff (by {rw hMx, apply mem_singleton _})).1 h, h2⟩, rfl⟩,
        rw hd,
        refine ⟨λ h2, indep_singleton.2 ((not_loop_iff (by {rw hMx, apply mem_singleton _})).1 h),
          λ h2, _⟩,
        rw [@linear_independent_image _ _ _ _ _ _ ({x} : set α) (λ e : α, (1 : 𝔽))
          (inj_on_singleton _ _), image_singleton],
        apply linear_independent_singleton,
        simp only [ne.def, one_ne_zero, not_false_iff] },
    end,
  support := λ e he,
    begin
      simp only [dite_eq_iff],
      right,
      simp_rw not_and_distrib,
      rw [hMx, mem_singleton_iff] at he,
      refine ⟨(or.intro_right (¬ M.nonloop x)) he, rfl⟩,
    end }

variables [fintype α]

open_locale big_operators

lemma coindep_excluded_minor (M : matroid_in α)
(hM : excluded_minor {N : matroid_in α | N.is_representable 𝔽} M) (x y : α) (hxy : x ≠ y)
(hx : {x, y} ⊆ M.E)
  : M.coindep {x, y} :=
begin
  by_contra,
  rw coindep_iff_forall_subset_not_cocircuit at h,
  push_neg at h,
  obtain ⟨K, hK1, hK2⟩ := h,
  have h2 := (dual_circuit_iff_cocircuit.2 hK2).nonempty,
  cases ssubset_or_eq_of_subset hK1 with hKs hKeq,
  obtain ⟨a, ⟨ha1, ha2⟩⟩ := ssubset_iff_subset_diff_singleton.1 hKs,
  obtain ⟨rfl | h2⟩ := (mem_insert_iff.1 ha1),
  -- duplicate code
  -- use add_coloop_rep,
  { simp only [insert_diff_of_mem, mem_singleton, diff_singleton_eq_self
      (mem_singleton_iff.1.mt hxy), subset_singleton_iff_eq] at ha2,
    cases ha2 with hempty hs,
    { apply (nonempty_iff_ne_empty.1 h2) hempty },
    rw hs at *,
    rw [← ground_inter_left (subset_trans hK1 hx)] at h2,
    obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := hM.delete_mem h2,
    have hyMy : y ∉ (M ⟋ y).E,
      rw [contract_elem, contract_ground],
      apply not_mem_diff_of_mem (mem_singleton _),
    have φM := add_coloop_rep φ hyMy,
    simp only [excluded_minor, mem_minimals_prop_iff] at hM,
    apply hM.1,
    rw [contract_elem, contract_ground, ← delete_ground ] at hyMy,
    rw (add_coloop_eq (M ⟍ {y}) M hyMy).2 ⟨coloop_iff_cocircuit.2 hK2, delete_elem M y⟩,
    apply is_representable_of_rep φM, },
  { rw mem_singleton_iff.1 h at *,
    rw [← union_singleton, union_comm, union_singleton] at *,
    simp only [insert_diff_of_mem, mem_singleton, diff_singleton_eq_self
      (mem_singleton_iff.1.mt (ne.symm hxy)), subset_singleton_iff_eq] at ha2,
    cases ha2 with hempty hs,
    { apply (nonempty_iff_ne_empty.1 h2) hempty },
    rw hs at *,
    rw [← ground_inter_left (subset_trans hK1 hx)] at h2,
    obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := hM.delete_mem h2,
    have hyMy : x ∉ (M ⟋ x).E,
      rw [contract_elem, contract_ground],
      apply not_mem_diff_of_mem (mem_singleton _),
    have φM := add_coloop_rep φ hyMy,
    simp only [excluded_minor, mem_minimals_prop_iff] at hM,
    apply hM.1,
    rw [contract_elem, contract_ground, ← delete_ground] at hyMy,
    rw (add_coloop_eq (M ⟍ {x}) M hyMy).2 ⟨coloop_iff_cocircuit.2 hK2, delete_elem M x⟩,
    apply is_representable_of_rep φM },
  rw hKeq at *,
  have hyy := singleton_nonempty y,
  rw ← ground_inter_left (insert_subset.1 hx).2 at hyy,
  --rw [ground_inter_left _] at hyy,
  have h3 := hM.contract_mem hyy,
  obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := h3,
  rw ← M.contract_elem y at φ,
  have hxMy : x ∈ (M ⟋ y).E,
    rw [contract_elem, contract_ground],
    apply (mem_diff x).2,
    refine ⟨_, mem_singleton_iff.1.mt hxy⟩,
    apply mem_of_subset_of_mem hx,
    simp only [mem_insert_iff, eq_self_iff_true, true_or],
  have hyMy : y ∉ (M ⟋ y).E,
    rw [contract_elem, contract_ground],
    apply not_mem_diff_of_mem (mem_singleton _),
 --have hf := series_extend_eq (M ⟋ y) M hK2 hxMy rfl hyMy,
  simp only [excluded_minor, mem_minimals_prop_iff] at hM,
  apply hM.1,
  have hMx : ¬(M ⟋ y).coloop x,
    rw [contract_elem, coloop, contract_dual_eq_dual_delete, not_loop_iff, delete_nonloop_iff],
    rw [cocircuit, circuit_iff_dep_forall_diff_singleton_indep] at hK2,
    cases hK2 with hxy2 hin,
    specialize hin y (mem_insert_of_mem _ (mem_singleton y)),
    rw [insert_eq, union_comm, ← insert_eq, insert_diff_of_mem _ (mem_singleton _),
      diff_singleton_eq_self (mem_singleton_iff.1.mt (ne.symm hxy))] at hin,
    refine ⟨indep_singleton.1 hin, mem_singleton_iff.1.mt hxy⟩,
  rw [(eq_series_extend_iff hxMy hMx hyMy).2 ⟨hK2, rfl⟩, mem_set_of],
  obtain φM := series_extend_rep φ hxMy hyMy hMx,
  exact is_representable_of_rep φM,
end

lemma excluded_minor_nonloop (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor matroid_in.is_binary M) {f : α} (hf : f ∈ M.E) : M.nonloop f :=
begin
  by_contra,
  have hfM : ({f} ∩ M.E).nonempty,
    simp only [ground_inter_left, singleton_nonempty],
  obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := hM.delete_mem hfM,
  rw [excluded_minor, mem_minimals_prop_iff] at hM,
  simp only [not_nonloop_iff] at h,
  apply hM.1,
  apply is_representable_of_rep (rep_of_loop M h φ),
end

lemma excluded_minor_nonpara (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor matroid_in.is_binary M) {x y : α} (hxy : x ≠ y) :
  ¬ M.circuit {x, y}  :=
begin
  by_contra,
  have hfM : ({y} ∩ M.E).nonempty,
    simp only [singleton_inter_nonempty],
    apply mem_of_subset_of_mem h.subset_ground,
    simp only [mem_insert_iff, mem_singleton, or_true],
  obtain  ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := hM.delete_mem hfM,
  rw [excluded_minor, mem_minimals_prop_iff] at hM,
  apply hM.1,
  have hx : (M ⟍ y).nonloop x,
    rw [delete_elem, delete_nonloop_iff],
    rw circuit_iff_dep_forall_diff_singleton_indep at h,
    cases h with hxy2 hin,
    specialize hin y (mem_insert_of_mem _ (mem_singleton y)),
    rw [insert_eq, union_comm, ← insert_eq, insert_diff_of_mem _ (mem_singleton _),
      diff_singleton_eq_self (mem_singleton_iff.1.mt (ne.symm hxy))] at hin,
    refine ⟨indep_singleton.1 hin, mem_singleton_iff.1.mt hxy⟩,
  have hy : y ∉ (M ⟍ y).E,
    rw [delete_elem, delete_ground],
    apply not_mem_diff_singleton,
  obtain φM := parallel_extend_rep φ hx hy,
  simp_rw ← delete_elem at φM,
  rw ← (eq_parallel_extend_iff hx hy).2 ⟨h, rfl⟩ at φM,
  apply is_representable_of_rep (rep_of_congr (rep_of_matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
    (λ (e : α), ite (e = y) (-φ x) (φ e)) (insert y (M ⟍ y).E)) φM),
  --rw parallel_extend_eq,
end

lemma excluded_minor_simple (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor matroid_in.is_binary M) : simple M :=
begin
  intros e he f hf,
  rw indep_iff_forall_subset_not_circuit,
  intros C hC,
  by_cases hef : e = f,
  { rw hef at *,
    rw insert_eq_of_mem (mem_singleton f) at hC,
    cases ssubset_or_eq_of_subset hC with hempty heq,
    { rw ssubset_singleton_iff.1 hempty,
      apply empty_not_circuit },
    { rw heq,
      rw ← loop_iff_circuit,
      apply (excluded_minor_nonloop M hM hf).1 } },
  { cases ssubset_or_eq_of_subset hC with hC2 heq,
    { rw ssubset_iff_subset_diff_singleton at hC2,
      obtain ⟨x, ⟨hx1, hx2⟩⟩ := hC2,
      simp at hx1,
      obtain ⟨rfl | rfl⟩ := hx1,
      { simp at hx2,
        rw subset_diff at hx2,
        cases (subset_iff_ssubset_or_eq.1 hx2.1) with hempty heq,
        rw ssubset_singleton_iff.1 hempty,
        apply empty_not_circuit,
        rw heq,
        rw ← loop_iff_circuit,
        apply (excluded_minor_nonloop M hM hf).1 },
      { rw hx1 at *,
        rw [← union_singleton, union_comm, union_singleton] at hx2,
        simp at hx2,
        rw subset_diff at hx2,
        cases (subset_iff_ssubset_or_eq.1 hx2.1) with hempty heq,
        rw ssubset_singleton_iff.1 hempty,
        apply empty_not_circuit,
        rw [heq, ← loop_iff_circuit],
        apply (excluded_minor_nonloop M hM he).1 } },
    rw heq,
    apply excluded_minor_nonpara M hM hef },
  apply insert_subset.2 ⟨he, singleton_subset_iff.2 hf⟩,
end

-- should be an instance but i can't figure it out rn
lemma nontrivial_excluded_minor (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor matroid_in.is_binary M) : nontrivial M.E :=
begin
  by_contra,
  simp only [nontrivial_coe_sort, not_nontrivial_iff] at h,
  rw [excluded_minor, mem_minimals_prop_iff] at hM,
  apply hM.1,
  cases h.eq_empty_or_singleton with hempty hsing,
  { apply is_representable_of_rep (rep_empty (zmod 2) M hempty) },
  { obtain ⟨x, hx⟩ := hsing,
    apply is_representable_of_rep (rep_singleton (zmod 2) M hx) },
end

lemma excluded_minor_binary_unif (hM : excluded_minor matroid_in.is_binary M)
  (ψ : M ≃i unif 2 M.E.ncard) (h2 : 2 ≤ M.E.ncard) : 4 ≤ M.E.ncard :=
begin
  rw [excluded_minor, mem_minimals_prop_iff] at hM,
  rw le_iff_eq_or_lt at h2,
  cases h2 with h2 h3,
  { by_contra,
    apply hM.1,
    rw ← h2 at ψ,
    obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := U22_binary,
    apply is_representable_of_rep (iso.rep _ _ ψ φ) },
  { have h2 := nat.add_one_le_iff.2 h3,
    rw le_iff_eq_or_lt at h2,
    cases h2 with h2 h3,
    { by_contra,
      apply hM.1,
      rw ← h2 at ψ,
      obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := U23_binary,
      apply is_representable_of_rep (iso.rep _ _ ψ φ) },
    { apply nat.add_one_le_iff.2 h3 } },
end

lemma excluded_minor_binary_rk2 (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor (set_of matroid_in.is_binary) M) : M.rk = 2 :=
begin
  haveI hME := nontrivial_excluded_minor M hM,
  rw [nontrivial_coe_sort, nontrivial_iff_pair_subset] at hME,
  obtain ⟨x, ⟨y, ⟨hxy1, hxy2⟩⟩⟩ := hME,
  have h2 := coindep_excluded_minor M hM x y hxy1 hxy2,

  have hxyr : matroid_in.is_binary (M ⟍ ({x, y} : set α)),
    apply excluded_minor.delete_mem hM,
    rw ground_inter_left,
    apply insert_nonempty,

  obtain ⟨B, ⟨hBxy, ⟨φ⟩⟩⟩ := hxyr,

  obtain ⟨Bx, ⟨hBx, ⟨φx⟩⟩⟩ := (((excluded_minor_iff _ (@minor_closed_rep _ (zmod 2) _)).1 hM).2 x
    (hxy2 (mem_union_left {y} (mem_singleton x)))).2,

  obtain ⟨By, ⟨hBy, ⟨φy⟩⟩⟩ := (((excluded_minor_iff _ (@minor_closed_rep _ (zmod 2) _)).1 hM).2 y
    (hxy2 (mem_union_right {x} (mem_singleton y)))).2,

  have hB := coindep.base_of_basis_del h2 (delete_base_iff.1 hBxy),

  have hBy : (M ⟍ y).base B,
    rw [delete_elem, delete_base_iff],
    apply hB.basis_of_subset _,
    apply subset.trans,
    apply hBxy.subset_ground,
    rw [delete_ground, ← union_singleton, union_comm, ← diff_diff],
    apply diff_subset_diff_left (diff_subset _ _),
    apply diff_subset M.E ({y} : set α),

  have hBx : (M ⟍ x).base B,
    rw [delete_elem, delete_base_iff],
    apply hB.basis_of_subset _,
    apply subset.trans,
    apply hBxy.subset_ground,
    rw [delete_ground, ← union_singleton, ← diff_diff],
    apply diff_subset_diff_left (diff_subset _ _),
    apply diff_subset M.E ({x} : set α),

  have hMM'E : M.E = (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E).E,
    rw matroid_of_module_fun.ground,
  have hMM'x := delete_elem_eq_of_binary hBxy hBx hB φ φx,
  have hByx := hBxy,
  have hxyyx : M ⟍ {x, y} = M ⟍ {y, x},
    rw [← union_singleton, union_comm, union_singleton],
  rw [← union_singleton, union_comm, union_singleton] at hByx,
  have hMM'y := delete_elem_eq_of_binary hByx hBy hB (rep_of_congr φ hxyyx) φy,
  have hφ : ∀ (a : α), ((rep_of_congr φ hxyyx).standard_rep hByx) a = (φ.standard_rep hBxy) a,
  { intros a,
    rw φ.standard_rep_eq_of_congr hxyyx },
  simp_rw [λ (a : α), hφ a] at hMM'y,
  have hB' : (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E).base B,
  { rw hMM'x at hBx,
    rw hMM'y at hBy,
    rw [base_iff_basis_ground, ← @diff_empty _ (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E).E,
      ← singleton_inter_eq_empty.2 (mem_singleton_iff.1.mt hxy1), diff_inter],
    rw [delete_elem, delete_base_iff] at hBx hBy,
    apply basis.basis_union hBx hBy },
  have hMM'r : M.rk = (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E).rk,
  { rw [← hB'.card, hB.card] },
  have hnxy : ({x, y} : set α).ncard = 2,
    { rw ncard_eq_to_finset_card,
      simp only [finite.to_finset_insert, finite.to_finset_singleton],
      apply finset.card_insert_of_not_mem (finset.not_mem_singleton.2 hxy1) },
  have hMM' : M ≠ (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
    (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E),
    { by_contra,
      rw [excluded_minor, mem_minimals_prop_iff] at hM,
      apply hM.1,
      rw [h, mem_def],
      apply is_representable_of_rep (rep_of_matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
        (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E) },
    rw [ne.def, eq_iff_indep_iff_indep_forall, matroid_of_module_fun.ground] at hMM',
    simp only [eq_self_iff_true, true_and, not_forall, exists_prop] at hMM',
    obtain ⟨Z, ⟨hZM, hZ⟩⟩ := hMM',
    rw [iff_def, not_and_distrib] at hZ,
    push_neg at hZ,
    cases hZ with hMZ hM'Z,
    { have hJZ : ∀ (J : set α), M.indep J → Z ⊆ J → J = {x, y},
      { intros J hMJ hZJ,
        -- duplicate code
        have hZx : x ∈ Z,
          { by_contra,
            have hZs : (M ⟍ x).indep Z,
            { rw [delete_elem, delete_indep_iff],
              refine ⟨hMZ.1, disjoint_singleton_right.2 h⟩ },
            rw [hMM'x, delete_elem] at hZs,
            apply hMZ.2 hZs.of_delete },
        have hZy : y ∈ Z,
          { by_contra,
            have hZs : (M ⟍ y).indep Z,
            { rw [delete_elem, delete_indep_iff],
              refine ⟨hMZ.1, disjoint_singleton_right.2 h⟩ },
            rw [hMM'y, delete_elem] at hZs,
            apply hMZ.2 hZs.of_delete },
        have hZxy := union_subset (singleton_subset_iff.2 hZy) (singleton_subset_iff.2 hZx),
        rw union_singleton at hZxy,
        by_contra,
        have hJxyM : ((J \ {x, y}) ∩ M.E).nonempty,
        { simp only [ground_inter_left],
          apply nonempty_iff_ne_empty.2,
          apply diff_eq_empty.1.mt,
          by_contra h2,
          apply h (eq_of_subset_of_subset h2 (subset_trans hZxy hZJ)) },
        obtain ⟨BN, ⟨hBN, ⟨φN⟩⟩⟩ := hM.contract_mem hJxyM,
        have φN' := rep_of_contr _ (rep_of_matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
          (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E) (J \ {x, y})
          (by { rw matroid_of_module_fun.ground, apply subset_trans (diff_subset _ _)
          hMJ.subset_ground }),
        apply h (indep_eq_doubleton_of_subset M (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
          (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E) hMM'r hMM'E
          x y hxy1 (by { left, apply h2 }) hMM'x hMM'y hZx hZy hMZ.1 hMZ.2 hZJ hMJ φN φN') },
      obtain ⟨BZ, hBZ⟩ := hMZ.1,
      specialize hJZ BZ hBZ.1.indep hBZ.2,
      rw hJZ at *,
      rw [← hBZ.1.card, hnxy] },
  { have hJZ : ∀ (J : set α), (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
      (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E).indep J
      → Z ⊆ J → J = {x, y},
    { intros J hMJ hZJ,
      have hZx : x ∈ Z,
        { by_contra,
        have hZs : ((matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
          (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset,
          (standard_rep φ hBxy) i) M.E) ⟍ x).indep Z,
        { rw [delete_elem, delete_indep_iff],
          refine ⟨hM'Z.1, disjoint_singleton_right.2 h⟩ },
        rw [← hMM'x, delete_elem] at hZs,
        apply hM'Z.2 hZs.of_delete },
      have hZy : y ∈ Z,
        { by_contra,
          have hZs : ((matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
            (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset,
            (standard_rep φ hBxy) i) M.E) ⟍ y).indep Z,
          { rw [delete_elem, delete_indep_iff],
            refine ⟨hM'Z.1, disjoint_singleton_right.2 h⟩ },
          rw [← hMM'y, delete_elem] at hZs,
          apply hM'Z.2 hZs.of_delete },
      have hZxy := union_subset (singleton_subset_iff.2 hZy) (singleton_subset_iff.2 hZx),
      rw union_singleton at hZxy,
      by_contra,
      have hJxyM' : ((J \ {x, y}) ∩ (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
            (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset,
            (standard_rep φ hBxy) i) M.E).E).nonempty,
      { simp only [ground_inter_left],
        apply nonempty_iff_ne_empty.2,
        apply diff_eq_empty.1.mt,
        by_contra h2,
        apply h (eq_of_subset_of_subset h2 (subset_trans hZxy hZJ)) },
      obtain ⟨BN, ⟨hBN, ⟨φN⟩⟩⟩ := hM.contract_mem hJxyM',
      have φN' := rep_of_contr _ (rep_of_matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
        (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E) (J \ {x, y})
        (by { rw matroid_of_module_fun.ground, apply subset_trans (diff_subset _ _)
        hMJ.subset_ground }),
      apply h (indep_eq_doubleton_of_subset (matroid_of_module_fun (zmod 2) (B →₀ zmod 2)
        (λ e : α, ∑ i in (M.fund_circuit e B ∩ B).to_finset, (standard_rep φ hBxy) i) M.E) M
        (eq.symm hMM'r) (eq.symm hMM'E) x y hxy1 (by { right, apply h2 }) (eq.symm hMM'x)
        (eq.symm hMM'y) hZx hZy hM'Z.1 hM'Z.2 hZJ hMJ φN' φN) },
    obtain ⟨BZ, hBZ⟩ := hM'Z.1,
    specialize hJZ BZ hBZ.1.indep hBZ.2,
    rw hJZ at *,
    rw [hMM'r, ← hBZ.1.card, hnxy] },
end

lemma excluded_minor_binary_ncard (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor (set_of matroid_in.is_binary) M) : 2 ≤ M.E.ncard :=
by { rw [← excluded_minor_binary_rk2 M hM, rk_def], apply r_le_card }

lemma excluded_minor_binary (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor (set_of matroid_in.is_binary) M) : unif 2 4 ≤i M :=
begin
  obtain ⟨ψ⟩ := (iso_line_iff (excluded_minor_binary_ncard M hM)).2 ⟨excluded_minor_simple M hM,
    ⟨excluded_minor_binary_rk2 M hM, ⟨to_finite M.E, rfl⟩⟩⟩,
  apply iso_minor.trans (unif_iso_minor (excluded_minor_binary_unif hM ψ
    (excluded_minor_binary_ncard M hM))) (ψ.symm.trans_iso_minor (minor.refl.iso_minor)),
end

lemma excluded_minor_binary_iso_unif (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor (set_of matroid_in.is_binary) M) : nonempty (M ≃i (unif 2 M.E.ncard)) :=
(iso_line_iff (excluded_minor_binary_ncard M hM)).2 ⟨excluded_minor_simple M hM,
⟨excluded_minor_binary_rk2 M hM, ⟨to_finite M.E, rfl⟩⟩⟩

lemma excluded_minor_binary_ncard4 (hM : excluded_minor matroid_in.is_binary M) : 4 = M.E.ncard :=
begin
  obtain ⟨ψ⟩ := excluded_minor_binary_iso_unif M hM,
  have h3 := excluded_minor_binary_unif hM ψ (excluded_minor_binary_ncard M hM),
  rw le_iff_eq_or_lt at h3,
  cases h3 with h3 h4,
  { apply h3 },
  { by_contra,
    obtain ⟨ψ2⟩ := (iso_line_iff (excluded_minor_binary_ncard M hM)).2 ⟨excluded_minor_simple M hM, ⟨excluded_minor_binary_rk2 M hM,
      ⟨to_finite M.E, rfl⟩⟩⟩,
    have h4 := (excluded_minor_iff matroid_in.is_binary (@minor_closed_rep _ (zmod 2) _)).1 hM,
    have h5 := iso_minor.trans (@unif_iso_minor _ _ 2 (excluded_minor_binary_unif hM ψ2
      (excluded_minor_binary_ncard M hM))) (ψ2.symm.iso_minor),
    rw iso_minor at h5,
    obtain ⟨M', ⟨hM'M, ⟨g⟩⟩⟩ := h5,
    have h8 := ncard_le_of_subset hM'M.ground_subset,
    rw le_iff_eq_or_lt at h8,
    cases h8 with hcontra hlt,
    { rw ncard_eq_to_finset_card M.E at hcontra,
      have h9 := (fintype.bijective_iff_injective_and_card ψ2).1 ψ2.bijective,
      apply h,
      rw [← to_finset_card, ← finite.to_finset_eq_to_finset, ← ncard_eq_to_finset_card M.E] at h9,
      rw h9.2,
      have h10 := (fintype.bijective_iff_injective_and_card g).1 g.bijective,
      rw [← to_finset_card M'.E, ← finite.to_finset_eq_to_finset,
        ← ncard_eq_to_finset_card M'.E] at h10,
      rw [← ncard_eq_to_finset_card M.E] at hcontra,
      rw [← hcontra, ← h10.2, unif_ground_eq, ← to_finset_card univ, to_finset_univ,
        finset.card_univ, fintype.card_fin, unif_ground_eq, ← to_finset_card univ, to_finset_univ,
        finset.card_univ, fintype.card_fin] },
    { obtain ⟨e, ⟨heM, heM'⟩⟩ := exists_mem_not_mem_of_ncard_lt_ncard hlt,
      have h7 := hM'M.minor_contract_or_minor_delete ((mem_diff e).2 ⟨heM, heM'⟩),
      apply U24_nonbinary,
      cases h7 with hMe hMe,
      { obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := is_rep_of_minor_of_is_rep _ hMe (h4.2 e heM).1,
        apply is_representable_of_rep (iso.rep _ _ g φ) },
      { obtain ⟨B, ⟨hB, ⟨φ⟩⟩⟩ := is_rep_of_minor_of_is_rep _ hMe (h4.2 e heM).2,
        apply is_representable_of_rep (iso.rep _ _ g φ) } } },
end

lemma excluded_minor_binary_iso_unif24 (M : matroid_in α) [finite_rk M]
  (hM : excluded_minor (set_of matroid_in.is_binary) M) : nonempty (M ≃i (unif 2 4)) :=
by { rw excluded_minor_binary_ncard4 hM, apply excluded_minor_binary_iso_unif M hM }

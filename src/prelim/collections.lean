import .size .induction 
----------------------------------------------------------------
open_locale classical 
open_locale big_operators 
noncomputable theory 


open set 
-- The operations needed on the ftype A.

variables {A: Type}[fintype A]


def is_lb (P : set A → Prop) (X : set A) : Prop := ∀ Y, P Y → X ⊆ Y 
def is_ub (P : set A → Prop) (X : set A) : Prop := ∀ Y, P Y → Y ⊆ X

def down_closed (P : set A → Prop) : Prop := ∀ X Y, X ⊆ Y → P Y → P X
def up_closed (P : set A → Prop) : Prop := ∀ X Y, X ⊆ Y → P X → P Y

def is_minimal (P : set A → Prop) (X : set A) : Prop := P X ∧ ∀ Y, (Y ⊂ X → ¬ P Y)
def is_maximal (P : set A → Prop) (X : set A) : Prop := P X ∧ ∀ Y, (X ⊂ Y → ¬ P Y)

lemma max_iff_compl_min (P : set A → Prop) (X : set A) :
  is_maximal P X ↔ is_minimal (λ Z, P Zᶜ) Xᶜ :=
begin 
  refine ⟨λ h, ⟨by {rw ←compl_compl X at h, exact h.1},λ Y hY, _⟩, λ h, ⟨by {rw ←compl_compl X, exact h.1},λ Y hY, _⟩⟩, 
  exact h.2 _ (scompl_subset_comm.mpr hY), rw ←compl_compl Y, exact h.2 _ (scompl_subset_compl.mpr hY), 
end

lemma down_closed_iff_negation_up_closed (P : set A → Prop) : 
  down_closed P ↔ up_closed (λ X, ¬P X) := 
by {unfold down_closed up_closed, simp_rw not_imp_not}

lemma contains_min {P : set A → Prop} {X : set A}:
  P X → ∃ Y, Y ⊆ X ∧ is_minimal P Y := 
minimal_example P 

lemma max_contains {P : set A → Prop} {X : set A}:
  P X → ∃ Y, X ⊆ Y ∧ is_maximal P Y :=  
maximal_example P  
 
-- Union/Intersection-closed collections of sets

def union_closed (P : set A → Prop) : Prop := P ∅ ∧ ∀ X Y, P X → P Y → P (X ∪ Y)
def inter_closed (P : set A → Prop) : Prop := P univ ∧ ∀ X Y, P X → P Y → P (X ∩ Y)

lemma union_closed_iff_compl_inter_closed (P : set A → Prop) : 
  union_closed P ↔ inter_closed (λ X, P Xᶜ) := 
begin
  refine ⟨λ h, ⟨by {rw compl_univ, exact h.1},λ X Y hX hY, _⟩, λ h,⟨by {rw ←compl_univ, exact h.1},λ X Y hX hY,_⟩ ⟩,  
  rw compl_inter, exact h.2 _ _ hX hY, 
  rw [←compl_compl (X ∪ Y), compl_union], rw ←compl_compl X at hX, rw ←compl_compl Y at hY, exact h.2 _ _ hX hY,
end 

lemma inter_closed_exists_min (P : set A → Prop) : 
  inter_closed P → ∃ X, is_minimal P X :=  
λ h, by {cases (contains_min h.1) with Y, use Y, exact h_1.2}

lemma inter_closed_min_unique (P : set A → Prop) : 
  inter_closed P → ∀ X₁ X₂, is_minimal P X₁ → is_minimal P X₂ → X₁ = X₂ := 
by {intros hP _ _ h₁ h₂, replace hP := hP.2 _ _ h₁.1 h₂.1, by_contra a, 
    cases ssubset_inter a, exact (h₁.2 _ h) hP, exact (h₂.2 _ h) hP} 

lemma inter_closed_min_iff_in_and_lb {P : set A → Prop}(hP : inter_closed P) (X : set A):
  is_minimal P X ↔ P X ∧ is_lb P X := 
  begin
    refine ⟨λ h, ⟨h.1, λ Z pZ,_⟩, λ h,⟨h.1, λ Y hY hPY, _⟩⟩, 
    by_contra a, rw subset_iff_union at a, refine  h.2 _ _ (hP.2 _ _ pZ h.1), 
    rw [←subset_iff_union, subset_iff_inter, inter_comm] at a, 
    exact ssubset_of_subset_ne (inter_subset_right _ _) a, 
    exact ssubset_not_supset hY (h.2 _ hPY), 
  end

lemma union_closed_exists_max (P : set A → Prop) : 
  union_closed P → ∃ X, is_maximal P X :=  
  λ h, by {cases (max_contains h.1) with Y, use Y, exact h_1.2}

lemma union_closed_max_unique (P : set A → Prop) : 
  union_closed P → ∀ X₁ X₂, is_maximal P X₁ → is_maximal P X₂ → X₁ = X₂ := 
  begin
    rw [union_closed_iff_compl_inter_closed], simp_rw [max_iff_compl_min], refine λ h X₁ X₂ h₁ h₂,_ ,
    rw [←compl_compl X₁, ←compl_compl X₂, inter_closed_min_unique _ h _ _ h₁ h₂],
  end 

lemma union_closed_max_iff_in_and_ub {P : set A → Prop}(hP : union_closed P) (X : set A):
  is_maximal P X ↔ P X ∧ is_ub P X := 
  begin
    refine ⟨λ h, ⟨h.1, λ Z pZ,_⟩, λ h,⟨h.1, λ Y hY hPY, _⟩⟩, 
    by_contra a, rw subset_iff_union at a, refine  h.2 _ _ (hP.2 _ _ pZ h.1), 
    exact ssubset_of_subset_ne (subset_union_right _ _) (ne.symm a), 
    exact ssubset_not_supset hY (h.2 _ hPY), 
  end

def min_of_inter_closed {P : set A → Prop} (h : inter_closed P) : set A := 
  classical.some (inter_closed_exists_min P h) 

def max_of_union_closed {P : set A → Prop} (h : union_closed P) : set A := 
  classical.some (union_closed_exists_max P h) 

lemma min_of_inter_closed_in {P : set A → Prop}(h : inter_closed P) :
  P (min_of_inter_closed h) := 
  (classical.some_spec (inter_closed_exists_min P h)).1 

lemma min_of_inter_closed_is_lb {P : set A → Prop}(h : inter_closed P): 
  is_lb P (min_of_inter_closed h) :=
  begin
    intros X hX, rcases contains_min hX with ⟨Y, ⟨hY₁, hY₂⟩⟩,  
    rw inter_closed_min_unique P h _ _  hY₂ ((classical.some_spec (inter_closed_exists_min P h))) at hY₁, exact hY₁,
  end

/-lemma min_of_inter_closed_is_min {P : set A → Prop}(h : inter_closed P) : 
  is_minimal P (min_of_inter_closed h) :=
  (classical.some_spec (inter_closed_exists_min P h))-/

lemma is_min_of_inter_closed {P : set A → Prop}(h : inter_closed P) {X : set A}:
  P X → is_lb P X → X = min_of_inter_closed h := 
begin
  intros hX hlb, 
  refine inter_closed_min_unique P h X (min_of_inter_closed h) ⟨hX,λ Y hY hPY, _⟩ ⟨_,λ Y hY hPY,_⟩,
  exact ssubset_not_supset hY (hlb Y hPY),     
  exact min_of_inter_closed_in h, 
  refine ssubset_not_supset (subset.lt_of_le_of_lt (hlb _ hPY) hY ) _, 
  exact (min_of_inter_closed_is_lb h) _ hX,
end

lemma is_min_of_inter_closed_iff {P : set A → Prop}(hic : inter_closed P) (X : set A):
  X = min_of_inter_closed hic ↔ P X ∧ is_lb P X := 
begin
  refine ⟨λ h, _, λ h, is_min_of_inter_closed hic h.1 h.2 ⟩ , 
  rw h, exact ⟨min_of_inter_closed_in hic, min_of_inter_closed_is_lb hic⟩,
end

lemma max_of_union_closed_in {P : set A → Prop} (h : union_closed P) : 
  P (max_of_union_closed h) := 
  (classical.some_spec (union_closed_exists_max P h)).1 

lemma max_of_union_closed_is_ub {P : set A → Prop}(h : union_closed P) : 
  is_ub P (max_of_union_closed h) :=
begin
  intros X hX, rcases max_contains hX with ⟨Y, ⟨hY₁, hY₂⟩⟩,  
  rw union_closed_max_unique P h _ _  hY₂ ((classical.some_spec (union_closed_exists_max P h))) at hY₁, exact hY₁ 
end

lemma is_max_of_union_closed {P : set A → Prop}(h : union_closed P) {X : set A}:
  P X → is_ub P X → X = max_of_union_closed h := 
begin
  intros hX hub, 
  refine union_closed_max_unique P h X (max_of_union_closed h) ⟨hX,λ Y hY hPY, _⟩ ⟨_,λ Y hY hPY,_⟩,
  exact ssubset_not_supset hY (hub Y hPY), 
  exact max_of_union_closed_in h, 
  refine ssubset_not_supset (subset.lt_of_lt_of_le hY (hub _ hPY)) _, 
  exact (max_of_union_closed_is_ub h) _ hX,
end

lemma is_max_of_union_closed_iff {P : set A → Prop}(huc : union_closed P) (X : set A):
  X = max_of_union_closed huc ↔ P X ∧ is_ub P X := 
begin
  refine ⟨λ h, _, λ h, is_max_of_union_closed huc h.1 h.2 ⟩ , 
  rw h, exact ⟨max_of_union_closed_in huc, max_of_union_closed_is_ub huc⟩,
end



--- Unions/Intersections of collections
lemma lb_union_closed (P : set A → Prop) : 
  union_closed (λ X, is_lb P X) := 
  ⟨λ Z hZ, empty_subset Z, λ X Y hX hY, λ Z hZ, union_of_subsets (hX Z hZ) (hY Z hZ)⟩

lemma ub_inter_closed (P : set A → Prop) : 
  inter_closed (λ X, is_ub P X) := 
  ⟨λ Z hZ, subset_univ Z, λ X Y hX hY, λ Z hZ, subset_of_inter_mpr (hX Z hZ) (hY Z hZ)⟩


def inter_all (P : set A → Prop) : set A := max_of_union_closed (lb_union_closed P)

def union_all (P : set A → Prop) : set A := min_of_inter_closed (ub_inter_closed P)

lemma subset_inter_all_iff (P : set A → Prop) (X : set A):
  X ⊆ inter_all P ↔ is_lb P X :=
  begin
    refine ⟨λ h, λ Y hY, _ , λ h, max_of_union_closed_is_ub (lb_union_closed P) _ h ⟩,
    exact subset.trans h (max_of_union_closed_in (lb_union_closed P) Y hY), 
  end

lemma union_all_subset_iff (P : set A → Prop) (X : set A): 
  union_all P ⊆ X ↔ is_ub P X := 
  begin
    refine ⟨λ h, λ Y hY, _ , λ h, min_of_inter_closed_is_lb (ub_inter_closed P) _ h ⟩,
    exact subset.trans (min_of_inter_closed_in (ub_inter_closed P) Y hY) h,  
  end

lemma union_all_ub (P : set A → Prop):
  is_ub P (union_all P) :=
  (union_all_subset_iff P _).mp (subset_refl _ )
  
section size 

lemma has_subset_of_size {X : set A}{n : ℤ}:
  0 ≤ n → n ≤ size X → ∃ Y, Y ⊆ X ∧ size Y = n :=
let P := λ Y, Y ⊆ X ∧ size Y ≤ n in 
begin
  intros hn hnX, 
  rcases maximal_example_aug P (⟨empty_subset X, by linarith [size_empty A]⟩ : P ∅) with ⟨Y, ⟨_,⟨⟨h₁,h₂⟩, h₃⟩⟩⟩, 
  refine ⟨Y, ⟨h₁,_⟩⟩, 
  cases subset_ssubset_or_eq h₁, 
  by_contra a, 
  rcases elem_only_larger_ssubset h with ⟨e, ⟨h₁e, h₂e⟩⟩, 
  push_neg at h₃, 
  --rw elem_iff at h₁e, 
  from a (by linarith [add_nonmem_size h₂e, h₃ e h₂e (union_of_subsets h₁ (singleton_subset_iff.mpr h₁e ))]), 
  rw h at h₂ ⊢, 
  linarith, 
end

section fin_sum

variables {α β : Type}[fintype α][add_comm_monoid β](f : α → β)

lemma set.to_finset_insert' (X : set α)(e : α) : 
  (X ∪ {e}).to_finset = X.to_finset ∪ {e} :=
by {ext, simp[or_comm]}  


lemma fin_sum_empty : 
  ∑ (a : (∅ : set α)), f a = 0 :=  
by convert finset.sum_empty 

lemma fin_sum_eq (X : set α): 
  ∑ (a : X), f a = ∑ a in X.to_finset, f a := 
let φ : X ↪ α := ⟨coe, subtype.coe_injective⟩ in (finset.sum_map (finset.univ) φ f).symm

#check finset.sum_union 

--set_option pp.notation false
lemma fin_sum_insert {α β : Type}[fintype α][add_comm_monoid β](f : α → β){X : set α}{e : α}: 
  e ∉ X → ∑ (a : X ∪ {e}), f a = (∑ (a : X), f a) + f e :=
begin
  intro he, 
  set X' := X.to_finset with hX', 
  have he' : e ∉ X' := by rwa [hX', mem_to_finset],  
  convert (@fin_sum_eq _ _ _ _ f (X ∪ {e} : set α)), 
  have hX : X.finite := finite.of_fintype X, 
  -- fintype instance mismatches happening here. 
  have := (set.to_finset_insert' X e), 
  rw [eq_comm, fin_sum_eq], 
  --calc (X ∪ {e}).to_finset.sum f
  calc 
      _ = (X.to_finset ∪ {e}).sum f                  : by {congr', convert this}
    ... = X.to_finset.sum f + ({e} : finset α).sum f : finset.sum_union (by {sorry} : disjoint X.to_finset {e}) 
    ... = X.to_finset.sum f + f e                    : (sorry : ({e} : finset α).sum f = f e)
    ... = _ : sorry, 
  --suffices : f e + Σ (a : X) f a = (X.to_finset ∪ {e}).sum f, 
  
  --have := @finset.sum_insert α β _ _ f _ _ he',  
  
  --simp_rw ←union_singleton at this, 
end

end fin_sum

end size 

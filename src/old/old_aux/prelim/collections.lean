import .size .induction_size algebra.big_operators.order finsum.fin_api .embed
----------------------------------------------------------------
open_locale classical 
open_locale big_operators 
noncomputable theory 

universes u v w

open set 

section extrema 
variables {α: Type*} [fintype α]


def is_lb (P : set α → Prop) (X : set α) : Prop := ∀ Y, P Y → X ⊆ Y 
def is_ub (P : set α → Prop) (X : set α) : Prop := ∀ Y, P Y → Y ⊆ X

def down_closed (P : set α → Prop) : Prop := ∀ X Y, X ⊆ Y → P Y → P X
def up_closed (P : set α → Prop) : Prop := ∀ X Y, X ⊆ Y → P X → P Y

def is_minimal (P : set α → Prop) (X : set α) : Prop := P X ∧ ∀ Y, (Y ⊂ X → ¬ P Y)
def is_maximal (P : set α → Prop) (X : set α) : Prop := P X ∧ ∀ Y, (X ⊂ Y → ¬ P Y)

lemma max_iff_compl_min (P : set α → Prop) (X : set α) :
  is_maximal P X ↔ is_minimal (λ Z, P Zᶜ) Xᶜ :=
begin 
  refine ⟨λ h, ⟨by {rw ←compl_compl X at h, exact h.1},λ Y hY, _⟩, 
          λ h, ⟨by {rw ←compl_compl X, exact h.1},λ Y hY, _⟩⟩, 
  exact h.2 _ (ssubset_compl_comm.mpr hY), rw ←compl_compl Y, 
  exact h.2 _ (compl_ssubset_compl_iff.mpr hY), 
end

lemma down_closed_iff_negation_up_closed (P : set α → Prop) : 
  down_closed P ↔ up_closed (λ X, ¬P X) := 
by {unfold down_closed up_closed, simp_rw not_imp_not}

lemma contains_min {P : set α → Prop} {X : set α} :
  P X → ∃ Y, Y ⊆ X ∧ is_minimal P Y := 
minimal_example P 

lemma max_contains {P : set α → Prop} {X : set α} :
  P X → ∃ Y, X ⊆ Y ∧ is_maximal P Y :=  
maximal_example P  
 
-- Union/Intersection-closed collections of sets

def union_closed (P : set α → Prop) : Prop := P ∅ ∧ ∀ X Y, P X → P Y → P (X ∪ Y)
def inter_closed (P : set α → Prop) : Prop := P univ ∧ ∀ X Y, P X → P Y → P (X ∩ Y)

lemma union_closed_iff_compl_inter_closed (P : set α → Prop) : 
  union_closed P ↔ inter_closed (λ X, P Xᶜ) := 
begin
  refine ⟨λ h, ⟨by {rw compl_univ, exact h.1},λ X Y hX hY, _⟩, 
          λ h,⟨by {rw ←compl_univ, exact h.1},λ X Y hX hY,_⟩ ⟩,  
  rw compl_inter, exact h.2 _ _ hX hY, 
  rw [←compl_compl (X ∪ Y), compl_union], 
  rw ←compl_compl X at hX, 
  rw ←compl_compl Y at hY, 
  exact h.2 _ _ hX hY,
end 

lemma inter_closed_exists_min (P : set α → Prop) : 
  inter_closed P → ∃ X, is_minimal P X :=  
λ h, by {cases (contains_min h.1) with Y, use Y, exact h_1.2}

lemma inter_closed_min_unique (P : set α → Prop) : 
  inter_closed P → ∀ X₁ X₂, is_minimal P X₁ → is_minimal P X₂ → X₁ = X₂ := 
by {intros hP _ _ h₁ h₂, replace hP := hP.2 _ _ h₁.1 h₂.1, by_contra a, 
    cases ssubset_inter a, exact (h₁.2 _ h) hP, exact (h₂.2 _ h) hP} 

lemma inter_closed_min_iff_in_and_lb {P : set α → Prop} (hP : inter_closed P) (X : set α) :
  is_minimal P X ↔ P X ∧ is_lb P X := 
  begin
    refine ⟨λ h, ⟨h.1, λ Z pZ,_⟩, λ h,⟨h.1, λ Y hY hPY, _⟩⟩, 
    by_contra a, rw subset_iff_union_eq_left at a, refine  h.2 _ _ (hP.2 _ _ pZ h.1), 
    rw [←subset_iff_union_eq_left, subset_iff_inter_eq_left, inter_comm] at a, 
    exact ssubset_of_subset_ne (inter_subset_right _ _) a, 
    exact ssubset_not_supset hY (h.2 _ hPY), 
  end

lemma union_closed_exists_max (P : set α → Prop) : 
  union_closed P → ∃ X, is_maximal P X :=  
  λ h, by {cases (max_contains h.1) with Y, use Y, exact h_1.2}

lemma union_closed_max_unique (P : set α → Prop) : 
  union_closed P → ∀ X₁ X₂, is_maximal P X₁ → is_maximal P X₂ → X₁ = X₂ := 
  begin
    rw [union_closed_iff_compl_inter_closed], 
    simp_rw [max_iff_compl_min], 
    refine λ h X₁ X₂ h₁ h₂,_ ,
    rw [←compl_compl X₁, ←compl_compl X₂, inter_closed_min_unique _ h _ _ h₁ h₂],
  end 

lemma union_closed_max_iff_in_and_ub {P : set α → Prop} (hP : union_closed P) (X : set α) :
  is_maximal P X ↔ P X ∧ is_ub P X := 
  begin
    refine ⟨λ h, ⟨h.1, λ Z pZ,_⟩, λ h,⟨h.1, λ Y hY hPY, _⟩⟩, 
    by_contra a, rw subset_iff_union_eq_left at a, refine  h.2 _ _ (hP.2 _ _ pZ h.1), 
    exact ssubset_of_subset_ne (subset_union_right _ _) (ne.symm a), 
    exact ssubset_not_supset hY (h.2 _ hPY), 
  end

def min_of_inter_closed {P : set α → Prop} (h : inter_closed P) : set α := 
  classical.some (inter_closed_exists_min P h) 

def max_of_union_closed {P : set α → Prop} (h : union_closed P) : set α := 
  classical.some (union_closed_exists_max P h) 

lemma min_of_inter_closed_in {P : set α → Prop} (h : inter_closed P) :
  P (min_of_inter_closed h) := 
  (classical.some_spec (inter_closed_exists_min P h)).1 

lemma min_of_inter_closed_is_lb {P : set α → Prop} (h : inter_closed P) : 
  is_lb P (min_of_inter_closed h) :=
  begin
    intros X hX, rcases contains_min hX with ⟨Y, ⟨hY₁, hY₂⟩⟩,  
    rwa inter_closed_min_unique P h _ _  hY₂ 
      ((classical.some_spec (inter_closed_exists_min P h))) at hY₁, 
  end

/-lemma min_of_inter_closed_is_min {P : set α → Prop} (h : inter_closed P) : 
  is_minimal P (min_of_inter_closed h) :=
  (classical.some_spec (inter_closed_exists_min P h))-/

lemma is_min_of_inter_closed {P : set α → Prop} (h : inter_closed P) {X : set α} :
  P X → is_lb P X → X = min_of_inter_closed h := 
begin
  intros hX hlb, 
  refine inter_closed_min_unique P h X (min_of_inter_closed h) ⟨hX,λ Y hY hPY, _⟩ ⟨_,λ Y hY hPY,_⟩,
  exact ssubset_not_supset hY (hlb Y hPY),     
  exact min_of_inter_closed_in h, 
  refine ssubset_not_supset (subset.lt_of_le_of_lt (hlb _ hPY) hY ) _, 
  exact (min_of_inter_closed_is_lb h) _ hX,
end

lemma is_min_of_inter_closed_iff {P : set α → Prop} (hic : inter_closed P) (X : set α) :
  X = min_of_inter_closed hic ↔ P X ∧ is_lb P X := 
begin
  refine ⟨λ h, _, λ h, is_min_of_inter_closed hic h.1 h.2 ⟩ , 
  rw h, exact ⟨min_of_inter_closed_in hic, min_of_inter_closed_is_lb hic⟩,
end

lemma max_of_union_closed_in {P : set α → Prop} (h : union_closed P) : 
  P (max_of_union_closed h) := 
  (classical.some_spec (union_closed_exists_max P h)).1 

lemma max_of_union_closed_is_ub {P : set α → Prop} (h : union_closed P) : 
  is_ub P (max_of_union_closed h) :=
begin
  intros X hX, rcases max_contains hX with ⟨Y, ⟨hY₁, hY₂⟩⟩,  
  rwa union_closed_max_unique 
    P h _ _  hY₂ ((classical.some_spec (union_closed_exists_max P h))) at hY₁
end

lemma is_max_of_union_closed {P : set α → Prop} (h : union_closed P) {X : set α} :
  P X → is_ub P X → X = max_of_union_closed h := 
begin
  intros hX hub, 
  refine union_closed_max_unique P h X (max_of_union_closed h) ⟨hX,λ Y hY hPY, _⟩ ⟨_,λ Y hY hPY,_⟩,
  exact ssubset_not_supset hY (hub Y hPY), 
  exact max_of_union_closed_in h, 
  refine ssubset_not_supset (subset.lt_of_lt_of_le hY (hub _ hPY)) _, 
  exact (max_of_union_closed_is_ub h) _ hX,
end

lemma is_max_of_union_closed_iff {P : set α → Prop} (huc : union_closed P) (X : set α) :
  X = max_of_union_closed huc ↔ P X ∧ is_ub P X := 
begin
  refine ⟨λ h, _, λ h, is_max_of_union_closed huc h.1 h.2 ⟩ , 
  rw h, exact ⟨max_of_union_closed_in huc, max_of_union_closed_is_ub huc⟩,
end



--- Unions/Intersections of collections
lemma lb_union_closed (P : set α → Prop) : 
  union_closed (λ X, is_lb P X) := 
  ⟨λ Z hZ, empty_subset Z, λ X Y hX hY, λ Z hZ, union_subset (hX Z hZ) (hY Z hZ)⟩

lemma ub_inter_closed (P : set α → Prop) : 
  inter_closed (λ X, is_ub P X) := 
  ⟨λ Z hZ, subset_univ Z, λ X Y hX hY, λ Z hZ, subset_inter (hX Z hZ) (hY Z hZ)⟩


def inter_all (P : set α → Prop) : set α := max_of_union_closed (lb_union_closed P)

def union_all (P : set α → Prop) : set α := min_of_inter_closed (ub_inter_closed P)

lemma subset_inter_all_iff (P : set α → Prop) (X : set α) :
  X ⊆ inter_all P ↔ is_lb P X :=
  begin
    refine ⟨λ h, λ Y hY, _ , λ h, max_of_union_closed_is_ub (lb_union_closed P) _ h ⟩,
    exact subset.trans h (max_of_union_closed_in (lb_union_closed P) Y hY), 
  end

lemma union_all_subset_iff (P : set α → Prop) (X : set α) : 
  union_all P ⊆ X ↔ is_ub P X := 
  begin
    refine ⟨λ h, λ Y hY, _ , λ h, min_of_inter_closed_is_lb (ub_inter_closed P) _ h ⟩,
    exact subset.trans (min_of_inter_closed_in (ub_inter_closed P) Y hY) h,  
  end

lemma union_all_ub (P : set α → Prop) :
  is_ub P (union_all P) :=
  (union_all_subset_iff P _).mp (subset_refl _ )
  
end extrema 
section size 

variables {α : Type*} [fintype α]

lemma size_sUnion_of_common_inter {I : set α} {S : set (set α)}
(hne : S.nonempty) (h : ∀ X X' ∈ S, X ≠ X' → X ∩ X' = I) : 
  size (⋃₀ S) = size I + ∑ᶠ X in S, (size X - size I) :=
begin
  revert S, 
  refine induction_set_size_insert _ (by simp) (λ S X₀ hX₀ IH, _), 
  rcases (eq_empty_or_nonempty S) with (rfl | hS), simp, 
  rintros - h, 
  rw [sUnion_insert, size_union, IH hS (λ X X' hX hX' hXX', _) ], swap,
  { apply h, repeat {rw mem_insert_iff, right, assumption,}, assumption  },
  rw fin.finsum_in_insert _ hX₀, 
  suffices hI : X₀ ∩ ⋃₀S = I, { rw hI, ring, },
  have hI' : ∀ X' ∈ S, X₀ ∩ X' = I,
  { intros X' hX', apply h, simp, rwa mem_insert_iff, exact or.inr hX', rintro rfl, exact hX₀ hX'},
  apply subset.antisymm, swap, 
  { obtain ⟨X', hX'⟩ := nonempty_def.mp hS, 
    rw ← hI' _ hX', 
    apply inter_subset_inter_right, 
    intros x hx, 
    rw mem_sUnion, 
    exact ⟨X', hX', hx⟩},
  intros x hx, 
  simp only [exists_prop, mem_inter_eq, mem_set_of_eq] at hx, 
  obtain ⟨X₁, hX₁, hxX₁⟩ := hx.2, 
  rw [← hI' X₁ hX₁, mem_inter_iff], 
  exact ⟨hx.1, hxX₁⟩,
end

lemma size_sUnion_of_common_inter' {I : set α} {S : set (set α)}
(hne : S.nonempty) (h : ∀ X X' ∈ S, X ≠ X' → X ∩ X' = I) : 
  size (⋃₀ S) =  ∑ᶠ X in S, size X - (size S - 1) * (size I)  := 
begin
  rw [size_sUnion_of_common_inter hne h],  
  have hsub : ∑ᶠ (X : set α) in S, (size X - size I) 
            = ∑ᶠ (X : set α) in S, size X - ∑ᶠ (X : set α) in S, size I,
  { apply fin.finsum_in_sub_distrib, } ,
  rw [hsub, int.finsum_in_const_eq_mul_size], 
  ring, 
end

lemma size_disjoint_sUnion {S : set (set α)}
(hdj : pairwise_disjoint S) : 
  size (⋃₀ S) =  ∑ᶠ X in S, size X :=
begin
  rcases S.eq_empty_or_nonempty with (rfl | hS), simp, 
  have hX : ∀ X X' ∈ S, X ≠ X' → X ∩ X' = ∅, 
  { simp_rw ← disjoint_iff_inter_eq_empty, 
    exact λ X X' hX hX' hXX', hdj X hX X' hX' hXX'}, 
  rw size_sUnion_of_common_inter' hS hX, simp, 
end


end size 

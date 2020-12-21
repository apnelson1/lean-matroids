import order.bounded_lattice  -- For the has_bot / has_top notation classes.
import .basic .induction .single 
----------------------------------------------------------------
local attribute [instance] classical.prop_decidable

noncomputable theory 


namespace boolalg 
-- The operations needed on the boolalg A.

variables {A: boolalg}


def is_lb (P : A → Prop) (X : A) : Prop := ∀ Y, P Y → X ⊆ Y 
def is_ub (P : A → Prop) (X : A) : Prop := ∀ Y, P Y → Y ⊆ X

def down_closed (P : A → Prop) : Prop := ∀ X Y, X ⊆ Y → P Y → P X
def up_closed (P : A → Prop) : Prop := ∀ X Y, X ⊆ Y → P X → P Y

def is_minimal (P : A → Prop) (X : A) : Prop := P X ∧ ∀ Y, (Y ⊂ X → ¬ P Y)
def is_maximal (P : A → Prop) (X : A) : Prop := P X ∧ ∀ Y, (X ⊂ Y → ¬ P Y)

lemma max_iff_compl_min (P : A → Prop) (X : A) :
  is_maximal P X ↔ is_minimal (λ Z, P Zᶜ) Xᶜ :=
  begin 
    refine ⟨λ h, ⟨by {rw ←compl_compl X at h, exact h.1},λ Y hY, _⟩, λ h, ⟨by {rw ←compl_compl X, exact h.1},λ Y hY, _⟩⟩, 
    exact h.2 _ (ssubset_compl_right hY), rw ←compl_compl Y, exact h.2 _ (ssubset_to_compl hY), 
  end

lemma down_closed_iff_negation_up_closed (P : A → Prop) : 
  down_closed P ↔ up_closed (λ X, ¬P X) := 
  by {unfold down_closed up_closed, simp_rw not_imp_not}


lemma contains_min {P : A → Prop} {X : A}:
  P X → ∃ Y, Y ⊆ X ∧ is_minimal P Y := 
  minimal_example P 

lemma max_contains {P : A → Prop} {X : A}:
  P X → ∃ Y, X ⊆ Y ∧ is_maximal P Y :=  
  maximal_example P

-- Union/Intersection-closed collections of sets

def union_closed (P : A → Prop) : Prop := P ⊥ ∧ ∀ X Y, P X → P Y → P (X ∪ Y)
def inter_closed (P : A → Prop) : Prop := P ⊤ ∧ ∀ X Y, P X → P Y → P (X ∩ Y)

lemma union_closed_iff_compl_inter_closed (P : A → Prop) : 
  union_closed P ↔ inter_closed (λ X, P Xᶜ) := 
  begin
    refine ⟨λ h, ⟨by {rw compl_top, exact h.1},λ X Y hX hY, _⟩, λ h,⟨by {rw ←compl_top, exact h.1},λ X Y hX hY,_⟩ ⟩,  
    rw compl_inter, exact h.2 _ _ hX hY, 
    rw [←compl_compl (X ∪ Y), compl_union], rw ←compl_compl X at hX, rw ←compl_compl Y at hY, exact h.2 _ _ hX hY,
  end 

lemma inter_closed_exists_min (P : A → Prop) : 
  inter_closed P → ∃ X, is_minimal P X :=  
  λ h, by {cases (contains_min h.1) with Y, use Y, exact h_1.2}

lemma inter_closed_min_unique (P : A → Prop) : 
  inter_closed P → ∀ X₁ X₂, is_minimal P X₁ → is_minimal P X₂ → X₁ = X₂ := 
  by {intros hP _ _ h₁ h₂, replace hP := hP.2 _ _ h₁.1 h₂.1, by_contra, 
      cases ssubset_inter a, exact (h₁.2 _ h) hP, exact (h₂.2 _ h) hP} 

lemma inter_closed_min_iff_in_and_lb {P : A → Prop}(hP : inter_closed P) (X : A):
  is_minimal P X ↔ P X ∧ is_lb P X := 
  begin
    refine ⟨λ h, ⟨h.1, λ Z pZ,_⟩, λ h,⟨h.1, λ Y hY hPY, _⟩⟩, 
    by_contra, rw subset_def_union at a, refine  h.2 _ _ (hP.2 _ _ pZ h.1), 
    rw [←subset_def_union, subset_def_inter, inter_comm] at a, 
    exact ⟨inter_subset_right _ _, a⟩, 
    exact ssubset_not_supset hY (h.2 _ hPY), 
  end

lemma union_closed_exists_max (P : A → Prop) : 
  union_closed P → ∃ X, is_maximal P X :=  
  λ h, by {cases (max_contains h.1) with Y, use Y, exact h_1.2}

lemma union_closed_max_unique (P : A → Prop) : 
  union_closed P → ∀ X₁ X₂, is_maximal P X₁ → is_maximal P X₂ → X₁ = X₂ := 
  begin
    rw [union_closed_iff_compl_inter_closed], simp_rw [max_iff_compl_min], refine λ h X₁ X₂ h₁ h₂,_ ,
    rw [←compl_compl X₁, ←compl_compl X₂, inter_closed_min_unique _ h _ _ h₁ h₂],
  end 

lemma union_closed_max_iff_in_and_ub {P : A → Prop}(hP : union_closed P) (X : A):
  is_maximal P X ↔ P X ∧ is_ub P X := 
  begin
    refine ⟨λ h, ⟨h.1, λ Z pZ,_⟩, λ h,⟨h.1, λ Y hY hPY, _⟩⟩, 
    by_contra, rw subset_def_union at a, refine  h.2 _ _ (hP.2 _ _ pZ h.1), 
    exact ⟨subset_union_right _ _, ne.symm a⟩, 
    exact ssubset_not_supset hY (h.2 _ hPY), 
  end

def min_of_inter_closed {P : A → Prop} (h : inter_closed P) : A := 
  classical.some (inter_closed_exists_min P h) 

def max_of_union_closed {P : A → Prop} (h : union_closed P) : A := 
  classical.some (union_closed_exists_max P h) 

lemma min_of_inter_closed_in {P : A → Prop}(h : inter_closed P) :
  P (min_of_inter_closed h) := 
  (classical.some_spec (inter_closed_exists_min P h)).1 

lemma min_of_inter_closed_is_lb {P : A → Prop}(h : inter_closed P): 
  is_lb P (min_of_inter_closed h) :=
  begin
    intros X hX, rcases contains_min hX with ⟨Y, ⟨hY₁, hY₂⟩⟩,  
    rw inter_closed_min_unique P h _ _  hY₂ ((classical.some_spec (inter_closed_exists_min P h))) at hY₁, exact hY₁,
  end

/-lemma min_of_inter_closed_is_min {P : A → Prop}(h : inter_closed P) : 
  is_minimal P (min_of_inter_closed h) :=
  (classical.some_spec (inter_closed_exists_min P h))-/

lemma is_min_of_inter_closed {P : A → Prop}(h : inter_closed P) {X : A}:
  P X → is_lb P X → X = min_of_inter_closed h := 
  begin
    intros hX hlb, 
    refine inter_closed_min_unique P h X (min_of_inter_closed h) ⟨hX,λ Y hY hPY, _⟩ ⟨_,λ Y hY hPY,_⟩,
    exact ssubset_not_supset hY (hlb Y hPY),     
    exact min_of_inter_closed_in h, 
    refine ssubset_not_supset (subset_ssubset_trans (hlb _ hPY) hY ) _, 
    exact (min_of_inter_closed_is_lb h) _ hX,
  end

lemma is_min_of_inter_closed_iff {P : A → Prop}(hic : inter_closed P) (X : A):
  X = min_of_inter_closed hic ↔ P X ∧ is_lb P X := 
  begin
    refine ⟨λ h, _, λ h, is_min_of_inter_closed hic h.1 h.2 ⟩ , 
    rw h, exact ⟨min_of_inter_closed_in hic, min_of_inter_closed_is_lb hic⟩,
  end

lemma max_of_union_closed_in {P : A → Prop} (h : union_closed P) : 
  P (max_of_union_closed h) := 
  (classical.some_spec (union_closed_exists_max P h)).1 

lemma max_of_union_closed_is_ub {P : A → Prop}(h : union_closed P) : 
  is_ub P (max_of_union_closed h) :=
  begin
    intros X hX, rcases max_contains hX with ⟨Y, ⟨hY₁, hY₂⟩⟩,  
    rw union_closed_max_unique P h _ _  hY₂ ((classical.some_spec (union_closed_exists_max P h))) at hY₁, exact hY₁ 
  end

lemma is_max_of_union_closed {P : A → Prop}(h : union_closed P) {X : A}:
  P X → is_ub P X → X = max_of_union_closed h := 
  begin
    intros hX hub, 
    refine union_closed_max_unique P h X (max_of_union_closed h) ⟨hX,λ Y hY hPY, _⟩ ⟨_,λ Y hY hPY,_⟩,
    exact ssubset_not_supset hY (hub Y hPY), 
    exact max_of_union_closed_in h, 
    refine ssubset_not_supset (ssubset_subset_trans hY (hub _ hPY)) _, 
    exact (max_of_union_closed_is_ub h) _ hX,
  end

lemma is_max_of_union_closed_iff {P : A → Prop}(huc : union_closed P) (X : A):
  X = max_of_union_closed huc ↔ P X ∧ is_ub P X := 
  begin
    refine ⟨λ h, _, λ h, is_max_of_union_closed huc h.1 h.2 ⟩ , 
    rw h, exact ⟨max_of_union_closed_in huc, max_of_union_closed_is_ub huc⟩,
  end



--- Unions/Intersections of collections
lemma lb_union_closed (P : A → Prop) : 
  union_closed (λ X, is_lb P X) := 
  ⟨λ Z hZ, bot_subset Z, λ X Y hX hY, λ Z hZ, union_of_subsets (hX Z hZ) (hY Z hZ)⟩

lemma ub_inter_closed (P : A → Prop) : 
  inter_closed (λ X, is_ub P X) := 
  ⟨λ Z hZ, subset_top Z, λ X Y hX hY, λ Z hZ, subset_of_inter_mpr (hX Z hZ) (hY Z hZ)⟩


def inter_all (P : A → Prop) : A := max_of_union_closed (lb_union_closed P)

def union_all (P : A → Prop) : A := min_of_inter_closed (ub_inter_closed P)

lemma subset_inter_all_iff (P : A → Prop) (X : A):
  X ⊆ inter_all P ↔ is_lb P X :=
  begin
    refine ⟨λ h, λ Y hY, _ , λ h, max_of_union_closed_is_ub (lb_union_closed P) _ h ⟩,
    exact subset_trans h (max_of_union_closed_in (lb_union_closed P) Y hY), 
  end

lemma union_all_subset_iff (P : A → Prop) (X : A): 
  union_all P ⊆ X ↔ is_ub P X := 
  begin
    refine ⟨λ h, λ Y hY, _ , λ h, min_of_inter_closed_is_lb (ub_inter_closed P) _ h ⟩,
    exact subset_trans (min_of_inter_closed_in (ub_inter_closed P) Y hY) h,  
  end

lemma union_all_ub (P : A → Prop):
  is_ub P (union_all P) :=
  (union_all_subset_iff P _).mp (subset_refl _ )
  
def union_singles (P : single A → Prop) : A := 
  union_all (λ X, if h : (size X = 1)  then P ⟨X,h⟩ else false) 

def union_singles_elem_iff (P : single A → Prop)(e : single A) : 
  e ∈ (union_singles P) ↔ P e :=
  begin
    let Q := (λ X, if h : (size X = 1)  then P ⟨X,h⟩ else false),
    set X := union_all Q with hdefX, 
    have hX := (is_min_of_inter_closed_iff (ub_inter_closed Q) _ ).mp hdefX, 
    refine ⟨λ h, _, λ h, _⟩, by_contra h_contr,
    have : is_ub (λ Y, Q Y) (X \ e) := λ Z hZ, by 
    {
      simp only [Q] at hZ, split_ifs at hZ,
      
      show (⟨Z, h_1⟩ : single A) ∈ X \ e,
      rw elem_diff_iff, split, 
      have := hX.1 Z, simp only [Q] at this,  
      split_ifs at this, 
      from this hZ, 
      refine λ h', by {rw [←nested_singles_eq h'] at h_contr, from h_contr hZ }, 
      from false.elim hZ, 
    },
    from (nonelem_of_subset_remove_single _ _ (hX.2 _ this)) h, 
    have : Q e := by {simp only [Q], split_ifs, simp only [subtype.coe_eta], from h, from h_1 (size_single e)},
    from hX.1 _ this,  
  end


end boolalg 
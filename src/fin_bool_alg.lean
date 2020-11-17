import tactic.ext
--import tactic.ring 
import tactic.linarith
import tactic.tidy 

-- The API I would like to use for various basic objects.
-- This probably belongs in its own file by this point. 

section API

namespace fin_bool_alg 

structure fin_bool_alg :=
  (subset : Type)
  --(contained : subset → subset → Prop)
  (bot top : subset)
  (inter union : subset → subset → subset)
  (compl : subset → subset)
  (size : subset → ℤ)

  (size_bot_ax : size bot = 0)
  (size_nonneg_ax (X: subset) : 0 ≤ size X) 
  (size_modular_ax (X Y: subset) : size (union X Y) + size (inter X Y) = size X + size Y)
  (size_singleton_ax (X : subset) (hX : (∀ (Y: subset), (Y = inter Y X) → (Y ≠ X) → (Y = bot))) : size X ≤ 1)

  (inter_comm_ax (X Y : subset) : inter X Y = inter Y X)
  (union_comm_ax (X Y : subset) : union X Y = union Y X)
  
  (union_distrib_left_ax (X Y Z : subset) : union (inter X Y) Z = inter (union X Z) (union Y Z))
  (inter_distrib_left_ax (X Y Z : subset) : inter (union X Y) Z = union (inter X Z) (inter Y Z))

  (inter_top_ax (X : subset) : inter X top = X)
  (union_bot_ax (X : subset) : union X bot = X)

  (union_compl_ax (X: subset) : union X (compl X) = top)
  (inter_compl_ax (X: subset) : inter X (compl X) = bot)

-- associativity axioms can be removed - WIP
  (inter_assoc_ax (X Y Z : subset) : inter (inter X Y) Z = inter X (inter Y Z))
  (union_assoc_ax (X Y Z : subset) : union (union X Y) Z = union X (union Y Z))

-- Instances to enable ⊆ , ∩ , ∪ , ᶜ , ⊤, ⊥ , - (set diff)

instance i1 : has_coe_to_sort fin_bool_alg := {S := Type, coe := fin_bool_alg.subset}
instance i2 {A : fin_bool_alg} : has_bot A := {bot := A.bot}
instance i3 {A : fin_bool_alg} : has_top A := {top := A.top}
instance i4 {A : fin_bool_alg} : has_inter A := {inter := A.inter}
instance i5 {A : fin_bool_alg} : has_union A := {union := A.union}
instance i6 {A : fin_bool_alg} : has_compl A := {compl := A.compl}
instance i7 {A : fin_bool_alg} : has_subset A := {subset := λ (X Y), (X = X ∩ Y)} 
instance i8 {A : fin_bool_alg} : has_sub A := {sub := λ (X Y), X ∩ Yᶜ}

def size {A : fin_bool_alg} (X : A) : ℤ := A.size X
def sdiff {A: fin_bool_alg} (X Y : A) : A := (X - Y) ∪ (Y - X)


-- Lemmas (some are just the axioms rewritten in terms of the notation to make linarith etc behave more nicely)

-- Commutativity

lemma inter_comm {A : fin_bool_alg} (X Y : A) : 
  (X ∩ Y = Y ∩ X) := 
  A.inter_comm_ax X Y

lemma union_comm {A : fin_bool_alg} (X Y : A) :
  (X ∪ Y = Y ∪ X) := 
  A.union_comm_ax X Y

-- Top/Bottom with unions and intersections 

lemma inter_top_right  {A : fin_bool_alg} (X : A) : X ∩ ⊤ = X := A.inter_top_ax X

lemma inter_top_left {A : fin_bool_alg} (X : A) : 
  ⊤ ∩ X = X := 
  eq.trans (inter_comm ⊤ X) (inter_top_right  X) 

lemma union_bot_right {A : fin_bool_alg} (X : A) : X ∪ ⊥ = X := A.union_bot_ax X 

lemma union_bot_left {A : fin_bool_alg} (X : A) : 
  ⊥ ∪ X = X := 
  eq.trans (union_comm ⊥ X) (union_bot_right X)


-- Complements

lemma union_compl {A: fin_bool_alg} (X: A) : 
  X ∪ Xᶜ = ⊤ := 
  A.union_compl_ax X 

lemma inter_compl {A: fin_bool_alg} (X: A) : X ∩ Xᶜ = ⊥ := A.inter_compl_ax X 



-- Distributivity

lemma union_distrib_left {A : fin_bool_alg} (X Y Z : A) : (X ∩ Y) ∪ Z = (X ∪ Z) ∩ (Y ∪ Z) := A.union_distrib_left_ax X Y Z

lemma union_distrib_right {A : fin_bool_alg} (X Y Z : A) : X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z) := 
  by calc X ∪ (Y ∩ Z) = (Y ∩ Z) ∪ X       : union_comm X (Y ∩ Z) 
                  ... = (Y ∪ X) ∩ (Z ∪ X) : union_distrib_left Y Z X  
                  ... = (X ∪ Y) ∩ (X ∪ Z) : by rw [union_comm X Y, union_comm X Z]

lemma inter_distrib_left {A : fin_bool_alg} (X Y Z : A) : (X ∪ Y) ∩ Z = (X ∩ Z) ∪ (Y ∩ Z) := A.inter_distrib_left_ax X Y Z

lemma inter_distrib_right {A : fin_bool_alg} (X Y Z : A) : X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) := 
  by calc X ∩ (Y ∪ Z) = (Y ∪ Z) ∩ X       : inter_comm X (Y ∪ Z) 
      ...             = (Y ∩ X) ∪ (Z ∩ X) : inter_distrib_left Y Z X
      ...             = (X ∩ Y) ∪ (X ∩ Z) : by rw [inter_comm X Y, inter_comm X Z]

-- Building things up from a minimal axiom set for fun

lemma bot_unique {A : fin_bool_alg} (X : A) : 
  (∀ (Y: A), Y ∪ X = Y) → X = ⊥ := 
  by intros hX; calc X = ⊥ ∪ X : (union_bot_left X).symm ... = ⊥ : hX ⊥

lemma top_unique {A : fin_bool_alg} (X : A) : 
  (∀ (Y: A), Y ∩ X = Y) → X = ⊤ := 
  by intros hX; calc X = ⊤ ∩ X : (inter_top_left X).symm ... = ⊤ : hX ⊤ 

-- Idempotence

lemma union_idem {A : fin_bool_alg} (X : A) : 
  X ∪ X = X := 
  by rw [←(inter_top_right  (X ∪ X)), ←(union_compl X), ←(union_distrib_right X X Xᶜ), inter_compl, union_bot_right]

lemma inter_idem {A : fin_bool_alg} (X : A): 
  X ∩ X = X := 
  by rw [←(union_bot_right (X ∩ X)), ←(inter_compl X), ←(inter_distrib_right X X Xᶜ), union_compl, inter_top_right ]

lemma union_top_right {A : fin_bool_alg} (X : A) :
  X ∪ ⊤ = ⊤ := 
  by calc X ∪ ⊤ = ⊤ ∩ (X ∪ ⊤)        : by rw inter_top_left
            ... = (X ∪ Xᶜ) ∩ (X ∪ ⊤) : by rw union_compl 
            ... = ⊤    : by rw [←union_distrib_right, inter_top_right , union_compl]

lemma union_top_left {A : fin_bool_alg} (X : A) : 
  ⊤ ∪ X = ⊤ := 
  eq.trans (union_comm ⊤ X) (union_top_right X)


lemma inter_bot_right {A : fin_bool_alg} (X : A) :
  X ∩ ⊥ = ⊥ := 
  by calc X ∩ ⊥ = ⊥ ∪ (X ∩ ⊥)        : by rw union_bot_left
            ... = (X ∩ Xᶜ) ∪ (X ∩ ⊥) : by rw inter_compl 
            ... = ⊥    : by rw [←inter_distrib_right, union_bot_right, inter_compl]

lemma inter_bot_left {A : fin_bool_alg} (X : A) : 
  ⊥ ∩ X = ⊥ := 
  eq.trans (inter_comm ⊥ X) (inter_bot_right X)


-- Absorption

lemma absorb_union_inter {A : fin_bool_alg} (X Y : A) : 
  X ∪ (X ∩ Y) = X := 
  by calc X ∪ (X ∩ Y) = (X ∩ ⊤) ∪ (X ∩ Y) : by rw inter_top_right  ... = X : by rw [←inter_distrib_right, union_comm, union_top_right, inter_top_right ]

lemma absorb_inter_union {A : fin_bool_alg} (X Y : A) : 
  X ∩ (X ∪ Y) = X := 
  by calc X ∩ (X ∪ Y) = (X ∪ ⊥) ∩ (X ∪ Y) : by rw union_bot_right ... = X : by rw [←union_distrib_right, inter_comm, inter_bot_right, union_bot_right]


-- Associativity (In fact, this can be discarded eventually : WIP)

lemma inter_assoc {A : fin_bool_alg} (X Y Z : A) : (X ∩ Y) ∩ Z = X ∩ (Y ∩ Z) := A.inter_assoc_ax X Y Z 

lemma union_assoc {A : fin_bool_alg} (X Y Z : A) : (X ∪ Y) ∪ Z = X ∪ (Y ∪ Z) := A.union_assoc_ax X Y Z 





-- Size 

lemma size_modular {A : fin_bool_alg} (X Y : A) : size (X ∪ Y) + size (X ∩ Y) = size (X) + size Y := A.size_modular_ax X Y

lemma size_bot (A : fin_bool_alg) : 
  size (⊥ : A) = 0 := 
  A.size_bot_ax

lemma size_singleton {A : fin_bool_alg} (X : A) 
  (hX : (∀ (Y : A), Y ⊆ X → Y ≠ X → Y = ⊥)) : size X = 1 := 
  A.size_singleton_ax X hX 

lemma size_nonneg {A : fin_bool_alg} (X : A) : 
  0 ≤ size X := 
  A.size_nonneg_ax X 

-- Subsets 

lemma inter_subset {A : fin_bool_alg} (X Y: A) : 
  (X ⊆ Y) ↔ (X ∩ Y = X) 
  := by split; apply eq.symm; tidy; rw a; tidy 

lemma union_subset {A: fin_bool_alg} (X Y : A) : 
  (X ⊆ Y) ↔ (X ∪ Y = Y) := 
begin
  split, 
  intros hXY,
  unfold has_subset.subset at hXY,
  calc X ∪ Y = (X ∩ Y) ∪ Y : by rw ← hXY
  ...        = Y ∪ (X ∩ Y) : union_comm _ _
  ...        = Y ∪ (Y ∩ X) : by rw (inter_comm X)
  ...        = Y           : absorb_union_inter _ _, 
  
  intros hXY2,
  calc X = X ∩ (X ∪ Y)  : eq.symm (absorb_inter_union X Y)
  ...    = X ∩ Y        : by rw hXY2,
end

lemma ss_antisymm {A : fin_bool_alg} {X Y : A} 
  (hXY : X ⊆ Y) (hYX : Y ⊆ X) : X = Y := 
  by unfold has_subset.subset at hXY hYX; calc X = X ∩ Y : hXY ... = Y ∩ X : inter_comm X Y ... = Y : by rw ← hYX


lemma inter_subset_left {A: fin_bool_alg} (X Y : A) : 
  (X ∩ Y) ⊆ X := 
  by apply (union_subset (X ∩ Y) X).mpr; rw union_comm (X ∩ Y) X; apply absorb_union_inter


lemma inter_subset_right {A : fin_bool_alg} (X Y : A) : 
  (X ∩ Y) ⊆ Y := 
  by apply (union_subset (X ∩ Y) Y).mpr; rw [union_comm,inter_comm X Y]; apply absorb_union_inter


lemma subset_top {A : fin_bool_alg} (X : A) : 
  X ⊆ ⊤ := 
  by unfold has_subset.subset; exact eq.symm (inter_top_right  X)

lemma top_subset {A : fin_bool_alg} {X : A} 
  (hX : ⊤ ⊆ X) : X = ⊤ := 
  ss_antisymm (subset_top X) hX


lemma bot_subset {A : fin_bool_alg} (X : A) : 
  ⊥ ⊆ X := 
  by unfold has_subset.subset; exact eq.symm (inter_bot_left X)

lemma subset_bot {A : fin_bool_alg} {X : A} 
  (hX : X ⊆ ⊥) : X = ⊥ := 
  ss_antisymm hX (bot_subset X)  


lemma disjoint_compl_subset {A : fin_bool_alg} {X Y : A} 
  (hXY: X ∩ Y = ⊥) : X ⊆ Yᶜ := 
begin
  apply eq.symm, 
  calc X ∩ Yᶜ = ⊥ ∪ (X ∩ Yᶜ)       : (union_bot_left _).symm 
          ... = (X ∩ Y) ∪ (X ∩ Yᶜ) : by rw ←hXY
          ... = X ∩ (Y ∪ Yᶜ)       : (inter_distrib_right _ _ _).symm 
          ... = X ∩ ⊤              : by rw (union_compl Y)
          ... = X                  : inter_top_right  X, 
end

lemma cover_compl_subset {A: fin_bool_alg} {X Y : A} 
  (hXY: X ∪ Y = ⊤) : Xᶜ ⊆ Y  := 
begin
  apply (union_subset Xᶜ Y).mpr, 
  calc Xᶜ ∪ Y = ⊤ ∩ (Xᶜ ∪ Y)        : (inter_top_left _).symm 
          ... = (X ∪ Y) ∩ (Xᶜ ∪ Y)  : by rw ←hXY
          ... = (X ∩ Xᶜ) ∪ Y        : (union_distrib_left _ _ _).symm 
          ... = ⊥ ∪ Y               : by rw inter_compl
          ... = Y                   : union_bot_left Y,
end
 
lemma compl_unique {A : fin_bool_alg} {X Y : A} 
  (hU : X ∪ Y = ⊤) (hI : X ∩ Y = ⊥) : Y = Xᶜ := 
begin
  apply ss_antisymm,
  exact disjoint_compl_subset (eq.trans (inter_comm Y X) hI),
  exact cover_compl_subset hU, 
end 


lemma compl_involution {A : fin_bool_alg} (X : A) : 
  Xᶜᶜ = X := 
begin
  apply ss_antisymm,
  apply cover_compl_subset, 
  exact eq.trans (union_comm Xᶜ X) (union_compl X), 
  exact disjoint_compl_subset (inter_compl X),
end


lemma compl_inter {A : fin_bool_alg} (X Y : A) : 
  (X ∩ Y)ᶜ = Xᶜ ∪ Yᶜ := 
begin
  apply eq.symm, 
  apply compl_unique, 
  calc X ∩ Y ∪ (Xᶜ ∪ Yᶜ) = (X ∪ (Xᶜ ∪ Yᶜ)) ∩ (Y ∪ (Xᶜ ∪ Yᶜ)) : union_distrib_left _ _ _ 
                    ...  = ((X ∪ Xᶜ) ∪ Yᶜ) ∩ ((Y ∪ Yᶜ) ∪ Xᶜ) : by rw [(union_assoc X), (union_comm Xᶜ), (union_assoc Y)]
                    ...  = ⊤                                 : by rw [union_compl X, union_compl Y, union_top_left, union_top_left, inter_idem],
  
  calc (X ∩ Y) ∩ (Xᶜ ∪ Yᶜ) = (X ∩ Y ∩ Xᶜ) ∪ (X ∩ Y ∩ Yᶜ)     : inter_distrib_right _ _ _
                      ...  = (Y ∩ X ∩ Xᶜ) ∪ (X ∩ Y ∩ Yᶜ)     : by rw (inter_comm X Y)
                      ...  = (Y ∩ (X ∩ Xᶜ)) ∪ (X ∩ (Y ∩ Yᶜ)) : by rw [inter_assoc, inter_assoc]
                      ...  = ⊥                               : by rw [inter_compl X, inter_compl Y, inter_bot_right Y, inter_bot_right X, union_idem]
end 

lemma compl_union {A : fin_bool_alg} (X Y : A) : 
(X ∪ Y)ᶜ = Xᶜ ∩ Yᶜ := 
begin
  calc (X ∪ Y)ᶜ = (Xᶜᶜ ∪ Yᶜᶜ)ᶜ    : by rw [compl_involution X,compl_involution Y]
        ...     = ((Xᶜ ∩ Yᶜ)ᶜ)ᶜ   : by rw (compl_inter Xᶜ Yᶜ)
        ...     = (Xᶜ ∩ Yᶜ)       : by rw (compl_involution (Xᶜ ∩ Yᶜ)), 
end

lemma compl_subset {A : fin_bool_alg} {X Y : A} 
(hXY : X ⊆ Y) : Yᶜ ⊆ Xᶜ := 
begin
  apply eq.symm, 
  rw [←((inter_subset X Y).mp hXY), compl_inter, union_comm], 
  apply absorb_inter_union,
end 





-- Self-Distributivity

lemma inter_distrib_inter_left {A : fin_bool_alg} (X Y Z : A) : 
  (X ∩ Y) ∩ Z = (X ∩ Z) ∩ (Y ∩ Z) := 
  by rw [inter_assoc X Z, inter_comm Z, inter_assoc Y, inter_idem, inter_assoc]  


lemma union_distrib_union_left {A : fin_bool_alg} (X Y Z : A) : 
  (X ∪ Y) ∪ Z = (X ∪ Z) ∪ (Y ∪ Z) := 
  by rw [union_assoc X Z, union_comm Z, union_assoc Y, union_idem, union_assoc]

lemma union_distrib_union_right {A : fin_bool_alg} (X Y Z : A) : 
  X ∪ (Y ∪ Z) = (X ∪ Y) ∪ (X ∪ Z) := 
  by rw [union_comm X, union_distrib_union_left Y Z X, union_comm X, union_comm X]   





lemma inter_is_lb {A : fin_bool_alg} (X Y Z : A) : 
Z ⊆ X → Z ⊆ Y → Z ⊆ (X ∩ Y) := 
begin
  unfold has_subset.subset,
  intros hZX hZY, 
  calc Z = Z ∩ Y        : hZY
  ...    = (Z ∩ X) ∩ Y  : by rw ← hZX
  ...    = Z ∩ (X ∩ Y)  : inter_assoc Z X Y, 
end 

lemma union_is_ub {A : fin_bool_alg} (X Y Z : A) : 
X ⊆ Z → Y ⊆ Z → X ∪ Y ⊆ Z := 
begin
  unfold has_subset.subset, 
  intros hXZ hYZ, 
  calc X ∪ Y = (X ∩ Z) ∪ (Y ∩ Z)    : by rw [←hXZ, ←hYZ]
  ...        = (X ∪ Y) ∩ Z          : by rw inter_distrib_left, 
end

lemma diff_subset {A : fin_bool_alg} (X Y : A) : X - Y ⊆ X := inter_subset_left X Yᶜ

lemma diff_union {A : fin_bool_alg} (X Y : A): 
(X ∩ Y) ∪ (Y - X) = Y := 
begin
  unfold has_sub.sub, 
  rw ← inter_comm Y X, 
  rw ← inter_distrib_right, 
  rw union_compl, 
  exact inter_top_right  Y,
end

lemma diff_union_subset {A : fin_bool_alg} {X Y : A} (hXY : X ⊆ Y) : 
X ∪ (Y - X) = Y := 
begin
  unfold has_subset.subset at hXY, 
  have := diff_union X Y, 
  rw ← hXY at this, 
  exact this, 
end

lemma diff_inter {A : fin_bool_alg} (X Y : A) : 
X ∩ (Y - X) = ⊥ := 
begin
  unfold has_sub.sub, 
  rw [←inter_assoc, inter_comm X Y, inter_assoc, inter_compl ,inter_bot_right],
end

lemma size_monotone {A : fin_bool_alg} {X Y: A} 
(hXY : X ⊆ Y) : size X ≤ size Y := 
begin
  have := size_modular X (Y-X), 
  rw diff_union_subset hXY at this, 
  rw diff_inter at this, 
  linarith [size_nonneg(Y-X), size_bot A],
end

lemma size_disjoint_sum {A : fin_bool_alg} {X Y : A} 
(hXY: X ∩ Y = ⊥) : size (X ∪ Y) = size X + size Y := 
begin
  have := size_modular X Y, 
  rw [hXY, size_bot] at this, 
  linarith, -- for some reason 'ring' doesn't work here. I don't know why.  
end

lemma size_compl_sum {A : fin_bool_alg} (X : A) : 
size X + size Xᶜ = size (⊤ : A) := 
begin
  have := size_disjoint_sum (inter_compl X),
  rw (union_compl X) at this, 
  linarith, 
end 

lemma compl_inter_size {A: fin_bool_alg} (X Y : A) : 
size (X ∩ Y) + size (Xᶜ ∩ Y) = size Y := 
    by rw [←size_modular, ←inter_distrib_left, union_compl, inter_top_left, ←inter_distrib_inter_left, inter_compl, inter_bot_left, size_bot]; ring


lemma compl_inter_size_subset {A : fin_bool_alg} {X Y : A} 
(hXY : X ⊆ Y) : size (Xᶜ ∩ Y) = size Y - size X := 
begin
    have := compl_inter_size X Y, 
    rw hXY.symm at this, 
    linarith, 
end

lemma diff_size {A : fin_bool_alg} {X Y : A} 
(hXY : X ⊆ Y) : size (Y - X) = size Y - size X :=  
begin 
    unfold has_sub.sub, 
    rw inter_comm, 
    exact compl_inter_size_subset hXY, 
end  


lemma subset_inter_subset_left {A : fin_bool_alg} (X Y Z : A) : 
(X ⊆ Y) → (X ∩ Z) ⊆ (Y ∩ Z) := 
begin
  unfold has_subset.subset, 
  intro hXY, 
  rw [←inter_distrib_inter_left, ←hXY],
end

lemma subset_union_subset_left {A : fin_bool_alg} (X Y Z : A) : 
(X ⊆ Y) → (X ∪ Z) ⊆ (Y ∪ Z) := 
begin
  rw union_subset _ _, 
  rw union_subset _ _, 
  intros hXY, 
  rw [←union_distrib_union_left, hXY], 
end

def fin_bool_alg.canonical (size : ℤ) :
  (0 ≤ size) → fin_bool_alg := sorry

-- Construct a fin_bool_alg from a finite set S 

def power_set_alg {γ : Type} [decidable_eq γ] (S : finset γ) : fin_bool_alg := 
{
  subset := {X: finset γ | X ⊆ S},

  bot := ⟨∅, finset.empty_subset S⟩,
  top := ⟨S, finset.subset.refl S⟩,
  inter := λ (X Y : _), ⟨X.val ∩ Y.val, finset.subset.trans (X.val.inter_subset_left Y) X.property⟩, 
  union := λ (X Y : _), ⟨X.val ∪ Y.val, finset.union_subset X.property Y.property⟩,
  size  := λ X, (finset.card (X.val) : ℤ), 
  compl := λ X, ⟨S \ X.val, finset.sdiff_subset_self⟩,

  size_bot_ax := by tidy, 
  size_nonneg_ax := by tidy, 
  size_modular_ax := by tidy; apply finset.card_union_add_card_inter,
  size_singleton_ax := 
  begin
    tidy, 
    
    sorry, 
  end, 

  inter_comm_ax := by tidy, 
  union_comm_ax := by intros X Y; simp_rw finset.union_comm; trivial, 
  inter_assoc_ax := by tidy, 
  union_assoc_ax := by tidy,
  union_distrib_left_ax := by intros _ _ _; apply subtype.eq; simp_rw finset.union_distrib_left; exact finset.union_distrib_right _ _ _,
  inter_distrib_left_ax := by intros _ _ _; apply subtype.eq; simp_rw finset.inter_distrib_left; exact finset.inter_distrib_right _ _ _,  
  inter_top_ax := by tidy, 
  union_bot_ax := by tidy, 
  union_compl_ax := by tidy, 
  inter_compl_ax := by tidy, 
}


--def sub_alg (A : fin_bool_alg) (X : A) : fin_bool_alg := {}
end fin_bool_alg
end API 
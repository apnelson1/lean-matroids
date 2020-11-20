import tactic.ext
--import tactic.ring 
import tactic.linarith
import tactic.tidy 

-- The API I would like to use for various basic objects.
-- This probably belongs in its own file by this point. 

local attribute [instance] classical.prop_decidable

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
  (size_singleton_ax (X : subset) : (1 < size X) → (∃ (Y : subset), (inter X Y = Y) ∧ (0 < size Y) ∧ (size Y < size X)))

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

variables {A : fin_bool_alg}


instance i1  : has_coe_to_sort fin_bool_alg := {S := Type, coe := fin_bool_alg.subset}
instance i2  : has_bot A := {bot := A.bot}
instance i3  : has_top A := {top := A.top}
instance i4  : has_inter A := {inter := A.inter}
instance i5  : has_union A := {union := A.union}
instance i6  : has_compl A := {compl := A.compl}
instance i7  : has_subset A := {subset := λ (X Y), (X = X ∩ Y)} 
instance i8  : has_sub A := {sub := λ (X Y), X ∩ Yᶜ}

def size  (X : A) : ℤ := A.size X
def sdiff  (X Y : A) : A := (X - Y) ∪ (Y - X)


-- Lemmas (some are just the axioms rewritten in terms of the notation to make linarith etc behave more nicely)

-- Commutativity

lemma inter_comm (X Y : A) : (X ∩ Y = Y ∩ X) := 
  A.inter_comm_ax X Y

lemma union_comm (X Y : A) : (X ∪ Y = Y ∪ X) := 
  A.union_comm_ax X Y

-- Top/Bottom with unions and intersections 

lemma inter_top (X : A) : X ∩ ⊤ = X := A.inter_top_ax X

lemma top_inter  (X : A) : ⊤ ∩ X = X := 
  eq.trans (inter_comm ⊤ X) (inter_top  X) 

lemma union_bot {A : fin_bool_alg} (X : A) : X ∪ ⊥ = X := A.union_bot_ax X 

lemma bot_union {A : fin_bool_alg} (X : A) : 
  ⊥ ∪ X = X := 
  eq.trans (union_comm ⊥ X) (union_bot X)


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

lemma bot_unique (X : A) : (∀ (Y: A), Y ∪ X = Y) → X = ⊥ := 
  by intros hX; calc X = ⊥ ∪ X : (bot_union X).symm ... = ⊥ : hX ⊥

lemma top_unique (X : A) : (∀ (Y: A), Y ∩ X = Y) → X = ⊤ := 
  by intros hX; calc X = ⊤ ∩ X : (top_inter X).symm ... = ⊤ : hX ⊤ 



-- Idempotence

lemma union_idem (X : A) : X ∪ X = X := 
  by rw [←(inter_top  (X ∪ X)), ←(union_compl X), ←(union_distrib_right X X Xᶜ), inter_compl, union_bot]

lemma inter_idem (X : A): X ∩ X = X := 
  by rw [←(union_bot (X ∩ X)), ←(inter_compl X), ←(inter_distrib_right X X Xᶜ), union_compl, inter_top ]

lemma union_top  (X : A) : X ∪ ⊤ = ⊤ := 
  by calc X ∪ ⊤ = ⊤ ∩ (X ∪ ⊤)        : by rw top_inter
            ... = (X ∪ Xᶜ) ∩ (X ∪ ⊤) : by rw union_compl 
            ... = ⊤    : by rw [←union_distrib_right, inter_top , union_compl]

lemma top_union (X : A) : ⊤ ∪ X = ⊤ := 
  eq.trans (union_comm ⊤ X) (union_top X)


lemma inter_bot  (X : A) : X ∩ ⊥ = ⊥ := 
  by calc X ∩ ⊥ = ⊥ ∪ (X ∩ ⊥)        : by rw bot_union
            ... = (X ∩ Xᶜ) ∪ (X ∩ ⊥) : by rw inter_compl 
            ... = ⊥    : by rw [←inter_distrib_right, union_bot, inter_compl]

lemma bot_inter  (X : A) : ⊥ ∩ X = ⊥ := 
  eq.trans (inter_comm ⊥ X) (inter_bot X)


-- Absorption

@[simp] lemma absorb_union_inter (X Y : A) : X ∪ (X ∩ Y) = X := 
  by calc X ∪ (X ∩ Y) = (X ∩ ⊤) ∪ (X ∩ Y) : by rw inter_top  ... = X : by rw [←inter_distrib_right, union_comm, union_top, inter_top ]

@[simp] lemma absorb_inter_union (X Y : A) : X ∩ (X ∪ Y) = X := 
  by calc X ∩ (X ∪ Y) = (X ∪ ⊥) ∩ (X ∪ Y) : by rw union_bot ... = X : by rw [←union_distrib_right, inter_comm, inter_bot, union_bot]


-- Size 

lemma size_modular (X Y : A) : size (X ∪ Y) + size (X ∩ Y) = size (X) + size Y := A.size_modular_ax X Y

lemma size_bot (A : fin_bool_alg) : size (⊥ : A) = 0 := 
  A.size_bot_ax

lemma size_singleton (X : A) : (1 < size X) → (∃ (Y : A), (X ∩ Y = Y) ∧ (0 < size Y) ∧ (size Y < size X)) := 
  A.size_singleton_ax X 

lemma size_nonneg (X : A) : 0 ≤ size X := 
  A.size_nonneg_ax X 

-- Subsets 

lemma subset_refl (X : A) : X ⊆ X :=
  by unfold has_subset.subset; rw inter_idem 

lemma inter_subset_iff (X Y: A) : (X ⊆ Y) ↔ (X ∩ Y = X) :=
  by split; apply eq.symm; tidy; rw a; tidy 

lemma union_subset_iff (X Y : A) : (X ⊆ Y) ↔ (X ∪ Y = Y) := 
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

lemma inter_subset  {X Y : A} (hXY : X ⊆ Y) : X ∩ Y = X := 
  (inter_subset_iff X Y).mp hXY

lemma union_subset  {X Y : A} (hXY : X ⊆ Y) : X ∪ Y = Y :=
  (union_subset_iff X Y).mp hXY


lemma ss_antisymm  {X Y : A} (hXY : X ⊆ Y) (hYX : Y ⊆ X) : X = Y := 
  by unfold has_subset.subset at hXY hYX; calc X = X ∩ Y : hXY ... = Y ∩ X : inter_comm X Y ... = Y : by rw ← hYX

lemma inter_subset_left {A: fin_bool_alg} (X Y : A) : (X ∩ Y) ⊆ X := 
  by apply (union_subset_iff (X ∩ Y) X).mpr; rw union_comm (X ∩ Y) X; apply absorb_union_inter

lemma inter_subset_right (X Y : A) : (X ∩ Y) ⊆ Y := 
  by apply (union_subset_iff (X ∩ Y) Y).mpr; rw [union_comm,inter_comm X Y]; apply absorb_union_inter

lemma subset_union_left (X Y : A) : X ⊆ X ∪ Y := 
  by unfold has_subset.subset; exact (absorb_inter_union X Y).symm 

lemma subset_union_right (X Y : A) : Y ⊆ X ∪ Y := 
  by rw union_comm; exact subset_union_left Y X
   
lemma subset_top (X : A) : X ⊆ ⊤ := 
  by unfold has_subset.subset; exact eq.symm (inter_top  X)

lemma top_subset  {X : A} (hX : ⊤ ⊆ X) : X = ⊤ := 
  ss_antisymm (subset_top X) hX

lemma bot_subset  (X : A) : ⊥ ⊆ X := 
  by unfold has_subset.subset; exact eq.symm (bot_inter X)

lemma subset_bot  {X : A} (hX : X ⊆ ⊥) : X = ⊥ := 
  ss_antisymm hX (bot_subset X)  


lemma disjoint_compl_subset  {X Y : A} (hXY: X ∩ Y = ⊥) : X ⊆ Yᶜ := 
begin
  apply eq.symm, 
  calc X ∩ Yᶜ = ⊥ ∪ (X ∩ Yᶜ)       : (bot_union _).symm 
          ... = (X ∩ Y) ∪ (X ∩ Yᶜ) : by rw ←hXY
          ... = X ∩ (Y ∪ Yᶜ)       : (inter_distrib_right _ _ _).symm 
          ... = X ∩ ⊤              : by rw (union_compl Y)
          ... = X                  : inter_top  X, 
end

lemma cover_compl_subset {A: fin_bool_alg} {X Y : A} (hXY: X ∪ Y = ⊤) : Xᶜ ⊆ Y  := 
begin
  apply (union_subset_iff Xᶜ Y).mpr, 
  calc Xᶜ ∪ Y = ⊤ ∩ (Xᶜ ∪ Y)        : (top_inter _).symm 
          ... = (X ∪ Y) ∩ (Xᶜ ∪ Y)  : by rw ←hXY
          ... = (X ∩ Xᶜ) ∪ Y        : (union_distrib_left _ _ _).symm 
          ... = ⊥ ∪ Y               : by rw inter_compl
          ... = Y                   : bot_union Y,
end
 
lemma compl_unique {X Y : A} (hU : X ∪ Y = ⊤) (hI : X ∩ Y = ⊥) : Y = Xᶜ := 
begin
  apply ss_antisymm,
  exact disjoint_compl_subset (eq.trans (inter_comm Y X) hI),
  exact cover_compl_subset hU, 
end 


@[simp] lemma compl_compl  (X : A) : Xᶜᶜ = X := 
begin
  apply ss_antisymm,
  apply cover_compl_subset, 
  exact eq.trans (union_comm Xᶜ X) (union_compl X), 
  exact disjoint_compl_subset (inter_compl X),
end


lemma compl_top (A : fin_bool_alg) : (⊤ : A)ᶜ = ⊥ := 
  eq.symm (compl_unique (top_union ⊥) (inter_bot ⊤))

lemma compl_bot (A : fin_bool_alg) : (⊥ : A)ᶜ = ⊤ := 
  eq.symm (compl_unique (union_top ⊥) (bot_inter ⊤)) 
  
lemma union_compl_union  (X Y : A) : X ∪ (Xᶜ ∪ Y) = ⊤ :=  
  by rw [←top_inter(X ∪ (Xᶜ ∪ Y)), ←union_compl, ←union_distrib_right, absorb_inter_union] 

lemma inter_compl_inter (X Y : A) : X ∩ (Xᶜ ∩ Y) = ⊥ := 
  by rw [←bot_union(X ∩ (Xᶜ ∩ Y)), ←inter_compl, ←inter_distrib_right, absorb_union_inter]

lemma union_inter_compl_inter (X Y : A) : (X ∪ Y) ∪ (Xᶜ ∩ Yᶜ)  = ⊤ := 
  begin
    rw [union_distrib_right, union_comm _ Xᶜ, union_comm X Y, union_comm _ Yᶜ, ←(compl_compl Y)],
    rw [compl_compl Yᶜ, union_compl_union Yᶜ, union_comm _ X, ←(compl_compl X), compl_compl Xᶜ, union_compl_union Xᶜ, inter_idem],
  end

lemma inter_union_compl_union (X Y : A) : (X ∩ Y) ∩ (Xᶜ ∪ Yᶜ)  = ⊥ := 
  begin
    rw [inter_distrib_right, inter_comm _ Xᶜ, inter_comm X Y, inter_comm _ Yᶜ, ←(compl_compl Y)],
    rw [compl_compl Yᶜ, inter_compl_inter Yᶜ, inter_comm _ X, ←(compl_compl X), compl_compl Xᶜ, inter_compl_inter Xᶜ, union_idem],
  end

lemma inter_union_compl_inter (X Y : A) : (X ∪ Y) ∩ (Xᶜ ∩ Yᶜ) = ⊥ := 
  by rw [inter_distrib_left X Y, inter_compl_inter, inter_comm Xᶜ, inter_compl_inter, union_idem]
  
lemma union_inter_compl_union  (X Y : A) : (X ∩ Y) ∪ (Xᶜ ∪ Yᶜ) = ⊤ := 
  by rw [union_distrib_left X Y, union_compl_union, union_comm Xᶜ, union_compl_union, inter_idem]

lemma compl_inter (X Y : A) : (X ∩ Y)ᶜ = Xᶜ ∪ Yᶜ := 
  eq.symm (compl_unique (union_inter_compl_union X Y) (inter_union_compl_union X Y))

lemma compl_union (X Y : A) : (X ∪ Y)ᶜ = Xᶜ ∩ Yᶜ := 
  eq.symm (compl_unique (union_inter_compl_inter X Y) (inter_union_compl_inter X Y))

lemma compl_partition (X Y : A) : (X ∩ Y) ∪ (Xᶜ ∩ Y) = Y := 
  by rw [←inter_distrib_left, union_compl, top_inter]

lemma compl_partition_subset  {X Y : A} (hXY : X ⊆ Y) :
  X ∪ (Xᶜ ∩ Y) = Y := 
  by nth_rewrite 0 ←(inter_subset hXY); exact compl_partition X Y
  


-- Associativity (In fact, this can be discarded eventually : WIP)

lemma inter_assoc (X Y Z : A) : (X ∩ Y) ∩ Z = X ∩ (Y ∩ Z) := 
  A.inter_assoc_ax X Y Z 

lemma union_assoc (X Y Z : A) : (X ∪ Y) ∪ Z = X ∪ (Y ∪ Z) := 
  A.union_assoc_ax X Y Z 

lemma compl_subset {X Y : A} (hXY : X ⊆ Y) : Yᶜ ⊆ Xᶜ := 
begin
  apply eq.symm, 
  rw inter_subset_iff at hXY, 
  rw [←hXY, compl_inter, union_comm], 
  apply absorb_inter_union,
end 

-- Self-Distributivity

lemma inter_distrib_inter_left (X Y Z : A) : (X ∩ Y) ∩ Z = (X ∩ Z) ∩ (Y ∩ Z) := 
  by rw [inter_assoc X Z, inter_comm Z, inter_assoc Y, inter_idem, inter_assoc]  


lemma union_distrib_union_left (X Y Z : A) : (X ∪ Y) ∪ Z = (X ∪ Z) ∪ (Y ∪ Z) := 
  by rw [union_assoc X Z, union_comm Z, union_assoc Y, union_idem, union_assoc]

lemma union_distrib_union_right (X Y Z : A) : X ∪ (Y ∪ Z) = (X ∪ Y) ∪ (X ∪ Z) := 
  by rw [union_comm X, union_distrib_union_left Y Z X, union_comm X, union_comm X]   





lemma inter_is_lb  (X Y Z : A) : Z ⊆ X → Z ⊆ Y → Z ⊆ (X ∩ Y) := 
begin
  unfold has_subset.subset,
  intros hZX hZY, 
  calc Z = Z ∩ Y        : hZY
  ...    = (Z ∩ X) ∩ Y  : by rw ← hZX
  ...    = Z ∩ (X ∩ Y)  : inter_assoc Z X Y, 
end 

lemma union_is_ub  (X Y Z : A) : X ⊆ Z → Y ⊆ Z → X ∪ Y ⊆ Z := 
begin
  unfold has_subset.subset, 
  intros hXZ hYZ, 
  calc X ∪ Y = (X ∩ Z) ∪ (Y ∩ Z)    : by rw [←hXZ, ←hYZ]
  ...        = (X ∪ Y) ∩ Z          : by rw inter_distrib_left, 
end

lemma diff_subset  (X Y : A) : X - Y ⊆ X := 
  inter_subset_left X Yᶜ

lemma diff_union (X Y : A): (X ∩ Y) ∪ (Y - X) = Y := 
  by unfold has_sub.sub; rw [inter_comm Y Xᶜ, compl_partition]

lemma diff_union_subset {X Y : A} (hXY : X ⊆ Y) : X ∪ (Y - X) = Y := 
begin
  unfold has_subset.subset at hXY, 
  have := diff_union X Y, 
  rw ← hXY at this, 
  exact this, 
end



lemma diff_inter (X Y : A) : X ∩ (Y - X) = ⊥ := 
begin
  unfold has_sub.sub, 
  rw [←inter_assoc, inter_comm X Y, inter_assoc, inter_compl ,inter_bot],
end

lemma size_monotone {X Y: A} (hXY : X ⊆ Y) : size X ≤ size Y := 
begin
  have := size_modular X (Y-X), 
  rw diff_union_subset hXY at this, 
  rw diff_inter at this, 
  linarith [size_nonneg(Y-X), size_bot A],
end

lemma size_subadditive {X Y : A} : size (X ∪ Y) ≤ size X + size Y :=
  by linarith [size_modular X Y, size_nonneg (X ∩ Y)] 

lemma size_disjoint_sum {X Y : A} (hXY: X ∩ Y = ⊥) : size (X ∪ Y) = size X + size Y := 
begin
  have := size_modular X Y, 
  rw [hXY, size_bot] at this, 
  linarith, -- for some reason 'ring' doesn't work here. I don't know why.  
end

lemma size_compl_sum (X : A) : size X + size Xᶜ = size (⊤ : A) := 
begin
  have := size_disjoint_sum (inter_compl X),
  rw (union_compl X) at this, 
  linarith, 
end 

lemma compl_inter_size (X Y : A) : size (X ∩ Y) + size (Xᶜ ∩ Y) = size Y := 
    by rw [←size_modular, ←inter_distrib_left, union_compl, top_inter, ←inter_distrib_inter_left, inter_compl, bot_inter, size_bot]; ring


lemma compl_inter_size_subset {X Y : A} (hXY : X ⊆ Y) : size (Xᶜ ∩ Y) = size Y - size X := 
begin
    have := compl_inter_size X Y, 
    rw hXY.symm at this, 
    linarith, 
end

lemma diff_size {X Y : A} (hXY : X ⊆ Y) : size (Y - X) = size Y - size X :=  
begin 
    unfold has_sub.sub, 
    rw inter_comm, 
    exact compl_inter_size_subset hXY, 
end  

-- more subsets 

lemma subset_trans {X Y Z : A} (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) : X ⊆ Z :=
  by unfold has_subset.subset at *; rw [hXY, inter_assoc, ←hYZ]
  
lemma union_of_subsets (X Y Z : A) : (X ⊆ Z) → (Y ⊆ Z) → (X ∪ Y ⊆ Z) := 
  begin
    unfold has_subset.subset, 
    intros hXZ hYZ, 
    calc X ∪ Y = (X ∩ Z) ∪ (Y ∩ Z) : by rw [←hXZ, ←hYZ] 
           ... = (X ∪ Y) ∩ Z : by rw inter_distrib_left, 
  end

lemma inter_of_supsets (X Y Z : A) : (X ⊆ Y) → (X ⊆ Z) → (X ⊆ Y ∩ Z) := 
  begin
    intros hXY hXZ, 
    unfold has_subset.subset at *,
    calc X = X ∩ Z       : by rw ←hXZ
      ...  = (X ∩ Y) ∩ Z : by rw ←hXY
      ...  = X ∩ (Y ∩ Z) : inter_assoc _ _ _, 
  end 


lemma inter_of_subsets (X Y Z : A) : (X ⊆ Z) → (X ∩ Y ⊆ Z) := 
  by intros h; exact subset_trans (inter_subset_left X Y) h

lemma union_of_supsets (X Y Z : A) : (X ⊆ Y) → (X ⊆ Y ∪ Z) := 
  by intros h; exact subset_trans h (subset_union_left Y Z)

lemma subset_inter_subset_left (X Y Z : A) : (X ⊆ Y) → (X ∩ Z) ⊆ (Y ∩ Z) := 
begin
  unfold has_subset.subset, 
  intro hXY, 
  rw [←inter_distrib_inter_left, ←hXY],
end

lemma subset_union_subset_left (X Y Z : A) : (X ⊆ Y) → (X ∪ Z) ⊆ (Y ∪ Z) := 
begin
  rw union_subset_iff _ _, 
  rw union_subset_iff _ _, 
  intros hXY, 
  rw [←union_distrib_union_left, hXY], 
end

lemma in_between {X Y : A} : (X ⊆ Y) ∧ (X ≠ Y) → (∀ Z, (X ⊆ Z ∧ Z ⊆ Y) → (Z = X ∨ Z = Y)) → size Y - size X = 1 := 
  begin
    intros hZ,
    let S := Y-X, 
    sorry, 
  end

section embedding

structure fin_bool_alg.embedding (A B : fin_bool_alg) :=
  (func : A → B)

  (on_inter (X Y : A) : func (X ∩ Y) = (func X) ∩ (func Y))
  (on_union (X Y : A) : func (X ∪ Y) = (func X) ∪ (func Y))
  (on_size (X Y : A) : size X - size Y = size (func X) - size (func Y))

end /- section -/ embedding

def fin_bool_alg.canonical (size : ℤ) :
  (0 ≤ size) → fin_bool_alg := sorry

-- Construct a fin_bool_alg from a finite set S 

def power_set_alg {γ : Type} [decidable_eq γ] (S : finset γ) : fin_bool_alg := {

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
    intros X hX, 
    have X_nonempty : X.val.nonempty, by apply (finset.card_pos).mp; linarith,  
    cases finset.nonempty.bex X_nonempty with x hx, 
    use {x},
    tidy, 
  end, 

  inter_comm_ax := by tidy, 
  union_comm_ax := by intros X Y; simp_rw finset.union_comm; trivial, 
  inter_assoc_ax := by intros X Y Z; cases Z; cases Y; cases X; dsimp at *; simp at *, 
  union_assoc_ax := by intros X Y Z; cases Z; cases Y; cases X; dsimp at *; simp at *,
  union_distrib_left_ax := by intros _ _ _; apply subtype.eq; simp_rw finset.union_distrib_left; exact finset.union_distrib_right _ _ _,
  inter_distrib_left_ax := by intros _ _ _; apply subtype.eq; simp_rw finset.inter_distrib_left; exact finset.inter_distrib_right _ _ _,  
  inter_top_ax := by tidy, 
  union_bot_ax := by tidy, 
  union_compl_ax := by tidy, 
  inter_compl_ax := by tidy, 
}

-- Algebra of all sets containing S and contained in T
structure interval_alg := 
  (big : fin_bool_alg)
  (S T : big) 
  (hST : S ⊆ T)

def interval_alg.as_fin_bool_alg (small : interval_alg) : fin_bool_alg := 
let A := small.big, S := small.S, T := small.T, hST := small.hST in
{


  subset := {X: A | (S ⊆ X) ∧ (X ⊆ T)},

  bot := ⟨S, ⟨subset_refl S, hST⟩⟩,
  top := ⟨T, ⟨hST, subset_refl T⟩⟩,
  inter := λ (X Y : _), ⟨X.1 ∩ Y.1, ⟨inter_of_supsets S X Y X.2.1 Y.2.1, inter_of_subsets X Y T X.2.2⟩ ⟩, 
  union := λ (X Y : _), ⟨X.1 ∪ Y.1, ⟨union_of_supsets S X Y X.2.1, union_of_subsets X Y T X.2.2 Y.2.2⟩ ⟩,
  size  := λ X, (size (X.1) - size S),
  compl := λ X, ⟨S ∪ (T ∩ (X.1)ᶜ), ⟨by apply subset_union_left S, begin apply union_of_subsets S, exact hST, apply inter_subset_left, end ⟩ ⟩,

  size_bot_ax := by simp only [sub_self],
  size_nonneg_ax := by intros X; linarith [size_monotone (X.2.1)],

  size_modular_ax := by intros X Y; linarith[size_modular X.1 Y.1],
  size_singleton_ax := 
  begin
    sorry,
  end,

  inter_comm_ax := by intros X Y; apply subtype.eq; simp_rw [inter_comm X.1 Y.1], 
  union_comm_ax := by intros X Y; apply subtype.eq; simp_rw [union_comm X.1 Y.1],
  inter_assoc_ax := by tidy; apply inter_assoc,
  union_assoc_ax := by tidy; apply union_assoc,
  union_distrib_left_ax := by tidy; apply union_distrib_left,
  inter_distrib_left_ax := by tidy; apply inter_distrib_left,
  inter_top_ax := by intros X; cases X; cases X_property; simp only [subtype.mk_eq_mk]; solve_by_elim,
  union_bot_ax := by intros X; cases X; cases X_property; simp only [subtype.mk_eq_mk]; unfold has_subset.subset at *; rw [X_property_left, inter_comm S, absorb_union_inter],
  union_compl_ax := 
  begin
     intros X, 
     cases X, cases X_property, simp only [subtype.mk_eq_mk],
     have := union_subset X_property_left,
     rw union_comm at this, 
     rw [←union_assoc, this, inter_comm, compl_partition_subset X_property_right],
  end,
  inter_compl_ax := 
  begin
    intros X, cases X, cases X_property, simp only [subtype.mk_eq_mk], 
    have hi := inter_subset X_property_left,
    rw inter_comm at hi,
    rw [inter_distrib_right, hi, inter_comm T, ←inter_assoc, inter_compl, bot_inter, union_bot], 
  end,
}

def interval_alg.embedding (small : interval_alg) : small.as_fin_bool_alg.embedding small.big :=
{
  func := (λ X, X.val),
  on_inter := (λ X Y, rfl), 
  on_union := (λ X Y, rfl), 
  on_size := 
  begin
     intros X Y, 
     calc size X - size Y = (size X.val - size small.S) - (size Y.val - size small.S) : by refl
     ... = size X.val - size Y.val : by linarith, 
  end,
} 

/-@[simp] lemma interval_alg_inter  {S T : A} (hST : S ⊆ T) (X Y : interval_alg A S T hST):
  (X ∩ Y).val = X.val ∩ Y.val := rfl 

@[simp] lemma interval_alg_union  {S T : A} (hST : S ⊆ T) (X Y : interval_alg A S T hST):
  (X ∪ Y).val = X.val ∪ Y.val := rfl 

@[simp] lemma interval_alg_subset  {S T : A} (hST : S ⊆ T) (X Y : interval_alg A S T hST): 
  X ⊆ Y ↔ X.val ⊆ Y.val := 
  begin
    unfold has_subset.subset,
    split, 
    intros hXY, nth_rewrite 0 hXY, apply interval_alg_inter, 
    intros hXY, rw ←interval_alg_inter at hXY, exact subtype.eq hXY,   
  end 

lemma interval_alg_injective  {S T S' T' : A} {hST : S ⊆ T} {hST' : S' ⊆ T'} :
  (interval_alg A S T hST = interval_alg A S' T' hST') → (S = S' ∧ T = T')  := 
  begin
    intros hA, 
    split,
    injections_and_clear,

    have : (interval_alg A S T hST).subset = (interval_alg A S' T' hST').subset := by rw ←hA,
    have : S == S' := begin
      apply eq_rec_heq,

    end,
    have : (interval_alg A S T hST).bot.val = (interval_alg A S' T' hST').bot.val := begin 
      congr,
      funext,
      apply propext,
      
      sorry,
      exact hA
    end

  end


def sub_alg (A : fin_bool_alg) (new_top : A) : fin_bool_alg :=
  interval_alg A (⊥ : A) new_top (sorry : (⊥ :A ) ⊆ new_top)

@[simp] lemma sub_alg_size  {T : A} (X : sub_alg A T) : 
  size X = size X.val :=
  begin
    unfold size, 
    have : A.size ⊥ = 0 := A.size_bot_ax,
    exact ( by linarith : A.size X.val - A.size ⊥ =  A.size X.val), 
  end

@[simp] lemma sub_alg_subset  {T : A} {X Y : sub_alg A T} : 
  X ⊆ Y ↔ X.val ⊆ Y.val := 
  by simp only [interval_alg_subset]-/



end fin_bool_alg
end API 
import tactic.ext
--import tactic.ring 
import tactic.linarith
import tactic.tidy 

-- The API I would like to use for various basic objects.
-- This probably belongs in its own file by this point. 

local attribute [instance] classical.prop_decidable

section API


namespace boolalg 

structure boolalg :=
  (subset : Type)
  --(contained : subset → subset → Prop)
  (bot top : subset)
  (inter union : subset → subset → subset)
  (compl : subset → subset)
  (size : subset → ℤ)

  (size_bot_ax : size bot = 0)
  (size_nonneg_ax (X: subset) : 0 ≤ size X) 
  (size_modular_ax (X Y: subset) : size (union X Y) + size (inter X Y) = size X + size Y)
  (size_singleton_ax (X : subset) : (X ≠ bot) → (∀(Y Z : subset), (X = inter X (union Y Z)) → ((X = inter X Y) ∨ (X = inter X Z))) → size X = 1 )
  --(1 < size X) → (∃ (Y : subset), (inter X Y = Y) ∧ (0 < size Y) ∧ (size Y < size X)))

  (inter_comm_ax (X Y : subset) : inter X Y = inter Y X)
  (union_comm_ax (X Y : subset) : union X Y = union Y X)
  
  (union_distrib_right_ax (X Y Z : subset) : union (inter X Y) Z = inter (union X Z) (union Y Z))
  (inter_distrib_right_ax (X Y Z : subset) : inter (union X Y) Z = union (inter X Z) (inter Y Z))

  (inter_top_ax (X : subset) : inter X top = X)
  (union_bot_ax (X : subset) : union X bot = X)

  (union_compl_ax (X: subset) : union X (compl X) = top)
  (inter_compl_ax (X: subset) : inter X (compl X) = bot)

-- associativity axioms can be removed - WIP
  (inter_assoc_ax (X Y Z : subset) : inter (inter X Y) Z = inter X (inter Y Z))
  (union_assoc_ax (X Y Z : subset) : union (union X Y) Z = union X (union Y Z))

-- Instances to enable ⊆ , ∩ , ∪ , ᶜ , ⊤, ⊥ , - (set diff)



variables {A : boolalg}


@[simp] instance i1  : has_coe_to_sort boolalg := {S := Type, coe := boolalg.subset}
@[simp] instance i2  : has_bot A := {bot := A.bot}
@[simp] instance i3  : has_top A := {top := A.top}
@[simp] instance i4  : has_inter A := {inter := A.inter}
@[simp] instance i5  : has_union A := {union := A.union}
@[simp] instance i6  : has_compl A := {compl := A.compl}
@[simp] instance i7  : has_subset A := {subset := λ (X Y), (X = X ∩ Y)} 
@[simp] instance i8  : has_sub A := {sub := λ (X Y), X ∩ Yᶜ}

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

lemma union_bot {A : boolalg} (X : A) : X ∪ ⊥ = X := A.union_bot_ax X 

lemma bot_union {A : boolalg} (X : A) : 
  ⊥ ∪ X = X := 
  eq.trans (union_comm ⊥ X) (union_bot X)


-- Complements

lemma union_compl {A: boolalg} (X: A) : 
  X ∪ Xᶜ = ⊤ := 
  A.union_compl_ax X 

lemma inter_compl {A: boolalg} (X: A) : X ∩ Xᶜ = ⊥ := A.inter_compl_ax X 



-- Distributivity

lemma union_distrib_right {A : boolalg} (X Y Z : A) : (X ∩ Y) ∪ Z = (X ∪ Z) ∩ (Y ∪ Z) := A.union_distrib_right_ax X Y Z

lemma union_distrib_left {A : boolalg} (X Y Z : A) : X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z) := 
  by calc X ∪ (Y ∩ Z) = (Y ∩ Z) ∪ X       : union_comm X (Y ∩ Z) 
                  ... = (Y ∪ X) ∩ (Z ∪ X) : union_distrib_right Y Z X  
                  ... = (X ∪ Y) ∩ (X ∪ Z) : by rw [union_comm X Y, union_comm X Z]

lemma inter_distrib_right {A : boolalg} (X Y Z : A) : (X ∪ Y) ∩ Z = (X ∩ Z) ∪ (Y ∩ Z) := A.inter_distrib_right_ax X Y Z

lemma inter_distrib_left {A : boolalg} (X Y Z : A) : X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z) := 
  by calc X ∩ (Y ∪ Z) = (Y ∪ Z) ∩ X       : inter_comm X (Y ∪ Z) 
      ...             = (Y ∩ X) ∪ (Z ∩ X) : inter_distrib_right Y Z X
      ...             = (X ∩ Y) ∪ (X ∩ Z) : by rw [inter_comm X Y, inter_comm X Z]

-- Building things up from a minimal axiom set for fun

lemma bot_unique (X : A) : (∀ (Y: A), Y ∪ X = Y) → X = ⊥ := 
  by intros hX; calc X = ⊥ ∪ X : (bot_union X).symm ... = ⊥ : hX ⊥

lemma top_unique (X : A) : (∀ (Y: A), Y ∩ X = Y) → X = ⊤ := 
  by intros hX; calc X = ⊤ ∩ X : (top_inter X).symm ... = ⊤ : hX ⊤ 



-- Idempotence

lemma union_idem (X : A) : X ∪ X = X := 
  by rw [←(inter_top  (X ∪ X)), ←(union_compl X), ←(union_distrib_left X X Xᶜ), inter_compl, union_bot]

lemma inter_idem (X : A): X ∩ X = X := 
  by rw [←(union_bot (X ∩ X)), ←(inter_compl X), ←(inter_distrib_left X X Xᶜ), union_compl, inter_top ]

lemma union_top  (X : A) : X ∪ ⊤ = ⊤ := 
  by calc X ∪ ⊤ = ⊤ ∩ (X ∪ ⊤)        : by rw top_inter
            ... = (X ∪ Xᶜ) ∩ (X ∪ ⊤) : by rw union_compl 
            ... = ⊤    : by rw [←union_distrib_left, inter_top , union_compl]

lemma top_union (X : A) : ⊤ ∪ X = ⊤ := 
  eq.trans (union_comm ⊤ X) (union_top X)


lemma inter_bot  (X : A) : X ∩ ⊥ = ⊥ := 
  by calc X ∩ ⊥ = ⊥ ∪ (X ∩ ⊥)        : by rw bot_union
            ... = (X ∩ Xᶜ) ∪ (X ∩ ⊥) : by rw inter_compl 
            ... = ⊥    : by rw [←inter_distrib_left, union_bot, inter_compl]

lemma bot_inter  (X : A) : ⊥ ∩ X = ⊥ := 
  eq.trans (inter_comm ⊥ X) (inter_bot X)


-- Absorption

@[simp] lemma absorb_union_inter (X Y : A) : X ∪ (X ∩ Y) = X := 
  by calc X ∪ (X ∩ Y) = (X ∩ ⊤) ∪ (X ∩ Y) : by rw inter_top  ... = X : by rw [←inter_distrib_left, union_comm, union_top, inter_top ]

@[simp] lemma absorb_inter_union (X Y : A) : X ∩ (X ∪ Y) = X := 
  by calc X ∩ (X ∪ Y) = (X ∪ ⊥) ∩ (X ∪ Y) : by rw union_bot ... = X : by rw [←union_distrib_left, inter_comm, inter_bot, union_bot]


-- Size 

lemma size_modular (X Y : A) : size (X ∪ Y) + size (X ∩ Y) = size (X) + size Y := A.size_modular_ax X Y

lemma size_bot (A : boolalg) : size (⊥ : A) = 0 := 
  A.size_bot_ax


lemma size_nonneg (X : A) : 0 ≤ size X := 
  A.size_nonneg_ax X 

-- Subsets 

lemma subset_refl (X : A) : X ⊆ X :=
  by unfold has_subset.subset; rw inter_idem 

@[simp] lemma inter_subset_iff (X Y: A) : (X ⊆ Y) ↔ (X ∩ Y = X) :=
  by split; apply eq.symm; tidy; rw a; tidy 

@[simp] lemma union_subset_iff (X Y : A) : (X ⊆ Y) ↔ (X ∪ Y = Y) := 
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

lemma inter_subset_left {A: boolalg} (X Y : A) : (X ∩ Y) ⊆ X := 
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
          ... = X ∩ (Y ∪ Yᶜ)       : (inter_distrib_left _ _ _).symm 
          ... = X ∩ ⊤              : by rw (union_compl Y)
          ... = X                  : inter_top  X, 
end

lemma cover_compl_subset {A: boolalg} {X Y : A} (hXY: X ∪ Y = ⊤) : Xᶜ ⊆ Y  := 
begin
  apply (union_subset_iff Xᶜ Y).mpr, 
  calc Xᶜ ∪ Y = ⊤ ∩ (Xᶜ ∪ Y)        : (top_inter _).symm 
          ... = (X ∪ Y) ∩ (Xᶜ ∪ Y)  : by rw ←hXY
          ... = (X ∩ Xᶜ) ∪ Y        : (union_distrib_right _ _ _).symm 
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


lemma compl_top (A : boolalg) : (⊤ : A)ᶜ = ⊥ := 
  eq.symm (compl_unique (top_union ⊥) (inter_bot ⊤))

lemma compl_bot (A : boolalg) : (⊥ : A)ᶜ = ⊤ := 
  eq.symm (compl_unique (union_top ⊥) (bot_inter ⊤)) 
  
lemma union_compl_union  (X Y : A) : X ∪ (Xᶜ ∪ Y) = ⊤ :=  
  by rw [←top_inter(X ∪ (Xᶜ ∪ Y)), ←union_compl, ←union_distrib_left, absorb_inter_union] 

lemma inter_compl_inter (X Y : A) : X ∩ (Xᶜ ∩ Y) = ⊥ := 
  by rw [←bot_union(X ∩ (Xᶜ ∩ Y)), ←inter_compl, ←inter_distrib_left, absorb_union_inter]

lemma union_inter_compl_inter (X Y : A) : (X ∪ Y) ∪ (Xᶜ ∩ Yᶜ)  = ⊤ := 
  begin
    rw [union_distrib_left, union_comm _ Xᶜ, union_comm X Y, union_comm _ Yᶜ, ←(compl_compl Y)],
    rw [compl_compl Yᶜ, union_compl_union Yᶜ, union_comm _ X, ←(compl_compl X), compl_compl Xᶜ, union_compl_union Xᶜ, inter_idem],
  end

lemma inter_union_compl_union (X Y : A) : (X ∩ Y) ∩ (Xᶜ ∪ Yᶜ)  = ⊥ := 
  begin
    rw [inter_distrib_left, inter_comm _ Xᶜ, inter_comm X Y, inter_comm _ Yᶜ, ←(compl_compl Y)],
    rw [compl_compl Yᶜ, inter_compl_inter Yᶜ, inter_comm _ X, ←(compl_compl X), compl_compl Xᶜ, inter_compl_inter Xᶜ, union_idem],
  end

lemma inter_union_compl_inter (X Y : A) : (X ∪ Y) ∩ (Xᶜ ∩ Yᶜ) = ⊥ := 
  by rw [inter_distrib_right X Y, inter_compl_inter, inter_comm Xᶜ, inter_compl_inter, union_idem]
  
lemma union_inter_compl_union  (X Y : A) : (X ∩ Y) ∪ (Xᶜ ∪ Yᶜ) = ⊤ := 
  by rw [union_distrib_right X Y, union_compl_union, union_comm Xᶜ, union_compl_union, inter_idem]

lemma compl_inter (X Y : A) : (X ∩ Y)ᶜ = Xᶜ ∪ Yᶜ := 
  eq.symm (compl_unique (union_inter_compl_union X Y) (inter_union_compl_union X Y))

lemma compl_union (X Y : A) : (X ∪ Y)ᶜ = Xᶜ ∩ Yᶜ := 
  eq.symm (compl_unique (union_inter_compl_inter X Y) (inter_union_compl_inter X Y))

lemma compl_partition (X Y : A) : (X ∩ Y) ∪ (Xᶜ ∩ Y) = Y := 
  by rw [←inter_distrib_right, union_compl, top_inter]

lemma compl_partition_subset  {X Y : A} (hXY : X ⊆ Y) :
  X ∪ (Xᶜ ∩ Y) = Y := 
  by nth_rewrite 0 ←(inter_subset hXY); exact compl_partition X Y
  
lemma size_singleton (X : A) : (∀(Y Z : A), (X ⊆ Y ∪ Z) → (X ⊆ Y ∨ X ⊆ Z)) → size X = 1 := 
  begin
    intros h, apply A.size_singleton_ax, intros Y Z hYZ,
    have := h Y Z ((inter_subset_iff X (Y ∪ Z)).mpr hYZ.symm), 
    rw inter_subset_iff at this, rw inter_subset_iff at this,
    cases this, 
    left, exact this.symm, 
    right, exact this.symm,  -- this proof is terrible; probably should be one-liner. 
  end


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
  ...        = (X ∪ Y) ∩ Z          : by rw inter_distrib_right, 
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
    by rw [←size_modular, ←inter_distrib_right, union_compl, top_inter, ←inter_distrib_inter_left, inter_compl, bot_inter, size_bot]; ring


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
           ... = (X ∪ Y) ∩ Z : by rw inter_distrib_right, 
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

--- Embeddings of interval algebras (probably deprecated)

structure interval_embedding (A B : boolalg) :=
  (func : A → B)

  (on_inter (X Y : A) : func (X ∩ Y) = (func X) ∩ (func Y))
  (on_union (X Y : A) : func (X ∪ Y) = (func X) ∪ (func Y))
  (on_size (X Y : A) : size X - size Y = size (func X) - size (func Y))

lemma bot_to_bot_interval_embedding_size {A B : boolalg} (emb : interval_embedding A B) (h_bot : emb.func (⊥ : A) = (⊥ : B)) (X : A) : 
  size X = size (emb.func X) :=  
  begin
    have := emb.on_size X ⊥,
    rw [@size_bot A, h_bot, @size_bot B] at this, 
    linarith, 
  end

lemma interval_embedding_on_subset {A B : boolalg} (emb : interval_embedding A B) {X Y : A} (hXY : X ⊆ Y) : 
  emb.func X ⊆ emb.func Y := 
  by rw inter_subset_iff at *; rw [←emb.on_inter, hXY]

-- Embedding and subalgebras 


structure embed (A B : boolalg) :=
  (f : A → B)
  (on_bot : f ⊥ = ⊥)
  -- note : top is not respected by embedding
  (on_inter (X Y) : f (X ∩ Y) = (f X) ∩ (f Y))
  (on_union (X Y) : f (X ∪ Y) = (f X) ∪ (f Y))
  -- note : compl is not respected by embedding
  (on_size (X : A) : size X = size (f X))

lemma embed.on_subset {A B : boolalg} (emb : embed A B) {X Y : A} :
  (X ⊆ Y) → (emb.f X) ⊆ (emb.f Y) := 
  λ hXY, by rw inter_subset_iff at *; rw [←emb.on_inter, hXY]

def subalg (ground : A) : boolalg := 
{ 
  subset := {X : A | X ⊆ ground},
  bot := ⟨⊥, bot_subset ground⟩,
  top := ⟨ground, subset_refl ground⟩,
  inter := λ X Y, ⟨X.val ∩ Y.val, inter_of_subsets X.val Y.val ground X.property⟩,
  union := λ X Y, ⟨X.val ∪ Y.val, union_of_subsets X.val Y.val ground X.property Y.property⟩,
  compl := λ X, ⟨ground - X.val, diff_subset ground X.val⟩,
  size := λ X, size X.val, 
  size_bot_ax := @size_bot A, 
  size_nonneg_ax := λ X, size_nonneg X.val,
  size_modular_ax := λ X Y, size_modular X.val Y.val, 
  size_singleton_ax := sorry,
  inter_comm_ax := λ X Y, subtype.eq (inter_comm X.val Y.val), 
  union_comm_ax := λ X Y, subtype.eq (union_comm X.val Y.val),
  union_distrib_right_ax := λ X Y Z, subtype.eq (union_distrib_right X Y Z),
  inter_distrib_right_ax := λ X Y Z, subtype.eq (inter_distrib_right X Y Z),
  inter_top_ax := by intros X; cases X; simp only [subtype.mk_eq_mk]; exact inter_subset X_property,
  union_bot_ax := by intros X; cases X; simp only [subtype.mk_eq_mk]; apply union_bot, 
  union_compl_ax := sorry,
  inter_compl_ax := sorry,
  inter_assoc_ax := sorry,
  union_assoc_ax := sorry
}



instance embed.coe_to_fun {A B : boolalg.boolalg} : has_coe_to_fun (boolalg.embed A B) := {
  F := (λ _, A → B),
  coe := sorry,
}
def subalg.embed {E : A} : boolalg.embed (subalg E) A := sorry








def boolalg.canonical (size : ℤ) :
  (0 ≤ size) → boolalg := sorry

-- Construct a boolalg from a finite set S 

def powersetalg (γ : Type)[fintype γ][decidable_eq γ] : boolalg := 
{ 
  subset := finset γ,
  bot := ∅,
  top := finset.univ,
  inter := λ X Y, X ∩ Y,
  union := λ X Y, X ∪ Y,
  compl := λ X, Xᶜ,
  size := λ X, (X.card : ℤ),
  size_bot_ax := by simp only [finset.card_empty, int.coe_nat_zero],
  size_nonneg_ax := by simp only [forall_const, int.coe_nat_nonneg],
  size_modular_ax := λ X Y, by linarith [finset.card_union_add_card_inter X Y],
  size_singleton_ax := 
  begin
    intros X hbot hX, unfold_coes, 
    sorry, 
    --finset.card_eq_one, 
  end,
  inter_comm_ax := finset.inter_comm,
  union_comm_ax := finset.union_comm,
  inter_distrib_right_ax := finset.inter_distrib_right,
  union_distrib_right_ax := finset.union_distrib_right,
  inter_top_ax := finset.inter_univ, 
  union_bot_ax := finset.union_empty, 
  union_compl_ax := by intros X; rw finset.compl_eq_univ_sdiff; simp only [finset.union_eq_right_iff_subset, finset.union_sdiff_self_eq_union]; intros a a_1; simp only [finset.mem_univ],  
  inter_compl_ax := by intros X; ext1; simp only [finset.not_mem_empty, finset.mem_compl, and_not_self, finset.mem_inter],
  inter_assoc_ax := finset.inter_assoc,
  union_assoc_ax := finset.union_assoc,
}



def power_set_subset_alg {γ : Type} [decidable_eq γ] (S : finset γ) : boolalg := 
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
    sorry, 
  end, 

  inter_comm_ax := by tidy, 
  union_comm_ax := by intros X Y; simp_rw finset.union_comm; trivial, 
  inter_assoc_ax := by intros X Y Z; cases Z; cases Y; cases X; dsimp at *; simp at *, 
  union_assoc_ax := by intros X Y Z; cases Z; cases Y; cases X; dsimp at *; simp at *,
  union_distrib_right_ax := by intros _ _ _; apply subtype.eq; simp_rw finset.union_distrib_right; exact finset.union_distrib_left _ _ _,
  inter_distrib_right_ax := by intros _ _ _; apply subtype.eq; simp_rw finset.inter_distrib_right; exact finset.inter_distrib_left _ _ _,  
  inter_top_ax := by tidy, 
  union_bot_ax := by tidy, 
  union_compl_ax := by tidy, 
  inter_compl_ax := by tidy, 
}

-- Algebra of all sets containing S and contained in T (again, probably deprecated)
structure interval_alg := 
  (big : boolalg)
  (S T : big) 
  (hST : S ⊆ T)

def interval_alg.as_boolalg (small : interval_alg) : boolalg := 
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
  union_distrib_right_ax := by tidy; apply union_distrib_right,
  inter_distrib_right_ax := by tidy; apply inter_distrib_right,
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
    rw [inter_distrib_left, hi, inter_comm T, ←inter_assoc, inter_compl, bot_inter, union_bot], 
  end,
}

def interval_alg.embedding (small : interval_alg) : small.as_boolalg.embedding small.big :=
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

--def sub_alg (R : A) : interval_alg := ⟨A, ⊥, R, (bot_subset R : ⊥ ⊆ R)⟩ 

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


def sub_alg (A : boolalg) (new_top : A) : boolalg :=
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



end boolalg
end API 
import tactic.ext
--import tactic.ring 
import tactic.linarith
import tactic.tidy 
import tactic 

-- The API I would like to use for various basic objects.
-- This probably belongs in its own file by this point. 

local attribute [instance] classical.prop_decidable

section API


namespace boolalg 

structure boolalg :=
  (member : Type)
  --(contained : subset → subset → Prop)
  (bot top : member)
  (inter union : member → member → member)
  (compl : member → member)
  (size : member → ℤ)
  (subset : member → member → Prop)

  (size_bot_ax : size bot = 0)
  (size_nonneg_ax (X: member) : 0 ≤ size X) 
  (size_modular_ax (X Y: member) : size (union X Y) + size (inter X Y) = size X + size Y)
  --(size_singleton_ax (X : member) : (X ≠ bot) → (∀(Y Z : member), (X = inter X (union Y Z)) → ((X = inter X Y) ∨ (X = inter X Z))) → size X = 1 )
  --(1 < size X) → (∃ (Y : member), (inter X Y = Y) ∧ (0 < size Y) ∧ (size Y < size X)))
  (singleton_subset_ax (X : member) : X = bot ∨ ∃ Y Z, inter Y Z = bot ∧ union Y Z = X ∧ size Y = 1)

  (inter_comm_ax (X Y : member) : inter X Y = inter Y X)
  (union_comm_ax (X Y : member) : union X Y = union Y X)
  
  (union_distrib_right_ax (X Y Z : member) : union (inter X Y) Z = inter (union X Z) (union Y Z))
  (inter_distrib_right_ax (X Y Z : member) : inter (union X Y) Z = union (inter X Z) (inter Y Z))

  (inter_top_ax (X : member) : inter X top = X)
  (union_bot_ax (X : member) : union X bot = X)

  (union_compl_ax (X : member) : union X (compl X) = top)
  (inter_compl_ax (X : member) : inter X (compl X) = bot)

  (inter_subset_ax (X Y : member) : subset X Y ↔ inter X Y = X)

-- associativity axioms can be removed - WIP
  (inter_assoc_ax (X Y Z : member) : inter (inter X Y) Z = inter X (inter Y Z))
  (union_assoc_ax (X Y Z : member) : union (union X Y) Z = union X (union Y Z))

-- Instances to enable ⊆ , ∩ , ∪ , ᶜ , ⊤, ⊥ , - (set diff)



variables {A : boolalg}


@[simp] instance i1  : has_coe_to_sort boolalg := {S := Type, coe := boolalg.member}
@[simp] instance i2  : has_bot A := {bot := A.bot}
@[simp] instance i3  : has_top A := {top := A.top}
@[simp] instance i4  : has_inter A := {inter := A.inter}
@[simp] instance i5  : has_union A := {union := A.union}
@[simp] instance i6  : has_compl A := {compl := A.compl}
@[simp] instance i7  : has_subset A := {subset := A.subset} 
@[simp] instance i8  : has_sub A := {sub := λ (X Y), X ∩ Yᶜ}
@[simp] instance i9  : has_ssubset A := {ssubset := λ X Y, X ⊆ Y ∧ X ≠ Y}

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

lemma size_compl (X : A) : size Xᶜ = size (⊤ : A) - size X :=
  calc size Xᶜ = size (X ∪ Xᶜ) + size (X ∩ Xᶜ) - size X : by linarith [size_modular X Xᶜ]
  ...          = size (⊤ : A)  + size (⊥ : A)  - size X : by rw [union_compl X, inter_compl X]
  ...          = size (⊤ : A) - size X                  : by linarith [size_bot A]

lemma size_nonneg (X : A) : 0 ≤ size X := 
  A.size_nonneg_ax X 

lemma singleton_subset (X : A) : X = ⊥ ∨ (∃ Y Z, Y ∩ Z = ⊥ ∧ Y ∪ Z = X ∧ size Y = 1) := 
  sorry --A.singleton_subset_ax X, 

-- Subsets 

lemma subset_refl (X : A) : X ⊆ X :=
  begin unfold has_subset.subset, apply (A.inter_subset_ax X X).mpr, apply inter_idem end 

lemma ssubset_bot (X : A) : ¬ X ⊂ ⊥ := sorry 

@[simp] lemma inter_subset (X Y: A) : (X ⊆ Y) ↔ (X ∩ Y = X) :=
  A.inter_subset_ax X Y 

@[simp] lemma union_subset (X Y : A) : (X ⊆ Y) ↔ (X ∪ Y = Y) := 
begin
  rw inter_subset at *, 
  split, intros h, 
  rw [←h, union_comm, inter_comm X, absorb_union_inter],
  intros h, 
  rw [←h, absorb_inter_union], 
end

lemma inter_subset_mp  {X Y : A} : X ⊆ Y → X ∩ Y = X := 
  (inter_subset X Y).mp 

lemma inter_subset_mpr  {X Y : A} : X ∩ Y = X → X ⊆ Y  := 
  (inter_subset X Y).mpr 

lemma union_subset_mp  {X Y : A} : X ⊆ Y → X ∪ Y = Y :=
  (union_subset X Y).mp

lemma union_subset_mpr {X Y : A} : X ∪ Y = Y → X ⊆ Y := 
  (union_subset X Y).mpr 


lemma subset_antisymm  {X Y : A} (hXY : X ⊆ Y) (hYX : Y ⊆ X) : X = Y := 
  begin rw inter_subset at *, rw inter_comm at hXY, exact (rfl.congr hYX).mp (eq.symm hXY) end 

lemma inter_subset_left {A: boolalg} (X Y : A) : (X ∩ Y) ⊆ X := 
  begin apply union_subset_mpr; rw union_comm; apply absorb_union_inter end 

lemma inter_subset_right (X Y : A) : (X ∩ Y) ⊆ Y := 
  begin rw inter_comm, apply inter_subset_left end 

lemma subset_union_left (X Y : A) : X ⊆ X ∪ Y := 
  begin apply inter_subset_mpr, rw absorb_inter_union end 

lemma subset_union_right (X Y : A) : Y ⊆ X ∪ Y := 
  begin rw union_comm, exact subset_union_left Y X end 
   
lemma subset_top (X : A) : X ⊆ ⊤ := 
  begin apply inter_subset_mpr; exact (inter_top X) end 

lemma top_subset  {X : A} (hX : ⊤ ⊆ X) : X = ⊤ := 
  subset_antisymm (subset_top X) hX

lemma bot_subset  (X : A) : ⊥ ⊆ X := 
  begin apply inter_subset_mpr, exact (bot_inter X) end 

lemma subset_bot  {X : A} (hX : X ⊆ ⊥) : X = ⊥ := 
  subset_antisymm hX (bot_subset X)  


lemma disjoint_compl_subset  {X Y : A} (hXY: X ∩ Y = ⊥) : X ⊆ Yᶜ := 
begin
  apply inter_subset_mpr, 
  calc X ∩ Yᶜ = ⊥ ∪ (X ∩ Yᶜ)       : (bot_union _).symm 
          ... = (X ∩ Y) ∪ (X ∩ Yᶜ) : by rw ←hXY
          ... = X ∩ (Y ∪ Yᶜ)       : (inter_distrib_left _ _ _).symm 
          ... = X ∩ ⊤              : by rw (union_compl Y)
          ... = X                  : inter_top  X, 
end

lemma cover_compl_subset {A: boolalg} {X Y : A} (hXY: X ∪ Y = ⊤) : Xᶜ ⊆ Y  := 
begin
  apply union_subset_mpr, 
  calc Xᶜ ∪ Y = ⊤ ∩ (Xᶜ ∪ Y)        : (top_inter _).symm 
          ... = (X ∪ Y) ∩ (Xᶜ ∪ Y)  : by rw ←hXY
          ... = (X ∩ Xᶜ) ∪ Y        : (union_distrib_right _ _ _).symm 
          ... = ⊥ ∪ Y               : by rw inter_compl
          ... = Y                   : bot_union Y,
end
 
lemma compl_unique {X Y : A} (hU : X ∪ Y = ⊤) (hI : X ∩ Y = ⊥) : Y = Xᶜ := 
  begin apply subset_antisymm, exact disjoint_compl_subset (eq.trans (inter_comm Y X) hI), exact cover_compl_subset hU, end 

@[simp] lemma compl_compl  (X : A) : Xᶜᶜ = X := 
  begin apply subset_antisymm, apply cover_compl_subset, exact eq.trans (union_comm Xᶜ X) (union_compl X), exact disjoint_compl_subset (inter_compl X) end

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

lemma compl_partition_subset  {X Y : A} (hXY : X ⊆ Y) : X ∪ (Xᶜ ∩ Y) = Y := 
  begin nth_rewrite 0 ←(inter_subset_mp hXY), exact compl_partition X Y end 
  

-- Associativity (In fact, this can be discarded eventually : WIP)

lemma inter_assoc (X Y Z : A) : (X ∩ Y) ∩ Z = X ∩ (Y ∩ Z) := 
  A.inter_assoc_ax X Y Z 

lemma union_assoc (X Y Z : A) : (X ∪ Y) ∪ Z = X ∪ (Y ∪ Z) := 
  A.union_assoc_ax X Y Z 

lemma compl_subset {X Y : A} (hXY : X ⊆ Y) : Yᶜ ⊆ Xᶜ := 
  begin rw inter_subset at hXY, rw [←hXY, compl_inter, union_comm], apply subset_union_left end 

-- Self-Distributivity

lemma inter_distrib_inter_left (X Y Z : A) : (X ∩ Y) ∩ Z = (X ∩ Z) ∩ (Y ∩ Z) := 
  by rw [inter_assoc X Z, inter_comm Z, inter_assoc Y, inter_idem, inter_assoc]  


lemma union_distrib_union_left (X Y Z : A) : (X ∪ Y) ∪ Z = (X ∪ Z) ∪ (Y ∪ Z) := 
  by rw [union_assoc X Z, union_comm Z, union_assoc Y, union_idem, union_assoc]

lemma union_distrib_union_right (X Y Z : A) : X ∪ (Y ∪ Z) = (X ∪ Y) ∪ (X ∪ Z) := 
  by rw [union_comm X, union_distrib_union_left Y Z X, union_comm X, union_comm X]   

lemma inter_is_lb  (X Y Z : A) : Z ⊆ X → Z ⊆ Y → Z ⊆ (X ∩ Y) := 
begin intros hZX hZY, rw inter_subset at *, rw [←inter_assoc, hZX, hZY] end 

lemma union_is_ub  (X Y Z : A) : X ⊆ Z → Y ⊆ Z → X ∪ Y ⊆ Z := 
begin intros hXZ hYZ, rw union_subset at *, rw [union_assoc, hYZ, hXZ] end

lemma diff_subset  (X Y : A) : X - Y ⊆ X := 
  inter_subset_left X Yᶜ

lemma diff_union (X Y : A): (X ∩ Y) ∪ (Y - X) = Y := 
  by unfold has_sub.sub; rw [inter_comm Y Xᶜ, compl_partition]

lemma diff_union_subset {X Y : A} (hXY : X ⊆ Y) : X ∪ (Y - X) = Y := 
  begin rw inter_subset at hXY, have := diff_union X Y, rw hXY at this, exact this end

lemma diff_inter (X Y : A) : X ∩ (Y - X) = ⊥ := 
  begin  unfold has_sub.sub, rw [←inter_assoc, inter_comm X Y, inter_assoc, inter_compl ,inter_bot] end

lemma size_monotone {X Y: A} (hXY : X ⊆ Y) : size X ≤ size Y := 
  begin have := size_modular X (Y-X), rw diff_union_subset hXY at this, rw diff_inter at this, linarith [size_nonneg(Y-X), size_bot A] end

lemma size_subadditive {X Y : A} : size (X ∪ Y) ≤ size X + size Y :=
  by linarith [size_modular X Y, size_nonneg (X ∩ Y)] 

lemma size_disjoint_sum {X Y : A} (hXY: X ∩ Y = ⊥) : size (X ∪ Y) = size X + size Y := 
  begin have := size_modular X Y, rw [hXY, size_bot] at this, linarith end

lemma size_compl_sum (X : A) : size X + size Xᶜ = size (⊤ : A) := 
  begin have := size_disjoint_sum (inter_compl X), rw (union_compl X) at this, linarith end 

lemma compl_inter_size (X Y : A) : size (X ∩ Y) + size (Xᶜ ∩ Y) = size Y := 
  by rw [←size_modular, ←inter_distrib_right, union_compl, top_inter, ←inter_distrib_inter_left, inter_compl, bot_inter, size_bot]; ring

lemma compl_inter_size_subset {X Y : A} (hXY : X ⊆ Y) : size (Xᶜ ∩ Y) = size Y - size X := 
  begin have := compl_inter_size X Y, rw inter_subset_mp hXY at this, linarith end

lemma diff_size {X Y : A} (hXY : X ⊆ Y) : size (Y - X) = size Y - size X :=  
  begin unfold has_sub.sub, rw inter_comm, exact compl_inter_size_subset hXY end  

lemma size_zero_bot {X : A} : (size X = 0) → X = ⊥ := sorry


-- more subsets 

lemma subset_trans {X Y Z : A} (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) : X ⊆ Z :=
  begin rw inter_subset at *, rw [←hXY, inter_assoc, hYZ] end 
  
lemma union_of_subsets (X Y Z : A) : (X ⊆ Z) → (Y ⊆ Z) → (X ∪ Y ⊆ Z) := 
  begin intros hXZ hYZ, rw inter_subset at *, rw [inter_distrib_right, hXZ, hYZ] end

lemma inter_of_supsets (X Y Z : A) : (X ⊆ Y) → (X ⊆ Z) → (X ⊆ Y ∩ Z) := 
  begin intros hXY hXZ, rw inter_subset at *, rw [←inter_assoc, hXY, hXZ]  end 

lemma inter_of_subsets (X Y Z : A) : (X ⊆ Z) → (X ∩ Y ⊆ Z) := 
  λ h, subset_trans (inter_subset_left X Y) h

lemma union_of_supsets (X Y Z : A) : (X ⊆ Y) → (X ⊆ Y ∪ Z) := 
  λ h, subset_trans h (subset_union_left Y Z)

lemma subset_inter_subset_left (X Y Z : A) : (X ⊆ Y) → (X ∩ Z) ⊆ (Y ∩ Z) := 
  begin intro hXY, rw inter_subset at *, rw [←inter_distrib_inter_left, hXY] end 

lemma subset_union_subset_left (X Y Z : A) : (X ⊆ Y) → (X ∪ Z) ⊆ (Y ∪ Z) := 
  begin intros hXY, rw union_subset at *, rw [←union_distrib_union_left, hXY] end


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
  by rw inter_subset at *; rw [←emb.on_inter, hXY]

-- Embedding and subalgebras 


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
  begin intros h, rw inter_subset at *, rw [←emb.on_inter, h] end 

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
  union := λ X Y, ⟨X.val ∪ Y.val, union_of_subsets X.val Y.val ground X.property Y.property⟩,
  compl := λ X, ⟨ground - X.val, diff_subset ground X.val⟩,
  size := λ X, size X.val, 
  size_bot_ax := @size_bot A, 
  size_nonneg_ax := λ X, size_nonneg X.val,
  size_modular_ax := λ X Y, size_modular X.val Y.val, 
  singleton_subset_ax := sorry,
  inter_comm_ax := λ X Y, subtype.eq (inter_comm X.val Y.val), 
  union_comm_ax := λ X Y, subtype.eq (union_comm X.val Y.val),
  union_distrib_right_ax := λ X Y Z, subtype.eq (union_distrib_right X Y Z),
  inter_distrib_right_ax := λ X Y Z, subtype.eq (inter_distrib_right X Y Z),
  inter_subset_ax:= begin sorry end,
  inter_top_ax := by intros X; cases X; simp only [subtype.mk_eq_mk]; exact inter_subset_mp X_property,
  union_bot_ax := by intros X; cases X; simp only [subtype.mk_eq_mk]; apply union_bot, 
  union_compl_ax := sorry,
  inter_compl_ax := sorry,
  inter_assoc_ax := sorry,
  union_assoc_ax := sorry
}

def embed.from_subset (X : A) : embed (subalg X) A := 
⟨(λ X,X.val),rfl,(λ X Y,rfl),(λ X Y,rfl),(λ X,rfl)⟩ 

def embed.from_nested_pair {X₁ X₂ : A} : (X₁ ⊆ X₂) → embed (subalg X₁) (subalg X₂) := fun hX₁X₂, 
⟨λ X, ⟨X.val, subset_trans X.property hX₁X₂⟩,rfl, (λ X Y, rfl), (λ X Y, rfl), (λ X, rfl)⟩ 

lemma embed.compose_subset_nested_pair (X₁ X₂ : A) (hX₁X₂ : X₁ ⊆ X₂) :
  (embed.compose (embed.from_nested_pair hX₁X₂) (embed.from_subset X₂)) = embed.from_subset X₁ := rfl 

lemma embed.compose_nested_triple (X₁ X₂ X₃ : A) (h₁₂ : X₁ ⊆ X₂) (h₂₃ : X₂ ⊆ X₃) :
  (embed.compose (embed.from_nested_pair h₁₂) (embed.from_nested_pair h₂₃)) = embed.from_nested_pair (subset_trans h₁₂ h₂₃) :=
rfl

/-instance embed.coe_to_fun {A B : boolalg.boolalg} : has_coe_to_fun (boolalg.embed A B) := {
  F := (λ _, A → B),
  coe := λ emb, emb.f,
}-/
def subalg.embed {E : A} : boolalg.embed (subalg E) A := sorry

---- Isomorphisms 

structure iso (A B : boolalg) := 
  (fwd : embed A B)
  (bwd : embed B A)
  (fwd_then_bwd : embed.compose fwd bwd = embed.id)
  (bwd_then_fwd : embed.compose bwd fwd = embed.id)

def boolalg.canonical (size : ℤ) :
  (0 ≤ size) → boolalg := sorry

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
  singleton_subset_ax := 
  begin
    --intros X hbot hX, unfold_coes, 
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
  inter_subset_ax := sorry, 
  inter_assoc_ax := finset.inter_assoc,
  union_assoc_ax := finset.union_assoc,
}

-- Induction stuff 

lemma induction_prop (P : A → Prop) : P ⊥ ∧ (∀ X Y, size Y = 1 ∧ P X -> P (Y ∪ X)) → ∀ S, P S := 
begin
  rintros ⟨hBot, hAug⟩ ,
  suffices h : ∀(S' : A) (n : ℕ), (size S' = n) → P S', 
  intros S, 
  apply h S (size S).to_nat,  
  exact (int.to_nat_of_nonneg (size_nonneg S)).symm, 
  intros S' n,
  induction n with N IH generalizing S',
  intros hS'bot,
  rw [size_zero_bot hS'bot], assumption, 
  intros hS', 
  have S_decomp := singleton_subset S', 
  cases S_decomp with bot_case aug_case, 
  rw bot_case, assumption, 
  rcases aug_case with ⟨Y,Z,hInter,hUnion,hSize⟩,
  specialize hAug Z Y, 
  specialize IH Z, 
  change size S' = N+1 at hS', 
  have := size_disjoint_sum hInter, 
  have sizeS : size Z = N := by rw hUnion at this; linarith , 
  rw ←hUnion, 
  apply hAug, 
  exact ⟨hSize, IH sizeS⟩, 
end

lemma strong_induction_prop (P : A → Prop) : (∀ W, (∀ U, U ⊂ W → P U) → P W) → ∀ S, P S :=
begin
  intros hP, 
  set Q : A → Prop := λ S, ∀ X, X ⊆ S → P X with hQ, 
  have hBot : Q ⊥ := 
  begin 
    rw hQ, intros X hX, rw (subset_bot hX), 
    apply hP, intros Y hY, exfalso, exact ssubset_bot Y hY, 
  end,

  suffices : ∀ S, Q S, {intros S, exact this S S (subset_refl S)},
  apply induction_prop Q, split, exact hBot, 
  rintros X Y ⟨hSize, hQX⟩ Z hZ, 
  have : Z ⊆ X ∨ (Y ⊆ Z) ∧ (Z-Y ⊆ X) := sorry, 
  cases this, 
  exact hQX Z this, 
  have := hQX (Z-Y) this.2, 
  
  have : P Y := 
  begin
    
  end,
  sorry,  
end


lemma min_counterexample_bot (Y : A)(P : A → Prop) : ¬P Y → ∃ Z, Z ⊆ Y ∧ ¬P Z ∧ (∀ Z', Z' ⊂ Z → P Z') := 
begin
  intros hY, 
  set minProp : A → Prop := λ Y, ¬P Y → ∃ Z, Z ⊆ Y ∧ ¬P Z ∧ (∀ Z', Z' ⊂ Z → P Z') with hMP,  /- fill this in -/
  suffices : ∀ Y', minProp Y', 
  specialize this Y hY, exact this, 
  apply induction_prop minProp, split, 
  intros h, use ⊥, 
  refine ⟨subset_refl ⊥, h,_⟩,  
  intros Z' hZ', exfalso, apply ssubset_bot Z', exact hZ',

  rintros X Y ⟨hSize, hMP'⟩ hYX ,  
  rw hMP at hMP',
  have : (P X ∨ ¬ P X) := em (P X),
  cases this, 
  {
    
    sorry,
  },
  {
    specialize hMP' this,
    cases hMP' with Z, use Z, 
    exact ⟨(subset_trans hMP'_h.1 (subset_union_right Y X)), hMP'_h.2⟩, 
  },
  --by_contradiction, push_neg, 
  --subst minProp,
end


lemma min_counterexample {X Y : A} {hXY : X ⊆ Y} (P : A → Prop) : P X → ¬P Y → ∃ Z, (X ⊆ Z) ∧ (Z ⊆ Y) ∧ (¬P Z) ∧ (∀ Z', X ⊆ Z ∧ Z' ⊂ Z → P Z) := 
begin
  sorry 
end


end boolalg



end API 
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
  --(single_subset_ax (X : member) : X ≠  bot → ∃ Y Z, inter Y Z = bot ∧ union Y Z = X ∧ size Y = 1)
  (contains_single_ax (X : member) : X ≠  bot → ∃ Y, subset Y X ∧ size Y = 1)


  (inter_comm_ax (X Y : member) : inter X Y = inter Y X)
  (union_comm_ax (X Y : member) : union X Y = union Y X)
  
  (union_distrib_right_ax (X Y Z : member) : union (inter X Y) Z = inter (union X Z) (union Y Z))
  (inter_distrib_right_ax (X Y Z : member) : inter (union X Y) Z = union (inter X Z) (inter Y Z))

  (inter_top_ax (X : member) : inter X top = X)
  (union_bot_ax (X : member) : union X bot = X)

  (union_compl_ax (X : member) : union X (compl X) = top)
  (inter_compl_ax (X : member) : inter X (compl X) = bot)

  (union_subset_ax (X Y : member) : subset X Y ↔ union X Y = Y)

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
  λ hX, by calc X = ⊥ ∪ X : (bot_union X).symm ... = ⊥ : hX ⊥

lemma top_unique (X : A) : (∀ (Y: A), Y ∩ X = Y) → X = ⊤ := 
  λ hX, by calc X = ⊤ ∩ X : (top_inter X).symm ... = ⊤ : hX ⊤ 



-- Idempotence

lemma union_idem (X : A) : X ∪ X = X := 
  by rw [←(inter_top  (X ∪ X)), ←(union_compl X), ←(union_distrib_left X X Xᶜ), inter_compl, union_bot]

lemma inter_idem (X : A): X ∩ X = X := 
  by rw [←(union_bot (X ∩ X)), ←(inter_compl X), ←(inter_distrib_left X X Xᶜ), union_compl, inter_top ]

lemma union_top  (X : A) : X ∪ ⊤ = ⊤ := 
  by calc _ = ⊤ ∩ (X ∪ ⊤)        : by rw top_inter
            ... = (X ∪ Xᶜ) ∩ (X ∪ ⊤) : by rw ←union_compl 
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

@[simp] lemma size_bot (A : boolalg) : size (⊥ : A) = 0 := 
  A.size_bot_ax

lemma compl_size (X : A) : size Xᶜ = size (⊤ : A) - size X :=
  calc size Xᶜ = size (X ∪ Xᶜ) + size (X ∩ Xᶜ) - size X : by linarith [size_modular X Xᶜ]
  ...          = size (⊤ : A)  + size (⊥ : A)  - size X : by rw [union_compl X, inter_compl X]
  ...          = size (⊤ : A) - size X                  : by linarith [size_bot A]

lemma size_compl (X : A) : size X = size (⊤ : A) - size(Xᶜ) := 
  by linarith [compl_size X]

lemma size_nonneg (X : A) : 0 ≤ size X := 
  A.size_nonneg_ax X 

lemma contains_single (X : A) : X ≠ ⊥ → (∃ Y, Y ⊆ X ∧ size Y = 1) :=
  A.contains_single_ax X 
  

-- Subsets 


lemma union_subset (X Y : A) : (X ⊆ Y) ↔ (X ∪ Y = Y) := 
  A.union_subset_ax X Y 

lemma inter_subset (X Y: A) : (X ⊆ Y) ↔ (X ∩ Y = X) :=
  by {rw union_subset, exact ⟨λ h, by rw [←h, absorb_inter_union], λ h, by rw[←h, union_comm, inter_comm, absorb_union_inter]⟩} 

lemma subset_refl (X : A) : X ⊆ X :=
  by rw [inter_subset, inter_idem]

lemma inter_subset_mp  {X Y : A} : X ⊆ Y → X ∩ Y = X := 
  (inter_subset X Y).mp 

lemma inter_subset_mpr  {X Y : A} : X ∩ Y = X → X ⊆ Y  := 
  (inter_subset X Y).mpr 

lemma union_subset_mp  {X Y : A} : X ⊆ Y → X ∪ Y = Y :=
  (union_subset X Y).mp

lemma union_subset_mpr {X Y : A} : X ∪ Y = Y → X ⊆ Y := 
  (union_subset X Y).mpr 

lemma subset_ssubset_or_eq {X Y : A} : (X ⊆ Y) → (X ⊂ Y) ∨ X =Y :=
  λ hXY, by {by_cases X = Y, exact or.inr h, exact or.inl ⟨hXY, h⟩}

lemma ssubset_size {X Y : A} : (X ⊆ Y) → (size X < size Y) → (X ⊂ Y) := 
  λ hXY hS, ⟨hXY, by {intros heq, rw heq at hS, linarith}⟩

lemma subset_antisymm  {X Y : A} (hXY : X ⊆ Y) (hYX : Y ⊆ X) : X = Y := 
  by {rw inter_subset at *, rw inter_comm at hXY, exact (rfl.congr hYX).mp (eq.symm hXY)}

lemma inter_subset_left {A: boolalg} (X Y : A) : (X ∩ Y) ⊆ X := 
  by {apply union_subset_mpr; rw union_comm; apply absorb_union_inter}

lemma inter_subset_right (X Y : A) : (X ∩ Y) ⊆ Y := 
  by {rw inter_comm, apply inter_subset_left}

lemma subset_union_left (X Y : A) : X ⊆ X ∪ Y := 
  by {apply inter_subset_mpr, rw absorb_inter_union}

lemma subset_union_right (X Y : A) : Y ⊆ X ∪ Y := 
  by {rw union_comm, exact subset_union_left Y X} 
   
lemma subset_top (X : A) : X ⊆ ⊤ := 
  by {apply inter_subset_mpr; exact (inter_top X)}

lemma top_subset  {X : A} (hX : ⊤ ⊆ X) : X = ⊤ := 
  subset_antisymm (subset_top X) hX

lemma bot_subset  (X : A) : ⊥ ⊆ X := 
  by {apply inter_subset_mpr, exact (bot_inter X)}

lemma subset_bot  {X : A} (hX : X ⊆ ⊥) : X = ⊥ := 
  subset_antisymm hX (bot_subset X)  

lemma ssubset_bot (X : A) : ¬ X ⊂ ⊥ := 
  λ h, h.2 (subset_bot h.1) 

lemma disjoint_compl_subset  {X Y : A} (hXY: X ∩ Y = ⊥) : X ⊆ Yᶜ := 
  by rw [inter_subset, ← bot_union (X ∩ Yᶜ), ←hXY, ←inter_distrib_left, union_compl, inter_top]

lemma cover_compl_subset {A: boolalg} {X Y : A} (hXY: X ∪ Y = ⊤) : Xᶜ ⊆ Y  := 
  by rw [union_subset, ←top_inter (Xᶜ ∪ Y), ←hXY, ←union_distrib_right, inter_compl, bot_union]

lemma compl_unique {X Y : A} (hU : X ∪ Y = ⊤) (hI : X ∩ Y = ⊥) : Y = Xᶜ := 
  by {apply subset_antisymm, exact disjoint_compl_subset (eq.trans (inter_comm Y X) hI), exact cover_compl_subset hU}

@[simp] lemma compl_compl  (X : A) : Xᶜᶜ = X := 
  by {apply subset_antisymm, apply cover_compl_subset, exact eq.trans (union_comm Xᶜ X) (union_compl X), exact disjoint_compl_subset (inter_compl X)}

lemma compl_inj {X Y : A} (hXY : Xᶜ = Yᶜ) : X = Y := 
  by rw [←compl_compl X, ←compl_compl Y, hXY]


lemma compl_top (A : boolalg) : (⊤ : A)ᶜ = ⊥ := 
  eq.symm (compl_unique (top_union ⊥) (inter_bot ⊤))

lemma compl_bot (A : boolalg) : (⊥ : A)ᶜ = ⊤ := 
  eq.symm (compl_unique (union_top ⊥) (bot_inter ⊤)) 

lemma bot_of_compl_top {X : A} (hX : Xᶜ = ⊤) : X = ⊥  := 
  by rw [←compl_compl X, hX, compl_top]

lemma top_of_compl_bot {X : A} (hX : Xᶜ = ⊥) : X = ⊤  := 
  by rw [←compl_compl X, hX, compl_bot]

lemma inter_compl_left {X : A} : Xᶜ ∩ X = ⊥ := 
  by rw [inter_comm, inter_compl]

lemma union_compl_left {X : A} : Xᶜ ∪ X = ⊤ := 
  by rw [union_comm, union_compl]

lemma union_compl_union  (X Y : A) : X ∪ (Xᶜ ∪ Y) = ⊤ :=  
  by rw [←top_inter(X ∪ (Xᶜ ∪ Y)), ←union_compl, ←union_distrib_left, absorb_inter_union] 

lemma inter_compl_inter (X Y : A) : X ∩ (Xᶜ ∩ Y) = ⊥ := 
  by rw [←bot_union(X ∩ (Xᶜ ∩ Y)), ←inter_compl, ←inter_distrib_left, absorb_union_inter]

lemma inter_compl_union (X Y : A) : X ∩ (Xᶜ ∪ Y) = X ∩ Y :=
  by rw [inter_distrib_left, inter_compl, bot_union]

lemma union_compl_inter (X Y : A) : X ∪ (Xᶜ ∩ Y) = X ∪ Y :=
  by rw [union_distrib_left, union_compl, top_inter]

lemma union_inter_compl_inter (X Y : A) : (X ∪ Y) ∪ (Xᶜ ∩ Yᶜ)  = ⊤ := 
  by rw [union_distrib_left, union_comm _ Xᶜ, union_comm X Y, union_comm _ Yᶜ,
      ←(compl_compl Y),  compl_compl Yᶜ, union_compl_union Yᶜ, union_comm _ X, 
      ←(compl_compl X),    compl_compl Xᶜ, union_compl_union Xᶜ, inter_idem]

lemma inter_union_compl_union (X Y : A) : (X ∩ Y) ∩ (Xᶜ ∪ Yᶜ)  = ⊥ := 
  by rw [inter_distrib_left, inter_comm _ Xᶜ, inter_comm X Y, inter_comm _ Yᶜ, 
        ←(compl_compl Y), compl_compl Yᶜ, inter_compl_inter Yᶜ, inter_comm _ X, 
        ←(compl_compl X), compl_compl Xᶜ, inter_compl_inter Xᶜ, union_idem]
  

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
  by {nth_rewrite 0 ←(inter_subset_mp hXY), exact compl_partition X Y}

lemma compl_pair {X Y : A} : (Xᶜ = Y) → (X = Yᶜ) := 
  λ h, by rw [←h, compl_compl]

lemma compl_diff (X Y : A) : (X - Y)ᶜ = Xᶜ ∪ Y := 
  by {dunfold has_sub.sub, rw [compl_inter, compl_compl]}
  
-- Associativity (In fact, this can be discarded eventually, but why bother?)

lemma inter_assoc (X Y Z : A) : (X ∩ Y) ∩ Z = X ∩ (Y ∩ Z) := 
  A.inter_assoc_ax X Y Z 

lemma union_assoc (X Y Z : A) : (X ∪ Y) ∪ Z = X ∪ (Y ∪ Z) := 
  A.union_assoc_ax X Y Z 

lemma subset_to_compl {X Y : A} (hXY : X ⊆ Y) : Yᶜ ⊆ Xᶜ := 
  by {rw inter_subset at hXY, rw [←hXY, compl_inter, union_comm], apply subset_union_left} 

lemma compl_to_subset {X Y : A} (hXY : Xᶜ ⊆ Yᶜ) : Y ⊆ X := 
  by {have := subset_to_compl hXY, repeat {rw compl_compl at this}, exact this }

lemma subset_compl_right {X Y : A} (hXY : X ⊆ Yᶜ) : Y ⊆ Xᶜ := 
  by {rw [←compl_compl X] at hXY, exact compl_to_subset hXY}

lemma subset_compl_left {X Y : A} (hXY : Xᶜ ⊆ Y) : Yᶜ ⊆ X := 
  by {rw [←compl_compl Y] at hXY, exact compl_to_subset hXY}

lemma subset_of_compl_iff_disjoint {X Y: A} : X ⊆ Yᶜ ↔ X ∩ Y = ⊥ := 
  begin 
        rw inter_subset,  refine ⟨λ h, _, λ h, _⟩, 
        rw [←h, inter_assoc, inter_comm _ Y, inter_compl, inter_bot], 
        rw [←union_bot (X ∩ Yᶜ), ←h, ←inter_distrib_left, union_comm, union_compl, inter_top] 
  end

-- Unions/Inters of triples 

lemma union_left_comm (X Y Z : A) : X ∪ (Y ∪ Z) = Y ∪ (X ∪ Z) := 
  by rw [←union_assoc, ←union_assoc, union_comm X] 

lemma inter_left_comm (X Y Z : A) : X ∩ (Y ∩ Z) = Y ∩ (X ∩ Z) := 
  by rw [←inter_assoc, ←inter_assoc, inter_comm X]

lemma union_right_comm (X Y Z : A) : X ∪ Y ∪ Z = X ∪ Z ∪ Y := 
  by rw [union_assoc _ Y, union_comm Y, ←union_assoc]

lemma inter_right_comm (X Y Z : A) : X ∩ Y ∩ Z = X ∩ Z ∩ Y := 
  by rw [inter_assoc _ Y, inter_comm Y, ←inter_assoc]

lemma inter_distrib_inter_left (X Y Z : A) : (X ∩ Y) ∩ Z = (X ∩ Z) ∩ (Y ∩ Z) := 
  by rw [inter_assoc X Z, inter_comm Z, inter_assoc Y, inter_idem, inter_assoc] 

lemma inter_distrib_inter_right (X Y Z : A) : X ∩ (Y ∩ Z) = (X ∩ Y) ∩ (X ∩ Z) := 
  by rw [inter_comm _ (X ∩ Z), inter_assoc _ _ (X ∩ Y), inter_comm Z, ←inter_assoc X, ←inter_assoc X, ←inter_assoc X, inter_idem]

lemma union_distrib_union_left (X Y Z : A) : (X ∪ Y) ∪ Z = (X ∪ Z) ∪ (Y ∪ Z) := 
  by rw [union_assoc X Z, union_comm Z, union_assoc Y, union_idem, union_assoc]

lemma union_distrib_union_right (X Y Z : A) : X ∪ (Y ∪ Z) = (X ∪ Y) ∪ (X ∪ Z) := 
  by rw [union_comm X, union_distrib_union_left Y Z X, union_comm X, union_comm X]   

-- Misc

lemma inter_is_lb  (X Y Z : A) : Z ⊆ X → Z ⊆ Y → Z ⊆ (X ∩ Y) := 
  λ hZX hZY, by {rw inter_subset at *, rw [←inter_assoc, hZX, hZY]}

lemma union_is_ub  (X Y Z : A) : X ⊆ Z → Y ⊆ Z → X ∪ Y ⊆ Z := 
  λ hXZ hYZ, by {rw union_subset at *, rw [union_assoc, hYZ, hXZ]}

lemma diff_def (X Y : A) : X - Y = X ∩ Yᶜ := 
  rfl 

lemma diff_subset  (X Y : A) : X - Y ⊆ X := 
  inter_subset_left X Yᶜ

@[simp] lemma top_diff (X : A) : ⊤ - X = Xᶜ := 
  by {unfold has_sub.sub, apply top_inter}

lemma diff_union (X Y : A): X = (X ∩ Y) ∪ (X - Y) := 
  by rw [diff_def, ←inter_distrib_left, union_compl, inter_top]

lemma inter_diff (X Y : A): X ∩ (Y - X)  = ⊥ := 
  by rw [diff_def, ←inter_assoc, inter_right_comm, inter_compl, bot_inter]

lemma partition_inter (X Y : A) : (X ∩ Y) ∩ (X - Y) = ⊥ := 
  by rw [inter_assoc, inter_diff, inter_bot]

lemma diff_bot_subset (X Y : A) (hXY : X-Y = ⊥) : X ⊆ Y := 
  by {rw [diff_union X Y, hXY, union_bot], apply inter_subset_right}

lemma subset_diff_bot (X Y : A) (hXY : X ⊆ Y) : X-Y = ⊥ := 
  by {rw diff_def, rw inter_subset at hXY, rw [←hXY, inter_assoc, inter_compl, inter_bot]}

lemma diff_bot_iff_subset (X Y : A) : X-Y = ⊥ ↔ X ⊆ Y := 
  by {split, apply diff_bot_subset, apply subset_diff_bot}

lemma ssubset_diff_nonempty {X Y : A} (hXY : X ⊂ Y) : Y-X ≠ ⊥ :=
  by {intros hYX, rw diff_bot_iff_subset at hYX, exact hXY.2 (subset_antisymm hXY.1 hYX)}

lemma union_diff_of_subset  {X Y : A} : X ⊆ Y → X ∪ (Y - X) = Y := 
  λ h, by {rw [inter_subset, inter_comm] at h, have := diff_union Y X, rw h at this, exact this.symm}

lemma diff_inter (X Y : A) : (Y - X) ∩ X = ⊥ := 
  by rw [inter_comm, inter_diff]

lemma union_diff (X Y : A) : X ∪ (Y -X) = X ∪ Y := 
  by {rw [diff_def, union_distrib_left, union_compl, inter_top]}

lemma union_diff_diff (X Y : A) : (X ∪ Y) - (Y-X) = X := 
  by rw [diff_def, diff_def, compl_inter,compl_compl,union_comm, ←union_distrib_right, inter_compl, bot_union]

lemma diff_bot (X : A) : X - ⊥ = X := 
  by {rw [diff_def, compl_bot, inter_top]} 

lemma size_monotone {X Y: A} (hXY : X ⊆ Y) : size X ≤ size Y := 
  by {have := size_modular X (Y-X), rw union_diff_of_subset  hXY at this, rw inter_diff at this, linarith [size_nonneg(Y-X), size_bot A]}

lemma size_subadditive {X Y : A} : size (X ∪ Y) ≤ size X + size Y :=
  by linarith [size_modular X Y, size_nonneg (X ∩ Y)] 

lemma size_disjoint_sum {X Y : A} (hXY: X ∩ Y = ⊥) : size (X ∪ Y) = size X + size Y := 
  by {have := size_modular X Y, rw [hXY, size_bot] at this, linarith}

lemma size_induced_partition (X Y : A) : size X = size (X ∩ Y) + size (X-Y) := 
  by {nth_rewrite 0 diff_union X Y,refine size_disjoint_sum _, apply partition_inter}

lemma size_compl_sum (X : A) : size X + size Xᶜ = size (⊤ : A) := 
  by {have := size_disjoint_sum (inter_compl X), rw (union_compl X) at this, linarith}

lemma compl_inter_size (X Y : A) : size (X ∩ Y) + size (Xᶜ ∩ Y) = size Y := 
  by rw [←size_modular, ←inter_distrib_right, union_compl, top_inter, ←inter_distrib_inter_left, inter_compl, bot_inter, size_bot]; ring

lemma compl_inter_size_subset {X Y : A} (hXY : X ⊆ Y) : size (Xᶜ ∩ Y) = size Y - size X := 
  by {have := compl_inter_size X Y, rw inter_subset_mp hXY at this, linarith} 

lemma diff_size {X Y : A} (hXY : X ⊆ Y) : size (Y - X) = size Y - size X :=  
  by rw [diff_def, inter_comm, compl_inter_size_subset hXY]

lemma size_zero_bot {X : A} : (size X = 0) →  X = ⊥ := 
  λ h, by {by_contra h', cases contains_single X h' with Y hY, cases hY, linarith [size_monotone hY_left] }
    
lemma size_zero_iff_bot {X : A} : (size X = 0) ↔ (X = ⊥) := 
  by {split, apply size_zero_bot, intros h, rw h, exact size_bot A}

lemma size_nonempty {X : A} : X ≠ ⊥ → 0 < size X  := 
  λ hX, lt_of_le_of_ne (size_nonneg X) (λ h, hX (size_zero_bot h.symm))

lemma size_strict_monotone {X Y : A} (hXY : X ⊂ Y) : size X < size Y := 
  by {rw [size_induced_partition Y X, inter_comm, inter_subset_mp hXY.1], linarith [size_nonempty (ssubset_diff_nonempty hXY)]} 

lemma eq_of_eq_size_subset {X Y : A} : (X ⊆ Y) → (size X = size Y) → X = Y :=
  λ hXY, by {cases subset_ssubset_or_eq hXY, intros sXY, exfalso, replace h := size_strict_monotone h, linarith, exact λ h', h}

lemma size_eq_of_supset {X Y : A} : (X ⊆ Y) → (size Y ≤ size X) → size X = size Y := 
  λ hss hs, by linarith[size_monotone hss]

-- more subsets 

lemma subset_trans {X Y Z : A} : X ⊆ Y → Y ⊆ Z →  X ⊆ Z :=
  λ hXY hYZ, by {rw inter_subset at *, rw [←hXY, inter_assoc, hYZ]}

lemma subset_of_inter_mp {X Y Z : A} : X ⊆ Y ∩ Z → X ⊆ Y ∧ X ⊆ Z := 
  λ h, ⟨subset_trans h (inter_subset_left _ _), subset_trans h (inter_subset_right _ _)⟩  

lemma union_of_subsets {X Y Z : A} : (X ⊆ Z) → (Y ⊆ Z) → (X ∪ Y ⊆ Z) := 
  λ hXZ hYZ, by {rw inter_subset at *, rw [inter_distrib_right, hXZ, hYZ]}

lemma subset_of_inter_mpr  {X Y Z : A} : (X ⊆ Y) → (X ⊆ Z) → (X ⊆ Y ∩ Z) := 
  λ hXY hXZ, by {rw inter_subset at *, rw [←inter_assoc, hXY, hXZ]}

lemma subset_of_inter_iff {X Y Z :A} : X ⊆ (Y ∩ Z) ↔ (X ⊆ Y ∧ X ⊆ Z) := 
  ⟨λ h, subset_of_inter_mp h, λ h, subset_of_inter_mpr  h.1 h.2⟩

lemma inter_of_subsets (X Y Z : A) : (X ⊆ Z) → (X ∩ Y ⊆ Z) := 
  λ h, subset_trans (inter_subset_left X Y) h

lemma union_of_supsets (X Y Z : A) : (X ⊆ Y) → (X ⊆ Y ∪ Z) := 
  λ h, subset_trans h (subset_union_left Y Z)

lemma subset_inter_subset_left (X Y Z : A) : (X ⊆ Y) → (X ∩ Z) ⊆ (Y ∩ Z) := 
  λ hXY, by {rw inter_subset at *, rw [←inter_distrib_inter_left, hXY]}

lemma subset_inter_subset_right (X Y Z : A) : (X ⊆ Y) → (Z ∩ X) ⊆ (Z ∩ Y) := 
  by {rw [inter_comm _ X, inter_comm _ Y], apply subset_inter_subset_left }

lemma subset_union_subset_left (X Y Z : A) : (X ⊆ Y) → (X ∪ Z) ⊆ (Y ∪ Z) := 
  λ hXY, by {rw union_subset at *, rw [←union_distrib_union_left, hXY]}

lemma subset_union_subset_right (X Y Z : A) : (X ⊆ Y) → (Z ∪ X) ⊆ (Z ∪ Y) := 
  by {rw [union_comm _ X, union_comm _ Y], apply subset_union_subset_left }

lemma subset_of_set_and_compl {X Y: A} : X ⊆ Y → X ⊆ Yᶜ → X = ⊥ :=
  λ h1 h2, by {have := subset_of_inter_mpr h1 h2, rw inter_compl at this, exact subset_bot this}

lemma subset_ssubset_trans {X Y Z : A} : X ⊆ Y → Y ⊂ Z → X ⊂ Z := 
  λ hXY hYZ, ⟨subset_trans hXY hYZ.1, λ h, by {rw ←h at hYZ, exact hYZ.2 (subset_antisymm hYZ.1 hXY)}⟩ 

lemma ssubset_subset_trans {X Y Z : A} : X ⊂ Y → Y ⊆ Z → X ⊂ Z := 
  λ hXY hYZ, ⟨subset_trans hXY.1 hYZ, λ h, by {rw h at hXY, exact hXY.2 (subset_antisymm hXY.1 hYZ)}⟩ 

@[simp] lemma ssubset_iff {X Y : A} : X ⊂ Y ↔ (X ⊆ Y) ∧ (X ≠ Y) :=
  by unfold has_ssubset.ssubset

lemma ssubset_irrefl (X : A) : ¬ (X ⊂ X) :=
  λ h, h.2 rfl

lemma ssubset_not_supset {X Y : A} : X ⊂ Y → ¬(Y ⊆ X) :=
  λ h h', ssubset_irrefl _ (ssubset_subset_trans h h') 

lemma subset_not_ssupset {X Y : A} : X ⊆ Y → ¬(Y ⊂ X) := 
  λ h h', ssubset_irrefl _ (subset_ssubset_trans h h')

lemma eq_of_ssubset {X Y: A} : X ⊆ Y → ¬(X ⊂ Y) → X = Y := 
  λ h h', by {simp only [not_and, not_not, ssubset_iff] at h', exact h' h}

lemma ssubset_trans {X Y Z : A} (hXY : X ⊂ Y) (hYZ : Y ⊂ Z) : X ⊂ Z := 
  subset_ssubset_trans hXY.1 hYZ

lemma ssubset_inter {X Y : A} : X ≠ Y → X ∩ Y ⊂ X ∨ X ∩ Y ⊂ Y:=
  λ h, by {by_contra, push_neg at a, cases a, erw [not_and', not_imp_not] at a_left a_right, 
  exact h (eq.trans (a_left (inter_subset_left X Y)).symm (a_right (inter_subset_right X Y)) )}

lemma single_subset (X : A) : X ≠ ⊥ → (∃ Y Z, Y ∩ Z = ⊥ ∧ Y ∪ Z = X ∧ size Y = 1) := 
  begin
    intro h, cases contains_single X h with Y hY, use Y, use X-Y, 
    exact ⟨inter_diff _ _,⟨union_diff_of_subset  hY.1,hY.2⟩⟩,
  end

lemma single_subset_nonempty {X : A}: X ≠ ⊥ → (∃ Y Z, Y ∩ Z = ⊥ ∧ Y ∪ Z = X ∧ size Y = 1) := 
  λ hX, single_subset X hX 


lemma union_ssubsets (X : A) : 1 < size X  → ∃ Y Z : A, Y ⊂ X ∧ Z ⊂ X ∧ Y ∩ Z = ⊥ ∧ Y ∪ Z = X := 
  begin
    intros hX, 
    have h := (λ h', by {rw [h', @size_bot A] at hX, linarith }: X ≠ ⊥), 
    rcases single_subset X h with ⟨Y,⟨Z,⟨hI,hU,h1⟩⟩⟩, use Y, use Z, 
    refine ⟨⟨by {rw ←hU, apply subset_union_left},_⟩,⟨by {rw ←hU, apply subset_union_right},_⟩,hI,hU⟩, 
    intros hYX, rw hYX at h1, linarith, 
    intros hZX, 
    have := size_modular Y Z, 
    rw [hU, hI, @size_bot A, h1,hZX] at this, 
    linarith
  end

lemma ssubset_to_compl {X Y : A} (hXY : X ⊂ Y) : Yᶜ ⊂ Xᶜ := 
  ⟨subset_to_compl (hXY.1), λ h, hXY.2 (compl_inj h).symm⟩

lemma compl_to_ssubset {X Y : A} (hXY : Xᶜ ⊂ Yᶜ) : Y ⊂ X := 
  by {have := ssubset_to_compl hXY, repeat {rw compl_compl at this}, exact this }

lemma ssubset_compl_right {X Y : A} (hXY : X ⊂ Yᶜ) : Y ⊂ Xᶜ := 
  by {rw [←compl_compl X] at hXY, exact compl_to_ssubset hXY}

lemma ssubset_compl_left {X Y : A} (hXY : Xᶜ ⊂ Y) : Yᶜ ⊂ X := 
  by {rw [←compl_compl Y] at hXY, exact compl_to_ssubset hXY}

--lemma ssubset_of_comp {X Y : A} (hXY : X ⊂ Yᶜ) : Y ⊂ X := 


-- Singles

def single (A : boolalg): Type := {X : A // size X = 1}

instance coe_single {A : boolalg} : has_coe (single A) A := ⟨λ e, e.val⟩  

def elem : (single A) → A → Prop := λ e X, (e:A) ⊆ X 
def notelem : (single A) → A → Prop := λ e X, ¬elem e X 

infix ∈ := elem 
infix ∉ := notelem 

@[simp] lemma notelem_simp {e : single A}{X : A}: ¬ (e ∈ X) ↔ e ∉ X := by refl  

lemma elem_iff (e : single A)(X : A) : e ∈ X ↔ (e:A) ⊆ X := 
  by unfold elem

lemma notelem_iff (e : single A)(X : A) : e ∉ X ↔ ¬(e:A) ⊆ X := 
  by trivial 

@[simp] lemma size_coe_single {A : boolalg} (e : single A) : size (e : A) = 1 := e.2 

lemma single_ne_bot (e : single A) : (e:A) ≠ ⊥ := 
  λ h, by {have := size_coe_single e, rw [h,size_bot] at this, linarith}

lemma single_nonelem_bot (e : single A) : e ∉ (⊥:A) := 
  by {rw notelem_iff, intro h, replace h := size_monotone h, simp at h, linarith}

lemma nonempty_has_elem {X : A}  : X ≠ ⊥ → ∃ e, e ∈ X := 
  λ hX, by {rcases single_subset_nonempty hX with ⟨Y,Z ,⟨hI,hU,h1⟩⟩, use ⟨Y,h1⟩, 
                rw ←hU, exact subset_union_left Y Z}

lemma nonempty_iff_has_elem {X : A} : X ≠ ⊥ ↔ ∃ e, e ∈ X :=
  ⟨λ h, nonempty_has_elem h, λ h, λ hb, by {cases h with e he, rw hb at he, exact single_nonelem_bot e he}⟩ 



lemma nested_singles_eq {e f: single A} (hef : (e: A) ⊆ (f :A)) : e = f :=
  begin
    ext, refine eq_of_eq_size_subset hef _,
    calc _ = 1 :size_coe_single e ... = _: (size_coe_single f).symm, 
  end

lemma nonelement_disjoint {e : single A} {X : A} (heX : e ∉ X) : (e:A) ∩ X = ⊥ :=
  begin
    by_contra, rcases nonempty_has_elem a with ⟨f,hf⟩, 
    rcases subset_of_inter_mp hf with ⟨hfe, hfx⟩, 
    rw nested_singles_eq hfe at hfx, exact heX hfx, 
  end

lemma inter_distinct_singles {e f : single A} (hef : e ≠ f) : (e ∩ f :A) = ⊥ := 
  by {apply nonelement_disjoint, exact λ h, hef (nested_singles_eq h)} 

lemma elem_compl_iff {X : A}{e : single A} : e ∈ Xᶜ ↔ e ∉ X := 
  begin
    refine ⟨λ h, λ he, _, λ h, _⟩, 
    have := subset_of_inter_mpr  he h, rw inter_compl at this, have := size_monotone this, linarith [size_coe_single e, size_bot A],   
    have := nonelement_disjoint h, rw ← subset_of_compl_iff_disjoint at this, assumption,  
  end


lemma nonelem_compl_iff {X : A}{e : single A} : e ∉ Xᶜ ↔ e ∈ X  := 
  by {rw ←elem_compl_iff, rw [compl_compl]}

lemma elem_union_iff {e : single A} {X Y : A} : e ∈ X ∪ Y ↔ e ∈ X ∨ e ∈ Y :=
   begin 
     refine ⟨λ h, _, λ h, _⟩, by_contra, push_neg at a, 
     repeat {rw [notelem_simp] at a, rw ←elem_compl_iff at a}, 
     have h' := subset_of_inter_mpr a.1 h, nth_rewrite 1 ←(compl_compl X) at h', 
     rw [inter_compl_union, inter_comm] at h', 
     exact single_ne_bot _ (subset_of_set_and_compl (subset_trans h' (inter_subset_left Y Xᶜ)) a.2),
     cases h, exact subset_trans h (subset_union_left X Y), 
     exact subset_trans h (subset_union_right X Y)
   end


lemma nonelem_inter_iff {e : single A} {X Y : A} : e ∉ X ∩ Y ↔ e ∉ X ∨ e ∉ Y := 
  by rw [←elem_compl_iff, compl_inter, elem_union_iff, elem_compl_iff, elem_compl_iff] 


lemma elem_diff_iff {e : single A}{X Y : A} : 
  e ∈ X - Y ↔ e ∈ X ∧ e ∉ Y :=
  begin
    refine ⟨λ h ,⟨subset_trans h (diff_subset _ _),λ heY,_⟩, λ h, _⟩, 
    have := subset_of_inter_mpr  h heY, rw diff_inter at this, 
    linarith [size_monotone this, size_bot A, size_coe_single e], 
    rw [diff_def, elem_iff, subset_of_inter_iff], 
    rw [ ←elem_compl_iff, elem_iff, elem_iff] at h, exact h
  end


lemma subset_iff_elems_contained {X Y : A} :
  X ⊆ Y ↔ ∀ e, e ∈ X → e ∈ Y := 
  begin
    rw [←diff_bot_iff_subset, ←not_iff_not, (_: ¬(X - Y) = ⊥ ↔ X-Y ≠ ⊥),nonempty_iff_has_elem],
    simp_rw elem_diff_iff, rw not_forall, simp_rw not_imp, exact iff.rfl, exact iff.rfl, 
  end

lemma eq_iff_same_elems {X Y : A} :
  X = Y ↔ ∀ e, e ∈ X ↔ e ∈ Y :=
  begin
    refine ⟨λ h, λ e, by rw h, λ h, subset_antisymm _ _ ⟩, 
    rw subset_iff_elems_contained, exact λ e, (h e).mp, 
    rw subset_iff_elems_contained, exact λ e, (h e).mpr
  end

lemma add_from_compl_ssubset {X : A} {e : single A} : e ∈ Xᶜ → X ⊂ X ∪ e := 
  begin
     refine λ hXe, ⟨subset_union_left _ _, _⟩, intro h, rw [h, compl_union] at hXe, 
     have ebot := subset_trans hXe (inter_subset_right Xᶜ _), 
     rw [inter_subset, inter_compl] at ebot,  
     have := size_coe_single e, rw ←ebot at this, linarith [size_bot A], 
  end

lemma add_nonelem_ssubset {X : A} {e : single A}: e ∉ X → X ⊂ X ∪ e := 
  λ hXe, add_from_compl_ssubset (elem_compl_iff.mpr hXe)

lemma elem_diff_ssubset {X Y : A} : X ⊂ Y → ∃ e, e ∈ Y - X :=
  λ h, by {have := ssubset_diff_nonempty h, rw ←nonempty_iff_has_elem, assumption}

lemma elem_only_larger_ssubset {X Y : A} : X ⊂ Y → ∃ e, e ∈ Y ∧ e ∉ X :=
  λ h, by {have := elem_diff_ssubset h, simp_rw elem_diff_iff at this, assumption}


lemma add_compl_single_size {X : A} {e : single A} (hXe : e ∈ Xᶜ) : size (X ∪ e) = size X + 1 := 
begin
  have := size_modular X e, 
  rw [inter_comm X, nonelement_disjoint (elem_compl_iff.mp hXe), size_coe_single, size_bot] at this, 
  linarith, 
end

lemma add_nonelem_size {X : A} {e : single A}: e ∉ X →  size (X ∪ e) = size X + 1 := 
  λ hXe, by {apply add_compl_single_size, exact elem_compl_iff.mpr hXe}

lemma compl_single_remove {X : A} {e : single A} (heX : e ∈ X) : (X - e)ᶜ = Xᶜ ∪ e := 
  by rw [diff_def, compl_inter, compl_compl]

lemma remove_add_single {X : A} {e : single A} (heX : e ∈ X) : (X-e) ∪ e = X := 
  by {rw [elem_iff, union_subset,union_comm] at heX, 
      rw [diff_def, union_distrib_right, union_compl_left, inter_top, heX]}
   
lemma remove_single_size {X :A}{e : single A} (heX : e ∈ X) : size (X - e) = size X - 1 := 
begin
  have h: e ∈ (X-e)ᶜ := by {rw compl_single_remove heX, apply subset_union_right}, 
  nth_rewrite 1 ←remove_add_single heX, linarith [add_compl_single_size h], 
end

lemma remove_single_ssubset {X : A} {e : single A} (heX : e ∈ X) : X - e ⊂ X := 
  ⟨diff_subset _ _, λ h, by {have := remove_single_size heX, rw h at this, linarith }⟩

lemma nonbot_single_removal {X : A} (hX : X ≠ ⊥) : ∃ Y :A, Y ⊂ X ∧ size Y = size X - 1 := 
  by {cases nonempty_has_elem hX with e he, exact ⟨X-e, ⟨remove_single_ssubset he,remove_single_size he⟩ ⟩}

lemma nontop_single_addition {X : A} (hX : X ≠ ⊤) : ∃ Y, X ⊂ Y ∧ size Y = size X + 1 := 
  begin
    rcases nonbot_single_removal (λ h, _ : Xᶜ ≠ ⊥) with ⟨Y, ⟨h₁,h₂⟩ ⟩, 
    refine ⟨Yᶜ , ⟨ssubset_compl_right h₁, _⟩⟩,
    linarith [size_compl X, size_compl Y], 
    exact hX (top_of_compl_bot h), 
  end

lemma add_from_nonempty_diff {X Y : A} :
  X ⊂ Y ↔ ∃e, e ∉ X ∧ X ∪ e ⊆ Y := 
  begin
    refine ⟨λ h,_, λ h, _⟩, 
    cases nonempty_has_elem (ssubset_diff_nonempty h) with e he, use e, 
    exact ⟨(elem_diff_iff.mp he).2, union_of_subsets h.1 (subset_trans he (diff_subset _ _))⟩ ,  
    rcases h with ⟨e,⟨he1,he2⟩⟩, 
    exact ssubset_subset_trans (add_nonelem_ssubset he1) he2,
  end


lemma size_union_distinct_singles {e f : single A}: 
  e ≠ f → size (e ∪ f :A) = 2 :=
  begin
    intros hef, 
    have : ¬((e:A) ⊆ (f:A)) := λ h, hef (nested_singles_eq h), 
    have := add_nonelem_size this, 
    rw [union_comm, size_coe_single] at this, 
    linarith, 
  end 

lemma size_union_singles_lb (e f : single A): 
  1 ≤ size (e ∪ f : A) := 
  by {linarith [size_monotone (subset_union_left (e:A) f), size_coe_single e]}

lemma size_union_singles_ub (e f : single A):
  size (e ∪ f :A) ≤ 2 := 
  by {by_cases e = f, rw [h, union_idem, size_coe_single], linarith, linarith [size_union_distinct_singles h]}

lemma subset_single {e : single A}{X : A} :
  X ⊆ e → X = ⊥ ∨ X = e := 
  begin
    intro h, cases lt_or_ge 0 (size X), 
    apply or.inr, exact eq_of_eq_size_subset h (by linarith [size_coe_single e, size_monotone h]), 
    apply or.inl, exact (size_zero_bot (by linarith [size_nonneg X])),
  end

lemma ssubset_pair {e f : single A}{X : A}:
  X ⊂ (e ∪ f : A) → X = ⊥ ∨ (X = e) ∨ (X = f) :=
  begin
    intro h, cases h with hs hne, rw [inter_subset, inter_distrib_left] at hs,
    cases subset_single (inter_subset_right X e),
    rw [h, bot_union, ←inter_subset] at hs, cases subset_single hs, exact or.inl h_1, apply or.inr, exact or.inr h_1,
    rw [inter_comm, ←inter_subset] at h, apply or.inr, cases subset_single (inter_subset_right X f),
    rw [h_1, union_bot, ←inter_subset] at hs,  exact or.inl (subset_antisymm hs h), 
    rw [inter_subset, inter_comm] at h,
    rw [h_1, h] at hs, exfalso, exact hne hs.symm, 
  end


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
  λ h, by {rw inter_subset at *, rw [←emb.on_inter, h]}

def embed.single_emb {A B : boolalg} (emb : embed A B) : @single A → @single B := 
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
  compl := λ X, ⟨ground - X.val, diff_subset ground X.val⟩,
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



end API 
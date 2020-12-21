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
  (contains_single_ax (X : member) : X ≠ bot → ∃ Y, subset Y X ∧ size Y = 1)


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
@[simp] instance i8  : has_sdiff A := {sdiff := λ (X Y), X ∩ Yᶜ}
@[simp] instance i9  : has_ssubset A := {ssubset := λ X Y, X ⊆ Y ∧ X ≠ Y}

def size  (X : A) : ℤ := A.size X
def symm_diff  (X Y : A) : A := (X \ Y) ∪ (Y \ X)


@[simp] lemma diff_def (X Y : A) : X \ Y = X ∩ Yᶜ := 
  rfl 

-- Lemmas (some are just the axioms rewritten in terms of the notation to make linarith etc behave more nicely)

-- Commutativity

lemma inter_comm (X Y : A) : (X ∩ Y = Y ∩ X) := 
  A.inter_comm_ax X Y

lemma union_comm (X Y : A) : (X ∪ Y = Y ∪ X) := 
  A.union_comm_ax X Y

-- Top/Bottom with unions and intersections 

@[simp] lemma inter_top (X : A) : X ∩ ⊤ = X := A.inter_top_ax X

@[simp] lemma top_inter  (X : A) : ⊤ ∩ X = X := 
  eq.trans (inter_comm ⊤ X) (inter_top  X) 

@[simp] lemma union_bot {A : boolalg} (X : A) : X ∪ ⊥ = X := A.union_bot_ax X 

@[simp] lemma bot_union {A : boolalg} (X : A) : 
  ⊥ ∪ X = X := 
  eq.trans (union_comm ⊥ X) (union_bot X)


-- Complements

@[simp] lemma union_compl {A: boolalg} (X: A) : 
  X ∪ Xᶜ = ⊤ := 
  A.union_compl_ax X 

@[simp] lemma inter_compl {A: boolalg} (X: A) : X ∩ Xᶜ = ⊥ 
  := A.inter_compl_ax X 

@[simp] lemma union_compl_rev {A: boolalg} (X: A) : Xᶜ ∪ X = ⊤ := 
  by rw [union_comm, union_compl]

@[simp] lemma inter_compl_rev {A: boolalg} (X: A) : Xᶜ ∩ X = ⊥ := 
  by rw [inter_comm, inter_compl]

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

@[simp] lemma union_idem (X : A) : X ∪ X = X := 
  by rw [←(inter_top  (X ∪ X)), ←(union_compl X), ←(union_distrib_left X X Xᶜ), inter_compl, union_bot]

@[simp] lemma inter_idem (X : A): X ∩ X = X := 
  by rw [←(union_bot (X ∩ X)), ←(inter_compl X), ←(inter_distrib_left X X Xᶜ), union_compl, inter_top ]

@[simp] lemma union_top  (X : A) : X ∪ ⊤ = ⊤ := 
  by calc _ = ⊤ ∩ (X ∪ ⊤)        : by rw top_inter
            ... = (X ∪ Xᶜ) ∩ (X ∪ ⊤) : by rw ←union_compl 
            ... = ⊤    : by rw [←union_distrib_left, inter_top , union_compl]

@[simp] lemma top_union (X : A) : ⊤ ∪ X = ⊤ := 
  eq.trans (union_comm ⊤ X) (union_top X)


@[simp] lemma inter_bot  (X : A) : X ∩ ⊥ = ⊥ := 
  by calc X ∩ ⊥ = ⊥ ∪ (X ∩ ⊥)        : by rw bot_union
            ... = (X ∩ Xᶜ) ∪ (X ∩ ⊥) : by rw inter_compl 
            ... = ⊥    : by rw [←inter_distrib_left, union_bot, inter_compl]

@[simp] lemma bot_inter  (X : A) : ⊥ ∩ X = ⊥ := 
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
  


-- Associativity (In fact, this can be discarded eventually, but why bother?)

lemma inter_assoc (X Y Z : A) : (X ∩ Y) ∩ Z = X ∩ (Y ∩ Z) := 
  A.inter_assoc_ax X Y Z 

lemma union_assoc (X Y Z : A) : (X ∪ Y) ∪ Z = X ∪ (Y ∪ Z) := 
  A.union_assoc_ax X Y Z 


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



-- Subsets 


lemma subset_def_union (X Y : A) : (X ⊆ Y) ↔ (X ∪ Y = Y) := 
  A.union_subset_ax X Y 

lemma subset_def_inter (X Y: A) : (X ⊆ Y) ↔ (X ∩ Y = X) :=
  by {rw subset_def_union, from ⟨λ h, by rw [←h, absorb_inter_union], λ h, by rw[←h, union_comm, inter_comm, absorb_union_inter]⟩} 

lemma subset_refl (X : A) : X ⊆ X :=
  by rw [subset_def_inter, inter_idem]

lemma subset_def_inter_mp  {X Y : A} : X ⊆ Y → X ∩ Y = X := 
  (subset_def_inter X Y).mp 

lemma subset_def_inter_mpr  {X Y : A} : X ∩ Y = X → X ⊆ Y  := 
  (subset_def_inter X Y).mpr 

lemma subset_def_union_mp  {X Y : A} : X ⊆ Y → X ∪ Y = Y :=
  (subset_def_union X Y).mp

lemma subset_def_union_mpr {X Y : A} : X ∪ Y = Y → X ⊆ Y := 
  (subset_def_union X Y).mpr 

lemma subset_ssubset_or_eq {X Y : A} : (X ⊆ Y) → (X ⊂ Y) ∨ X =Y :=
  λ hXY, by {by_cases X = Y, from or.inr h, from or.inl ⟨hXY, h⟩}

lemma ssubset_size {X Y : A} : (X ⊆ Y) → (size X < size Y) → (X ⊂ Y) := 
  λ hXY hS, ⟨hXY, by {intros heq, rw heq at hS, linarith}⟩

lemma subset_antisymm  {X Y : A} : X ⊆ Y → Y ⊆ X → X = Y := 
  λ hXY hYX, by {rw subset_def_inter at *, rw inter_comm at hXY, from (rfl.congr hYX).mp (eq.symm hXY)}

lemma inter_subset_left {A: boolalg} (X Y : A) : (X ∩ Y) ⊆ X := 
  by {apply subset_def_union_mpr; rw union_comm; apply absorb_union_inter}

lemma inter_subset_right (X Y : A) : (X ∩ Y) ⊆ Y := 
  by {rw inter_comm, apply inter_subset_left}

lemma subset_union_left (X Y : A) : X ⊆ X ∪ Y := 
  by {apply subset_def_inter_mpr, rw absorb_inter_union}

lemma subset_union_right (X Y : A) : Y ⊆ X ∪ Y := 
  by {rw union_comm, from subset_union_left Y X} 
   
lemma subset_top (X : A) : X ⊆ ⊤ := 
  by {apply subset_def_inter_mpr; from (inter_top X)}

lemma top_subset  {X : A} : ⊤ ⊆ X → X = ⊤ := 
  λ h, subset_antisymm (subset_top X) h

lemma bot_subset  (X : A) : ⊥ ⊆ X := 
  by {apply subset_def_inter_mpr, from (bot_inter X)}

lemma subset_bot  {X : A} (hX : X ⊆ ⊥) : X = ⊥ := 
  subset_antisymm hX (bot_subset X)  

lemma ssubset_bot (X : A) : ¬ X ⊂ ⊥ := 
  λ h, h.2 (subset_bot h.1) 

lemma disjoint_compl_subset {X Y : A} : X ∩ Y = ⊥ → X ⊆ Yᶜ := 
  λ h, by rw [subset_def_inter, ← bot_union (X ∩ Yᶜ), ←h, ←inter_distrib_left, union_compl, inter_top]

lemma cover_compl_subset {X Y : A} :  X ∪ Y = ⊤ → Xᶜ ⊆ Y  := 
  λ h, by rw [subset_def_union, ←top_inter (Xᶜ ∪ Y), ←h, ←union_distrib_right, inter_compl, bot_union]

lemma compl_unique {X Y : A} : X ∪ Y = ⊤ → X ∩ Y = ⊥ → Y = Xᶜ := 
  λ hU hI, by {apply subset_antisymm, from disjoint_compl_subset (eq.trans (inter_comm Y X) hI), from cover_compl_subset hU}

@[simp] lemma compl_compl  (X : A) : Xᶜᶜ = X := 
  by {apply subset_antisymm, apply cover_compl_subset, from eq.trans (union_comm Xᶜ X) (union_compl X), from disjoint_compl_subset (inter_compl X)}

lemma compl_inj {X Y : A} : Xᶜ = Yᶜ → X = Y := 
  λ h, by rw [←compl_compl X, ←compl_compl Y, h]

lemma compl_inj_iff {X Y : A} : Xᶜ = Yᶜ ↔ X = Y := 
  ⟨λ h, compl_inj h, λ h, by rw h⟩ 

@[simp] lemma compl_top (A : boolalg) : (⊤ : A)ᶜ = ⊥ := 
  eq.symm (compl_unique (top_union ⊥) (inter_bot ⊤))

@[simp] lemma compl_bot (A : boolalg) : (⊥ : A)ᶜ = ⊤ := 
  eq.symm (compl_unique (union_top ⊥) (bot_inter ⊤)) 

lemma bot_of_compl_top {X : A} (hX : Xᶜ = ⊤) : X = ⊥  := 
  by rw [←compl_compl X, hX, compl_top]

lemma top_of_compl_bot {X : A} (hX : Xᶜ = ⊥) : X = ⊤  := 
  by rw [←compl_compl X, hX, compl_bot]

@[simp] lemma inter_compl_left {X : A} : Xᶜ ∩ X = ⊥ := 
  by rw [inter_comm, inter_compl]

@[simp] lemma union_compl_left {X : A} : Xᶜ ∪ X = ⊤ := 
  by rw [union_comm, union_compl]

@[simp] lemma union_compl_union  (X Y : A) : X ∪ (Xᶜ ∪ Y) = ⊤ :=  
  by rw [←top_inter(X ∪ (Xᶜ ∪ Y)), ←union_compl, ←union_distrib_left, absorb_inter_union] 

@[simp] lemma inter_compl_inter (X Y : A) : X ∩ (Xᶜ ∩ Y) = ⊥ := 
  by rw [←bot_union(X ∩ (Xᶜ ∩ Y)), ←inter_compl, ←inter_distrib_left, absorb_union_inter]

@[simp] lemma inter_compl_union (X Y : A) : X ∩ (Xᶜ ∪ Y) = X ∩ Y :=
  by rw [inter_distrib_left, inter_compl, bot_union]

@[simp] lemma union_compl_inter (X Y : A) : X ∪ (Xᶜ ∩ Y) = X ∪ Y :=
  by rw [union_distrib_left, union_compl, top_inter]

@[simp] lemma union_inter_compl_inter (X Y : A) : (X ∪ Y) ∪ (Xᶜ ∩ Yᶜ)  = ⊤ := 
  by rw [union_distrib_left, union_comm _ Xᶜ, union_comm X Y, union_comm _ Yᶜ,
      ←(compl_compl Y),  compl_compl Yᶜ, union_compl_union Yᶜ, union_comm _ X, 
      ←(compl_compl X),    compl_compl Xᶜ, union_compl_union Xᶜ, inter_idem]

@[simp] lemma inter_union_compl_union (X Y : A) : (X ∩ Y) ∩ (Xᶜ ∪ Yᶜ)  = ⊥ := 
  by rw [inter_distrib_left, inter_comm _ Xᶜ, inter_comm X Y, inter_comm _ Yᶜ, 
        ←(compl_compl Y), compl_compl Yᶜ, inter_compl_inter Yᶜ, inter_comm _ X, 
        ←(compl_compl X), compl_compl Xᶜ, inter_compl_inter Xᶜ, union_idem]
  
@[simp] lemma inter_union_compl_inter (X Y : A) : (X ∪ Y) ∩ (Xᶜ ∩ Yᶜ) = ⊥ := 
  by rw [inter_distrib_right X Y, inter_compl_inter, inter_comm Xᶜ, inter_compl_inter, union_idem]
  
@[simp] lemma union_inter_compl_union  (X Y : A) : (X ∩ Y) ∪ (Xᶜ ∪ Yᶜ) = ⊤ := 
  by rw [union_distrib_right X Y, union_compl_union, union_comm Xᶜ, union_compl_union, inter_idem]

lemma compl_inter (X Y : A) : (X ∩ Y)ᶜ = Xᶜ ∪ Yᶜ := 
  eq.symm (compl_unique (union_inter_compl_union X Y) (inter_union_compl_union X Y))

lemma compl_union (X Y : A) : (X ∪ Y)ᶜ = Xᶜ ∩ Yᶜ := 
  eq.symm (compl_unique (union_inter_compl_inter X Y) (inter_union_compl_inter X Y))

lemma compl_compl_inter_left (X Y : A) : (Xᶜ ∩ Y)ᶜ = X ∪ Yᶜ := 
  by {nth_rewrite 0 ←(compl_compl Y), rw [compl_inter, compl_compl, compl_compl] }

lemma compl_compl_inter_right (X Y : A) : (X ∩ Yᶜ)ᶜ = Xᶜ ∪ Y := 
  by {nth_rewrite 0 ←(compl_compl X), rw [compl_inter, compl_compl, compl_compl] }

lemma compl_compl_union_left (X Y : A) : (Xᶜ ∪ Y)ᶜ = X ∩ Yᶜ := 
  by {nth_rewrite 0 ←(compl_compl Y), rw [compl_union, compl_compl, compl_compl] }

lemma compl_compl_union_right (X Y : A) : (X ∪ Yᶜ)ᶜ = Xᶜ ∩ Y := 
  by {nth_rewrite 0 ←(compl_compl X), rw [compl_union, compl_compl, compl_compl] }

lemma compl_partition (X Y : A) : (X ∩ Y) ∪ (Xᶜ ∩ Y) = Y := 
  by rw [←inter_distrib_right, union_compl, top_inter]

lemma compl_partition_subset  {X Y : A}: X ⊆ Y → X ∪ (Xᶜ ∩ Y) = Y := 
  λ h, by {nth_rewrite 0 ←(subset_def_inter_mp h), from compl_partition X Y}

lemma compl_pair {X Y : A} : (Xᶜ = Y) → (X = Yᶜ) := 
  λ h, by rw [←h, compl_compl]

lemma compl_diff (X Y : A) : (X \ Y)ᶜ = Xᶜ ∪ Y := 
  by {dunfold has_sdiff.sdiff, rw [compl_inter, compl_compl]}

@[simp] lemma union_union_compl (X Y : A) : X ∪ (Y ∪ Yᶜ) = ⊤ := 
  by rw[union_compl, union_top]

@[simp] lemma inter_inter_compl (X Y : A) : X ∩ (Y ∩ Yᶜ) = ⊥ := 
  by rw[inter_compl, inter_bot]

@[simp] lemma union_inter_compl (X Y : A) : X ∪ (Y ∩ Yᶜ) = X :=
  by rw [inter_compl, union_bot]

@[simp] lemma inter_union_compl (X Y : A) : X ∩ (Y ∪ Yᶜ) = X :=
  by rw [union_compl, inter_top]

lemma subset_to_compl {X Y : A} : X ⊆ Y → Yᶜ ⊆ Xᶜ := 
  λ hXY, by {rw subset_def_inter at hXY, rw [←hXY, compl_inter, union_comm], apply subset_union_left} 

lemma compl_to_subset {X Y : A}: Xᶜ ⊆ Yᶜ → Y ⊆ X := 
  λ hXY, by {have := subset_to_compl hXY, repeat {rw compl_compl at this}, from this }

lemma subset_compl_right {X Y : A}: X ⊆ Yᶜ → Y ⊆ Xᶜ := 
  λ hXY, by {rw [←compl_compl X] at hXY, from compl_to_subset hXY}

lemma subset_compl_left {X Y : A} : Xᶜ ⊆ Y → Yᶜ ⊆ X := 
  λ hXY, by {rw [←compl_compl Y] at hXY, from compl_to_subset hXY}

lemma subset_of_compl_iff_disjoint {X Y: A} : X ⊆ Yᶜ ↔ X ∩ Y = ⊥ := 
  begin 
        rw subset_def_inter,  refine ⟨λ h, _, λ h, _⟩, 
        rw [←h, inter_assoc, inter_comm _ Y, inter_compl, inter_bot], 
        rw [←union_bot (X ∩ Yᶜ), ←h, ←inter_distrib_left, union_comm, union_compl, inter_top] 
  end

lemma subset_own_compl {X : A} : X ⊆ Xᶜ → X = ⊥ := 
  λ h, by {rw [subset_def_union,union_compl, ←compl_bot, compl_inj_iff] at h, rw ←h }
----

-- more subsets 
lemma disjoint_iff_subset_compl {X Y : A} : X ∩ Y = ⊥ ↔ X ⊆ Yᶜ := 
  by {refine ⟨λ h, _, λ h, _⟩, rw [subset_def_inter, ←union_bot (X ∩ Yᶜ), ←h, ←inter_distrib_left], simp, 
    rw [subset_def_inter] at h, rw [←h, inter_assoc], simp } 

lemma subset_trans {X Y Z : A} : X ⊆ Y → Y ⊆ Z →  X ⊆ Z :=
  λ hXY hYZ, by {rw subset_def_inter at *, rw [←hXY, inter_assoc, hYZ]}

lemma inter_subset_union (X Y : A) : X ∩ Y ⊆ X ∪ Y := 
  subset_trans (inter_subset_left X Y) (subset_union_left X Y)

lemma subset_of_inter_mp {X Y Z : A} : X ⊆ Y ∩ Z → X ⊆ Y ∧ X ⊆ Z := 
  λ h, ⟨subset_trans h (inter_subset_left _ _), subset_trans h (inter_subset_right _ _)⟩  

lemma union_of_subsets {X Y Z : A} : (X ⊆ Z) → (Y ⊆ Z) → (X ∪ Y ⊆ Z) := 
  λ hXZ hYZ, by {rw subset_def_inter at *, rw [inter_distrib_right, hXZ, hYZ]}

lemma subset_of_inter_mpr  {X Y Z : A} : (X ⊆ Y) → (X ⊆ Z) → (X ⊆ Y ∩ Z) := 
  λ hXY hXZ, by {rw subset_def_inter at *, rw [←inter_assoc, hXY, hXZ]}

lemma subset_of_inter_iff {X Y Z :A} : X ⊆ (Y ∩ Z) ↔ (X ⊆ Y ∧ X ⊆ Z) := 
  ⟨λ h, subset_of_inter_mp h, λ h, subset_of_inter_mpr  h.1 h.2⟩

lemma inter_of_subsets (X Y Z : A) : (X ⊆ Z) → (X ∩ Y ⊆ Z) := 
  λ h, subset_trans (inter_subset_left X Y) h

lemma union_of_supsets (X Y Z : A) : (X ⊆ Y) → (X ⊆ Y ∪ Z) := 
  λ h, subset_trans h (subset_union_left Y Z)

lemma subset_inter_subset_left (X Y Z : A) : (X ⊆ Y) → (X ∩ Z) ⊆ (Y ∩ Z) := 
  λ hXY, by {rw subset_def_inter at *, rw [←inter_distrib_inter_left, hXY]}

lemma subset_inter_subset_right (X Y Z : A) : (X ⊆ Y) → (Z ∩ X) ⊆ (Z ∩ Y) := 
  by {rw [inter_comm _ X, inter_comm _ Y], apply subset_inter_subset_left }

lemma subset_union_subset_left (X Y Z : A) : (X ⊆ Y) → (X ∪ Z) ⊆ (Y ∪ Z) := 
  λ hXY, by {rw subset_def_union at *, rw [←union_distrib_union_left, hXY]}

lemma subset_union_subset_right (X Y Z : A) : (X ⊆ Y) → (Z ∪ X) ⊆ (Z ∪ Y) := 
  by {rw [union_comm _ X, union_comm _ Y], apply subset_union_subset_left }

lemma union_subset_pairs {X₁ X₂ Y₁ Y₂ : A} : X₁ ⊆ Y₁ → X₂ ⊆ Y₂ → X₁ ∪ X₂ ⊆ Y₁ ∪ Y₂ :=
  λ h₁ h₂, subset_trans (subset_union_subset_left X₁ Y₁ X₂ h₁) (subset_union_subset_right X₂ Y₂ Y₁ h₂) 

lemma subset_of_set_and_compl {X Y: A} : X ⊆ Y → X ⊆ Yᶜ → X = ⊥ :=
  λ h1 h2, by {have := subset_of_inter_mpr h1 h2, rw inter_compl at this, from subset_bot this}

lemma subset_ssubset_trans {X Y Z : A} : X ⊆ Y → Y ⊂ Z → X ⊂ Z := 
  λ hXY hYZ, ⟨subset_trans hXY hYZ.1, λ h, by {rw ←h at hYZ, from hYZ.2 (subset_antisymm hYZ.1 hXY)}⟩ 

lemma ssubset_subset_trans {X Y Z : A} : X ⊂ Y → Y ⊆ Z → X ⊂ Z := 
  λ hXY hYZ, ⟨subset_trans hXY.1 hYZ, λ h, by {rw h at hXY, from hXY.2 (subset_antisymm hXY.1 hYZ)}⟩ 

@[simp] lemma ssubset_iff {X Y : A} : X ⊂ Y ↔ (X ⊆ Y) ∧ (X ≠ Y) :=
  by unfold has_ssubset.ssubset

lemma ssubset_irrefl (X : A) : ¬ (X ⊂ X) :=
  λ h, h.2 rfl

lemma ssubset_not_supset {X Y : A} : X ⊂ Y → ¬(Y ⊆ X) :=
  λ h h', ssubset_irrefl _ (ssubset_subset_trans h h') 

lemma subset_not_ssupset {X Y : A} : X ⊆ Y → ¬(Y ⊂ X) := 
  λ h h', ssubset_irrefl _ (subset_ssubset_trans h h')

lemma eq_of_ssubset {X Y: A} : X ⊆ Y → ¬(X ⊂ Y) → X = Y := 
  λ h h', by {simp only [not_and, not_not, ssubset_iff] at h', from h' h}

lemma ssubset_trans {X Y Z : A}: X ⊂ Y → Y ⊂ Z → X ⊂ Z := 
  λ hXY hYZ, subset_ssubset_trans hXY.1 hYZ

lemma ssubset_inter {X Y : A} : X ≠ Y → X ∩ Y ⊂ X ∨ X ∩ Y ⊂ Y:=
  λ h, by {by_contra, push_neg at a, cases a, erw [not_and', not_imp_not] at a_left a_right, 
  from h (eq.trans (a_left (inter_subset_left X Y)).symm (a_right (inter_subset_right X Y)) )}

-- Misc

lemma inter_is_lb  {X Y Z : A} : Z ⊆ X → Z ⊆ Y → Z ⊆ (X ∩ Y) := 
  λ hZX hZY, by {rw subset_def_inter at *, rw [←inter_assoc, hZX, hZY]}

lemma union_is_ub  {X Y Z : A} : X ⊆ Z → Y ⊆ Z → X ∪ Y ⊆ Z := 
  λ hXZ hYZ, by {rw subset_def_union at *, rw [union_assoc, hYZ, hXZ]}

lemma union_of_disjoint {X Y Z : A} : X ∩ Y = ⊥ → X ∩ Z = ⊥ → X ∩ (Y ∪ Z) = ⊥ :=
  λ hY hZ, by {rw [inter_distrib_left, hY, hZ], simp }

lemma diff_subset  (X Y : A) : X \ Y ⊆ X := 
  inter_subset_left X Yᶜ

@[simp] lemma diff_union (X Y : A): (X ∩ Y) ∪ (X \ Y) = X  := 
  by rw [diff_def, ←inter_distrib_left, union_compl, inter_top]

@[simp] lemma inter_diff (X Y : A): X ∩ (Y \ X)  = ⊥ := 
  by rw [diff_def, ←inter_assoc, inter_right_comm, inter_compl, bot_inter]

@[simp] lemma partition_inter (X Y : A) : (X ∩ Y) ∩ (X \ Y) = ⊥ := 
  by rw [inter_assoc, inter_diff, inter_bot]

@[simp] lemma diffs_disj (X Y : A) : (X \ Y) ∩ (Y \ X) = ⊥ := 
  by {simp only [diff_def], rw [inter_assoc, ←inter_assoc Yᶜ], simp}

lemma diff_bot_subset (X Y : A) : X \ Y = ⊥ → X ⊆ Y := 
  λ hXY, by {rw [←diff_union X Y, hXY, union_bot], apply inter_subset_right}

lemma subset_diff_bot (X Y : A) : X ⊆ Y → X \ Y = ⊥ := 
  λ hXY, by {rw diff_def, rw subset_def_inter at hXY, rw [←hXY, inter_assoc, inter_compl, inter_bot]}

lemma diff_bot_iff_subset (X Y : A) : X \ Y = ⊥ ↔ X ⊆ Y := 
  by {split, apply diff_bot_subset, apply subset_diff_bot}

lemma subset_diff_disjoint (X Y Z: A) : X ⊆ Y → X ∩ Z = ⊥ → X ⊆ Y \ Z := 
  λ hXY hXZ, by {rw [disjoint_iff_subset_compl, subset_def_inter] at hXZ, 
                rw [diff_def, subset_def_inter, inter_comm Y, ←inter_assoc, hXZ, subset_def_inter_mp hXY], }

lemma ssubset_diff_nonempty {X Y : A} : X ⊂ Y → Y \ X ≠ ⊥ :=
  λ hXY, by {intros hYX, rw diff_bot_iff_subset at hYX, from hXY.2 (subset_antisymm hXY.1 hYX)}

lemma union_diff_of_subset  {X Y : A} : X ⊆ Y → X ∪ (Y \ X) = Y := 
  λ h, by {rw [subset_def_inter, inter_comm] at h, have := diff_union Y X, rw h at this, from this}

@[simp] lemma diff_inter (X Y : A) : (Y \ X) ∩ X = ⊥ := 
  by rw [inter_comm, inter_diff]

@[simp] lemma union_diff (X Y : A) : X ∪ (Y \ X) = X ∪ Y := 
  by {rw [diff_def, union_distrib_left, union_compl, inter_top]}

@[simp] lemma union_diff_diff (X Y : A) : (X ∪ Y) \ (Y \ X) = X := 
  by rw [diff_def, diff_def, compl_inter,compl_compl,union_comm, ←union_distrib_right, inter_compl, bot_union]

lemma inter_distrib_diff (X Y Z : A) : X ∩ (Y \ Z) = (X ∩ Y) \ (X ∩ Z) := 
  by {rw [diff_def, diff_def, compl_inter, inter_distrib_left, inter_right_comm, inter_compl, bot_inter, bot_union, ←inter_assoc]}

@[simp] lemma diff_bot (X : A) : X \ ⊥ = X := 
  by {rw [diff_def, compl_bot, inter_top]} 

@[simp] lemma bot_diff (X : A) : ⊥ \ X = ⊥ := 
  by rw [diff_def, bot_inter]

@[simp] lemma top_diff (X : A) : ⊤ \ X = Xᶜ := 
  by rw [diff_def, top_inter]

@[simp] lemma diff_top (X : A) : X \ ⊤ = ⊥ := 
  by rw [diff_def, compl_top, inter_bot]

@[simp] lemma diff_self (X : A) : X \ X = ⊥ := 
  inter_compl X 

@[simp] lemma symm_diff_self (X : A) : symm_diff X X = ⊥ :=
  by {unfold symm_diff, rw [diff_self, bot_union]}

lemma symm_diff_alt (X Y : A) : symm_diff X Y = (X ∪ Y) \ (X ∩ Y) := 
begin
   unfold symm_diff, 
   repeat {rw [diff_def]}, 
   rw [compl_inter, inter_distrib_right, inter_distrib_left, inter_distrib_left],
   simp,   
end  

lemma size_monotone {X Y: A} (hXY : X ⊆ Y) : size X ≤ size Y := 
  by {have := size_modular X (Y \ X), rw union_diff_of_subset  hXY at this      , 
        rw inter_diff at this, linarith [size_nonneg(Y \ X), size_bot A]}

lemma size_subadditive {X Y : A} : size (X ∪ Y) ≤ size X + size Y :=
  by linarith [size_modular X Y, size_nonneg (X ∩ Y)] 

lemma compl_inter_size (X Y : A) : size (X ∩ Y) + size (Xᶜ ∩ Y) = size Y := 
  by rw [←size_modular, ←inter_distrib_right, union_compl, top_inter, ←inter_distrib_inter_left, inter_compl, bot_inter, size_bot]; ring

lemma compl_inter_size_subset {X Y : A} : X ⊆ Y → size (Xᶜ ∩ Y) = size Y - size X := 
  λ hXY, by {have := compl_inter_size X Y, rw subset_def_inter_mp hXY at this, linarith} 

lemma diff_size {X Y : A} : X ⊆ Y → size (Y \ X) = size Y - size X :=  
  λ hXY, by rw [diff_def, inter_comm, compl_inter_size_subset hXY]

lemma size_disjoint_sum {X Y : A}: X ∩ Y = ⊥ → size (X ∪ Y) = size X + size Y := 
  λ hXY, by {have := size_modular X Y, rw [hXY, size_bot] at this, linarith}

lemma size_modular_diff (X Y : A) : size (X ∪ Y) = size (X \ Y) + size (Y \ X) + size (X ∩ Y) :=
  by {rw [←size_disjoint_sum (diffs_disj X Y)], have := (symm_diff_alt X Y), 
        unfold symm_diff at this,rw this, linarith [diff_size (inter_subset_union X Y)]  }


lemma size_induced_partition (X Y : A) : size X = size (X ∩ Y) + size (X \ Y) := 
  by {nth_rewrite 0 ←diff_union X Y, refine size_disjoint_sum _, apply partition_inter}

lemma size_compl_sum (X : A) : size X + size Xᶜ = size (⊤ : A) := 
  by {have := size_disjoint_sum (inter_compl X), rw (union_compl X) at this, linarith}

lemma size_zero_bot {X : A} : (size X = 0) →  X = ⊥ := 
  λ h, by {by_contra h', cases contains_single X h' with Y hY, cases hY, linarith [size_monotone hY_left] }
    
lemma size_zero_iff_bot {X : A} : (size X = 0) ↔ (X = ⊥) := 
  by {split, apply size_zero_bot, intros h, rw h, from size_bot A}

lemma size_nonempty {X : A} : X ≠ ⊥ → 0 < size X  := 
  λ hX, lt_of_le_of_ne (size_nonneg X) (λ h, hX (size_zero_bot h.symm))

lemma size_strict_monotone {X Y : A} : X ⊂ Y → size X < size Y := 
  λ hXY, by {rw [size_induced_partition Y X, inter_comm, subset_def_inter_mp hXY.1], 
                linarith [size_nonempty (ssubset_diff_nonempty hXY)]} 

lemma eq_of_eq_size_subset {X Y : A} : (X ⊆ Y) → (size X = size Y) → X = Y :=
  λ hXY, by {cases subset_ssubset_or_eq hXY, intros sXY, exfalso, replace h := size_strict_monotone h, linarith, from λ h', h}

lemma eq_of_ge_size_subset {X Y : A} : (X ⊆ Y) → (size Y ≤ size X) → X = Y :=
  λ hXY hXY', by {apply eq_of_eq_size_subset hXY, from le_antisymm (size_monotone hXY) hXY'}

lemma size_eq_of_supset {X Y : A} : (X ⊆ Y) → (size Y ≤ size X) → size X = size Y := 
  λ hss hs, by linarith[size_monotone hss]

lemma single_subset (X : A) : X ≠ ⊥ → (∃ Y Z, Y ∩ Z = ⊥ ∧ Y ∪ Z = X ∧ size Y = 1) := 
  begin
    intro h, cases contains_single X h with Y hY, use Y, use X \ Y, 
    from ⟨inter_diff _ _,⟨union_diff_of_subset  hY.1,hY.2⟩⟩,
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

lemma ssubset_to_compl {X Y : A} : X ⊂ Y → Yᶜ ⊂ Xᶜ := 
  λ h, ⟨subset_to_compl h.1, λ h', h.2 (compl_inj h').symm⟩

lemma compl_to_ssubset {X Y : A} : Xᶜ ⊂ Yᶜ → Y ⊂ X := 
  λ h, by {have := ssubset_to_compl h, repeat {rw compl_compl at this}, from this }

lemma ssubset_compl_right {X Y : A} : X ⊂ Yᶜ → Y ⊂ Xᶜ := 
  λ h, by {rw [←compl_compl X] at h, from compl_to_ssubset h}

lemma ssubset_compl_left {X Y : A} : Xᶜ ⊂ Y → Yᶜ ⊂ X := 
  λ h, by {rw [←compl_compl Y] at h, from compl_to_ssubset h}


end boolalg



end API 
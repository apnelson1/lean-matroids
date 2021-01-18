import tactic.ext
--import tactic.ring 
import tactic.linarith
import tactic.tidy 
import tactic 
import .int_lemmas 


-- The API I would like to use for various basic objects.
-- This probably belongs in its own file by this point. 

local attribute [instance] classical.prop_decidable
noncomputable theory 

section API


namespace boolalg 

structure boolalg :=
  (E : Type)
  (is_fin : ∃ (fin : fintype E), true )


def fintype_of (U : boolalg) : fintype (U.E) := classical.some U.is_fin 

def as_finset_top (U : boolalg) := (fintype_of U).elems 

def as_finset (U : boolalg)(X : set U.E) : finset U.E := 
  @set.to_finset _ X (@fintype.subtype_of_fintype _ (fintype_of U) X) 



variables {A : boolalg}

@[simp] instance alg_coe : has_coe_to_sort boolalg := 
  {S := Type, coe := λ A, set (A.E)}


def symm_diff  (X Y : A) : A := (X \ Y) ∪ (Y \ X)


-- Size -----------------------------------------------------

def size_nat (U : boolalg)(X : set U.E) := (as_finset U X).card 

def size {U : boolalg}(X : set U.E) : ℤ := (size_nat U X)

lemma size_bot_ax :
   size (⊥ : A) = 0 := 
  by simp [size, size_nat, as_finset]

lemma size_single_ax (e : A.E): 
  size ({e}:A) = 1 := 
begin
  simp only  [size, size_nat], 
  have : (({e} : set A.E).to_finset = as_finset A {e}) := 
    by rw [as_finset, set.to_finset_inj], 
  rw [←this], 
  norm_cast, 
end

lemma size_modular_ax (X Y : A): 
  size (X ∪ Y) + size (X ∩ Y) = size X + size Y :=
begin
  have hu : as_finset A (X ∪ Y) = as_finset A X ∪ as_finset A Y := by {simp only [as_finset], tidy},
  have hi : as_finset A (X ∩ Y) = as_finset A X ∩ as_finset A Y := by {simp only [as_finset], tidy},
  simp only [size,size_nat,hu,hi], 
  norm_cast, apply finset.card_union_add_card_inter, 
end

lemma size_nonneg (X : A) : 0 ≤ size X := 
  by {simp only [size, size_nat], norm_cast, apply zero_le}  

-------------------------------------------------------------

lemma univ_eq_top :
  set.univ = (⊤ : A) := 
  set.top_eq_univ

lemma empty_eq_bot :
  ∅ = (⊥ : A) := 
  set.bot_eq_empty

--@[simp] def top_size (A : boolalg) := size (⊤ : A)

@[simp] lemma diff_def (X Y : A) : X \ Y = X ∩ Yᶜ := 
  rfl 

def nontrivial (A : boolalg) := (⊥ : A) ≠ ⊤

-- Commutativity

lemma inter_comm (X Y : A) : (X ∩ Y = Y ∩ X) := 
  set.inter_comm _ _

lemma union_comm (X Y : A) : (X ∪ Y = Y ∪ X) := 
  set.union_comm _ _ 

-- Top/Bottom with unions and intersections 

@[simp] lemma inter_top (X : A) : X ∩ ⊤ = X := 
  by simp 

@[simp] lemma top_inter  (X : A) : ⊤ ∩ X = X := 
  by simp 

@[simp] lemma union_bot {A : boolalg} (X : A) : X ∪ ⊥ = X := 
  by simp 

@[simp] lemma bot_union {A : boolalg} (X : A) : 
  ⊥ ∪ X = X := 
  by simp 


-- Complements

@[simp] lemma union_compl {A: boolalg} (X: A) : 
  X ∪ Xᶜ = ⊤ := 
  by simp  

@[simp] lemma inter_compl {A: boolalg} (X: A) : X ∩ Xᶜ = ⊥ := by simp 

@[simp] lemma union_compl_rev {A: boolalg} (X: A) : Xᶜ ∪ X = ⊤ := 
  by rw [union_comm, union_compl]

@[simp] lemma inter_compl_rev {A: boolalg} (X: A) : Xᶜ ∩ X = ⊥ := 
  by rw [inter_comm, inter_compl]

-- Distributivity

lemma union_distrib_right {A : boolalg} (X Y Z : A) : (X ∩ Y) ∪ Z = (X ∪ Z) ∩ (Y ∪ Z) := 
  by apply set.union_distrib_right

lemma union_distrib_left {A : boolalg} (X Y Z : A) : X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z) := 
  by calc X ∪ (Y ∩ Z) = (Y ∩ Z) ∪ X       : union_comm X (Y ∩ Z) 
                  ... = (Y ∪ X) ∩ (Z ∪ X) : union_distrib_right Y Z X  
                  ... = (X ∪ Y) ∩ (X ∪ Z) : by rw [union_comm X Y, union_comm X Z]

lemma inter_distrib_right {A : boolalg} (X Y Z : A) : (X ∪ Y) ∩ Z = (X ∩ Z) ∪ (Y ∩ Z) := 
  by apply set.inter_distrib_right

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

lemma size_modular (X Y : A) : size (X ∪ Y) + size (X ∩ Y) = size (X) + size Y := 
  size_modular_ax X Y

@[simp] lemma size_bot (A : boolalg) : size (⊥ : A) = 0 := 
  size_bot_ax

lemma compl_size (X : A) : size Xᶜ = size (⊤ : A) - size X :=
  calc size Xᶜ = size (X ∪ Xᶜ) + size (X ∩ Xᶜ) - size X : by linarith [size_modular X Xᶜ]
  ...          = size (⊤ : A)  + size (⊥ : A)  - size X : by rw [union_compl X, inter_compl X]
  ...          = size (⊤ : A) - size X                  : by linarith [size_bot A]

lemma size_compl (X : A) : size X = size (⊤ : A) - size(Xᶜ) := 
  by linarith [compl_size X]

lemma contains_single (X : A) : X ≠ ⊥ → (∃ Y, Y ⊆ X ∧ size Y = 1) :=
begin
  intro h, 
  rw [set.bot_eq_empty, set.ne_empty_iff_nonempty] at h, 
  cases h with e he, 
  from ⟨{e},⟨set.singleton_subset_iff.mpr he, size_single_ax e⟩⟩, 
end
  


-- Associativity (In fact, this can be discarded eventually, but why bother?)

lemma inter_assoc (X Y Z : A) : (X ∩ Y) ∩ Z = X ∩ (Y ∩ Z) := 
  set.inter_assoc _ _ _

lemma union_assoc (X Y Z : A) : (X ∪ Y) ∪ Z = X ∪ (Y ∪ Z) := 
  set.union_assoc _ _ _ 


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
  by rw [←set.compl_subset_compl, set.subset_iff_inter_eq_self, ←set.compl_union, compl_inj_iff, union_comm Y X]

lemma subset_def_inter (X Y: A) : (X ⊆ Y) ↔ (X ∩ Y = X) :=
  by {rw subset_def_union, exact ⟨λ h, by rw [←h, absorb_inter_union], λ h, by rw[←h, union_comm, inter_comm, absorb_union_inter]⟩} 

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

lemma subset_ssubset_or_eq {X Y : A} : (X ⊆ Y) → (X ⊂ Y) ∨ X = Y :=
  λ hXY, by {rw or_comm, apply set.eq_or_ssubset_of_subset hXY}


@[simp] lemma ssubset_iff {X Y : A} : X ⊂ Y ↔ (X ⊆ Y) ∧ (X ≠ Y) :=
  set.ssubset_iff_subset_ne

lemma ssubset_of_subset_ne {X Y : A} : X ⊆ Y → X ≠ Y → X ⊂ Y := 
  @lt_of_le_of_ne _ _ X Y 

lemma ssubset_irrefl (X : A) : ¬(X ⊂ X) :=
  λ h, by {rw ssubset_iff at h, from h.2 rfl}


lemma ssubset_size {X Y : A} : (X ⊆ Y) → (size X < size Y) → (X ⊂ Y) := 
  λ h h', by {rw ssubset_iff, from ⟨h, λ h'', by {rw h'' at h', linarith}⟩}


  --λ hXY hS, ⟨hXY, by {intros h, rw h at hS, linarith}⟩

lemma subset_antisymm  {X Y : A} : X ⊆ Y → Y ⊆ X → X = Y := 
  λ hXY hYX, by {rw subset_def_inter at *, rw inter_comm at hXY, exact (rfl.congr hYX).mp (eq.symm hXY)}

lemma inter_subset_left {A: boolalg} (X Y : A) : (X ∩ Y) ⊆ X := 
  by {apply subset_def_union_mpr; rw union_comm; apply absorb_union_inter}

lemma inter_subset_right (X Y : A) : (X ∩ Y) ⊆ Y := 
  by {rw inter_comm, apply inter_subset_left}

lemma subset_union_left (X Y : A) : X ⊆ X ∪ Y := 
  by {apply subset_def_inter_mpr, rw absorb_inter_union}

lemma subset_union_right (X Y : A) : Y ⊆ X ∪ Y := 
  by {rw union_comm, exact subset_union_left Y X} 
   
lemma subset_top (X : A) : X ⊆ ⊤ := 
  by {apply subset_def_inter_mpr; exact (inter_top X)}

lemma top_subset  {X : A} (hX : ⊤ ⊆ X) : X = ⊤ := 
  subset_antisymm (subset_top X) hX

lemma bot_subset  (X : A) : ⊥ ⊆ X := 
  by {apply subset_def_inter_mpr, exact (bot_inter X)}

lemma subset_bot  {X : A} : X ⊆ ⊥ → X = ⊥ := 
  λ hX, subset_antisymm hX (bot_subset X)  

lemma ssubset_bot (X : A) : ¬ X ⊂ ⊥ := 
  λ h, by {rw ssubset_iff at h, from h.2 (subset_bot h.1)}

lemma disjoint_compl_subset {X Y : A} : X ∩ Y = ⊥ → X ⊆ Yᶜ := 
  λ h, by rw [subset_def_inter, ← bot_union (X ∩ Yᶜ), ←h, ←inter_distrib_left, union_compl, inter_top]

lemma subset_compl_disjoint {X Y : A} : X ⊆ Yᶜ → X ∩ Y = ⊥ := 
  λ h, by {rw subset_def_inter at h, rw [←h, inter_assoc], simp}

lemma disjoint_iff_subset_compl {X Y : A} : X ∩ Y = ⊥ ↔ X ⊆ Yᶜ := 
  ⟨λ h, disjoint_compl_subset h, λ h, subset_compl_disjoint h⟩   


lemma cover_compl_subset {X Y : A} :  X ∪ Y = ⊤ → Xᶜ ⊆ Y  := 
  λ h, by rw [subset_def_union, ←top_inter (Xᶜ ∪ Y), ←h, ←union_distrib_right, inter_compl, bot_union]

lemma compl_unique {X Y : A} : X ∪ Y = ⊤ → X ∩ Y = ⊥ → Y = Xᶜ := 
  λ hU hI, by {apply subset_antisymm, exact disjoint_compl_subset (eq.trans (inter_comm Y X) hI), exact cover_compl_subset hU}

@[simp] lemma compl_compl  (X : A) : Xᶜᶜ = X := 
  by {apply subset_antisymm, apply cover_compl_subset, exact eq.trans (union_comm Xᶜ X) (union_compl X), exact disjoint_compl_subset (inter_compl X)}

lemma compl_inj {X Y : A} : Xᶜ = Yᶜ → X = Y := 
  λ h, by rw [←compl_compl X, ←compl_compl Y, h]

lemma compl_inj_iff {X Y : A} : Xᶜ = Yᶜ ↔ X = Y := 
  ⟨λ h, compl_inj h, λ h, by rw h⟩ 

@[simp] lemma compl_top (A : boolalg) : (⊤ : A)ᶜ = ⊥ := 
  eq.symm (compl_unique (top_union ⊥) (inter_bot ⊤))

@[simp] lemma compl_bot (A : boolalg) : (⊥ : A)ᶜ = ⊤ := 
  eq.symm (compl_unique (union_top ⊥) (bot_inter ⊤)) 

@[simp] lemma bot_iff_compl_top {X : A} : Xᶜ = ⊤ ↔ X = ⊥ := 
  by rw [←compl_bot, compl_inj_iff]

lemma bot_of_compl_top {X : A} : Xᶜ = ⊤ → X = ⊥  := 
  by {rw [set.top_eq_univ, set.bot_eq_empty], exact set.compl_univ_iff.mp} 

@[simp] lemma top_iff_compl_bot {X : A} : Xᶜ = ⊥ ↔ X = ⊤ := 
  by rw [←compl_top, compl_inj_iff]

lemma top_of_compl_bot {X : A} : Xᶜ = ⊥ → X = ⊤  := 
  by {rw top_iff_compl_bot, exact congr_arg _}

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

lemma compl_partition_subset  {X Y : A} (hXY : X ⊆ Y) : X ∪ (Xᶜ ∩ Y) = Y := 
  by {nth_rewrite 0 ←(subset_def_inter_mp hXY), exact compl_partition X Y}

lemma compl_pair {X Y : A} : (Xᶜ = Y) → (X = Yᶜ) := 
  λ h, by rw [←h, compl_compl]

lemma compl_pair_iff {X Y : A} : (Xᶜ = Y) ↔ (X = Yᶜ) := 
  ⟨λ h, compl_pair h, λ h, by {rw eq_comm at h, from (compl_pair h).symm}⟩

lemma compl_diff (X Y : A) : (X \ Y)ᶜ = Xᶜ ∪ Y := 
  by rw [diff_def, compl_inter, compl_compl]

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
  λ hXY, by {have := subset_to_compl hXY, repeat {rw compl_compl at this}, exact this }

lemma subset_compl_right {X Y : A}: X ⊆ Yᶜ → Y ⊆ Xᶜ := 
  λ hXY, by {rw [←compl_compl X] at hXY, exact compl_to_subset hXY}

lemma subset_compl_left {X Y : A} : Xᶜ ⊆ Y → Yᶜ ⊆ X := 
  λ hXY, by {rw [←compl_compl Y] at hXY, exact compl_to_subset hXY}

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

/--/ by {refine ⟨λ h, _, λ h, _⟩, rw [subset_def_inter, ←union_bot (X ∩ Yᶜ), ←h, ←inter_distrib_left], simp, 
    rw [subset_def_inter] at h, rw [←h, inter_assoc], sorry  } -/

@[trans] lemma subset_trans {X Y Z : A} : X ⊆ Y → Y ⊆ Z →  X ⊆ Z :=
  λ hXY hYZ, by {rw subset_def_inter at *, rw [←hXY, inter_assoc, hYZ]}

--instance i_subset_trans : is_trans A (λ X Y : A ,X ⊆ Y) := { trans := λ X Y Z, @subset_trans _ X Y Z }

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
  λ h1 h2, by {have := subset_of_inter_mpr h1 h2, rw inter_compl at this, exact subset_bot this}

lemma subset_ssubset_trans {X Y Z : A} : X ⊆ Y → Y ⊂ Z → X ⊂ Z := 
  @lt_of_le_of_lt _ _ X Y Z

lemma ssubset_subset_trans {X Y Z : A} : X ⊂ Y → Y ⊆ Z → X ⊂ Z := 
  @lt_of_lt_of_le _ _ X Y Z 

lemma ssubset_not_supset {X Y : A} : X ⊂ Y → ¬(Y ⊆ X) :=
  λ h h', ssubset_irrefl _ (ssubset_subset_trans h h') 

lemma subset_not_ssupset {X Y : A} : X ⊆ Y → ¬(Y ⊂ X) := 
  λ h h', ssubset_irrefl _ (subset_ssubset_trans h h')

lemma eq_of_ssubset {X Y: A} : X ⊆ Y → ¬(X ⊂ Y) → X = Y := 
  λ h h', by {simp only [not_and, not_not, ssubset_iff] at h', exact h' h}

lemma inter_of_ssubsets (X Y Z : A) : (X ⊂ Z) → (X ∩ Y ⊂ Z) := 
  λ h, ssubset_of_subset_ne (inter_of_subsets X Y Z h.1)
      (λ heq, by {rw ←heq at h, have := ssubset_not_supset h, from this (inter_subset_left _ _) })


lemma ssubset_trans {X Y Z : A} (hXY : X ⊂ Y) (hYZ : Y ⊂ Z) : X ⊂ Z := 
  subset_ssubset_trans hXY.1 hYZ

lemma ssubset_inter {X Y : A} : X ≠ Y → X ∩ Y ⊂ X ∨ X ∩ Y ⊂ Y:=
  λ h, by {by_contra a, push_neg at a, simp_rw [ssubset_iff, not_and', not_imp_not] at a, 
  exact h (eq.trans (a.1 (inter_subset_left X Y)).symm (a.2 (inter_subset_right X Y)) )}

-- Misc

lemma union_union_diff (X Y Z : A) : (X ∪ Z) ∪ (Y \ Z) = X ∪ Y ∪ Z :=
  by {rw [diff_def, union_distrib_left, union_right_comm, union_assoc _ Z], simp, rw [univ_eq_top, union_top, inter_top], }

lemma union_inter_diff (X Y Z : A) : (X ∪ Z) ∩ (Y \ Z) = (X ∩ Y) \ Z :=
  by {rw [diff_def, diff_def, inter_distrib_right], simp_rw [←inter_assoc, inter_right_comm Z Y Zᶜ], simp, }

lemma inter_is_lb  {X Y Z : A} : Z ⊆ X → Z ⊆ Y → Z ⊆ (X ∩ Y) := 
  λ hZX hZY, by {rw subset_def_inter at *, rw [←inter_assoc, hZX, hZY]}

lemma union_is_ub  {X Y Z : A} : X ⊆ Z → Y ⊆ Z → X ∪ Y ⊆ Z := 
  λ hXZ hYZ, by {rw subset_def_union at *, rw [union_assoc, hYZ, hXZ]}


lemma eq_of_union_eq_inter {X Y : A} : X ∪ Y = X ∩ Y → X = Y := 
begin
  intro h, apply subset_antisymm, 
  calc X ⊆ (X ∪ Y) : subset_union_left _ _ ... = X ∩ Y : h ... ⊆ Y : inter_subset_right _ _,  
  calc Y ⊆ (X ∪ Y) : subset_union_right _ _ ... = X ∩ Y : h ... ⊆ X : inter_subset_left _ _,  
end 

lemma union_of_disjoint {X Y Z : A} : X ∩ Y = ⊥ → X ∩ Z = ⊥ → X ∩ (Y ∪ Z) = ⊥ :=
  λ hY hZ, by {rw [inter_distrib_left, hY, hZ], simp }

lemma diff_subset  (X Y : A) : X \ Y ⊆ X := 
  inter_subset_left X Yᶜ

lemma diff_subset_diff {X Y : A} (Z : A) : X ⊆ Y → X \ Z ⊆ Y \ Z := 
  λ h, subset_inter_subset_left _ _ _ h

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
  λ hXY, by {intros hYX, rw diff_bot_iff_subset at hYX, from ssubset_irrefl _ (ssubset_subset_trans hXY hYX)}

lemma union_diff_of_subset  {X Y : A} : X ⊆ Y → X ∪ (Y \ X) = Y := 
  λ h, by {rw [subset_def_inter, inter_comm] at h, have := diff_union Y X, rw h at this, exact this}

@[simp] lemma diff_inter (X Y : A) : (Y \ X) ∩ X = ⊥ := 
  by rw [inter_comm, inter_diff]

@[simp] lemma union_diff (X Y : A) : X ∪ (Y \ X) = X ∪ Y := 
  by {rw [diff_def, union_distrib_left, union_compl, inter_top]}

@[simp] lemma union_diff_diff (X Y : A) : (X ∪ Y) \ (Y \ X) = X := 
  by rw [diff_def, diff_def, compl_inter,compl_compl,union_comm, ←union_distrib_right, inter_compl, bot_union]

lemma inter_distrib_diff (X Y Z : A) : X ∩ (Y \ Z) = (X ∩ Y) \ (X ∩ Z) := 
  by {rw [diff_def, diff_def, compl_inter, inter_distrib_left, inter_right_comm, inter_compl, bot_inter, bot_union, ←inter_assoc]}





--lemma union_distrib_diff (X Y Z : A) : X ∪ (Y \ Z) = X ∪ 



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

lemma size_diff_le_size (X Y : A) : size (X \ Y) ≤ size X := 
  size_monotone (diff_subset _ _) 

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
  by {split, apply size_zero_bot, intros h, rw h, exact size_bot A}

lemma size_nonempty {X : A} : X ≠ ⊥ → 0 < size X  := 
  λ hX, lt_of_le_of_ne (size_nonneg X) (λ h, hX (size_zero_bot h.symm))

lemma size_strict_monotone {X Y : A} : X ⊂ Y → size X < size Y := 
  λ hXY, by {rw [size_induced_partition Y X, inter_comm, subset_def_inter_mp hXY.1], 
                linarith [size_nonempty (ssubset_diff_nonempty hXY)]} 

lemma eq_of_eq_size_subset {X Y : A} : (X ⊆ Y) → (size X = size Y) → X = Y :=
  λ hXY, by {cases subset_ssubset_or_eq hXY, intros sXY, exfalso, replace h := size_strict_monotone h, linarith, exact λ h', h}

lemma eq_of_ge_size_subset {X Y : A} : (X ⊆ Y) → (size Y ≤ size X) → X = Y :=
  λ hXY hXY', by {apply eq_of_eq_size_subset hXY, exact le_antisymm (size_monotone hXY) hXY'}

lemma size_eq_of_supset {X Y : A} : (X ⊆ Y) → (size Y ≤ size X) → size X = size Y := 
  λ hss hs, by linarith[size_monotone hss]

lemma single_subset (X : A) : X ≠ ⊥ → (∃ Y Z, Y ∩ Z = ⊥ ∧ Y ∪ Z = X ∧ size Y = 1) := 
  begin
    intro h, cases contains_single X h with Y hY, use Y, use X \ Y, 
    exact ⟨inter_diff _ _,⟨union_diff_of_subset  hY.1,hY.2⟩⟩,
  end

lemma single_subset_nonempty {X : A}: X ≠ ⊥ → (∃ Y Z, Y ∩ Z = ⊥ ∧ Y ∪ Z = X ∧ size Y = 1) := 
  λ hX, single_subset X hX 


lemma union_ssubsets (X : A) : 1 < size X  → ∃ Y Z : A, Y ⊂ X ∧ Z ⊂ X ∧ Y ∩ Z = ⊥ ∧ Y ∪ Z = X := 
  begin
    intros hX, 
    have h := (λ h', by {rw [h', @size_bot A] at hX, linarith }: X ≠ ⊥), 
    rcases single_subset X h with ⟨Y,⟨Z,⟨hI,hU,h1⟩⟩⟩, use Y, use Z, 
    simp_rw ←hU at ⊢ hX, 
    simp only [true_and, set.subset_union_right, and_true, 
      set.bot_eq_empty, set.subset_union_left, eq_self_iff_true, ne.def,ssubset_iff], 
    refine ⟨λ hY, _, ⟨λ hZ, _, hI⟩ ⟩, 
    rw [←hY,h1] at hX, from lt_irrefl _ hX, 
    have := size_modular Y Z, 
    rw [hU, hI, @size_bot A, h1,hZ, ←hU] at this, 
    linarith,
  end

lemma ssubset_to_compl {X Y : A} : X ⊂ Y → Yᶜ ⊂ Xᶜ := 
  λ h, ssubset_of_subset_ne (subset_to_compl h.1) 
                            (λ h', by {rw (compl_inj h') at h, from ssubset_irrefl _ h}) 

lemma compl_to_ssubset {X Y : A} : Xᶜ ⊂ Yᶜ → Y ⊂ X := 
  λ h, by {have := ssubset_to_compl h, repeat {rw compl_compl at this}, exact this }

lemma ssubset_compl_right {X Y : A} : X ⊂ Yᶜ → Y ⊂ Xᶜ := 
  λ h, by {rw [←compl_compl X] at h, exact compl_to_ssubset h}

lemma ssubset_compl_left {X Y : A} : Xᶜ ⊂ Y → Yᶜ ⊂ X := 
  λ h, by {rw [←compl_compl Y] at h, exact compl_to_ssubset h}





end boolalg



end API 
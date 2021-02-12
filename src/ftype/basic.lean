
import tactic 
import .int_lemmas 

/-
  API for ftype, which is a type with a bundled fintype instance. The bundling seems like 
  it is the smoothest way to make things work; moving things before the colon caused problems. 
  The fintype instance is only extracted when needed and used with care. 

  A lot of this file is a redundant artefact of an earlier design, and now just follows from
  lemmas in the set namespace. The main exceptions are lemmas involving size, which need to be
  reproved using the slightly kooky way size is defined. The same is true for collections.lean
  and embed.lean. 
  
  Other than that, a cleanup is in order, even though things work for now. 
-/


open_locale classical 
noncomputable theory 

open set 

structure ftype  :=
  (E : Type)
  [ft : fintype E]
  

namespace ftype 


--@[simp] instance ftype_sets.nonempty : nonempty ftype := ⟨⟩ 

@[simp] instance ftype_coe : has_coe_to_sort ftype := 
  {S := Type, coe := λ A, A.E}


instance fintype_of (U : ftype) : fintype U := U.ft 

instance set_fintype_of (U : ftype) : fintype (set U) := 
  by {apply_instance}

instance subtype_fintype_of (U : ftype)(X : set U) : fintype X := 
  by {apply_instance}

--def as_finset_univ (U : ftype) := (fintype_of U).elems 

instance ftype_mem (U : ftype): has_mem U (set U) := {mem := λ x X, x ∈ X}

def as_finset (U : ftype)(X : set U) : finset U := 
  set.to_finset X 
  


variables {A : ftype}


def symm_diff  (X Y : set A) : set A := (X \ Y) ∪ (Y \ X)


/------------------------------------------------------------

We define size manually by hooking into finset.card. The following
small set of lemmas characterizes the size function 

- Size -----------------------------------------------------/

def size_nat (U : ftype)(X : set U.E) := (as_finset U X).card 

/-- the size of a set, as an integer -/
def size {U : ftype}(X : set U.E) : ℤ := (size_nat U X)

lemma size_empty_ax :
   size (∅ : set A) = 0 := 
  by simp [size, size_nat, as_finset]

lemma size_single_ax (e : A): 
  size ({e}: set A) = 1 := 
begin
  simp only  [size, size_nat], 
  have : (({e} : set A.E).to_finset = as_finset A {e}) := 
    by rw [as_finset, to_finset_inj], 
  rw [←this, to_finset_card], norm_cast, 
  rw fintype.card_eq_one_iff, 
  use e; simp, 
end

lemma size_modular_ax (X Y : set A): 
  size (X ∪ Y) + size (X ∩ Y) = size X + size Y :=
begin
  simp only [size, size_nat], norm_cast, 
  convert finset.card_union_add_card_inter _ _, 
  from (by {simp only [as_finset], tidy} : as_finset _ _ = as_finset _ _ ∪ as_finset _ _),
  from (by {simp only [as_finset], tidy} : as_finset _ _ = as_finset _ _ ∩ as_finset _ _),
end

lemma size_nonneg (X : set A) : 0 ≤ size X := 
  by {simp only [size, size_nat], norm_cast, apply zero_le}  

-------------------------------------------------------------

notation `univ` := set.univ

lemma univ_eq_top :
  set.univ = (univ : set A) := 
  set.top_eq_univ 


@[simp] lemma diff_def (X Y : set A) : X \ Y = X ∩ Yᶜ := 
  rfl 

/-- Universe is nonempty -/
def nontriv (A : ftype) := (univ : set A).nonempty

open set 

-- univ/empty with unions and intersections 


@[simp] lemma univ_inter  (X : set A) : univ ∩ X = X := 
  by simp 


-- Complements

@[simp] lemma union_compl {A: ftype} (X: set A) : 
  X ∪ Xᶜ = univ := 
  by simp  

@[simp] lemma inter_compl {A: ftype} (X: set A) : X ∩ Xᶜ = ∅ := by simp 

@[simp] lemma union_compl_rev {A: ftype} (X: set A) : Xᶜ ∪ X = univ := 
  by rw [union_comm, union_compl]

@[simp] lemma inter_compl_rev {A: ftype} (X: set A) : Xᶜ ∩ X = ∅ := 
  by rw [inter_comm, inter_compl]

-- Building things up from a minimal axiom set for fun

lemma empty_unique (X : set A) : (∀ (Y: set A), Y ∪ X = Y) → X = ∅ := 
  λ hX, by calc X = ∅ ∪ X : (empty_union X).symm ... = ∅ : hX ∅

lemma univ_unique (X : set A) : (∀ (Y: set A), Y ∩ X = Y) → X = univ := 
  λ hX, by calc X = univ ∩ X : (univ_inter X).symm ... = univ : hX univ 



-- Idempotence

@[simp] lemma union_univ  (X : set A) : X ∪ univ = univ := 
  by calc _ = univ ∩ (X ∪ univ)        : by rw univ_inter
            ... = (X ∪ Xᶜ) ∩ (X ∪ univ) : by rw ←union_compl 
            ... = univ    : by rw [←union_distrib_left, inter_univ , union_compl]

@[simp] lemma univ_union (X : set A) : univ ∪ X = univ := 
  eq.trans (union_comm univ X) (union_univ X)

@[simp] lemma empty_inter  (X : set A) : ∅ ∩ X = ∅ := 
  eq.trans (inter_comm ∅ X) (inter_empty X)


-- Absorption

@[simp] lemma absorb_union_inter (X Y : set A) : X ∪ (X ∩ Y) = X := 
  by calc X ∪ (X ∩ Y) = (X ∩ univ) ∪ (X ∩ Y) : by rw inter_univ  ... = X : by rw [←inter_distrib_left, union_comm, union_univ, inter_univ ]

@[simp] lemma absorb_inter_union (X Y : set A) : X ∩ (X ∪ Y) = X := 
  by calc X ∩ (X ∪ Y) = (X ∪ ∅) ∩ (X ∪ Y) : by rw union_empty ... = X : by rw [←union_distrib_left, inter_comm, inter_empty, union_empty]

-- Size 

lemma size_modular (X Y : set A) : size (X ∪ Y) + size (X ∩ Y) = size (X) + size Y := 
  size_modular_ax X Y

@[simp] lemma size_empty (A : ftype) : size (∅ : set A) = 0 := 
  size_empty_ax


lemma compl_size (X : set A) : size Xᶜ = size (univ : set A) - size X :=
  calc size Xᶜ = size (X ∪ Xᶜ) + size (X ∩ Xᶜ) - size X : by linarith [size_modular X Xᶜ]
  ...          = size (univ : set A)  + size (∅ : set A)  - size X : by rw [union_compl X, inter_compl X]
  ...          = size (univ : set A) - size X                  : by linarith [size_empty A]

lemma size_compl (X : set A) : size X = size (univ : set A) - size(Xᶜ) := 
  by linarith [compl_size X]

lemma contains_single (X : set A) : X.nonempty → (∃ Y, Y ⊆ X ∧ size Y = 1) :=
begin
  rintros ⟨e,he⟩,  
  from ⟨{e},⟨set.singleton_subset_iff.mpr he, size_single_ax e⟩⟩, 
end
  


-- Unions/Inters of triples 

lemma union_left_comm (X Y Z : set A) : X ∪ (Y ∪ Z) = Y ∪ (X ∪ Z) := 
  by rw [←union_assoc, ←union_assoc, union_comm X] 

lemma inter_left_comm (X Y Z : set A) : X ∩ (Y ∩ Z) = Y ∩ (X ∩ Z) := 
  by rw [←inter_assoc, ←inter_assoc, inter_comm X]

@[simp] lemma union_left_absorb (X Y : set A) : (X ∪ Y) ∪ X = X ∪ Y := 
by rw [union_right_comm, union_self]  

@[simp] lemma union_right_absorb (X Y : set A) : X ∪ (Y ∪ X) = X ∪ Y := 
by rw [union_left_comm, union_self, union_comm]  

@[simp] lemma inter_left_absorb (X Y : set A) : (X ∩ Y) ∩ X = X ∩ Y := 
by rw [inter_right_comm, inter_self]  

@[simp] lemma inter_right_absorb (X Y : set A) : X ∩ (Y ∩ X) = X ∩ Y := 
by rw [inter_left_comm, inter_self, inter_comm]

lemma inter_distrib_inter_left (X Y Z : set A) : (X ∩ Y) ∩ Z = (X ∩ Z) ∩ (Y ∩ Z) := 
  by rw [inter_assoc X Z, inter_comm Z, inter_assoc Y, inter_self, inter_assoc] 

lemma inter_distrib_inter_right (X Y Z : set A) : X ∩ (Y ∩ Z) = (X ∩ Y) ∩ (X ∩ Z) := 
  by rw [inter_comm _ (X ∩ Z), inter_assoc _ _ (X ∩ Y), inter_comm Z, ←inter_assoc X, ←inter_assoc X, ←inter_assoc X, inter_self]

lemma union_distrib_union_left (X Y Z : set A) : (X ∪ Y) ∪ Z = (X ∪ Z) ∪ (Y ∪ Z) := 
  by rw [union_assoc X Z, union_comm Z, union_assoc Y, union_self, union_assoc]

lemma union_distrib_union_right (X Y Z : set A) : X ∪ (Y ∪ Z) = (X ∪ Y) ∪ (X ∪ Z) := 
  by rw [union_comm X, union_distrib_union_left Y Z X, union_comm X, union_comm X]   

/-lemma union_inter_union (X Y Z W : set A): (X ∪ Y) ∩ (Z ∪ W) = (X ∪ Z) ∩ (Y ∪ W) := 
begin
  simp_rw [inter_distrib_left, inter_distrib_right],
end-/


-- Subsets 

lemma subset_def_union (X Y : set A) : (X ⊆ Y) ↔ (X ∪ Y = Y) := 
  by rw [←compl_subset_compl, subset_iff_inter_eq_left, ←compl_union, compl_inj_iff, union_comm Y X]

lemma subset_def_inter (X Y: set A) : (X ⊆ Y) ↔ (X ∩ Y = X) :=
  by {rw subset_def_union, exact ⟨λ h, by rw [←h, absorb_inter_union], λ h, by rw[←h, union_comm, inter_comm, absorb_union_inter]⟩} 

lemma subset_refl (X : set A) : X ⊆ X :=
  by rw [subset_def_inter, inter_self]

lemma subset_def_inter_mp  {X Y : set A} : X ⊆ Y → X ∩ Y = X := 
  (subset_def_inter X Y).mp 

lemma subset_def_inter_mpr  {X Y : set A} : X ∩ Y = X → X ⊆ Y  := 
  (subset_def_inter X Y).mpr 

lemma subset_def_union_mp  {X Y : set A} : X ⊆ Y → X ∪ Y = Y :=
  (subset_def_union X Y).mp

lemma subset_def_union_mpr {X Y : set A} : X ∪ Y = Y → X ⊆ Y := 
  (subset_def_union X Y).mpr 


lemma subset_ssubset_or_eq {X Y : set A} : (X ⊆ Y) → (X ⊂ Y) ∨ X = Y :=
  λ hXY, by {rw or_comm, apply eq_or_ssubset_of_subset hXY}

lemma subset_iff_ssubset_or_eq {X Y : set A} : (X ⊆ Y) ↔ (X ⊂ Y) ∨ X = Y :=
  ⟨λ h, subset_ssubset_or_eq h, λ h, by {cases h, from h.1, rw h}⟩


@[simp] lemma ssubset_iff {X Y : set A} : X ⊂ Y ↔ (X ⊆ Y) ∧ (X ≠ Y) :=
  ssubset_iff_subset_ne



lemma ssubset_of_subset_ne {X Y : set A} : X ⊆ Y → X ≠ Y → X ⊂ Y := 
  @lt_of_le_of_ne _ _ X Y 

lemma ne_of_ssubset {X Y : set A} : X ⊂ Y → X ≠ Y := 
  ne_of_irrefl

lemma ssubset_irrefl (X : set A) : ¬(X ⊂ X) :=
  λ h, by {rw ssubset_iff at h, from h.2 rfl}


lemma ssubset_size {X Y : set A} : (X ⊆ Y) → (size X < size Y) → (X ⊂ Y) := 
  λ h h', by {rw ssubset_iff, from ⟨h, λ h'', by {rw h'' at h', linarith}⟩}


  --λ hXY hS, ⟨hXY, by {intros h, rw h at hS, linarith}⟩

lemma subset_antisymm  {X Y : set A} : X ⊆ Y → Y ⊆ X → X = Y := 
  λ hXY hYX, by {rw subset_def_inter at *, rw inter_comm at hXY, exact (rfl.congr hYX).mp (eq.symm hXY)}

lemma univ_subset  {X : set A} (hX : univ ⊆ X) : X = univ := 
  subset_antisymm (subset_univ X) hX
 
instance subset_subtype_nonempty {X : set A} : nonempty {Y : set A // Y ⊆ X} := 
  by {apply nonempty_subtype.mpr, from ⟨_,empty_subset _⟩,  }

instance subtype_coe {X : set A} : has_coe {Y : set A // Y ⊆ X} (set A) := coe_subtype

lemma subset_empty  {X : set A} : X ⊆ ∅ → X = ∅ := 
  λ hX, subset_antisymm hX (empty_subset X)  

lemma ssubset_empty (X : set A) : ¬ X ⊂ ∅ := 
  λ h, by {rw ssubset_iff at h, from h.2 (subset_empty h.1)}

lemma disjoint_compl_subset {X Y : set A} : X ∩ Y = ∅ → X ⊆ Yᶜ := 
  λ h, by rw [subset_def_inter, ← empty_union (X ∩ Yᶜ), ←h, ←inter_distrib_left, union_compl, inter_univ]

lemma subset_compl_disjoint {X Y : set A} : X ⊆ Yᶜ → X ∩ Y = ∅ := 
  λ h, by {rw subset_def_inter at h, rw [←h, inter_assoc], simp}


lemma disjoint_iff_subset_compl {X Y : set A} : X ∩ Y = ∅ ↔ X ⊆ Yᶜ := 
  ⟨λ h, disjoint_compl_subset h, λ h, subset_compl_disjoint h⟩   

lemma subset_iff_diff_empty (X Y : set A) : X ⊆ Y ↔ X \ Y = ∅ :=
  by {rw [←compl_compl Y, ←disjoint_iff_subset_compl], simp}

lemma subset_iff_disjoint_compl {X Y : set A} : X ⊆ Y ↔ X ∩ Yᶜ = ∅ :=
by {rw [subset_iff_diff_empty], simp,  }

lemma disjoint_of_subset_left' {X Y Z : set A }: X ⊆ Y → Y ∩ Z = ∅ → X ∩ Z = ∅ :=
λ h h', by {rw ←disjoint_iff_inter_eq_empty at *, exact disjoint_of_subset_left h h', }

lemma disjoint_of_subset_right' {X Y Z : set A }: X ⊆ Y → Z ∩ Y = ∅ → Z ∩ X = ∅ :=
λ h h', by {rw ←disjoint_iff_inter_eq_empty at *, exact disjoint_of_subset_right h h', }

lemma disjoint_of_subsets {X X' Y Y' : set A }: X ⊆ X' → Y ⊆ Y' → X' ∩ Y' = ∅ → X ∩ Y = ∅ :=
λ h h' h'', by {rw ←disjoint_iff_inter_eq_empty at *, exact disjoint_of_subset h h' h'', }

lemma cover_compl_subset {X Y : set A} :  X ∪ Y = univ → Xᶜ ⊆ Y  := 
  λ h, by rw [subset_def_union, ←univ_inter (Xᶜ ∪ Y), ←h, ←union_distrib_right, inter_compl, empty_union]

lemma compl_unique {X Y : set A} : X ∪ Y = univ → X ∩ Y = ∅ → Y = Xᶜ := 
  λ hU hI, by {apply subset_antisymm, exact disjoint_compl_subset (eq.trans (inter_comm Y X) hI), exact cover_compl_subset hU}

lemma compl_inj {X Y : set A} : Xᶜ = Yᶜ → X = Y := 
  λ h, by rw [←compl_compl X, ←compl_compl Y, h]

lemma compl_inj_iff {X Y : set A} : Xᶜ = Yᶜ ↔ X = Y := 
  ⟨λ h, compl_inj h, λ h, by rw h⟩ 

@[simp] lemma empty_iff_compl_univ {X : set A} : Xᶜ = univ ↔ X = ∅ := 
  by rw [←compl_empty, compl_inj_iff]

lemma empty_of_compl_univ {X : set A} : Xᶜ = univ → X = ∅  := 
  set.compl_univ_iff.mp

@[simp] lemma univ_iff_compl_empty {X : set A} : Xᶜ = ∅ ↔ X = univ := 
  by rw [←compl_univ, compl_inj_iff]

lemma univ_of_compl_empty {X : set A} : Xᶜ = ∅ → X = univ  := 
  by {rw univ_iff_compl_empty, exact congr_arg _}

@[simp] lemma inter_compl_left {X : set A} : Xᶜ ∩ X = ∅ := 
  by rw [inter_comm, inter_compl]

@[simp] lemma union_compl_left {X : set A} : Xᶜ ∪ X = univ := 
  by rw [union_comm, union_compl]

@[simp] lemma union_compl_union  (X Y : set A) : X ∪ (Xᶜ ∪ Y) = univ :=  
  by rw [←univ_inter(X ∪ (Xᶜ ∪ Y)), ←union_compl, ←union_distrib_left, absorb_inter_union] 

@[simp] lemma inter_compl_inter (X Y : set A) : X ∩ (Xᶜ ∩ Y) = ∅ := 
  by rw [←empty_union(X ∩ (Xᶜ ∩ Y)), ←inter_compl, ←inter_distrib_left, absorb_union_inter]

@[simp] lemma inter_compl_union (X Y : set A) : X ∩ (Xᶜ ∪ Y) = X ∩ Y :=
  by rw [inter_distrib_left, inter_compl, empty_union]

@[simp] lemma union_compl_inter (X Y : set A) : X ∪ (Xᶜ ∩ Y) = X ∪ Y :=
  by rw [union_distrib_left, union_compl, univ_inter]

@[simp] lemma union_inter_compl_inter (X Y : set A) : (X ∪ Y) ∪ (Xᶜ ∩ Yᶜ)  = univ := 
  by rw [union_distrib_left, union_comm _ Xᶜ, union_comm X Y, union_comm _ Yᶜ,
      ←(compl_compl Y),  compl_compl Yᶜ, union_compl_union Yᶜ, union_comm _ X, 
      ←(compl_compl X),    compl_compl Xᶜ, union_compl_union Xᶜ, inter_self]

@[simp] lemma inter_union_compl_union (X Y : set A) : (X ∩ Y) ∩ (Xᶜ ∪ Yᶜ)  = ∅ := 
  by rw [inter_distrib_left, inter_comm _ Xᶜ, inter_comm X Y, inter_comm _ Yᶜ, 
        ←(compl_compl Y), compl_compl Yᶜ, inter_compl_inter Yᶜ, inter_comm _ X, 
        ←(compl_compl X), compl_compl Xᶜ, inter_compl_inter Xᶜ, union_self]
  

@[simp] lemma inter_union_compl_inter (X Y : set A) : (X ∪ Y) ∩ (Xᶜ ∩ Yᶜ) = ∅ := 
  by rw [inter_distrib_right X Y, inter_compl_inter, inter_comm Xᶜ, inter_compl_inter, union_self]
  
@[simp] lemma union_inter_compl_union  (X Y : set A) : (X ∩ Y) ∪ (Xᶜ ∪ Yᶜ) = univ := 
  by rw [union_distrib_right X Y, union_compl_union, union_comm Xᶜ, union_compl_union, inter_self]

lemma compl_compl_inter_left (X Y : set A) : (Xᶜ ∩ Y)ᶜ = X ∪ Yᶜ := 
  by {nth_rewrite 0 ←(compl_compl Y), rw [compl_inter, compl_compl, compl_compl] }

lemma compl_compl_inter_right (X Y : set A) : (X ∩ Yᶜ)ᶜ = Xᶜ ∪ Y := 
  by {nth_rewrite 0 ←(compl_compl X), rw [compl_inter, compl_compl, compl_compl] }

lemma compl_compl_union_left (X Y : set A) : (Xᶜ ∪ Y)ᶜ = X ∩ Yᶜ := 
  by {nth_rewrite 0 ←(compl_compl Y), rw [compl_union, compl_compl, compl_compl] }

lemma compl_compl_union_right (X Y : set A) : (X ∪ Yᶜ)ᶜ = Xᶜ ∩ Y := 
  by {nth_rewrite 0 ←(compl_compl X), rw [compl_union, compl_compl, compl_compl] }


lemma compl_partition (X Y : set A) : (X ∩ Y) ∪ (Xᶜ ∩ Y) = Y := 


  by rw [←inter_distrib_right, union_compl, univ_inter]

lemma compl_partition_subset  {X Y : set A} (hXY : X ⊆ Y) : X ∪ (Xᶜ ∩ Y) = Y := 
  by {nth_rewrite 0 ←(subset_def_inter_mp hXY), exact compl_partition X Y}

lemma compl_pair {X Y : set A} : (Xᶜ = Y) → (X = Yᶜ) := 
  λ h, by rw [←h, compl_compl]

lemma compl_pair_iff {X Y : set A} : (Xᶜ = Y) ↔ (X = Yᶜ) := 
  ⟨λ h, compl_pair h, λ h, by {rw eq_comm at h, from (compl_pair h).symm}⟩

lemma compl_diff (X Y : set A) : (X \ Y)ᶜ = Xᶜ ∪ Y := 
  by rw [diff_def, compl_inter, compl_compl]

@[simp] lemma union_union_compl (X Y : set A) : (X ∪ Y) ∪ Yᶜ = univ := 
  by rw [union_assoc, union_compl, union_univ]

@[simp] lemma inter_inter_compl (X Y : set A) : (X ∩ Y) ∩ Yᶜ = ∅ := 
  by rw [inter_assoc, inter_compl, inter_empty]

@[simp] lemma union_union_compl_right (X Y : set A) : X ∪ (Y ∪ Xᶜ) = univ := 
by rw [←union_assoc, union_comm X, union_union_compl]

@[simp] lemma inter_inter_compl_right (X Y : set A) : X ∩ (Y ∩ Xᶜ) = ∅ := 
by rw [←inter_assoc, inter_comm X, inter_inter_compl]

lemma union_inter_compl_self (X Y : set A) : X ∪ (Y ∩ Yᶜ) = X :=
  by {simp}

lemma inter_union_compl_self (X Y : set A) : X ∩ (Y ∪ Yᶜ) = X :=
  by rw [union_compl, inter_univ]

lemma subset_to_compl {X Y : set A} : X ⊆ Y → Yᶜ ⊆ Xᶜ := 
  λ hXY, by {rw subset_def_inter at hXY, rw [←hXY, compl_inter, union_comm], apply subset_union_left} 

lemma compl_to_subset {X Y : set A}: Xᶜ ⊆ Yᶜ → Y ⊆ X := 
  λ hXY, by {have := subset_to_compl hXY, repeat {rw compl_compl at this}, exact this }

lemma subset_iff_subset_compl {X Y : set A}: X ⊆ Y ↔ Yᶜ ⊆ Xᶜ := 
by {split, apply subset_to_compl, apply compl_to_subset,}

lemma subset_compl_right {X Y : set A}: X ⊆ Yᶜ → Y ⊆ Xᶜ := 
  λ hXY, by {rw [←compl_compl X] at hXY, exact compl_to_subset hXY}

lemma subset_compl_left {X Y : set A} : Xᶜ ⊆ Y → Yᶜ ⊆ X := 
  λ hXY, by {rw [←compl_compl Y] at hXY, exact compl_to_subset hXY}



lemma subset_of_compl_iff_disjoint {X Y: set A} : X ⊆ Yᶜ ↔ X ∩ Y = ∅ := 
  begin 
        rw subset_def_inter,  refine ⟨λ h, _, λ h, _⟩, 
        rw [←h, inter_assoc, inter_comm _ Y, inter_compl, inter_empty], 
        rw [←union_empty (X ∩ Yᶜ), ←h, ←inter_distrib_left, union_comm, union_compl, inter_univ] 
  end

lemma subset_own_compl {X : set A} : X ⊆ Xᶜ → X = ∅ := 
  λ h, by {rw [subset_def_union,union_compl, ←compl_empty, compl_inj_iff] at h, rw ←h }
----

-- more subsets 

/--/ by {refine ⟨λ h, _, λ h, _⟩, rw [subset_def_inter, ←union_empty (X ∩ Yᶜ), ←h, ←inter_distrib_left], simp, 
    rw [subset_def_inter] at h, rw [←h, inter_assoc], sorry  } -/

@[trans] lemma subset_trans {X Y Z : set A} : X ⊆ Y → Y ⊆ Z →  X ⊆ Z :=
  λ hXY hYZ, by {rw subset_def_inter at *, rw [←hXY, inter_assoc, hYZ]}

--instance i_subset_trans : is_trans A (λ X Y : set A ,X ⊆ Y) := { trans := λ X Y Z, @subset_trans _ X Y Z }

lemma inter_subset_union (X Y : set A) : X ∩ Y ⊆ X ∪ Y := 
  subset_trans (inter_subset_left X Y) (subset_union_left X Y)

lemma subset_of_inter_mp {X Y Z : set A} : X ⊆ Y ∩ Z → X ⊆ Y ∧ X ⊆ Z := 
  λ h, ⟨subset_trans h (inter_subset_left _ _), subset_trans h (inter_subset_right _ _)⟩  

lemma union_of_subsets {X Y Z : set A} : (X ⊆ Z) → (Y ⊆ Z) → (X ∪ Y ⊆ Z) := 
  λ hXZ hYZ, by {rw subset_def_inter at *, rw [inter_distrib_right, hXZ, hYZ]}

lemma subset_of_inter_mpr  {X Y Z : set A} : (X ⊆ Y) → (X ⊆ Z) → (X ⊆ Y ∩ Z) := 
  λ hXY hXZ, by {rw subset_def_inter at *, rw [←inter_assoc, hXY, hXZ]}

lemma subset_of_inter_iff {X Y Z : set A} : X ⊆ (Y ∩ Z) ↔ (X ⊆ Y ∧ X ⊆ Z) := 
  ⟨λ h, subset_of_inter_mp h, λ h, subset_of_inter_mpr  h.1 h.2⟩

lemma inter_of_subsets (X Y Z : set A) : (X ⊆ Z) → (X ∩ Y ⊆ Z) := 
  λ h, subset_trans (inter_subset_left X Y) h

lemma union_of_supsets (X Y Z : set A) : (X ⊆ Y) → (X ⊆ Y ∪ Z) := 
  λ h, subset_trans h (subset_union_left Y Z)

lemma subset_inter_subset_left (X Y Z : set A) : (X ⊆ Y) → (X ∩ Z) ⊆ (Y ∩ Z) := 
  λ hXY, by {rw subset_def_inter at *, rw [←inter_distrib_inter_left, hXY]}

lemma subset_inter_subset_right (X Y Z : set A) : (X ⊆ Y) → (Z ∩ X) ⊆ (Z ∩ Y) := 
  by {rw [inter_comm _ X, inter_comm _ Y], apply subset_inter_subset_left }

lemma subset_union_subset_left (X Y Z : set A) : (X ⊆ Y) → (X ∪ Z) ⊆ (Y ∪ Z) := 
  λ hXY, by {rw subset_def_union at *, rw [←union_distrib_union_left, hXY]}

lemma subset_union_subset_right (X Y Z : set A) : (X ⊆ Y) → (Z ∪ X) ⊆ (Z ∪ Y) := 
  by {rw [union_comm _ X, union_comm _ Y], apply subset_union_subset_left }

lemma union_subset_pairs {X₁ X₂ Y₁ Y₂ : set A} : X₁ ⊆ Y₁ → X₂ ⊆ Y₂ → X₁ ∪ X₂ ⊆ Y₁ ∪ Y₂ :=
  λ h₁ h₂, subset_trans (subset_union_subset_left X₁ Y₁ X₂ h₁) (subset_union_subset_right X₂ Y₂ Y₁ h₂) 

lemma inter_subset_pairs {X₁ X₂ Y₁ Y₂ : set A} : X₁ ⊆ Y₁ → X₂ ⊆ Y₂ → X₁ ∩ X₂ ⊆ Y₁ ∩ Y₂ :=
  λ h₁ h₂, inter_subset_inter h₁ h₂

lemma subset_of_set_and_compl {X Y: set A} : X ⊆ Y → X ⊆ Yᶜ → X = ∅ :=
  λ h1 h2, by {have := subset_of_inter_mpr h1 h2, rw inter_compl at this, exact subset_empty this}

@[trans] lemma subset_ssubset_trans {X Y Z : set A} : X ⊆ Y → Y ⊂ Z → X ⊂ Z := 
  @lt_of_le_of_lt _ _ X Y Z

@[trans] lemma ssubset_subset_trans {X Y Z : set A} : X ⊂ Y → Y ⊆ Z → X ⊂ Z := 
  @lt_of_lt_of_le _ _ X Y Z 

lemma ssubset_not_supset {X Y : set A} : X ⊂ Y → ¬(Y ⊆ X) :=
  λ h h', ssubset_irrefl _ (ssubset_subset_trans h h') 

lemma subset_not_ssupset {X Y : set A} : X ⊆ Y → ¬(Y ⊂ X) := 
  λ h h', ssubset_irrefl _ (subset_ssubset_trans h h')

lemma eq_of_ssubset {X Y: set A} : X ⊆ Y → ¬(X ⊂ Y) → X = Y := 
  λ h h', by {simp only [not_and, not_not, ssubset_iff] at h', exact h' h}

lemma inter_of_ssubsets (X Y Z : set A) : (X ⊂ Z) → (X ∩ Y ⊂ Z) := 
  λ h, ssubset_of_subset_ne (inter_of_subsets X Y Z h.1)
      (λ heq, by {rw ←heq at h, have := ssubset_not_supset h, from this (inter_subset_left _ _) })


@[trans] lemma ssubset_trans {X Y Z : set A}: X ⊂ Y → Y ⊂ Z → X ⊂ Z := 
  λ hXY hYZ, subset_ssubset_trans hXY.1 hYZ

lemma ssubset_inter {X Y : set A} : X ≠ Y → X ∩ Y ⊂ X ∨ X ∩ Y ⊂ Y:=
  λ h, by {by_contra a, push_neg at a, simp_rw [ssubset_iff, not_and', not_imp_not] at a, 
  exact h (eq.trans (a.1 (inter_subset_left X Y)).symm (a.2 (inter_subset_right X Y)) )}

-- Misc


lemma union_union_diff (X Y Z : set A) : (X ∪ Z) ∪ (Y \ Z) = X ∪ Y ∪ Z :=
  by {rw [diff_def, union_distrib_left, union_right_comm, union_assoc _ Z], simp,}

lemma union_diff_absorb (X Y : set A) : X ∪ (Y \ X) = X ∪ Y :=
by {nth_rewrite 0 ←union_self X, rw union_union_diff, simp}

@[simp] lemma union_inter_compl (X Y : set A) : X ∪ (Y ∩ Xᶜ) = X ∪ Y := 
by rw [←diff_def, union_diff_absorb]

@[simp] lemma union_union_inter_compl (X Y Z : set A) : (X ∪ Z) ∪ (Y ∩ Zᶜ) = X ∪ Y ∪ Z :=
  by rw [←diff_def, union_union_diff] 

lemma union_inter_diff (X Y Z : set A) : (X ∪ Z) ∩ (Y \ Z) = (X ∩ Y) \ Z :=
  by {rw [diff_def, diff_def, inter_distrib_right], simp_rw [←inter_assoc, inter_right_comm Z Y Zᶜ], simp, }

lemma inter_is_lb  {X Y Z : set A} : Z ⊆ X → Z ⊆ Y → Z ⊆ (X ∩ Y) := 
  λ hZX hZY, by {rw subset_def_inter at *, rw [←inter_assoc, hZX, hZY]}

lemma union_is_ub  {X Y Z : set A} : X ⊆ Z → Y ⊆ Z → X ∪ Y ⊆ Z := 
  λ hXZ hYZ, by {rw subset_def_union at *, rw [union_assoc, hYZ, hXZ]}


lemma eq_of_union_eq_inter {X Y : set A} : X ∪ Y = X ∩ Y → X = Y := 
begin
  intro h, apply subset_antisymm, 
  calc X ⊆ (X ∪ Y) : subset_union_left _ _ ... = X ∩ Y : h ... ⊆ Y : inter_subset_right _ _,  
  calc Y ⊆ (X ∪ Y) : subset_union_right _ _ ... = X ∩ Y : h ... ⊆ X : inter_subset_left _ _,  
end 

lemma union_of_disjoint {X Y Z : set A} : X ∩ Y = ∅ → X ∩ Z = ∅ → X ∩ (Y ∪ Z) = ∅ :=
  λ hY hZ, by {rw [inter_distrib_left, hY, hZ], simp }

lemma diff_subset_diff {X Y : set A} (Z : set A) : X ⊆ Y → X \ Z ⊆ Y \ Z := 
  λ h, subset_inter_subset_left _ _ _ h

@[simp] lemma diff_union (X Y : set A): (X ∩ Y) ∪ (X \ Y) = X  := 
  by rw [diff_def, ←inter_distrib_left, union_compl, inter_univ]

@[simp] lemma inter_diff (X Y : set A): X ∩ (Y \ X)  = ∅ := 
  by rw [diff_def, ←inter_assoc, inter_right_comm, inter_compl, empty_inter]

@[simp] lemma partition_inter (X Y : set A) : (X ∩ Y) ∩ (X \ Y) = ∅ := 
  by rw [inter_assoc, inter_diff, inter_empty]

@[simp] lemma diffs_disj (X Y : set A) : (X \ Y) ∩ (Y \ X) = ∅ := 
  by {simp only [diff_def], rw [inter_assoc, ←inter_assoc Yᶜ], simp}

lemma diff_empty_subset (X Y : set A) : X \ Y = ∅ → X ⊆ Y := 
  λ hXY, by {rw [←diff_union X Y, hXY, union_empty], apply inter_subset_right}

lemma subset_diff_empty (X Y : set A) : X ⊆ Y → X \ Y = ∅ := 
  λ hXY, by {rw diff_def, rw subset_def_inter at hXY, rw [←hXY, inter_assoc, inter_compl, inter_empty]}

lemma diff_empty_iff_subset (X Y : set A) : X \ Y = ∅ ↔ X ⊆ Y := 
  by {split, apply diff_empty_subset, apply subset_diff_empty}

lemma subset_diff_disjoint (X Y Z: set A) : X ⊆ Y → X ∩ Z = ∅ → X ⊆ Y \ Z := 
  λ hXY hXZ, by {rw [disjoint_iff_subset_compl, subset_def_inter] at hXZ, 
                rw [diff_def, subset_def_inter, inter_comm Y, ←inter_assoc, hXZ, subset_def_inter_mp hXY], }


lemma ssubset_diff_nonempty {X Y : set A} : X ⊂ Y → (Y \ X).nonempty :=
  λ hXY, set.nonempty_of_ssubset hXY

lemma union_diff_of_subset  {X Y : set A} : X ⊆ Y → X ∪ (Y \ X) = Y := 
  λ h, by {rw [subset_def_inter, inter_comm] at h, have := diff_union Y X, rw h at this, exact this}

@[simp] lemma diff_inter (X Y : set A) : (Y \ X) ∩ X = ∅ := 
  by rw [inter_comm, inter_diff]

@[simp] lemma union_diff (X Y : set A) : X ∪ (Y \ X) = X ∪ Y := 
  by {rw [diff_def, union_distrib_left, union_compl, inter_univ]}

@[simp] lemma union_diff_diff (X Y : set A) : (X ∪ Y) \ (Y \ X) = X := 
  by rw [diff_def, diff_def, compl_inter,compl_compl,union_comm, ←union_distrib_right, inter_compl, empty_union]

lemma inter_distrib_diff (X Y Z : set A) : X ∩ (Y \ Z) = (X ∩ Y) \ (X ∩ Z) := 
  by {rw [diff_def, diff_def, compl_inter, inter_distrib_left, inter_right_comm, inter_compl, empty_inter, empty_union, ←inter_assoc]}





--lemma union_distrib_diff (X Y Z : set A) : X ∪ (Y \ Z) = X ∪ 



@[simp] lemma diff_empty (X : set A) : X \ ∅ = X := 
  by {rw [diff_def, compl_empty, inter_univ]} 

@[simp] lemma empty_diff (X : set A) : ∅ \ X = ∅ := 
  by rw [diff_def, empty_inter]

@[simp] lemma univ_diff (X : set A) : univ \ X = Xᶜ := 
  by rw [diff_def, univ_inter]

@[simp] lemma diff_univ (X : set A) : X \ univ = ∅ := 
  by rw [diff_def, compl_univ, inter_empty]

@[simp] lemma diff_self (X : set A) : X \ X = ∅ := 
  inter_compl X 

@[simp] lemma symm_diff_self (X : set A) : symm_diff X X = ∅ :=
  by {unfold symm_diff, rw [diff_self, empty_union]}

lemma symm_diff_alt (X Y : set A) : symm_diff X Y = (X ∪ Y) \ (X ∩ Y) := 
begin
   unfold symm_diff, 
   repeat {rw [diff_def]}, 
   rw [compl_inter, inter_distrib_right, inter_distrib_left, inter_distrib_left],
   simp,   
end  

lemma size_monotone {X Y: set A} (hXY : X ⊆ Y) : size X ≤ size Y := 
  by {have := size_modular X (Y \ X), rw union_diff_of_subset  hXY at this      , 
        rw inter_diff at this, linarith [size_nonneg(Y \ X), size_empty A]}

lemma size_subadditive {X Y : set A} : size (X ∪ Y) ≤ size X + size Y :=
  by linarith [size_modular X Y, size_nonneg (X ∩ Y)] 

lemma compl_inter_size (X Y : set A) : size (X ∩ Y) + size (Xᶜ ∩ Y) = size Y := 
  by rw [←size_modular, ←inter_distrib_right, union_compl, univ_inter, ←inter_distrib_inter_left, inter_compl, empty_inter, size_empty]; ring

lemma compl_inter_size_subset {X Y : set A} : X ⊆ Y → size (Xᶜ ∩ Y) = size Y - size X := 
  λ hXY, by {have := compl_inter_size X Y, rw subset_def_inter_mp hXY at this, linarith} 

lemma diff_size {X Y : set A} : X ⊆ Y → size (Y \ X) = size Y - size X :=  
  λ hXY, by rw [diff_def, inter_comm, compl_inter_size_subset hXY]

lemma size_diff_le_size (X Y : set A) : size (X \ Y) ≤ size X := 
  size_monotone (diff_subset _ _) 

lemma size_disjoint_sum {X Y : set A}: X ∩ Y = ∅ → size (X ∪ Y) = size X + size Y := 
  λ hXY, by {have := size_modular X Y, rw [hXY, size_empty] at this, linarith}

lemma size_modular_diff (X Y : set A) : size (X ∪ Y) = size (X \ Y) + size (Y \ X) + size (X ∩ Y) :=
  by {rw [←size_disjoint_sum (diffs_disj X Y)], have := (symm_diff_alt X Y), 
        unfold symm_diff at this,rw this, linarith [diff_size (inter_subset_union X Y)]  }


lemma size_induced_partition (X Y : set A) : size X = size (X ∩ Y) + size (X \ Y) := 
  by {nth_rewrite 0 ←diff_union X Y, refine size_disjoint_sum _, apply partition_inter}

lemma size_induced_partition_inter (X Y : set A) : size X = size (X ∩ Y) + size (X ∩ Yᶜ) := 
  by {rw ←diff_def, apply size_induced_partition,}

lemma size_compl_sum (X : set A) : size X + size Xᶜ = size (univ : set A) := 
  by {have := size_disjoint_sum (inter_compl X), rw (union_compl X) at this, linarith}

lemma size_mono_inter_left (X Y : set A) : size (X ∩ Y) ≤ size X := 
size_monotone (inter_subset_left _ _)

lemma size_mono_inter_right (X Y : set A) : size (X ∩ Y) ≤ size Y := 
size_monotone (inter_subset_right _ _)

lemma size_mono_union_left (X Y : set A) : size X ≤ size (X ∪ Y)  := 
size_monotone (subset_union_left _ _)

lemma size_mono_union_right (X Y : set A) : size Y ≤ size (X ∪ Y) := 
size_monotone (subset_union_right _ _)


lemma size_zero_empty {X : set A} : (size X = 0) → X = ∅ := 
begin
  contrapose!, intros hne hs, 
  rw [push_neg.not_eq, set.ne_empty_iff_nonempty] at hne, 
  cases contains_single X hne with Y hY,
  linarith [size_monotone hY.1], 
end  

lemma size_zero_iff_empty {X : set A} : (size X = 0) ↔ (X = ∅) := 
  by {split, apply size_zero_empty, intros h, rw h, exact size_empty A}

lemma size_nonempty {X : set A} : X.nonempty → 0 < size X  := 
begin
  rw ←set.ne_empty_iff_nonempty, 
  from λ hX, lt_of_le_of_ne (size_nonneg X) (λ h, hX (size_zero_empty h.symm)), 
end

lemma size_pos_iff_nonempty {X : set A} : X.nonempty ↔ 0 < size X := 
begin
  refine ⟨λ h, size_nonempty h, λ h, _⟩,
  rw ←set.ne_empty_iff_nonempty, 
  from λ h', by {rw [h', size_empty] at h, from lt_irrefl 0 h} 
end

lemma one_le_size_iff_nonempty {X : set A} : X.nonempty ↔ 1 ≤ size X := 
  size_pos_iff_nonempty


lemma nontriv_size (hA: nontriv A): 1 ≤ size (univ : set A) := 
  one_le_size_iff_nonempty.mp hA 

lemma size_img_inj {B : ftype}(f : A ↪ B)(X : set A): 
  size (f '' X) = size X := 
begin
  simp only [ftype.size_nat.equations._eqn_1, ftype.size.equations._eqn_1, int.coe_nat_inj'],
  convert finset.card_map f,
  unfold as_finset,
  ext, simp, 
end

lemma size_img_equiv {B : ftype}(f : A ≃ B)(X : set A):
  size (f '' X) = size X :=
size_img_inj (f.to_embedding) X 


lemma size_preimg_equiv {B : ftype}(f : A ≃ B)(X : set B):
  size (f ⁻¹' X) = size X :=
begin
  unfold_coes, 
  rw ←set.image_eq_preimage_of_inverse f.right_inv f.left_inv, 
  convert size_img_inj (f.symm.to_embedding) X, 
end

lemma size_subtype_img {E : set A}(X : set (⟨E⟩ : ftype)): 
  size (subtype.val '' X) = size X :=
begin
  let f : (⟨E⟩ : ftype) ↪ A := ⟨subtype.val, λ x y hxy, by {cases x, cases y, simp only [subtype.mk_eq_mk], exact hxy}⟩, 
  apply size_img_inj f, 
end





lemma size_strict_monotone {X Y : set A} : X ⊂ Y → size X < size Y := 
λ hXY, by {rw [size_induced_partition Y X, inter_comm, subset_def_inter_mp hXY.1], 
              linarith [size_nonempty (ssubset_diff_nonempty hXY)]} 

lemma eq_of_eq_size_subset {X Y : set A} : (X ⊆ Y) → (size X = size Y) → X = Y :=
  λ hXY, by {cases subset_ssubset_or_eq hXY, intros sXY, exfalso, replace h := size_strict_monotone h, linarith, exact λ h', h}

lemma eq_of_eq_size_subset_iff {X Y : set A} : (X ⊆ Y) → ((size X = size Y) ↔ X = Y) :=
  λ hXY, ⟨λ h, eq_of_eq_size_subset hXY h, λ h, by {rw h}⟩

lemma eq_of_ge_size_subset {X Y : set A} : (X ⊆ Y) → (size Y ≤ size X) → X = Y :=
  λ hXY hXY', by {apply eq_of_eq_size_subset hXY, exact le_antisymm (size_monotone hXY) hXY'}

lemma size_eq_of_supset {X Y : set A} : (X ⊆ Y) → (size Y ≤ size X) → size X = size Y := 
  λ hss hs, by linarith[size_monotone hss]

lemma single_subset (X : set A) : X.nonempty → (∃ Y Z, Y ∩ Z = ∅ ∧ Y ∪ Z = X ∧ size Y = 1) := 
  begin
    intro h, cases contains_single X h with Y hY, use Y, use X \ Y, 
    exact ⟨inter_diff _ _,⟨union_diff_of_subset  hY.1,hY.2⟩⟩,
  end

lemma empty_ssubset_nonempty {X : set A} : 
  X.nonempty → ∅ ⊂ X := 
  λ h, by {rw ←set.ne_empty_iff_nonempty at h, from ssubset_of_subset_ne (empty_subset X) (ne.symm h)}

lemma nonempty_iff_empty_subset {X : set A}: 
  X.nonempty ↔ ∅ ⊂ X := 
  ⟨λ h, empty_ssubset_nonempty h, λ h, by {rw ←set.ne_empty_iff_nonempty, from (ne_of_ssubset h).symm, }⟩

lemma single_subset_nonempty {X : set A}: X.nonempty → (∃ Y Z, Y ∩ Z = ∅ ∧ Y ∪ Z = X ∧ size Y = 1) := 
  λ hX, single_subset X hX 


lemma union_ssubsets (X : set A) : 1 < size X  → ∃ Y Z : set A, Y ⊂ X ∧ Z ⊂ X ∧ Y ∩ Z = ∅ ∧ Y ∪ Z = X := 
begin
  intros hX, 
  have h : X.nonempty := by {rw size_pos_iff_nonempty, linarith}, 
  rcases single_subset X h with ⟨Y,⟨Z,⟨hI,hU,h1⟩⟩⟩, use Y, use Z, 
  simp_rw ←hU at ⊢ hX, 
  refine ⟨ssubset_of_subset_ne _ (λ h, _), ssubset_of_subset_ne _ (λ h, _), hI, rfl⟩, 
  apply subset_union_left, 
  rw ←h at hX, linarith, 
  apply subset_union_right,
  have := size_modular Y Z, 
  rw [hU, hI, size_empty, h1, ←hU, ←h] at this,
  linarith, 
end

lemma ssubset_to_compl {X Y : set A} : X ⊂ Y → Yᶜ ⊂ Xᶜ := 
  λ h, ssubset_of_subset_ne (subset_to_compl h.1) 
                            (λ h', by {rw (compl_inj h') at h, from ssubset_irrefl _ h}) 

lemma compl_to_ssubset {X Y : set A} : Xᶜ ⊂ Yᶜ → Y ⊂ X := 
  λ h, by {have := ssubset_to_compl h, repeat {rw compl_compl at this}, exact this }

lemma ssubset_compl_right {X Y : set A} : X ⊂ Yᶜ → Y ⊂ Xᶜ := 
  λ h, by {rw [←compl_compl X] at h, exact compl_to_ssubset h}

lemma ssubset_compl_left {X Y : set A} : Xᶜ ⊂ Y → Yᶜ ⊂ X := 
  λ h, by {rw [←compl_compl Y] at h, exact compl_to_ssubset h}



end ftype


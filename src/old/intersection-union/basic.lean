
/- This file contains the basic definitions needed to talk about matroid union and matroid
intersection.-/

import matroid.submatroid.projection prelim.minmax

open_locale classical
noncomputable theory
open matroid set

variables {α : Type*} [fintype α]

-- setting up the various types we are minimizing/maximizing over, and associated nonempty/fintype
-- instances
section prelim

/-- property of a pair of independent sets in M₁, M₂ respectively  -/
def is_indep_pair (M₁ M₂ : matroid α) := λ (p : set α × set α), M₁.is_indep p.1 ∧ M₂.is_indep p.2

/-- property of being bases of both M₁ M₂  -/
def is_basis_pair (M₁ M₂ : matroid α) := λ (p : set α × set α), M₁.is_basis p.1 ∧ M₂.is_basis p.2

/-- type of disjoint pairs of sets in α -/
def is_disjoint (pair : (set α × set α)) := pair.1 ∩ pair.2 = ∅ 

/-- type of pairs of independent sets of M₁,M₂ respectively -/
def indep_pair (M₁ M₂ : matroid α) := {p : set α × set α // is_indep_pair M₁ M₂ p }

/-- type of pairs of bases of M₁, M₂ -/
def basis_pair (M₁ M₂ : matroid α) := {p : set α × set α // is_basis_pair M₁ M₂ p }

/-- type of pairs of independent sets that are both contained in a subset X -/
def indep_pair_of_subset (M₁ M₂ : matroid α) (X : set α) :=
  {p : set α × set α // is_indep_pair M₁ M₂ p ∧ (p.1 ⊆ X ∧ p.2 ⊆ X) }

/-- size of the intersection of a pair of sets -/
def inter_size (pair : (set α × set α)) : ℤ := size (pair.1 ∩ pair.2)

/-- size of the union of a pair of sets -/
def union_size (pair : (set α × set α)) : ℤ := size (pair.1 ∪ pair.2)

/-- type of pairs of disjoint independent sets of M₁,M₂ respectively -/
def disjoint_indep_pair (M₁ M₂ : matroid α) := {pair : indep_pair M₁ M₂ // is_disjoint pair.1}

/-- type of pairs of disjoint bases of M₁,M₂ respectively -/
def disjoint_basis_pair (M₁ M₂ : matroid α) := {pair : basis_pair M₁ M₂ // is_disjoint pair.1}

/-- is the intersection of a basis of M₁ and a basis of M₂ -/
def is_inter_bases (M₁ M₂ : matroid α) :=
  λ X, ∃ B₁ B₂, is_basis M₁ B₁ ∧ is_basis M₂ B₂ ∧ B₁ ∩ B₂ = X

/-- type of sets that are the intersection of a basis of M₁ and a basis of M₂-/
def inter_bases (M₁ M₂ : matroid α) := {X : set α // is_inter_bases M₁ M₂ X}

/-- is contained in the intersection of a basis of M₁ and a basis of M₂-/
def is_subset_inter_bases (M₁ M₂ : matroid α) :=
  λ X, ∃ Y, is_inter_bases M₁ M₂ Y ∧ X ⊆ Y

/-- is the union of an independent set of M₁ and an independent set of M₂-/
def is_union_two_indep (M₁ M₂ : matroid α) : set α → Prop :=
  λ X, ∃ I₁ I₂, is_indep M₁ I₁ ∧ is_indep M₂ I₂ ∧ X = I₁ ∪ I₂

/-- has a partition into an independent set of M₁ and an independent set of M₂-/
def is_two_partitionable (M₁ M₂ : matroid α) : set α → Prop :=
  λ X, ∃ I₁ I₂, is_indep M₁ I₁ ∧ is_indep M₂ I₂ ∧ X = I₁ ∪ I₂ ∧ I₁ ∩ I₂ = ∅

/-- has a partition into a basis of M₁ and a basis set of M₂-/
def is_two_basis_partitionable (M₁ M₂ : matroid α) : set α → Prop :=
  λ X, ∃ B₁ B₂ , is_basis M₁ B₁ ∧ is_basis M₂ B₂ ∧ B₁ ∪ B₂ = X ∧ B₁ ∩ B₂ = ∅

/-- is the union of a basis of M₁ and a basis of M₂ -/
def is_union_two_bases (M₁ M₂ : matroid α) : set α → Prop :=
  λ X, ∃ B₁ B₂, is_basis M₁ B₁ ∧ is_basis M₂ B₂ ∧ B₁ ∪ B₂ = X

/--independence in both M₁ and M₂ -/
def is_common_ind (M₁ M₂ : matroid α) :=
  λ X, is_indep M₁ X ∧ is_indep M₂ X

/-- subtype of common independent sets -/
def common_ind (M₁ M₂ : matroid α) := {X : set α // is_common_ind M₁ M₂ X}


-- All the types above are trivially finite, and nonempty because bases/independent sets exist

instance indep_pair_fintype {M₁ M₂ : matroid α} : fintype (indep_pair M₁ M₂) :=
  by {unfold indep_pair, apply_instance }

instance basis_pair_fintype {M₁ M₂ : matroid α} : fintype (basis_pair M₁ M₂) :=
  by {unfold basis_pair, apply_instance }

instance indep_pair_nonempty {M₁ M₂ : matroid α} : nonempty (indep_pair M₁ M₂) :=
begin
  simp only [indep_pair, nonempty_subtype, prod.exists],
  from ⟨∅, ∅, ⟨M₁.empty_indep, M₂.empty_indep⟩ ⟩ ,
end

instance indep_pair_of_subset_nonempty {M₁ M₂ : matroid α} {X : set α} :
  nonempty (indep_pair_of_subset M₁ M₂ X) :=
begin
  simp only [indep_pair_of_subset, nonempty_subtype, prod.exists],
  from ⟨∅, ∅, ⟨M₁.empty_indep, M₂.empty_indep⟩, ⟨empty_subset _, empty_subset _⟩ ⟩ ,
end

instance indep_pair_of_subset_fintype {M₁ M₂ : matroid α} {X : set α} :
  fintype (indep_pair_of_subset M₁ M₂ X) :=
begin
  unfold indep_pair_of_subset, apply_instance,
end

instance basis_pair_nonempty {M₁ M₂ : matroid α} : nonempty (basis_pair M₁ M₂) :=
begin
  simp only [basis_pair, exists_and_distrib_right, nonempty_subtype, exists_and_distrib_left,
  prod.exists],
  cases exists_basis M₁ with B₁ hB₁,
  cases exists_basis M₂ with B₂ hB₂,
  from ⟨B₁, B₂, hB₁, hB₂⟩, 
end

lemma exists_inter_bases (M₁ M₂ : matroid α) :
  ∃ I, (is_inter_bases M₁ M₂ I) :=
begin
  cases exists_basis M₁ with B₁ hB₁,
  cases exists_basis M₂ with B₂ hB₂,
  from ⟨B₁ ∩ B₂, ⟨B₁,B₂,hB₁,hB₂,rfl⟩⟩,
end

instance inter_bases_nonempty (M₁ M₂ : matroid α) : nonempty (inter_bases M₁ M₂) :=
by {apply nonempty_subtype.mpr, apply exists_inter_bases, }

instance inter_bases_fintype (M₁ M₂ : matroid α) : fintype (inter_bases M₁ M₂) :=
by {unfold inter_bases, apply_instance,}

instance disjoint_indep_pair_nonempty (M₁ M₂ : matroid α) :
  nonempty (disjoint_indep_pair M₁ M₂) :=
by {unfold disjoint_indep_pair, refine nonempty_subtype.mpr _,
     use ⟨⟨∅,∅⟩, ⟨empty_indep M₁, empty_indep M₂⟩⟩, tidy,  }


instance nonempty_common_ind (M₁ M₂ : matroid α) : nonempty (common_ind M₁ M₂) :=
by {apply nonempty_subtype.mpr, from ⟨∅, ⟨empty_indep M₁, empty_indep M₂⟩⟩}

instance fintype_common_ind (M₁ M₂ : matroid α ) : fintype (common_ind M₁ M₂):=
  by {unfold common_ind, apply_instance}

instance coe_common_ind (M₁ M₂ : matroid α) : has_coe (common_ind M₁ M₂) (set α) :=
  ⟨λ X, X.val⟩


end prelim  

section params

/-- size of largest common independent set of M₁ and M₂ -/
def ν (M₁ M₂ : matroid α) : ℤ :=
  max_val (λ (X : common_ind M₁ M₂), size X.val)

/-- size of the largest set that is the union of independent sets of M₁ and M₂-/
def π₂ (M₁ M₂ : matroid α) : ℤ := 
  max_val (λ (Ip : indep_pair M₁ M₂), union_size Ip.val)

end params 

section lists

open_locale big_operators

variables {n : ℕ}


def is_indep_tuple (Ms : fin n → matroid α) (Xs : fin n → set α) :=
  ∀ i, (Ms i).is_indep (Xs i)

def indep_tuple (Ms : fin n → matroid α) :=
  {Is : fin n → set α // is_indep_tuple Ms Is}

instance indep_tuple_nonempty (Ms : fin n → matroid α) : nonempty (indep_tuple Ms) :=
  by {apply nonempty_subtype.mpr, exact ⟨λ i, ∅, λ i, (Ms i).empty_indep⟩,}

instance indep_tuple_fintype (Ms : fin n → matroid α) : fintype (indep_tuple Ms) :=
  by {unfold indep_tuple, apply_instance,  }

/-- size of largest partitionable set wrt a tuple of matroids -/
def π {n : ℕ} (Ms : fin n → matroid α) : ℤ :=
  max_val (λ Is : (indep_tuple Ms), size (set.Union Is.val))

def is_union_indep_tuple {n : ℕ} (Ms : fin n → matroid α) : (set α) → Prop :=
  λ X, ∃ (Is : indep_tuple Ms), X = set.Union Is.val



end lists
/-
/- property of a pair (M,X) that X is indep in M -/
def is_matroid_indep_pair : (matroid α) × (set α) → Prop := λ p, is_indep p.1 p.2

/- rank in M of X, given a pair (M,X) -/
def matroid_set_pair_to_rank : (matroid α) × (set α) → ℤ := λ p, p.1.r p.2

/- property of being a list of independent sets wrt a list of matroids -/
def is_indep_list (Ms : list (matroid α)) : list (set α) → Prop :=
  λ Xs, Xs.length = Ms.length ∧ (∀ MX ∈ Ms.zip Xs, is_matroid_indep_pair MX)

/- type of indep lists of a list of matroids -/
def indep_list (Ms : list (matroid α)) := {Xs : list (set α) // is_indep_list Ms Xs}

/- property of being the union of an indep list (equivalent to partitionability) -/
def is_union_indep_list'' (Ms : list (matroid α)) : (set α) → Prop :=
  λ Y, ∃ (Xs : indep_list Ms), list_union Xs.val = Y

def is_indep_pair_list : list (matroid α × set α) → Prop :=
  λ Ps, (∀ p ∈ Ps, is_matroid_indep_pair p) 

def indep_pair_list := {Ps : list (matroid α × set α) // is_indep_pair_list Ps}

def is_union_indep_list' (Ms : list (matroid α)) : set α → Prop :=
  λ Y, ∃ (Ps : indep_pair_list), Ps.val.unzip.1 = Ms ∧ list_union Ps.val.unzip.2 = Y

/- sum of ranks of a list of sets in a list of matroids -/
def sum_of_ranks_of_sets (Ms : list (matroid α)) (Xs : list (set α)) : ℤ :=
  list.sum (list.map (matroid_set_pair_to_rank) (Ms.zip Xs))

/- sum of ranks of a fixed set in a list of matroids -/
def sum_of_ranks_of_set (Ms : list (matroid α)) (X : set α) :ℤ :=
  sum_of_ranks_of_sets Ms (list.repeat X Ms.length)

@[simp] lemma sum_ranks_sets_empty_list (X : list (set α)) :
  sum_of_ranks_of_sets (list.nil) X = 0 :=
by {unfold sum_of_ranks_of_sets, simp, }

@[simp] lemma sum_ranks_set_empty_list (X : set α) :
  sum_of_ranks_of_set (list.nil) X = 0 :=
by {unfold sum_of_ranks_of_set, simp, }


instance indep_list_nonempty (Ms : list (matroid α)) : nonempty (indep_list Ms) :=
begin
  apply nonempty_subtype.mpr,
  unfold is_indep_list,
  induction Ms,
  from ⟨list.nil, by dec_trivial⟩,
  rcases Ms_ih with ⟨Ms',⟨h1,h2⟩⟩ ,
  refine ⟨Ms'.cons ∅, ⟨by simp [h1], λ MX, _⟩⟩, 
  simp only [list.mem_cons_iff, list.zip_cons_cons],
  rintro ⟨c1, c2⟩,
  apply empty_indep, apply h2, from H,
  -- I imagine this shouldn't be so hard 
end

instance indep_list_fintype (Ms : list (matroid α)) : fintype (indep_list Ms) :=
begin
  set f : indep_list Ms → vector (set α) (Ms.length) := λ Xs, ⟨Xs.val, Xs.property.1⟩ with hf,
  refine fintype.of_injective f (λ x x' hxx', _),
  dsimp [f] at hxx', cases x, cases x',
  rw subtype.mk_eq_mk at ⊢ hxx', from hxx',
  -- likewise
end

lemma indep_list_nil_elim {Xs : list (set α)} :
  is_indep_list (list.nil : list (matroid α)) Xs → Xs = list.nil :=
by {rintros ⟨hx,hx'⟩, simp [list.length_eq_zero] at hx, from hx,}

lemma indep_list_nil_iff_nil {Xs : list (set α)} :
  is_indep_list (list.nil : list (matroid α)) Xs ↔ Xs = list.nil :=
by {refine ⟨λ h, indep_list_nil_elim h, λ h,_⟩, unfold is_indep_list, rw h, simp, }


lemma indep_list_nil_elim_subtype (Xs : indep_list (list.nil : list (matroid α))) :
  Xs.val = list.nil :=
indep_list_nil_elim Xs.property

instance indep_nil_list_subsingleton :
  subsingleton (indep_list (list.nil : list (matroid α))) :=
⟨λ x y, by {cases x, cases y, rw [subtype.mk_eq_mk], rw [indep_list_nil_elim x_property, indep_list_nil_elim y_property],  }⟩






-- These next two lemmas are TODO - they should be provable and useful. Commented to avoid sorries 

/-lemma indep_list_iff_exists_zip (Ms : list (matroid α)) (X : set α) :
  is_union_indep_list Ms X ↔
    (∃ zMs : list ((matroid α) × (set α)),
    (
      ∀ p ∈ zMs, is_matroid_indep_pair p) ∧
      (list.unzip zMs).1 = Ms ∧
      list_union (list.unzip zMs).2 = X
    ) :=
begin
 
end
 



lemma union_of_indep_cons (Ms : list (matroid α)) (N : matroid α) (X : set α) :
  is_union_indep_list (N :: Ms) X ↔ ∃ Y X₀, is_indep N Y ∧ is_union_indep_list Ms X₀ ∧ Y ∪ X₀ = X :=
begin
  unfold is_union_indep_list,
  simp only [exists_exists_eq_and, exists_and_distrib_left, subtype.val_eq_coe],
  refine ⟨λ h, _, λ h, _⟩, 
  rcases h with ⟨⟨Xs, hXs⟩, hu⟩,
  induction Xs with Xhd Xtl, simp at hu,
end-/






/-
@[simp] lemma union_fin_zero (a : fin 0 → set α) :
  (⋃ i, a i) = ∅ :=

-/

-/


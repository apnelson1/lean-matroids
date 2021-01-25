
import tactic 
import .basic .int_lemmas 

open_locale classical 
open_locale big_operators 
noncomputable theory 

 
namespace ftype 

variables {U : ftype}

def list_union : list (set U) → set U := 
  λ Xs, (⋃ (X ∈ Xs), X) 

def list_inter : list (set U) → set U := 
  λ Xs, (⋂ (X ∈ Xs), X)

@[simp] lemma list_empty_union_eq_empty (Xs : list (set U)): 
  Xs = list.nil → list_union Xs = ∅ :=
λ h, by {unfold list_union, rw h, simp,}

@[simp] lemma list_empty_inter_eq_univ (Xs : list (set U)): 
  Xs = list.nil → list_inter Xs = univ :=
λ h, by {unfold list_inter, rw h, simp,}

@[simp] lemma list_single_union (Xs : list (set U)):
  Xs.length = 1 → list_union Xs = Xs.head := 
begin
  intro h, unfold list_union, rw list.eq_cons_of_length_one h, 
  ext, simp, 
end

@[simp] lemma list_single_inter (Xs : list (set U)):
  Xs.length = 1 → list_inter Xs = Xs.head := 
begin
  intro h, unfold list_inter, rw list.eq_cons_of_length_one h, 
  ext, simp, 
end

@[simp] lemma list_union_cons (Xs: list (set U))(Y : set U):
  list_union (Y :: Xs) = Y ∪ list_union Xs := 
begin
  unfold list_union, ext, 
  simp_rw[set.mem_union, set.mem_Union], 
  simp only [exists_prop, list.mem_cons_iff],
  refine ⟨λ h, _, λ h, _⟩; finish, 
end

@[simp] lemma list_inter_cons (Xs: list (set U))(Y : set U):
  list_inter (Y :: Xs) = Y ∩ list_inter Xs := 
begin
  unfold list_inter, ext, 
  simp_rw [set.mem_inter_iff, set.mem_Inter], 
  simp only [exists_prop, list.mem_cons_iff],
  refine ⟨λ h, _, λ h, _⟩; finish, 
end




end ftype

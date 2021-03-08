
import tactic 
import .size .int_lemmas 

open_locale classical 
open_locale big_operators 
noncomputable theory 

 
namespace ftype 
open set 

variables {U : Type}[fintype U]

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


namespace seq

@[simp] lemma fin_zero_Union (Xs : fin 0 → set U): 
set.Union Xs = ∅  := 
by {rw [set.Union_eq_empty], exact λ i, fin_zero_elim i}

@[simp] lemma fin_zero_Inter (Xs : fin 0 → set U): 
set.Inter Xs = univ  := 
by {rw [set.Inter_eq_univ], exact λ i, fin_zero_elim i}


lemma Union_cons {n : ℕ}(Xs : fin n → set U)(Y : set U):
set.Union (fin.cons Y Xs) = set.Union Xs ∪ Y  :=
begin
  ext, rw [iff.comm, set.mem_union, set.mem_Union, set.mem_Union],   
  refine ⟨λ h, _, λ h, _⟩, 
  rcases h with (⟨i, hi⟩ | h), 
    {use fin.succ i, simp [hi]},
    {use 0, convert h,},
  cases h with i hi, 
  revert i, refine λ i, fin.cases (λ h, _) (λ i₀ h, _) i,
    {right, convert h,}, 
  left, use i₀, 
  convert h, simp, 
end

lemma Inter_cons {n : ℕ}(Xs : fin n → set U)(Y : set U):
set.Inter (fin.cons Y Xs) = set.Inter Xs ∩ Y  :=
begin
  ext, rw [iff.comm, set.mem_inter_iff, set.mem_Inter, set.mem_Inter],   
  refine ⟨λ h, λ i, _, λ h, ⟨λ i, _, _⟩⟩, 
    {revert i, refine λ i, fin.cases (by convert h.2) (λ i₀, _) i, convert h.1 i₀, simp,  },
    {convert h (i.succ), simp,},
  convert h 0, 
end


end seq



end ftype

namespace list

lemma nil_of_unzip_nil_left {α β : Type}(L : list (α × β)) : 
  L.unzip.1 = list.nil → L = list.nil := 
λ h, by {rw [←L.zip_unzip, h], simp only [zip_nil_left]} 

lemma nil_of_unzip_nil_right {α β : Type}(L : list (α × β)) : 
  L.unzip.2 = list.nil → L = list.nil := 
λ h, by {rw [←L.zip_unzip, h], simp only [zip_nil_right]} 


end list 



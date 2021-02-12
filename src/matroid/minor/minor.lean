import ftype.basic ftype.embed ftype.minmax set_tactic.solver
import matroid.rankfun matroid.dual .projection .matroid_in

open_locale classical 
noncomputable theory

open ftype matroid set 

namespace matroid_in


variables {U : ftype}

section minor 

/-- minor relation between two matroid_in U-/
def is_minor (N M : matroid_in U) : Prop := 
  (N.E ⊆ M.E) ∧ 
  ∃ C ⊆ M.E \ N.E, (∀ X ⊆ N.E, N.r X = M.r (X ∪ C) - M.r C)  

/-- minor relation between a matroid_in U and a matroid U -/
def is_minor_of (N : matroid_in U)(M : matroid U) := 
  is_minor N M 

lemma minor_trans: transitive (λ (M₁ M₂ : matroid_in U), is_minor M₁ M₂) :=
begin
  rintros M₁ M₂ M₃ ⟨h1,⟨C₁,hC₁,h1'⟩⟩ ⟨h2,⟨C₂,hC₂,h2'⟩⟩, 
  refine ⟨subset_trans h1 h2,⟨C₁ ∪ C₂,⟨_,λ X hX, _⟩⟩⟩, 
  { convert union_subset_union hC₁ hC₂, ext, 
    simp only [ftype.diff_def, mem_inter_eq, mem_union_eq, mem_compl_eq], 
    tauto, },
  -- set_solver should work for the goal above, but it is glacial
  have hC₁M₂: C₁ ⊆ M₂.E := by 
  { intros x hx, simp only [ftype.diff_def, subset_inter_iff] at hC₁, tauto,},
  rw [h1' X hX, h2' (X ∪ C₁) _, h2' C₁ hC₁M₂, ←union_assoc],  ring,
  exact union_is_ub (subset_trans hX h1) hC₁M₂, 
end 

def contract (M : matroid_in U)(C : set U) : matroid_in U := 
⟨ M.E \ C, 
  M.carrier.project C, 
  by {convert M.carrier.projected_set_union_rank_zero C M.support, set_solver}⟩

@[simp, msimp] lemma contract_rank (M : matroid_in U)(C X: set U): 
  (M.contract C).r X = M.r (X ∪ C) - M.r C :=
M.carrier.project_r _ _ 

@[simp, msimp] lemma contract_E (M : matroid_in U)(C: set U):
  (M.contract C).E = M.E \ C := 
rfl 

def delete (M : matroid_in U)(D : set U) : matroid_in U := 
⟨ M.E \ D, 
  M.carrier.loopify D, 
  by {convert M.carrier.loopified_set_union_rank_zero D M.support, set_solver,}⟩

@[simp, msimp] lemma delete_rank (M : matroid_in U)(D X: set U): 
  (M.delete D).r X = M.r (X \ D) :=
rfl

@[simp, msimp] lemma delete_E (M : matroid_in U)(D: set U):
  (M.delete D).E = M.E \ D := 
rfl 


lemma con_del_eq_del_con (M : matroid_in U)(C D : set U)(h : C ∩ D = ∅) : 
  (M.contract C).delete D = (M.delete D).contract C := 
begin
  apply ext', simp [inter_right_comm _ Cᶜ], 
  intros X hX, 
  simp only [diff_def, matroid_in.contract_rank, matroid_in.delete_rank], 
  convert rfl;
  set_solver,
end

lemma dual_con_eq_del_dual (M : matroid_in U)(A : set U)(hA : A ⊆ M.E): 
  of_mat ((M.contract A).as_mat.dual) = (of_mat M.as_mat.dual).delete A :=
begin
  refine ext' (by simp) (λ X hX, _),
  simp only [matroid.dual_r] with msimp coe_up, 
  rw [(λ p q r z, by ring : ∀ p q r z : ℤ, p + (q-z) - (r-z) = p + q - r), 
  inter_comm _ Aᶜ, ←inter_assoc], 
  convert rfl; { ext, simp, tauto},
end


lemma dual_con (M : matroid_in U)(A : set U)(hu : A ⊆ M.E): 
  (M.contract A).dual = (M.dual).delete A :=
begin
  refine ext' (by simp) (λ X hX, _),
  simp only [matroid.dual_r] with msimp coe_up, 
  rw [(λ p q r z, by ring : ∀ p q r z : ℤ, p + (q-z) - (r-z) = p + q - r), 
  inter_comm _ Aᶜ, ←inter_assoc], 
  convert rfl; { ext, simp, tauto},
end

lemma dual_del (M : matroid_in U)(A : set U)(hu : A ⊆ M.E): 
  (M.delete A).dual = (M.dual).contract A :=
by {rw [←M.dual_dual, ← dual_con, matroid_in.dual_dual, matroid_in.dual_dual], exact hu}

lemma dual_con_del (M : matroid_in U)(C D : set U)(hi : C ∩ D = ∅)(hu : C ∪ D ⊆ M.E): 
  ((M.contract C).delete D).dual = ((M.dual).contract D).delete C :=
begin
  rw [dual_del _ D, dual_con _ C, con_del_eq_del_con], 
    rwa inter_comm, 
    exact subset_trans (subset_union_left _ _) hu, 
  simp only with msimp, set_solver, 
end

lemma dual_con_del' (M : matroid_in U)(C D : set U)(hi : C ∩ D = ∅)(hu : C ∪ D ⊆ M.E): 
  ((M.contract C).delete D).dual = (M.dual.delete C).contract D :=
by {rw [dual_con_del _ _ _ hi hu, con_del_eq_del_con],  rwa inter_comm,}

lemma minor_has_delete_contract {M N : matroid_in U}(h : is_minor N M): 
 ∃ C D, C ∪ D = M.E \ N.E ∧ C ∩ D = ∅ ∧ N = (M.contract C).delete D := 
begin
  rcases h with ⟨h, C, hC, hr⟩, 
  refine ⟨C, (M.E \ N.E) \ C, by { ext, simp at *, tauto,}, by simp, _⟩, 
  refine ext' (by { ext, simp at *, tauto,}) (λ X hX, _), 
  rw hr X hX, 
  simp only [ftype.diff_def, matroid_in.contract_rank, matroid_in.delete_rank, sub_left_inj], 
  convert rfl, 
  ext, simp, tauto, 
end

lemma minor_iff_has_delete_contract {M N : matroid_in U} : 
  is_minor N M 
↔ ∃ C D, C ∪ D = M.E \ N.E ∧ C ∩ D = ∅ ∧ N = (M.contract C).delete D :=
begin
  split, apply minor_has_delete_contract, 
  rintros ⟨C ,D, hu, hi, rfl⟩, 
  refine ⟨_,⟨C,_,_⟩⟩, 
  { intros x hx, simp at *, tauto, },
  simp only with msimp at *,  
  {apply inter_is_lb, 
    { refine subset_trans (subset_union_left C D) _, rw hu, apply inter_subset_left,   },
  intros x hx, simp, tauto, },
  intros X hX, 
  simp only with msimp at *, convert rfl,
  ext, simp at *, tauto,  
end

/-- a structure whose existence certifies that N is a minor of M -/
@[ext] structure minor_pair (N M : matroid_in U) :=
(C : set U)
(D : set U)
(disj : C ∩ D = ∅)
(union : C ∪ D = M.E \ N.E)
(minor : (M.contract C).delete D = N)


namespace minor_pair 

variables {N M : matroid_in U}

/-- constructs a minor pair from disjoint sets C and D contained in the groundset of M -/
def to_minor_pair (M : matroid_in U)(C D : set U)(hi : C ∩ D = ∅)(hu : C ∪ D ⊆ M.E): 
  minor_pair ((M.contract C).delete D) M := 
{ C := C,
  D := D,
  disj := hi,
  union := begin 
    simp only with msimp, 
    rw [subset_def_inter, inter_comm] at hu, 
    rw [inter_assoc, ←compl_union, compl_inter, inter_distrib_left, compl_compl, hu], simp, 
  end,
  minor := rfl }


instance minor_pair_fintype : fintype (minor_pair N M) :=  
by tactic.mk_fintype_instance

lemma nonempty_iff:
  nonempty (minor_pair N M) ↔ is_minor N M := 
begin
  rw [minor_iff_has_delete_contract], 
  refine ⟨λ h, _, λ h,  _ ⟩, 
  { rcases h with ⟨C, D, h_disj, h_union, rfl⟩, exact ⟨C,D,h_union,⟨h_disj,rfl⟩⟩,},
  rcases h with ⟨C,D, h', h'', rfl⟩, tidy, 
end

lemma minor_pair_to_is_minor : 
  minor_pair N M → is_minor N M :=
by {rw ←nonempty_iff, exact nonempty.intro}

lemma nonempty_inst (h : is_minor N M) :
  nonempty (minor_pair N M):= 
nonempty_iff.mpr h 

lemma ground_subset (p : minor_pair N M):
  N.E ⊆ M.E :=
by {rw ←p.minor, intro x, simp, tauto}

@[simp, msimp] lemma ground_inter_D (p : minor_pair N M):
  N.E ∩ p.D = ∅ :=
by {simp only [←p.minor] with msimp, rw inter_assoc, simp,}

@[simp, msimp] lemma ground_disj_D (p : minor_pair N M):
  disjoint N.E p.D :=
by {rw disjoint_iff_inter_eq_empty, apply ground_inter_D}

@[simp, msimp] lemma ground_inter_C (p : minor_pair N M):
  N.E ∩ p.C = ∅ :=
by {simp only [←p.minor] with msimp, rw [inter_right_comm, inter_comm, inter_assoc M.E], simp,}

@[simp, msimp] lemma ground_disj_C (p : minor_pair N M):
  disjoint N.E p.C :=
by {rw disjoint_iff_inter_eq_empty, apply ground_inter_C}

lemma C_ss_E (p : minor_pair N M): 
  p.C ⊆ M.E := 
by {refine subset_trans (subset_union_left p.C p.D) _, rw p.union, simp,  }

lemma D_ss_E (p : minor_pair N M): 
  p.D ⊆ M.E := 
by {refine subset_trans (subset_union_right p.C p.D) _, rw p.union, simp,  }

lemma C_union_D_ss_E (p : minor_pair N M): 
  p.C ∪ p.D ⊆ M.E := 
by simp [p.union]

/-- converts a minor pair C D for N M to the minor pair D C for N* M*-/
def to_dual (p : minor_pair N M) : minor_pair N.dual M.dual := 
⟨ p.D, 
  p.C,
  by {rwa [inter_comm, p.disj]}, 
  by {rw [union_comm, p.union], simp}, 
  by {rw [←dual_con_del _ _ _ p.disj _], simp_rw p.minor, rw p.union, simp, }⟩ 
  
/-- converts a minor pair C D for N* M* to the minor pair D C for N M-/
def of_dual (p : minor_pair N.dual M.dual) : minor_pair N M := 
⟨(to_dual p).C,
 (to_dual p).D, 
 (to_dual p).disj, 
 (to_dual p).union, 
  by {have := (to_dual p).minor, simp only [matroid_in.dual_dual] at this, exact this  }⟩

/-- natural bijection between minor pairs and dual minor pairs -/
def dual_equiv : minor_pair N M ≃ minor_pair N.dual M.dual := 
{ to_fun := to_dual,
  inv_fun := of_dual,
  left_inv := λ x, by {ext; simp [of_dual,to_dual], },
  right_inv := λ x, by {ext; simp [of_dual,to_dual], }} 

@[simp, msimp] lemma dual_equiv_C (p : minor_pair N M) : (dual_equiv p).C = p.D := rfl  
@[simp, msimp] lemma dual_equiv_D (p : minor_pair N M) : (dual_equiv p).D = p.C := rfl 
@[simp, msimp] lemma dual_equiv_inv_C (p : minor_pair N.dual M.dual) : (dual_equiv.inv_fun p).C = p.D := rfl 
@[simp, msimp] lemma dual_equiv_inv_D (p : minor_pair N.dual M.dual) : (dual_equiv.inv_fun p).D = p.C := rfl 

/-- given a minor pair C,D and a subset of C whose removal doesn't drop the rank of C, we can move that subset to D -/
def move_to_delete (p : minor_pair N M){A : set U}
(h₁ : A ⊆ p.C) (h₂ : M.r (p.C \ A) = M.r p.C) : minor_pair N M := 
{ C := p.C \ A,
  D := p.D ∪ A,
  disj := by {have := p.disj, ext, simp at *, rw ←subset_of_compl_iff_disjoint at this, tauto ,  },
  union := by {rw ←p.union, ext, simp at *,tauto,  },
  minor := begin
    have := p.minor, simp_rw ← this, clear this, 
    apply ext', { ext, simp at *, tauto, },
    
    intros X hX, repeat {rw r_eq_r_inter _ X}, rw diff_def at h₂,  
    rw (by rw p.minor : ((M.contract p.C).delete p.D).E = N.E) at *, 
    rw (by {simp_rw ←p.minor, ext, simp [compl_inter], tauto,} :
      ((M.contract (p.C \ A)).delete (p.D ∪ A)).E = N.E) at *, 
    
    simp only [compl_union, h₂, sub_left_inj, union_comm _ (p.C ∩ Aᶜ), union_comm _ p.C] with msimp, 
    
    suffices : X ∩ N.E ∩ p.Dᶜ = X ∩ N.E ∩ (p.Dᶜ ∩ Aᶜ), 
    { rw this, apply rank_eq_of_le_union_supset, apply inter_subset_left, exact h₂, }, 
    suffices : N.E ∩ Aᶜ = N.E, 
    { rw ←this, ext, simp, tauto, }, 
    rw [←subset_def_inter, subset_compl_iff_disjoint, ←disjoint_iff_inter_eq_empty], 
    exact disjoint_of_subset_right h₁ (ground_disj_C p), 
  end } 

/-- given a minor pair C,D and a subset of D that is spanned by C, we can move that subset to C -/
def move_to_contract (p : minor_pair N M){A : set U}
(h₁ : A ⊆ p.D)(h₂ : M.r (p.C ∪ A) = M.r p.C) : minor_pair N M :=
{ C := p.C ∪ A, 
  D := p.D \ A, 
  disj := by {have := p.disj, ext, simp at *, rw ←subset_of_compl_iff_disjoint at this, tauto ,  },
  union := by {rw ←p.union, ext, simp at *,tauto,  },
  minor := begin
    have := p.minor, simp_rw ← this, clear this, 
    apply ext', { ext, simp at *, tauto, },
    
    intros X hX, repeat {rw r_eq_r_inter _ X}, 
    rw (by rw p.minor : ((M.contract p.C).delete p.D).E = N.E) at *, 
    rw (by {simp_rw ←p.minor, ext, simp [compl_inter], tauto,} :
      ((M.contract (p.C ∪ A)).delete (p.D \ A)).E = N.E) at *, 
    
    simp only [h₂, sub_left_inj] with msimp at ⊢ hX, 
    rw [union_comm, union_comm _ p.C, eq_comm], 
    suffices : X ∩ N.E ∩ p.Dᶜ = X ∩ N.E ∩ (p.D ∩ Aᶜ)ᶜ, 
    { rw this, apply rank_eq_of_le_union_supset, apply subset_union_left, exact h₂.symm,},
    rw [compl_inter, inter_distrib_left, inter_assoc _ _ Aᶜᶜ],
    suffices : N.E ∩ Aᶜᶜ = ∅, rw this, simp, 
    rw [compl_compl, ←disjoint_iff_inter_eq_empty], 
    exact disjoint_of_subset_right h₁ (ground_disj_D p), 
  end
}


end minor_pair 

lemma dual_minor_of_minor {M N : matroid_in U}: 
  N.is_minor M → N.dual.is_minor M.dual :=
begin
  simp_rw [minor_iff_has_delete_contract, dual_ground], 
  intro h, 
  rcases h with ⟨C, D, h, h', rfl⟩, 
  refine ⟨D,C, by {rwa union_comm}, by {rwa inter_comm}, dual_con_del _ _ _ h' _⟩,
  rw h, simp,     
end

lemma minor_iff_dual_minor {M N : matroid_in U}:
  N.is_minor M ↔ N.dual.is_minor M.dual := 
begin
  refine ⟨λ h, dual_minor_of_minor h, λ h, _⟩, 
  rw [←dual_dual N, ←dual_dual M], 
  exact dual_minor_of_minor h, 
end

 /-- A minor pair C D with C dependent doesn't maximize r C + r* D -/
lemma suboptimal_goodness {N M : matroid_in U}(p : minor_pair N M)(hdep : ¬is_indep M p.C): 
∃ p': minor_pair N M, M.r p.C + M.dual.r p.D < M.r p'.C + M.dual.r p'.D :=
begin
  simp_rw [indep_iff_carrier, not_indep_iff_exists_removal, r_carrier_eq_r, elem_iff_subset] at hdep, 
  rcases hdep with ⟨e,heC, he⟩, 
  use p.move_to_delete heC he, 
  rw [minor_pair.move_to_delete], dsimp only, rw [he, dual_r], 
  simp only [ftype.diff_def, matroid_in.dual_r, set.compl_union, sub_lt_sub_iff_right, add_lt_add_iff_left], 

  have h : size ((p.D ∪ e) ∩ M.E) = size (p.D ∩ M.E) + 1, 
  { rw [inter_distrib_right, subset_def_inter_mp (subset_trans heC p.C_ss_E)], 
    apply add_nonelem_size, 
    by_contra hn, 
    rw ←elem_iff_subset at heC, 
    have := eq_empty_iff_forall_not_mem.mp p.disj e,   
    simp only [set.mem_inter_eq] at this hn,
    tauto, },
  rw h, 
  apply (λ x y y' h', by {rw [add_right_comm, add_assoc],simp only [add_lt_add_iff_left, int.lt_add_one_iff, h'],}: 
  ∀ (x y y' : ℤ), y ≤ y' → x + y < x + 1 + y'), 
  simp_rw [←r_eq_inter_r], 
  have hCD : p.C ∪ p.Dᶜ = p.Dᶜ := subset_def_union_mp (by {rw subset_compl_iff_disjoint, exact p.disj}),
  have h' := (rank_eq_of_le_union_supset (p.Dᶜ ∩ (e : U)ᶜ) (by simp) he).symm,  
  
  convert (has_le.le.trans_eq (eq.le _) h'), 
  { rw [diff_def, ←inter_distrib_right, hCD], }, 
  convert rfl,
  rw [union_distrib_left, hCD, ←subset_def_inter],   
  convert subset_univ _, 
  rwa [←compl_subset_iff_union, ←subset_iff_subset_compl],
end


/-- each minor can be represented by a indep/coindep contract_delete pair -/
lemma minor_has_good_delete_contract {M N : matroid_in U}(h_minor : is_minor N M):
   ∃ (p : minor_pair N M), (M.is_indep p.C) ∧ (M.dual.is_indep p.D) := 
begin
  letI := minor_pair.nonempty_inst h_minor, 
  
  /- take a minor pair C D maximizing r C + r* D-/
  rcases max_spec (λ (p : minor_pair N M), M.r p.C + M.dual.r p.D) with ⟨p,⟨h,h'⟩⟩,
  use p, by_contra hn, rw not_and_distrib at hn, cases hn, 
  { rcases suboptimal_goodness p hn with ⟨p',hp'⟩, have := h' p', dsimp only at this, linarith,},
  
  rcases suboptimal_goodness (minor_pair.dual_equiv p) hn with ⟨p', hp'⟩, 
  specialize h' (minor_pair.dual_equiv.inv_fun p'), 
  simp only with msimp at h' hp',  
  linarith, 
end



end minor 


end matroid_in 


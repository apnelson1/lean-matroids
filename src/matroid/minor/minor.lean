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

/-def is_minor_pair (N M : matroid_in U) (CD : set U × set U) := 
  CD.1 ∩ CD.2 = ∅ ∧ CD.1 ∪ CD.2 = 

def minor_pair (N M : matroid_in U): Type := 
  {p : set U × set U // 
    p.1 ∩ p.2 = ∅ 
  ∧ p.1 ∪ p.2 = M.E \ N.E
  ∧ N = ((M: matroid_in U).contract p.1).delete p.2} -/

namespace minor_pair 

variables {N M : matroid_in U}




instance fintype:
  fintype (minor_pair N M) :=  
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

@[simp, msimp] lemma ground_disjoint_D (p : minor_pair N M):
  N.E ∩ p.D = ∅ :=
by {simp only [←p.minor] with msimp, rw inter_assoc, simp,}

@[simp, msimp] lemma ground_disjoint_C (p : minor_pair N M):
  N.E ∩ p.C = ∅ :=
by {simp only [←p.minor] with msimp, rw [inter_right_comm, inter_comm, inter_assoc M.E], simp,}

def to_dual: 
  minor_pair N M → minor_pair N.dual M.dual := 
λ mp, 
  ⟨mp.D, mp.C,
   by {rwa [inter_comm, mp.disj]}, 
   by {rw [union_comm, mp.union], simp}, 
   by {rw [←dual_con_del _ _ _ mp.disj _], simp_rw mp.minor, rw mp.union, simp, }⟩ 
  
def of_dual:
  minor_pair N.dual M.dual → minor_pair N M := 
λ p, ⟨(to_dual p).C,(to_dual p).D, (to_dual p).disj, (to_dual p).union, 
      by {have := (to_dual p).minor, simp only [matroid_in.dual_dual] at this, exact this  }⟩


def dual_equiv:
  minor_pair N M ≃ minor_pair N.dual M.dual := 
{ to_fun := to_dual,
  inv_fun := of_dual,
  left_inv := λ x, by {ext; simp [of_dual,to_dual], },
  right_inv := λ x, by {ext; simp [of_dual,to_dual], }} 

@[simp, msimp] lemma dual_equiv_C (p : minor_pair N M) : (dual_equiv p).C = p.D := rfl  
@[simp, msimp] lemma dual_equiv_D (p : minor_pair N M) : (dual_equiv p).D = p.C := rfl 
@[simp, msimp] lemma dual_equiv_inv_C (p : minor_pair N.dual M.dual) : (dual_equiv.inv_fun p).C = p.D := rfl 
@[simp, msimp] lemma dual_equiv_inv_D (p : minor_pair N.dual M.dual) : (dual_equiv.inv_fun p).D = p.C := rfl 

/-- given a minor pair and a subset of C whose removal doesn't drop the rank of C, we can move that subset to D-/
def move_to_delete (p : minor_pair N M){A : set U}(h₁ : A ⊆ p.C)
(h₂ : M.r (p.C \ A) = M.r p.C) : minor_pair N M := 
{ C := p.C \ A,
  D := p.D ∪ A,
  disj := by {have := p.disj, ext, simp at *, rw ←subset_of_compl_iff_disjoint at this, tauto ,  },
  union := by {rw ←p.union, ext, simp at *,tauto,  },
  minor := begin
    have := p.minor, simp_rw ← this, clear this, 
    apply ext', { ext, simp at *, tauto, },
    
    intros X hX, repeat {rw r_eq_r_inter _ X}, 
    rw (by rw p.minor : ((M.contract p.C).delete p.D).E = N.E) at *, 
    rw (by {simp_rw ←p.minor, ext, simp [compl_inter], tauto,} :
      ((M.contract (p.C \ A)).delete (p.D ∪ A)).E = N.E) at *, 
    
    have hXD : X ⊆ p.Dᶜ, 
    { refine subset_trans hX _, rw subset_compl_iff_disjoint, simp,}, 
    have hXA : X ⊆ Aᶜ,
    { refine subset_trans hX _, 
      rw [subset_compl_iff_disjoint, ←disjoint_iff_inter_eq_empty], 
      refine disjoint_of_subset_right h₁ _,
      rw disjoint_iff_inter_eq_empty,
      exact ground_disjoint_C p, }, 
    rw subset_def_inter at hX hXD hXA, rw diff_def at h₂,  
    simp only [compl_union, h₂, sub_left_inj, hX, hXD, hXA] with msimp, 
    rw [←inter_assoc, hXD, hXA, union_comm X, union_comm X],
    exact rank_eq_of_le_union_supset _ _ X (inter_subset_left p.C Aᶜ) h₂, 
  end } 


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

--def minor_pair_dual_equiv {M N : matroid}


def goodness (N M : matroid_in U) : set U × set U → ℤ := 
  λ p, (M.r p.1 + M.dual.r p.2)

@[msimp] lemma goodness_dual {N M : matroid_in U}(p : set U × set U):
  goodness N.dual M.dual p = goodness N M ⟨p.2,p.1⟩ := 
by {rw [goodness, goodness, dual_dual], dsimp only, apply add_comm }
  
lemma minor_has_good_delete_contract {M N : matroid_in U}:
  is_minor N M → ∃ (p : minor_pair N M), (M.is_indep p.C) ∧ (M.dual.is_indep p.D) := 
begin
  intro h_minor, 
  
  have suboptimal_goodness : 
  ∀ {N' M' : matroid_in U} (p : minor_pair N' M'), 
  ¬is_indep M' p.C → ∃ p': minor_pair N' M', goodness N' M' ⟨p.C,p.D⟩ < goodness N' M' ⟨p'.C,p'.D⟩, 
  begin
    rintros N' M' ⟨C,D,hi,hu,rfl⟩ hdep, dsimp only at *, 
    sorry, --rw matroid_in.indep_iff at hdep,  
  end,

  letI := minor_pair.nonempty_inst h_minor, 
  rcases max_spec (λ (p : minor_pair N M), goodness N M ⟨p.C,p.D⟩) with ⟨p,⟨h,h'⟩⟩,
  use p, by_contra hn, rw not_and_distrib at hn, cases hn, 
  {rcases suboptimal_goodness p hn with ⟨p',hp'⟩, linarith [h' p'], },

  rcases suboptimal_goodness (minor_pair.dual_equiv p) hn with ⟨p', hp'⟩, 
  specialize h' (minor_pair.dual_equiv.inv_fun p'), 
  simp only with msimp at h' hp',  
  linarith, 
end



end minor 


end matroid_in 


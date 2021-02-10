import ftype.basic set_tactic.solver
import .rankfun .dual .projection

open_locale classical 
noncomputable theory

open ftype 

variables {U : ftype}

/-- a matroid_in U corresponds to a matroid defined on some subset E of U. Implemented as a matroid on which the nonelements of 
E are all loops. -/
@[ext] structure matroid_in (U : ftype) :=
(groundset : set U)
(carrier : matroid U)
(support : carrier.r groundsetᶜ = 0)

namespace matroid_in 

/-- the rank of a set X wrt a matroid_in U. Elements of X outside the groundset of U are ingored -/
def r (M : matroid_in U)(X : set U) := M.carrier.r X 

lemma ext' (M₁ M₂ : matroid_in U)(h_ground : M₁.groundset = M₂.groundset)(h_r : ∀ X ⊆ M₁.groundset, M₁.r X = M₂.r X):
  M₁ = M₂ := 
begin
  apply matroid_in.ext _ _ h_ground, ext X,
  specialize h_r (X ∩ M₁.groundset) (by simp),  
  rw (by simp : X = (X ∩ M₁.groundset) ∪ (X ∩ M₁.groundsetᶜ)), 
  have h₁ := matroid.rank_inter_rank_zero X M₁.support,
  have h₂ := matroid.rank_inter_rank_zero X M₂.support, rw ←h_ground at h₂, 
  rw [matroid.rank_eq_rank_union_rank_zero (X ∩ M₁.groundset) h₁, matroid.rank_eq_rank_union_rank_zero (X ∩ M₁.groundset) h₂], 
  exact h_r, 
end

/-- the ftype coming from the groundset of M -/
def ground (M : matroid_in U) : ftype := ⟨M.groundset⟩

/-- a matroid_in U gives a matroid on a subtype -/
def as_mat_on (M : matroid_in U)(E : set U) : matroid ⟨E⟩ := 
{ r := λ X, M.r (subtype.val '' X),
  R0 := λ X, M.carrier.R0 _,
  R1 := λ X, by {dsimp only [r], rw ←size_subtype_img, apply M.carrier.R1},
  R2 := λ X Y hXY, by {apply M.carrier.R2, apply set.image_subset _ hXY, },
  R3 := λ X Y, by {dsimp only, convert M.carrier.R3 _ _, apply set.image_union, exact (set.image_inter subtype.val_injective).symm} }

/-- a matroid_in U, viewed as a matroid on the subtype defined by its groundset -/
def as_mat (M : matroid_in U) : matroid M.ground := as_mat_on M M.groundset 

/-- a matroid_in U, constructed from a matroid on a subtype of U -/
def of_mat {E : set U}(N : matroid ⟨E⟩) : matroid_in U := 
{ groundset := E,
  carrier := 
  { r := λ X, N.r {e : E | e.val ∈ X},
    R0 := λ X, N.R0 _,
    R1 := λ X, by {refine le_trans (N.R1 _) (eq.trans_le _ (size_mono_inter_right E X)), apply size_inter_subtype },
    R2 := λ X Y hXY, by {dsimp only, apply N.R2, tauto,  },
    R3 := λ X Y, N.R3 _ _, },
  support := by {simp, apply N.rank_empty, } }

lemma groundset_of_mat {E : set U}(N : matroid ⟨E⟩) : (of_mat N).groundset = E := rfl 

lemma as_mat_of_mat {E : set U}(N : matroid ⟨E⟩) : 
  as_mat (of_mat N) = N :=
begin
  ext X, dsimp only [as_mat, as_mat_on, of_mat], convert rfl, ext x, 
  suffices: x ∈ X ↔ x.val ∈ subtype.val '' X, from this, 
  simp only [set.image_congr, set.mem_image, exists_eq_right, subtype.exists, subtype.val_eq_coe],
  refine ⟨λ h, by {cases x, tauto}, λ h, _⟩,
  cases x with x hx, rcases h with ⟨y,z, h⟩, convert h.1, convert h.2.symm, 
end


def as_matroid_in (M : matroid U) : matroid_in U := ⟨univ, M, by simp⟩

instance coe_to_matroid_in : has_coe (matroid U) (matroid_in U) := ⟨λ M, as_matroid_in M⟩

section minor 

/-- minor relation between two matroid_in U-/
def is_minor (N M : matroid_in U) : Prop := 
  (N.groundset ⊆ M.groundset) ∧ 
  ∃ C ⊆ M.groundset \ N.groundset, (∀ X ⊆ N.groundset, N.r X = M.r (X ∪ C) - M.r C)  

/-- minor relation between a matroid_in U and a matroid U -/
def is_minor_of (N : matroid_in U)(M : matroid U) := 
  is_minor N M 

lemma minor_trans: transitive (λ (M₁ M₂ : matroid_in U), is_minor M₁ M₂) :=
begin
  rintros M₁ M₂ M₃ ⟨h1,⟨C₁,hC₁,h1'⟩⟩ ⟨h2,⟨C₂,hC₂,h2'⟩⟩, 
  refine ⟨subset_trans h1 h2,⟨C₁ ∪ C₂,⟨_,λ X hX, _⟩⟩⟩, 
  { convert set.union_subset_union hC₁ hC₂, ext, 
    simp only [ftype.diff_def, set.mem_inter_eq, set.mem_union_eq, set.mem_compl_eq], 
    tauto, },
  -- set_solver should work for the goal above, but it is glacial
  have hC₁M₂: C₁ ⊆ M₂.groundset := by 
  { intros x hx, simp only [ftype.diff_def, set.subset_inter_iff] at hC₁, tauto,},
  rw [h1' X hX, h2' (X ∪ C₁) _, h2' C₁ hC₁M₂, ←union_assoc],  ring,
  exact union_is_ub (subset_trans hX h1) hC₁M₂, 
end 

def contract (M : matroid_in U)(C : set U) : matroid_in U := 
⟨ M.groundset \ C, 
  M.carrier.project C, 
  by {convert M.carrier.projected_set_union_rank_zero C M.support, set_solver}⟩

@[simp] lemma contract_rank (M : matroid_in U)(C X: set U): 
  (M.contract C).r X = M.r (X ∪ C) - M.r C :=
M.carrier.project_r _ _ 

@[simp] lemma contract_groundset (M : matroid_in U)(C: set U):
  (M.contract C).groundset = M.groundset \ C := 
  rfl 

def delete (M : matroid_in U)(D : set U) : matroid_in U := 
⟨ M.groundset \ D, 
  M.carrier.loopify D, 
  by {convert M.carrier.loopified_set_union_rank_zero D M.support, set_solver,}⟩

@[simp] lemma delete_rank (M : matroid_in U)(D X: set U): 
  (M.delete D).r X = M.r (X \ D) :=
M.carrier.loopify_r _ _ 

@[simp] lemma delete_groundset (M : matroid_in U)(D: set U):
  (M.delete D).groundset = M.groundset \ D := 
  rfl 

lemma con_del_eq_del_con (M : matroid_in U)(C D : set U)(h : C ∩ D = ∅) : 
  (M.contract C).delete D = (M.delete D).contract C := 
begin
  apply ext', simp [inter_right_comm _ Cᶜ], 
  intros X hX, 
  simp only [ftype.diff_def, matroid_in.contract_rank, matroid_in.delete_rank], 
  convert rfl;
  set_solver,
end


end minor 

end matroid_in 


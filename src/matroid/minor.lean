import ftype.basic ftype.embed set_tactic.solver
import .rankfun .dual .projection

open_locale classical 
noncomputable theory

open ftype 

variables {U : ftype}


/-- a matroid_in U corresponds to a matroid defined on some subset E of U. Implemented as a matroid on which the nonelements of 
E are all loops. -/
@[ext] structure matroid_in (U : ftype) :=
(E : set U)
(carrier : matroid U)
(support : carrier.r Eᶜ = 0)

namespace matroid_in 

/-- the rank of a set X wrt a matroid_in U. Elements of X outside the E of U are ignored -/
def r (M : matroid_in U)(X : set U) := M.carrier.r X 

lemma ext' {M₁ M₂ : matroid_in U}(h_ground : M₁.E = M₂.E)(h_r : ∀ X ⊆ M₁.E, M₁.r X = M₂.r X):
  M₁ = M₂ := 
begin
  apply matroid_in.ext _ _ h_ground, ext X,
  specialize h_r (X ∩ M₁.E) (by simp),  
  rw (by simp : X = (X ∩ M₁.E) ∪ (X ∩ M₁.Eᶜ)), 
  have h₁ := matroid.rank_inter_rank_zero X M₁.support,
  have h₂ := matroid.rank_inter_rank_zero X M₂.support, rw ←h_ground at h₂, 
  rw [matroid.rank_eq_rank_union_rank_zero (X ∩ M₁.E) h₁, matroid.rank_eq_rank_union_rank_zero (X ∩ M₁.E) h₂], 
  exact h_r, 
end

/-- the ftype coming from the E of M -/
def ground (M : matroid_in U) := subftype M.E

/-- a matroid_in U gives a matroid on a subtype -/
def as_mat_on (M : matroid_in U)(E : set U) : matroid (subftype E) := 
{ r := λ X, M.r X,
  R0 := λ X, M.carrier.R0 _,
  R1 := λ X, by {dsimp only [r], rw ←size_subtype_img, apply M.carrier.R1},
  R2 := λ X Y hXY, by {apply M.carrier.R2, apply set.image_subset _ hXY, },
  R3 := λ X Y, by {dsimp only, convert M.carrier.R3 _ _, apply set.image_union, exact (set.image_inter subtype.val_injective).symm} }

/-- a matroid_in U, viewed as a matroid on the subtype defined by its E -/
def as_mat (M : matroid_in U) : matroid M.ground := as_mat_on M M.E 

mk_simp_attribute msimp "minor simp lemmas"


@[simp, msimp] lemma as_mat_r (M : matroid_in U)(X : set (subftype M.E)): 
  M.as_mat.r X = M.r (X : set U) :=
rfl 



/-- a matroid_in U, constructed from a matroid on a subtype of U -/
def of_mat {E : set U}(N : matroid (subftype E)) : matroid_in U := 
{ E := E,
  carrier := 
  { r := λ X, N.r (inter_subtype E X ),
    R0 := λ X, N.R0 _,
    R1 := λ X, by {refine le_trans (N.R1 _) (eq.trans_le _ (size_mono_inter_right E X)), apply size_inter_subtype },
    R2 := λ X Y hXY, by {dsimp only, apply N.R2, tauto,  },
    R3 := λ X Y, N.R3 _ _, },
  support := by {simp [inter_subtype],} }

@[simp, msimp] lemma of_mat_E {E : set U}(N : matroid (subftype E)) : 
  (of_mat N).E = E :=
rfl 

@[simp, msimp] lemma of_mat_r {E : set U}(N : matroid (subftype E))(X : set U) : 
  (of_mat N).r X = N.r (inter_subtype E X) := 
rfl 

lemma r_of_mat {E : set U}(N : matroid (subftype E))(X : set (subftype E)): 
  N.r X = (of_mat N).r X := 
begin
  simp only [matroid_in.of_mat_r], convert rfl, 
  unfold inter_subtype, ext x , --rcases x with ⟨x,hx⟩, 
  simp only [set.mem_set_of_eq, subtype.coe_mk], 
  refine ⟨λ h, _, λ h, ⟨x,⟨h, by simp⟩⟩ ⟩,
  rcases h with ⟨⟨y, h⟩, h', h''⟩, 
  cases x, 
  simp only [subtype.coe_mk] at h'', 
  convert h',  rwa h'', 
end


@[simp,msimp] lemma as_mat_of_mat {E : set U}(N : matroid (subftype E)) : 
  as_mat (of_mat N) = N :=
begin
  ext X, dsimp only [as_mat, as_mat_on, of_mat], convert rfl, ext x, 
  suffices: x ∈ X ↔ x.val ∈ subtype.val '' X, from this, 
  simp only [set.image_congr, set.mem_image, exists_eq_right, subtype.exists, subtype.val_eq_coe],
  refine ⟨λ h, by {cases x, tauto}, λ h, _⟩,
  cases x with x hx, rcases h with ⟨y,z, h⟩, convert h.1, convert h.2.symm, 
end

@[simp,msimp] lemma of_mat_as_mat (M : matroid_in U) : 
  of_mat (as_mat M) = M :=
ext' (by simp) 
     (λ X hX, by {simp only with msimp coe_up at *, convert rfl, rw subset_def_inter_mp hX}) 


lemma of_mat_as_mat_on {E E' : set U}(N : matroid (subftype E))(h : E' = E): 
   of_mat ((of_mat N).as_mat_on E') = of_mat N := 
begin
  apply ext', convert rfl, 
  intros X hX, 
  simp only [of_mat, as_mat_on], dsimp only [ftype.ftype_coe], 
  convert rfl, exact h.symm, 
  dsimp only [ftype.ftype_coe, r, inter_subtype],   
  ext Y, convert rfl,  ext e, rcases e with ⟨e,he⟩,  
  simp only [set.image_congr, set.mem_image, exists_eq_right, subtype.exists, subtype.val_eq_coe,
  exists_eq_right, subtype.coe_mk], 
  refine ⟨λ h', _, λ h', _⟩,
  {simp only at h', rcases h' with ⟨_, h'', rfl⟩, exact h'',}, 
  rw h, exact ⟨⟨e,he⟩,⟨h',rfl⟩⟩,
end

lemma of_mat_inj {R : set U}(N N' : matroid (subftype R)):
  of_mat N = of_mat N' → N = N' := 
λ h, by {ext, rw [r_of_mat,r_of_mat,h]}  

def as_matroid_in (M : matroid U) : matroid_in U := ⟨univ, M, by simp⟩

instance coe_to_matroid_in : has_coe (matroid U) (matroid_in U) := ⟨λ M, as_matroid_in M⟩




def dual (M : matroid_in U) : matroid_in U := 
  of_mat (as_mat M).dual 

@[simp, msimp] lemma dual_r (M : matroid_in U)(X : set U) :
  (dual M).r X = size (X ∩ M.E) + M.r (M.E \ X) - M.r M.E  :=
begin
  rw [dual, of_mat_r, matroid.dual_r], simp only with coe_up, convert rfl, 
  simp only with coe_up, 
  ext,simp only [ftype.diff_def, set.mem_inter_eq, set.mem_compl_eq], tauto, 
  simp only with coe_up, 
end 

lemma of_mat_dual {E : set U}(M : matroid (subftype E)): 
  of_mat M.dual = (of_mat M).dual := 
by {unfold dual, convert rfl, simp}


@[simp, msimp] lemma dual_ground (M : matroid_in U): 
  (dual M).E = M.E := 
rfl 

@[simp, msimp] lemma dual_dual (M : matroid_in U):
  M.dual.dual = M := 
by {simp_rw [dual,of_mat_dual, as_mat_of_mat, ←of_mat_dual, matroid.dual_dual, of_mat_as_mat]}

lemma dual_inj {M M' : matroid_in U}(h : M.dual = M'.dual):
  M = M' := 
by rw [←dual_dual M, ←dual_dual M',h]



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
  { convert set.union_subset_union hC₁ hC₂, ext, 
    simp only [ftype.diff_def, set.mem_inter_eq, set.mem_union_eq, set.mem_compl_eq], 
    tauto, },
  -- set_solver should work for the goal above, but it is glacial
  have hC₁M₂: C₁ ⊆ M₂.E := by 
  { intros x hx, simp only [ftype.diff_def, set.subset_inter_iff] at hC₁, tauto,},
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
  simp only [matroid.dual_r, ftype.diff_def] with msimp coe_up, 
  rw [(λ p q r z, by ring : ∀ p q r z : ℤ, p + (q-z) - (r-z) = p + q - r), 
  inter_comm _ Aᶜ, ←inter_assoc], 
  convert rfl; { ext, simp, tauto},
end


lemma dual_con (M : matroid_in U)(A : set U)(hu : A ⊆ M.E): 
  (M.contract A).dual = (M.dual).delete A :=
begin
  refine ext' (by simp) (λ X hX, _),
  simp only [matroid.dual_r, ftype.diff_def] with msimp coe_up, 
  rw [(λ p q r z, by ring : ∀ p q r z : ℤ, p + (q-z) - (r-z) = p + q - r), 
  inter_comm _ Aᶜ, ←inter_assoc], 
  convert rfl; { ext, simp, tauto},
end

lemma dual_del (M : matroid_in U)(A : set U)(hu : A ⊆ M.E): 
  (M.delete A).dual = (M.dual).contract A :=
by {rw [←dual_dual M, ← dual_con, dual_dual, dual_dual], exact hu}

lemma dual_con_del (M : matroid_in U)(C D : set U)(hi : C ∩ D = ∅)(hu : C ∪ D ⊆ M.E): 
  ((M.contract C).delete D).dual = ((M.dual).contract D).delete C :=
begin
  have : D ⊆ (M.contract C).E := by {simp only with msimp, set_solver, }, 
  rw dual_del _ D this, 
  


end

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
  simp only [ftype.diff_def] with msimp at *,  
  {apply inter_is_lb, 
    { refine subset_trans (subset_union_left C D) _, rw hu, apply inter_subset_left,   },
  intros x hx, simp, tauto, },
  intros X hX, 
  simp only with msimp at *, convert rfl,
  ext, simp at *, tauto,  
end

def minor_pair {M N : matroid_in U}(h : is_minor N M) : Type := 
  {p : set U × set U // 
    p.1 ∩ p.2 = ∅ 
  ∧ p.1 ∪ p.2 = M.E \ N.E
  ∧ N = ((M: matroid_in U).contract p.1).delete p.2} 

instance minor_pair_nonempty {M N : matroid_in U}(h : is_minor N M) :
  nonempty (minor_pair h):= 
begin
  apply nonempty_subtype.mpr, 
  rcases minor_has_delete_contract h with ⟨C,D, h', h'', rfl⟩,
  refine ⟨⟨C,D⟩, _,_,by simp⟩; try {assumption}, 
end

instance minor_pair_fintype {M N : matroid_in U}(h : is_minor N M) :
  fintype (minor_pair h):=  
by {unfold minor_pair, apply_instance}


lemma minor_has_good_delete_contract {M : matroid U}{N : matroid_in U}:
  is_minor N M → ∃ (C D : set U), 
  C ∩ D = ∅ 
  ∧ N = ((M : matroid_in U).contract C).delete D 
  ∧ M.is_indep C ∧ M.dual.is_indep D   :=
begin
  intro h_minor, 
  set badness : minor_pair h_minor → ℤ := 
  
end



end minor 

end matroid_in 


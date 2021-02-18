import prelim.embed prelim.minmax set_tactic.solver
import matroid.rankfun matroid.dual .projection

open_locale classical 
noncomputable theory

open matroid set 

variables {U : Type}[fintype U]

/-- a matroid_in U corresponds to a matroid defined on some subset E of U. 
Implemented as a matroid on which the nonelements of E are all loops. -/

structure matroid_in (U : Type)[fintype U] :=
(E : set U)
(carrier : matroid U)
(support : carrier.r Eᶜ = 0)

namespace matroid_in 

/-- the rank of a set X wrt a matroid_in U. Elements of X outside the E of U are ignored -/
def r (M : matroid_in U)(X : set U) := M.carrier.r X 

lemma r_carrier_eq_r (M : matroid_in U)(X : set U): 
  M.carrier.r X = M.r X := 
rfl 

lemma r_eq_r_inter (M : matroid_in U)(X : set U):
  M.r X = M.r (X ∩ M.E) :=
begin
  nth_rewrite 0 ←(inter_union_compl X M.E), 
  apply rank_eq_rank_union_rank_zero,
  exact rank_inter_rank_zero _ M.support, 
end

lemma r_eq_inter_r (M : matroid_in U)(X : set U):
  M.r X = M.r (M.E ∩ X) :=
by rw [r_eq_r_inter, inter_comm]

lemma ext' {M M' : matroid_in U}(h : M.E = M'.E)(h' : M.carrier = M'.carrier): 
  M = M' :=
by {cases M, cases M', dsimp only at *, induction h', induction h, refl,} 

@[ext] lemma ext {M₁ M₂ : matroid_in U}(h_ground : M₁.E = M₂.E)(h_r : ∀ X ⊆ M₁.E, M₁.r X = M₂.r X):
  M₁ = M₂ := 
begin
  apply ext' h_ground, ext X,
  specialize h_r (X ∩ M₁.E) (by simp),  
  rw (by simp : X = (X ∩ M₁.E) ∪ (X ∩ M₁.Eᶜ)), 
  have h₁ := matroid.rank_inter_rank_zero X M₁.support,
  have h₂ := matroid.rank_inter_rank_zero X M₂.support, rw ←h_ground at h₂, 
  rw [matroid.rank_eq_rank_union_rank_zero (X ∩ M₁.E) h₁, matroid.rank_eq_rank_union_rank_zero (X ∩ M₁.E) h₂], 
  exact h_r, 
end

/-- a matroid_in U gives a matroid on a subtype -/
def as_mat_on (M : matroid_in U)(E : set U) : matroid E := 
{ r := λ X, M.r X,
  R0 := λ X, M.carrier.R0 _,
  R1 := λ X, by {dsimp only [r], rw ←size_subtype_img, apply M.carrier.R1},
  R2 := λ X Y hXY, by {apply M.carrier.R2, apply set.image_subset _ hXY, },
  R3 := λ X Y, by {dsimp only, convert M.carrier.R3 _ _, apply set.image_union, exact (set.image_inter subtype.val_injective).symm} }

/-- a matroid_in U, viewed as a matroid on the subtype defined by its E -/
def as_mat (M : matroid_in U) : matroid M.E := as_mat_on M M.E 

mk_simp_attribute msimp "minor simp lemmas"

attribute [msimp] diff_eq 

@[simp, msimp] lemma as_mat_r (M : matroid_in U)(X : set (M.E)): 
  M.as_mat.r X = M.r (X : set U) :=
rfl 

/-- a matroid_in U, constructed from a matroid on a subtype of U -/
def of_mat {E : set U}(N : matroid E) : matroid_in U := 
{ E := E,
  carrier := 
  { r := λ X, N.r (inter_subtype E X ),
    R0 := λ X, N.R0 _,
    R1 := λ X, by {refine le_trans (N.R1 _) (eq.trans_le _ (size_mono_inter_right E X)), 
                  rw inter_comm, apply size_inter_subtype },
    R2 := λ X Y hXY, by {dsimp only, apply N.R2, tauto,  },
    R3 := λ X Y, N.R3 _ _, },
  support := by {simp [inter_subtype],} }

@[simp, msimp] lemma of_mat_E {E : set U}(N : matroid E) : 
  (of_mat N).E = E :=
rfl 

@[simp, msimp] lemma of_mat_r {E : set U}(N : matroid E)(X : set U) : 
  (of_mat N).r X = N.r (inter_subtype E X) := 
rfl 

lemma r_of_mat {E : set U}(N : matroid E)(X : set E): 
  N.r X = (of_mat N).r X := 
begin
  simp only [matroid_in.of_mat_r], convert rfl, 
  unfold inter_subtype, ext x , --rcases x with ⟨x,hx⟩, 
  simp only [set.mem_preimage], 
  tidy, 
end

@[simp,msimp] lemma as_mat_of_mat {E : set U}(N : matroid E) : 
  as_mat (of_mat N) = N :=
begin
  ext X, dsimp only [as_mat, as_mat_on, of_mat], convert rfl, ext x, 
  suffices: x ∈ X ↔ x.val ∈ subtype.val '' X, from this, 
  simp only [image_congr, mem_image, exists_eq_right, subtype.exists, subtype.val_eq_coe],
  refine ⟨λ h, by {cases x, tauto}, λ h, _⟩,
  cases x with x hx, rcases h with ⟨y,z, h⟩, convert h.1, convert h.2.symm, 
end

@[simp,msimp] lemma of_mat_as_mat (M : matroid_in U) : 
  of_mat (as_mat M) = M :=
ext (by simp) (λ X hX, by {simp only with msimp coe_up at *, congr', exact subset_def_inter_mp hX}) 


lemma of_mat_as_mat_on {E E' : set U}(N : matroid E)(h : E' = E): 
   of_mat ((of_mat N).as_mat_on E') = of_mat N := 
begin
  ext : 1, convert rfl, 
  intros X hX, 
  simp only [of_mat, as_mat_on],  
  convert rfl, exact h.symm, 
  ext Y, unfold r, dsimp only, congr' 1, 
  simp [h] with coe_up, 
end

lemma of_mat_inj {R : set U}(N N' : matroid R):
  of_mat N = of_mat N' → N = N' := 
λ h, by {ext, rw [r_of_mat,r_of_mat,h]}  

def as_matroid_in (M : matroid U) : matroid_in U := ⟨univ, M, by simp⟩

instance coe_to_matroid_in : has_coe (matroid U) (matroid_in U) := ⟨λ M, as_matroid_in M⟩

@[simp, msimp] lemma as_matroid_in_E (M : matroid U): 
  (as_matroid_in M).E = univ 
:= rfl 

@[simp, msimp] lemma coe_to_as_matroid_in_E (M : matroid U): 
  (M : matroid_in U).E = univ 
:= rfl 

@[simp, msimp] lemma as_matroid_in_r (M : matroid U)(X : set U): 
  (as_matroid_in M).r X = M.r X 
:= rfl 

@[simp, msimp] lemma coe_to_as_matroid_in_r (M : matroid U)(X : set U): 
  (M : matroid_in U).r X = M.r X 
:= rfl 

section defs 

/-- translates a property of sets defined on (matroid V) to the corresponding
set property on (matroid_in U). -/
def lift_mat_set_property (P : Π {V : Type}[ft : fintype V], @matroid V ft → set V → Prop): 
  (matroid_in U → set U → Prop) :=
  λ M, (λ X, X ⊆ M.E ∧ (P M.as_mat) (inter_subtype M.E X))

---------------------------------------------------------------------------

def is_indep (M : matroid_in U)(X : set U): Prop := 
  (lift_mat_set_property (@matroid.is_indep)) M X 

lemma indep_iff_r (M : matroid_in U)(X : set U): 
  is_indep M X ↔ M.r X = size X := 
begin
  rw [is_indep, lift_mat_set_property], dsimp only, rw [matroid.indep_iff_r],  
  simp only with coe_up msimp, 
  refine ⟨λ h, _, λ h, _⟩, 
  { rw subset_def_inter at h, rw ←h.1, exact h.2}, 
  suffices h' : X ⊆ M.E, refine ⟨h', by {rwa[subset_def_inter_mp h'],}⟩, 
  rw r_eq_r_inter at h, 
  have h' := M.carrier.rank_le_size (X ∩ M.E), 
  rw [r_carrier_eq_r, h] at h', 
  rw [subset_def_inter, eq_of_le_size_subset _ h'], 
  apply inter_subset_left, 
end

lemma indep_iff_carrier {M : matroid_in U}{X : set U}:
  M.is_indep X ↔ M.carrier.is_indep X :=
by rw [indep_iff_r, matroid.indep_iff_r, r_carrier_eq_r]

lemma indep_iff_subtype {M : matroid_in U}{X : set U}: 
  M.is_indep X ↔ X ⊆ M.E ∧ M.as_mat.is_indep (inter_subtype M.E X) :=
by rw [is_indep, lift_mat_set_property]

def is_circuit (M : matroid_in U)(C : set U) := 
  (lift_mat_set_property (@matroid.is_circuit)) M C 

lemma circuit_iff_r {M : matroid_in U}{C : set U}:
  M.is_circuit C ↔ M.r C = size C - 1 ∧ (∀ Y, Y ⊂ C → M.r Y = size Y) ∧ C ⊆ M.E := 
begin
  simp_rw [is_circuit, lift_mat_set_property, matroid.circuit_iff_r], 
  simp only with coe_up msimp, 
  refine ⟨λ h, _, λ h, _⟩, 
  { rcases h with ⟨h, h', h''⟩, 
    rwa subset_def_inter_mp h at h', 
    refine ⟨h', (λ Y hY, _), h⟩, 
    have hYE : Y ∩ M.E = Y := subset_def_inter_mp (subset.trans hY.1 h),
    rw subset_def_inter at h,  
    specialize h'' (inter_subtype _ Y) _, 
    { simp only with coe_up at h'',
      convert h''; 
      exact hYE.symm, },
    simpa only [h,hYE] with coe_up, },
  rcases h with ⟨h,h',h''⟩, 
  refine ⟨h'', _,λ Y hY, _⟩, 
  { convert h; rwa subset_def_inter_mp h'', },
  apply h', 
  refine subset.lt_of_lt_of_le hY (inter_subset_left _ _), 
end

lemma circuit_iff_carrier {M : matroid_in U}{C : set U}:
  M.is_circuit C ↔ M.carrier.is_circuit C ∧ C ⊆ M.E :=
by {simp_rw [circuit_iff_r, matroid.circuit_iff_r, r_carrier_eq_r], tauto}  

lemma circuit_iff_subtype {M : matroid_in U}{X : set U}:
  M.is_circuit X ↔ X ⊆ M.E ∧ M.as_mat.is_circuit (inter_subtype M.E X) := 
by rw [is_circuit, lift_mat_set_property]

def dual (M : matroid_in U) : matroid_in U := 
  of_mat (as_mat M).dual 

@[simp, msimp] lemma dual_r (M : matroid_in U)(X : set U) :
  (dual M).r X = size (X ∩ M.E) + M.r (M.E \ X) - M.r M.E  :=
begin
  rw [dual, of_mat_r, matroid.dual_r], simp only with coe_up, convert rfl, 
  simp only with coe_up, 
  ext,simp only [diff_eq, mem_inter_eq, mem_compl_eq], tauto, 
  simp only with coe_up, 
end 

lemma of_mat_dual {E : set U}(M : matroid E): 
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

lemma dual_inj_iff {M M' : matroid_in U}:
  M = M' ↔ M.dual = M'.dual := 
⟨λ h, by {rw h}, λ h, dual_inj h⟩

lemma coindep_iff_r {M : matroid_in U}{X : set U}: 
  M.dual.is_indep X ↔ X ⊆ M.E ∧ M.r (M.E \ X) = M.r M.E :=
begin
  simp_rw [indep_iff_r, dual_r, ←r_carrier_eq_r, diff_eq, subset_def_inter], 
  refine ⟨λ h, _, λ h, _⟩, 
  { have h1 := size_mono_inter_left X M.E, 
    have h2 := M.carrier.rank_mono_inter_left M.E Xᶜ,   
    refine ⟨eq_of_eq_size_subset (inter_subset_left _ _) (by linarith) , by linarith⟩},
  rw [h.1, h.2], simp, 
end

end defs 

variables {V : Type}[fintype V]

/-- isomorphism between a matroid_in an a matroid -/
def isom (M : matroid_in U)(N : matroid V) := 
  matroid.isom M.as_mat N 

def is_isom (M : matroid_in U)(N : matroid V) := 
  nonempty (M.isom N)

/-- for (M : matroid U), gives an matroid_in isomorphism from of_mat M to M -/
def of_mat_isom (M : matroid U) : isom (as_matroid_in M) M := 
{ equiv := equiv.subtype_univ_equiv (by tauto),
  on_rank := λ X, by {apply congr_arg, ext, exact iff.rfl, } }



end matroid_in
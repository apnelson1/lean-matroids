import prelim.embed 
import matroid.rankfun matroid.dual .projection .matroid_in 

open_locale classical 
noncomputable theory

open matroid set 

namespace matroid_in

variables {U V : Type}[nonempty (fintype U)][nonempty (fintype V)]


/-- the contraction of C in M. Implemented as a projection -/
def contract (M : matroid_in U)(C : set U) : matroid_in U := 
⟨ M.E \ C, 
  M.carrier.project C, 
  by {convert M.carrier.projected_set_union_rank_zero C M.support, 
      rw [diff_eq, compl_compl_inter_right], }⟩

/-- the deletion of D in M. Implemented as a loopification -/
def delete (M : matroid_in U)(D : set U) : matroid_in U := 
⟨ M.E \ D, 
  M.carrier.loopify D, 
  by {convert M.carrier.loopified_set_union_rank_zero D M.support, set_solver,}⟩

/-- the restriction of M to R (i.e. the deletion of Rᶜ)-/
def restrict (M : matroid_in U)(R : set U) : matroid_in U := M.delete Rᶜ 

notation M / C := matroid_in.contract M C 
notation M \ D := matroid_in.delete M D 
notation M ∣ R := matroid_in.restrict M R 

lemma restr_eq_del_compl (M : matroid_in U)(R : set U):
  M ∣ R = M \ Rᶜ := 
rfl 

@[simp, msimp] lemma con_rank (M : matroid_in U)(C X: set U): 
  (M / C).r X = M.r (X ∪ C) - M.r C :=
M.carrier.project_r _ _ 

@[simp, msimp] lemma con_E (M : matroid_in U)(C: set U):
  (M / C).E = M.E \ C := 
rfl 

@[simp, msimp] lemma del_rank (M : matroid_in U)(D X: set U): 
  (M \ D).r X = M.r (X \ D) :=
rfl

@[simp, msimp] lemma restr_r (M : matroid_in U)(R X : set U):
  (M ∣ R).r X = M.r (X ∩ R) := 
by rw [restr_eq_del_compl, del_rank, diff_compl]

@[simp, msimp] lemma del_E (M : matroid_in U)(D: set U):
  (M \ D).E = M.E \ D := 
rfl 

@[simp, msimp] lemma restr_E (M : matroid_in U)(R : set U): 
  (M ∣ R).E = M.E ∩ R := 
by rw [restr_eq_del_compl, del_E, diff_compl]

lemma contr_restr_E (M : matroid_in U){C R : set U}(hR : R ⊆ M.E \ C): 
  (M / C ∣ R).E = R := 
by rwa [restr_E, con_E, ←subset_iff_inter_eq_right]

@[simp, msimp] lemma con_empty (M : matroid_in U): 
  (M / ∅) = M := 
by {ext, simp, intros X hX, simp [←r_carrier_eq_r _ ∅]}

@[simp, msimp] lemma del_empty (M : matroid_in U): 
  (M \ ∅) = M := 
by {ext, simp, intros X hX, simp [←r_carrier_eq_r _ ∅]}

@[simp,msimp] lemma del_del (M : matroid_in U)(D D' : set U):
  (M \ D \ D') = M \ (D ∪ D') := 
by {ext, simp [diff_eq, ←inter_assoc], intros X hX, simp [diff_eq, ←inter_assoc, inter_right_comm ],  }

lemma del_del_comm (M : matroid_in U)(D D' : set U): 
  M \ D \ D' = M \ D' \ D := 
by rw [del_del, union_comm, ←del_del]

lemma del_eq_del_inter_E (M : matroid_in U)(D : set U): 
  M \ D = M \ (M.E ∩ D) :=
begin
  ext, 
  {  simp only [diff_eq] with msimp, rw [compl_inter, inter_distrib_left], simp,  },
  simp only [diff_eq] with msimp, intros X hX, 
  rw [subset_inter_iff, subset_iff_disjoint_compl, subset_iff_inter_eq_left] at hX, 
  rw [compl_inter, inter_distrib_left], simp [hX], 
end

lemma con_eq_con_inter_E (M : matroid_in U)(C : set U): 
  M / C = M / (M.E ∩ C) := 
begin
  ext,
  {  simp only [diff_eq] with msimp, rw [compl_inter, inter_distrib_left], simp,  },
  intros X hX, 
  simp only with msimp at *, 
  have : M.E ∩ X = X := by {rw inter_comm, exact subset_iff_inter_eq_left.mp (subset.trans hX (inter_subset_left _ _))}, 
  rw [r_eq_inter_r M C, r_eq_inter_r M (X ∪ C), inter_distrib_left, this],
end

lemma con_del_E (M : matroid_in U)(C D : set U): 
  (M / C \ D).E = M.E \ (C ∪ D) :=
by {simp only [diff_eq] with msimp, simp [←inter_assoc]}

lemma con_del_eq_del_con (M : matroid_in U)(C D : set U)(h : C ∩ D = ∅) : 
  M / C \ D = M \ D / C := 
begin
  ext, simp [diff_eq, inter_right_comm _ Cᶜ], 
  intros X hX, 
  simp only [diff_eq, matroid_in.con_rank, matroid_in.del_rank], 
  convert rfl; set_solver,
end

/- turns contract/delete to delete/contract when C ∩ D ≠ ∅ -/
lemma con_del_eq_del_con' (M : matroid_in U)(C D : set U):
  M / C \ D = M \ (D \ C) / C :=
begin
  rw [del_eq_del_inter_E, con_del_eq_del_con, del_eq_del_inter_E M (D \ C)], 
  congr' 2, simp [diff_eq, ←inter_assoc, inter_right_comm],  
  ext, simp, tauto, 
end

/- turns delete/contract to contract/delete when C ∩ D ≠ ∅ -/
lemma del_con_eq_con_del' (M : matroid_in U)(C D : set U):
  M \ D / C = M / (C \ D) \ D :=
begin
  rw [con_eq_con_inter_E, ←con_del_eq_del_con, con_eq_con_inter_E M (C \ D)], 
  congr' 2, simp [diff_eq, ←inter_assoc, inter_right_comm],  
  {ext, simp, tauto}, 
end

lemma dual_con_eq_del_dual (M : matroid_in U)(A : set U)(hA : A ⊆ M.E): 
  of_mat ((M / A).as_mat.dual) = (of_mat M.as_mat.dual) \ A :=
begin
  ext, simp, 
  refine (λ X hX, _),
  simp only [diff_eq, matroid.dual_r] with msimp coe_up, 
  rw [(λ p q r z, by ring : ∀ p q r z : ℤ, p + (q-z) - (r-z) = p + q - r), 
  inter_comm _ Aᶜ, ←inter_assoc], 
  convert rfl; {ext, simp, tauto},
end

lemma dual_con (M : matroid_in U)(A : set U): 
  (M / A).dual = (M.dual) \ A :=
begin
  rw [con_eq_con_inter_E, del_eq_del_inter_E],  simp only with msimp, 
  set A' := M.E ∩ A with hA', 
  ext, simp, 
  refine (λ X hX, _),
  simp only [diff_eq, matroid.dual_r] with msimp coe_up, 
  rw [(λ p q r z, by ring : ∀ p q r z : ℤ, p + (q-z) - (r-z) = p + q - r), 
  inter_comm _ A'ᶜ, ←inter_assoc], 
  convert rfl; { ext, simp, tauto},
end

lemma dual_del (M : matroid_in U)(A : set U):
  (M \ A).dual = M.dual / A :=
by rw [←M.dual_dual, ←dual_con, matroid_in.dual_dual, matroid_in.dual_dual]

lemma con_con (M : matroid_in U)(C C' : set U):
  (M / C / C') = M / (C ∪ C') :=
by {rw [←M.dual_dual], repeat {rw ←dual_del}, rw del_del}

lemma con_con_comm (M : matroid_in U)(C C' : set U): 
  M / C / C' = M / C' / C:= 
by rw [con_con, union_comm, ← con_con]

lemma con_del_con_del (M : matroid_in U)(C C' D D': set U)(h : (C ∪ C') ∩ (D ∪ D') = ∅ ):
  M / C \ D / C' \ D' = M / (C ∪ C') \ (D ∪ D') :=
begin
  repeat {rw con_del_eq_del_con}, rwa [con_con, del_del], 
  all_goals 
  {apply disjoint_of_subsets _ _ h, 
    repeat {apply subset_union_left}, 
    repeat {apply subset_union_right},}, 
end

lemma dual_con_del (M : matroid_in U){C D : set U}(hi : C ∩ D = ∅): 
  (M / C \ D).dual = M.dual / D \ C :=
by {rw [dual_del _ D, dual_con _ C, con_del_eq_del_con], rwa inter_comm,} 
    
lemma dual_con_del' (M : matroid_in U){C D : set U}(hi : C ∩ D = ∅): 
  (M / C \ D).dual = M.dual \ C / D :=
by {rw [dual_con_del _ hi, con_del_eq_del_con],  rwa inter_comm,}

lemma con_rank_ground (M : matroid_in U)(C : set U):
  (M / C).r (M / C).E = M.r M.E - M.r C := 
begin
  simp only [diff_eq] with msimp, 
  rw r_eq_inter_r, convert rfl, 
  rw [inter_distrib_left, ←inter_assoc, inter_self, ←inter_distrib_left], simp,    
end

lemma indep_del_iff_indep_loopify {M : matroid_in U}{D X : set U}: 
  (M \ D).is_indep X ↔ (M.carrier.loopify D).is_indep X := 
by rw [indep_iff_carrier, delete]

lemma indep_del_iff {M : matroid_in U}{D X : set U}: 
  (M \ D).is_indep X ↔ X ∩ D = ∅ ∧ M.is_indep X := 
by {rw [indep_del_iff_indep_loopify, indep_loopify_iff, indep_iff_r, matroid.indep_iff_r, r_carrier_eq_r], tauto,  }

lemma delete_coindep_rank_ground (M : matroid_in U){D : set U}(hD : M.dual.is_indep D):
  (M \ D).r (M \ D).E = M.r M.E := 
by {simp only [inter_assoc, inter_self, diff_eq] with msimp, exact (coindep_iff_r.mp hD).2,} 

lemma coindep_contract_iff {M : matroid_in U}{C X : set U}: 
  (M / C).dual.is_indep X ↔ X ∩ C = ∅ ∧ M.dual.is_indep X := 
by rw [dual_con, indep_del_iff]

/-- structure consisting of an ordered pair of disjoint sets contained in M.E . Possibly should
be abstracted away from matroids completely -/
@[ext] structure cd_pair (M : matroid_in U) :=
(C : set U)
(D : set U)
(disj : C ∩ D = ∅)
(C_ss_E : C ⊆ M.E)
(D_ss_E : D ⊆ M.E)

instance cd_pair.fintype (M : matroid_in U) : 
  nonempty (fintype (cd_pair M)) := 
nonempty.intro (by { letI := classical.choice _inst_1,  tactic.mk_fintype_instance, })

def cd_pair.trivial (M : matroid_in U): cd_pair M := 
⟨∅, ∅, by rw inter_self, empty_subset _, empty_subset _⟩ 

def cd_pair.switch {M : matroid_in U} (p : cd_pair M ): cd_pair M  :=
⟨p.D,p.C, by {simpa [inter_comm] using p.disj}, p.D_ss_E, p.C_ss_E ⟩

def cd_pair.of_eq_E {M M': matroid_in U}(p : cd_pair M)(hE : M'.E = M.E): 
  cd_pair M' :=
⟨p.C,p.D, p.disj, by simpa [hE] using p.C_ss_E, by simpa [hE] using p.D_ss_E⟩  

lemma cd_pair.rank {M : matroid_in U}(p : cd_pair M)(X : set U)(hX : X ⊆ (M / p.C \ p.D).E): 
  (M / p.C \ p.D).r X = M.r (X ∪ p.C) - M.r p.C := 
begin
  simp only [diff_eq] with msimp at *, congr', 
  exact subset_iff_inter_eq_left.mp (subset.trans hX (inter_subset_right _ _)), 
end

@[simp, msimp] lemma cd_pair.rank_subtype {M : matroid_in U}(p : cd_pair M)(X : set (M / p.C \ p.D).E): 
  (M / p.C \ p.D).r X = M.r (X ∪ p.C) - M.r p.C := 
by {rw cd_pair.rank, rintro x hx, obtain ⟨⟨x,h⟩,-,rfl⟩ := (mem_image _ _ _).mp hx, exact h, }

@[simp, msimp] lemma cd_pair.E {M : matroid_in U}(p : cd_pair M): 
  (M / p.C \ p.D).E = M.E \ (p.C ∪ p.D) := 
by simp only [diff_diff] with msimp

def cd_pair.of_restr (M : matroid_in U){R : set U}(hR : R ⊆ M.E): 
  cd_pair M := 
{ C := ∅, 
  D := M.E \ R, 
  C_ss_E := empty_subset _, 
  D_ss_E := diff_subset _ _, 
  disj := empty_inter _}

def cd_pair.of_con_restr (M : matroid_in U){C R : set U}(hC : C ⊆ M.E)(hR : R ⊆ M.E \ C): 
  cd_pair M :=
{ C := C, 
  D := M.E \ (C ∪ R), 
  C_ss_E := hC, 
  D_ss_E := diff_subset _ _,
  disj := by {ext, simp, tauto}}


/-- maps a cd_pair M to the corresponding pair in M.as_mat-/
def cd_pair.to_as_mat {M : matroid_in U}(p : cd_pair M): cd_pair (M.as_mat : matroid_in M.E) := 
{ C := (coe ⁻¹' p.C), 
  D := (coe ⁻¹' p.D), 
  disj := by {unfold_coes, rw [←preimage_inter, p.disj, preimage_empty]},
  C_ss_E := λ x hx, by {simp at *}, 
  D_ss_E := λ x hx, by {simp at *}}

/-- maps a cd_pair (M.as_mat : matroid_in M.E) to the corresponding pair in M-/
def cd_pair.from_as_mat {M : matroid_in U}(p : cd_pair (M.as_mat : matroid_in M.E)) : cd_pair M := 
{ C := coe '' p.C,
  D := coe '' p.D,
  disj := by {unfold_coes, rw [image_inter, p.disj, image_empty], exact subtype.coe_injective,  },
  C_ss_E := by simp,
  D_ss_E := by simp }

 
/-- the image of a cd_pair under an injection  -/
def cd_pair.image {M : matroid U}{M' : matroid V}(p : cd_pair (M : matroid_in U))(f : U ↪ V): 
  cd_pair (M' : matroid_in V) := 
{ C := (f.to_fun '' p.C),
  D := (f.to_fun '' p.D),
  disj := by {rw [(image_inter f.inj'), p.disj, image_empty], },
  C_ss_E := λ x hx, by simp, 
  D_ss_E := λ x hx, by simp} 

end matroid_in 

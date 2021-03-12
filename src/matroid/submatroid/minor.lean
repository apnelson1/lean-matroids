import prelim.embed prelim.minmax set_tactic.solver tactic.derive_fintype
import matroid.rankfun matroid.dual .projection .matroid_in .delete_contract 

open_locale classical 
noncomputable theory

open matroid set 

namespace matroid_in

variables {α β : Type} [fintype α][fintype β]

section minor 

/- a structure whose existence certifies that N is a minor of M -/
@[ext] structure minor_pair (N M : matroid_in α) extends cd_pair M :=
(minor : M / C \ D = N)

instance coe_to_cd_pair (N M : matroid_in α) : has_coe (minor_pair N M) (cd_pair M) := 
⟨λ x, x.to_cd_pair⟩  

@[simp] lemma to_cd_pair_as_coe {N M : matroid_in α} (p : minor_pair M N) :
  p.to_cd_pair = coe p := 
rfl

/-- minor relation on matroid_in α-/
def is_minor (N M : matroid_in α) : Prop := 
  nonempty (minor_pair N M)

def is_proper_minor (N M : matroid_in α) : Prop :=
  is_minor N M ∧ N ≠ M 

def is_restriction (N M : matroid_in α) : Prop := 
  ∃ P: minor_pair N M, P.C = ∅ 

def is_contraction_minor (N M : matroid_in α) : Prop := 
  ∃ P: minor_pair N M, P.D = ∅

/-- constructs a minor pair from contract/delete sets C and D  -/
def to_minor_pair (M : matroid_in α) (C D : set α) :
  minor_pair (M / C \ D) M :=
{ C := M.E ∩ C ,
  D := (M.E ∩ D) \ C,
  disj := by {ext, simp, tauto, },
  C_ss_E := inter_subset_left _ _,
  D_ss_E := subset.trans (diff_subset _ _) (inter_subset_left _ _),
  minor := by {
    dsimp, rw [← con_eq_con_inter_E], 
    nth_rewrite 1 [del_eq_del_inter_E], 
    simp [diff_eq, inter_right_comm], }}

namespace minor_pair 

variables {N M : matroid_in α} (mp : minor_pair N M)

/-- given a minor pair N M, returns the corresponding minor_pair in M.as_mat -/
def minor_pair_to_as_mat (P : minor_pair N M) : 
    minor_pair ((M.as_mat : matroid_in M.E) / (coe ⁻¹' P.C) \ (coe ⁻¹' P.D)) M.as_mat :=
{  minor := rfl, .. cd_pair.to_as_mat (coe P) }

instance fintype : fintype (minor_pair N M) :=  
fintype.of_injective (to_cd_pair) (λ x y hxy, by {cases x, cases y, tidy})

/-- constructs the trivial minor pair associated with M -/
def trivial (M : matroid_in α) : minor_pair M M := 
⟨cd_pair.trivial M, by simp [cd_pair.trivial]⟩

lemma union : mp.C ∪ mp.D = M.E \ N.E := 
let ⟨⟨C,D,disj,C_ss_E,D_ss_E⟩, hmin⟩ := mp in 
begin
  show C ∪ D = M.E \ N.E, 
  simp only [←hmin, diff_diff, diff_self_diff] with msimp, 
  rw [eq_comm, ←subset_iff_inter_eq_right, union_subset_iff], 
  split; assumption, 
end

lemma minor_eq : M / mp.C \ mp.D = N := mp.minor 

def of_restrict (M : matroid_in α){R : set α} (hR : R ⊆ M.E) : 
  minor_pair (M ∣ R) M := 
{minor := by {dsimp only [cd_pair.of_restr, restrict], rw [con_empty, diff_eq, ← del_eq_del_inter_E],} ,
 .. cd_pair.of_restr M hR}

def of_contract_restrict (M : matroid_in α){C R : set α} (hC : C ⊆ M.E) (hR : R ⊆ M.E \ C) : 
  minor_pair (M / C ∣ R) M :=
⟨ cd_pair.of_con_restr M hC hR,  
  by {rw [matroid_in.restrict, del_eq_del_inter_E _ Rᶜ], 
      congr' 1, simp [←inter_assoc, cd_pair.of_con_restr, diff_eq]}⟩ 

def choose_minor_pair (h : is_minor N M) : minor_pair N M := 
  classical.choice (h)

lemma minor_pair_to_is_minor : 
  minor_pair N M → is_minor N M :=
nonempty.intro

lemma NE_ss_ME (p : minor_pair N M) :
  N.E ⊆ M.E :=
by {rw ←p.minor, intro x, simp, tauto}

@[simp, msimp] lemma NE_inter_D (p : minor_pair N M) :
  N.E ∩ p.D = ∅ :=
by {simp only [←p.minor, diff_eq] with msimp, rw inter_assoc, simp,}

@[simp, msimp] lemma D_inter_NE (p : minor_pair N M) :
  p.D ∩ N.E = ∅ :=
by rw [inter_comm, NE_inter_D]

lemma NE_disj_D (p : minor_pair N M) :
  disjoint N.E p.D :=
by {rw disjoint_iff_inter_eq_empty, apply NE_inter_D}

@[simp, msimp] lemma NE_inter_C (p : minor_pair N M) :
  N.E ∩ p.C = ∅ :=
by {simp only [←p.minor, diff_eq] with msimp, rw [inter_right_comm, inter_comm, inter_assoc M.E], simp,}

@[simp, msimp] lemma C_inter_NE (p : minor_pair N M) :
  p.C ∩ N.E = ∅ :=
by rw [inter_comm, NE_inter_C]


lemma NE_disj_C (p : minor_pair N M) :
  disjoint N.E p.C :=
by {rw disjoint_iff_inter_eq_empty, apply NE_inter_C}

lemma C_union_D_ss_E (p : minor_pair N M) : 
  p.C ∪ p.D ⊆ M.E := 
union_subset p.C_ss_E p.D_ss_E

/-- converts a minor pair C D for N M to the minor pair D C for N* M*-/
def to_dual (p : minor_pair N M) : minor_pair N.dual M.dual := 
{ minor := by {simpa [←p.minor_eq, cd_pair.switch] using (dual_con_del M p.disj).symm,}, 
  ..((p : cd_pair M).switch) }
  
/-- converts a minor pair C D for N* M* to the minor pair D C for N M-/
def of_dual (p : minor_pair N.dual M.dual) : minor_pair N M := 
{ minor := by {conv_rhs {rw [←dual_dual N, ←p.minor]}, rw [dual_con_del _ (p.disj), dual_dual], refl, }, 
  .. ((p : cd_pair M.dual).of_eq_E (rfl : M.E = M.dual.E)).switch }

/-- natural bijection between minor pairs and dual minor pairs -/
def dual_equiv : minor_pair N M ≃ minor_pair N.dual M.dual := 
{ to_fun := to_dual,
  inv_fun := of_dual,
  left_inv := λ x, by { ext : 2; {simpa [of_dual, to_dual, cd_pair.switch]}},
  right_inv := λ x, by { ext : 2; {simpa [of_dual, to_dual, cd_pair.switch]}} } 

@[simp, msimp] lemma dual_equiv_C (p : minor_pair N M) : (dual_equiv p).C = p.D := rfl  
@[simp, msimp] lemma dual_equiv_D (p : minor_pair N M) : (dual_equiv p).D = p.C := rfl 
@[simp, msimp] lemma dual_equiv_inv_C (p : minor_pair N.dual M.dual) : (dual_equiv.inv_fun p).C = p.D := rfl 
@[simp, msimp] lemma dual_equiv_inv_D (p : minor_pair N.dual M.dual) : (dual_equiv.inv_fun p).D = p.C := rfl 

lemma rank (p : minor_pair N M) (X : set α) (hX : X ⊆ N.E) :
  N.r X = M.r (X ∪ p.C) - M.r p.C := 
begin
  simp only [←p.minor] with msimp,  congr', 
  refine subset_iff_inter_eq_left.mp (subset.trans hX _),
  exact subset_compl_iff_disjoint.mpr (p.NE_inter_D),  
end

lemma rank_subtype (p : minor_pair N M) (X : set N.E) :
  N.r ↑X = M.r (↑X ∪ p.C) - M.r p.C := 
by {rw rank, rintro x hx, obtain ⟨⟨x,h⟩,-,rfl⟩ := (mem_image _ _ _).mp hx, exact h, }

/-- given minor pairs for M₁ M₂ and M₂ M₃, constructs a minor pair for M₁ M₃ -/
def trans {M₁ M₂ M₃ : matroid_in α} (p₁₂ : minor_pair M₁ M₂) (p₂₃ : minor_pair M₂ M₃) : minor_pair M₁ M₃ := 
have h₁ : p₁₂.C ∩ p₂₃.D = ∅ := disjoint_of_subset_left' p₁₂.C_ss_E p₂₃.NE_inter_D,
have h₂ : p₂₃.C ∩ p₁₂.D = ∅ := disjoint_of_subset_right' p₁₂.D_ss_E p₂₃.C_inter_NE, 
{ C := p₁₂.C ∪ p₂₃.C,
  D := p₁₂.D ∪ p₂₃.D,
  disj := by simp_rw [inter_distrib_left, inter_distrib_right, h₁, h₂, p₁₂.disj, p₂₃.disj, union_self],
  C_ss_E := union_subset (subset.trans p₁₂.C_ss_E p₂₃.NE_ss_ME) (p₂₃.C_ss_E),
  D_ss_E := union_subset (subset.trans p₁₂.D_ss_E p₂₃.NE_ss_ME) (p₂₃.D_ss_E),
  minor := by {
    simp only [←p₁₂.minor, ←p₂₃.minor], 
    rw [union_comm p₁₂.C, union_comm p₁₂.D, ←del_del, ←con_con, con_del_eq_del_con _ _ _ h₁], }}


/-- given a minor pair C,D and a subset of C whose removal doesn't drop the rank of C, moves 
    that subset to D -/
def move_to_delete (p : minor_pair N M){A : set α}
(h₁ : A ⊆ p.C) (h₂ : M.r (p.C \ A) = M.r p.C) : minor_pair N M := 
let p' : cd_pair M := {
  C := p.C \ A,
  D := p.D ∪ A,
  disj := by {rw [diff_eq, inter_distrib_left, inter_right_comm, p.disj, inter_assoc],simp,},
  C_ss_E := subset.trans (diff_subset _ _) p.C_ss_E,
  D_ss_E := union_subset (p.D_ss_E) (subset.trans h₁ p.C_ss_E),} in 
{ minor := begin
    ext, simp [← p.minor] with msimp, tauto,
    intros X hX, rw p.rank X _, swap, 
    {simp only [←p.minor, diff_diff, pair_move _ h₁] with msimp at ⊢ hX, exact hX},
    rw cd_pair.rank _ _ hX,  
    simp only [h₂], 
    congr' 1, exact rank_eq_of_union_rank_diff_eq X h₂, 
  end, ..p' } 

/-- given a minor pair C,D and a subset of D that is spanned by C, moves that subset to C -/
def move_to_contract (p : minor_pair N M){A : set α}
(h₁ : A ⊆ p.D) (h₂ : M.r (p.C ∪ A) = M.r p.C) : minor_pair N M :=
let p' : cd_pair M := {
  C := p.C ∪ A,
  D := p.D \ A,
  disj := by {rw [diff_eq, inter_distrib_right, ←inter_assoc, p.disj, inter_comm p.D, ←inter_assoc], simp,},
  D_ss_E := subset.trans (diff_subset _ _) p.D_ss_E,
  C_ss_E := union_subset (p.C_ss_E) (subset.trans h₁ p.D_ss_E)} in 
{ minor := begin
    ext, simp [← p.minor] with msimp, tauto, 
    intros X hX, rw p.rank X _, swap, 
    {simp only [←p.minor, diff_diff, union_comm (p.C ∪ A) , pair_move _ h₁]
       with msimp at hX ⊢, rwa [union_comm], },
    simp only [h₂] with msimp, congr' 1, 
    have h := rank_eq_of_union_eq_rank_subset _ (subset_union_left p.C A) h₂.symm,
    simp_rw [r_carrier_eq_r, union_comm (p.C ∪ A)] at h, rw [← h, union_comm], congr' 2,
    simp only with msimp at hX, rw [←disjoint_iff_diff_eq_left], 
    exact disjoint_of_subset_left' hX (diff_inter_right_eq_empty _ _), 
  end .. p' }

/-- A minor pair C D with C dependent doesn't maximize r C + r* D -/
lemma suboptimal_goodness {N M : matroid_in α} (p : minor_pair N M) (hdep : ¬is_indep M p.C) : 
∃ p': minor_pair N M, M.r p.C + M.dual.r p.D < M.r p'.C + M.dual.r p'.D :=
begin
  simp_rw [indep_iff_carrier, not_indep_iff_exists_removal, r_carrier_eq_r, ←singleton_subset_iff] at hdep, 
  rcases hdep with ⟨e,heC, he⟩, 
  use p.move_to_delete heC he, 
  rw [minor_pair.move_to_delete], dsimp only, rw [he, dual_r], 
  simp only [diff_eq, matroid_in.dual_r, set.compl_union, sub_lt_sub_iff_right, add_lt_add_iff_left], 

  have h : size ((p.D ∪ {e}) ∩ M.E) = size (p.D ∩ M.E) + 1, 
  { rw [inter_distrib_right, subset_iff_inter_eq_left.mp (subset.trans heC p.C_ss_E)], 
    apply size_union_nonmem_singleton, 
    by_contra hn, 
    rw singleton_subset_iff at heC, 
    have := eq_empty_iff_forall_not_mem.mp p.disj e,   
    simp only [set.mem_inter_eq] at this hn,
    tauto, },
  rw h, 
  apply (λ x y y' h', by {rw [add_right_comm, add_assoc],simp only [add_lt_add_iff_left, int.lt_add_one_iff, h'],} : 
  ∀ (x y y' : ℤ), y ≤ y' → x + y < x + 1 + y'), 
  simp_rw [←r_eq_inter_r], 
  have hCD : p.C ∪ p.Dᶜ = p.Dᶜ := subset_iff_union_eq_left.mp (by {rw subset_compl_iff_disjoint, exact p.disj}),
  have h' := (rank_eq_of_union_eq_rank_subset (p.Dᶜ ∩ {e}ᶜ) (by simp) he).symm,  
  
  convert (has_le.le.trans_eq (eq.le _) h'), 
  { rw [diff_eq, ←inter_distrib_right, hCD], }, 
  convert rfl,
  rw [union_distrib_left, hCD, ←subset_iff_inter_eq_left],   
  convert subset_univ _, 
  rwa [←compl_subset_iff_union, ←compl_subset_compl.symm],
end

/-- each minor can be represented by a indep/coindep contract_delete pair -/
lemma minor_has_indep_coindep_pair {N M : matroid_in α} (h_minor : is_minor N M) :
   ∃ (p : minor_pair N M), (M.is_indep p.C) ∧ (M.dual.is_indep p.D) := 
begin
  letI : nonempty _ := h_minor, 
  
  /- take a minor pair (C,D) maximizing r C + r* D-/
  rcases max_spec (λ (p : minor_pair N M), M.r p.C + M.dual.r p.D) with ⟨p,⟨h,h'⟩⟩,
  use p, by_contra hn, rw not_and_distrib at hn, cases hn, 

  /- C is independent because otherwise we could improve C D  -/
  { rcases suboptimal_goodness p hn with ⟨p',hp'⟩, have := h' p', dsimp only at this, linarith,},
  
  /- D is coindependent by the dual argument -/
  rcases suboptimal_goodness (minor_pair.dual_equiv p) hn with ⟨p', hp'⟩, 
  specialize h' (minor_pair.dual_equiv.inv_fun p'), 
  simp only with msimp at h' hp',  
  linarith, 
end

/-- each minor N has a minor pair (C,D) with C independent and of size r M - r N. (Latter condition 
is equivalent to the coindependence of D in M) -/
lemma minor_has_indep_coindep_pair' {N M : matroid_in α} (h_minor : is_minor N M) :
   ∃ (p : minor_pair N M), M.is_indep p.C ∧ size p.C = M.r M.E - N.r N.E := 
begin
  rcases minor_has_indep_coindep_pair h_minor with ⟨p,hC,hD⟩, 
  refine ⟨p,hC,_⟩, 
  rw indep_iff_r at hC, 
  simp_rw [←p.minor], 
  have : (M / p.C).dual.is_indep p.D,
  { rw [coindep_contract_iff, inter_comm], exact ⟨p.disj, hD⟩},
  rw [delete_coindep_rank_ground (M / p.C) this, con_rank_ground],
  linarith, 
end

end minor_pair 


lemma con_del_is_minor (M : matroid_in α) (C D : set α) :
  (M / C \ D).is_minor M :=
⟨to_minor_pair M C D⟩  

lemma con_restr_is_minor (M : matroid_in α) (C R : set α) : 
  (M / C ∣ R).is_minor M := 
con_del_is_minor _ _ _ 

lemma minor_iff_dual_minor {M N : matroid_in α} :
  N.is_minor M ↔ N.dual.is_minor M.dual := 
begin
  repeat {rw ←minor_pair.nonempty_iff}, 
  refine ⟨λ a, _, λ a, _⟩, 
  cases a, apply nonempty.intro (a.to_dual),
  cases a, apply nonempty.intro (a.of_dual), 
end

lemma del_con_is_minor (M : matroid_in α) (C D : set α) :
   (M \ D / C).is_minor M :=
by {rw [del_con_eq_con_del'], apply con_del_is_minor,  }

lemma dual_minor_of_minor {M N : matroid_in α} : 
  N.is_minor M → N.dual.is_minor M.dual :=
minor_iff_dual_minor.mp 

lemma deletion_is_restriction (M : matroid_in α) (D : set α) :
  (M \ D).is_restriction M := 
by {nth_rewrite 0 ←con_empty M, refine ⟨to_minor_pair M ∅ D, by simp [to_minor_pair]⟩} 

lemma restriction_to_is_restriction (M : matroid_in α) (R : set α) : 
  (M ∣ R).is_restriction M := 
deletion_is_restriction M Rᶜ 

lemma contraction_is_contraction_minor (M : matroid_in α) (C : set α) :
  (M / C).is_contraction_minor M := 
by {rw ←del_empty (M / C), refine ⟨to_minor_pair M C ∅, by simp [to_minor_pair]⟩} 

lemma restriction_is_minor (N M : matroid_in α) : 
  N.is_restriction M → N.is_minor M := 
by {rintros ⟨h,-⟩, exact ⟨h⟩}

lemma contraction_minor_is_minor (N M : matroid_in α) : 
  N.is_contraction_minor M → N.is_minor M := 
by {rintros ⟨h,-⟩, exact ⟨h⟩}

lemma minor_antisymm: 
  anti_symmetric (@is_minor α _) := 
begin
  rintros M₁ M₂ ⟨p₁⟩ ⟨p₂⟩, --rw is_minor at h₁ h₂, 
  have := p₁.minor, simp_rw ←p₂.minor at this ⊢,   
  have h := congr_arg E this, simp only [diff_eq] with msimp at h, 
  repeat {rw [inter_assoc] at h}, 
  repeat {rw [←compl_union] at h}, 
  repeat {rw [←union_assoc] at h}, 
  rw [←subset_iff_inter_eq_left] at h, 
  have hC : p₂.C = ∅, 
  { refine empty_of_subset_compl (subset.trans p₂.C_ss_E (subset.trans h _)), 
    intro x, simp, tauto,  },
  have hD : p₂.D = ∅, 
  { refine empty_of_subset_compl (subset.trans p₂.D_ss_E (subset.trans h _)), 
    intro x, simp, tauto,  },
  simp only [hC,hD] with msimp, 
end

lemma minor_trans: 
  transitive (@is_minor α _) :=
by {rintros M₁ M₂ M₃ ⟨p₁⟩ ⟨p₂⟩, apply nonempty.intro (p₁.trans p₂)}

lemma minor_iff_has_contract {N M : matroid_in α} :
  N.is_minor M ↔ N.E ⊆ M.E ∧ ∃ C ⊆ M.E \ N.E, ∀ X ⊆ N.E, N.r X = M.r (X ∪ C) - M.r C := 
begin
  split, 
  { rintro ⟨⟨C,D,disj,hC,hD⟩,rfl⟩, simp only with msimp, 
    refine ⟨by {rw [diff_diff], apply diff_subset }, ⟨C,⟨_, λ X hX, _⟩⟩⟩,
    { simp only [diff_diff, diff_self_diff] with msimp,  
      exact subset_inter hC (subset_union_left _ _), }, 
    congr', exact diff_eq_self_of_subset_diff hX, },
  rintro ⟨hE, C, hC, hr⟩, 
  refine ⟨⟨⟨C,M.E \ (N.E ∪ C),_,subset.trans hC (diff_subset _ _ ),diff_subset _ _⟩,_⟩⟩, 
  { rw ←diff_diff, apply inter_diff_self, }, 
  have h: M.E \ C \ (M.E \ (N.E ∪ C)) = N.E, 
  { ext x, specialize @hC x, specialize @hE x, simp at *, tauto},
  ext : 1, simpa only with msimp using h,
  simp only [h] with msimp at *, 
  intros X hX, rw [hr X hX], congr', 
  { ext x, specialize @hC x, specialize @hE x, simp at *, tauto},
end

lemma con_or_del {N M : matroid_in α} {e : α} (h : is_minor N M) (he : e ∈ M.E \ N.E) : 
  is_minor N (M / {e}) ∨ is_minor N (M \ {e}) :=
begin
  rw is_minor at h, rcases h with ⟨p⟩, 
  rw [← p.union, mem_union] at he, 
  rw ←p.minor, 
  cases he, 
  { rw [←union_mem_singleton he, union_comm, ←con_con], 
    let Me := matroid_in.contract M {e}, 
    exact or.inl (con_del_is_minor (M / {e}) _ _),  },
  right, rw [con_del_eq_del_con _ _ _ p.disj, ←union_mem_singleton he, union_comm, ←del_del ],
  apply del_con_is_minor,   
end

end minor 

end matroid_in 

import prelim.embed prelim.minmax set_tactic.solver
import matroid.rankfun matroid.dual .projection .matroid_in .delete_contract 

open_locale classical 
noncomputable theory

open matroid set 

namespace matroid_in

variables {U V : Type}[fintype U][fintype V]

section minor 

/-- a structure whose existence certifies that N is a minor of M -/
@[ext] structure minor_pair (N M : matroid_in U) :=
(C : set U)
(D : set U)
(disj : C ∩ D = ∅)
(union : C ∪ D = M.E \ N.E)
(minor : M / C \ D = N)


/-- minor relation on matroid_in U-/
def is_minor (N M : matroid_in U) : Prop := 
  nonempty (minor_pair N M)

def is_proper_minor (N M : matroid_in U) : Prop :=
  is_minor N M ∧ N ≠ M 

def is_restriction (N M : matroid_in U) : Prop := 
  ∃ P: minor_pair N M, P.C = ∅ 

def is_contraction_minor (N M : matroid_in U) : Prop := 
  ∃ P: minor_pair N M, P.D = ∅

/-- constructs a minor pair from contract/delete sets C and D  -/
def to_minor_pair (M : matroid_in U)(C D : set U):
  minor_pair (M / C \ D) M :=
{ C := M.E ∩ C,
  D := (M.E ∩ D) \ C,
  disj := by {ext, simp, tauto, },
  union := by {ext, simp, tauto, },
  minor := begin
    rw ←con_eq_con_inter_E, 
    nth_rewrite 1 [del_eq_del_inter_E], 
    simp [diff_eq, inter_right_comm], 
  end  }

--def restrict_to_minor_pair (M : matroid_in U)(R : set U): 


namespace minor_pair 

variables {N M : matroid_in U}


instance minor_pair_fintype : fintype (minor_pair N M) :=  
by tactic.mk_fintype_instance
/-
lemma nonempty_iff:
  nonempty (minor_pair N M) ↔ is_minor N M := 
begin
  rw [minor_iff_has_delete_contract], 
  refine ⟨λ h, _, λ h,  _ ⟩, 
  { rcases h with ⟨C,D, h, h', rfl⟩, exact ⟨C,D,h,⟨h',rfl⟩⟩,},
  rcases h with ⟨C,D, h, h', rfl⟩, exact nonempty.intro ⟨C,D,h,h',rfl⟩, 
end
-/
def choose_minor_pair (h : is_minor N M): minor_pair N M := 
  classical.choice (h)

lemma minor_pair_to_is_minor : 
  minor_pair N M → is_minor N M :=
nonempty.intro

lemma E_subset (p : minor_pair N M):
  N.E ⊆ M.E :=
by {rw ←p.minor, intro x, simp, tauto}

@[simp, msimp] lemma E_inter_D (p : minor_pair N M):
  N.E ∩ p.D = ∅ :=
by {simp only [←p.minor, diff_eq] with msimp, rw inter_assoc, simp,}

@[simp, msimp] lemma E_disj_D (p : minor_pair N M):
  disjoint N.E p.D :=
by {rw disjoint_iff_inter_eq_empty, apply E_inter_D}

@[simp, msimp] lemma E_inter_C (p : minor_pair N M):
  N.E ∩ p.C = ∅ :=
by {simp only [←p.minor, diff_eq] with msimp, rw [inter_right_comm, inter_comm, inter_assoc M.E], simp,}

@[simp, msimp] lemma E_disj_C (p : minor_pair N M):
  disjoint N.E p.C :=
by {rw disjoint_iff_inter_eq_empty, apply E_inter_C}

lemma C_ss_E (p : minor_pair N M): 
  p.C ⊆ M.E := 
by {refine subset.trans (subset_union_left p.C p.D) _, rw p.union, simp [diff_eq],  }

lemma D_ss_E (p : minor_pair N M): 
  p.D ⊆ M.E := 
by {refine subset.trans (subset_union_right p.C p.D) _, rw p.union, simp [diff_eq],  }

lemma C_union_D_ss_E (p : minor_pair N M): 
  p.C ∪ p.D ⊆ M.E := 
by simp [diff_eq, p.union]

/-- converts a minor pair C D for N M to the minor pair D C for N* M*-/
def to_dual (p : minor_pair N M) : minor_pair N.dual M.dual := 
⟨  p.D, 
   p.C,
   by {rwa [inter_comm, p.disj]}, 
   by {rw [union_comm, p.union], simp}, 
   by {rw [←dual_con_del _ p.disj], simp_rw p.minor, }⟩ 
  
/-- converts a minor pair C D for N* M* to the minor pair D C for N M-/
def of_dual (p : minor_pair N.dual M.dual) : minor_pair N M := 
⟨ (to_dual p).C,
  (to_dual p).D, 
  (to_dual p).disj, 
  (to_dual p).union, 
  by {have := (to_dual p).minor, simp only [matroid_in.dual_dual] at this, assumption, }⟩

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

lemma rank (p : minor_pair N M)(X : set U)(hX : X ⊆ N.E):
  N.r X = M.r (X ∪ p.C) - M.r p.C := 
begin
  simp only [←p.minor] with msimp,  congr', 
  refine subset_iff_inter_eq_left.mp (subset.trans hX _),
  exact subset_compl_iff_disjoint.mpr (p.E_inter_D),  
end

/-- given minor pairs for M₁ M₂ and M₂ M₃, constructs a minor pair for M₁ M₃ -/
def trans {M₁ M₂ M₃ : matroid_in U}(p₁ : minor_pair M₁ M₂)(p₂ : minor_pair M₂ M₃) : minor_pair M₁ M₃ := 
let h₁ : p₁.C ∩ p₂.D = ∅ := disjoint_of_subset_left' p₁.C_ss_E (by simp), 
    h₂ : p₂.C ∩ p₁.D = ∅ := disjoint_of_subset_right' p₁.D_ss_E (by {rw inter_comm, simp}) in 
{ C := p₁.C ∪ p₂.C,
  D := p₁.D ∪ p₂.D,
  disj := by 
  {rw [inter_distrib_left, inter_distrib_right, inter_distrib_right, p₁.disj, p₂.disj, h₁, h₂], simp},  
  union := begin
    rw [(_ : M₃.E \ M₁.E = (M₃.E \ M₂.E) ∪ (M₂.E \ M₁.E)), ←p₁.union, ←p₂.union],
    ext, simp, tauto, 
    have := p₁.E_subset,
    have := p₂.E_subset, 
    ext, simp, tauto,  
  end,
  minor := begin
    simp_rw [←p₁.minor, ←p₂.minor],
    ext, {simp, tauto,}, 
    intros X hX, 
    simp only [diff_eq] with msimp, 
    rw (λ x y z, by linarith : ∀ x y z : ℤ, x-y - (z-y) = x-z),  
    rw [inter_distrib_right, inter_assoc, compl_union, union_assoc],
    congr' 2, 
    all_goals {convert rfl, rw [←subset_iff_inter_eq_left, subset_compl_iff_disjoint], exact h₁, },
  end }

/-- given a minor pair C,D and a subset of C whose removal doesn't drop the rank of C, moves 
    that subset to D -/
def move_to_delete (p : minor_pair N M){A : set U}
(h₁ : A ⊆ p.C) (h₂ : M.r (p.C \ A) = M.r p.C) : minor_pair N M := 
{ C := p.C \ A,
  D := p.D ∪ A,
  disj := by {have := p.disj, ext, simp at *, rw ←subset_compl_iff_disjoint at this, tauto ,  },
  union := by {rw ←p.union, ext, simp at *,tauto,  },
  minor := begin
    have := p.minor, simp_rw ← this, clear this, 
    ext, {simp at *, tauto, },
    
    intros X hX, repeat {rw r_eq_r_inter _ X}, rw diff_eq at h₂,  
    rw (by rw p.minor : ((M / p.C) \ p.D).E = N.E) at *, 
    rw (by {simp_rw ←p.minor, ext, simp [compl_inter], tauto,} :
      ((M / (p.C \ A)) \ (p.D ∪ A)).E = N.E) at *, 
    
    simp only [compl_union, h₂, sub_left_inj, union_comm _ (p.C ∩ Aᶜ), 
               diff_eq, union_comm _ p.C] with msimp, 
    
    suffices : X ∩ N.E ∩ p.Dᶜ = X ∩ N.E ∩ (p.Dᶜ ∩ Aᶜ), 
    { rw this, apply rank_eq_of_union_eq_rank_subset, apply inter_subset_left, exact h₂, }, 
    suffices : N.E ∩ Aᶜ = N.E, 
    { rw ←this, ext, simp, tauto, }, 
    rw [←subset_iff_inter_eq_left, subset_compl_iff_disjoint, ←disjoint_iff_inter_eq_empty], 
    exact disjoint_of_subset_right h₁ (E_disj_C p), 
  end } 

/-- given a minor pair C,D and a subset of D that is spanned by C, moves that subset to C -/
def move_to_contract (p : minor_pair N M){A : set U}
(h₁ : A ⊆ p.D)(h₂ : M.r (p.C ∪ A) = M.r p.C) : minor_pair N M :=
{ C := p.C ∪ A, 
  D := p.D \ A, 
  disj := by {have := p.disj, ext, simp at *, rw ←subset_compl_iff_disjoint at this, tauto ,  },
  union := by {rw ←p.union, ext, simp at *,tauto,  },
  minor := begin
    have := p.minor, simp_rw ← this, clear this, 
    ext, {simp at *, tauto, },
    
    intros X hX, repeat {rw r_eq_r_inter _ X}, 
    rw (by rw p.minor : ((M / p.C) \ p.D).E = N.E) at *, 
    rw (by {simp_rw ←p.minor, ext, simp [compl_inter], tauto,} :
      ((M / (p.C ∪ A)) \ (p.D \ A)).E = N.E) at *, 
    
    simp only [h₂, sub_left_inj, diff_eq] with msimp at ⊢ hX, 
    rw [union_comm, union_comm _ p.C, eq_comm], 
    suffices : X ∩ N.E ∩ p.Dᶜ = X ∩ N.E ∩ (p.D ∩ Aᶜ)ᶜ, 
    { rw this, apply rank_eq_of_union_eq_rank_subset, apply subset_union_left, exact h₂.symm,},
    rw [compl_inter, inter_distrib_left, inter_assoc _ _ Aᶜᶜ],
    suffices : N.E ∩ Aᶜᶜ = ∅, rw this, simp, 
    rw [compl_compl, ←disjoint_iff_inter_eq_empty], 
    exact disjoint_of_subset_right h₁ (E_disj_D p), 
  end }

/-- A minor pair C D with C dependent doesn't maximize r C + r* D -/
lemma suboptimal_goodness {N M : matroid_in U}(p : minor_pair N M)(hdep : ¬is_indep M p.C): 
∃ p': minor_pair N M, M.r p.C + M.dual.r p.D < M.r p'.C + M.dual.r p'.D :=
begin
  simp_rw [indep_iff_carrier, not_indep_iff_exists_removal, r_carrier_eq_r, ←singleton_subset_iff] at hdep, 
  rcases hdep with ⟨e,heC, he⟩, 
  use p.move_to_delete heC he, 
  rw [minor_pair.move_to_delete], dsimp only, rw [he, dual_r], 
  simp only [diff_eq, matroid_in.dual_r, set.compl_union, sub_lt_sub_iff_right, add_lt_add_iff_left], 

  have h : size ((p.D ∪ {e}) ∩ M.E) = size (p.D ∩ M.E) + 1, 
  { rw [inter_distrib_right, subset_iff_inter_eq_left.mp (subset.trans heC p.C_ss_E)], 
    apply size_insert_nonmem, 
    by_contra hn, 
    rw singleton_subset_iff at heC, 
    have := eq_empty_iff_forall_not_mem.mp p.disj e,   
    simp only [set.mem_inter_eq] at this hn,
    tauto, },
  rw h, 
  apply (λ x y y' h', by {rw [add_right_comm, add_assoc],simp only [add_lt_add_iff_left, int.lt_add_one_iff, h'],}: 
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
lemma minor_has_indep_coindep_pair {N M : matroid_in U}(h_minor : is_minor N M):
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
lemma minor_has_indep_coindep_pair' {N M : matroid_in U}(h_minor : is_minor N M):
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

-- The next few definitions relate a minor pair N M to a minor pair N' M.as_mat 

--def C_as_subtype (P : minor_pair N M) : set (M.E) := coe ⁻¹' P.C 
--def D_as_subtype (P : minor_pair N M) : set (M.E) := coe ⁻¹' P.D 

--def E_as_subtype (P : minor_pair N M) : set (M.E) := coe ⁻¹' N.E 

/-lemma E_inter_C_subtype (P : minor_pair N M) : 
  (coe ⁻¹' P.C : set M.E) ∩ (coe ⁻¹' N.E : set M.E) = ∅ := 
begin

end-/

def subset_pair_equiv {X Y : set U}(h : X ⊆ Y) :=
  equiv.set.range 
    (λ (x : X), (⟨x.val, mem_of_mem_of_subset x.property h⟩ : Y))
    (λ x y hxy, by {cases x, cases y, dsimp at hxy, rwa subtype.mk_eq_mk at *,  })


@[simp] lemma subset_pair_equiv_apply {X Y : set U}(h : X ⊆ Y)(x : X) :
  subset_pair_equiv h x = ⟨⟨x.val, mem_of_mem_of_subset x.property h⟩, mem_range_self x⟩ := 
rfl 

def subtype_equiv (P : minor_pair N M) := subset_pair_equiv P.E_subset

@[simp] lemma subtype_equiv_apply (P : minor_pair N M )(x : N.E): 
  P.subtype_equiv x = ⟨⟨x.val, mem_of_mem_of_subset x.property P.E_subset⟩, mem_range_self x⟩  := 
rfl 


#check subtype_equiv 

def foo_iso (P : minor_pair N M): 
  N.isom ((M.as_mat : matroid_in M.E) / (coe ⁻¹' P.C) \ (coe ⁻¹' P.D)) := 
⟨ P.subtype_equiv.trans (equiv.set.of_eq begin
    simp only with msimp,
    ext, cases x with x hx, 
    simp only [exists_prop, set_coe.exists, mem_range, exists_eq_right, 
    mem_preimage, mem_diff, subtype.coe_mk, univ_diff, mem_compl_eq], 
    rw [←not_iff_not, decidable.not_and_distrib, not_not, not_not, 
    ←mem_union, P.union, mem_diff], tauto, end ), 
  λ X, begin
    simp only with msimp, rw P.rank, swap, 
      {intros x hx, unfold_coes at hx,  
      obtain ⟨⟨y,hy⟩,-,rfl⟩ := (mem_image _ _ _).mp hx, exact hy,},
    congr, swap, unfold_coes, 
    rw [image_preimage_eq_of_subset], 
    rw [subtype.range_val], exact P.C_ss_E, 
    unfold_coes, 
    rw [image_union, image_diff, image_preimage_eq_of_subset, image_preimage_eq_of_subset],
    rotate, 
    { rw [subtype.range_val], exact P.C_ss_E}, 
    { rw [subtype.range_val], exact P.D_ss_E},
    { exact subtype.val_injective}, 
    ext, rw [mem_union, mem_diff], conv
    { to_lhs, congr, congr, rw mem_image, congr, funext, rw mem_image, 
      conv {congr, congr, funext, rw mem_image, },},
     simp, split, 
     rintro (⟨⟨x, hx, ⟨x',⟨hx'C,hx'D⟩,⟨⟨hxN,hxX⟩,hx'X, rfl⟩⟩, rfl⟩, hxD⟩ | hxC), 
     { left, exact ⟨hxN, hxX⟩}, {right, assumption}, 
     rintro (⟨hxE, hxX⟩ | hxC), swap, right, assumption, left, 
     have hxM := mem_of_mem_of_subset hxE P.E_subset, 
     have hxC : x ∉ P.C := nonmem_of_mem_disjoint hxE P.E_inter_C, 
     have hxD : x ∉ P.D := nonmem_of_mem_disjoint hxE P.E_inter_D, 
     refine ⟨⟨x,⟨_,⟨x,⟨⟨_,_⟩,⟨⟨hxE,_⟩,⟨_,rfl⟩⟩⟩⟩,rfl⟩⟩,_⟩; 
     assumption, 
    end⟩ 

  
end minor_pair 

/-
/- the image of a minor of M under an isomorphism of M to M' -/
def image_minor {N M : matroid_in U}{M' : matroid_in V}
(i : isom M M')(P : minor_pair N M) : 
  matroid_in V := 
(M' / (i.equiv '' P.C_as_subtype) \ (i.equiv '' P.D_as_subtype))

def foo (α : Type)(X Y : set α)(Z : set X)(h : coe '' Z = Y):
  Z ≃ Y :=
{ to_fun := λ z, ⟨z.val, by {simp [←h]}⟩ ,
  inv_fun := λ y, ⟨⟨y.val, 
    by {cases y with y hy, 
        dsimp only, 
        rw [←h, mem_image] at hy, 
        obtain ⟨x, ⟨hx, rfl⟩⟩ := hy, 
        exact x.property,  }⟩, 
    by {cases y with y hy, 
        rw [←h, mem_image] at hy,
        obtain ⟨x, ⟨hx,rfl⟩⟩ := hy, 
        simpa,  }⟩,
  left_inv := λ x, by simp ,
  right_inv := λ y, by simp, }


lemma isom_foo {N M : matroid_in U}(P : minor_pair N M):
  N.isom ((M.as_mat : matroid_in M.E) / (P.C_as_subtype) \ P.D_as_subtype) := 
⟨P.subtype_equiv, by {sorry}⟩  
  
/- the image of a minor under an isomorphism is isomorphic to the minor. The main difficulty in the
(horrible) proof is showing that the invisible equivalence is well-defined. There might be a nicer \
way to do it by chaining equivalences, but this works. -/
lemma image_minor_iso_minor {N M : matroid_in U}{M' : matroid_in V}
(i : isom M M')(P : minor_pair N M) :
  isom N (image_minor i P) := 
{ equiv := 
  { to_fun := λ x, 
    ⟨i.equiv ⟨x, P.E_subset x.2⟩, begin
      simp only [image_minor], unfold_coes, 
      simp only [minor_pair.C_as_subtype, minor_pair.D_as_subtype,
      elem_inter_iff, mem_diff] with msimp,
      refine ⟨⟨_,by_contra (λ hn, _)⟩,(by_contra (λ hn,_))⟩, 
      { exact (i.equiv.to_fun ⟨x.val, _⟩).property, },
      all_goals { cases x with x hx,
        simp only [not_exists, mem_image, equiv.to_fun_as_coe, exists_prop, 
        equiv.apply_eq_iff_eq, set_coe.exists, not_and, subtype.coe_prop, exists_and_distrib_right,
        not_not, subtype.mk_eq_mk, exists_eq_right, mem_preimage, exists_and_distrib_left,
        exists_prop_of_true, subtype.coe_eta, subtype.coe_mk, not_forall, subtype.val_eq_coe] at hn, 
        obtain ⟨y, hy, hy', rfl⟩ := hn, 
        have hy'' := mem_inter hx hy',
        try {rw P.E_inter_C at hy''}, 
        try {rw P.E_inter_D at hy''},
        exact not_mem_empty _ hy''},
    end⟩, 
    inv_fun := λ y, 
      ⟨i.equiv.inv_fun ⟨y,by 
        {cases y with y hy, rw subtype.coe_mk, 
        simp only [image_minor, mem_diff] with msimp at hy, 
        tauto}⟩, 
        begin 
          cases y with y hy,
          simp only [image_minor, mem_diff] with msimp at hy,
          rcases hy with ⟨⟨hyE', hC⟩, hD⟩,
          set x := (i.equiv.inv_fun ⟨y, hyE'⟩) with hx,
          suffices :  x.val  ∈ N.E, exact this, 
          unfold_coes at hC hD, simp only [not_exists, mem_image, 
          equiv.to_fun_as_coe, set_coe.exists, exists_and_distrib_right, 
          exists_eq_right, subtype.coe_mk, minor_pair.C_as_subtype, minor_pair.D_as_subtype] at hC hD, 
          specialize hC hyE', specialize hD hyE', push_neg at hC hD,  
          specialize hC x.val x.property,
          specialize hD x.val x.property, 
          
          rw [mem_preimage, subtype.coe_mk] at hC hD, push_neg at hC hD,  
          by_contra hn, 
          have hx' := (mem_diff _).mpr ⟨x.property, hn⟩, 
          rw [←P.union, mem_union] at hx', 
          rcases hx' with (hxC | hxD), 
          { specialize hC hxC, rw hx at hC, simp at hC, exact hC },
          { specialize hD hxD, rw hx at hD, simp at hD, exact hD },
      end⟩, 
    left_inv := λ x, by simp,
    right_inv := λ y, by simp },
  on_rank := begin
    
    intro X, 
    --have hr := i.on_rank, simp only  with msimp at hr, --unfold_coes at hr, 
    --have hr' : ∀ (Y : set V), M'.r Y = M'. 
    
    /-simp only [image_minor] with msimp, unfold_coes, 
    conv {to_lhs, congr, congr, skip, congr, congr, dsimp},
    unfold_coes, 
    conv {to_lhs, congr, congr, skip, congr, congr, dsimp,  }, -/
    

    simp only [not_exists, mem_image, equiv.to_fun_as_coe, exists_prop, con_E,
      equiv.apply_eq_iff_eq, equiv.coe_fn_mk, set_coe.exists, not_and, subtype.coe_prop, 
      exists_and_distrib_right, equiv.symm_apply_apply, not_not, eq_self_iff_true, 
      minor_pair.E_inter_C, not_true, equiv.apply_symm_apply, subtype.mk_eq_mk, exists_eq_right,
      mem_preimage, exists_and_distrib_left, exists_prop_of_true, ne.def, mem_diff, 
      subtype.coe_eta, minor_pair.E_inter_D,  subtype.coe_mk, del_E, not_forall, subtype.val_eq_coe,
      equiv.inv_fun_as_coe, image_minor, minor_pair.D_as_subtype, minor_pair.C_as_subtype] 
      with msimp,
    have hr := i.on_rank, simp only  with msimp at hr, 
    have hr' := i.symm.on_rank, simp only with msimp at hr', 
    rw [P.rank],  congr' 1,  swap,
    { rw hr, 
      unfold_coes, 
      rw [image_preimage_eq_of_subset], 
      rw [subtype.range_val], 
      apply minor_pair.C_ss_E, }, swap, 
    { unfold_coes, intro x, rw mem_image, rintros ⟨⟨y,hy⟩,-, rfl⟩, exact hy, },
    set f : N.E → M.E := λ x, ⟨x.val, mem_of_mem_of_subset x.property P.E_subset⟩ with hf, 
    
    have h : (↑X ∪ P.C) = ↑(f '' X ∪ P.C_as_subtype), sorry, 
    rw [h, ←hr], congr', 
    unfold_coes, 
    --unfold_coes, simp [minor_pair.C_as_subtype, minor_pair.D_as_subtype, hf, image_minor] 
    
    --{ }, 
    
    

  end
   }
/-⟨ (equiv.subtype_subtype_equiv_subtype (P.E_subset)).symm.trans 
  (by {refine (equiv.set.image i.equiv _ (equiv.injective _)).trans _, 
    apply foo, ext, simp [image_minor, minor_pair.C_as_subtype, minor_pair.D_as_subtype], tidy,  }),


  
  (equiv.set.of_eq (by {})), }, 
  by {}⟩ -/
--equiv.set.image N.E 


/-- given a minor pair N,M, an isomorphism from M to M' maps it to a minor pair N',M' -/
def image_minor_pair {N M : matroid_in U}{M' : matroid_in V}
(i : isom M M')(P : minor_pair N M): 
  minor_pair (image_minor i P) M' := 
 {  C := (i.equiv '' P.C_as_subtype : set M'.E),
    D := (i.equiv '' P.D_as_subtype : set M'.E),
    disj := begin
      unfold_coes, 
      repeat {rw [image_inter, image_eq_empty]}, 
      rw [minor_pair.C_as_subtype, minor_pair.D_as_subtype, ←preimage_inter, P.disj, preimage_empty],
      apply equiv.injective, apply subtype.val_injective, 
    end,
    union := begin
      simp only [image_minor], unfold_coes, 
      simp only [del_E, con_E, subtype.val_eq_coe, diff_diff, diff_self_diff], 
      rw [eq_comm, ←subset_iff_inter_eq_right, ←image_union, ←image_union],  
      refine subset.trans (image_subset_range _ _) _, 
      intro x, rw mem_range, rintros ⟨⟨y,hy⟩,rfl⟩, exact hy,  
    end,
    minor := rfl }


--def iso_of_minor_pair {N M : matroid_in U}{M : matroid_in V}

-/


lemma con_del_is_minor (M : matroid_in U)(C D : set U):
  (M / C \ D).is_minor M :=
⟨to_minor_pair M C D⟩  

lemma con_restr_is_minor (M : matroid_in U)(C R : set U): 
  (M / C ∣ R).is_minor M := 
con_del_is_minor _ _ _ 

lemma minor_iff_dual_minor {M N : matroid_in U}:
  N.is_minor M ↔ N.dual.is_minor M.dual := 
begin
  repeat {rw ←minor_pair.nonempty_iff}, 
  refine ⟨λ a, _, λ a, _⟩, 
  cases a, apply nonempty.intro (a.to_dual),
  cases a, apply nonempty.intro (a.of_dual), 
end

lemma del_con_is_minor (M : matroid_in U)(C D : set U):
   (M \ D / C).is_minor M :=
by {rw [del_con_eq_con_del'], apply con_del_is_minor,  }

lemma dual_minor_of_minor {M N : matroid_in U}: 
  N.is_minor M → N.dual.is_minor M.dual :=
minor_iff_dual_minor.mp 

lemma deletion_is_restriction (M : matroid_in U)(D : set U):
  (M \ D).is_restriction M := 
by {nth_rewrite 0 ←con_empty M, refine ⟨to_minor_pair M ∅ D, by simp [to_minor_pair]⟩} 

lemma restriction_to_is_restriction (M : matroid_in U)(R : set U): 
  (M ∣ R).is_restriction M := 
deletion_is_restriction M Rᶜ 

lemma contraction_is_contraction_minor (M : matroid_in U)(C : set U):
  (M / C).is_contraction_minor M := 
by {rw ←del_empty (M / C), refine ⟨to_minor_pair M C ∅, by simp [to_minor_pair]⟩} 

lemma restriction_is_minor (N M : matroid_in U): 
  N.is_restriction M → N.is_minor M := 
by {rintros ⟨h,-⟩, exact ⟨h⟩}

lemma contraction_minor_is_minor (N M : matroid_in U): 
  N.is_contraction_minor M → N.is_minor M := 
by {rintros ⟨h,-⟩, exact ⟨h⟩}

lemma minor_antisymm: 
  anti_symmetric (@is_minor U _) := 
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
  transitive (@is_minor U _) :=
by {rintros M₁ M₂ M₃ ⟨p₁⟩ ⟨p₂⟩, apply nonempty.intro (p₁.trans p₂)}

lemma minor_iff_has_contract {N M : matroid_in U}:
  N.is_minor M ↔ N.E ⊆ M.E ∧ ∃ C ⊆ M.E \ N.E, ∀ X ⊆ N.E, N.r X = M.r (X ∪ C) - M.r C := 
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨p⟩, 
    have hD := p.E_inter_D, 
    have hE := minor_pair.E_subset p, 
    rcases p with ⟨C,D,h,h',rfl⟩,  
    refine ⟨hE, C, by {rw ←h', apply subset_union_left,}, λ X hX, _ ⟩,
    dsimp only at hD, rw disjoint_iff_subset_compl at hD, 
    simp [subset_iff_inter_eq_left.mp (subset.trans hX hD), diff_eq], },
  rcases h with ⟨hE, C,hC, h⟩,
  have h' : M.E ∩ Cᶜ ∩ N.E = N.E, 
  { rw ←subset_iff_inter_eq_right, apply subset_inter hE, 
    rw [subset_compl_iff_disjoint, inter_comm, ←disjoint_iff_inter_eq_empty], 
    rw subset_diff at hC, exact hC.2, },
  set D := M.E \ N.E \ C with hD, 
  suffices hN : N = M / C \ D, rw hN, apply con_del_is_minor, 
  have hE' : (M / C \ D).E = N.E, 
  {  simp only [hD, diff_eq] with msimp, 
    simp only [compl_inter, compl_compl, inter_distrib_left],    
    rw [inter_right_comm, inter_assoc _ Cᶜ C, h'], simp,  },
  ext : 1, rw hE', intros X hX, rw h X hX, 
  simp only [diff_eq] with msimp, convert rfl, 
  rw [hD, ←subset_iff_inter_eq_left], 
  refine subset.trans hX _, 
  intros h hx, 
  simp only [and_imp, not_and, mem_diff, mem_compl_eq], tauto, 
end

lemma con_or_del {N M : matroid_in U}{e : U}(h : is_minor N M)(he : e ∈ M.E \ N.E): 
  is_minor N (M / {e}) ∨ is_minor N (M \ {e}) :=
begin
  rw is_minor at h, rcases h with ⟨⟨C,D,h,h',rfl⟩⟩, 
  rw [←h', mem_union] at he, cases he, 
  { left, 
    rw [←add_elem he, union_comm, ←con_con],  
    apply con_del_is_minor (M / {e}),  },
  right, 
  rw [con_del_eq_del_con _ _ _ h, ←add_elem he, union_comm, ←del_del ], 
  apply del_con_is_minor, 
end

end minor 

end matroid_in 

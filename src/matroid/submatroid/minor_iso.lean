import prelim.embed prelim.minmax set_tactic.solver
import .minor 

open_locale classical 
noncomputable theory
open matroid set matroid_in 


namespace matroid_in.minor_pair

variables {U V : Type}[fintype U][fintype V]{N M : matroid_in U}

-- The next few definitions relate a minor pair N M to a minor pair N' M.as_mat 

def subset_pair_equiv {X Y : set U}(h : X ⊆ Y) :=
  equiv.set.range 
    (λ (x : X), (⟨x.val, mem_of_mem_of_subset x.property h⟩ : Y))
    (λ x y hxy, by {cases x, cases y, dsimp at hxy, rwa subtype.mk_eq_mk at *,  })

def subtype_equiv (P : minor_pair N M) := subset_pair_equiv P.E_subset

@[simp] lemma subset_pair_equiv_apply {X Y : set U}(h : X ⊆ Y)(x : X) :
  subset_pair_equiv h x = ⟨⟨x.val, mem_of_mem_of_subset x.property h⟩, mem_range_self x⟩ := 
rfl 

@[simp] lemma subtype_equiv_apply (P : minor_pair N M)(x : N.E): 
  P.subtype_equiv x = ⟨⟨x.val, mem_of_mem_of_subset x.property P.E_subset⟩, mem_range_self x⟩  := 
rfl 

/-- maps a minor_pair N M to the corresponding minor pair N' M.as_mat-/
def minor_pair_to_as_mat (P : minor_pair N M): 
    minor_pair ((M.as_mat : matroid_in M.E) / (coe ⁻¹' P.C) \ (coe ⁻¹' P.D)) M.as_mat :=
  { C := (coe ⁻¹' P.C),
    D := (coe ⁻¹' P.D),
  disj := by {unfold_coes, rw [←preimage_inter, P.disj, preimage_empty]},
  union := by {unfold_coes, simp [←preimage_union, P.union, preimage_diff, compl_diff] with msimp},   
  minor := rfl }

/-- for a minor pair N M, gives the isomorphism from N to the corresponding minor N' 
of M.as_mat. Not a fun proof because dependent types are annoying - can we improve it?-/
def minor_isom_minor_as_mat (P : minor_pair N M): 
  N.isom ((M.as_mat : matroid_in M.E) / (coe ⁻¹' P.C) \ (coe ⁻¹' P.D)) := 
⟨ P.subtype_equiv.trans (equiv.set.of_eq begin
    simp only with msimp,
    ext, cases x with x hx, 
    simp only [exists_prop, set_coe.exists, mem_range, exists_eq_right, 
    mem_preimage, mem_diff, subtype.coe_mk, univ_diff, mem_compl_eq], 
    rw [←not_iff_not, decidable.not_and_distrib, not_not, not_not, 
    ←mem_union, P.union, mem_diff], tauto, end ), 
  λ X, begin
    simp only with msimp, rw P.rank_subtype, 
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

/-- given a matroid M, a minor_pair N M, and a matroid M' isomorphic to M, constructs the corresponding
minor pair N' M'-/
def minor_pair_matroid_to_minor_pair_iso {M : matroid U}{M' : matroid V}{N : matroid_in U}
(P : minor_pair N M)(i : M.isom M'):
  minor_pair ((M' : matroid_in V) / (i.equiv '' P.C) \ (i.equiv '' P.D)) M' := 
{ C := (i.equiv '' P.C),
  D := (i.equiv '' P.D),
  disj := by rw [image_inter i.equiv.injective, P.disj, image_empty],
  union := by {simp only with msimp, rw [diff_diff, ←image_union, P.union], simp,},
  minor := rfl }

/-- given a matroid M, a minor_pair N M, and a matroid M' isomorphic to M, gives an isomorphism from 
N to the corresponding minor N' of M' -/
def minor_matroid_to_minor_iso {M : matroid U}{M' : matroid V}{N : matroid_in U}
  (P : minor_pair N M)(i : M.isom M'):
  N.isom ((M' : matroid_in V) / (i.equiv '' P.C) \ (i.equiv '' P.D)) := 
⟨ (equiv.set.image i.equiv _ i.equiv.injective).trans (equiv.set.of_eq (
  by {simp only with msimp, 
      rw [diff_diff, ←image_union, P.union, univ_diff, ←equiv.image_compl, coe_E],
      simp,})) ,
  begin
    intro X, simp_rw [as_mat_r, P.rank_subtype, coe_r, ←i.on_rank], 
    simp only with msimp, congr, 
    simp_rw [←equiv.preimage_eq_iff_eq_image, preimage_union, preimage_diff, equiv.preimage_image], 
    congr' 1, unfold_coes, ext, 
    
    conv {congr, rw mem_diff, congr, rw mem_preimage, rw mem_image, congr, funext, 
    rw mem_image, conv {congr, congr, funext, conv {congr, skip, dsimp, }} }, rw mem_image, 
    split, 
    { rintro ⟨⟨⟨y,hy⟩,⟨⟨⟨z,hz⟩,⟨hzX,hy'⟩⟩,h'⟩ ⟩,hxD⟩,  
      dsimp only at h', subst h',
      exact ⟨⟨z,hz⟩,⟨hzX,by {by {simp at hy', assumption, }, }⟩⟩},
    rintro ⟨⟨y,hy⟩,⟨hyx,rfl⟩⟩, 
    refine ⟨⟨⟨i.equiv y, _⟩ ,_⟩,nonmem_of_mem_disjoint hy P.E_inter_D⟩, 
    { simp only with msimp, 
      rwa [diff_diff, ←image_union, P.union, coe_E, univ_diff, univ_diff, equiv.image_compl, 
      compl_compl, equiv.image_mem_image_iff_mem], }, 
    refine ⟨⟨⟨y,hy⟩,hyx,_⟩,rfl⟩, 
    rw subtype.mk_eq_mk, refl,   
  end⟩
 
/-- given a minor pair N,M, an isomorphism from M to M' maps it to a minor pair N',M' -/
def image_minor_pair {N M : matroid_in U}{M' : matroid_in V}
(i : isom M M')(P : minor_pair N M): 
  minor_pair (M' / (i.equiv '' (coe ⁻¹' P.C)) \ (i.equiv '' (coe ⁻¹' P.D))) M' := 
 {  C := (i.equiv '' (coe ⁻¹' P.C) : set M'.E),
    D := (i.equiv '' (coe ⁻¹' P.D) : set M'.E),
    disj := begin
      unfold_coes, 
      repeat {rw [image_inter, image_eq_empty]}, 
      rw [←preimage_inter, P.disj, preimage_empty],
      apply equiv.injective, apply subtype.val_injective, 
    end,
    union := begin
      unfold_coes, 
      simp only [del_E, con_E, subtype.val_eq_coe, diff_diff, diff_self_diff], 
      rw [eq_comm, ←subset_iff_inter_eq_right, ←image_union, ←image_union],  
      refine subset.trans (image_subset_range _ _) _, 
      intro x, rw mem_range, rintros ⟨⟨y,hy⟩,rfl⟩, exact hy,  
    end,
    minor := rfl }

lemma image_minor_iso_minor {N M : matroid_in U}{M' : matroid_in V}
(i : isom M M')(P : minor_pair N M) :
  isom N (M' / (i.equiv '' (coe ⁻¹' P.C)) \ (i.equiv '' (coe ⁻¹' P.D))) := 
let iN := minor_isom_minor_as_mat P, 
    iN' := minor_isom_minor_as_mat (image_minor_pair i P),
    P' := minor_pair_to_as_mat P,  
    i' := minor_matroid_to_minor_iso P' i, 
    h  : (↑(M'.as_mat) / ⇑(i.equiv) '' P'.C \ ⇑(i.equiv) '' P'.D 
          = (M'.as_mat : matroid_in M'.E) / coe ⁻¹' (image_minor_pair i P).C \ coe ⁻¹' (image_minor_pair i P).D) :=
      by {dsimp only [P', minor_pair_to_as_mat, image_minor_pair], unfold_coes, congr; {ext, simp}} in 
  (iN.trans (matroid_in.isom_equiv rfl h i')).trans iN'.symm 


end matroid_in.minor_pair 


namespace matroid 

open matroid_in.minor_pair 


variables {U V W : Type}[fintype U][fintype V][fintype W]


/-- an embedding of N into M as a minor-/
@[ext] structure minor_emb (N : matroid V)(M : matroid U) :=
{N' : matroid_in U}
(P  : minor_pair N' M)
(i  : isom_to_matroid N' N)

/-- an embedding of N into M as a restriction -/
@[ext] structure restr_emb (N : matroid V)(M : matroid U) := 
{N' : matroid_in U}
(P  : minor_pair N' M)
(hP : P.C = ∅)
(i  : isom_to_matroid N' N)

@[ext] structure minor_C_emb (N : matroid V)(M : matroid U) :=
(e : V ↪ U)
(C : set U)
(disj : C ∩ range e = ∅)
(on_rank : ∀ X : set V, N.r X = M.r (e '' X ∪ C) - M.r C)

def minor_emb_equiv_C_emb {N : matroid V}{M : matroid U}: 
  minor_emb N M ≃ minor_C_emb N M :=
{ to_fun := λ me, 
  { e := ⟨λ v, me.i.equiv.symm v, λ v v' hvv', by {have := subtype.val_injective hvv', simp at this, assumption, }⟩,
    C := me.P.C,
    disj := by {
      dsimp only, ext, 
      simp only [not_exists, mem_empty_eq, mem_inter_eq, not_and, mem_range, function.embedding.coe_fn_mk, 
      iff_false, equiv.inv_fun_as_coe], 
      rintros hx y hxy, rw ←hxy at hx, 
      cases me.i.equiv.symm y with z hz,  
      exact ne_empty_iff_has_mem.mpr ⟨_,(mem_inter hz hx)⟩ me.P.E_inter_C, },
    on_rank := λ X, by {
      cases me with N' P i, dsimp only, 
      rw [←i.symm.on_rank, as_mat_r, P.rank_subtype, coe_r], congr', 
      unfold_coes, ext, 
      simp only [mem_image, equiv.to_fun_as_coe, equiv.apply_eq_iff_eq, set_coe.exists, exists_and_distrib_right, 
      exists_eq_right, subtype.coe_mk, subtype.val_eq_coe, equiv.inv_fun_as_coe], 
      split, 
      { rintros ⟨hx,y,hy,hy'⟩, refine ⟨y,hy,_⟩, dsimp only [isom.symm] at hy', rw hy', refl,  },
      rintros ⟨y, hy, rfl⟩, exact ⟨((i.equiv.symm) y).property,y,⟨hy, by {ext, refl}⟩⟩,
    } },
  inv_fun := λ mc,
  { N' := ((M : matroid_in U) / mc.C) ∣ (range mc.e),
    P := minor_pair.of_contract_restrict 
      (M : matroid_in U) 
      (subset_univ mc.C) 
      (by {rw [univ_diff, ←disjoint_iff_subset_compl, inter_comm], exact mc.disj, } : range mc.e ⊆ univ \ mc.C),
    i := 
    let e1 := equiv.set.range mc.e mc.e.inj', 
        h := contr_restr_E (M : matroid_in U) 
          (by {rw [coe_E, univ_diff, ←disjoint_iff_subset_compl, inter_comm], exact mc.disj}),
        e2 := (equiv.set.of_eq h).symm in 
    matroid.isom.symm ⟨e1.trans e2, λ X, begin
      simp only [e1,e2, as_mat_r] with msimp, 
      rw mc.on_rank, congr, unfold_coes, ext, simp, sorry, 
    end⟩}, 
    
  left_inv := λ me, by {ext, },
  right_inv := sorry }





/-- the property of N being isomorphic to a minor of M-/
def is_iminor_of (N : matroid V)(M : matroid U) := nonempty (minor_emb N M)

/-- the property of N being isomorphic to a restriction of M -/
def is_irestr_of (N : matroid V)(M : matroid U) := nonempty (restr_emb N M)

lemma iminor_of_iff (N : matroid V)(M : matroid U) :
  N.is_iminor_of M ↔ ∃ (N' : matroid_in U), N'.is_minor M ∧ N'.is_isom_to_matroid N :=
by {split, rintros ⟨N',P,i⟩, exact ⟨N',⟨P⟩,⟨i⟩⟩, rintros ⟨N',⟨P⟩,⟨i⟩⟩, exact ⟨⟨N',P,i⟩⟩}  

def irestr_of_iff (N : matroid V)(M : matroid U) :
  N.is_irestr_of M ↔ ∃ (M' : matroid_in U), M'.is_restriction M ∧ M'.is_isom_to_matroid N := 
by {split, rintros ⟨N',P,hP,i⟩, exact ⟨N',⟨P,hP⟩,⟨i⟩⟩, rintros ⟨N',⟨P,hP⟩,⟨i⟩⟩, exact ⟨⟨N',P,hP,i⟩⟩}

lemma iminor_of_iff_exists_embedding {N : matroid V}{M : matroid U}:
  N.is_iminor_of M ↔ ∃ (φ : V ↪ U)(C : set U), (set.range φ) ∩ C = ∅ 
                         ∧ ∀ X, N.r X = M.r (φ '' X ∪ C) - M.r C := 
begin
  simp_rw [iminor_of_iff, matroid_in.isom_to_matroid_iff_exists_embedding], 
  split, 
  { rintros ⟨M,⟨P⟩, ⟨φ, ⟨hrange, hr⟩⟩⟩, 
    refine ⟨φ, P.C,_, λ X, _⟩, 
    { rw hrange, exact P.E_inter_C, },
    { rw [hr X, P.rank (φ '' X) (by {rw ←hrange, apply image_subset_range})], refl, }},
  rintros ⟨φ,C, hrange, hr⟩, 
  rw [disjoint_iff_inter_compl_eq_left, inter_comm] at hrange, 
  exact ⟨((M : matroid_in U) / C) ∣ 
    range φ, 
    matroid_in.con_restr_is_minor _ _ _, 
    φ, 
    ⟨by simp [hrange],
    λ X, by simp [hr X, subset_iff_inter_eq_left.mp (image_subset_range φ X)]⟩⟩, 
end

lemma iminor_of_iff_exists_good_embedding {N : matroid V}{M : matroid U}:
  N.is_iminor_of M ↔ ∃ (φ : V ↪ U)(C : set U), 
                           (set.range φ) ∩ C = ∅ 
                         ∧ (∀ X, N.r X = M.r (φ '' X ∪ C) - M.r C)
                         ∧ M.is_indep C 
                         ∧ N.r univ = M.r univ - M.r C := 
begin
  simp_rw [iminor_of_iff, matroid_in.isom_to_matroid_iff_exists_embedding], 
  split, 
  { rintros ⟨M',h_minor, ⟨φ, ⟨hrange, hr⟩⟩⟩, 
    obtain ⟨P,⟨hPi,hPs⟩⟩ := matroid_in.minor_pair.minor_has_indep_coindep_pair' h_minor, 
    rw matroid_in.indep_iff_coe at hPi,
    refine ⟨φ, P.C,_, λ X, _, hPi ,_⟩,  
    { rw hrange, exact P.E_inter_C, },
    { rw [hr X, P.rank (φ '' X) (by {rw ←hrange, apply image_subset_range})], refl},
    simp only [←indep_iff_r.mp hPi] with msimp at hPs, 
    rw [hPs, hr univ, image_univ, hrange], simp, },
  rintros ⟨φ,C, hrange, hr⟩, 
  rw [disjoint_iff_inter_compl_eq_left, inter_comm] at hrange, 
  exact ⟨((M : matroid_in U) / C) ∣ 
    range φ, 
    matroid_in.con_restr_is_minor _ _ _, 
    φ, 
    ⟨by simp [hrange],
    λ X, by {simp [hr.1 X, subset_iff_inter_eq_left.mp (image_subset_range φ X)],}, ⟩⟩, 
end


lemma irestr_of_iff_exists_map {N : matroid V}{M : matroid U}:
  N.is_irestr_of M ↔ ∃ (φ : V ↪ U), ∀ X, N.r X = M.r (φ '' X) := 
begin
  simp_rw [irestr_of_iff, matroid_in.isom_to_matroid_iff_exists_embedding], 
  split, 
  { rintros ⟨M', ⟨P,hC⟩, ⟨φ, hrange,hr⟩ ⟩, 
    refine ⟨φ, λ X, _⟩, 
    specialize hr X, 
    rw [matroid_in.minor_pair.rank P, hC] at hr, convert hr, simp, 
    rw ←hrange, apply image_subset_range, },
  rintros ⟨φ, hr⟩, 
  refine ⟨(M : matroid_in U) ∣ range φ, matroid_in.restriction_to_is_restriction _ _,φ, ⟨_,λ X, _⟩⟩,  
    simp, 
  rw hr X, simp [subset_iff_inter_eq_left.mp (image_subset_range _ _)], 
end

lemma iminor_refl (M : matroid U): 
  M.is_iminor_of M := 
iminor_of_iff_exists_embedding.mpr ⟨function.embedding.refl _,∅,by simp,λ X, by simp⟩


def minor_emb_of_isom_of_minor_emb {N : matroid U}{N' : matroid V}{M : matroid W} 
(i : N.isom N' )(e : N'.minor_emb M) : 
  N.minor_emb M := 
⟨e.N', e.P, e.i.trans i.symm⟩ 

def minor_emb_of_minor_emb_of_isom {N : matroid U}{M' : matroid V}{M : matroid W}
(e : N.minor_emb M' )(i : M'.isom M) :
  N.minor_emb M :=
{ N' := (M : matroid_in W) / (i.equiv '' e.P.C) \ (i.equiv '' e.P.D),
  P := (M : matroid_in W).to_minor_pair (i.equiv '' e.P.C) (i.equiv '' e.P.D),
  i := isom_to_matroid_of_isom ((e.P.minor_matroid_to_minor_iso i).symm.trans (isom_of_isom_to_matroid e.i))}
    
lemma iminor_of_isom_iminor {N : matroid U}{N' : matroid V}{M : matroid W}
(hNN' : N.is_isom N' )(hN'M : N'.is_iminor_of M):
  N.is_iminor_of M := 
begin
  unfold is_iminor_of is_isom at *, 
  obtain ⟨⟨i⟩,⟨e⟩⟩ := ⟨hNN', hN'M⟩, 
  exact ⟨minor_emb_of_isom_of_minor_emb i e⟩,
end

lemma iminor_of_iminor_isom {N : matroid U}{M : matroid V}{M' : matroid W}
(hNM : N.is_iminor_of M)(hMM' : M.is_isom M'):
  N.is_iminor_of M' := 
begin
  unfold is_iminor_of is_isom at *, 
  obtain ⟨⟨i⟩,⟨e⟩⟩ := ⟨hMM', hNM⟩, 
  exact ⟨minor_emb_of_minor_emb_of_isom e i⟩,
end

def iminor_emb_of_minor_pair {N M : matroid_in U}(P : N.minor_pair M): 
  N.as_mat.minor_emb M.as_mat := 
⟨P.minor_pair_to_as_mat, P.minor_isom_minor_as_mat.symm⟩


def minor_emb.trans {L : matroid U}{M : matroid V}{N : matroid W}
  (eLM : minor_emb L M)(eMN : minor_emb M N): 
minor_emb L N := 
begin
  cases eLM with N' P i, cases eMN with N'' P' i', 
  have := minor_pair_matroid_to_minor_pair_iso P, 
  refine ⟨_,_⟩, 
end 

lemma iminor_trans {L : matroid U}{M : matroid V}{N : matroid W}
(hLM : L.is_iminor_of M)(hMN : M.is_iminor_of N):
L.is_iminor_of N := 
begin
  
end
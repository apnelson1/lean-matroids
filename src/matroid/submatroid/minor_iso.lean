import prelim.embed prelim.minmax set_tactic.solver
import .minor 

open_locale classical 
noncomputable theory
open matroid set matroid_in 


namespace matroid_in.minor_pair

variables {α β : Type} [fintype α][fintype β]
{N M : matroid_in α}

-- The next few definitions relate a minor pair N M to a minor pair N' M.as_mat 

def subset_pair_equiv {X Y : set α} (h : X ⊆ Y) :=
  equiv.set.range 
    (λ (x : X), (⟨x.val, mem_of_mem_of_subset x.property h⟩ : Y))
    (λ x y hxy, by {cases x, cases y, dsimp at hxy, rwa subtype.mk_eq_mk at *,  })

def subtype_equiv (P : minor_pair N M) := subset_pair_equiv P.NE_ss_ME

@[simp] lemma subset_pair_equiv_apply {X Y : set α} (h : X ⊆ Y) (x : X) :
  subset_pair_equiv h x = ⟨⟨x.val, mem_of_mem_of_subset x.property h⟩, mem_range_self x⟩ := 
rfl 

@[simp] lemma subtype_equiv_apply (P : minor_pair N M) (x : N.E) : 
  P.subtype_equiv x = ⟨⟨x.val, mem_of_mem_of_subset x.property P.NE_ss_ME⟩, mem_range_self x⟩  := 
rfl 

/-- for a minor pair N M, gives the isomorphism from N to the corresponding minor N' 
of M.as_mat. Not a fun proof because dependent types are annoying - can we improve it?-/
def minor_isom_minor_as_mat (P : minor_pair N M) : 
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
     have hxM := mem_of_mem_of_subset hxE P.NE_ss_ME, 
     have hxC : x ∉ P.C := nonmem_of_mem_disjoint hxE P.NE_inter_C, 
     have hxD : x ∉ P.D := nonmem_of_mem_disjoint hxE P.NE_inter_D, 
     refine ⟨⟨x,⟨_,⟨x,⟨⟨_,_⟩,⟨⟨hxE,_⟩,⟨_,rfl⟩⟩⟩⟩,rfl⟩⟩,_⟩;
     assumption, 
    end⟩ 

/-- the image of a cd_pair under a matroid isomorphism -/
def image_cd_pair {M : matroid α} {M' : matroid β} (p : cd_pair (M : matroid_in α))
(i : M.isom M') : 
  cd_pair (M' : matroid_in β) := 
{ C := (i.equiv '' p.C),
  D := (i.equiv '' p.D),
  disj := by rw [(image_inter i.equiv.injective), p.disj, image_empty],
  C_ss_E := λ x hx, by simp, 
  D_ss_E := λ x hx, by simp}

/-- given a minor pair N,M, an isomorphism from M to M' maps it to a minor pair N',M' -/
def image_minor_pair {N M : matroid_in α} {M' : matroid_in β}
(i : isom M M') (P : minor_pair N M) : 
  minor_pair (M' / (i.equiv '' (coe ⁻¹' P.C)) \ (i.equiv '' (coe ⁻¹' P.D))) M' := 
{ minor := rfl, .. cd_pair.from_as_mat (image_cd_pair (cd_pair.to_as_mat (coe P)) i) }

/-- given a matroid M, a minor_pair N M, and a matroid M' isomorphic to M, gives an isomorphism 
from N to the corresponding minor N' of M' -/
def minor_matroid_to_minor_iso {M : matroid α} {M' : matroid β} {N : matroid_in α}
  (P : minor_pair N M) (i : M.isom M') :
  N.isom ((M' : matroid_in β) / (i.equiv '' P.C) \ (i.equiv '' P.D)) := 
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
    refine ⟨⟨⟨i.equiv y, _⟩ ,_⟩,nonmem_of_mem_disjoint hy P.NE_inter_D⟩, 
    { simp only with msimp, 
      rwa [diff_diff, ←image_union, P.union, coe_E, univ_diff, univ_diff, equiv.image_compl, 
      compl_compl, equiv.image_mem_image_iff_mem], }, 
    refine ⟨⟨⟨y,hy⟩,hyx,_⟩,rfl⟩, 
    rw subtype.mk_eq_mk, refl,   
  end⟩
 

def image_minor_iso_minor {N M : matroid_in α} {M' : matroid_in β}
(i : isom M M') (P : minor_pair N M) :
  isom N (M' / (i.equiv '' (coe ⁻¹' P.C)) \ (i.equiv '' (coe ⁻¹' P.D))) := 
let iN := minor_isom_minor_as_mat P, 
    iN' := minor_isom_minor_as_mat (image_minor_pair i P),
    P' := minor_pair_to_as_mat P,  
    i' := minor_matroid_to_minor_iso P' i in 
    have h : (
      ↑(M'.as_mat) / ⇑(i.equiv) '' P'.C \ ⇑(i.equiv) '' P'.D 
          = (M'.as_mat : matroid_in M'.E) 
              / coe ⁻¹' (image_minor_pair i P).C 
              \ coe ⁻¹' (image_minor_pair i P).D) :=
      by {dsimp only [P', minor_pair_to_as_mat, image_minor_pair, cd_pair.to_as_mat, 
          cd_pair.from_as_mat, image_cd_pair], 
          unfold_coes, congr; {ext, simp,}}, 
  (iN.trans (matroid_in.isom_equiv rfl h i')).trans iN'.symm 


end matroid_in.minor_pair 

namespace matroid 

open matroid_in.minor_pair 

variables {α β γ : Type}
[fintype α][fintype β][fintype γ]

/-- an embedding of N into M as a minor-/
@[ext] structure minor_emb (N : matroid β) (M : matroid α) :=
{N' : matroid_in α}
(P  : minor_pair N' M)
(i  : isom_to_matroid N' N)

@[ext] structure con_emb (N : matroid β) (M : matroid α) :=
(e : β ↪ α)
(C : set α)
(disj : disjoint (range e) C)
(on_rank : ∀ X : set β, N.r X = M.r (e '' X ∪ C) - M.r C)

def minor_emb.to_con_emb {N : matroid β} {M : matroid α} (me : minor_emb N M) : con_emb N M := 
{ e := ⟨λ v, me.i.equiv.symm v, λ v v' hvv', by simpa using subtype.val_injective hvv'⟩,
  C := me.P.C,
  disj := by {
    simp only [disjoint_iff_inter_eq_empty], ext, 
    simp only [not_exists, mem_empty_eq, mem_inter_eq, not_and, mem_range, 
      function.embedding.coe_fn_mk, iff_false, equiv.inv_fun_as_coe, to_cd_pair_as_coe, 
      exists_imp_distrib], 
    rintros y rfl hxy, 
    cases me.i.equiv.symm y with z hz,  
    exact ne_empty_iff_has_mem.mpr ⟨_,(mem_inter hz hxy)⟩ me.P.NE_inter_C, },
  on_rank := λ X, by {
    cases me with N' P i, dsimp only, 
    rw [←i.symm.on_rank, as_mat_r, P.rank_subtype, coe_r], congr', 
    unfold_coes, ext, 
    simp only [mem_image, equiv.to_fun_as_coe, equiv.apply_eq_iff_eq, set_coe.exists, 
      exists_and_distrib_right, exists_eq_right, subtype.coe_mk, subtype.val_eq_coe, 
      equiv.inv_fun_as_coe], 
    split, 
    { rintros ⟨hx,y,hy,hy'⟩, refine ⟨y,hy,_⟩, dsimp only [isom.symm] at hy', rw hy', refl,  },
    rintros ⟨y, hy, rfl⟩, exact ⟨((i.equiv.symm) y).property,y,⟨hy, by {ext, refl}⟩⟩,
  } }

def con_emb.to_minor_emb {N : matroid β} {M : matroid α} (ce : con_emb N M) : (minor_emb N M) := 
{ 
  P := minor_pair.of_contract_restrict 
    (M : matroid_in α) 
    (subset_univ ce.C) 
    (by {rw [univ_diff, ←disjoint_iff_subset_compl, ← disjoint_iff_inter_eq_empty], 
          exact ce.disj, } : range ce.e ⊆ univ \ ce.C),
  i := 
  let e1 := equiv.set.range ce.e ce.e.inj', 
      h := @contr_restr_E _ _ (M : matroid_in α) ce.C (range ce.e)
        (by {rw [coe_E, univ_diff, ←disjoint_iff_subset_compl, ← disjoint_iff_inter_eq_empty], 
          exact ce.disj}),
      e2 := (equiv.set.of_eq h).symm in 
  matroid.isom.symm ⟨e1.trans e2, λ X, 
  begin
    simp only [e1,e2, as_mat_r] with msimp, 
    rw ce.on_rank, congr, unfold_coes, ext, 
    simp only [mem_image, equiv.to_fun_as_coe, exists_prop, mem_range_self, restr_E, 
      equiv.set.range_apply, con_E, mem_inter_eq, set_coe.exists, mem_range, 
      function.embedding.to_fun_eq_coe, function.comp_app, subtype.mk_eq_mk, equiv.coe_trans, 
      equiv.set.of_eq_symm_apply, subtype.coe_mk, coe_E, univ_diff, mem_compl_eq, 
      subtype.val_eq_coe], 
    split, {rintro ⟨⟨_,-, h,rfl⟩,-,-⟩, exact h},
    rintro ⟨v,hv,rfl⟩,  refine ⟨⟨ce.e v,⟨⟨_,⟨_,rfl⟩⟩,⟨⟨_,hv,rfl⟩,rfl⟩⟩⟩,⟨v,rfl⟩⟩, 
    exact nonmem_of_mem_disjoint (mem_range_self _) (disjoint_iff_inter_eq_empty.mp ce.disj), 
  end⟩}

lemma con_emb.rank_le_rank_image {N : matroid β} {M : matroid α} (emb : con_emb N M) (X : set β) :
  N.r X ≤ M.r (emb.e '' X) :=
by {rw emb.on_rank, linarith [M.rank_subadditive (emb.e '' X) emb.C ]}

lemma con_emb.nonloop_of_nonloop {N : matroid β} {M : matroid α} (emb : con_emb N M)
{x : β} (he : N.is_nonloop x) :
  M.is_nonloop (emb.e x) := 
nonloop_of_one_le_rank 
  (by {rw [←rank_nonloop he, ← image_singleton], apply emb.rank_le_rank_image, })

/-- an embedding of N into M as a restriction -/
@[ext] structure restr_emb (N : matroid β) (M : matroid α) := 
{N' : matroid_in α}
(P  : minor_pair N' M)
(hP : P.C = ∅)
(i  : isom_to_matroid N' N)

@[ext] structure inj_emb (N : matroid β) (M : matroid α) := 
(e : β ↪ α)
(on_rank : ∀ X : set β, N.r X = M.r (e '' X))

def restr_emb.to_inj_emb {N : matroid β} {M : matroid α} (re : restr_emb N M) : inj_emb N M := 
{ e := ⟨λ v, re.i.equiv.symm v, λ v v' hvv', by simpa using subtype.val_injective hvv'⟩,
  on_rank := λ X, by {
    simp only [← re.i.symm.on_rank, as_mat_r, re.P.rank_subtype, coe_r, re.hP, rank_empty, sub_zero, 
    isom.symm, union_empty], unfold_coes, rw [←image_comp], }}

def inj_emb.to_restr_emb {N : matroid β} {M : matroid α} {ie : inj_emb N M } : restr_emb N M := 
{ P := minor_pair.of_restrict (M : matroid_in α) (subset_univ (range ie.e)), 
  hP := rfl,
  i := 
  let e1 := equiv.set.range ie.e ie.e.inj', 
      e2 := (equiv.set.of_eq (by simp : range ie.e = (↑M ∣ range ⇑(ie.e)).E)) in
  matroid.isom.symm ⟨e1.trans e2, λ X, begin
    simp only [ie.on_rank, as_mat_r, equiv.image_trans, e1, e2] with msimp,
    congr, unfold_coes, ext, 
    simp only [mem_image, equiv.to_fun_as_coe, exists_prop, mem_range_self, 
    equiv.set.of_eq_apply, restr_E, equiv.set.range_apply, mem_inter_eq, set_coe.exists, mem_range,
    function.embedding.to_fun_eq_coe, eq_self_iff_true, subtype.mk_eq_mk, exists_exists_and_eq_and, 
    exists_exists_eq_and, exists_and_distrib_left, exists_true_left, subtype.coe_mk, coe_E, 
    univ_inter, subtype.val_eq_coe, exists_apply_eq_apply], 
    split; tidy, 
  end ⟩ } 

def restr_emb.to_minor_emb {N : matroid β} {M : matroid α} (re : restr_emb N M) : 
  minor_emb N M := 
⟨re.P, re.i⟩ 

/-- the property of N being isomorphic to a minor of M-/
def is_iminor_of (N : matroid β) (M : matroid α) := nonempty (minor_emb N M)

/-- the property of N being isomorphic to a restriction of M -/
def is_irestr_of (N : matroid β) (M : matroid α) := nonempty (restr_emb N M)

lemma iminor_of_iff (N : matroid β) (M : matroid α) :
  N.is_iminor_of M ↔ ∃ (N' : matroid_in α), N'.is_minor M ∧ N'.is_isom_to_matroid N :=
by {split, rintros ⟨N',P,i⟩, exact ⟨N',⟨P⟩,⟨i⟩⟩, rintros ⟨N',⟨P⟩,⟨i⟩⟩, exact ⟨⟨P,i⟩⟩}  

lemma irestr_of_iff (N : matroid β) (M : matroid α) :
  N.is_irestr_of M ↔ ∃ (M' : matroid_in α), M'.is_restriction M ∧ M'.is_isom_to_matroid N := 
by {split, rintros ⟨N',P,hP,i⟩, exact ⟨N',⟨P,hP⟩,⟨i⟩⟩, rintros ⟨N',⟨P,hP⟩,⟨i⟩⟩, exact ⟨⟨P,hP,i⟩⟩}

lemma iminor_of_iff_exists_embedding {N : matroid β} {M : matroid α} :
  N.is_iminor_of M ↔ ∃ (φ : β ↪ α) (C : set α), disjoint (set.range φ) C 
                         ∧ ∀ X, N.r X = M.r (φ '' X ∪ C) - M.r C := 
begin
  simp_rw [iminor_of_iff, matroid_in.isom_to_matroid_iff_exists_embedding], 
  split, 
  { rintros ⟨M,⟨P⟩, ⟨φ, ⟨hrange, hr⟩⟩⟩, 
    refine ⟨φ, P.C,_, λ X, _⟩, 
    { rw hrange, exact P.NE_disj_C, },
    { rw [hr X, P.rank (φ '' X) (by {rw ←hrange, apply image_subset_range})], refl, }},
  rintros ⟨φ,C, hrange, hr⟩, 
  rw [disjoint_iff_inter_eq_empty, disjoint_iff_inter_compl_eq_left, inter_comm] at hrange, 
  exact ⟨((M : matroid_in α) / C) ∣ 
    range φ, 
    matroid_in.con_restr_is_minor _ _ _, 
    φ, 
    ⟨by simp [hrange],
    λ X, by simp [hr X, subset_iff_inter_eq_left.mp (image_subset_range φ X)]⟩⟩, 
end

lemma iminor_of_iff_exists_good_C {N : matroid β} {M : matroid α} :
  N.is_iminor_of M ↔ ∃ (φ : β ↪ α) (C : set α), 
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
    { rw hrange, exact P.NE_inter_C, },
    { rw [hr X, P.rank (φ '' X) (by {rw ←hrange, apply image_subset_range})], refl},
    simp only [←indep_iff_r.mp hPi] with msimp at hPs, 
    rw [hPs, hr univ, image_univ, hrange], simp, },
  rintros ⟨φ,C, hrange, hr⟩, 
  rw [disjoint_iff_inter_compl_eq_left, inter_comm] at hrange, 
  exact ⟨((M : matroid_in α) / C) ∣ 
    range φ, 
    matroid_in.con_restr_is_minor _ _ _, 
    φ, 
    ⟨by simp [hrange],
    λ X, by {simp [hr.1 X, subset_iff_inter_eq_left.mp (image_subset_range φ X)],}, ⟩⟩, 
end

lemma iminor_of_iff_exists_con_emb {N : matroid β} {M : matroid α} :
  N.is_iminor_of M ↔ nonempty (con_emb N M) :=
begin
  rw is_iminor_of, split, 
  { rintro ⟨me⟩, exact ⟨me.to_con_emb⟩, },
  { rintro ⟨ce⟩, exact ⟨ce.to_minor_emb⟩, }, 
end

lemma iminor_of_iff_exists_good_con_emb {N : matroid β} {M : matroid α} :
  N.is_iminor_of M ↔ ∃ em : con_emb N M, (M.is_indep em.C ∧ M.r em.C = M.r univ - N.r univ) :=
begin
  split, swap, rintros ⟨em,h₁,h₂⟩, exact ⟨em.to_minor_emb⟩, 
  rintro ⟨em⟩, 
  obtain ⟨P',⟨hPi,hPs⟩⟩ := matroid_in.minor_pair.minor_has_indep_coindep_pair' ⟨em.P⟩, 
  refine ⟨(minor_emb.to_con_emb ⟨P',em.i⟩),_,_⟩; dsimp [minor_emb.to_con_emb],
  {simpa using hPi},
  convert hPs using 1, unfold_coes, rw [←indep_iff_r], simpa using hPi, 
  convert rfl, 
  rw [← em.i.symm.on_rank, as_mat_r], 
  apply congr_arg, simp only [equiv.range_eq_univ, set.image_univ], unfold_coes, simp, 
end

lemma irestr_of_iff_exists_map {N : matroid β} {M : matroid α} :
  N.is_irestr_of M ↔ ∃ (φ : β ↪ α), ∀ X, N.r X = M.r (φ '' X) := 
begin
  simp_rw [irestr_of_iff, matroid_in.isom_to_matroid_iff_exists_embedding], 
  split, 
  { rintros ⟨M', ⟨P,hC⟩, ⟨φ, hrange,hr⟩ ⟩, 
    refine ⟨φ, λ X, _⟩, 
    specialize hr X, 
    rw [matroid_in.minor_pair.rank P, hC] at hr, convert hr, simp, 
    rw ←hrange, apply image_subset_range, },
  rintros ⟨φ, hr⟩, 
  refine ⟨(M : matroid_in α) ∣ range φ, matroid_in.restriction_to_is_restriction _ _,φ, ⟨_,λ X, _⟩⟩,  
    simp, 
  rw hr X, simp [subset_iff_inter_eq_left.mp (image_subset_range _ _)], 
end

lemma iminor_refl (M : matroid α) : 
  M.is_iminor_of M := 
iminor_of_iff_exists_embedding.mpr ⟨function.embedding.refl _,∅,by simp,λ X, by simp⟩

def minor_emb_of_isom_of_minor_emb {N : matroid α} {N' : matroid β} {M : matroid γ} 
(i : N.isom N' ) (e : N'.minor_emb M) : 
  N.minor_emb M := 
⟨e.P, e.i.trans i.symm⟩ 

def minor_emb_of_minor_emb_of_isom {N : matroid α} {M' : matroid β} {M : matroid γ}
(e : N.minor_emb M' ) (i : M'.isom M) :
  N.minor_emb M :=
{ N' := (M : matroid_in γ) / (i.equiv '' e.P.C) \ (i.equiv '' e.P.D),
  P := (M : matroid_in γ).to_minor_pair (i.equiv '' e.P.C) (i.equiv '' e.P.D),
  i := isom_to_matroid_of_isom ((e.P.minor_matroid_to_minor_iso i).symm.trans 
                                                  (isom_of_isom_to_matroid e.i))}
    
lemma iminor_of_irestr {N : matroid α} {M : matroid β} (h : N.is_irestr_of M) : 
  N.is_iminor_of M :=
let ⟨re⟩ := h in ⟨restr_emb.to_minor_emb re⟩ 

lemma iminor_of_isom_iminor {N : matroid α} {N' : matroid β} {M : matroid γ}
(hNN' : N.is_isom N' ) (hN'M : N'.is_iminor_of M) :
  N.is_iminor_of M := 
begin
  unfold is_iminor_of is_isom at *, 
  obtain ⟨⟨i⟩,⟨e⟩⟩ := ⟨hNN', hN'M⟩, 
  have := minor_emb_of_isom_of_minor_emb, 
  exact ⟨this i e⟩ , 
end

lemma iminor_of_iminor_isom {N : matroid α} {M : matroid β} {M' : matroid γ}
(hNM : N.is_iminor_of M) (hMM' : M.is_isom M') :
  N.is_iminor_of M' := 
begin
  unfold is_iminor_of is_isom at *, 
  obtain ⟨⟨i⟩,⟨e⟩⟩ := ⟨hMM', hNM⟩, 
  have := minor_emb_of_minor_emb_of_isom,
  exact ⟨this e i⟩, 
end

def iminor_emb_of_minor_pair {N M : matroid_in α} (P : N.minor_pair M) : 
  N.as_mat.minor_emb M.as_mat := 
⟨P.minor_pair_to_as_mat, P.minor_isom_minor_as_mat.symm⟩


def minor_emb.trans {L : matroid α} {M : matroid β} {N : matroid γ}
  (eLM : minor_emb L M) (eMN : minor_emb M N) : 
minor_emb L N := 
let ⟨e₁,C₁,h₁,hr₁⟩ := eLM.to_con_emb, 
    ⟨e₂,C₂,h₂,hr₂⟩ := eMN.to_con_emb in 
con_emb.to_minor_emb ({
  e := e₁.trans e₂, 
  C := (e₂ '' C₁) ∪ C₂, 
  disj := by {rw [disjoint_iff_inter_eq_empty, inter_distrib_left, 
                          union_empty_iff, function.embedding.trans],  
    unfold_coes at ⊢ h₁ h₂, dsimp only,  split, 
    { rwa [range_comp, image_inter e₂.inj', image_eq_empty, ← disjoint_iff_inter_eq_empty]},
    rw disjoint_iff_inter_eq_empty at h₂, 
    exact disjoint_of_subset_left' (range_comp_subset_range _ _) h₂, },
  on_rank := λ X, 
  begin
    rw [hr₁, hr₂, hr₂], ring, 
    rw [neg_add_eq_sub, image_union, ←union_assoc, function.embedding.trans], 
    unfold_coes, rw ←image_comp, 
  end
})

lemma iminor_trans {L : matroid α} {M : matroid β} {N : matroid γ}
(hLM : L.is_iminor_of M) (hMN : M.is_iminor_of N) :
L.is_iminor_of N := 
begin
  -- why is this silly hack neccessary? 
  unfold is_iminor_of at *, 
  obtain ⟨⟨e₁⟩,⟨e₂⟩⟩ := ⟨hLM, hMN⟩, 
  have := minor_emb.trans, 
  exact ⟨this e₁ e₂⟩, 
end 

/-- the property of having an N-minor -/
def has_iminor (M : matroid α) (N : matroid β) := 
  N.is_iminor_of M 

/-- the property of having an N-restriction -/
def has_irestr (M : matroid α) (N : matroid β) := 
  N.is_irestr_of M 

end matroid 

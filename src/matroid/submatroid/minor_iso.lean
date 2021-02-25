import prelim.embed prelim.minmax set_tactic.solver
import .minor 

open_locale classical 
noncomputable theory
open matroid set


variables {U V W : Type}[fintype U][fintype V][fintype W]

/-- the property of N being isomorphic to a minor of M-/
def matroid.is_iminor_of (N : matroid V)(M : matroid U) := 
  ∃ (M' : matroid_in U), M'.is_minor M ∧ M'.is_isom N 

def matroid.is_irestr_of (N : matroid V)(M : matroid U) := 
  ∃ (M' : matroid_in U), M'.is_restriction M ∧ M'.is_isom N 

lemma iminor_of_iff_exists_map {N : matroid V}{M : matroid U}:
  N.is_iminor_of M ↔ ∃ (φ : V ↪ U)(C : set U), (set.range φ) ∩ C = ∅ 
                         ∧ ∀ X, N.r X = M.r (φ '' X ∪ C) - M.r C := 
begin
  simp_rw [matroid.is_iminor_of, matroid_in.isom_iff_exists_embedding], 
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

lemma iminor_of_iff_exists_good_map {N : matroid V}{M : matroid U}:
  N.is_iminor_of M ↔ ∃ (φ : V ↪ U)(C : set U), 
                           (set.range φ) ∩ C = ∅ 
                         ∧ (∀ X, N.r X = M.r (φ '' X ∪ C) - M.r C)
                         ∧ M.is_indep C 
                         ∧ N.r univ = M.r univ - M.r C := 
begin
  simp_rw [matroid.is_iminor_of, matroid_in.isom_iff_exists_embedding], 
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
  simp_rw [matroid.is_irestr_of, matroid_in.isom_iff_exists_embedding], 
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

lemma iminor_of_isom_iminor {N : matroid U}{N' : matroid V}{M : matroid W}
(hNN' : N.is_isom N' )(hN'M : N'.is_iminor_of M):
  N.is_iminor_of M := 
begin
  unfold is_isom at hNN',  
  obtain ⟨i⟩ := hNN', 
  obtain ⟨M', ⟨h, ⟨j⟩⟩⟩ := hN'M, 
  exact ⟨M', ⟨h,⟨j.trans i.symm⟩ ⟩⟩, 
end

lemma iminor_of_minor {N M : matroid_in U}(h : N.is_minor M): 
  N.as_mat.is_iminor_of M.as_mat := 
begin
  unfold matroid_in.is_minor at h, rcases h with ⟨P⟩, 
  set f : N.E ↪ M.E := 
    ⟨λ x, ⟨x.val, mem_of_mem_of_subset x.property P.E_subset⟩,
    λ x y hxy,  by {dsimp only at hxy, cases x, cases y, simp at *, assumption }⟩ with hf,  
  refine ⟨(M.as_mat : matroid_in M.E) / (coe ⁻¹' P.C) \ (coe ⁻¹' P.D),_,_⟩, 
    apply matroid_in.con_del_is_minor, 
  rw matroid_in.isom_iff_exists_embedding, 
  refine ⟨f, _,λ X, _⟩,
  { simp only [univ_inter] with msimp,   
    rw [←compl_union, inv_image_union], }, 

  --refine ⟨_⟩, -- etc etc. 
  --sorry, 
end



lemma iminor_trans {L : matroid U}{M : matroid V}{N : matroid W}
(hLM : L.is_iminor_of M)(hMN : M.is_iminor_of N):
L.is_iminor_of N := 
begin
  obtain ⟨L',⟨hL,⟨iL⟩⟩⟩  := hLM,  obtain ⟨M',⟨hM,⟨iM⟩⟩⟩ := hMN,  
  refine iminor_of_isom_iminor ⟨iL.symm⟩ _,  
  --simp_rw [matroid.is_iminor_of] at hLM hMN, 
end
import prelim.embed prelim.minmax set_tactic.solver
import .minor 

open_locale classical 
noncomputable theory

open matroid set


variables {U V : Type}[fintype U][fintype V]

/-- the property of N being isomorphic to a minor of M-/
def matroid.is_iso_to_minor_of (N : matroid V)(M : matroid U) := 
  ∃ (M' : matroid_in U), M'.is_minor M ∧ M'.is_isom N 

def matroid.is_iso_to_restr_of (N : matroid V)(M : matroid U) := 
  ∃ (M' : matroid_in U), M'.is_restriction M ∧ M'.is_isom N 

lemma iso_to_minor_of_iff_exists_map {N : matroid V}{M : matroid U}:
  N.is_iso_to_minor_of M ↔ ∃ (φ : V ↪ U)(C : set U), (set.range φ) ∩ C = ∅ 
                         ∧ ∀ X, N.r X = M.r (φ '' X ∪ C) - M.r C := 
begin
  simp_rw [matroid.is_iso_to_minor_of, matroid_in.isom_iff_exists_embedding], 
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

lemma iso_to_restriction_of_iff_exists_map {N : matroid V}{M : matroid U}:
  N.is_iso_to_restr_of M ↔ ∃ (φ : V ↪ U), ∀ X, N.r X = M.r (φ '' X) := 
begin
  simp_rw [matroid.is_iso_to_restr_of, matroid_in.isom_iff_exists_embedding], 
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



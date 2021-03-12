import prelim.collections prelim.embed prelim.size prelim.induction prelim.minmax finsum.fin_api
import matroid.pointcount matroid.simple 
import matroid.submatroid.projection matroid.submatroid.minor_iso 
import matroid.constructions.uniform 

noncomputable theory 
open_locale classical big_operators 

open set matroid 

universes u v w 

section uniform 

variables {α : Type*} [fintype α] {M : matroid α} {a b : ℤ} 

/-- the rank-a uniform matroid on b elements with ground set `fin' b`. Junk unless `0 ≤ a ≤ b` -/
def canonical_unif (a b : ℤ) : 
  matroid (fin' b) := 
unif.uniform_matroid_on (fin' b) a

lemma canonical_unif_simple_iff (ha : 0 ≤ a) (hb : 2 ≤ b) : 
  (canonical_unif a b).is_simple ↔ 2 ≤ a := 
begin
 convert unif.uniform_matroid_simple_iff (fin' b) _ ha, 
 rwa size_fin' b (by linarith : 0 ≤ b), 
end

lemma canonical_unif_simple_of_two_le_r (ha : 2 ≤ a) : 
  (canonical_unif a b).is_simple :=
unif.unif_simple_of_two_le_r _ ha

@[simp] lemma canonical_unif_r (ha : 0 ≤ a) (X : set (fin' b)) :
  (canonical_unif a b).r X = min a (size X) :=
unif.uniform_matroid_rank ha _

/-- the property of having a `U_{a,b}` -minor -/
def matroid.has_unif_minor (M : matroid α) (a b : ℤ) :=
  M.has_iminor (canonical_unif a b)

lemma has_unif_minor_def : 
  M.has_unif_minor a b ↔ (canonical_unif a b).is_iminor_of M := 
iff.rfl 

lemma has_unif_minor_def' : 
  M.has_unif_minor a b ↔ M.has_iminor (canonical_unif a b) := 
iff.rfl 

lemma has_unif_minor_iff (ha : 0 ≤ a) (hab : a ≤ b) :
  M.has_unif_minor a b ↔ 
    ∃ S C : set α,  disjoint S C 
                  ∧ size S = b 
                  ∧ ∀ X ⊆ S, min a (size X) = M.r (X ∪ C) - M.r C :=
begin
  rw [has_unif_minor_def, iminor_of_iff_exists_embedding], 
  split, 
  { rintros ⟨ φ, C, hdisj, hr⟩, 
    refine ⟨range φ, C, hdisj, _, λ X hX, _⟩,
    { rw [← image_univ, size_image_emb, size_fin'_univ], exact le_trans ha hab,  },
    convert hr (φ ⁻¹' X), 
    rw [canonical_unif_r ha, size_preimage_embed_subset_range _ _ hX],
    rw image_preimage_eq_of_subset hX, },
  rintros ⟨S, C, hdisj, hsize, hr⟩, 
  rw [eq_comm, ← size_fin' _ (le_trans ha hab)] at hsize, 
  obtain ⟨φ, rfl⟩ := exists_emb_of_type_size_eq_size_set hsize,   
  refine ⟨φ, C, hdisj, λ F, _⟩, 
  convert hr (φ '' F) (λ x, by tidy), 
  rw [size_image_emb, canonical_unif_r ha], 
end

lemma has_good_C_of_has_unif_minor (ha : 0 ≤ a) (hab : a ≤ b) :
  M.has_unif_minor a b → 
    ∃ S C : set α,  disjoint S C 
                  ∧ size S = b 
                  ∧ (∀ X ⊆ S, min a (size X) = M.r (X ∪ C) - M.r C)
                  ∧ M.is_indep C 
                  ∧ M.r C = M.r univ - a :=
begin
  rw [has_unif_minor_def, iminor_of_iff_exists_good_C], 
  rintros ⟨ φ, C, hdisj, hr, hind, hrank⟩, 
  refine ⟨range φ, C, (disjoint_iff_inter_eq_empty.mpr hdisj), _, λ X hX, _, hind, _⟩,
  { rw [← image_univ, size_image_emb, size_fin'_univ], exact le_trans ha hab,  },
  { convert hr (φ ⁻¹' X), 
    rw [canonical_unif_r ha, size_preimage_embed_subset_range _ _ hX],
    rw image_preimage_eq_of_subset hX}, 
  rw [canonical_unif_r ha, ← type_size_eq, size_fin' _ (le_trans ha hab), min_eq_left hab] at hrank, 
  linarith,  
end

def matroid.has_unif_restr (M : matroid α) (a b : ℤ) :=
  M.has_irestr (canonical_unif a b)

lemma has_unif_restr_def :
  M.has_unif_restr a b ↔ (canonical_unif a b).is_irestr_of M := 
iff.rfl 

lemma has_unif_restr_iff (ha : 0 ≤ a) (hab : a ≤ b) :
  M.has_unif_restr a b ↔ ∃ S : set α, (size S = b) ∧ (∀ X ⊆ S, M.r X = min a (size X)) :=
begin
  rw [has_unif_restr_def, irestr_of_iff_exists_map],  
  split, 
  { rintros ⟨φ, hr⟩, 
    refine ⟨range φ, _, λ X hX, _⟩,
    { rw [← image_univ, size_image_emb], convert size_fin' _ (le_trans ha hab)},
    convert (hr (φ ⁻¹' X)).symm using 1,
    rw image_preimage_eq_of_subset hX, 
    rw [canonical_unif_r ha, size_preimage_embed_subset_range _ _ hX],  }, 
  rintros ⟨S, hsize, hr⟩, 
  rw [eq_comm, ← size_fin' _ (le_trans ha hab)] at hsize, 
  obtain ⟨φ, rfl⟩ := exists_emb_of_type_size_eq_size_set hsize,   
  refine ⟨φ, λ F, _⟩, 
  convert (hr (φ '' F) (λ x, by tidy)).symm using 1, 
  rw [size_image_emb, canonical_unif_r ha], 
end

lemma matroid.has_unif_minor_iff_si_has_unif_minor {M : matroid α} {a b : ℤ} {ha : 2 ≤ a} :
  M.has_unif_minor a b ↔ (si M).has_unif_minor a b := 
(iminor_iff_iminor_si (canonical_unif_simple_of_two_le_r ha)).symm

end uniform

section line

variables {α : Type u} [fintype α] {M : matroid α} {a b : ℤ} 


end line 
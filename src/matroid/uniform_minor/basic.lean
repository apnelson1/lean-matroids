import prelim.collections prelim.embed prelim.size prelim.induction prelim.minmax finsum.fin_api
import matroid.pointcount matroid.simple 
import matroid.submatroid.projection matroid.submatroid.minor_iso 
import matroid.constructions.uniform 

noncomputable theory 
open_locale classical big_operators 

open set matroid 

variables {α : Type}[fintype α]{M : matroid α}

def ground (b : ℤ) := fin (b.to_nat)
instance ground_fin {b : ℤ}: fintype (ground b) := by {unfold ground, apply_instance}

@[simp] lemma ground_type_size {b : ℤ}(hb : 0 ≤ b): type_size (ground b) = b := 
by simp [ground, int.to_nat_of_nonneg hb]

@[simp] lemma ground_univ_size {b : ℤ}(hb : 0 ≤ b): size (univ : set (ground b)) = b := 
by rw [← type_size_eq, ground_type_size hb]

/-- the rank-a uniform matroid on b elements with ground set (fin b). Junk unless 0 ≤ a ≤ b -/
def canonical_unif (a b : ℤ): 
  matroid (ground b) := 
unif.uniform_matroid_on (ground b) a

lemma canonical_unif_simple_iff {a b : ℤ}(ha : 0 ≤ a)(hb : 2 ≤ b): 
  (canonical_unif a b).is_simple ↔ 2 ≤ a := 
begin
 convert unif.uniform_matroid_simple_iff (ground b) _ ha, 
 rwa ground_type_size (by linarith : 0 ≤ b), 
end

lemma canonical_unif_simple_of_two_le_r {a b : ℤ}(ha : 2 ≤ a): 
  (canonical_unif a b).is_simple :=
unif.unif_simple_of_two_le_r _ ha

@[simp] lemma canonical_unif_r {a b : ℤ}(ha : 0 ≤ a)(X : set (ground b)):
  (canonical_unif a b).r X = min a (size X) :=
unif.uniform_matroid_rank ha _

/-- the property of having a U_{a,b}-minor -/
def matroid.has_unif_minor (M : matroid α) (a b : ℤ) :=
  M.has_iminor (canonical_unif a b)

lemma has_unif_minor_def {M : matroid α} {a b : ℤ} : 
  M.has_unif_minor a b ↔ (canonical_unif a b).is_iminor_of M := 
iff.rfl 

lemma has_unif_minor_def' {M : matroid α} {a b : ℤ} : 
  M.has_unif_minor a b ↔ M.has_iminor (canonical_unif a b) := 
iff.rfl 

lemma has_unif_minor_iff_embedding {M : matroid α} {a b : ℤ}(ha : 0 ≤ a)(hab : a ≤ b) :
  M.has_unif_minor a b ↔ 
    ∃ S C : set α,  disjoint S C 
                  ∧ size S = b 
                  ∧ ∀ X ⊆ S, min a (size X) = M.r (X ∪ C) - M.r C :=
begin
  rw [has_unif_minor_def, iminor_of_iff_exists_embedding], 
  split, 
  { rintros ⟨ φ, C, hdisj, hr⟩, 
    refine ⟨range φ, C, hdisj, _, λ X hX, _⟩,
    { rw [← image_univ, size_img_emb, ground_univ_size], exact le_trans ha hab,  },
    convert hr (φ ⁻¹' X), 
    rw [canonical_unif_r ha, size_preimage_embed_subset_range _ _ hX],
    rw image_preimage_eq_of_subset hX, },
  rintros ⟨S, C, hdisj, hsize, hr⟩, 
  

end

def matroid.has_unif_restr (M : matroid α) (a b : ℤ) :=
  M.has_irestr (canonical_unif a b)



lemma matroid.has_unif_minor_iff_si_has_unif_minor {M : matroid α} {a b : ℤ} {ha : 2 ≤ a} :
  M.has_unif_minor a b ↔ (si M).has_unif_minor a b := 
(iminor_iff_iminor_si (canonical_unif_simple_of_two_le_r ha)).symm


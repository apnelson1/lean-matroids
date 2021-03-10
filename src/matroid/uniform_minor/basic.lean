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

/-- the property of having a U_{a,b}-minor -/
def matroid.has_unif_minor (M : matroid α)(a b : ℤ) :=
  M.has_iminor (canonical_unif a b)

lemma has_unif_minor_def {M : matroid α}{a b : ℤ}: 
  M.has_unif_minor a b ↔ (canonical_unif a b).is_iminor_of M := 
iff.rfl 

lemma has_unif_minor_def' {M : matroid α}{a b : ℤ}: 
  M.has_unif_minor a b ↔ M.has_iminor (canonical_unif a b) := 
iff.rfl 

lemma matroid.has_unif_minor_iff_si_has_unif_minor {M : matroid α}{a b : ℤ}{ha : 2 ≤ a} :
  M.has_unif_minor a b ↔ (si M).has_unif_minor a b := 
(iminor_iff_iminor_si (canonical_unif_simple_of_two_le_r ha)).symm


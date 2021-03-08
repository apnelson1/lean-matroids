import prelim.collections prelim.embed prelim.size prelim.induction prelim.minmax finsum.fin_api
import matroid.pointcount 
import matroid.submatroid.projection matroid.submatroid.minor_iso 
import matroid.constructions.uniform 

noncomputable theory 
open_locale classical big_operators 

open set matroid 

variables {α : Type}[fintype α]{M : matroid α}

def ground (b : ℤ) := fin (int.nat_abs b)
instance ground_fin {b : ℤ}: fintype (ground b) := by {unfold ground, apply_instance}

/-- the rank-a uniform matroid on b elements with ground set (fin b). Junk unless 0 ≤ a ≤ b -/
def canonical_unif (a b : ℤ): 
  matroid (ground b) := 
unif.uniform_matroid_on (ground b) a



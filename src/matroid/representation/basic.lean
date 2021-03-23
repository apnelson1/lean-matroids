import matroid.rankfun 
import linear_algebra.finite_dimensional

noncomputable theory 
open_locale classical 

open finite_dimensional
variables {α : Type*} [fintype α] {𝔽 : Type*} [field 𝔽] 


def proj_to_set (𝔽 : Type*) [field 𝔽] (X : set α) := linear_map.fun_left 𝔽 𝔽 (coe : X → α)

def proj_subspace_to_set (R : submodule 𝔽 (α → 𝔽)) (X : set α) := 
  submodule.map (proj_to_set 𝔽 X) R 

def is_matroid_rep (R : submodule 𝔽 ( α → 𝔽 )) (M : matroid α) := 
  ∀ X : set α, ( findim 𝔽 (proj_subspace_to_set R X) : ℤ) = M.r X 
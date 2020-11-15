/-
Copyright (c) 2019-2020 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen (with help from Mario Carneiro, Chris Hughes,
Kenny Lau and others in the Leanprover Zulip chat room).
-/
--import for_mathlib
import data.finset data.equiv.list

/-!
Matroids, after Chapter 1 of Oxley, Matroid Theory, 1992.

We begin with the two axiomatizations of matroids defined in Whitney's 1935 paper:
- matroids from independent sets
- matroids from circuits

Everything in this file is under the `matroid` namespace, so we have named the two
structures `of_indep` and `of_circuits`, respectively, so that their fully-qualified
names are `matroid.of_indep` and `matroid.of_circuits`.

-/

open finset

/-! § 1.1 Independent sets and circuits.
-/

namespace matroid

variables (E : Type*) [decidable_eq E] [fintype E]

/-- `of_indep E` is the type of matroids in the independent set representation
with ground set `E` (encoded in Lean as a `fintype`).

It has the following fields:
- `indep : finset (finset E)` : the set of independent subsets of E
- `empty_mem_indep` : axiom (I1), the empty set is independent.
- `indep_of_subset_indep` : axiom (I2), subsets of independent sets are independent.
- `indep_exch` : axiom (I3), the exchange axiom. Given two independent sets `x`, `y` with `x.card < y.card`, there exists `e ∈ y \ x` such that `insert e x` is independent.
-/
structure of_indep :=
(indep : finset (finset E))
-- (I1)
(empty_mem_indep : ∅ ∈ indep)
-- (I2)
(indep_of_subset_indep {x y : finset E} (hx : x ∈ indep) (hyx : y ⊆ x) : y ∈ indep)
-- (I3)
(indep_exch {x y : finset E} (hx : x ∈ indep) (hy : y ∈ indep) (hcard : card x < card y)
  : ∃ e, e ∈ y \ x ∧ insert e x ∈ indep)

namespace of_indep

variable {E}

end of_indep

end matroid

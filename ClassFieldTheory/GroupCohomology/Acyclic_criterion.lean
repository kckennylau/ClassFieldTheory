import Mathlib
import ClassFieldTheory.GroupCohomology._2_Acyclic_def
import ClassFieldTheory.GroupCohomology.CyclicGroup_v2

open
  CategoryTheory
  CategoryTheory.Limits
  groupCohomology

variable {R : Type} [CommRing R]
variable {G : Type} [Group G]

/--
If `H¹(H,M)` and `H²(H,M)` are both zero for every subgroup of `G` then `M` is acyclic.
-/
theorem groupCohomology.Acyclic_ofH1_ofH2_of_solvable [Finite G] [IsSolvable G]
    (M : Rep R G)
    (h1 : ∀ H : Subgroup G, IsZero (H1 (M ↓ H)))
    (h2 : ∀ H : Subgroup G, IsZero (H2 (M ↓ H))) :
    M.IsAcyclic := by
  /-
  This is proved by induction on `H`.
  If `H` is the trivial subgroup then the result is true.
  Assume that the result is true for every proper subgroup of `H`, and choose a
  normal subgroup `K` of `H` such that `H ⧸ K` is cyclic. We are therefore assuming
  than the restriction of `M` to `K` is acyclic.

  Since `M` is `K`-acyclic, we have for every `n > 0` an inflation-restriction sequence:

    `0 ⟶ Hⁿ(H/K,Mᴷ) ⟶ Hⁿ(H,M) ⟶ Hⁿ(K,M)`.

  as the last term is zero, we have isomorphisms `Hⁿ(H/K,Mᴷ) ≅ Hⁿ(H,M)` for all `n > 0`.
  In particular `H¹(H/K,Mᴷ)` and `H²(H/K,Mᴷ)` are both zero.
  By the periodicity of the cohomology of a cyclic group, `Hⁿ(H/K,Mᴷ)` is zero for all `n > 0`.
  Therefore `Hⁿ(H,M)=0` for all `n > 0`.
  -/
  sorry

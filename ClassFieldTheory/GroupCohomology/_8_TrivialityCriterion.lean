import Mathlib
import ClassFieldTheory.GroupCohomology._1_TateCohomology_def
import ClassFieldTheory.GroupCohomology._2_TrivialCohomology
import ClassFieldTheory.GroupCohomology._5_DimensionShift
import ClassFieldTheory.GroupCohomology._7_inflationRestriction
import ClassFieldTheory.GroupCohomology._6_CyclicGroup_v2

open
  CategoryTheory
  CategoryTheory.Limits
  groupCohomology
  Rep
  dimensionShift

variable {R : Type} [CommRing R]
variable {G : Type} [Group G]

/--
If `H²ⁿ⁺²(H,M)` and `H²ᵐ⁺¹(H,M)` are both zero for every subgroup `H` of `G` then `M` is acyclic.
-/
theorem groupCohomology.trivialCohomology_of_even_of_odd_of_solvable [Finite G] [IsSolvable G]
    (M : Rep R G) (n m : ℕ)
    (h_even : ∀ (H : Subgroup G) [DecidableEq H], IsZero (groupCohomology (M ↓ H) (2 * n + 2)))
    (h_odd : ∀ (H : Subgroup G) [DecidableEq H], IsZero (groupCohomology (M ↓ H) (2 * m + 1))) :
    M.TrivialCohomology := by
  /-
  This is proved by induction on `H`.
  If `H` is the trivial subgroup then the result is true.
  Assume that the result is true for every proper subgroup of `H`, and choose a
  normal subgroup `K` of `H` such that `H ⧸ K` is cyclic. We are therefore assuming
  that the restriction of `M` to `K` is acyclic.

  Since `M` is `K`-acyclic, we have for every `r > 0` an inflation-restriction sequence:

    `0 ⟶ Hʳ(H/K,Mᴷ) ⟶ Hʳ(H,M) ⟶ Hʳ(K,M)`.

  as the last term is zero, we have isomorphisms `Hʳ(H/K,Mᴷ) ≅ Hʳ(H,M)` for all `r > 0`.
  In particular `H²ⁿ⁺²(H/K,Mᴷ)` and `H²ᵐ⁺¹(H/K,Mᴷ)` are both zero.
  By the periodicity of the cohomology of a cyclic group, `Hʳ(H/K,Mᴷ)` is zero for all `r > 0`.
  Therefore `Hʳ(H,M)=0` for all `r > 0`.
  -/
  sorry

theorem groupCohomology.trivialCohomology_of_even_of_odd [Finite G]
    (M : Rep R G) (n m : ℕ)
    (h_even : ∀ (H : Subgroup G) [DecidableEq H], IsZero (groupCohomology (M ↓ H) (2 * n + 2)))
    (h_odd : ∀ (H : Subgroup G) [DecidableEq H], IsZero (groupCohomology (M ↓ H) (2 * m + 1))) :
    M.TrivialCohomology := by
  sorry


instance Rep.dimensionShift.up_trivialCohomology [Finite G] (M : Rep R G) [M.TrivialCohomology] :
    (up.obj M).TrivialCohomology := sorry

instance Rep.dimensionShift.down_trivialCohomology [Finite G] (M : Rep R G) [M.TrivialCohomology] :
    (down.obj M).TrivialCohomology := sorry

lemma groupCohomology.TateCohomology_of_trivialCohomology [Finite G] [DecidableEq G] (M : Rep R G)
    [M.TrivialCohomology] (n : ℤ) : IsZero ((TateCohomology n).obj M) := sorry

instance Rep.trivialHomology_of_trivialCohomology [Finite G] (M : Rep R G) [M.TrivialCohomology] :
    M.TrivialHomology := sorry

import Mathlib
import ClassFieldTheory.GroupCohomology._0_Current_PRs
import ClassFieldTheory.GroupCohomology._1_inflation
import ClassFieldTheory.GroupCohomology._2_Acyclic_def
import ClassFieldTheory.GroupCohomology._5_DimensionShift

noncomputable section

open
  Rep
  dimensionShift
  groupCohomology
  CategoryTheory
  Limits

variable {R : Type} [CommRing R]
variable {G : Type} [Group G] (H : Subgroup G) [H.Normal]

def inflationRestriction (n : ℕ) (M : Rep R G) : ShortComplex (ModuleCat R) where
  X₁ := groupCohomology (M ↑ H) (n + 1)
  X₂ := groupCohomology M (n + 1)
  X₃ := groupCohomology (M ↓ H) (n + 1)
  f := (infl H (n + 1)).app M
  g := (rest H (n + 1)).app M
  zero := sorry -- uses current PR for definitions.


theorem inflation_restriction_mono (n : ℕ) {M : Rep R G}
    (hM : ∀ i : ℕ, i < n → IsZero (groupCohomology (M ↓ H) (i + 1))) :
    Mono (inflationRestriction H (n + 1) M).f :=
  /-
  The proof is by induction on `n`. The `H¹` case (i.e. `n = 0`) is in Mathlib.
  For the inductive step, use the fact that the following square commutes by `infl_δ_naturality`.

  ` Hⁿ⁺¹(G⧸H,Mᴴ)     ⟶  Hⁿ⁺¹(G,M)    `
  `     |                   |        `
  ` Hⁿ(G⧸H,(up M)ᴴ)  ⟶  Hⁿ(G,up M)   `

  The vertical maps are the dimension-shifting isomorphisms.
  -/
  sorry

theorem inflation_restriction_exact (n : ℕ) {M : Rep R G}
    (hM : ∀ i : ℕ, i < n → IsZero (groupCohomology (M ↓ H) (i + 1))) :
    (inflationRestriction H (n + 1) M).Exact :=
  /-
  The proof is by induction on `n`. The `H¹` case (i.e. `n = 0`) is a current PR.
  For the inductive step, use the fact that the following diagram commutes by
  `infl_δ_naturality` and `rest_δ_naturality`.

  ` Hⁿ⁺¹(G⧸H,Mᴴ)     ⟶    Hⁿ⁺¹(G,Mᴴ)     ⟶    Hⁿ⁺¹(H,M)   `
  `       |                   |                   |       `
  ` Hⁿ(G⧸H,(up M)ᴴ)  ⟶    Hⁿ(G,(up M)ᴴ)  ⟶    Hⁿ(H,up M)  `

  The vertical maps are the dimension-shifting isomorphisms.
  -/
  sorry


end

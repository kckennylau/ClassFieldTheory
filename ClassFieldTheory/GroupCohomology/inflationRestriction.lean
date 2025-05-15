import Mathlib
import ClassFieldTheory.GroupCohomology._0_Current_PRs
import ClassFieldTheory.GroupCohomology._1_inflation
import ClassFieldTheory.GroupCohomology._2_Acyclic_def
import ClassFieldTheory.GroupCohomology._4_DimensionShift

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

/--
A weak form of the inflation restriction sequence.
This states the existence of a sequence but doesn't describe the maps.
It's sufficient for proving that various cohomology groups are trivial.

To prove a stronger version, we need that inflation and restriction commute with the
connecting homomorphisms defined by short exact sequences.
-/
theorem  weak_inflation_restriction (n : ℕ) {M : Rep R G}
    (hM : ∀ i : ℕ, i < n → IsZero (groupCohomology (M ↓ H) (i + 1))) :
    ∃ infRes : ShortComplex (ModuleCat R),
    ∃ φ₁ : infRes.X₁ ≅ groupCohomology (M.quotientToInvariants H) (n + 1),
    ∃ φ₂ : infRes.X₂ ≅ groupCohomology M (n + 1),
    ∃ φ₃ : infRes.X₂ ≅ groupCohomology (M ↓ H) (n + 1),
    infRes.Exact ∧ Mono infRes.f := by
  revert M
  induction n with
  | zero =>
    -- from current PR.
    sorry
  | succ n ih =>
    intro M hM
    have iso₁ {i : ℕ} : groupCohomology ((up.obj M).quotientToInvariants H) (i + 1)
        ≅ groupCohomology (M.quotientToInvariants H) (i + 2)
    · /-
      By `hM`, we have `H¹(H,M)= 0` so we have a short exact sequence

        `0 ⟶ Mᴴ ⟶ (coind'₁ M)ᴴ ⟶ (up M)ᴴ ⟶ 0`.

      The isomorphism required is the connecting homomorphism in `G ⧸ H`-cohomology
      from this short exact sequence. It is a isomorphism because `(coind'₁ M)ᴴ` is acyclic.
      -/
      specialize hM 0 (Nat.zero_lt_succ n)
      sorry
    have iso₂ {i : ℕ} : groupCohomology (up.obj M) (i + 1) ≅ groupCohomology M (i + 2)
    · apply up_δiso M i
    have iso₃ {i : ℕ} : groupCohomology ((up.obj M) ↓ H) (i + 1) ≅ groupCohomology (M ↓ H) (i + 1 + 1)
    · apply up_δiso' M H i
    have : ∀ i, (i < n → IsZero (groupCohomology ((up.obj M) ↓ H) (i + 1)))
    · intro i hi
      exact IsZero.of_iso (hM _ (by simpa)) iso₃
    specialize ih this
    obtain ⟨S, φ₁, φ₂, φ₃, hS₁, hS₂⟩ := ih
    use S
    use φ₁ ≪≫ iso₁
    use φ₂ ≪≫ iso₂
    use φ₃ ≪≫ iso₃



theorem inflation_restriction_mono (n : ℕ) {M : Rep R G}
    (hM : ∀ i : ℕ, i < n → IsZero (groupCohomology (M ↓ H) (i + 1))) :
    Mono (inflationRestriction H (n + 1) M).f :=
  /-
  The proof is by induction on `n`. The `H¹` case (i.e. `n = 0`) is a current PR.
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

import Mathlib
import ClassFieldTheory.GroupCohomology.Current_PRs
import ClassFieldTheory.GroupCohomology.Acyclic
import ClassFieldTheory.GroupCohomology.DimensionShift

open Rep
  groupCohomology
  CategoryTheory
  Limits

variable {R : Type} [CommRing R]
variable {G : Type} [Group G]


/--
We shall construct this by induction on `n` by dimension-shifting.
The case `n = 1` is a current PR. The induction step is
-/
noncomputable def H1InfRes' (H : Subgroup G) [H.Normal] (n : ℕ) (M : Rep R G)
    --(hM : ∀ i : ℕ, i ≤ n → IsZero (groupCohomology (M ↓ H) i))
    : ShortComplex (ModuleCat R) := by
  induction n with
  | zero =>  exact {
      X₁ := groupCohomology (M.quotientToInvariants H) 1
      X₂ := groupCohomology M 1
      X₃ := groupCohomology (M ↓ H) 1
      f := map (QuotientGroup.mk' H) sorry 1
      g := map H.subtype (𝟙 _) 1
      zero := sorry
    }
  | succ n _ => exact {
      X₁ := groupCohomology (M.quotientToInvariants H) (n + 1)
      X₂ := groupCohomology M (n + 1)
      X₃ := groupCohomology (M ↓ H) (n + 1)
      f := sorry
      g := sorry
      zero := sorry
    }

theorem  H1InfRes'_Exact {M : Rep R G} (H : Subgroup G) [H.Normal] (n : ℕ)
    (hM : ∀ i : ℕ, i ≤ n → IsZero (groupCohomology (M ↓ H) i)) :
    (H1InfRes' H n M).Exact :=
  sorry

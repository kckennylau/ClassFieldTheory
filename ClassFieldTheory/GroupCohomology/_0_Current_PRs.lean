import Mathlib

open CategoryTheory
    Rep

variable {R : Type} [CommRing R]
variable {G : Type} [Group G] [DecidableEq G]

noncomputable section Long_Exact_Sequences

namespace groupCohomology
/--
# Leave this as a sorry, and then remove once Amelia's PR 25872 on long exact sequences is merged.

(This has the same name and Type as in PR 25872.)

The connecting homomorphism in the long exact sequence in group cohomology.
-/
def δ {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (i j : ℕ) (hij : i + 1 = j) :
    groupCohomology S.X₃ i ⟶ groupCohomology S.X₁ j := sorry

def longExactSequence₁ {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : ℕ) :
  ShortComplex (ModuleCat R) where
    X₁ := groupCohomology S.X₁ n
    X₂ := groupCohomology S.X₂ n
    X₃ := groupCohomology S.X₃ n
    f := groupCohomology.map (MonoidHom.id G) S.f n
    g := groupCohomology.map (MonoidHom.id G) S.g n
    zero := sorry

def longExactSequence₂ {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : ℕ) :
  ShortComplex (ModuleCat R) where
    X₁ := groupCohomology S.X₂ n
    X₂ := groupCohomology S.X₃ n
    X₃ := groupCohomology S.X₁ (n + 1)
    f := groupCohomology.map (MonoidHom.id G) S.g n
    g := groupCohomology.δ hS n (n+1) rfl
    zero := sorry

def longExactSequence₃ {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : ℕ) :
  ShortComplex (ModuleCat R) where
    X₁ := groupCohomology S.X₃ n
    X₂ := groupCohomology S.X₁ (n + 1)
    X₃ := groupCohomology S.X₂ (n + 1)
    f := groupCohomology.δ hS n (n+1) rfl
    g := groupCohomology.map (MonoidHom.id G) S.f (n + 1)
    zero := sorry

lemma isLongExact₁ {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : ℕ) :
    (longExactSequence₁ hS n).Exact := sorry
lemma isLongExact₂ {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : ℕ) :
    (longExactSequence₁ hS n).Exact := sorry
lemma isLongExact₃ {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : ℕ) :
    (longExactSequence₁ hS n).Exact := sorry

end groupCohomology
end Long_Exact_Sequences


noncomputable section Homology -- from #25880

def groupHomology.chainsMap {H : Type} [Group H] [DecidableEq H]
    (f : G →* H) {M : Rep R G} {M' : Rep R H}
    (φ : M ⟶ (Action.res (ModuleCat R) f).obj M') : inhomogeneousChains M ⟶ inhomogeneousChains M'
    := sorry

def groupHomology.map {H : Type} [Group H] [DecidableEq H] (f : G →* H) {M : Rep R G} {M' : Rep R H}
    (φ : M ⟶ (Action.res (ModuleCat R) f).obj M') (n : ℕ) : groupHomology M n ⟶ groupHomology M' n
    := sorry

def groupHomology.one_trivial_int_iso :
    groupHomology (trivial ℤ G ℤ) 1 ≅ ModuleCat.of ℤ (Additive (Abelianization G)) := sorry

end Homology

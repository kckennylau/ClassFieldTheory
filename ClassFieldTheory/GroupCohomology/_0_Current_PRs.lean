import Mathlib

open CategoryTheory
    Rep

variable {R : Type} [CommRing R]
variable {G : Type} [Group G] [DecidableEq G]

noncomputable section Long_Exact_Sequences

namespace groupCohomology

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

def groupHomology.one_trivial_int_iso :
    groupHomology (trivial ℤ G ℤ) 1 ≅ ModuleCat.of ℤ (Additive (Abelianization G)) := sorry

end Homology


-- # 25937
/-- Shapiro's lemma: given a finite index subgroup `S ≤ G` and an `S`-representation `A`, we have
`Hⁿ(G, Coind_S^G(A)) ≅ Hⁿ(S, A).` -/
noncomputable def coindIso [DecidableEq G] (S : Subgroup G) (A : Rep R S) (n : ℕ) :
    groupCohomology (coind S.subtype A) n ≅ groupCohomology A n :=
  sorry

-- # 25996
/-- Shapiro's lemma: given a finite index subgroup `S ≤ G` and an `S`-representation `A`, we have
`Hₙ(G, Ind_S^G(A)) ≅ Hₙ(S, A).` -/
noncomputable def indIso [DecidableEq G] (S : Subgroup G) (A : Rep R S) (n : ℕ) :
    groupHomology (ind S.subtype A) n ≅ groupHomology A n :=
  sorry

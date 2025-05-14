import Mathlib

open CategoryTheory

variable {R : Type} [CommRing R]
variable {G : Type} [Group G]

noncomputable section Long_Exact_Sequences

namespace groupCohomology
/--
# Leave this as a sorry, and then remove once Amelia's PR 21760 on long exact sequences is merged.

(This has the same name and Type as in PR 21760.)

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


section Inflation_Restriction

namespace groupCohomology

abbrev _root_.Rep.quotientToInvariants (M : Rep R G) (S : Subgroup G) [S.Normal] : Rep R (G ⧸ S) :=
  sorry

variable (M : Rep R G) (S : Subgroup G) [S.Normal]

@[simps X₁ X₂ X₃]
noncomputable def H1InfRes :
    ShortComplex (ModuleCat R) where
  X₁ := H1 (M.quotientToInvariants S)
  X₂ := H1 M
  X₃ := H1 ((Action.res _ S.subtype).obj M)
  f := H1Map (QuotientGroup.mk' S) sorry
  g := H1Map S.subtype (𝟙 _)
  zero := sorry

/-- The inflation map `H¹(G ⧸ S, A^S) ⟶ H¹(G, A)` is a monomorphism. -/
instance : Mono (H1InfRes M S).f := sorry

/-- Given a `G`-representation `A` and a normal subgroup `S ≤ G`, the short complex
`H¹(G ⧸ S, A^S) ⟶ H¹(G, A) ⟶ H¹(S, A)` is exact. -/
lemma H1InfRes_exact : (H1InfRes M S).Exact :=sorry

end groupCohomology

end Inflation_Restriction


noncomputable section Homology -- from #21740, #21754

def groupHomology.inhomogeneousChains (M : Rep R G) :
    ChainComplex (ModuleCat R) ℕ := sorry

def groupHomology (M : Rep R G) (n : ℕ) : ModuleCat R :=
  (groupHomology.inhomogeneousChains M).homology n

def groupHomology.chainsMap {H : Type} [Group H] (f : G →* H) {M : Rep R G} {M' : Rep R H}
    (φ : M ⟶ (Action.res (ModuleCat R) f).obj M') : inhomogeneousChains M ⟶ inhomogeneousChains M'
    := sorry

def groupHomology.Map {H : Type} [Group H] (f : G →* H) {M : Rep R G} {M' : Rep R H}
    (φ : M ⟶ (Action.res (ModuleCat R) f).obj M') (n : ℕ) : groupHomology M n ⟶ groupHomology M' n
    := sorry

end Homology

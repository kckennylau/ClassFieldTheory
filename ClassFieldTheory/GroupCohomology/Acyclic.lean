import Mathlib
import ClassFieldTheory.GroupCohomology.Current_PRs
import ClassFieldTheory.GroupCohomology.restriction

/-!
An object `M : Rep R G` is called acyclic if
`Hⁿ(H,M)=0` for all `n > 0` and all subgroup `H` of `G`.

We prove that if `G` is a finite solvable group, and `H¹(H,M) = H²(H,M) = 0` for
all subgroup `H` of `G` then `M` is acyclic. This is used in proving that `split σ` is
acyclic, where `σ` is a 2-cocycle in a finite class formation.

The proof requires the inflation-restriction sequence in the following generality:

Let `H` be a normal subgroup of `G` and assume that `Hʳ(H,M) = 0` for all `0 < r < n`. Then we have an
exact sequence

  0 ⟶ Hⁿ(G ⧸ H, Mᴴ) ⟶ Hⁿ(G,M) ⟶ Hⁿ(H,M).

Note that the result remains true without the assumption that `G` is solvable. The more general
result is needed for global class field theory but not local class field theory because the Galois
groups of extensions of local fields are solvable.

The proof of the more general result requires the corestriction map `Cor : Hⁿ(H,M) ⟶ Hⁿ(G,M)`.
One shows that if `σ` is a non-zero cohomology class, then there exists a prime `p` such that the
restriction of `σ` to the `p`-Sylow subgroup is non-zero. However the `p`-Sylow subgroups are
solvable so we get a contradiction.

Once #22653 is merged, we can state the more general version of inflation-restriction.
-/

-- # requires #22653

open
  CategoryTheory
  CategoryTheory.Limits
  groupCohomology

variable {R : Type} [CommRing R]
variable {G : Type} [Group G]


-- # To be removed after PR merged:
/--
The `H`-invariants of a representation of `G`, regarded as a representation of `G ⧸ H`.
-/
def Rep.invariants' (H : Subgroup G) [H.Normal] : Rep R G ⥤ Rep R (G ⧸ H) := sorry

def Rep.coinduced (H : Subgroup G) : Rep R H ⥤ Rep R G := sorry



/--
A representation `M : Rep R G` is acyclic if the cohomology groups `Hⁿ(H,M)` are all zero
for every subgroup `H` of `G` and every `n > 0`.
-/
def Rep.IsAcyclic (M : Rep R G) : Prop :=
  ∀ (H : Subgroup G), ∀ n : ℕ, IsZero (groupCohomology (M ↓ H) n.succ)

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

noncomputable section
namespace groupCohomology


--In this section, only the last sorry can be removed until #21760 is merged.
--The other lines are a `sorry` version on long exact sequences.


lemma groupCohomology.isIso_of_acyclic {S : ShortComplex (Rep R G)}
    (short_exact : S.ShortExact) (acyclic : S.X₂.IsAcyclic) (n : ℕ) :
    IsIso (groupCohomology.δ short_exact (n + 1) (n + 2) rfl) := by
  sorry

end groupCohomology
end

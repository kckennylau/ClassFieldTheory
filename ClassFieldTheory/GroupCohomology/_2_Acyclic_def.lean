import Mathlib
import ClassFieldTheory.GroupCohomology._1_Basic
import ClassFieldTheory.GroupCohomology._1_restriction

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

variable {R G : Type _} [CommRing R]  [Group G]
/--
A representation `M : Rep R G` is acyclic if the cohomology groups `Hⁿ(H,M)` are all zero
for every subgroup `H` of `G` and every `n > 0`.
-/
def Rep.IsAcyclic (M : Rep R G) : Prop :=
  ∀ (H : Subgroup G), ∀ n : ℕ, IsZero (groupCohomology (M ↓ H) (n + 1))

lemma Rep.isAcyclic_of_iso {M N : Rep R G} (f : M ≅ N) (hN : N.IsAcyclic) : M.IsAcyclic := by
  intro H n
  have : (functor R H n.succ).obj (M ↓ H) ≅ (functor R H n.succ).obj (N ↓ H)
  · exact (functor _ _ n.succ).mapIso ((res H).mapIso f)
  apply IsZero.of_iso (hN H n) this

def Rep.IsHomologyAcyclic.{u} (M : Rep R G) : Prop :=
  ∀ (H : Subgroup G), ∀ n : ℕ, IsZero.{u,u+1} (groupHomology (M ↓ H) (n + 1))

lemma Rep.isHomologyAcyclic_of_iso {M N : Rep R G} (f : M ≅ N) (hN : N.IsHomologyAcyclic) :
    M.IsHomologyAcyclic := by
  sorry

lemma groupCohomology.isZero_of_isAcyclic {M : Rep R G} (hM : M.IsAcyclic) (n : ℕ) :
    IsZero (groupCohomology M (n + 1)) := IsZero.of_iso (hM ⊤ n) (rest_top_iso _ _)

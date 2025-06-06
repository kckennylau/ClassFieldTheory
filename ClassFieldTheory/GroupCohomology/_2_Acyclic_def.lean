import Mathlib
import ClassFieldTheory.GroupCohomology._1_Basic
import ClassFieldTheory.GroupCohomology._1_restriction
import ClassFieldTheory.GroupCohomology._1_TateCohomology_def

/-!
An object `M : Rep R G` is has trivial cohomology if
`Hⁿ(H,M)=0` for all `n > 0` and all subgroup `H` of `G`.

We prove that if `G` is a finite solvable group, and `H¹(H,M) = H²(H,M) = 0` for
all subgroup `H` of `G` then `M` has trivial cohomology. This is used in proving that `split σ` has
trivial cohomology, where `σ` is a `2`-cocycle in a finite class formation.

The proof requires the inflation-restriction sequence in the following generality:

Let `H` be a normal subgroup of `G` and assume that `Hʳ(H,M) = 0` for all `0 < r < n`. Then we have an
exact sequence

  `0 ⟶ Hⁿ(G ⧸ H, Mᴴ) ⟶ Hⁿ(G,M) ⟶ Hⁿ(H,M)`.

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
A representation `M : Rep R G` has trivial cohomology if the cohomology groups `Hⁿ(H,M)`
are zero for every subgroup `H` of `G` and every `n > 0`.
-/
class Rep.TrivialCohomology (M : Rep R G) : Prop where
  zero {H : Subgroup G} {n : ℕ} : IsZero (groupCohomology (M ↓ H) (n + 1))

lemma Rep.trivialCohomology_of_iso {M N : Rep R G} (f : M ≅ N) [N.TrivialCohomology] : M.TrivialCohomology := by
  constructor
  intro H n
  have : (functor R H n.succ).obj (M ↓ H) ≅ (functor R H n.succ).obj (N ↓ H)
  · exact (functor _ _ n.succ).mapIso ((res H).mapIso f)
  apply IsZero.of_iso TrivialCohomology.zero this

class Rep.TrivialHomology.{u} (M : Rep R G) : Prop where
  zero (H : Subgroup G) (n : ℕ) : IsZero.{u,u+1} (groupHomology (M ↓ H) (n + 1))

lemma Rep.trivialHomology_of_iso {M N : Rep R G} (f : M ≅ N) [N.TrivialHomology] :
    M.TrivialHomology := by
  sorry

lemma groupCohomology.isZero_of_trivialCohomology {M : Rep R G} [M.TrivialCohomology] (n : ℕ) :
    IsZero (groupCohomology M (n + 1)) :=
  IsZero.of_iso Rep.TrivialCohomology.zero (rest_top_iso _ _)

class Rep.TrivialTateCohomology [Finite G] (M : Rep R G) : Prop where
  zero (H : Subgroup G) (n : ℤ) : IsZero ((TateCohomology (n + 1)).obj (M ↓ H))



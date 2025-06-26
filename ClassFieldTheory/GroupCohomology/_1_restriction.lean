import Mathlib
import ClassFieldTheory.GroupCohomology._1_Basic

open
  Rep
  CategoryTheory
  ConcreteCategory
  Limits
  groupCohomology
  BigOperators

variable {R : Type} [CommRing R]
variable {G : Type} [Group G] [DecidableEq G]

-- # TODO : move this to a more sensible file.
/--
If `M` is a trivial representation of a finite group `G` and `M` is torsion-free
then `H¹(G,M) = 0`.
-/
lemma groupCohomology.H1_isZero_of_trivial (M : Rep R G) [NoZeroSMulDivisors ℕ M] [IsTrivial M]
    [Finite G] : IsZero (H1 M) :=
  /-
  Since `M` is trivial, we can identify `H¹(G,M)` with `Hom(G,M)`, which is zero if
  `M` is finite and `M` is torsion-free.

  This uses `groupCohomology.H1LequivOfIsTrivial`.
  -/
  sorry


noncomputable section

namespace Rep


/--
The restriction functor `Rep R G ⥤ Rep R H` for a subgroup `H` of `G`.
-/
-- abbrev res (H : Subgroup G) : Rep R G ⥤ Rep R H := Action.res (ModuleCat R) H.subtype
abbrev res {H : Type} [Group H] (φ : H →* G) : Rep R G ⥤ Rep R H := Action.res (ModuleCat R) φ

set_option quotPrecheck false in
/--
If `M` is an object of `Rep R G` and `φ : H →* G` then `M ↓ φ` is the restriction of the
representation `M` to `H`, as an object of `Rep R H`.

This is notation for `(Rep.res H).obj M`, which is an abbreviation of
`(Action.res (ModuleCat R) H.subtype).obj M`
-/
notation M "↓" φ => (res φ).obj M

/-
`simp` lemmas for `Action.res` also work for `Rep.res` because it is an abbreviation:
-/
example (M : Rep R G) (H : Type) [Group H] (φ : H →* G) (h : H) :
  (M ↓ φ).ρ h = M.ρ (φ h) := by simp

example (M : Rep R G) (H : Type) [Group H] (φ : H →* G)  :
  (M ↓ φ).V = M.V := by simp

instance (H : Type) [Group H] (f : H →* G) : PreservesLimits (Action.res (ModuleCat.{0} R) f) := by
  apply Action.preservesLimitsOfSize_of_preserves (Action.res (ModuleCat R) f)
  exact Action.preservesLimits_forget (ModuleCat R) G

instance (H : Type) [Group H] (f : H →* G) : ReflectsLimits (Action.res (ModuleCat.{0} R) f) :=
  reflectsLimits_of_reflectsIsomorphisms

instance (H : Type) [Group H] (f : H →* G) : PreservesColimits (Action.res (ModuleCat.{0} R) f) :=
  Action.preservesColimitsOfSize_of_preserves (Action.res (ModuleCat R) f) <|
  Action.preservesColimits_forget (ModuleCat R) G

instance (H : Type) [Group H] (f : H →* G) : ReflectsColimits (Action.res (ModuleCat.{0} R) f) :=
  reflectsColimits_of_reflectsIsomorphisms

/--
The instances above show that the restriction functor `res φ : Rep R G ⥤ Rep R H`
preserves and reflects exactness.
-/
example (H : Type) [Group H] (φ : H →* G) (S : ShortComplex (Rep R G)) :
    (S.map (Rep.res φ)).Exact ↔ S.Exact := by
  rw [ShortComplex.exact_map_iff_of_faithful]



/--
An object of `Rep R G` is zero iff the underlying `R`-module is zero.
-/
lemma isZero_iff (M : Rep R G) : IsZero M ↔ IsZero (M.V) := by
  simp only [IsZero.iff_id_eq_zero]
  apply Action.hom_ext_iff


/--
An object of `Rep R G` is zero iff its restriction to `H` is zero.
-/
lemma isZero_res_iff (M : Rep R G) {H : Type} [Group H] [DecidableEq H] (φ : H →* G) :
    IsZero (M ↓ φ) ↔ IsZero M := by
  simp [isZero_iff]

/--
The restriction functor `res φ : Rep R G ⥤ Rep R H` takes short exact sequences to short
exact sequences.
-/
lemma res_respectsShortExact {H : Type} [Group H] (φ : H →* G) (S : ShortComplex (Rep R G)) :
    (S.map (Rep.res φ)).ShortExact ↔ S.ShortExact :=
  sorry

lemma res_ofShortExact {H : Type} [Group H] (φ : H →* G) {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) : (S.map (Rep.res φ)).ShortExact := by
  rwa [res_respectsShortExact]

lemma res_of_projective (H : Type) [Group H] (φ : H →* G) (inj : Function.Injective φ) {P : Rep R G}
    (hP : Projective P) (H : Subgroup G) : Projective (P ↓ φ) := by
  /-
  *Note : this is probably probably not needed.*

  A representation is projective iff it is a direct summand of a free module over the group ring.
  This lemma follows because "R[G]" is free as an "R[H]"-module (a basis is given by a set of
  coset representatives).
  -/
  sorry

end Rep

namespace groupCohomology

variable [DecidableEq G]

/--
The restriction map `Hⁿ(G,M) ⟶ Hⁿ(H,M)`, defined as a natural transformation:
-/
def rest {H : Type} [Group H] [DecidableEq H] (φ : H →* G) (n : ℕ) :
    functor R G n ⟶ Rep.res φ ⋙ functor R H n  where
  app M               := map φ (𝟙 (M ↓ φ)) n
  naturality M₁ M₂ f  := by
    sorry

lemma rest_app {H : Type} [Group H] [DecidableEq H] (φ : H →* G) (n : ℕ) (M : Rep R G) :
    (rest φ n).app M = map φ (𝟙 (M ↓ φ)) n := rfl


/--
Given any short exact sewuence `0 → A → B → C → 0` in `Rep R G` and any
subgroup `H` of `G`, the following diagram is commutative

  Hⁿ(G,C) ⟶ H^{n+1}(G A)
      |         |
      ↓         ↓
  Hⁿ(H,C) ⟶ H^{n+1}(G A).

The vertical arrows are restriction and the horizontals are connecting homomorphisms.

For this, it would be sensible to define restriction as a natural transformation, so that it
automatically commutes with the other maps. This requires us to first define cohomology as a functor.
-/
lemma rest_δ_naturality {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    {H : Type} [Group H] [DecidableEq H] (φ : H →* G) (i j : ℕ) (hij : i + 1 = j) :
    (δ hS i j hij) ≫ (rest φ j).app S.X₁ = (rest φ i).app S.X₃ ≫ δ (res_ofShortExact φ hS) i j hij
    := by
  /-
  This will essentially be `HomologicalComplex.HomologySequence.δ_naturality`, but it relies on
  the definition of `groupCohomology.δ`, which is a current PR.
  -/
  sorry


-- /--
-- The restriction map in cohomology from `Hⁿ(G,M)` to `Hⁿ(⊤,M ↓ G)` is an isomorphism.
-- This is useful when we have a hypothesis concerning `Hⁿ(H,M ↓ H)` for all subgroups `H` of `G`,
-- for example `Rep.TrivialCohomology`.
-- -/
-- def rest_top_iso (M : Rep R G) (n : ℕ) : groupCohomology M n ≅ groupCohomology (M ↓ ⊤) n where
--   hom := (rest ⊤ n).app M
--   inv := sorry
--   hom_inv_id := sorry
--   inv_hom_id := sorry

end groupCohomology

end

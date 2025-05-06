import Mathlib

open
  Rep
  CategoryTheory
  ConcreteCategory
  Limits
  groupCohomology
  BigOperators

variable {R : Type} [CommRing R]
variable {G : Type} [Group G]

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


section Restriction

namespace Rep


/--
The restriction functor `Rep R G ⥤ Rep R H` for a subgroup `H` of `G`.
-/
abbrev res (H : Subgroup G) : Rep R G ⥤ Rep R H := Action.res (ModuleCat R) H.subtype

set_option quotPrecheck false in
/--
If `M` is an object of `Rep R G` then `M ↓ H` is the restriction of the representation `M` to
a subgroup `H`, as an object of `Rep R H`.

This is notation for `(Rep.res H).obj M`, which is an abbreviation of
`(Action.res (ModuleCat R) H.subtype).obj M`
-/
notation M "↓" H => (res H).obj M

/-
`simp` lemmas for `Action.res` also work for `Rep.res` because it is an abbreviation:
-/
example (M : Rep R G) (H : Subgroup G) (h : H) :
  (M ↓ H).ρ h = M.ρ ↑h := by simp

example (M : Rep R G) (H : Subgroup G) :
  (M ↓ H).V = M.V := by simp

instance (H : Type) [Group H] (f : H →* G) : PreservesLimits (Action.res (ModuleCat R) f) :=
  Action.preservesLimitsOfSize_of_preserves (Action.res (ModuleCat R) f) <|
    Action.preservesLimits_forget (ModuleCat R) G

instance (H : Type) [Group H] (f : H →* G) : ReflectsLimits (Action.res (ModuleCat R) f) :=
  reflectsLimits_of_reflectsIsomorphisms

instance (H : Type) [Group H] (f : H →* G) : PreservesColimits (Action.res (ModuleCat R) f) :=
  Action.preservesColimitsOfSize_of_preserves (Action.res (ModuleCat R) f) <|
    Action.preservesColimits_forget (ModuleCat R) G

instance (H : Type) [Group H] (f : H →* G) : ReflectsColimits (Action.res (ModuleCat R) f) :=
  reflectsColimits_of_reflectsIsomorphisms

/--
The instances above show that the restriction functor `res H : Rep R G ⥤ Rep R H`
preserves and reflects exactness.
-/
example (H : Subgroup G) (S : ShortComplex (Rep R G)) :
    (S.map (res H)).Exact ↔ S.Exact := by
  rw [ShortComplex.exact_map_iff_of_faithful]

/--
An object of `Rep R G` is zero iff the underlying `R`-module is zero.
-/
lemma isZero_iff (M : Rep R G) : IsZero M ↔ IsZero (M.V) := by
  simp only [IsZero.iff_id_eq_zero]
  constructor
  · --This case should follow using the fact that `Action.forget` preserves zero-morphisms.
    intro h
    ext v
    change 𝟙 M v = 0
    rw [h]
    rfl
  · intro h
    ext : 1
    exact h

/--
An object of `Rep R G` is zero iff its restriction to a subgroup is zero.
-/
lemma isZero_res_iff (M : Rep R G) (H : Subgroup G) : IsZero (M ↓ H) ↔ IsZero M := by
  simp [isZero_iff]

/--
The restriction functor `res H : Rep R G ⥤ Rep R H` is takes short exact sequences to short
exact sequences.
-/
lemma res_respectsShortExact (H : Subgroup G) (S : ShortComplex (Rep R G)) :
    (S.map (res H)).ShortExact ↔ S.ShortExact :=
  sorry

lemma res_of_projective {P : Rep R G} (hP : Projective P) (H : Subgroup G) :
    Projective (P ↓ H) := by
  /-
  A representation is projective iff it is a direct summand of a free module over the group ring.
  This lemma follows because "R[G]" is free as an "R[H]"-module (a basis is given by a set of
  coset representatives).

  There is perhaps a better proof than this.
  -/
  sorry

end Rep

end Restriction

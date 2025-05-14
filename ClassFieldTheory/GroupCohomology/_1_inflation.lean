import Mathlib
import ClassFieldTheory.GroupCohomology._0_Current_PRs
import ClassFieldTheory.GroupCohomology._1_Basic
import ClassFieldTheory.GroupCohomology._1_restriction

open CategoryTheory
  Limits
  Rep
  groupCohomology
  HomologicalComplex

variable {R G : Type} [CommRing R] [Group G]

variable (H : Subgroup G) [H.Normal]

def Rep.invariants' (H : Subgroup G) [H.Normal] : Rep R G ⥤ Rep R (G ⧸ H) where
  obj M := M.quotientToInvariants H --current PR
  map f := sorry

instance : (invariants' (R := R) H).PreservesZeroMorphisms := sorry

set_option quotPrecheck false in
/--
`M ↑ H` means the `H` invariants of `M`, as a representation of `G ⧸ H`.
-/
notation M " ↑ " H => (Rep.invariants' H).obj M
--infix : 80 " ↑ " => fun (M : Rep R G) (H : Subgroup G) [H.Normal] ↦ (Rep.invariants' H).obj M



def groupCohomology.cochain_infl :
    invariants' H ⋙ cochainsFunctor R (G ⧸ H) ⟶ cochainsFunctor R G := sorry -- current PR

/--
# TODO :
  move this to the file `Basic.lean`.

The `n`-th group cohomology functor is the composition of the cochains functor and the
`n`-homology functor.
-/
lemma groupCohomology.functor_eq_cochainsFunctor_comp_homology (n : ℕ) :
    functor R G n = cochainsFunctor R G ⋙ homologyFunctor _ _ n := rfl

/--
The inflation map `Hⁿ(G⧸H, M ↑ H) ⟶ Hⁿ(G,M)` as a natural transformation.
This is defined using the inflation map on cocycles.
-/
noncomputable def groupCohomology.infl (n : ℕ) :
    Rep.invariants' H ⋙ (functor R (G ⧸ H) n) ⟶ functor R G n := by
  dsimp only [functor_eq_cochainsFunctor_comp_homology, ←Functor.assoc]
  exact (groupCohomology.cochain_infl H) ◫ 𝟙 _

/--
Suppose we have a short exact sewuence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` in `Rep R G`.
If `H¹(H,A) = 0` then the invariants form a short exact sequence in `Rep R (G ⧸ H)`:

  `0 ⟶ Aᴴ ⟶ Bᴴ ⟶ Cᴴ ⟶ 0`.
-/
lemma invariants'_shortExact_ofShortExact {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    (hS' : IsZero (H1 (S.X₁ ↓ H))) : (S.map (invariants' H)).ShortExact :=
  /-
  This is the opening section of the long exact sequence. The next term is `H¹(H,S.X₁)`, which
  is assumeed to be zero.
  -/
  sorry

/--
Assume that we have a short exact sequence `0 → A → B → C → 0` in `Rep R G`
and that the sequence of `H`- invariants is also a short exact in `Rep R (G ⧸ H)` :

  `0 → Aᴴ → Bᴴ → Cᴴ → 0`.

Then we have a commuting square

`   Hⁿ(G ⧸ H, Cᴴ)  ⟶   H^{n+1}(G ⧸ H, Aᴴ) `
`         |                 |             `
`         ↓                 ↓             `
`     Hⁿ(G , C)    ⟶   H^{n+1}(G,A)       `

where the horizontal maps are connecting homomorphisms
and the vertical maps are inflation.
-/
lemma infl_δ_naturality {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    (hS' : (S.map (invariants' H)).ShortExact)  (i j : ℕ) (hij : i + 1 = j) :
    δ hS' i j hij ≫ (infl H j).app _ = (infl H i).app _ ≫ δ hS i j hij
    := by
  let C := S.map (cochainsFunctor R G)
  let S' := S.map (invariants' H)
  let C' := S'.map (cochainsFunctor R (G ⧸ H))
  let φ : C' ⟶ C := {
    τ₁ := by
        change (cochainsFunctor _ _).obj S'.X₁ ⟶ (cochainsFunctor _ _).obj S.X₁
        exact (cochain_infl H).app S.X₁
    τ₂ := by
        change (cochainsFunctor _ _).obj S'.X₂ ⟶ (cochainsFunctor _ _).obj S.X₂
        exact (cochain_infl H).app S.X₂
    τ₃ := by
        change (cochainsFunctor _ _).obj S'.X₃ ⟶ (cochainsFunctor _ _).obj S.X₃
        exact (cochain_infl H).app S.X₃
    comm₁₂ := ((cochain_infl H).naturality S.f).symm
    comm₂₃ := ((cochain_infl H).naturality S.g).symm
  }
  have ses₁ : C.ShortExact := sorry -- current PR
  have ses₂ : C'.ShortExact := sorry -- current PR
  convert HomologySequence.δ_naturality φ ses₂ ses₁ i j hij
  · sorry --should be `rfl` after defn of `groupCohomology.δ` included in current PR
  · sorry --should be `rfl` after defn of `groupCohomology.δ` included in current PR

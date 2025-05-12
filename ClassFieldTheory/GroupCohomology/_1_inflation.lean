import Mathlib
import ClassFieldTheory.GroupCohomology._0_Current_PRs
import ClassFieldTheory.GroupCohomology._1_Basic
import ClassFieldTheory.GroupCohomology._1_restriction

open CategoryTheory
  Limits
  Rep
  groupCohomology

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


/--
The inflation map `Hⁿ(G⧸H, M ↑ H) ⟶ Hⁿ(G,M)`.
-/
def groupCohomology.infl (n : ℕ) : Rep.invariants' H ⋙ (functor R (G ⧸ H) n) ⟶ functor R G n where
  app M := sorry -- current PR
  naturality := sorry



/--
Suppose we have a short exact sewuence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` in `Rep R G`.
If `H¹(H,A) = 0` then the invariants form a short exact sequence in `Rep R (G ⧸ H)`:

  `0 ⟶ Aᴴ ⟶ Bᴴ ⟶ Cᴴ ⟶ 0`.
-/
lemma infl_ofShortExact {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
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
    (infl H i).app _ ≫ δ hS i j hij = δ hS' i j hij ≫ (infl H j).app _
    := by
  /-
  This will essentially be `HomologicalComplex.HomologySequence.δ_naturality`, but it relies on
  definitions which are current PRs.
  -/
  sorry

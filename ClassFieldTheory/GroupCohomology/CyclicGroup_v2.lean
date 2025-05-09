import Mathlib
import ClassFieldTheory.GroupCohomology.DimensionShift
import ClassFieldTheory.GroupCohomology.LeftRegular

/-!
Let `M : Rep R G`, where `G` is a finite cyclic group.
We construct an isomorphism

  `dimensionShift.up M ≅ dimensionShift.down M`.

Using this, construct isomorphisms

  `Hⁿ(G,M) ≅ H^{n+2}(G,M)`.

-/

open
  Rep
  leftRegular
  dimensionShift
  CategoryTheory
  ConcreteCategory
  Limits
  BigOperators


variable {R : Type} [CommRing R]
variable (G : Type) [Group G] [IsCyclic G] [Fintype G]
variable (M : Rep R G)

noncomputable section

/--
`gen G` is a generator of the cyclic group `G`.
-/
abbrev gen : G := IsCyclic.exists_generator.choose

variable {G}

def oneSubGen : coind'.obj M ⟶ coind'.obj M where
  hom := by
    rw [coind']
    apply ofHom
    simp only [ihom_obj_V_carrier, ihom_obj_V_isAddCommGroup, ihom_obj_V_isModule]
    exact {
      toFun f := f - f ∘ₗ (leftRegular R G).ρ (gen G)
      map_add' := sorry
      map_smul' := sorry
    }
  comm := sorry

lemma oneSubGen_comp_up_ι : up_ι M ≫ oneSubGen M = 0 := sorry

lemma down_π_comp_oneSubGen : oneSubGen M ≫ down_π M = 0 := sorry

def cx₁ : ShortComplex (Rep R G) where
  zero := oneSubGen_comp_up_ι M

def cx₂ : ShortComplex (Rep R G) where
  zero := down_π_comp_oneSubGen M

lemma cx₁_exact : (cx₁ M).Exact := sorry

lemma cx₂_exact : (cx₂ M).Exact := sorry

def upToDown : up M ⟶ down M := by
  let : up M ⟶ coind'.obj M
  · apply cokernel.desc (up_ι M) (oneSubGen M) (oneSubGen_comp_up_ι M)
  rw [down]
  · apply kernel.lift (down_π M) this
    sorry

lemma upToDown_isIso : IsIso (upToDown M) :=
  /-
  This follows using the lemmas `cx₁_exact` and `cx₂_exact`.
  -/
  sorry

def periodicCohomology (n : ℕ) : groupCohomology M (n + 1) ≅ groupCohomology M (n + 3) :=
  /-
  We have isomorphisms

    `H^{n+1}(G,M) ≅ H^{n+2}(G,down M)` and  `H^{n+2}(G, up M) ≅ H^{n+3}(G,M)`

  and an isomorphism `up M ≅ down M`.
  -/
  sorry

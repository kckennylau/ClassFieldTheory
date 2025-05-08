import Mathlib
import ClassFieldTheory.GroupCohomology.LeftRegular

open
  Rep
  leftRegular
  CategoryTheory
  ConcreteCategory
  Limits
  groupCohomology

noncomputable section

variable {R : Type} [CommRing R]
variable {G : Type} [Group G]
variable (M : Rep R G)

/--
The coinduced representation of a repesentation `M`, defined to be the
space of linear maps `R[G] → M`, on which `G` acts on both `R[G]` and `M`.
This is isomorphic to the function space `G → M` on which `G` acts on both `G` and `M`.
-/
abbrev Rep.coind : Rep R G ⥤ Rep R G := (leftRegular R G).ihom

/--
Coinduced representation are acyclic.
-/
theorem Rep.coind_isAcyclic (n : ℕ) : (coind.obj M).IsAcyclic :=
  /-
  There are many ways to prove this. The following method uses none of the
  technology of homological algebra, so it should be fairly easy to formalize.

  Fix a subgroup `H` of `G` and let `{gᵢ}` be a set of coset representatives for `H \ G`.
  Recall that a homogeneous `n + 1`-cochain on `H` with values in `G → M`
  is a function `σ : H^{n+2} → (G → M)` satisfying

    `σ (h * h₀, ... , h * h_{n+1}) (h * g) = h • σ (h₀,...,hₙ).`

  The cochain `σ` is a cocycle if it satisfies the relation

    `∑ (-1)ⁱ * σ (h₀, ... , (not hᵢ), ... , h_{n+2}) (g) = 0`.

  Given a homogeneous `n + 1`-cocycle `σ`, we'll define a homogeneous `n`-cochain `τ` by

    `τ (h₀,...,hₙ) (h * gᵢ) = σ (h,h₀,...,hₙ) (h * gᵢ)`.

  The cocycle relation for `σ` implies `∂ τ = σ`, so `σ` is a coboundary.

  Let's rephrase this in terms of inhomogeneous cocycles. The inhomogeneous cocycle
  corresponding to `σ` is

    `σ' (h₀,...,hₙ) (h * gᵢ) = σ (1,h₁,h₁*h₂,..., h₁*...*hₙ) (h * gᵢ)`

  and the inhomogeneous cochain corresponding to `τ` is

    `τ' (h₁,...,hₙ) (h * gᵢ)  = τ (1,h₁,... , h₁*...*hₙ) (h * gᵢ)`
    `                         = σ (h, 1, h₁, h₁*h₂, ..., h₁*...*hₙ) (h * gᵢ)`
    `                         = h • σ (1, h⁻¹, h⁻¹*h₁, h⁻¹*h₁*h₂, ..., h⁻¹* h₁*...*hₙ) (gᵢ)`
    `                         = h • σ' (h⁻¹,h₁,...,hₙ) (gᵢ)`.

  The last formula above defines an inhomogeneous cochain `τ'`, such that `∂ τ' = σ'`.
  -/
  sorry

namespace Rep.dimensionShift


/--
The inclusion of `M` in its coinduced representation. If we think of the
coinduced representation as the function space `G → M`, then this inclusion is
the map `m ↦ const G m`.

We could define it as a natural transformation, but we don't need that right now.
-/
def up_ι : M ⟶ coind.obj M := by
  rw [coind]
  apply ofHom
  exact {
    val := {
      toFun m := {
        toFun v := ε R G v • m
        map_add' := sorry
        map_smul' := sorry
      }
      map_add' := sorry
      map_smul' := sorry
    }
    property := sorry
  }

/--
The map from `M` to its coinduced representation is a monomorphism.
-/
instance : Mono (up_ι M) := by
  /-
  This is because the map is injective.
  -/
  sorry


/--
We could define this as a functor, but there's no need right now.
-/
def up : Rep R G := cokernel (up_ι M)

@[simps X₁ X₂ X₃ f g]
def up_ses : ShortComplex (Rep R G) where
  X₁ := M
  X₂ := coind.obj M
  X₃ := up M
  f := up_ι M
  g := cokernel.π (up_ι M)
  zero := cokernel.condition (up_ι M)

lemma up_shortExact : (up_ses M).ShortExact where
  exact := sorry -- should be somewhere in Mathlib.
  mono_f := inferInstanceAs (Mono (up_ι M))
  epi_g := coequalizer.π_epi

/--
The connecting homomorphism from `H^{n+1}(G,dimensionShift M)` to `H^{n+2}(G,M)` is
an epimorphism (i.e. surjective).
-/
lemma up_δ_zero_epi : Epi (δ (up_shortExact M) 0 1 rfl) :=
  /-
  The next term in the long exact sequence is zero by `groupCohomology.ofCoind`.
  -/
  sorry

/--
The connecting homomorphism from `H^{n+1}(G,up M)` to `H^{n+2}(G,M)` is an
isomorphism.
-/
lemma up_δ_isIso (n : ℕ) : IsIso (δ (up_shortExact M) (n + 1) (n + 2) rfl) :=
  /-
  This map is sandwiched between two zeros by `groupCohomology.ofCoind`.
  -/
  sorry

variable [Fintype G]

def down_π : coind.obj M ⟶ M where
  hom := by
    rw [coind]
    apply ofHom
    simp only [ihom_obj_V_carrier, ihom_obj_V_isAddCommGroup, ihom_obj_V_isModule]
    exact {
      toFun f := ∑ g : G, f (leftRegular.of g)
      map_add' := sorry
      map_smul' := sorry
    }
  comm := sorry

def down : Rep R G := kernel (down_π M)

def down_ses : ShortComplex (Rep R G) where
  X₁ := down M
  X₂ := coind.obj M
  X₃ := M
  f := kernel.ι (down_π M)
  g := down_π M
  zero := kernel.condition (down_π M)

lemma down_shortExact : (down_ses M).ShortExact := sorry

/--
The connecting homomorphism from `H^{n+1}(G,M)` to `H^{n+2}(G,down M)` is
an epimorphism (i.e. surjective).
-/
lemma down_δ_zero_epi : Epi (δ (down_shortExact M) 0 1 rfl) :=
  /-
  The next term in the long exact sequence is zero by `groupCohomology.ofCoind`.
  -/
  sorry

/--
The connecting homomorphism from `H^{n+1}(G,M)` to `H^{n+2}(G,down M)` is an
isomorphism.
-/
lemma down_δ_isIso (n : ℕ) : IsIso (δ (up_shortExact M) (n + 1) (n + 2) rfl) :=
  /-
  This map is sandwiched between two zeros by `groupCohomology.ofCoind`.
  -/
  sorry
end dimensionShift

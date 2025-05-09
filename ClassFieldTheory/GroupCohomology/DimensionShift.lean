import Mathlib
import ClassFieldTheory.GroupCohomology.LeftRegular

/-!
We define two "coinduction" functors taking values in the acyclic objects of `Rep R G`.

The first is `coind G : ModuleCat R ⥤ Rep R G`.

This takes an `R`-module `A` to the space of linear maps `R[G] ⟶ A`, where `G` acts by
its action of `R[G]`. Note that the linear maps `R[G] ⟶ A` are equivalent to the functions
`G → A`, since the elements of `G` form a basis for the group ring `R[G]`.

The second functor is `coind' : Rep R G ⥤ Rep R G`.

This takes a representation `M` of `G` to the space of
This takes an `R`-module `A` to the space of linear maps `R[G] ⟶ M`, where `G` acts by
conjugation (i.e. on both `R[G]` and on `M`).

The representations `coind'.obj M` and `(coind G).obj M.V` are isomorphic (although
the isomorphism is not simply the identity map on the space of functions `G → M`, since the
actions of `G` on these spaces are not the same).

For any `M : Rep R G` we construct two short exact sequences
(the second defined only for finite `G`):

  `0 ⟶ M ⟶ coind'.obj M ⟶ up M ⟶ 0` and `0 ⟶ down M ⟶ coind'.obj M ⟶ M ⟶ 0`.

These can be used for dimension-shifting because `coind'.obj M` is acyclic.
-/

open
  Rep
  leftRegular
  CategoryTheory
  ConcreteCategory
  Limits
  groupCohomology

noncomputable section

variable {R : Type} [CommRing R]
variable (G : Type) [Group G]

namespace Rep
/--
The functor taking an `R`-module `M` to the trivial representation of `G` on `M`.
-/
def fTrivial : ModuleCat R ⥤ Rep R G where
  obj M := trivial R G M
  map f := {
    hom := f
    comm := by tauto
  }

/--
The coinduced representation of an `R`-module `M`, defined to be the
space of linear maps `R[G] → M`, on which `G` acts on `R[G]`.
This is isomorphic to the function space `G → M`, where `G` acts by translation.
-/
abbrev coind : ModuleCat R ⥤ Rep R G := fTrivial G ⋙ (leftRegular R G).ihom

/--
Coinduced representations are acyclic.
-/
theorem coind_isAcyclic (A : ModuleCat R) : ((coind G).obj A).IsAcyclic :=
  /-
  There are many ways to prove this. The following method uses none of the
  technology of homological algebra, so it should be fairly easy to formalize.

  Fix a subgroup `H` of `G` and let `{gᵢ}` be a set of coset representatives for `H \ G`.
  Recall that a homogeneous `n + 1`-cochain on `H` with values in `G → A`
  is a function `σ : H^{n+2} → (G → A)` satisfying

    `σ (h * h₀, ... , h * h_{n+1}) (h * g) = σ (h₀,...,hₙ).`

  The cochain `σ` is a cocycle if it satisfies the relation

    `∑ᵢ (-1)ⁱ * σ (h₀, ... , (not hᵢ), ... , h_{n+2}) (g) = 0`.

  Given a homogeneous `n + 1`-cocycle `σ`, we'll define a homogeneous `n`-cochain `τ` by

    `τ (h₀,...,hₙ) (h * gᵢ) = σ (h,h₀,...,hₙ) (h * gᵢ)`.

  The cocycle relation for `σ` implies `∂ τ = σ`, so `σ` is a coboundary.

  Let's rephrase this in terms of inhomogeneous cocycles. The inhomogeneous cocycle
  corresponding to `σ` is

    `σ' (h₀,...,hₙ) (h * gᵢ) = σ (1,h₁,h₁*h₂,..., h₁*...*hₙ) (h * gᵢ)`

  and the inhomogeneous cochain corresponding to `τ` is

    `τ' (h₁,...,hₙ) (h * gᵢ)  = τ (1,h₁,... , h₁*...*hₙ) (h * gᵢ)`
    `                         = σ (h, 1, h₁, h₁*h₂, ..., h₁*...*hₙ) (h * gᵢ)`
    `                         = σ (1, h⁻¹, h⁻¹*h₁, h⁻¹*h₁*h₂, ..., h⁻¹* h₁*...*hₙ) (gᵢ)`
    `                         = σ' (h⁻¹,h₁,...,hₙ) (gᵢ)`.

  The last formula above defines an inhomogeneous cochain `τ'`, such that `∂ τ' = σ'`.
  -/
  sorry


def coind_quotientToInvariants_iso (A : ModuleCat R) (H : Subgroup G) [H.Normal] :
    ((coind G).obj A).quotientToInvariants H ≅ (coind (G ⧸ H)).obj A :=
  /-
  Use the isomorphism `Rep.coind_iso` on the left.
  Then the `H`-invariants on the left hand side are just functions `G/H ⟶ M` with the action
  of `G/H` by translation on `G/H`. This is exactly the right hand side.

  Since `quotientToInvariants` is a current PR, this will have to wait.
  -/
  sorry

lemma coind_quotientToInvariants_isAcyclic (A : ModuleCat R) (H : Subgroup G) [H.Normal] :
    (((coind G).obj A).quotientToInvariants H).IsAcyclic := by
  apply Rep.isAcyclic_of_iso
  apply Rep.coind_quotientToInvariants_iso
  exact coind_isAcyclic (G ⧸ H) A

variable {G}

/--
The coinduced representation of a repesentation `M`, defined to be the
space of linear maps `R[G] → M`, on which `G` acts on both `R[G]` and `M`.
This is isomorphic to the function space `G → M` on which `G` acts on both `G` and `M`.
-/
abbrev coind' : Rep R G ⥤ Rep R G := (leftRegular R G).ihom


/--
Both of the representations `coind'.obj M` and `(coind G).obj M.V` can be thought of
as spaces of linear maps `R[G] ⟶ M`, or equivalently as spaces of functions `G → M`.
However the action of `G` on `coind'.obj M` is by conjugation, wheras the action
of `G` on `(coind G).obj M.V` is by translation on `G`.
The isomorphism between them takes a function `f : G → M` to the function
`x ↦ M.ρ x⁻¹ (f x)`. Equivalently, if `F : R[G] ⟶ M` is a linear map then this is taken to the
linear map `R[G] ⟶ M` defined by `v ↦ ∑ x ∈ v.support, (v x) •  M.ρ x⁻¹ (F (leftRegular.of x))`.

It would be nicer to state this as an isomorphism of functors
between `coind'` and `(forget₂ _ _) ⋙ coind G`, but this isn't needed right now.
-/
def coind'_iso_coind (M : Rep R G) : coind'.obj M ≅ (coind G).obj M.V where
  hom := {
    hom := ofHom {
      toFun φ := {
        toFun v := ∑ g ∈ v.support, (v g) • M.ρ g⁻¹ (φ.toFun (leftRegular.of g))
        map_add' := sorry
        map_smul' := sorry
      }
      map_add' := sorry
      map_smul' := sorry
    }
    comm g := by
      sorry
  }
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

variable (M : Rep R G)

lemma coind'_isAcyclic : (coind'.obj M).IsAcyclic := by
  apply isAcyclic_of_iso
  apply coind'_iso_coind
  exact coind_isAcyclic G M.V

lemma coind'_quotientToInvariants_isAcyclic (H : Subgroup G) [H.Normal] :
    ((coind'.obj M).quotientToInvariants H).IsAcyclic := by
  have : (coind'.obj M).quotientToInvariants H ≅ ((coind G).obj M.V).quotientToInvariants H
  · /-
    It would be helpful to define `quotientToInvariants` as a functor, in order to make this
    automatic from the isomorphism `coind'.obj M ≅ (coind G).obj M.V`. Since `quotientToInvariants`
    is a current PR, this will need to wait.
    -/
    sorry
  exact Rep.isAcyclic_of_iso this (coind_quotientToInvariants_isAcyclic _ _ _)

namespace dimensionShift

/--
The inclusion of `M` in its coinduced representation. If we think of the
coinduced representation as the function space `G → M`, then this inclusion is
the map `m ↦ const G m`.

We could define it as a natural transformation, but we don't need that right now.
-/
def up_ι : M ⟶ coind'.obj M := by
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
    property g := by
      sorry
  }

/--
The map from `M` to its coinduced representation is a monomorphism.
-/
instance : Mono (up_ι M) := by
  /-
  This is because the map is injective.
  (Choose `v` in `R[G]` such that `ε R G v = 1`; for example we can take
  `v := leftRegular.of 1`. Then we have `m = (up_ι M m).toFun v`.)
  -/
  sorry


/--
We could define this as a functor, but there's no need right now.
-/
def up : Rep R G := cokernel (up_ι M)

/--
The short exact sequence

  `0 ⟶ M ⟶ coind'.obj M ⟶ up M ⟶ 0`

This can be used for dimension shifting because `coind'.obj M` is acyclic.
-/
abbrev up_ses : ShortComplex (Rep R G) where
  X₁ := M
  X₂ := coind'.obj M
  X₃ := up M
  f := up_ι M
  g := cokernel.π (up_ι M)
  zero := cokernel.condition (up_ι M)

lemma up_shortExact : (up_ses M).ShortExact where
  exact := ShortComplex.exact_cokernel (up_ι M)
  mono_f := inferInstance
  epi_g := coequalizer.π_epi

lemma up_shortExact' (H : Subgroup G) :
    ((up_ses M).map (res H)).ShortExact := by
  rw [res_respectsShortExact]
  exact up_shortExact M

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

/--
The connecting homomorphism from `H^{n+1}(G,dimensionShift M)` to `H^{n+2}(G,M)` is
an epimorphism (i.e. surjective).
-/
lemma up_δ_zero_epi' (H : Subgroup G) : Epi (δ (up_shortExact' M H) 0 1 rfl) :=
  /-
  The next term in the long exact sequence is zero by `groupCohomology.ofCoind`.
  -/
  sorry

/--
The connecting homomorphism from `H^{n+1}(G,up M)` to `H^{n+2}(G,M)` is an
isomorphism.
-/
lemma up_δ_isIso' (H : Subgroup G) (n : ℕ) : IsIso (δ (up_shortExact' M H) (n + 1) (n + 2) rfl) :=
  /-
  This map is sandwiched between two zeros by `groupCohomology.ofCoind`.
  -/
  sorry

variable [Fintype G]

def down_π : coind'.obj M ⟶ M where
  hom := by
    rw [coind']
    apply ofHom
    simp only [ihom_obj_V_carrier, ihom_obj_V_isAddCommGroup, ihom_obj_V_isModule]
    exact {
      toFun f := ∑ g : G, f (leftRegular.of g)
      map_add' := sorry
      map_smul' := sorry
    }
  comm := sorry

instance : Epi (down_π M) :=
  /-
  This is because `down_π M` is surjective.
  A pre-image of an element `m : M` is the function `G → M` taking the value
  `m` at `1 : G` and `0` elsewhere. Equivalently this is the linear map
  `(leftRegular R G).V ⟶ M.V` taking `f` to `(f 1) • m`.
  -/
  sorry

def down : Rep R G := kernel (down_π M)

abbrev down_ses : ShortComplex (Rep R G) where
  X₁ := down M
  X₂ := coind'.obj M
  X₃ := M
  f := kernel.ι (down_π M)
  g := down_π M
  zero := kernel.condition (down_π M)

lemma down_shortExact : (down_ses M).ShortExact where
  exact := ShortComplex.exact_kernel (down_π M)
  mono_f := inferInstance
  epi_g := inferInstance

lemma down_shortExact' (H : Subgroup G) :
    ((down_ses M).map (res H)).ShortExact := by
  rw [res_respectsShortExact]
  exact down_shortExact M

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
end Rep
end

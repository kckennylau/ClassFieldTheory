import Mathlib
import ClassFieldTheory.GroupCohomology._1_Basic
import ClassFieldTheory.GroupCohomology._2_TrivialCohomology

section Group

variable {R G : Type} [Group G] [CommRing R]

open
  Classical
  Finsupp
  CategoryTheory
  ConcreteCategory
open Rep hiding of
open scoped CategoryTheory BigOperators

/-
# helper lemmas concerning the object `leftRegular R G` of `Rep R G`.
-/
namespace Rep.leftRegular

/--
`Rep.leftRegular.of g` is the group element `g : G` regarded as
as element of `Rep.leftRegular ℤ G`. Its type is `CoeSort.coe (Rep.leftRegular ℤ G)`.
-/
noncomputable abbrev of (g : G) : leftRegular R G := single g 1

lemma coeff_of (g h : G) : (of g) h = if (g = h) then (1 : R) else (0 : R) :=
  Finsupp.single_apply

lemma coeff_of_eq_one (g : G) : (of g) g = (1 : R) := by
  rw [coeff_of, if_pos rfl]

example (g : G) : (of g) g = (1 : R) := by
  rw [coeff_of]
  simp

@[ext] lemma ext (v w : (leftRegular R G)) (h : ∀ x : G, v x = w x) : v = w :=
  Finsupp.ext h

example (v : leftRegular R G) :
    v = v.sum (fun x s ↦ s • of x) :=
by
  simp only [smul_single, smul_eq_mul, mul_one, sum_single]

lemma eq_sum_smul_of (v : leftRegular R G) : v = ∑ x ∈ v.support, (v x) • (of x) := by
  change v = v.sum (fun x s ↦ s • of x)
  simp

lemma ρReg_apply (g : G) : (leftRegular R G).ρ g = lmapDomain R R (g * ·) := rfl

lemma ρReg_apply_apply (g : G) (v : leftRegular R G) :
    (leftRegular R G).ρ g v = lmapDomain R R (g * ·) v := rfl

lemma coeff_ρReg_apply_self_mul (g : G) (v : leftRegular R G) (x : G) :
    ((leftRegular R G).ρ g v) (g * x) = v x := by
  rw [ρReg_apply_apply, lmapDomain_apply]
  have : Function.Injective (g * ·)
  · intro x y hxy
    dsimp at hxy
    simpa using hxy
  exact mapDomain_apply this v x

lemma coeff_ρReg_apply (g : G) (v : leftRegular R G) (x : G) :
    ((leftRegular R G).ρ g v) x = v (g⁻¹ * x) := by
  convert coeff_ρReg_apply_self_mul g v (g⁻¹ * x)
  rw [←mul_assoc, mul_inv_cancel, one_mul]

lemma ρReg_apply_of (g x : G) : (leftRegular R G).ρ g (of x) = of (g * x) := by
  rw [ρReg_apply_apply, lmapDomain_apply, leftRegular.of, mapDomain_single, ←leftRegular.of]

lemma ρReg_comp_lsingle (g x : G) : (leftRegular R G).ρ g ∘ₗ lsingle x = lsingle (g * x) := by
  ext; simp

lemma of_eq_ρReg_of_one (g : G) : of g = (leftRegular R G).ρ g (of 1) := by
  rw [ρReg_apply_of, mul_one]

lemma hom_comp_ρReg {B : Rep R G} (b : B) (g : G) (v : leftRegular R G) :
    (leftRegularHom B b) ((leftRegular R G).ρ g v) = B.ρ g ((leftRegularHom B b) v) :=
  hom_comm_apply (B.leftRegularHom b) g v

/--
If two morphisms from the left regular representation agree at `of 1` then they are equal.
-/
lemma Hom.ext {A : Rep R G} (f₁ f₂: leftRegular R G ⟶ A) (hfg : f₁ (of 1) = f₂ (of 1)) : f₁ = f₂
    := by
  rw [←(leftRegularHomEquiv A).toEquiv.apply_eq_iff_eq]
  exact hfg

lemma leftRegularHom_of {A : Rep R G} (v : A) (g : G) :
    (A.leftRegularHom v) (of g) = A.ρ g v := by
  have := leftRegularHom_hom_single g v 1
  rw [one_smul] at this
  exact this

/--
If `g` is in the centre of `G` then the unique morphism of the
left regular representation which takes `1` to `g` is (as a linear map) `(leftRegular R G).ρ g`.
-/
lemma leftRegularHom_eq_ρReg (g : G) (hg : g ∈ Subgroup.center G) :
    hom ((leftRegular R G).leftRegularHom (of g)).hom = (leftRegular R G).ρ g :=
by
  ext
  simp [hg.comm]


variable (R G)
/--The augmentation map from the left regular representation to the trivial module.-/
noncomputable
def ε : leftRegular R G ⟶ trivial R G R := leftRegularHom (trivial R G R) (1 : R)

variable {R G}
lemma ε_of_one : (ε R G) (of 1) = (1 : R) :=
  leftRegularHom_of 1 1

lemma ε_comp_ρ (g : G) : ModuleCat.ofHom ((leftRegular R G).ρ g) ≫ (ε R G).hom = (ε R G).hom :=
  (ε R G).comm g

lemma ε_comp_ρ_apply (g : G) (v : (leftRegular R G).V) :
  (ε R G) ((leftRegular R G).ρ g v) = (ε R G) v :=
by
  change ((ModuleCat.ofHom _) ≫ (ε R G).hom).hom v = _
  rw [ε_comp_ρ]
  rfl

@[simp]
lemma ε_of (g : G) : ε R G (of g) = (1 : R) :=
by
  have : of g = (leftRegular R G).ρ g (of 1)
  · rw [ρReg_apply_of, mul_one]
  rw [this, ε_comp_ρ_apply, ε_of_one]

instance : AddMonoidHomClass (Action.HomSubtype (ModuleCat R) G (leftRegular R G) (trivial R G R))
    (leftRegular R G) (trivial R G R) where
  map_add f := map_add f.val
  map_zero f := map_zero f.val

instance : MulActionHomClass (Action.HomSubtype (ModuleCat R) G (leftRegular R G) (trivial R G R))
    R (leftRegular R G) (trivial R G R) where
  map_smulₛₗ f := map_smul f.val

lemma ε_eq_sum_coeff (v : leftRegular R G) : ε R G v = ∑ x ∈ v.support, v x :=
by
  nth_rw 1 [eq_sum_smul_of v, map_sum]
  apply Finset.sum_congr rfl
  intros
  rw [map_smul, ε_of, smul_eq_mul, mul_one]

lemma ε_eq_sum [Fintype G] (v : leftRegular R G) : ε R G v = ∑ x ∈ Fintype.elems, v x :=
by
  rw [ε_eq_sum_coeff]
  have : (v : G → R).support ⊆ v.support
  · simp
  have := finsum_eq_finset_sum_of_support_subset v this
  rw [←this]
  rw [finsum_eq_sum_of_fintype]
  rfl

/--
The left regular representation is nontrivial (i.e. non-zero) if and only if the coefficient
ring is trivial.
-/
lemma nontrivial_iff_nontrivial : Nontrivial (leftRegular R G) ↔ Nontrivial R :=
by
  simp only [nontrivial_iff]
  constructor
  · intro h
    contrapose! h
    intro v w
    ext
    apply h
  · intro ⟨x,y,hxy⟩
    use x • (of 1), y • (of 1)
    contrapose! hxy
    apply_fun fun v ↦ (v 1) at hxy
    simpa using hxy

/--
The module over the group algebra corresponding to `leftRegular R G` is isomorphic to
the group algebra. This is used in proving that `leftRegular R G` is free, and hence projective.
-/
noncomputable def equiv_MonoidAlgebra :
    (Representation.ofMulAction R G G).asModule  ≃ₗ[MonoidAlgebra R G] MonoidAlgebra R G where
      toFun := id
      map_add' := by tauto
      map_smul' := by
        intros
        dsimp only [id_eq, AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply, smul_eq_mul]
        rw [Representation.ofMulAction_self_smul_eq_mul]
      invFun := id
      left_inv := by tauto
      right_inv := by tauto

/--
`leftRegular R G` is free as a module over the group algebra.
-/
noncomputable def free : Basis Unit (MonoidAlgebra R G) <|
    (equivalenceModuleMonoidAlgebra.functor.obj (leftRegular R G) : Type) where repr := {
  toFun := single ()
  map_add' := by simp
  map_smul' := by
    intros
    dsimp only [AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply]
    rw [smul_single', Representation.ofMulAction_self_smul_eq_mul]
  invFun := fun a ↦ a ()
  left_inv := fun _ ↦ single_eq_same
  right_inv := by
    intro
    dsimp only [AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply, id_eq, eq_mpr_eq_cast]
    ext
    apply single_eq_same
  }

/--
`leftRegular R G` is projective in the category `Rep R G`.
-/
instance : CategoryTheory.Projective (leftRegular R G) :=
by
  apply Rep.equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective
  apply ModuleCat.projective_of_free
  exact free



-- The next few things are used for dimension-shifting.
-- Given an representation M, we want an acyclic module N and a short exact sequence
--
--  `0 ⟶ M ⟶ N ⟶ Q ⟶ 0`.
--
-- This is achieved by taking `N` to be the function space `G → M`, or equivalently
-- `(leftRegular R G).ihom.obj M`.

/--
`leftRegular R G` is free as a module over the group algebra of a subgroup `H`.
-/
noncomputable def free' {H : Type} [Group H] {φ : H →* G} (inj : Function.Injective φ)
    : Basis (G ⧸ φ.range) (MonoidAlgebra R H) <|
    (equivalenceModuleMonoidAlgebra.functor.obj (leftRegular R G ↓ φ) : Type) :=
  /-
  There is a basis indexed by the coset type `G ⧸ H`, with basis
  vectors `of g⁻¹` for coset representatives.
  -/
  sorry


end Rep.leftRegular

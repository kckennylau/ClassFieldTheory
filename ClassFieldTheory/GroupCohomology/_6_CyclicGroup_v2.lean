import Mathlib
import ClassFieldTheory.GroupCohomology._3_LeftRegular
import ClassFieldTheory.GroupCohomology._5_DimensionShift

/-!
Let `M : Rep R G`, where `G` is a finite cyclic group.
We construct an exact sequence

  `0 ⟶ M ⟶ coind₁'.obj M ⟶ ind₁'.obj M ⟶ M ⟶ 0`.

Using this sequence, we construct an isomorphism

  `dimensionShift.up.obj M ≅ dimensionShift.down.obj M`.

Using this, construct isomorphisms

  `Hⁿ⁺¹(G,M) ≅ Hⁿ⁺³(G,M)`.

-/

open
  Finsupp
  Rep
  leftRegular
  dimensionShift
  CategoryTheory
  ConcreteCategory
  Limits
  BigOperators
  groupCohomology


variable {R : Type} [CommRing R]
variable (G : Type) [Group G] [IsCyclic G] [Finite G] [DecidableEq G]
variable (M : Rep R G)

noncomputable section

/--
`gen G` is a generator of the cyclic group `G`.
-/
abbrev gen : G := IsCyclic.exists_generator.choose

variable {G}

@[simp] lemma ofHom_sub (A B : ModuleCat R) (f₁ f₂ : A →ₗ[R] B) :
  (ofHom (f₁ - f₂) : A ⟶ B) = ofHom f₁ - ofHom f₂ := rfl

@[simp] lemma ofHom_add (A B : ModuleCat R) (f₁ f₂ : A →ₗ[R] B) :
  (ofHom (f₁ + f₂) : A ⟶ B) = ofHom f₁ + ofHom f₂ := rfl

@[simp] lemma ofHom_zero (A B : ModuleCat R) :
  (ofHom 0 : A ⟶ B) = 0 := rfl

@[simp] lemma ofHom_one (A : ModuleCat R) :
  (ofHom 1 : A ⟶ A) = 𝟙 A := rfl

@[simp] lemma Rep.ρ_mul_eq_comp (M : Rep R G) (x y : G) :
    Action.ρ M (x * y) = (Action.ρ M y) ≫ (Action.ρ M x) := by
  rw [Rep.Action_ρ_eq_ρ, map_mul]
  rfl

section Representation

variable {A : Type} [AddCommGroup A] [Module R A] (ρ : Representation R G A)

@[simps] def Representation.map₁ : (G → A) →ₗ[R] (G → A) where
  toFun f x := f x - f ((gen G)⁻¹ * x)
  map_add' := sorry
  map_smul' := sorry

lemma Representation.map₁_comm (g : G) :
    map₁ ∘ₗ ρ.coind₁' g = ρ.coind₁' g ∘ₗ map₁  := by
  apply LinearMap.ext
  intro
  apply funext
  intro
  simp [mul_assoc]

omit [Finite G] [DecidableEq G] in
lemma Representation.map₁_comp_coind_ι :
    map₁ (R := R) (G := G) (A := A) ∘ₗ coind₁'_ι = 0 := by
  ext; simp

omit [Finite G] [DecidableEq G] in
lemma Representation.map₁_ker :
    LinearMap.ker (map₁ (R := R) (G := G) (A := A)) = LinearMap.range coind₁'_ι :=
  sorry

@[simps!] def Representation.map₂ : (G →₀ A) →ₗ[R] (G →₀ A) :=
  LinearMap.id - lmapDomain _ _ (fun x ↦ x * gen G)

omit [Finite G] [DecidableEq G] in
@[simp] lemma Representation.map₂_comp_lsingle (x : G) :
    map₂ (R := R) (G := G) (A := A) ∘ₗ lsingle x = lsingle x - lsingle (x * gen G) := by
  ext
  simp [map₂, LinearMap.sub_comp]

omit [Finite G] [DecidableEq G] in
lemma Representation.map₂_comm (g : G) :
    map₂ ∘ₗ ρ.ind₁' g = ρ.ind₁' g ∘ₗ map₂ := by
  ext x : 1
  rw [LinearMap.comp_assoc, ind₁'_comp_lsingle, LinearMap.comp_assoc, map₂_comp_lsingle,
    LinearMap.comp_sub, ind₁'_comp_lsingle, ←LinearMap.comp_assoc, map₂_comp_lsingle, mul_assoc,
    LinearMap.sub_comp, ind₁'_comp_lsingle]

omit [Finite G] [DecidableEq G] in
lemma Representation.ind₁'_π_comp_map₂ :
    ind₁'_π ∘ₗ map₂ (R := R) (G := G) (A := A) = 0 := by
  ext : 1
  rw [LinearMap.comp_assoc, map₂_comp_lsingle, LinearMap.comp_sub,
    LinearMap.zero_comp, sub_eq_zero, ind₁'_π_comp_lsingle, ind₁'_π_comp_lsingle]

lemma Representation.map₂_range :
    LinearMap.range (map₂ (R := R) (G := G) (A := A)) = LinearMap.ker ind₁'_π :=
  sorry


end Representation

namespace Rep

/--
The map `coind₁'.obj M ⟶ coind₁' M` which takes a function `f : G → M.V` to
`x ↦ f x - f (gen G * x)`.
-/
def map₁ : coind₁' (R := R) (G := G) ⟶ coind₁' where
  app M := {
    hom := ofHom Representation.map₁
    comm g := by
      ext : 1
      apply Representation.map₁_comm
  }
  naturality := sorry

lemma coind_ι_gg_map₁_app : coind₁'_ι.app M ≫ map₁.app M = 0 := by
  ext : 2
  apply Representation.map₁_comp_coind_ι

lemma coind_ι_gg_map₁ : coind₁'_ι ≫ map₁ (R := R) (G := G) = 0 := by
  ext : 2
  apply coind_ι_gg_map₁_app


def map₂ : ind₁' (R := R) (G := G) ⟶ ind₁' where
  app M := {
    hom := ofHom Representation.map₂
    comm g := by
      ext : 1
      apply Representation.map₂_comm
  }
  naturality := sorry

omit [Finite G] [DecidableEq G] in
lemma map₂_app_gg_ind₁'_π_app :  map₂.app M ≫ ind₁'_π.app M = 0 := by
  ext : 2
  apply Representation.ind₁'_π_comp_map₂

omit [Finite G] [DecidableEq G] in
lemma map₂_gg_ind₁'_π : map₂ (R := R) (G := G) ≫ ind₁'_π = 0 := by
  ext : 2
  apply map₂_app_gg_ind₁'_π_app

/--
Let `M` be a representation of a finite cyclic group `G`.
Then the following square commutes

  ` coind₁'.obj M -------> coind₁'.obj M `
  `      |                      |        `
  `      |                      |        `
  `      ↓                      ↓        `
  `   ind₁'.obj M ------->   ind₁'.obj M `

The vertical maps are the canonical isomorphism `ind₁'_iso_coind₁`
and the horizontal maps are `map₁` and `map₂`.
-/
lemma map₁_comp_ind₁'_iso_coind₁' :
    map₁.app M ≫ (ind₁'_iso_coind₁'.app M).inv = (ind₁'_iso_coind₁'.app M).inv ≫ map₂.app M :=
  sorry


/--
For a cyclic group `G`, this is the sequence of representations of a cyclic group:

` 0 ⟶ M ⟶ coind₁'.obj M ⟶ ind₁'.obj M ⟶ M ⟶ 0 `.

The middle map is `map₁ ≫ ind₁'_iso_coind₁'.inv`, which is
equal to `ind₁'_iso_coind₁'.inv ≫ map₂`. The sequence is exact.

It might be sensible to make this into a functor.
-/
def periodicitySequence : CochainComplex (Rep R G) (Fin 4) where
  X
  | 0 => M
  | 1 => coind₁'.obj M
  | 2 => ind₁'.obj M
  | 3 => M
  d
  | 0,1 => coind₁'_ι.app M
  | 1,2 => map₁.app M ≫ (ind₁'_iso_coind₁'.app M).inv
  | 2,3 => ind₁'_π.app M
  | _,_ => 0
  d_comp_d' :=
    /-
    Proved in lemmas above in the non-trivial cases.
    -/
    sorry

lemma periodicitySequence_exactAt_one : (periodicitySequence M).ExactAt 1 := sorry

lemma periodicitySequence_exactAt_two : (periodicitySequence M).ExactAt 2 := sorry

def up_obj_iso_down_obj : up.obj M ≅ down.obj M :=
  /-
  `up.obj M` is the cokernel of the first map is `periodicitySequence`,
  so is isomorphic to the image of the second map. This in turn is isomorphic to the
  kernel of the last map, which is `down.obj M`.
  -/
  sorry

def up_iso_down : up (R := R) (G := G) ≅ down where
  hom := {
    app M := (up_obj_iso_down_obj M).hom
    naturality := sorry
  }
  inv := {
    app M := (up_obj_iso_down_obj M).inv
    naturality := sorry
  }

def periodicCohomology (n : ℕ) :
    functor R G (n + 1) ≅ functor R G (n + 3) := by
  apply Iso.trans (down_δiso_natTrans n)
  apply Iso.trans (isoWhiskerRight up_iso_down.symm _)
  apply up_δiso_natTrans

/--
Let `M` be a representation of a finite cyclic group `G`.
If `H¹(G,M)` and `H²(G,M)` are both zero then `Hⁿ(G,M)` is zero for all `n > 0`.
-/
lemma isZero_ofH1_ofH2 {M : Rep R G} (h1 : IsZero (groupCohomology M 1))
    (h2 : IsZero (groupCohomology M 2)) (n : ℕ) : IsZero (groupCohomology M (n + 1)) := by
  induction n using Nat.twoStepInduction with
  | zero => exact h1
  | one => exact h2
  | more n ih _ =>
    apply IsZero.of_iso ih
    apply (periodicCohomology n).symm.app



section six_term_sequence
variable {S : ShortComplex (Rep R G)} (hS : S.ShortExact)

def herbrandSixTermSequence : CochainComplex (ModuleCat R) (Fin 6) where
  X
  | 0 => groupCohomology S.X₁ 2
  | 1 => groupCohomology S.X₂ 2
  | 2 => groupCohomology S.X₃ 2
  | 3 => groupCohomology S.X₁ 1
  | 4 => groupCohomology S.X₂ 1
  | 5 => groupCohomology S.X₃ 1
  d
  | 0,1 => (functor R G 2).map S.f
  | 1,2 => (functor R G 2).map S.g
  | 2,3 => δ hS 2 3 rfl ≫ (periodicCohomology 0).inv.app S.X₁
  | 3,4 => (functor R G 1).map S.f
  | 4,5 => (functor R G 1).map S.g
  | 5,0 => δ hS 1 2 rfl
  | _,_ => 0
  shape i j _ := by fin_cases i,j <;> tauto
  d_comp_d' i _ _ hij hjk := by
    simp only [ComplexShape.up_Rel, Fin.isValue] at hij hjk
    rw [←hjk,←hij]
    sorry


lemma herbrandSixTermSequence_exactAt (i : Fin 6) : (herbrandSixTermSequence hS).ExactAt i :=
  /-
  It should be possible to get this out of Mathlib.
  -/
  sorry

def herbrandQuotient : ℚ := Nat.card (groupCohomology M 2) / Nat.card (groupCohomology M 1)

lemma herbrandQuotient_nonzero_of_shortExact₃
  (h₁ : S.X₁.herbrandQuotient ≠ 0) (h₂ : S.X₂.herbrandQuotient ≠ 0) :
  S.X₃.herbrandQuotient ≠ 0 := sorry

lemma herbrandQuotient_nonzero_of_shortExact₂
  (h₁ : S.X₁.herbrandQuotient ≠ 0) (h₃ : S.X₃.herbrandQuotient ≠ 0) :
  S.X₂.herbrandQuotient ≠ 0 := sorry

lemma herbrandQuotient_nonzero_of_shortExact₁
  (h₁ : S.X₂.herbrandQuotient ≠ 0) (h₃ : S.X₃.herbrandQuotient ≠ 0) :
  S.X₁.herbrandQuotient ≠ 0 := sorry

lemma herbrandQuotient_eq_of_shortExact
    (h₁ : S.X₁.herbrandQuotient ≠ 0) (h₂ : S.X₂.herbrandQuotient ≠ 0)
    (h₃ : S.X₃.herbrandQuotient ≠ 0) :
    S.X₂.herbrandQuotient = S.X₁.herbrandQuotient * S.X₃.herbrandQuotient :=
  /-
  We have a six term long exact sequence of finite `R`-modules.
  Hence the products of the orders of the even terms is
  equal to the product of the orders of the odd terms.
  This implies the relation.
  -/
  sorry

end six_term_sequence

end Rep

namespace Representation

variable [Fintype G]
variable {A : Type} [AddCommGroup A] [Module R A]
variable (ρ : Representation R G A)

def oneSubGen : A →ₗ[R] A := 1 - ρ (gen G)

def norm  : A →ₗ[R] A := ∑ g : G, ρ g

lemma oneSubGen_comp_norm : oneSubGen ρ ∘ₗ norm ρ = 0 := sorry

lemma norm_comp_oneSubGen : norm ρ ∘ₗ oneSubGen ρ = 0 := sorry

end Representation

namespace Rep
variable [Fintype G] (M : Rep R G)
open HomologicalComplex
/--
Let `G` be a finite cyclic group or order `n` generated by `g`, and let `M` be an `RG`-module.
This is the complex `Fin 2` indexed complex of `R` modules whose
objects are both `M` with morphisms given by `1- g` and `1 + g + ... + g ^ (n-1)`.
-/
@[simps] def herbrandComplex : CochainComplex (ModuleCat R) (Fin 2) where
  X _ := M.V
  d
  | 0,0 => 0
  | 0,1 => ofHom M.ρ.oneSubGen
  | 1,0 => ofHom M.ρ.norm
  | 1,1 => 0
  shape i j:= by fin_cases i <;> fin_cases j <;> tauto
  d_comp_d' i _ _ hij hjk := by
    simp only [ComplexShape.up_Rel, Fin.isValue] at hij hjk
    fin_cases i <;> simp [←hij,←hjk] <;> ext : 1
    · exact M.ρ.norm_comp_oneSubGen
    · exact M.ρ.oneSubGen_comp_norm

def herbrandH0_iso_groupCohomology_two : homology (herbrandComplex M) 0 ≅ groupCohomology M 2 :=
  sorry

def herbrandH1_iso_groupCohomology_one : homology (herbrandComplex M) 1 ≅ groupCohomology M 1 :=
  sorry



end Rep

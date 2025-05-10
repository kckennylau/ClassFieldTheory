import Mathlib
-- import ClassFieldTheory.GroupCohomology.CyclicGroup
import ClassFieldTheory.GroupCohomology._2_Acyclic_def
import ClassFieldTheory.GroupCohomology._1_restriction
import ClassFieldTheory.GroupCohomology._3_LeftRegular


/-!
Let `R` be a commutative ring and `G` a group.
We define the augmentation module `aug R G : Rep R G` to be the kernel of
the augmentation map "ε : R[G] ⟶ R".

We show that there is a short exact sequence of `H`-modules for every subgroup `H` of `G`.

  0 ⟶ aug R G ⟶ R[G] ⟶ R ⟶ 0.

In the case that `G` is finite, the representation `R[G]` is coinduced, and so has
trivial cohomology (with respect to any subgroup `H`). This implies that the connecting homomorphism

  H^n(H,R) ⟶ H^{n+1}(H, aug R G)

are isomorphisms for all `n > 0`.

We also have isomorphisms

  H¹(H,aug R G) ≅ R ⧸ |H|R,

  H²(H,aug R G) ≅ 0, assuming `NoZeroSMulDivisors ℕ R`.

-/

open
  Rep
  leftRegular
  CategoryTheory
  ConcreteCategory
  Limits
  groupCohomology
  BigOperators

variable (R : Type) [CommRing R]
variable (G : Type) [Group G]

noncomputable section AugmentationModule

/--
The augmentation module `aug R G` is the kernel of the augmentation map

  `ε : leftRegular R G ⟶ trivial R G R`.

-/
abbrev Rep.aug : Rep R G := kernel (ε R G)

namespace Rep.aug

abbrev ι : aug R G ⟶ leftRegular R G := kernel.ι (ε R G)


/--
The inclusion of `aug R G` in `leftRegular R G`.
-/

lemma ε_comp_ι : ι R G ≫ ε R G = 0 := kernel.condition (ε R G)

lemma ε_apply_ι (v : aug R G) : ε R G (ι R G v) = 0 :=
  sorry
  -- use the previous lemma.

lemma sum_coeff_ι [Fintype G] (v : aug R G) : ∑ g : G, (ι R G v) g = 0 :=
  sorry
  -- use the previous lemma.

lemma exists_ofSubOfOne (g : G) : ∃ v : aug R G, ι R G v = leftRegular.of g - leftRegular.of 1 := by
  apply exists_kernelι_eq
  rw [map_sub, ε_of, ε_of, sub_self]

/--
The element of `aug R G` whose image in `leftRegular R G` is `of g - of 1`.
-/
def ofSubOfOne (g : G) : aug R G := (exists_ofSubOfOne R G g).choose

@[simp] lemma ofSubOfOne_spec (g : G) :
    ι R G (ofSubOfOne R G g) = leftRegular.of g - leftRegular.of 1 :=
  (exists_ofSubOfOne R G g).choose_spec

/--
The short exact sequence

    0 ⟶ aug R G ⟶ R[G] ⟶ R ⟶ 0.

-/
def aug_shortExactSequence : ShortComplex (Rep R G) where
  X₁ := aug R G
  X₂ := leftRegular R G
  X₃ := trivial R G R
  f := ι R G
  g := ε R G
  zero := ε_comp_ι R G

/--
The sequence

  0 ⟶ aug R G ⟶ R[G] ⟶ R ⟶ 0

is a short exact sequence of G-modules.
-/
lemma isShortExactSequence  : (aug_shortExactSequence R G).ShortExact := sorry

/--
The sequence

  0 ⟶ aug R G ⟶ R[G] ⟶ R ⟶ 0

is a short exact sequence of `H`-modules for any subgroup `H` of `G`.
-/
lemma isShortExactSequence' (H : Subgroup G) :
    ((aug_shortExactSequence R G).map (res H)).ShortExact := by
  sorry

lemma _root_.groupCohomology.of_coinduced (A : Rep R G) (n : ℕ):
    IsZero (groupCohomology ((ihom (leftRegular R G)).obj A) (n + 1)) := by sorry

lemma _root_.Rep.leftRegular.isZero_groupCohomology [Finite G] (n : ℕ) :
    IsZero (groupCohomology (leftRegular R G) (n+1)) := by
  /-
  show that if `G` is finite then `leftRegular R G` is coinduced from `trivial R G R`.
  Then apply `groupCohomology.ofcoinduced`.
  -/
  sorry

lemma _root_.groupCohomology.of_projective [Finite G] (P : Rep R G) [Projective P] (n : ℕ) :
    IsZero (groupCohomology P (n+1)) :=
  /-
  Use the isomorphism in Mathlib between group cohomology and Ext.
  -/
  sorry

/--
If `G` is a finite group and `H` is a subgroup of `G` then `H^{n+1}(H,R[G]) = 0`.
-/
lemma _root_.Rep.leftRegular.isZero_groupCohomology' [Finite G] (n : ℕ) (H : Subgroup G) :
    IsZero (groupCohomology (leftRegular R G ↓ H) (n + 1)) := by
  /-
  Show that `R[G]` is isomorphic as an `H`-module to a direct sum of copies of `R[H]`.
  Then use `Rep.leftRegular.isZero_groupCohomology`.
  -/
  sorry

/--
The connecting homomorphism from H^{n+1}(G,R) to H^{n+2}(G,aug R G) is an isomorphism.
-/
lemma cohomology_aug_succ_iso [Finite G] (n : ℕ) :
    IsIso (δ (isShortExactSequence R G) (n + 1) (n + 2) rfl) :=
  /-
  This connecting homomorphism is sandwiched between two modules H^{n+1}(G,R[G]) and H^{n+2}(G,R[G]),
  where P is the left regular representation.
  Then use `Rep.leftRegular.isZero_groupCohomology` to show that both of these are zero.
  -/
  sorry

lemma H2_aug_isZero [Finite G] [NoZeroSMulDivisors ℕ R] : IsZero (H2 (aug R G)) :=
  /-
  This follows from `cohomology_aug_succ_iso` and `groupCohomology.H1_isZero_of_trivial`.
  -/
  sorry



/--
The connecting homomorphism from H^{n+1}(G,R) to H^{n+2}(G,aug R G) is an isomorphism.
-/
lemma cohomology_aug_succ_iso' [Finite G] (H : Subgroup G) (n : ℕ):
    IsIso (δ (isShortExactSequence' R G H) (n + 1) (n + 2) rfl) :=
  /-
  The proof is similar to that of `cohomology_aug_succ_iso` but uses
  `Rep.leftRegular.isZero_groupCohomology'` in place of `Rep.leftRegular.isZero_groupCohomology`.
  -/
  sorry

def cohomology_aug_one_iso [Finite G] :
    H0 (aug R G) ≅ ModuleCat.of R (R ⧸ Ideal.span {(Nat.card G : R)}) :=
  /-
  If Tate cohomology is defined, then this is proved in the same way as the previous
  lemma. If not, then using usual cohomology we have a long exact sequence containing the
  following section:

    H⁰(G,R[G]) ⟶ H⁰(G,R) ⟶ H¹(aug R G) ⟶ 0.

  We clearly have H⁰(G,R) = R.
  The group H⁰(G,R[G]) is also cyclic over R, and is generated by the norm element, i.e. the sum of
  all elements of `G`. The image of the norm element in H⁰(G,R) is |G|, since every element of the
  group is mapped by `ε` to `1`.
  -/
  sorry

def cohomology_res_aug_one_iso [Finite G] (H : Subgroup G) :
    H0 (aug R G ↓ H) ≅ ModuleCat.of R (R ⧸ Ideal.span {(Nat.card H : R)}) :=
  /-
  If Tate cohomology is defined, then this is proved in the same way as the previous
  lemma. If not, then using usual cohomology we have a long exact sequence containing the
  following section:

    H⁰(H,R[G]) ⟶ H⁰(H,R) ⟶ H¹(aug R G) ⟶ 0.

  We clearly have H⁰(H,R) = R.
  The group H⁰(H,R[G]) is generated by the indicator functions of coset of `H`,
  The image of such a function in H⁰(H,R) is |H|, since every element of the
  group is mapped by `ε` to `1`.
  -/
  sorry

end Rep.aug

end AugmentationModule

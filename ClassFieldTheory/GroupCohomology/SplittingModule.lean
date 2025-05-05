import Mathlib
import ClassFieldTheory.GroupCohomology.CyclicGroup

open
  CategoryTheory
  ConcreteCategory
  Limits
  Rep
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

/--
The restriction functor `Rep R G ⥤ Rep R H` for a subgroup `H` of `G`.
-/
abbrev Rep.res (H : Subgroup G) : Rep R G ⥤ Rep R H := Action.res (ModuleCat R) H.subtype

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
lemma Rep.isZero_iff (M : Rep R G) : IsZero M ↔ IsZero (M.V) := by
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
lemma Rep.isZero_res_iff (M : Rep R G) (H : Subgroup G) : IsZero (M ↓ H) ↔ IsZero M := by
  simp [isZero_iff]

/--
The restriction functor `res H : Rep R G ⥤ Rep R H` is takes short exact sequences to short
exact sequences.
-/
lemma Rep.res_respectsShortExact (H : Subgroup G) (S : ShortComplex (Rep R G)) :
    (S.map (res H)).ShortExact ↔ S.ShortExact :=
  sorry

lemma Rep.res_of_projective {P : Rep R G} (hP : Projective P) (H : Subgroup G) :
    Projective (P ↓ H) := by
  /-
  A representation is projective iff it is a direct summand of a free module over the group ring.
  This lemma follows because "R[G]" is free as an "R[H]"-module (a basis is given by a set of
  coset representatives).

  There is perhaps a better proof than this.
  -/
  sorry

/--
# Leave this as a sorry, and then remove once Amelia's PR on long exact sequences is merged.
-/
def _root_.groupCohomology.δ {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : ℕ) :
    groupCohomology S.X₃ n ⟶ groupCohomology S.X₁ (n + 1) := sorry

noncomputable section AugmentationModule

namespace Rep.leftRegular


/-
# TODO

1. add a few definitional lemmas for `Rep.res`.

2. Restate the results about the splitting module more generally in terms of the cohomology og `H`.

-/


variable (R G)
/--
The augmentation module `aug R G` is the kernel of the augmentation map

  `ε : leftRegular R G ⟶ trivial R G R`.

-/
abbrev _root_.Rep.aug : Rep R G := kernel (ε R G)

/--
The inclusion of `aug R G` in `leftRegular R G`.
-/
abbrev _root_.Rep.augι : aug R G ⟶ leftRegular R G := kernel.ι (ε R G)

lemma ε_comp_augι : augι R G ≫ ε R G = 0 := kernel.condition (ε R G)

lemma ε_apply_augι (v : aug R G) : ε R G (augι R G v) = 0 :=
  sorry
  -- use the previous lemma.

lemma sum_coeff_augι [Fintype G] (v : aug R G) : ∑ g : G, (augι R G v) g = 0 :=
  sorry
  -- use the previous lemma.

lemma exists_ofSubOfOne (g : G) : ∃ v : aug R G, augι R G v = of g - of 1 := by
  apply exists_kernelι_eq
  rw [map_sub, ε_of, ε_of, sub_self]

/--
The element of `aug R G` whose image in `leftRegular R G` is `of g - of 1`.
-/
def ofSubOfOne (g : G) : aug R G := (exists_ofSubOfOne R G g).choose

@[simp] lemma ofSubOfOne_spec (g : G) : augι R G (ofSubOfOne R G g) = of g - of 1 :=
  (exists_ofSubOfOne R G g).choose_spec

/--
The short exact sequence

    0 ⟶ aug R G ⟶ R[G] ⟶ R ⟶ 0.

-/
def aug_shortExactSequence : ShortComplex (Rep R G) where
  X₁ := aug R G
  X₂ := leftRegular R G
  X₃ := trivial R G R
  f := augι R G
  g := ε R G
  zero := ε_comp_augι R G

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
    IsIso (δ (isShortExactSequence R G) (n + 1)) :=
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
    IsIso (δ (isShortExactSequence' R G H) (n + 1)) :=
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

end Rep.leftRegular

end AugmentationModule


noncomputable section SplittingModule
variable [Fintype G]
variable {M : Rep R G}

namespace Rep.splittingModule

set_option linter.unusedVariables false in
abbrev carrier (σ : twoCocycles M) : Type := (aug R G) × M

variable (σ : twoCocycles M)

def representation : Representation R G (carrier σ) where
  toFun g := {
    toFun v := {
      fst := (aug R G).ρ g v.fst
      snd := M.ρ g v.snd + ∑ x : G, augι R G v.fst x • σ ⟨g, x⟩
    }
    map_add' := sorry
    map_smul' := sorry
  }
  map_one' := by
    ext : 1
    · simp
      ext v : 1
      rw [LinearMap.comp_apply]
      dsimp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Finsupp.coe_add, Pi.add_apply,
        Prod.mk_add_mk, LinearMap.one_apply, AddHom.toFun_eq_coe, RingHom.id_apply, AddHom.coe_mk,
        Prod.smul_fst, Prod.smul_snd, SetLike.val_smul, Finsupp.coe_smul, Pi.smul_apply,
        smul_eq_mul, Prod.smul_mk, LinearMap.coe_inl, LinearMap.coe_mk, LinearMap.coe_comp,
        Function.comp_apply]
      ext : 1
      · rfl
      · dsimp only
        rw [zero_add]
        have (x : G) : σ (1,x) = σ (1,1)
        · -- essentially the same statement is in Mathlib.
          sorry
        simp only [this]
        rw [←Finset.sum_smul, leftRegular.sum_coeff_augι, zero_smul]
    · ext v : 1
      simp
  map_mul' g₁ g₂ := by
    simp only [map_mul, LinearMap.mul_apply, equalizer_as_kernel]
    ext v
    · simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_inl,
      Function.comp_apply, map_zero, zero_add, LinearMap.mul_apply, map_sum, map_smul]
    · simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_inl,
      Function.comp_apply, map_zero, zero_add, LinearMap.mul_apply, map_sum, map_smul]
      sorry
    · simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_inr,
      Function.comp_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply, zero_smul,
      Finset.sum_const_zero, add_zero, LinearMap.mul_apply]
    · simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_inr,
      Function.comp_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply, zero_smul,
      Finset.sum_const_zero, add_zero, LinearMap.mul_apply]


def _root_.Rep.splittingModule : Rep R G := Rep.of (splittingModule.representation σ)

lemma apply (g : G) (vm : carrier σ) : (splittingModule σ).ρ g vm
    = ⟨(aug R G).ρ g vm.1, M.ρ g vm.2 + ∑ x : G, augι R G vm.1 x • σ ⟨g, x⟩⟩ := rfl

lemma apply_fst (g : G) (vm : carrier σ) :
    ((splittingModule σ).ρ g vm).fst = (aug R G).ρ g vm.1 := rfl

lemma apply_snd (g : G) (vm : carrier σ) :
    ((splittingModule σ).ρ g vm).snd = M.ρ g vm.2 + ∑ x : G, augι R G vm.1 x • σ ⟨g, x⟩ := rfl

@[ext] lemma ext (vm vm' : splittingModule σ) (hv : vm.1 =vm'.1) (hm : vm.2 = vm'.2) : vm = vm' := by
  change (⟨vm.1,vm.2⟩ : aug R G × M) = ⟨vm'.1,vm'.2⟩
  rw [hv,hm]

@[simp] lemma add_fst (vm vm' : splittingModule σ) : (vm + vm').1 = vm.1 + vm'.1 := rfl
@[simp] lemma add_snd (vm vm' : splittingModule σ) : (vm + vm').2 = vm.2 + vm'.2 := rfl
@[simp] lemma sub_fst (vm vm' : splittingModule σ) : (vm - vm').1 = vm.1 - vm'.1 := rfl
@[simp] lemma sub_snd (vm vm' : splittingModule σ) : (vm - vm').2 = vm.2 - vm'.2 := rfl


/--
The natural inclusion of a `G`-module `M` in the splitting module
of a 2-cocycle `σ : Z²(G,M)`.
-/
def ι : M ⟶ splittingModule σ := by
  apply ofHom
  exact {
    val := LinearMap.inr R (aug R G) M
    property g := by
      ext m : 1
      simp only [id_eq, ρ_hom, Function.comp_apply]
      rw [apply]
      ext
      · change 0 = (aug R G).ρ g 0
        rw [map_zero]
      · change M.ρ g m = (M.ρ g) m + ∑ x : G, (augι R G) 0 x • σ (g, x)
        rw [map_zero]
        simp
  }

lemma ι_apply (m : M) : ι σ m = ⟨0,m⟩ := rfl

/--
The projection from the splitting module of a 2-cocycle to `aug R G`.
-/
def π : splittingModule σ ⟶ aug R G := by
  apply ofHom
  exact {
    val := LinearMap.fst R (aug R G) M
    property := sorry
  }

def shortExactSequence : ShortComplex (Rep R G) where
  X₁ := M
  X₂ := splittingModule σ
  X₃ := aug R G
  f := ι σ
  g := π σ
  zero := sorry

lemma isShortExact : ShortComplex.ShortExact (shortExactSequence σ) := sorry






/--
The function from the group `G` to the splitting module of a 2-cocycle `σ`,
which takes `g : G` to ([1]-[g], σ (g,1)).

The coboundary of this function is equal to the image of `σ` in H²(G,split).
-/
noncomputable def τ (g : G) : splittingModule σ :=
  ⟨leftRegular.ofSubOfOne R G g, M.ρ g (σ (1,1))⟩

open leftRegular Classical


/--
Given a 2-cocycle `σ`, the image of `σ` in the splitting module of `σ` is equal to the
coboundary of `τ σ`.
-/
lemma τ_property (g h : G) : (splittingModule σ).ρ g (τ σ h) - τ σ (g * h) + τ σ g  = ι σ (σ (g,h))
    := by
  rw [τ, apply, τ, τ, ι_apply]
  ext
  · simp only [ofSubOfOne_spec, Finsupp.coe_sub, Pi.sub_apply, add_fst, sub_fst]
    sorry
  · simp [leftRegular.of, Finsupp.single_apply, sub_smul]
    sorry



/--
Given a 2-cocycle `σ : Z²(G,M)`, the image of `σ` in `Z²(G,splittingModule σ)` is a coboundary.
-/
lemma splits : ι σ ∘ σ ∈ twoCoboundaries (splittingModule σ) := by
  use τ σ
  ext : 1
  rw [groupCohomology.dOne_apply, Function.comp_apply, τ_property]


/-
The hypotheses `h2` and `h2'` say that `H²(G,M)` is isomorphic to `R / |G|R`,
and is generated by (the class of) `σ`.
-/

/--
If `σ` generates H²(G,M) then the map H²(G,M) ⟶ H²(G,split σ) is zero.
-/
lemma TateTheorem_lemma_1
    (h2 : ∀ (c : H2 M), ∃ r : R, c = r • H2π M σ) :
    H2Map (MonoidHom.id G) (ι σ) = 0 :=
  /-
  every element is a multiple of `σ`, and we have proved in `splits` that the image of `σ` is a
  coboundary.
  -/
  sorry

lemma helper (I : Ideal R) (f : R ⧸ I →ₗ[R] R ⧸ I) (surj : Function.Surjective f) :
    Function.Injective f :=
  /-
  I didn't find this in Mathlib, but it's worth checking again.

  Without loss of generality `I = 0`, since `f` may be regarded as an `R ⧸ I`-linear map.
  So we have a surjective linear map `f : R → R`. Let `c = f 1`.
  Then for any `x` we have `f x = f (x * 1) = x * f 1 = x * c`.
  Since `f` is surjective, `c` is a unit, and multiplication by `c⁻¹` is a 2-sided inverse of `f`.
  -/
  sorry


/--
The connecting hommotphism in the splitting module long exact sequence

    H¹(G,aug) ⟶ H²(G,M)

is an isomorphism.
-/
lemma TateTheorem_lemma_2
    (h2 : ∀ (c : H2 M), ∃ r : R, c = r • H2π M σ)
    (h2' : ∀ r : R, r • H2π M σ = 0 ↔ (Nat.card G : R) ∣ r) :
    IsIso (δ (isShortExact σ) 1) :=
  /-
  We have a long exact sequence containing the section

      H¹(G,aug) ⟶ H²(G,M) ⟶ H²(G,split).

  We proved in `TateTheorem_lemma_1` that the second map is zero, so the connecting homomorphism
  is surjective.
  We are assuming that H²(G,M) ≅ R/|G|, and we have proved above that H¹(G,aug R G) ≅ R/|G|.
  We can therefore use `helper` to prove that the connecting homomorphism is also injective.
  -/
  sorry




lemma TateTheorem_lemma_3
    (h1 : IsZero (H1 M))
    (h2 : ∀ (c : H2 M), ∃ r : R, c = r • H2π M σ)
    (h2' : ∀ r : R, r • H2π M σ = 0 ↔ (Nat.card G : R) ∣ r) :
    IsZero (H1 (splittingModule σ)) :=
  /-
  We therefore have a long exact sequence containing the section

    0 ⟶ H¹(G,split) ⟶ H¹(G,aug) ⟶ H²(G,M).

  the second map above is an isomorphism by `TateTheorem_lemma_2`.
  -/
  sorry

lemma TateTheorem_lemma_4 [NoZeroSMulDivisors ℕ R]
    (h2 : ∀ (c : H2 M), ∃ r : R, c = r • H2π M σ)
    : IsZero (H2 (splittingModule σ)) :=
  /-
  By assumption, `R` has no elements of finite additive order,
  so we have H²(G,aug) ≅ H¹(G,R) ≅ Hom(G,R) ≅ 0. This uses `groupCohomology.H1_isZero_of_trivial`

  We therefore have a long exact sequence containing

    H²(G,M) ⟶ H²(G,split) ⟶ 0.

  We have shown in `TateTheorem_lemma_1` that the map above is zero.
  -/
  sorry

/-

# TODO

1. Show that we have a short exact sequence:

    0 ⟶ M ⟶ splittingModule σ ⟶ aug R G ⟶ 0.

2. Show that the image of `σ` in Z²(G,splittingModule σ) is a coboundary. The formula for the
coboundary is in Milne's lecture notes on class field theory.

3. Assume next that H²(G,M) ≅ R / |G|R and is generated by `σ`, and that H¹(G,M) = 0.

Note that we now have a long exact sequence containing:

    0 ⟶ H¹(G,split) ⟶ R/|G|R ⟶ H²(G,M) ⟶ H²(G,split) ⟶ 0.

using this, prove that H¹(G,split) = 0 and H²(G,split) = 0.
It's sufficient for class field theory to prove this only in the case `R = ℤ` although
the general case is not much harder.

3. *Tate's Theorem* (The statement below is slightly vague)

Assuming that `M` satisfies the conditions above for all subgroups of `G`,
prove that Hⁿ(G,split) = 0 for all `n` (if this is Tate cohomology).
For class field theory, it is sufficient to prove this only for Tate cohomology in dimensions
`0` and `-1`, but if Tate cohomology is not available
then perhaps it makes sense to prove this is all positive dimensions.

This is proved by induction on the subgroup of `G`.
It's proved for cyclic `G` by periodicity together with (3.)
For solvable groups, the inductive step is by inflation-restriction.
For a general group notince that the p-Sylov subgroup of Hⁿ(G,split) is isomorphic to
a subgroup of Hⁿ(Gₚ,split), where Gₚ is a Sylow p-subgroup of G. We then use the fact that
Gₚ is solvable.

Note that for local class field theory, it's enough to prove in the case that `G` is solvable.

4. define an isomorphism between Hⁿ(G,R) and H^{n+1}(G,aug R G), which we have already seen
is isomorphic to H^{n+2}(G,R).
-/

end Rep.splittingModule


end SplittingModule








-- section AugmentationModule

-- variable (R : Type) [CommRing R]
-- variable (G : Type) [Group G]

-- /--
-- The augmentation module is the kernel of the map
-- `ε R G : leftRegular R G ⟶ trivial R G R`.
-- -/
-- noncomputable abbrev AugmentationModule := LinearMap.ker (leftRegular.ε R G).hom.hom
--   --Limits.kernel (leftRegular.ε R G)
--   --we have not used Limits.kernel, since this uses the axiom of choice to define the type.
--   --We will (perhaps) need the actual type.

-- lemma AugmentationModule_prop [Fintype G] (v : AugmentationModule R G) :
--     ∑ x : G, v.val x = 0 := sorry



-- noncomputable def augmentationRepresentation : Representation R G <| AugmentationModule R G where
--   toFun g := by
--     apply LinearMap.restrict ((leftRegular R G).ρ g)
--     sorry -- check the file LeftRegular for the relevant lemma.
--   map_one' := sorry
--   map_mul' := sorry

-- lemma augmentationRepresentation_apply (g : G) (v : AugmentationModule R G) :
--     (augmentationRepresentation R G g v).val = (leftRegular R G).ρ g v.val := rfl

-- lemma augmentationRepresentation_apply_apply (g : G) (v : AugmentationModule R G) (x : G) :
--     (augmentationRepresentation R G g v).val x = v.val (g⁻¹ * x) := by
--   rw [augmentationRepresentation_apply]
--   apply leftRegular.coeff_ρReg_apply

-- noncomputable def augmentationRep : Rep R G := of (augmentationRepresentation R G)

-- -- this takes the place of `augmentationRep_apply`
-- def augmentation_ι : augmentationRep R G ⟶ leftRegular R G where
--   hom := ofHom (AugmentationModule R G).subtype

-- @[ext] lemma augmentation_ι_injective : Function.Injective (augmentation_ι R G) :=
--   fun _ _ ↦ Subtype.ext



-- end AugmentationModule


-- section SplittingModule
-- variable (R : Type) [CommRing R]
-- variable (G : Type) [Group G] [Fintype G]
-- variable (M : Rep R G)

-- noncomputable abbrev SplittingModule : Type := (AugmentationModule R G) × M

-- variable {R G M}
-- variable (σ : groupCohomology.twoCocycles M)

-- noncomputable def splittingModuleRepresentation : Representation R G (SplittingModule R G M) where
--   toFun g := {
--     toFun v := {
--       fst := augmentationRepresentation R G g v.fst
--       snd := M.ρ g v.snd + ∑ x : G, v.fst.val x • σ ⟨g, x⟩ -- can replace v.1.val by augmentation_ι v.1
--     }
--     map_add' := sorry
--     map_smul' := sorry
--   }
--   map_one' := by
--     ext : 1
--     · simp
--       ext v : 1
--       rw [LinearMap.comp_apply]
--       dsimp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Finsupp.coe_add, Pi.add_apply,
--         Prod.mk_add_mk, LinearMap.one_apply, AddHom.toFun_eq_coe, RingHom.id_apply, AddHom.coe_mk,
--         Prod.smul_fst, Prod.smul_snd, SetLike.val_smul, Finsupp.coe_smul, Pi.smul_apply,
--         smul_eq_mul, Prod.smul_mk, LinearMap.coe_inl, LinearMap.coe_mk, LinearMap.coe_comp,
--         Function.comp_apply]
--       ext : 1
--       · rfl
--       · dsimp only
--         rw [zero_add]
--         have (x : G) : σ (1,x) = σ (1,1)
--         · -- essentially the same statement is in Mathlib.
--           sorry
--         simp only [this]
--         rw [←Finset.sum_smul, AugmentationModule_prop, zero_smul]
--     · ext v : 1
--       simp
--   map_mul' g₁ g₂ := by
--     ext v : 2
--     · simp only [map_mul, LinearMap.mul_apply, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk,
--       LinearMap.coe_inl, Function.comp_apply, map_zero, zero_add, map_sum, map_smul, Prod.mk.injEq,
--       true_and]
--       conv => {
--         right
--         right
--         right
--         intro
--         rw [augmentationRepresentation_apply_apply]
--       }
--       sorry
--       /-
--       This follows using the 2-cocycle relation together with the fact that `v` is in the
--       augmentation module, so the sum of its coefficients is zero.
--       -/
--     · simp only [map_mul, LinearMap.mul_apply, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk,
--       LinearMap.coe_inr, Function.comp_apply, map_zero, ZeroMemClass.coe_zero, Finsupp.coe_zero,
--       Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]


-- noncomputable def splittingModule : Rep R G := Rep.of (splittingModuleRepresentation σ)






-- noncomputable instance : AddCommMonoid (SplittingModule R G M) where
--   add v w := ⟨v.x + w.x, v.m + w.m, sorry⟩
--   add_assoc := sorry
--   zero := sorry
--   zero_add := sorry
--   add_zero := sorry
--   nsmul := sorry
--   nsmul_zero := sorry
--   nsmul_succ := sorry
--   add_comm := sorry

-- noncomputable instance : Module R (SplittingModule R G M) where
--   smul r v := ⟨r • v.x, r • v.m, sorry⟩
--   one_smul := sorry
--   mul_smul := sorry
--   smul_zero := sorry
--   smul_add := sorry
--   add_smul := sorry
--   zero_smul := sorry

-- variable {R G M} (σ : groupCohomology M 2)

-- def SplittingModule.ρ : Representation R G (SplittingModule R G M) where
--   toFun g := {
--     toFun v := {
--       x := sorry
--       m := sorry
--       x_one := sorry
--     }
--     map_add' := sorry
--     map_smul' := sorry
--   }
--   map_one' := sorry
--   map_mul' := sorry

-- end SplittingModule

/-
The restriction functor from `Rep R G` to `Rep R H`, where `H` is a subgroup
of a group `G`.
-/
-- noncomputable def Rep.restriction : (Rep R G) ⥤ (Rep R H) where
--   obj X := {
--     V := X.V
--     ρ := {
--       toFun := fun ⟨h,_⟩ ↦ CategoryTheory.ConcreteCategory.ofHom (X.ρ h)
--       map_one' := sorry
--       map_mul' := sorry
--     }
--   }
--   map f := {
--     hom := f.hom
--     comm := fun _ ↦ f.comm _
--   }
--   map_id := sorry
--   map_comp := sorry



-- variable (C : Rep R G)

-- #check (restriction H).obj C

-- variable (hC₁ : Unique (groupCohomology ((restriction H).obj C) 1))
-- variable (hC₂ : Nat.card (groupCohomology ((restriction H).obj C) 2) = Nat.card H)
-- variable (H2_gen : groupCohomology ((restriction H).obj C) 2)
-- variable (H2_gen_spec : ∀ σ : groupCohomology ((restriction H).obj C) 2, ∃ n : ℤ, σ = n • H2_gen)


-- instance : AddCommGroup {f : G → R // f 1 = 0} where
--   add f f' := ⟨f + f', sorry⟩
--   add_assoc := sorry
--   zero := ⟨0,rfl⟩
--   zero_add := sorry
--   add_zero := sorry
--   nsmul n f := ⟨n • f,sorry⟩
--   nsmul_zero := sorry
--   nsmul_succ := sorry
--   neg f := ⟨f,sorry⟩
--   sub f g := ⟨f - g, sorry⟩
--   sub_eq_add_neg := sorry
--   zsmul n f := ⟨n • f,sorry⟩
--   zsmul_zero' := sorry
--   zsmul_succ' := sorry
--   zsmul_neg' := sorry
--   neg_add_cancel := sorry
--   add_comm := sorry


-- noncomputable instance : Module R {f : G → R // f 1 = 0} where
--   smul x f := ⟨x • f, sorry⟩
--   one_smul := sorry
--   mul_smul := sorry
--   smul_zero := sorry
--   smul_add := sorry
--   add_smul := sorry
--   zero_smul := sorry

-- #check H2_gen

-- variable {C}
-- /--the 2-cocycle representing the generator of H^2(G,C).-/
-- def φ : G → G → C := sorry


-- noncomputable instance : Representation R G (C × {f : G → R // f 1 = 0}) where
--   toFun g := by
--     by_cases hg : g = 1
--     · exact 1
--     · exact {
--         toFun := by
--           -- need to check all this.
--           intro ⟨c,f⟩
--           constructor
--           · exact C.ρ g c + ∑ h : G, ((f.val h) • φ g h) - (f.val 1) • (φ g 1)
--           · exact {
--             val := by
--               intro h
--               by_cases hgh : g=h
--               · exact f.val 1 - f.val g
--               · exact f.val (g⁻¹ * h)
--             property := sorry
--           }
--         map_add' := sorry
--         map_smul' := sorry
--       }
--   map_one' := sorry
--   map_mul' := sorry



-- noncomputable
-- def splittingModule : Rep R G where
--   V := {
--     carrier := C × {f : G → R // f 1 = 0}
--     isAddCommGroup := inferInstance
--     isModule := inferInstance
--   }
--   ρ := by
--     change G →* _
--     exact {
--       toFun := by
--         change G →* _
--         exact {
--           toFun := by
--             intro g
--             exact {
--               toFun := by
--                 intro ⟨c, f⟩
--                 let φ : G → G → C := sorry -- the 2-cocycle
--                 let c' := C.ρ g c + ∑ h : G, (f.val g : R) • (φ g h : C)
--                 sorry
--               map_add' := sorry
--               map_smul' := sorry
--             }
--           map_one' := sorry
--           map_mul' := sorry
--         }
--       map_one' := sorry
--       map_mul' := sorry
--     }




-- def dimensionShift (r : ℕ) : groupCohomology (Rep.trivial R G R) r ⟶ groupCohomology C (r + 2) := {
--   toFun := sorry
--   map_add' := sorry
--   map_smul' := sorry
-- }

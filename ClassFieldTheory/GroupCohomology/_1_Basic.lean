import Mathlib
import ClassFieldTheory.GroupCohomology._0_Current_PRs

variable {R G : Type} [Group G] [CommRing R]

section Rep

open Rep CategoryTheory.ConcreteCategory
open scoped CategoryTheory

/-
# General lemmas for the category `Rep R G`.
-/



-- lemma Rep.hom_comp_ρ {A B : Rep R G} (f : A ⟶ B) (g : G) (v : A) :
--     f.hom (A.ρ g v) = B.ρ g (f.hom v) :=
-- by
--   exact hom_comm_apply f g v
  -- calc
  --   _ = (A.ρ g ≫ f.hom) v := rfl
  --   _ = (f.hom ≫ B.ρ g) v := by congr 1; exact f.comm g

#synth CategoryTheory.ConcreteCategory (ModuleCat R) (fun A B ↦ A →ₗ[R] B)

-- instance (A B : ModuleCat R) : FunLike (A ⟶ B) A B where
--   coe f := (f : A → B)
--   coe_injective' _ _ hfg := CategoryTheory.ConcreteCategory.hom_ext_iff.mpr (congrFun hfg)

-- instance (A B : Rep R G) : FunLike (A ⟶ B) A.V B.V where
--   coe f := (f : A.V → B.V)
--   coe_injective' _ _ hfg := CategoryTheory.ConcreteCategory.hom_ext_iff.mpr (congrFun hfg)

-- instance (A B : Rep R G) : FunLike (A ⟶ B) A.V B.V where
--   coe f := (f : A.V → B.V)
--   coe_injective' _ _ hfg := CategoryTheory.ConcreteCategory.hom_ext_iff.mpr (congrFun hfg)

-- instance (A B : ModuleCat R) : AddHomClass (A ⟶ B) A B where
--   map_add f _ _ := by
--     change f.hom _ = f.hom _ + f.hom _
--     apply map_add



-- @[simp]
-- lemma Rep.apply_eq_hom (A B : Rep R G) (f : A ⟶ B) (v : A) :
--     f v = f.hom v := rfl

-- example (A B : Rep R G) (v w : A) (f : A ⟶ B) : f (v + w) = f v + f w := by simp

instance mine₁ (A B : Rep R G) : MulActionHomClass (Action.HomSubtype _ _ A B) R A B where
  map_smulₛₗ f := map_smul f.val

instance mine₂ (A B : Rep R G) :
    AddMonoidHomClass (Action.HomSubtype (ModuleCat R) G A B) A B where
  map_add f := map_add f.val
  map_zero f := map_zero f.val

/-
# TODO
find out why this hack is needed, and why the previous instance isn't working.

(asked on zulip.)
-/
instance (A : Rep R G) (H : Type) [MulAction G H] :
    MulActionHomClass (Action.HomSubtype _ _ A (ofMulAction R G H)) R A (ofMulAction R G H) :=
  mine₁ _ _
instance (A : Rep R G) (H : Type) [MulAction G H] :
    AddMonoidHomClass (Action.HomSubtype (ModuleCat R) G A (ofMulAction R G H))
    A (ofMulAction R G H) := mine₂ A (ofMulAction R G H)

lemma Rep.hom_comm_apply' {A B : Rep R G} (f : A ⟶ B) (g : G) (x : A) :
    f (A.ρ g x) = B.ρ g (f x) := hom_comm_apply f g x

lemma Rep.hom_apply {A B : Rep R G} (f : A ⟶ B) (x : A) : f.hom x = f x := rfl

example (A B : Rep R G) (f : A ⟶ B ) (a b : A) (c : R) : f (a + c • b) = f a + c • f b := by
  simp

#check Action.zero_hom
#check Action.add_hom
#check Action.smul_hom
@[simp]
lemma Action.sub_hom.{u} {V : Type (u + 1)} [CategoryTheory.LargeCategory V] {G : Type u} [Monoid G]
    [CategoryTheory.Preadditive V] {X Y : Action V G} (f g : X ⟶ Y) : (f - g).hom = f.hom - g.hom
    := by
  rw [eq_sub_iff_add_eq, ←Action.add_hom, sub_add_cancel]

#check ModuleCat.hom_add
#check ModuleCat.hom_sub
#check ModuleCat.hom_zero

-- /-
-- # No longer needed
-- This will combine with `Action.zero_hom` to simplify `(O : A ⟶ B) v`,
-- where `A` and `B` are in `Rep ℤ G`. check the example below.
-- -/
-- @[simp]
-- lemma ModuleCat.zero_apply (V V' : ModuleCat R) (v : V) :
--     (0 : V ⟶ V') v = 0 :=
-- by
--   rfl

-- example (A B : Rep R G) (v : A) : (0 : A ⟶ B) v = (0 : B) :=
-- by
--   simp

-- @[simp]
-- lemma ModuleCat.add_apply {S : Type} [Ring S] {A B : ModuleCat S} (f g : A ⟶ B) (v : A) :
--   (f + g) v = f v + g v :=
-- by
--   rfl

-- @[simp]
-- lemma ModuleCat.sub_apply {S : Type} [Ring S] {A B : ModuleCat S} (f g : A ⟶ B) (v : A) :
--   (f - g) v = f v - g v :=
-- by
--   rfl


@[simp]
lemma Rep.zero_apply {A B : Rep R G} (v : A) : (0 : A ⟶ B) v = 0 := rfl
@[simp]
lemma Rep.add_apply {A B : Rep R G} (f₁ f₂ : A ⟶ B) (v : A) : (f₁ + f₂) v = f₁ v + f₂ v := rfl
@[simp]
lemma Rep.sub_apply {A B : Rep R G} (f₁ f₂ : A ⟶ B) (v : A) : (f₁ - f₂) v = f₁ v - f₂ v := by
  rw [eq_sub_iff_add_eq, ←add_apply, sub_add_cancel]
@[simp]
lemma Rep.smul_apply {A B : Rep R G} (c : R) (f : A ⟶ B) (v : A) : (c • f) v = c • (f v) := rfl

lemma Rep.comp_apply {A B C : Rep R G} (f : A ⟶ B) (g : B ⟶ C) (v : A.V) : (f ≫ g) v = g (f v) :=
  rfl

example {A B C : Rep R G} (f : A ⟶ B) : f ≫ (0 : B ⟶ C) = 0 := by
  simp only [CategoryTheory.Limits.comp_zero] -- rfl

example {A B C : Rep R G} (f : B ⟶ C) : (0 : A ⟶ B) ≫ f = 0 := by
  simp only [CategoryTheory.Limits.zero_comp]

example {A B C : Rep R G} (f : A ⟶ B) (g h : B ⟶ C) : f ≫ (g + h) = f ≫ g + f ≫ h := by
  simp only [CategoryTheory.Preadditive.comp_add]


example {A B : Rep R G} (f : A ⟶ B) (v w : A) : f (v - w) = f v - f w := by
  rw [map_sub]


example (A B : ModuleCat R) (v w : A) (f : A ⟶ B) : f (v + w) = f v + f w := by simp

example {S : Type} [Ring S] {A B : ModuleCat S} (f : A ⟶ B) (v : A) (s : S) :
  f (s • v) = s • f v :=
by
  simp only [LinearMapClass.map_smul]

example {A B : Rep R G} (f : A ⟶ B) (v : A) (r : R) :
  f (r • v) = r • f v :=
by
  simp

example {A B : Rep R G} (f g : A ⟶ B) (v : A) :
    (f + g) v = f v + g v := by
  rw [Rep.add_apply]


-- @[simp]
-- lemma Rep.add_hom {A B : Rep R G} (f g : A ⟶ B) : (f + g).hom = f.hom + g.hom := Action.add_hom _ _

-- @[simp]
-- lemma Rep.sub_hom {A B : Rep R G} (f g : A ⟶ B) : (f - g).hom = f.hom - g.hom :=
-- calc
--   _ = (f-g).hom + g.hom - g.hom := by rw [add_sub_cancel_right]
--   _ = (f-g+g).hom - g.hom       := by rw [Rep.add_hom]
--   _ = f.hom - g.hom             := by rw [sub_add_cancel]


-- example (A B : Rep R G) (f g : A ⟶ B) (v : A) :
--     (f - g) v = f.hom v - g.hom v :=
-- by
--   simp


-- # Some API for exact sequences?

open CategoryTheory CategoryTheory.Limits


lemma Rep.leftRegularHomEquiv_symm_comp {A B : Rep R G} (f : A ⟶ B) (a : A) :
    (leftRegularHomEquiv A).symm a ≫ f = (leftRegularHomEquiv B).symm (f a) := by
  rw [LinearEquiv.eq_symm_apply, leftRegularHomEquiv_apply, hom_apply, Rep.comp_apply]
  congr
  exact A.leftRegularHomEquiv.right_inv a

lemma Rep.exists_kernelι_eq {A B : Rep R G} (f : A ⟶ B) (a : A) (ha : f a = 0) :
    ∃ k : kernel f (C := Rep R G), kernel.ι f k = a := by
  let g : leftRegular R G ⟶ A := (leftRegularHomEquiv A).symm a
  have : g ≫ f = 0
  · rw [leftRegularHomEquiv_symm_comp, ha, map_zero]
  let lift : leftRegular R G ⟶ kernel f := kernel.lift f g this
  use leftRegularHomEquiv (kernel f) lift
  rw [leftRegularHomEquiv_apply]
  change (lift ≫ kernel.ι f) (Finsupp.single 1 1) = a
  rw [kernel.lift_ι]
  convert (leftRegularHomEquiv_apply A g).symm
  change a = A.leftRegularHomEquiv (A.leftRegularHomEquiv.symm a)
  rw [LinearEquiv.apply_symm_apply]




-- /--
-- A short sequence in `Rep R G` is exact iff the underlying sequence in `ModuleCat R` is exact.
-- -/
-- lemma Rep.exact_iff {A B C : Rep R G} (f : A ⟶ B) (g : B ⟶ C) :
--     Function.Exact f g ↔ Function.Exact f.hom g.hom :=
-- by
--   rfl

/-
To check whether the underlying sequence is exact in `ModuleCat R`, we can use this:
-/
#check ShortComplex.ab_exact_iff
#check ShortComplex.Exact
#check ShortComplex.map

-- example (A B C : ModuleCat R) (f : A ⟶ B) (g : B ⟶ C) : CategoryTheory.Exact f g ↔ LinearMap.range f = LinearMap.ker g :=
-- by
--   exact ModuleCat.exact_iff f g




--#check AddCommGrp.exact_iff

-- example (A B C : Ab) (f : A ⟶ B) (g : B ⟶ C) : Exact f g ↔ f.range = g.ker :=
-- by
--   exact AddCommGroupCat.exact_iff f g



end Rep


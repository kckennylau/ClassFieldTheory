import Mathlib

section Rep

variable {G R : Type} [Group G] [CommRing R]

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

instance (A B : ModuleCat R) : FunLike (A ⟶ B) A B where
  coe f := (f : A → B)
  coe_injective' _ _ hfg := CategoryTheory.ConcreteCategory.hom_ext_iff.mpr (congrFun hfg)

instance (A B : Rep R G) : FunLike (A ⟶ B) A.V B.V where
  coe f := (f : A.V → B.V)
  coe_injective' _ _ hfg := CategoryTheory.ConcreteCategory.hom_ext_iff.mpr (congrFun hfg)

instance (A B : Rep R G) : FunLike (A ⟶ B) A.V B.V where
  coe f := (f : A.V → B.V)
  coe_injective' _ _ hfg := CategoryTheory.ConcreteCategory.hom_ext_iff.mpr (congrFun hfg)

instance (A B : ModuleCat R) : AddHomClass (A ⟶ B) A B where
  map_add f _ _ := by
    change f.hom _ = f.hom _ + f.hom _
    apply map_add


@[simp]
lemma Rep.apply_eq_hom (A B : Rep R G) (f : A ⟶ B) (v : A) :
    f v = f.hom v := rfl

instance (A B : Rep R G) : AddHomClass (Action.HomSubtype _ _ A B) A.V B.V where
  map_add f x y := map_add f.val x y

instance (A B : Rep R G) : MulActionHomClass (Action.HomSubtype _ _ A B) R A.V B.V where
  map_smulₛₗ f c v := map_smul f.val c v

example (A B : Rep R G) (f : A ⟶ B ) (a b : A) (c : R) : f (a + c • b) = f a + c • f b := by
  simp

#check Action.zero_hom
#check Action.add_hom
#check Action.smul_hom
universe u
@[simp]
lemma Action.sub_hom {V : Type (u + 1)} [CategoryTheory.LargeCategory V] {G : Type u} [Monoid G]
    [CategoryTheory.Preadditive V] {X Y : Action V G} (f g : X ⟶ Y) : (f - g).hom = f.hom - g.hom
    := by
  rw [eq_sub_iff_add_eq, ←Action.add_hom, sub_add_cancel]



#check ModuleCat.hom_add
#check ModuleCat.hom_sub
#check ModuleCat.hom_zero

/-
This will combine with `Action.zero_hom` to simplify `(O : A ⟶ B) v`,
where `A` and `B` are in `Rep ℤ G`. check the example below.
-/
@[simp]
lemma ModuleCat.zero_apply (V V' : ModuleCat R) (v : V) :
    (0 : V ⟶ V') v = 0 :=
by
  rfl

-- example (A B : Rep R G) (v : A) : (0 : A ⟶ B) v = (0 : B) :=
-- by
--   simp

@[simp]
lemma ModuleCat.add_apply {S : Type} [Ring S] {A B : ModuleCat S} (f g : A ⟶ B) (v : A) :
  (f + g) v = f v + g v :=
by
  rfl

-- example {A B : Rep R G} (f g : A ⟶ B) (v : A) :
--     (f + g) v = f.hom v + g.hom v := by simp

example {S : Type} [Ring S] {A B : ModuleCat S} (f : A ⟶ B) (v : A) (s : S) :
  f (s • v) = s • f v :=
by
  simp only [LinearMapClass.map_smul]

example [CommRing R] {A B : Rep R G} (f : A ⟶ B) (v : A) (r : R) :
  f (r • v) = r • f v :=
by
  --rw [apply_eq_hom, apply_eq_hom, map_smul]
  simp

@[simp]
lemma ModuleCat.sub_apply {S : Type} [Ring S] {A B : ModuleCat S} (f g : A ⟶ B) (v : A) :
  (f - g) v = f v - g v :=
by
  rfl


lemma Rep.comp_apply {A B C : Rep R G} (f : A ⟶ B) (g : B ⟶ C) (v : A.V) : (f ≫ g) v = g (f v) :=
  rfl

lemma Rep.zero_apply {A B : Rep R G} (v : A) : (0 : A ⟶ B) v = 0 := rfl

lemma Rep.apply_sub {A B : Rep R G} (f : A ⟶ B) (v w : A) : f (v - w) = f v - f w := by
  simp only [apply_eq_hom, map_sub]

lemma Rep.hom_comm_apply' {A B : Rep R G} (f : A ⟶ B) (g : G) (x : A) :
    f (A.ρ g x) = B.ρ g (f x) := hom_comm_apply f g x




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

open CategoryTheory

/--
A short sequence in `Rep R G` is exact iff the underlying sequence in `ModuleCat R` is exact.
-/
lemma Rep.exact_iff {A B C : Rep R G} (f : A ⟶ B) (g : B ⟶ C) :
    Function.Exact f g ↔ Function.Exact f.hom g.hom :=
by
  rfl

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

import Mathlib
import ClassFieldTheory.GroupCohomology._2_Acyclic_def

/-!
We define two functors:

  `coind₁ G : ModuleCat R ⥤ Rep R G` and
  `ind₁ G : ModuleCat R ⥤ Rep R G`.

For an `R`-module `A`, the representation `(coind₁ G).obj A` is the space of functions `f : G → A`,
with the action of `G` by right-translation. In other words `(g f) x = f (x g)` for `g : G`.

The space `(ind₁ G).obj A` is `G →₀ A` with the action of `G` by left-translation, i.e.
`g (single x v) = single (g * x) v`.

We prove that `coind₁.obj A` is acyclic and `ind₁.obj X` is homology-acyclic.

W show that `coind₁` is isomorphic to the functor `coindFunctor R (1 : Unit →* G)` in Mathlib.

There is an intertwining map `ind₁_toCoind₁ : (ind₁ G).obj A ⟶ (coind₁ G).obj A`,
which takes a finitely supported function `f` to the function `x ↦ f x⁻¹`.
If `G` is finite then this map is an isomorphism, so in this case both representations
are both acyclic and homology-acyclic.

We also define two functors

  `coind₁' : Rep R G ⥤ Rep R G` and
  `ind₁' : Rep R G ⥤ Rep R G`.

For a representation `M` of `G`, the representation `coind₁'.obj M` is the representation of `G`
on `G → M.V`, where the actio of `G` is by `M.ρ` on `M.V` and by right-translation on `G`.

`ind₁'.obj M` is the representation of `G` on `G →₀ M.V`, where the action of `G` is by `M.ρ` on
`M.V` and by left-translation on `G`.

We define the canonical monomorphism `coind₁'_ι : M ⟶ coind₁'.obj M` which takes a vector `v` to
the constant function on `G` with value `v`.

We define the canonical epimorphism `ind₁'_π : ind₁'.obj M ⟶ M` which takes a finitely supported
function to the sum of its values.

We prove that `ind₁'.obj M` is isomorphic to `(ind₁ G).obj M.V`, and is therefore homology acyclic.
Similarly we show that `coind₁'.obj M` is isomorphic to `(coind₁ G).obj M.V` and is therefore
acyclic.
-/

open
  Finsupp
  Representation
  Rep
  CategoryTheory
  NatTrans
  ConcreteCategory
  Limits
  groupCohomology

noncomputable section

variable (R G : Type) [CommRing R] [Group G]

namespace Representation

variable (V W : Type) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]


/--
The representation of `G` on the space `G → V` by right-translation on `G`.
(`V` is an `R`-module with no action of `G`).
-/
@[simps] def coind₁ : Representation R G (G → V) where
  toFun g       := LinearMap.funLeft R V fun a ↦ a * g
  map_one'      := by ext; simp
  map_mul' _ _  := by ext; simp [mul_assoc]

@[simp] lemma coind₁_apply₃ (f : G → V) (g x : G) : coind₁ R G V g f x = f (x * g) := rfl

variable {R G V}
lemma mem_coindV_unit (f : G → V) :
    f ∈ coindV (1 : Unit →* G) (1 : Unit →* (V →ₗ[R] V)) := by
  intro h x
  simp

variable (R G V)
/--
The linear isomorphism from `coindV 1 1` to `G → V`.
-/
@[simps] def coindV_unit_lequiv :
    coindV (1 : Unit →* G) (1 : Unit →* (V →ₗ[R] V)) ≃ₗ[R] (G → V) where
  toFun f := f.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨f,mem_coindV_unit f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/--
The isomorphism `coindV_unit_lequiv` intertwines the actions of `G`
by `coind 1 1` and `coind₁`.
-/
lemma coindV_unit_lequiv_comm (g : G) :
    coind₁ R G V g ∘ₗ (coindV_unit_lequiv R G V).toLinearMap
    = coindV_unit_lequiv R G V  ∘ₗ coind 1 1 g := rfl


/--
The induced representation of a group `G` on `G →₀ V`, where the action of `G` is by
left-translation on `G`; no action of `G` on `V` is assumed.
-/
@[simps] def ind₁ : Representation R G (G →₀ V) where
  toFun g       := lmapDomain _ _ (fun x ↦ g * x)
  map_one'      := by ext; simp
  map_mul' _ _  := by ext; simp [mul_assoc]

@[simp] lemma ind₁_apply₂ (g x : G) (f : G →₀ V) : ind₁ R G V g f x = f (g⁻¹ * x) := by
  simp [ind₁_apply]
  convert mapDomain_apply (mul_right_injective g) _ _
  rw [mul_inv_cancel_left]

@[simp] lemma ind₁_apply_single (g x : G) (v : V) :
    ind₁ R G V g (single x v) = single (g * x) v := by
  rw [ind₁_apply, lmapDomain_apply, mapDomain_single]

@[simp] lemma ind₁_comp_lsingle (g x : G) : ind₁ R G V g ∘ₗ lsingle x = lsingle (g * x) := by
  ext
  simp

variable {R G V} (ρ : Representation R G V)

/--
Given a representation `ρ` of `G` on `V`, `coind₁' ρ` is the representation of `G`
on `G → V`, where the action of `G` is `g f ↦ (x ↦ ρ g (f x * g))`.
-/
@[simps] def coind₁' : Representation R G (G → V) where
  toFun g := {
    toFun f x := ρ g (f (x * g))
    map_add' := sorry
    map_smul' := sorry
  }
  map_one' := sorry
  map_mul' g₁ g₂ := by ext; simp [mul_assoc]

@[simp] lemma coind₁'_apply₃ (g x : G) (f : G → V) : coind₁' ρ g f x = ρ g (f (x * g)) := rfl

/--
The linear bijection from `G → V` to `G → V`, which gives intertwines the
representations `coind₁' ρ` and `coind₁ R G V`.
-/
@[simps] def coind₁'_lequiv_coind₁ : (G → V) ≃ₗ[R] (G → V) where
  toFun f x     := ρ x (f x)
  map_add' _ _  := by ext; simp
  map_smul' _ _ := by ext; simp
  invFun f x    := ρ x⁻¹ (f x)
  left_inv _    := by ext; simp
  right_inv _   := by ext; simp

lemma coind₁'_lequiv_coind₁_comm (g : G) :
    coind₁'_lequiv_coind₁ ρ ∘ₗ coind₁' ρ g = coind₁ R G V g ∘ₗ coind₁'_lequiv_coind₁ ρ := by
  ext; simp

/--
The linear map from `V` to `G → V` taking a vector `v : V` to the comstant function
with value `V`. If `ρ` is a representation of `G` on `V`, then this map intertwines
`ρ` and `ρ.coind₁'`.
-/
@[simps] def coind₁'_ι : V →ₗ[R] (G → V) where
  toFun     := Function.const G
  map_add'  := by simp
  map_smul' := by simp

/--
The map `coind₁'_ι` intertwines a representation `ρ` of `G` on `V` with the
representation `ρ.coind₁'` of `G` on `G → V`.
-/
lemma coind₁'_ι_comm (g : G) : coind₁' ρ g ∘ₗ coind₁'_ι = coind₁'_ι ∘ₗ ρ g := by ext; simp

-- /--
-- The natural incluion of a representation `(V,ρ)` into `(G → V, coind₁ R G V)`.
-- This takes a vector `v : V` to the function `x ↦ ρ x v`.
-- -/
-- @[simps] def coind₁_ι : V →ₗ[R] (G → V) where
--   toFun v       := fun g ↦ ρ g v
--   map_add' _ _  := by ext; simp
--   map_smul' _ _ := by ext; simp

-- /--
-- The map `coind_ι ρ : V ` commutes with the actions of `G`.
-- -/
-- lemma coind₁_ι_comm (g : G) : coind₁_ι ρ ∘ₗ ρ g = coind₁ R G V g ∘ₗ coind₁_ι ρ := by ext; simp

variable {W X : Type} [AddCommGroup W] [Module R W] [AddCommGroup X] [Module R X]

@[simp] def ind₁_map (φ : V →ₗ[R] W) : (G →₀ V) →ₗ[R] (G →₀ W) := mapRange.linearMap φ

omit [Group G] in
@[simp] lemma ind₁_map_comp_lsingle (φ : V →ₗ[R] W) (x : G) :
    ind₁_map φ ∘ₗ lsingle x = lsingle x ∘ₗ φ := by ext; simp

omit [Group G] in
lemma ind₁_map_apply (φ : V →ₗ[R] W) (f : G →₀ V) : ind₁_map φ f = (mapRange.linearMap φ f) := rfl

omit [Group G] in
@[simp] lemma ind₁_map_apply₂ (φ : V →ₗ[R] W) (f : G →₀ V) (x : G) : ind₁_map φ f x = φ (f x) := rfl

omit [Group G] in
@[simp] lemma ind₁_map_single (φ : V →ₗ[R] W) (x : G) (v : V) :
    ind₁_map φ (single x v) = single x (φ v) := by
  rw [ind₁_map_apply, mapRange.linearMap_apply, mapRange_single]

omit [Group G] in
@[simp] lemma ind₁_map_id : ind₁_map (G := G) (1 : V →ₗ[R] V) = LinearMap.id := by ext; rfl

omit [Group G] in
@[simp] lemma ind₁_map_comp (φ : V →ₗ[R] W) (ψ : W →ₗ[R] X) :
    ind₁_map (G := G) (ψ ∘ₗ φ) = ind₁_map ψ ∘ₗ ind₁_map φ := by ext; rfl

/--
`ind₁' ρ` is the representation of `G` on `G →₀ V`, where the action is defined by
`ind₁' ρ g f x = f (g⁻¹ * x)`.

Note : using left-translation instead of right-translation on the group allows us to extend the
definition to representations of monoids.
-/
@[simps] def ind₁' : Representation R G (G →₀ V) where
  toFun g := lmapDomain _ _ (fun x ↦ g * x) ∘ₗ mapRange.linearMap (ρ g)
  map_one' := sorry
  map_mul' _ _ := by ext; simp [mul_assoc]

@[simp] lemma ind₁'_comp_lsingle (g x : G) : ρ.ind₁' g ∘ₗ lsingle x = lsingle (g * x) ∘ₗ ρ g := by
  ext
  simp

@[simps] def ind₁'_π : (G →₀ V) →ₗ[R] V where
  toFun f := f.sum (fun _ ↦ (1 : V →ₗ[R] V))
  map_add' := sorry
  map_smul' := sorry

omit [Group G] in
@[simp] lemma ind₁'_π_comp_lsingle (x : G) :
    ind₁'_π ∘ₗ lsingle x = LinearMap.id (R := R) (M := V) := by
  ext
  simp


lemma ind₁'_π_comm (g : G) : ind₁'_π ∘ₗ ind₁' ρ g = ρ g ∘ₗ ind₁'_π := by
  ext; simp

/--
The linear automorphism of `G →₀ V`, which gives an isomorphism
between `ind₁' ρ` and `ind₁ R G V`.
-/
@[simps] def ind₁'_lequiv : (G →₀ V) ≃ₗ[R] (G →₀ V) where
  toFun f:= f.sum (fun x v ↦ single x (ρ x⁻¹ v))
  map_add' := sorry
  map_smul' := sorry
  invFun f := f.sum (fun x v ↦ single x (ρ x v))
  left_inv f := sorry
  right_inv := sorry


@[simp] lemma ind₁'_lequiv_comp_lsingle (x : G) :
    ρ.ind₁'_lequiv.toLinearMap ∘ₗ lsingle x = lsingle x ∘ₗ ρ x⁻¹ := by ext; simp

lemma ind₁'_lequiv_comm (g : G) :
    ind₁'_lequiv ρ ∘ₗ ind₁' ρ g = ind₁ R G V g ∘ₗ ind₁'_lequiv ρ := by ext; simp

variable {ρ}

/--
If `f : V →ₗ[R] W` intertwines representations `ρ` and `ρ'` then `ind₁_map f` intertwines the
representations `ρ.ind₁'` and `ρ'.ind₁'`.
-/
lemma ind₁_map_comm {ρ' : Representation R G W} {f : V →ₗ[R] W}
    (hf : ∀ g : G, f ∘ₗ ρ g = ρ' g ∘ₗ f) (g : G) :
    ind₁_map f ∘ₗ ρ.ind₁' g = ρ'.ind₁' g ∘ₗ ind₁_map f := by
  ext : 1
  rw [LinearMap.comp_assoc, LinearMap.comp_assoc, ind₁'_comp_lsingle, ind₁_map_comp_lsingle,
    ←LinearMap.comp_assoc, ←LinearMap.comp_assoc, ind₁'_comp_lsingle, ind₁_map_comp_lsingle,
    LinearMap.comp_assoc, LinearMap.comp_assoc, hf]



-- def ind₁_π : (G →₀ V) →ₗ[R] V where
--   toFun f := f.sum (fun x ↦ (1 : V →ₗ[R] V))
--   map_add' f₁ f₂ := sum_add_index' (by simp) (by simp)
--   map_smul' r f := by simp

-- lemma ind₁_π_apply (f : G →₀ V) : ind₁_π (R := R) f = f.sum (fun x ↦ trivial R G V x) := rfl

-- @[simp] lemma ind₁_π_single (x : G) (v : V) : ind₁_π (R := R) (single x v) = v := by
--   simp [ind₁_π_apply]

-- lemma ind₁_π_comm (g : G) : (ind₁_π ρ) ∘ₗ ind₁ R G V g = (ρ g) ∘ₗ (ind₁_π ρ) := by
--   ext x
--   simp [ind₁_apply, ind₁_π_apply]

-- lemma ind₁_π_comm_apply (g : G) (f : G →₀ V) : (ind₁_π ρ) (ind₁ R G V g f) = (ρ g) (ind₁_π ρ f)
--     := by
--   rw [←LinearMap.comp_apply, ind₁_π_comm, LinearMap.comp_apply]



-- lemma ind₁'_π_naturality {ρ' : Representation R G W} {φ : V →ₗ[R] W}
--     (hφ : ∀ g : G, ρ' g ∘ₗ φ = φ ∘ₗ ρ g) :
--     ind₁'_π ∘ₗ ind₁'_map hφ = φ ∘ₗ ind₁'_π := by
--   ext x v
--   simp only [LinearMap.coe_comp, Function.comp_apply, lsingle_apply, ind₁_map_single,
--     ind₁_π_apply, map_zero, sum_single_index]
--   rw [←LinearMap.comp_apply, hφ, LinearMap.comp_apply]

variable (R G V)
/--
The map from `G →₀ V` to `G → V`. This takes `f : G →₀ V` to the function `G → V` defined by

  `fun x ↦ f x⁻¹`.

The reason for the inverse is because the `ind₁`-action of `G` on `G →₀ V` is by left-translation
and the `coind₁`-action on `G → V` is by right-translation. These choices allow the actions to be
defined in the case that `G` is only a monoid.
-/
@[simps] def ind₁_toCoind₁ : (G →₀ V) →ₗ[R] (G → V) where
  toFun f := fun x ↦ f x⁻¹
  map_add' := sorry
  map_smul' := sorry

variable {R G V}

@[simp] lemma ind₁_toCoind₁_comp_lsingle (x : G) [DecidableEq G]:
    (ind₁_toCoind₁ R G V) ∘ₗ lsingle x = lcoeFun ∘ₗ (lsingle x⁻¹) := by
  ext y z
  simp only [LinearMap.coe_comp, Function.comp_apply, lsingle_apply, ind₁_toCoind₁_apply,
    lcoeFun_apply]
  rw [single_apply]
  split_ifs with h
  · simp [h]
  · rw [single_apply, if_neg]
    contrapose! h
    rw [←h, inv_inv]



-- lemma ind₁_toCoind₁_apply₂ (f : G →₀ V) (x : G) : ind₁_toCoind₁ (R := R) f x = f x := rfl

-- lemma ind₁_toCoind₁_single [DecidableEq G] (x : G) (v : V) :
--     ind₁_toCoind₁ (R := R) (single x v) = single x v :=
--   rfl

lemma ind₁_toCoind₁_comm [DecidableEq G] (g : G) :
    ind₁_toCoind₁ R G V ∘ₗ ind₁ R G V g = coind₁ R G V g ∘ₗ ind₁_toCoind₁ R G V := by
  ext : 1
  rw [LinearMap.comp_assoc, LinearMap.comp_assoc, ind₁_toCoind₁_comp_lsingle, ind₁_comp_lsingle]
  ext v y
  simp only [coind₁_apply, LinearMap.coe_comp, Function.comp_apply, lsingle_apply,
    LinearMap.funLeft_apply, lcoeFun_apply, ind₁_toCoind₁_comp_lsingle, mul_inv_rev]
  rw [single_apply]
  split_ifs with h
  · rw [←h, inv_mul_cancel_right, single_eq_same]
  · rw [single_apply, if_neg]
    contrapose! h
    rw [h, mul_inv_cancel_right]

variable (R G V)
@[simps] def ind₁_equiv_coind₁ [Finite G] : (G →₀ V) ≃ₗ[R] (G → V) where
  toLinearMap := ind₁_toCoind₁ R G V
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

lemma ind₁_equiv_coind₁_comm [DecidableEq G] [Finite G] (g : G) :
    ind₁_equiv_coind₁ R G V ∘ₗ ind₁ R G V g = coind₁ R G V g ∘ₗ ind₁_equiv_coind₁ R G V :=
  ind₁_toCoind₁_comm g

end Representation

namespace Rep

variable {R} (M : Rep R G) (A : ModuleCat R)

def coind₁_obj : Rep R G := of (coind₁ R G A)

@[simp] lemma coind₁_obj_ρ_apply (g x : G) (f : G → A) : (coind₁_obj G A).ρ g f x = f (x * g) := rfl

@[simp] lemma coind₁_obj_ρ_apply' (g x : G) (f : coind₁_obj G A) :
    (coind₁_obj G A).ρ g f x = f (x * g) := rfl

def coind₁ : ModuleCat R ⥤ Rep R G where
  obj   := coind₁_obj G
  map φ := ⟨ofHom ((hom φ).compLeft G), fun _ ↦ rfl⟩

lemma coind₁_map_hom (A B : ModuleCat R) (φ : A ⟶ B) :
    ((coind₁ G).map φ).hom = ofHom ((hom φ).compLeft G) := rfl

@[simp] lemma coind₁_map_apply₂ (A B : ModuleCat R) (φ : A ⟶ B) (f : G → A):
    ((coind₁ G).map φ) f = φ ∘ f := rfl

-- # TODO : update Mathlib, remove fTrivial and replace it by trivialFunctor.
/--
The functor taking an `R`-module `A` to the trivial representation of `G` on `A`.
-/
def fTrivial : ModuleCat R ⥤ Rep R G where
  obj A := trivial R G A
  map f := ⟨f, by tauto⟩

@[simp] lemma fTrivial_obj_apply (A : ModuleCat R) : ((fTrivial G).obj A).V = A := rfl
@[simp] lemma fTrivial_map_hom (A B : ModuleCat R) (f : A ⟶ B) : ((fTrivial G).map f).hom = f := rfl

/--
The coinduced representation of an `R`-module `A`, defined to be the
space of function `G → A`, on which `G` acts by right-translation.
-/
def coind₁_iso_fTrivial_comp_coindFunctor : coind₁ G ≅ fTrivial Unit ⋙ coindFunctor R 1 := sorry

/--
Coinduced representations are acyclic.
-/
instance coind₁_isAcyclic (A : ModuleCat R) : ((coind₁ G).obj A).IsAcyclic :=
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


def coind₁_quotientToInvariants_iso (A : ModuleCat R) (H : Subgroup G) [H.Normal] :
    ((coind₁ G).obj A).quotientToInvariants H ≅ (coind₁ (G ⧸ H)).obj A :=
  /-
  As an `R`-module, `(coind₁ G).obj A` is the function space `G → A`, the action of `G` is by
  right translation on `G`.
  The `H`-invariants are just functions `G / H ⟶ M` with the action
  of `G / H` by translation on `G / H`. This is exactly the right hand side.
  -/
  sorry

/--
The `H`-invariants of `(coind₁ G).obj A` form an acyclic representation of `G ⧸ H`.
-/
instance coind₁_quotientToInvariants_isAcyclic (A : ModuleCat R) (H : Subgroup G) [H.Normal] :
    (((coind₁ G).obj A).quotientToInvariants H).IsAcyclic :=
  Rep.isAcyclic_of_iso (Rep.coind₁_quotientToInvariants_iso _ _ _)

variable {G}

/--
The functor which takes a representation `ρ` of `G` on `V` to the
coinduced representation on `G → V`, where the action of `G` is by `ρ` in `V` and by
right translation on `G`.
-/
def coind₁' : Rep R G ⥤ Rep R G where
  obj M := of M.ρ.coind₁'
  map := by
    intro X Y φ
    exact {
      hom := ofHom ((ModuleCat.Hom.hom φ.hom).compLeft G)
      comm g := by
        ext
        change (Action.ρ X g ≫ φ.hom) _ = _
        rw [φ.comm]
        rfl
  }
  map_id := sorry
  map_comp := sorry


/--
The inclusion of a representation `M` of `G` in the coinduced representation `coind₁'.obj M`.
-/
@[simps] def coind₁'_ι : 𝟭 (Rep R G) ⟶ coind₁' where
  app M := {
    hom    := ofHom Representation.coind₁'_ι
    comm _ := by ext : 1; exact M.ρ.coind₁'_ι_comm _
  }
  naturality := sorry

@[simps] def coind₁'_obj_iso_coind₁ : coind₁'.obj M ≅ (coind₁ G).obj M.V where
  hom := {
    hom := ofHom M.ρ.coind₁'_lequiv_coind₁.toLinearMap
    comm g := by
      ext : 1
      exact M.ρ.coind₁'_lequiv_coind₁_comm g
  }
  inv := {
    hom := ofHom M.ρ.coind₁'_lequiv_coind₁.symm.toLinearMap
    comm := sorry
  }
  hom_inv_id := sorry
  inv_hom_id := sorry

@[simps] def coind₁'_iso_forget₂_ggg_coind₁ :
    coind₁' ≅ forget₂ (Rep R G) (ModuleCat R) ⋙ coind₁ G where
  hom := {
    app M := M.coind₁'_obj_iso_coind₁.hom
    naturality := sorry
  }
  inv := {
    app M := M.coind₁'_obj_iso_coind₁.inv
    naturality := sorry
  }
  hom_inv_id := sorry
  inv_hom_id := sorry

instance coind₁'_isAcyclic : (coind₁'.obj M).IsAcyclic :=
  isAcyclic_of_iso (coind₁'_obj_iso_coind₁ M)

instance coind₁'_quotientToInvariants_isAcyclic (H : Subgroup G) [H.Normal] :
    ((coind₁'.obj M).quotientToInvariants H).IsAcyclic := by
  have : (coind₁'.obj M).quotientToInvariants H ≅ ((coind₁ G).obj M.V).quotientToInvariants H
  · sorry
  apply isAcyclic_of_iso this


variable (G)

/--
The functor taking an `R`-module `A` to the induced representation of `G` on `G →₀ A`,
where the action of `G` is by left-translation.
-/
def ind₁ : ModuleCat R ⥤ Rep R G where
  obj A := of (Representation.ind₁ R G A)
  map := by
    intro X Y φ
    exact {
      hom := ofHom (ind₁_map (ModuleCat.Hom.hom φ))
      comm g := by
        ext : 1
        simp only [RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, MonoidHom.coe_comp,
          MonoidHom.coe_coe, RingHom.coe_coe, Function.comp_apply, ModuleCat.hom_comp,
          ModuleCat.hom_ofHom]
        change ind₁_map _ ∘ₗ Representation.ind₁ R G X g = Representation.ind₁ R G Y g ∘ₗ _
        ext : 1
        rw [LinearMap.comp_assoc, LinearMap.comp_assoc, ind₁_comp_lsingle, ind₁_map_comp_lsingle,
          ind₁_map_comp_lsingle, ←LinearMap.comp_assoc, ind₁_comp_lsingle]
    }
  map_id M := by ext : 2; exact ind₁_map_id
  map_comp _ _ := by ext : 2; exact ind₁_map_comp _ _

instance (A : ModuleCat R) : FunLike ((ind₁ G).obj A) G A :=
  inferInstanceAs (FunLike (G →₀ A) _ _)

instance ind₁_isHomologyAcyclic (A : ModuleCat R) : IsHomologyAcyclic ((ind₁ G).obj A) :=
  sorry -- relies on current PR (defn of group homology).

@[ext] lemma ind₁_obj.ext {A : ModuleCat R} (f₁ f₂ : (ind₁ G).obj A) (h : ⇑f₁ = ⇑f₂) :
    f₁ = f₂ := by
  apply DFunLike.ext
  rw [h]
  exact fun _ ↦ rfl

@[simp] lemma ind₁_obj_ρ (A : ModuleCat R) : ((ind₁ G).obj A).ρ = Representation.ind₁ R G A := rfl

@[simp] lemma ind₁_map_hom (A B : ModuleCat R) (φ : A ⟶ B) :
    ((ind₁ G).map φ).hom = ofHom (ind₁_map (R := R) (G := G) (V := A) (W := B) φ.hom) := rfl

@[simp] lemma ind₁_map_apply₂ (A B : ModuleCat R) (φ : A ⟶ B) (f : (ind₁ G).obj A) (x : G):
    ((ind₁ G).map φ) f x = φ (f x) := rfl

/--
The map from `ind₁ G` to `coind₁ G`. This takes `f : G →₀ V` to the function `G → V` defined by

  `fun x ↦ f x⁻¹`.

The reason for the inverse is because the action of `G` on `ind₁` is by left-translation and the
action on `coind₁` is by right-translation. These choices allow the actions to be defined in the
case that `G` is only a monoid.
-/
def ind₁_toCoind₁ [DecidableEq G] : ind₁ G (R := R) ⟶ coind₁ G where
  app _ := {
    hom     := ofHom (Representation.ind₁_toCoind₁ _ _ _)
    comm _  := by
      ext : 1
      apply ind₁_toCoind₁_comm
  }

variable {G}

/--
The functor taking a representation `M` of `G` to the induced representation on
the space `G →₀ M`. The action of `G` on `G →₀ M.V` is by left-translation on `G` and
by `M.ρ` on `M.V`.
-/
def ind₁' : Rep R G ⥤ Rep R G where
  obj M := of M.ρ.ind₁'
  map f := {
    hom := ofHom (Representation.ind₁_map (ModuleCat.Hom.hom f.hom))
    comm g := by
      ext : 1
      apply ind₁_map_comm
      intro g
      simpa [ConcreteCategory.ext_iff] using f.comm g
  }
  map_id _ := by
    ext : 2
    apply ind₁_map_id
  map_comp _ _ := by
    ext : 2
    apply ind₁_map_comp

/--
The natural projection `ind₁'.obj M ⟶ M`, which takes `f : G →₀ M.V` to the sum of the
values of `f`.
-/
def ind₁'_π : ind₁' ⟶ 𝟭 (Rep R G) where
  app M := ofHom {
    val := Representation.ind₁'_π
    property g := by
      rw [←LinearMap.coe_comp, ←LinearMap.coe_comp, ←DFunLike.ext'_iff]
      apply ind₁'_π_comm
  }
  naturality := sorry

instance : Epi (ind₁'_π.app M) :=
  /-
  This is because `ind₁'_π.app M` is surjective.
  A pre-image of an element `m : M` is `single 1 m : G →₀ V`.
  -/
  sorry

lemma ind₁'_obj_ρ_apply (g : G) : (ind₁'.obj M).ρ g = M.ρ.ind₁' g := rfl

def ind₁'_obj_iso : ind₁'.obj M ≅ (ind₁ G).obj M.V where
  hom := by
    apply ofHom {
      val := M.ρ.ind₁'_lequiv.toLinearMap
      property g := by
        rw [←LinearMap.coe_comp, ←LinearMap.coe_comp, ←DFunLike.ext'_iff]
        exact M.ρ.ind₁'_lequiv_comm g
    }
  inv := ofHom {
    val := M.ρ.ind₁'_lequiv.symm.toLinearMap
    property g := by
      rw [←LinearMap.coe_comp, ←LinearMap.coe_comp, ←DFunLike.ext'_iff]
      sorry
  }
  hom_inv_id := sorry
  inv_hom_id := sorry

def ind₁'_iso_forget₂_ggg_ind₁ : ind₁' ≅ forget₂ (Rep R G) (ModuleCat R) ⋙ ind₁ G where
  hom := {
    app M := M.ind₁'_obj_iso.hom
    naturality := sorry
  }
  inv := {
    app M := M.ind₁'_obj_iso.inv
    naturality := sorry
  }
  hom_inv_id := sorry
  inv_hom_id := sorry

universe u
instance ind₁'_isHomologyAcyclic : IsHomologyAcyclic.{u} (ind₁'.obj M) :=
  let _ := (ind₁_isHomologyAcyclic.{u} G M.V)
  isHomologyAcyclic_of_iso (ind₁'_obj_iso M)

section FiniteGroup

variable [DecidableEq G] (A : ModuleCat R)
set_option linter.unusedSectionVars false

instance [Finite G] : IsIso ((ind₁_toCoind₁ G).app A) := sorry

def ind₁_obj_iso_coind₁_obj [Finite G] : (ind₁ G).obj A ≅ (coind₁ G).obj A :=
  asIso ((ind₁_toCoind₁ G).app A)


/--
If `G` is a finite group then `ind₁ G` is isomorphic to `coind₁ G`.
-/
def ind₁_iso_coind₁ [Finite G] : ind₁ (R := R) G ≅ coind₁ G where
  hom := ind₁_toCoind₁ G
  inv := {
    app M := (ind₁_obj_iso_coind₁_obj M).inv
    naturality := sorry
  }

/--
If `G` is a finite group then the functors `ind₁'` and `coind₁'` from `Rep R G` to itself
are isomorphic.
-/
@[simp] def ind₁'_iso_coind₁' [Finite G] : ind₁' (R := R) (G := G) ≅ coind₁' :=
  ind₁'_iso_forget₂_ggg_ind₁.trans
  ((NatIso.hcomp (Iso.refl (forget₂ (Rep R G) (ModuleCat R))) ind₁_iso_coind₁).trans
  coind₁'_iso_forget₂_ggg_coind₁.symm)

lemma ind₁'_iso_coind₁'_app_apply [Finite G] (f : G →₀ M.V) (x : G) :
    (ind₁'_iso_coind₁'.app M).hom f x = f x⁻¹ := by
  simp
  rw [coind₁'_obj_iso_coind₁]
  dsimp
  change M.ρ.coind₁'_lequiv_coind₁.symm
    ((hom (ind₁_iso_coind₁.hom.app ((forget₂ (Rep R G) (ModuleCat R)).obj M)))
    ((hom (ind₁'_iso_forget₂_ggg_ind₁.hom.app M)) f)) x = f x⁻¹
  simp
  rw [ind₁_iso_coind₁]
  dsimp
  rw [ind₁_toCoind₁]
  dsimp
  change (M.ρ x⁻¹)
    (((Representation.ind₁_toCoind₁ R G ↑((forget₂ (Rep R G) (ModuleCat R)).obj M)))
    ((hom (ind₁'_iso_forget₂_ggg_ind₁.hom.app M)) f) x) = f x⁻¹
  simp
  rw [ind₁'_iso_forget₂_ggg_ind₁]
  dsimp [ind₁'_obj_iso, ind₁'_lequiv]
  rw [hom_ofHom]
  change (M.ρ x⁻¹) (( f.sum fun x v ↦ fun₀ | x => (M.ρ x⁻¹) v) x⁻¹) = f x⁻¹
  rw [Finsupp.sum]
  simp
  rw [Finset.sum_eq_single x⁻¹]
  · simp
  · intro y _ hxy
    convert map_zero (M.ρ x⁻¹)
    rw [single_apply_eq_zero]
    intro
    symm at hxy
    contradiction
  · intro hx
    convert map_zero (M.ρ x⁻¹)
    simp at hx
    rw [hx]
    simp

instance ind₁_isAcyclic [Finite G] : IsAcyclic ((ind₁ G).obj A) :=
  isAcyclic_of_iso (ind₁_obj_iso_coind₁_obj A)

instance ind₁'_isAcyclic [Finite G] : IsAcyclic (ind₁'.obj M) :=
  isAcyclic_of_iso (ind₁'_obj_iso M)

instance coind₁_isHomologyAcyclic [Finite G] : IsHomologyAcyclic.{u} ((coind₁ G).obj A) :=
  isHomologyAcyclic_of_iso.{u} (ind₁_obj_iso_coind₁_obj A).symm

instance coind₁'_isHomologyAcyclic [Finite G] : IsHomologyAcyclic.{u} (coind₁'.obj M) :=
  isHomologyAcyclic_of_iso.{u} (coind₁'_obj_iso_coind₁ M)

end FiniteGroup

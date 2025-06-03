import Mathlib
import ClassFieldTheory.GroupCohomology._1_TateCohomology_def
import ClassFieldTheory.GroupCohomology._4_coind1_and_ind1

/-!
We define two "coinduction" functors taking values in the acyclic objects of `Rep R G`.

The first is `coind₁ G : ModuleCat R ⥤ Rep R G`.

This takes an `R`-module `A` to the space of linear maps `R[G] ⟶ A`, where `G` acts by
its action of `R[G]`. Note that the linear maps `R[G] ⟶ A` are equivalent to the functions
`G → A`, since the elements of `G` form a basis for the group ring `R[G]`.

The second functor is `coind₁' : Rep R G ⥤ Rep R G`.

This takes a representation `M` of `G` to the space of
This takes an `R`-module `A` to the space of linear maps `R[G] ⟶ M`, where `G` acts by
conjugation (i.e. on both `R[G]` and on `M`).

The representations `coind₁'.obj M` and `(coind₁ G).obj M.V` are isomorphic (although
the isomorphism is not simply the identity map on the space of functions `G → M`, since the
actions of `G` on these spaces are not the same).

For any `M : Rep R G` we construct two short exact sequences
(the second defined only for finite `G`):

  `0 ⟶ M ⟶ coind₁'.obj M ⟶ up M ⟶ 0` and `0 ⟶ down M ⟶ coind₁'.obj M ⟶ M ⟶ 0`.

These can be used for dimension-shifting because `coind₁'.obj M` is acyclic.
-/

open
  Rep
  Representation
  CategoryTheory
  NatTrans
  ConcreteCategory
  Limits
  groupCohomology

noncomputable section

variable {R G : Type} [CommRing R] [Group G] (M : Rep R G)

namespace Rep.dimensionShift


-- /--
-- The inclusion of `M` in its coinduced representation. If we think of the
-- coinduced representation as the function space `G → M`, then this inclusion is
-- the map `m ↦ (fun x ↦ M.ρ x m)`.
-- -/
-- @[simps] def coind₁'_ι.app : M ⟶ coind₁'.obj M where
--   hom := ofHom (Representation.coind₁_ι M.ρ)
--   comm g := by
--     ext : 1
--     apply Representation.coind₁_ι_comm

-- def coind₁' : Rep R G ⥤ Rep R G := forget₂ _ _ ⋙ coind₁ G

@[simp] lemma forget₂_map_apply {N : Rep R G} (f : M ⟶ N) :
    (forget₂ (Rep R G) (ModuleCat R)).map f = f.hom :=
  rfl

lemma coind₁'_ι.app_apply {M : Rep R G} (m : M) (x : G) : (coind₁'_ι.app M m) x = M.ρ x m := sorry

/--
The map from `M` to its coinduced representation is a monomorphism.
-/
instance : Mono (coind₁'_ι.app M) := by
  /-
  This is because the map is injective.
  (Choose `v` in `R[G]` such that `ε R G v = 1`; for example we can take
  `v := leftRegular.of 1`. Then we have `m = (coind₁'_ι.app M m).toFun v`.)
  -/
  sorry

/--
The functor taking `M : Rep R G` to `up.obj M`, defined by the short exact sequence

  `0 ⟶ M ⟶ coind₁'.obj M ⟶ up.obj M ⟶ 0`.

Since `coind₁'.obj M` is acyclic, the cohomology of `up.obj M` is a shift by one
of the cohomology of `M`.
-/
@[simps] def up : Rep R G ⥤ Rep R G where
  obj M := cokernel (coind₁'_ι.app M)
  map f:= by
    apply cokernel.desc _ (coind₁'.map f ≫ cokernel.π _)
    rw [←Category.assoc, ←coind₁'_ι.naturality, Category.assoc, cokernel.condition, comp_zero]
  map_id := sorry
  map_comp := sorry

/--
The functor taking `M : Rep R G` to the short complex:

  `M ⟶ coind₁'.obj M ⟶ up.obj M`.

-/
@[simps] def upSes : Rep R G ⥤ ShortComplex (Rep R G) where
  obj M := {
    X₁ := M
    X₂ := coind₁'.obj M
    X₃ := up.obj M
    f := coind₁'_ι.app M
    g := cokernel.π (coind₁'_ι.app M)
    zero := cokernel.condition (coind₁'_ι.app M)
  }
  map f := {
    τ₁ := f
    τ₂ := coind₁'.map f
    τ₃ := up.map f
    comm₁₂ := coind₁'_ι.naturality f
    comm₂₃ := (cokernel.π_desc _ _ _).symm
  }
  map_comp f g := by
    congr
    rw [Functor.map_comp]
  map_id M := by
    congr
    rw [up_map]
    apply IsColimit.desc_self

/--
`upSes.obj M` is a short exact sequence of representations.
-/
lemma up_shortExact : (upSes.obj M).ShortExact where
  exact := ShortComplex.exact_cokernel (coind₁'_ι.app M)
  mono_f := inferInstanceAs (Mono (coind₁'_ι.app M))
  epi_g := coequalizer.π_epi

lemma up_shortExact_res (H : Subgroup G) : ((upSes.obj M).map (res H)).ShortExact := by
  rw [res_respectsShortExact]
  exact up_shortExact M

abbrev up_π : coind₁' ⟶ up (R := R) (G := G) where
  app _             := (upSes.obj _).g
  naturality _ _ _  := (upSes.map _).comm₂₃

/--
The connecting homomorphism from `H⁰(G,up M)` to `H¹(G,M)` is
an epimorphism (i.e. surjective).
-/
lemma up_δ_zero_epi : Epi (δ (up_shortExact M) 0 1 rfl) :=
  /-
  The next term in the long exact sequence is `H¹(G,coind₁'.obj M)`, which is zero
  since coinduced representations are acyclic.
  -/
  sorry

/--
The connecting homomorphism from `Hⁿ⁺¹(G,up M)` to `Hⁿ⁺²(G,M)` is an isomorphism.
-/
instance up_δ_isIso (n : ℕ) : IsIso (δ (up_shortExact M) (n + 1) (n + 2) rfl) :=
  /-
  This map is sandwiched between two zeros by `groupCohomology.ofCoind₁`.
  -/
  sorry

def up_δiso (n : ℕ) : groupCohomology (up.obj M) (n + 1) ≅ groupCohomology M (n + 2) :=
  asIso (δ (up_shortExact M) (n + 1) (n + 2) rfl)

def up_δiso_natTrans (n : ℕ) : up ⋙ functor R G (n + 1) ≅ functor R G (n + 2) where
  hom := {
    app M := (up_δiso M n).hom
    naturality := sorry
  }
  inv := {
    app M := (up_δiso M n).inv
    naturality := sorry
  }

/--
The connecting homomorphism from `H^{n+1}(G,dimensionShift M)` to `H^{n+2}(G,M)` is
an epimorphism (i.e. surjective).
-/
lemma up_δ_zero_epi_res (H : Subgroup G) : Epi (δ (up_shortExact_res M H) 0 1 rfl) :=
  /-
  The next term in the long exact sequence is zero.
  -/
  sorry

/--
The connecting homomorphism from `H^{n+1}(G,up M)` to `H^{n+2}(G,M)` is an
isomorphism.
-/
instance up_δ_isIso_res (H : Subgroup G) (n : ℕ) : IsIso (δ (up_shortExact_res M H) (n + 1) (n + 2) rfl)
  :=
  /-
  This map is sandwiched between two zeros by `groupCohomology.ofCoind₁`.
  -/
  sorry

def up_δiso_res (H : Subgroup G) (n : ℕ) :
    groupCohomology (up.obj M ↓ H) (n + 1) ≅ groupCohomology (M ↓ H) (n + 2) :=
  asIso (δ (up_shortExact_res M H) (n + 1) (n + 2) rfl)

lemma ind₁'_obj_ρ : (ind₁'.obj M).ρ = M.ρ.ind₁' := rfl

lemma ind₁'_obj_ρ_apply (g : G) : (ind₁'.obj M).ρ g = M.ρ.ind₁' g := rfl

abbrev ind₁'_toCoind₁' [DecidableEq G]: ind₁' (R := R) (G := G) ⟶ coind₁' :=
  ind₁'_iso_forget₂_ggg_ind₁.hom ≫ (𝟙 _ ◫ ind₁_toCoind₁ G) ≫ coind₁'_iso_forget₂_ggg_coind₁.inv

lemma ind₁'_π.app_hom : (ind₁'_π.app M).hom = ofHom Representation.ind₁'_π := rfl

lemma ind₁'_π.app_apply (f : ind₁'.obj M) :
    (ind₁'_π.app M) f = Finsupp.sum f (fun _ ↦ LinearMap.id (R := R)) := rfl

def down : Rep R G ⥤ Rep R G where
  obj M := kernel (ind₁'_π.app M)
  map φ := by
    dsimp only [Functor.id_obj]
    apply kernel.lift _ (kernel.ι _ ≫ ind₁'.map φ)
    rw [Category.assoc, ind₁'_π.naturality, ←Category.assoc, kernel.condition, zero_comp]
  map_id := sorry
  map_comp := sorry

abbrev down_ses : ShortComplex (Rep R G) where
  X₁ := down.obj M
  X₂ := ind₁'.obj M
  X₃ := M
  f := kernel.ι (ind₁'_π.app M)
  g := ind₁'_π.app M
  zero := kernel.condition (ind₁'_π.app M)

lemma down_shortExact : (down_ses M).ShortExact where
  exact   := ShortComplex.exact_kernel (ind₁'_π.app M)
  mono_f  := inferInstance
  epi_g   := inferInstance

lemma down_shortExact_res (H : Subgroup G) :
    ((down_ses M).map (res H)).ShortExact := by
  rw [res_respectsShortExact]
  exact down_shortExact M

variable [DecidableEq G] [Finite G]

/--
The connecting homomorphism `H⁰(G,down.obj M) ⟶ H¹(G, M)` is an epimorphism if `G` is finite.
-/
lemma down_δ_zero_epi : Epi (δ (down_shortExact M) 0 1 rfl) := by
  have := ind₁'_isAcyclic M
  sorry

/--
The connecting homomorphism `H⁰(H,down.obj M ↓ H) ⟶ H¹(H, M ↓ H)` is an epimorphism if
`H` is a subgroup of a finite group `G`.
-/
lemma down_δ_zero_res_epi (H : Subgroup G) : Epi (δ (down_shortExact_res M H) 0 1 rfl) := by
  have := ind₁'_isAcyclic M
  sorry

/--
The connecting homomorphism `Hⁿ⁺¹(G,down.obj M) ⟶ Hⁿ⁺²(G, M)` is an isomorphism
if `G` is finite.
-/
instance down_δ_isIso  (n : ℕ) : IsIso (δ (down_shortExact M) (n + 1) (n + 2) rfl) := by
  have := ind₁'_isAcyclic M
  sorry

def down_δiso (n : ℕ) : groupCohomology M (n + 1) ≅ groupCohomology (down.obj M) (n + 2) :=
  asIso (δ (down_shortExact M) (n + 1) (n + 2) rfl)

def down_δiso_natTrans (n : ℕ) : functor R G (n + 1) ≅ down ⋙ functor R G (n + 2) where
  hom := {
    app M := (down_δiso M n).hom
    naturality := sorry
  }
  inv := {
    app M := (down_δiso M n).inv
    naturality := sorry
  }

/--
The connecting homomorphism `Hⁿ⁺¹(H,down.obj M ↓ H) ⟶ Hⁿ⁺²(H, M ↓ H)` is an isomorphism
if `H` is a subgroup of a finite group `G`.
-/
instance down_δ_res_isIso (n : ℕ) (H : Subgroup G) :
    IsIso (δ (down_shortExact_res M H) (n + 1) (n + 2) rfl) := by
  have := ind₁'_isAcyclic M
  sorry

def down_δiso_res (H : Subgroup G) (n : ℕ) :
    groupCohomology (M ↓ H) (n + 1) ≅ groupCohomology (down.obj M ↓ H) (n + 2) :=
  asIso (δ (down_shortExact_res M H) (n + 1) (n + 2) rfl)

end dimensionShift

end Rep

namespace groupCohomology

variable [Finite G]
open Rep
  dimensionShift

/--
All of the Tate cohomology groups of `(coind₁ G).obj A ↓ H` are zero.
-/
lemma TateCohomology_coind₁ (A : ModuleCat R) (H : Subgroup G) (n : ℕ) :
    IsZero ((TateCohomology n).obj ((Rep.coind₁ G).obj A ↓ H)) :=
  /-
  For `n > 0` this is proved elsewhere for `groupCohomology`.
  For `n < -1` this is proved elsewhere for `groupHomology` (and relies on a current PR).
  The cases `n = 0` and `n = -1` need to be proved here.
  -/
  sorry -- requires current PR.

/--
All of the Tate cohomology groups of `coind₁'.obj M ↓ H` are zero.
-/
lemma TateCohomology_coind₁' (M : Rep R G) (H : Subgroup G) (n : ℕ) :
    IsZero ((TateCohomology n).obj (coind₁'.obj M ↓ H)) :=
  /-
  It is shown earier that `coind₁'.obj M ≅ (coind₁ G).obj M.V`, so we can use the previous result.
  -/
  sorry

lemma TateCohomology_ind₁' (M : Rep R G) (H : Subgroup G) (n : ℕ) :
    IsZero ((TateCohomology n).obj (ind₁'.obj M ↓ H)) :=
  /-
  It is shown earier that `ind₁'.obj M ≅ coind₁'.obj M`, so we can use the previous result.
  -/
  sorry

instance (M : Rep R G) (n : ℤ) : IsIso (TateCohomology.δ (up_shortExact M) n) :=
  /-
  This follows from `TateCohomology_coind₁'`.
  -/
  sorry

instance (M : Rep R G) (n : ℤ) : IsIso (TateCohomology.δ (down_shortExact M) n) := by
  /-
  This follows from `TateCohomology_coind₁'`.
  -/
  sorry

def upδiso_Tate (n : ℤ) (M : Rep R G) :
    (TateCohomology n).obj (up.obj M) ≅ (TateCohomology (n + 1)).obj M :=
  asIso (TateCohomology.δ (up_shortExact M) n)

def downδiso_Tate (n : ℤ) (M : Rep R G) :
    (TateCohomology n).obj M ≅ (TateCohomology (n + 1)).obj (down.obj M) :=
  asIso (TateCohomology.δ (down_shortExact M) n)

end groupCohomology

end

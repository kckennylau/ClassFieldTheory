import ClassFieldTheory.Mathlib.ValuativeLemmas
import Mathlib

/-!
# Definition of Non-Archimedean Local Fields

We define non-archimedean local fields as a class `IsNonArchLF`.

-/

universe u v

class IsNonarchLocalField (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] : Prop extends
  ValuativeTopology K,
  IsUniformAddGroup K,
  LocallyCompactSpace K,
  ValuativeRel.IsNontrivial K
  -- ValuativeRel.IsRankLeOne K -- TODO: in future mathlib
  -- IsTopologicalDivisionRing K,
  -- CompleteSpace K,
  -- ValuativeRel.IsDiscrete K

open ValuativeRel

namespace ValuativeExtension

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [ValuativeRel A] [ValuativeRel B]
  [Algebra A B] [ValuativeExtension A B] (a b : A)

lemma algebraMap_le : valuation B (algebraMap A B a) ≤ valuation B (algebraMap A B b) ↔
    valuation A a ≤ valuation A b := by
  simp_rw [← Valuation.Compatible.rel_iff_le, rel_iff_rel]

lemma algebraMap_eq : valuation B (algebraMap A B a) = valuation B (algebraMap A B b) ↔
    valuation A a = valuation A b := by
  simp_rw [le_antisymm_iff, algebraMap_le]

lemma algebraMap_lt : valuation B (algebraMap A B a) < valuation B (algebraMap A B b) ↔
    valuation A a < valuation A b := by
  simp_rw [lt_iff_le_not_ge, algebraMap_le]

end ValuativeExtension

namespace IsNonarchLocalField

section Padic

variable (p : ℕ) [Fact p.Prime]

instance : LocallyCompactSpace ℚ_[p] := inferInstance

instance : IsNonarchLocalField ℚ_[p] where
  mem_nhds_iff := sorry

end Padic

variable (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsNonarchLocalField K]
  (L : Type v) [Field L] [ValuativeRel L] [UniformSpace L] [IsNonarchLocalField L]

instance : (Valued.v : Valuation K (ValueGroupWithZero K)).IsNontrivial :=
  ValuativeRel.isNontrivial_iff_isNontrivial.mp inferInstance

instance : IsTopologicalDivisionRing K := inferInstance

instance : ValuativeRel.IsRankLeOne K := sorry

noncomputable
instance : (Valued.v : Valuation K (ValueGroupWithZero K)).RankOne where
  hom := IsRankLeOne.nonempty.some.emb
  strictMono' := IsRankLeOne.nonempty.some.strictMono

open scoped Valued in
instance : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K

instance : IsDiscreteValuationRing 𝒪[K] :=
  (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mp inferInstance).2.1

instance : (Valued.v : Valuation K (ValueGroupWithZero K)).IsNontrivial :=
  ValuativeRel.isNontrivial_iff_isNontrivial.mp inferInstance

noncomputable
instance : (Valued.v : Valuation K (ValueGroupWithZero K)).RankOne where
  hom := IsRankLeOne.nonempty.some.emb
  strictMono' := IsRankLeOne.nonempty.some.strictMono

open scoped Valued in
instance : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K

open Valued.integer in
instance compactSpace_integer : CompactSpace 𝒪[K] :=
  properSpace_iff_compactSpace_integer.mp inferInstance

open Valued.integer in
instance : CompleteSpace 𝒪[K] :=
  (compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
    (compactSpace_integer K)).1

open Valued.integer in
instance : Finite 𝓀[K] :=
  (properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mp
    inferInstance).2.2

theorem prime_ringChar : (ringChar 𝓀[K]).Prime :=
  CharP.char_is_prime 𝓀[K] _

open Valued.integer in
instance : CompleteSpace K :=
  (properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mp
    inferInstance).1

/-- This is how you show that there is a uniformiser (which in Mathlib is called `Irreducible`). -/
example : ∃ ϖ : 𝒪[K], Irreducible ϖ :=
  IsDiscreteValuationRing.exists_irreducible _

example : ∀ ϖ : 𝒪[K], Irreducible ϖ → ϖ ≠ 0 :=
  fun _ h ↦ h.ne_zero

lemma associated_iff_of_irreducible (x y : 𝒪[K]) (hx : Irreducible x) :
    Associated y x ↔ Irreducible y :=
  ⟨fun hyx ↦ hyx.symm.irreducible hx,
  fun hy ↦ IsDiscreteValuationRing.associated_of_irreducible _ hy hx⟩

theorem open_OK : IsOpen (𝒪[K] : Set K) :=
  sorry

def compactOpenOK : TopologicalSpace.CompactOpens K where
  carrier := 𝒪[K]
  isCompact' := isCompact_iff_compactSpace.mpr <| compactSpace_integer K
  isOpen' := open_OK K

-- TODO: add Haar measure (or check that it works with `example`)

variable [Algebra K L] [ValuativeExtension K L]

instance : FiniteDimensional K L :=
  sorry

omit [UniformSpace K] [IsNonarchLocalField K] [UniformSpace L] [IsNonarchLocalField L] in
lemma algebraMap_mem_integer (x : 𝒪[K]) : (algebraMap 𝒪[K] L) x ∈ 𝒪[L] := by
  rcases x with ⟨x, hx⟩
  change valuation L (algebraMap K L x) ≤ 1
  simpa only [map_one] using (ValuativeExtension.algebraMap_le K L x 1).mpr hx

instance : Algebra 𝒪[K] 𝒪[L] where
  smul r a := ⟨r • a, Algebra.smul_def r (a : L) ▸ mul_mem (algebraMap_mem_integer ..) a.2⟩
  algebraMap := (algebraMap K L).restrict 𝒪[K] 𝒪[L] fun x hx => algebraMap_mem_integer K L ⟨x, hx⟩
  commutes' _ _ := Subtype.ext (Algebra.commutes _ _)
  smul_def' _ _ := Subtype.ext (Algebra.smul_def _ _)

namespace ValuativeRel

theorem posSubmonoid.ne_zero {R : Type u} [CommRing R] [ValuativeRel R]
    (x : posSubmonoid R) : x.val ≠ 0 :=
  mt (· ▸ rel_rfl) x.2

theorem valuation_surjective₀ {F : Type u} [Field F] [ValuativeRel F]
    (γ : ValueGroupWithZero F) : ∃ x : F, valuation F x = γ :=
  let ⟨x, y, hxy⟩ := valuation_surjective γ
  ⟨x / y.val, by rw [map_div₀, hxy]⟩

theorem units_map_valuation_surjective {F : Type u} [Field F] [ValuativeRel F]
    (γ : (ValueGroupWithZero F)ˣ) : ∃ x : Fˣ, Units.map (valuation F) x = γ :=
  let ⟨x, hx⟩ := valuation_surjective₀ γ.val
  ⟨Units.mk0 x (mt (by rw [← hx, ·, map_zero]) γ.ne_zero),
    Units.ext <| by simpa using hx⟩

end ValuativeRel

theorem density (y : Lˣ) : ∃ (x : Kˣ), Valued.v (algebraMap K L x) ≤ Valued.v y.val := sorry

instance : ContinuousSMul K L := by
  apply continuousSMul_of_algebraMap K L (continuous_of_continuousAt_zero _ _)
  simp only [ContinuousAt, map_zero]
  obtain B₁ := Valued.hasBasis_nhds_zero K (ValueGroupWithZero K)
  obtain B₂ := Valued.hasBasis_nhds_zero L (ValueGroupWithZero L)
  apply (Filter.HasBasis.tendsto_iff B₁ B₂).mpr
  simp only [Set.mem_setOf_eq, true_and]
  intro b hb
  obtain ⟨a, ha⟩ := IsNonarchLocalField.ValuativeRel.units_map_valuation_surjective b
  rw [← ha]
  obtain ⟨a', ha'⟩ := density K L a
  use Units.map (valuation K) (a')
  intro x hx
  simp only [Units.coe_map, MonoidHom.coe_coe] at *
  change valuation _ _ ≤ valuation _ _ at ha'
  change valuation _ _ < valuation _ _
  change valuation _ _ < valuation _ _  at hx
  exact lt_of_lt_of_le ((ValuativeExtension.algebraMap_lt K L x a'.val).mpr hx) ha'


-- TODO: Maddy

instance : Module.Finite 𝒪[K] 𝒪[L] :=
  sorry

@[fun_prop] lemma continuous_algebraMap : Continuous (algebraMap K L) :=
  _root_.continuous_algebraMap K L

instance : IsScalarTower 𝒪[K] K L := inferInstance

instance : IsScalarTower 𝒪[K] 𝒪[L] L := sorry --inferInstance

noncomputable def e : ℕ :=
  Ideal.ramificationIdx (algebraMap 𝒪[K] 𝒪[L]) 𝓂[K] 𝓂[L]

theorem e_spec {ϖK : 𝒪[K]} {ϖL : 𝒪[L]} (hk : Irreducible ϖK) (hl : Irreducible ϖL) :
    Associated (ϖL ^ e K L) (algebraMap 𝒪[K] 𝒪[L] (ϖK)) :=
  sorry

noncomputable def f : ℕ :=
  Ideal.inertiaDeg 𝓂[K] 𝓂[L]

instance : 𝓂[L].LiesOver 𝓂[K] := sorry

theorem f_spec : Nat.card 𝓀[K] ^ f K L = Nat.card 𝓀[K] := sorry

lemma non_triv_maximal_embedding : (Ideal.map (algebraMap 𝒪[K] 𝒪[L]) 𝓂[K]) ≠ ⊥
  ∧ (Ideal.map (algebraMap 𝒪[K] 𝒪[L]) 𝓂[K]) ≠ ⊤ := sorry

theorem e_pos : 0 < e K L := sorry

theorem f_pos : 0 < f K L := Ideal.inertiaDeg_pos 𝓂[K] 𝓂[L]

lemma irreducible_pow_span_pow {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {ϖ : R} (h : Irreducible ϖ) {n : ℕ} : Ideal.span {ϖ ^ n} = (Ideal.span {ϖ})^(n) := sorry

lemma unique_maximal_ideal_factorization [DecidableEq (Ideal ↥𝒪[L])] : (UniqueFactorizationMonoid.factors
  (Ideal.map (algebraMap 𝒪[K] 𝒪[L]) 𝓂[K])).toFinset = {𝓂[L]} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible (non_triv_maximal_embedding K L).1 hϖ
  have irred_ele_span_irred_ideal : Irreducible (Ideal.span {ϖ}) := by
    sorry
  rw [hn, Irreducible.maximalIdeal_eq hϖ, irreducible_pow_span_pow hϖ]
  simp
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible irred_ele_span_irred_ideal]
  simp
  rw [Multiset.nsmul_singleton, Multiset.toFinset_replicate]
  have g : n ≠ 0 := by
    intro h
    rw [h, irreducible_pow_span_pow] at hn
    simp at hn
    exact False.elim ((non_triv_maximal_embedding K L).2 hn)
    assumption
  simp
  intro a
  exact False.elim (g a)

theorem e_mul_f_eq_n : e K L * f K L = Module.finrank K L := by
  symm
  calc
  _ = (Ideal.ramificationIdx (algebraMap 𝒪[K] 𝒪[L]) 𝓂[K] 𝓂[L]) * (Ideal.inertiaDeg 𝓂[K] 𝓂[L]) := by
    symm
    rw [← Ideal.sum_ramification_inertia 𝒪[L] 𝓂[K]]
    classical rw [unique_maximal_ideal_factorization]
    rfl
    exact IsDiscreteValuationRing.not_a_field ↥𝒪[K]

-- TODO: generalise to extensions of DVRs.
class IsUnramified : Prop where
  e_eq_one : e K L = 1

theorem unramified_def : IsUnramified K L ↔ e K L = 1 :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

theorem unramified_iff_unramified : IsUnramified K L ↔ Algebra.Unramified 𝒪[K] 𝒪[L] :=
  sorry

section make_finite_extension

/- # Constructing a finite extension from a minimal set of assumptions. -/

variable (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]

/-
open scoped Valued in
#check (inferInstance : NormedField K)
#check (inferInstance : Valuation.RankOne (Valued.v (R := K)))
-/

open scoped Valued NormedField in
include K in
theorem isNonarchLocalField_of_finiteDimensional :
    ∃ (_ : ValuativeRel L) (_ : ValuativeExtension K L)
    (_ : UniformSpace L), IsNonarchLocalField L := by
  letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
  haveI : IsUltrametricDist L := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_nnnorm
    isNonarchimedean_spectralNorm
  let v := NormedField.valuation (K := L)
  haveI := locallyCompactSpace_of_complete_of_finiteDimensional K L
  refine ⟨inferInstance, ⟨fun k₁ k₂ ↦ ?_⟩, inferInstance, .mk⟩
  rw [Valuation.Compatible.rel_iff_le (v := v),
    Valuation.Compatible.rel_iff_le (v := ValuativeRel.valuation K)]
  change spectralNorm K L _ ≤ spectralNorm K L _ ↔ _
  rw [spectralNorm_extends, spectralNorm_extends]
  change Valued.norm _ ≤ Valued.norm _ ↔ _
  rw [Valued.norm_def, Valued.norm_def, NNReal.coe_le_coe,
    (Valuation.RankOne.strictMono Valued.v).le_iff_le]
  rfl

/- TODO:
1. Show that given a valuative extension, we can already make a local field (generalise the above
   proof)
2. Show that given an extension of local fields, the valuative rel is the same as this one given by
   the spectral norm.
3. As a result, conclude that there is only one valuative rel that is a valuative extension in the
   situation above.
-/

end make_finite_extension

end IsNonarchLocalField

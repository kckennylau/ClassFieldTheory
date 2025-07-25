import ClassFieldTheory.LocalCFT.Continuity
import ClassFieldTheory.Mathlib.Topology.Algebra.Module.FiniteDimension
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
  simpa only [map_one] using (ValuativeExtension.algebraMap_le (B := L)).mpr hx

instance : Algebra 𝒪[K] 𝒪[L] where
  smul r a := ⟨r • a, Algebra.smul_def r (a : L) ▸ mul_mem (algebraMap_mem_integer ..) a.2⟩
  algebraMap := (algebraMap K L).restrict 𝒪[K] 𝒪[L] fun x hx => algebraMap_mem_integer K L ⟨x, hx⟩
  commutes' _ _ := Subtype.ext (Algebra.commutes _ _)
  smul_def' _ _ := Subtype.ext (Algebra.smul_def _ _)


omit  [UniformSpace K][IsNonarchLocalField K][UniformSpace L][IsNonarchLocalField L]
lemma IsInjective : Function.Injective ⇑(algebraMap ↥𝒪[K] ↥𝒪[L]) := by
  refine fun x {y} hxy => ?_
  have{s}: (algebraMap ↥𝒪[K] ↥𝒪[L]) s = ((algebraMap K L).restrict 𝒪[K] 𝒪[L]
    fun x hx => algebraMap_mem_integer K L ⟨x, hx⟩) s :=rfl
  obtain ⟨x,sx⟩ :=x
  obtain ⟨y,sy⟩ :=y
  simpa[this, RingHom.restrict, Subtype.eq_iff, RingHom.codRestrict_apply,
    RingHom.restrict_apply, algebraMap.coe_inj] using hxy
variable[UniformSpace K][IsNonarchLocalField K][UniformSpace L][IsNonarchLocalField L]


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
  exact lt_of_lt_of_le ((ValuativeExtension.algebraMap_lt ).mpr hx) ha'


-- TODO: Maddy

instance : Module.Finite 𝒪[K] 𝒪[L] :=
  sorry

instance : IsScalarTower 𝒪[K] K L := inferInstance

instance : IsScalarTower 𝒪[K] 𝒪[L] L := sorry --inferInstance

noncomputable def e : ℕ :=
  Ideal.ramificationIdx (algebraMap 𝒪[K] 𝒪[L]) 𝓂[K] 𝓂[L]

theorem e_spec {ϖK : 𝒪[K]} {ϖL : 𝒪[L]} (hk : Irreducible ϖK) (hl : Irreducible ϖL) :
    Associated (ϖL ^ e K L) (algebraMap 𝒪[K] 𝒪[L] (ϖK)) :=by
  obtain ⟨r, hn⟩ :=
   IsDiscreteValuationRing.ideal_eq_span_pow_irreducible ((Submodule.ne_bot_iff (Ideal.map (algebraMap ↥𝒪[K] ↥𝒪[L])
        (IsLocalRing.maximalIdeal ↥𝒪[K]))).mpr ⟨ algebraMap 𝒪[K] 𝒪[L] (ϖK),
        ⟨by simpa [((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖK).mp hk),
        Ideal.map_span, Set.image_singleton] using (Ideal.mem_span_singleton_self _),
        (map_ne_zero_iff (algebraMap ↥𝒪[K] ↥𝒪[L]) (IsInjective _ _)).mpr hk.ne_zero⟩⟩) hl
  simp only [← Ideal.span_singleton_eq_span_singleton, ← Set.image_singleton, ← Ideal.map_span, ←
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖK).mp hk), hn]
  simp only [Set.image_singleton,← Ideal.span_singleton_pow]
  refine congrArg (HPow.hPow (Ideal.span {ϖL})) ?_
  have l1{s:ℕ} : sSup {n| n≤ s} =s := csSup_eq_of_is_forall_le_of_forall_le_imp_ge (
      Set.nonempty_def.mpr ⟨0,by simp only [Set.mem_setOf_eq, zero_le]⟩
    ) (fun a ha => by simpa using ha) (fun b sh => sh s (by simp only [Set.mem_setOf_eq, le_refl]))
  have: sSup {n | (IsLocalRing.maximalIdeal ↥𝒪[L]) ^ r ≤ (IsLocalRing.maximalIdeal ↥𝒪[L]) ^ n}
      =r := by
      have {n}:(IsLocalRing.maximalIdeal ↥𝒪[L]) ^ r ≤ (IsLocalRing.maximalIdeal ↥𝒪[L]) ^ n
       ↔  r ≥ n := by
        refine StrictAnti.le_iff_le (Ideal.pow_right_strictAnti
        (IsLocalRing.maximalIdeal ↥𝒪[L])
        (IsDiscreteValuationRing.not_a_field ↥𝒪[L]) Ideal.IsPrime.ne_top')
      simp only [this, l1]
  simp only [e, Ideal.ramificationIdx,hn,← Ideal.span_singleton_pow
  ,← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖL).mp hl,this]


noncomputable def f : ℕ :=
  Ideal.inertiaDeg 𝓂[K] 𝓂[L]

instance : 𝓂[L].LiesOver 𝓂[K] := sorry

-- bad instance : IsLocalHom (algebraMap 𝒪[K] 𝒪[L]) := sorry

instance :  Algebra 𝓀[K] 𝓀[L] :=Ideal.Quotient.algebraQuotientOfLEComap
    (IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝓂[L])).ge

theorem f_spec : Nat.card 𝓀[K] ^ f K L = Nat.card 𝓀[L] :=by
  have s :Module.finrank 𝓀[K] 𝓀[L] = f K L :=by
    simp only [f, Ideal.inertiaDeg,IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝓂[L]), ↓reduceDIte,
    IsLocalRing.ResidueField]
  letI : Fintype 𝓀[K] :=Fintype.ofFinite (IsLocalRing.ResidueField ↥𝒪[K])
  letI : Fintype 𝓀[L] :=Fintype.ofFinite (IsLocalRing.ResidueField ↥𝒪[L])
  rw[← s,Nat.card_eq_fintype_card,← Module.card_eq_pow_finrank
  ,Nat.card_eq_fintype_card]


lemma non_triv_maximal_embedding : (Ideal.map (algebraMap 𝒪[K] 𝒪[L]) 𝓂[K]) ≠ ⊥
  ∧ (Ideal.map (algebraMap 𝒪[K] 𝒪[L]) 𝓂[K]) ≠ ⊤ :=by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  refine ⟨by
    simpa[(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
    Set.image_singleton, ne_eq, Ideal.span_singleton_eq_bot] using
    (map_ne_zero_iff (algebraMap ↥𝒪[K] ↥𝒪[L]) (IsInjective _ _)).mpr hϖ.ne_zero,?_⟩
  by_contra sa
  obtain ⟨j,sj2⟩:=by simpa only[←sa,
  (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
    Set.image_singleton,Ideal.mem_span_singleton'] using Submodule.mem_top (R:=↥𝒪[L]) (x:=(1:↥𝒪[L]))
  have h:¬  IsUnit ((algebraMap ↥𝒪[K] ↥𝒪[L]) ϖ) :=by
    refine Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr ?_
    have l1:1=(valuation L) ↑((algebraMap ↥𝒪[K] ↥𝒪[L]) 1) :=by
      simp only [map_one, OneMemClass.coe_one]
    have{s}: ((algebraMap ↥𝒪[K] ↥𝒪[L]) s ).1 =(algebraMap K L) s.1 :=rfl
    simp only[this,l1,ValuativeExtension.algebraMap_lt]
    rw[OneMemClass.coe_one,map_one]
    exact Valuation.integer.v_irreducible_lt_one hϖ
  exact h (isUnit_iff_exists.mpr ⟨j,⟨by simp only [← sj2,mul_comm],by simp only [← sj2]⟩⟩)


instance : IsDedekindDomain 𝒪[L] :=by
  exact instIsDedekindDomainOfIsDomainOfIsDedekindRing ↥𝒪[L]

theorem e_pos : 0 < e K L :=
 Nat.zero_lt_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx_ne_zero
   (non_triv_maximal_embedding _ _).1 ( Ideal.IsMaximal.isPrime' _)  (
       IsLocalRing.le_maximalIdeal  (non_triv_maximal_embedding _ _).2  ))


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

open scoped NormedField in
include K in
theorem isNonarchLocalField_of_finiteDimensional :
    ∃ (_ : ValuativeRel L) (_ : ValuativeExtension K L)
    (_ : UniformSpace L), IsNonarchLocalField L := by
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField (L := K)
  letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
  haveI : IsUltrametricDist L := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_nnnorm
    isNonarchimedean_spectralNorm
  let v := NormedField.valuation (K := L)
  haveI : ValuativeExtension K L := by
    refine ⟨fun x y ↦ ?_⟩
    rw [Valuation.Compatible.rel_iff_le (v := v),
    Valuation.Compatible.rel_iff_le (v := ValuativeRel.valuation K)]
    change spectralNorm K L _ ≤ spectralNorm K L _ ↔ _
    rw [spectralNorm_extends, spectralNorm_extends]
    change Valued.norm _ ≤ Valued.norm _ ↔ _
    rw [Valued.norm_def, Valued.norm_def, NNReal.coe_le_coe,
      (Valuation.RankOne.strictMono Valued.v).le_iff_le]
    rfl
  haveI := locallyCompactSpace_of_complete_of_finiteDimensional K L
  refine ⟨inferInstance, inferInstance, inferInstance, .mk⟩


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

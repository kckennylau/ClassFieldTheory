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
  -- IsTopologicalDivisionRing K, -- TODO: remove IsTopologicalDivisionRing
  -- ValuativeRel.IsRankLeOne K -- TODO: in future mathlib
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

variable (p : ℕ) [Fact p.Prime]

instance : LocallyCompactSpace ℚ_[p] := inferInstance

instance : IsNonarchLocalField ℚ_[p] where
  mem_nhds_iff := sorry

variable (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsNonarchLocalField K]
  (L : Type v) [Field L] [ValuativeRel L] [UniformSpace L] [IsNonarchLocalField L]

instance : (Valued.v : Valuation K (ValueGroupWithZero K)).IsNontrivial :=
  ValuativeRel.isNontrivial_iff_isNontrivial.mp inferInstance

-- waiting andrew
instance : IsTopologicalDivisionRing K := sorry

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

-- class HasExtension [Algebra K L] : Prop extends
--   Valuation.HasExtension (Valued.v (R := K)) (Valued.v (R := L))
class HasExtension [Algebra K L] : Prop extends ValuativeExtension K L

variable [Algebra K L] [HasExtension K L]

instance : FiniteDimensional K L :=
  sorry
  -- FiniteDimensional.of_locallyCompactSpace K (E := L)

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

instance : ContinuousSMul K L :=
  sorry
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

open scoped Valued in
#check (inferInstance : NormedField K)
#check (inferInstance : Valuation.RankOne (Valued.v (R := K)))

section

variable {R : Type u} [CommRing R] [ValuativeRel R] {Γ : Type v}
  [LinearOrderedCommMonoidWithZero Γ] (v : Valuation R Γ) [Valuation.Compatible v] (x : R)

lemma _root_.Valuation.Compatible.rel_one_iff :
    x ≤ᵥ 1 ↔ v x ≤ 1 := by
  rw [← map_one v, ← Valuation.Compatible.rel_iff_le]

lemma _root_.Valuation.Compatible.rel_zero_iff :
    x ≤ᵥ 0 ↔ v x ≤ 0 := by
  rw [← map_zero v, ← Valuation.Compatible.rel_iff_le]

lemma _root_.Valuation.Compatible.one_rel_iff :
    1 ≤ᵥ x ↔ 1 ≤ v x := by
  rw [← map_one v, ← Valuation.Compatible.rel_iff_le]

end

@[ext] theorem _root_.ValuativeRel.ext {R : Type u} [CommRing R] {v v' : ValuativeRel R}
    (h : ∀ a b, v.rel a b ↔ v'.rel a b) : v = v' := by
  cases v; cases v'; congr; ext; apply h

theorem _root_.ValuativeRel.rel_iff_one_rel_div {F : Type u} [Field F] [ValuativeRel F]
    {x : F} (y : F) (hx : x ≠ 0) : x ≤ᵥ y ↔ 1 ≤ᵥ y / x :=
  ⟨fun h ↦ by simpa [hx, inv_mul_eq_div] using rel_mul_left x⁻¹ h,
  fun h ↦ by simpa [hx] using rel_mul_right x h⟩

theorem _root_.ValuativeRel.rel_iff_div_rel_one {F : Type u} [Field F] [ValuativeRel F]
    (x : F) {y : F} (hy : y ≠ 0) : x ≤ᵥ y ↔ x / y ≤ᵥ 1 := by
  rw [Valuation.Compatible.rel_iff_le (v := ValuativeRel.valuation F),
    Valuation.Compatible.rel_iff_le (v := ValuativeRel.valuation F),
    map_div₀, map_one, div_le_one₀ (bot_lt_iff_ne_bot.2 ((map_ne_zero _).2 hy))]

theorem _root_.ValuativeRel.rel_zero_iff {F : Type u} [Field F] [ValuativeRel F] (x : F) :
    x ≤ᵥ 0 ↔ x = 0 := by
  rw [Valuation.Compatible.rel_iff_le (v := valuation F), map_zero, le_zero_iff, map_eq_zero]

/-- Two valuative relations on a field are equal iff their rings of integers are equal. -/
@[ext high] theorem _root_.ValuativeRel.ext_field {F : Type u} [Field F] {v v' : ValuativeRel F}
    (h : ∀ x, v.rel x 1 ↔ v'.rel x 1) : v = v' := by
  ext x y
  by_cases hy : y = 0
  · simp_rw [hy, rel_zero_iff]
  · rw [rel_iff_div_rel_one _ hy, @rel_iff_div_rel_one _ _ v x y hy, h]

@[simp] theorem _root_.NormedField.valuation_le_valuation_iff {K : Type u} [NormedField K]
    [IsUltrametricDist K] (x y : K) :
    letI := ValuativeRel.ofValuation (NormedField.valuation (K := K))
    valuation K x ≤ valuation K y ↔ ‖x‖ ≤ ‖y‖ := by
  letI := ValuativeRel.ofValuation (NormedField.valuation (K := K))
  haveI := Valuation.Compatible.ofValuation (S := K) NormedField.valuation
  simp_rw [← Valuation.Compatible.rel_iff_le,
    Valuation.Compatible.rel_iff_le (v := NormedField.valuation),
    NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm]

@[simp] theorem _root_.NormedField.valuation_lt_valuation_iff {K : Type u} [NormedField K]
    [IsUltrametricDist K] (x y : K) :
    letI := ValuativeRel.ofValuation (NormedField.valuation (K := K))
    valuation K x < valuation K y ↔ ‖x‖ < ‖y‖ := by
  letI := ValuativeRel.ofValuation (NormedField.valuation (K := K))
  simp_rw [lt_iff_le_not_ge, NormedField.valuation_le_valuation_iff]

@[simp] theorem _root_.NormedField.ball_norm_eq {K : Type u} [NormedField K] [IsUltrametricDist K]
    (x : K) :
    letI := ValuativeRel.ofValuation (NormedField.valuation (K := K))
    Metric.ball 0 ‖x‖ = { y | valuation K y < valuation K x } := by
  letI := ValuativeRel.ofValuation (NormedField.valuation (K := K))
  ext y
  rw [mem_ball_zero_iff, Set.mem_setOf_eq, NormedField.valuation_lt_valuation_iff]

theorem _root_.ValuativeRel.posSubmonoid.ne_zero {R : Type u} [CommRing R] [ValuativeRel R]
    (x : posSubmonoid R) : x.val ≠ 0 :=
  mt (· ▸ rel_rfl) x.2

theorem _root_.ValuativeRel.valuation_surjective₀ {F : Type u} [Field F] [ValuativeRel F]
    (γ : ValueGroupWithZero F) : ∃ x : F, valuation F x = γ :=
  let ⟨x, y, hxy⟩ := valuation_surjective γ
  ⟨x / y.val, by rw [map_div₀, hxy]⟩

theorem _root_.ValuativeRel.units_map_valuation_surjective {F : Type u} [Field F] [ValuativeRel F]
    (γ : (ValueGroupWithZero F)ˣ) : ∃ x : Fˣ, Units.map (valuation F) x = γ :=
  let ⟨x, hx⟩ := valuation_surjective₀ γ.val
  ⟨Units.mk0 x (mt (by rw [← hx, ·, map_zero]) γ.ne_zero),
    Units.ext <| by simpa using hx⟩

theorem _root_.NormedField.valuativeTopology (K : Type u) [NormedField K] [IsUltrametricDist K] :
    @ValuativeTopology K _ (ValuativeRel.ofValuation (NormedField.valuation (K := K))) _ := by
  letI := ValuativeRel.ofValuation (NormedField.valuation (K := K))
  refine { mem_nhds_iff s := ?_ }
  by_cases nontrivial : ∃ x : K, x ≠ 0 ∧ ‖x‖ < 1
  · obtain ⟨x, hx0, hx1⟩ := nontrivial
    refine ⟨fun hs ↦ ?_, fun ⟨γ, hγ⟩ ↦ ?_⟩
    · simp_rw [(Metric.nhds_basis_ball_pow (norm_pos_iff.2 hx0) hx1).mem_iff, ← norm_pow,
        NormedField.ball_norm_eq] at hs
      obtain ⟨n, -, hns⟩ := hs
      let u : (ValueGroupWithZero K)ˣ :=
        IsUnit.unit (a := valuation K x) (isUnit_iff_ne_zero.2 (by simp [hx0]))
      exact ⟨u ^ n, by simpa [u] using hns⟩
    · rw [Metric.mem_nhds_iff]
      obtain ⟨z, rfl⟩ := ValuativeRel.units_map_valuation_surjective γ
      refine ⟨‖z.val‖, norm_pos_iff.2 z.ne_zero, by simpa using hγ⟩
  haveI := DiscreteTopology.of_forall_le_norm (E := K) one_pos (by simpa using nontrivial)
  rw [nhds_discrete, Filter.mem_pure]
  refine ⟨fun h0s ↦ ⟨1, ?_⟩, fun ⟨γ, hγ⟩ ↦ ?_⟩
  · simp_rw [Units.val_one, ← map_one (valuation K), NormedField.valuation_lt_valuation_iff,
      norm_one]
    simp_rw [not_exists, not_and, not_imp_not] at nontrivial
    exact fun x hx ↦ by rwa [nontrivial x hx]
  · obtain ⟨z, rfl⟩ := ValuativeRel.units_map_valuation_surjective γ
    exact hγ (by simp)

-- open scoped Valued in
theorem locallyCompactSpace_of_complete_of_finiteDimensional (K : Type u) (L : Type v)
    [NontriviallyNormedField K] [CompleteSpace K] [LocallyCompactSpace K]
    [AddCommGroup L] [TopologicalSpace L] [IsTopologicalAddGroup L] [T2Space L]
    [Module K L] [ContinuousSMul K L] [FiniteDimensional K L] :
    LocallyCompactSpace L := by
  obtain ⟨s, ⟨b⟩⟩ := Basis.exists_basis K L
  haveI := FiniteDimensional.fintypeBasisIndex b
  exact b.equivFun.toContinuousLinearEquiv.toHomeomorph.isOpenEmbedding.locallyCompactSpace

noncomputable
def spectralNorm.nontriviallyNormedField (K : Type u) [NontriviallyNormedField K] (L : Type v)
    [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [hu : IsUltrametricDist K] [CompleteSpace K] :
    NontriviallyNormedField L where
  __ := spectralNorm.normedField K L
  non_trivial :=
    let ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
    ⟨algebraMap K L x, hx.trans_eq <| (spectralNorm_extends _).symm⟩

theorem _root_.ValuativeRel.isNontrivial (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] :
    letI := ValuativeRel.ofValuation (NormedField.valuation (K := K))
    ValuativeRel.IsNontrivial K := by
  letI := ofValuation (NormedField.valuation (K := K))
  haveI := Valuation.Compatible.ofValuation (S := K) NormedField.valuation
  obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
  refine ⟨⟨valuation K x, ?_, ?_⟩⟩
  · rw [Valuation.ne_zero_iff]
    exact norm_pos_iff.1 (one_pos.trans hx)
  · have := NormedField.valuation_lt_valuation_iff 1 x
    simp only [map_one, norm_one] at this
    exact ne_of_gt <| this.2 hx

open scoped Valued in
include K in
theorem isNonarchLocalField_of_finiteDimensional :
    ∃ (_ : ValuativeRel L) (_ : ValuativeExtension K L)
    (_ : UniformSpace L), IsNonarchLocalField L := by
  letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
  haveI : IsUltrametricDist L := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_nnnorm
    isNonarchimedean_spectralNorm
  let v := NormedField.valuation (K := L)
  letI := ValuativeRel.ofValuation v
  haveI := Valuation.Compatible.ofValuation v
  haveI := NormedField.valuativeTopology L
  haveI := locallyCompactSpace_of_complete_of_finiteDimensional K L
  haveI := ValuativeRel.isNontrivial L
  refine ⟨inferInstance, ⟨fun k₁ k₂ ↦ ?_⟩, inferInstance, .mk⟩
  rw [Valuation.Compatible.rel_iff_le (v := v),
    Valuation.Compatible.rel_iff_le (v := ValuativeRel.valuation K)]
  change spectralNorm K L _ ≤ spectralNorm K L _ ↔ _
  rw [spectralNorm_extends, spectralNorm_extends]
  change Valued.norm _ ≤ Valued.norm _ ↔ _
  rw [Valued.norm_def, Valued.norm_def, NNReal.coe_le_coe,
    (Valuation.RankOne.strictMono Valued.v).le_iff_le]
  rfl

end make_finite_extension

end IsNonarchLocalField

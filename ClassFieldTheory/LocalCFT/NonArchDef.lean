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
  ValuativeRel.IsNontrivial K,
  IsTopologicalDivisionRing K, -- TODO: remove IsTopologicalDivisionRing
  ValuativeRel.IsRankLeOne K -- TODO: in future mathlib
  -- CompleteSpace K,
  -- ValuativeRel.IsDiscrete K


open ValuativeRel

namespace IsNonarchLocalField

variable (p : ℕ) [Fact p.Prime]

instance : LocallyCompactSpace ℚ_[p] := inferInstance

instance : IsNonarchLocalField ℚ_[p] where
  mem_nhds_iff := sorry
  nonempty := sorry

variable (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsNonarchLocalField K]
  (L : Type u) [Field L] [ValuativeRel L] [UniformSpace L] [IsNonarchLocalField L]

instance : (Valued.v : Valuation K (ValueGroupWithZero K)).IsNontrivial :=
  ValuativeRel.isNontrivial_iff_isNontrivial.mp inferInstance

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

theorem compact_OK : IsCompact (𝒪[K] : Set K) :=
  sorry

theorem open_OK : IsOpen (𝒪[K] : Set K) :=
  sorry

def compactOpenOK : TopologicalSpace.CompactOpens K where
  carrier := 𝒪[K]
  isCompact' := compact_OK K
  isOpen' := open_OK K

-- TODO: add Haar measure (or check that it works with `example`)

-- class HasExtension [Algebra K L] : Prop extends
--   Valuation.HasExtension (Valued.v (R := K)) (Valued.v (R := L))
class HasExtension [Algebra K L] : Prop extends ValuativeExtension K L

variable [Algebra K L] [HasExtension K L]

instance : FiniteDimensional K L :=
  sorry

open Valuation.HasExtension in
instance : Algebra 𝒪[K] 𝒪[L] where
  smul r a := ⟨r • a,
    Algebra.smul_def r (a : L) ▸ mul_mem sorry a.2⟩
  algebraMap := (algebraMap K L).restrict 𝒪[K] 𝒪[L]
    sorry
    -- (by simp [Valuation.mem_integer_iff, val_map_le_one_iff vR vA])
  commutes' _ _ := Subtype.ext (Algebra.commutes _ _)
  smul_def' _ _ := Subtype.ext (Algebra.smul_def _ _)
  -- Valuation.HasExtension.instAlgebraInteger (R := K) (A := L) (vR := Valued.v) (vA := Valued.v)

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

instance {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
  IsLocalization.AtPrime R (IsLocalRing.maximalIdeal R) := by sorry

theorem unramified_def : IsUnramified K L ↔ e K L = 1 :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

theorem unramified_maximal_ideal_eq : IsUnramified K L
  ↔ Ideal.map (algebraMap 𝒪[K] 𝒪[L]) 𝓂[K] = 𝓂[L] := by
  rw [unramified_def]
  simp [e]
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_one_iff (IsDiscreteValuationRing.not_a_field ↥𝒪[L])]
  sorry
  -- still can't unify this extra localization
  sorry

-- Since residue field is finite, separable should be free
theorem residue_separable : Algebra.IsSeparable 𝓀[K] 𝓀[L] := sorry
-- looks like it can make type checker happy
theorem residue_separable' : Algebra.IsSeparable 𝓂[K].ResidueField 𝓂[L].ResidueField := sorry

theorem unramified_iff_unramified : IsUnramified K L ↔ Algebra.Unramified 𝒪[K] 𝒪[L] := by calc
  _ ↔ Algebra.IsUnramifiedAt 𝒪[K] 𝓂[L] := by
    rw [Algebra.isUnramifiedAt_iff_map_eq (p := 𝓂[K]), unramified_maximal_ideal_eq]
    constructor
    intro h
    constructor
    exact (residue_separable' K L)
    sorry
    -- need to show Localize.AtPrime 𝓂[K] = 𝒪[K]
    intro h
    -- exact h.2
    sorry
    -- same as above
  _ ↔ Algebra.Unramified 𝒪[K] 𝒪[L] := by
    constructor
    intro h
    have fu : Algebra.FormallyUnramified 𝒪[K] 𝒪[L] := by
      rw [(Iff.symm (Algebra.unramifiedLocus_eq_univ_iff (A := 𝒪[L]) (R := 𝒪[K])))]
      sorry
      -- Now use the lemma `iff_pid_with_one_nonzero_prime` to describe the specturm of DVR
    exact { formallyUnramified := fu, finiteType := inferInstance }
    intro h
    have x := (Iff.symm (Algebra.unramifiedLocus_eq_univ_iff (A := 𝒪[L]) (R := 𝒪[K]))).mp h.formallyUnramified
    simp [Algebra.unramifiedLocus] at x
    -- same as above
    sorry

section make_finite_extension

/- # Constructing a finite extension from a minimal set of assumptions. -/

variable (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]

include K in
theorem unique_hasExtension : ∃! v : ValuativeRel L, ValuativeExtension K L :=
  sorry -- by María Inés

-- def of_finite_extension [ValuativeRel L] [ValuativeExtension K L] :
--     IsNonarchLocalField L :=
--   sorry
/-
failed to synthesize
  UniformSpace L
-/

end make_finite_extension

end IsNonarchLocalField

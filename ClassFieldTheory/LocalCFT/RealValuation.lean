import ClassFieldTheory.Mathlib.RingTheory.Valuation.ValuativeRel
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.RingTheory.Valuation.Discrete.Basic

open ValuativeRel

theorem Valuation.IsRankOneDiscrete.ofIsDiscreteValuationRing
    (K : Type*) [Field K] [ValuativeRel K] [IsDiscreteValuationRing 𝒪[K]] :
    (valuation K).IsRankOneDiscrete where
  exists_generator_lt_one' := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    have : valuation K ϖ ≠ 0 := mt (by simpa using ·) hϖ.ne_zero
    let ϖ' := Units.mk0 (valuation K ϖ) this
    refine ⟨ϖ', ?_, ?_⟩
    · refine le_antisymm (Subgroup.zpowers_le.2 ?_) ((Subgroup.closure_le _).2 ?_)
      · refine MonoidWithZeroHom.mem_valueGroup _ ⟨ϖ, rfl⟩
      · rintro γ -
        have {γ : (ValueGroupWithZero K)ˣ} (hγ : γ ≤ 1) : γ ∈ Subgroup.zpowers ϖ' := by
          obtain ⟨x, rfl⟩ := unitsMap_valuation_surjective γ
          let x' : 𝒪[K] := ⟨x, hγ⟩
          have hx' : x' ≠ 0 := fun hx' ↦ x.ne_zero congr(($hx').val)
          obtain ⟨n, u, hnu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx' hϖ
          replace hnu : x = (u * ϖ ^ n : K) := by simpa using congr(($hnu).val)
          refine ⟨n, Units.ext ?_⟩
          have hu : valuation K u = 1 :=
            Valuation.Integers.one_of_isUnit (Valuation.integer.integers _) u.isUnit
          simp [hnu, hu, ϖ']
        obtain hγ | hγ := le_total γ 1
        · exact this hγ
        · exact (Subgroup.inv_mem_iff _).1 (this <| inv_le_one_of_one_le hγ)
    · refine (Valuation.Integer.not_isUnit_iff_valuation_lt_one (x := ϖ)).1 hϖ.not_isUnit

@[ext] structure Real.Small : Type where
  val : ℝ
  pos : 0 < val
  lt_one : val < 1



def discreteValuation :

#min_imports

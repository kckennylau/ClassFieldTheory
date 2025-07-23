import Mathlib

/-!
# Definition of Non-Archimedean Local Fields

We define non-archimedean local fields as a class `IsNonArchLF`.

-/

universe u v

class IsNonArchLF (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] : Prop extends
  IsTopologicalDivisionRing K,
  IsUniformAddGroup K,
  LocallyCompactSpace K,
  CompleteSpace K,
  ValuativeTopology K,
  ValuativeRel.IsNontrivial K,
  ValuativeRel.IsRankLeOne K,
  ValuativeRel.IsDiscrete K

open ValuativeRel

namespace IsNonArchLF

variable (p : ℕ) [Fact p.Prime]

instance : LocallyCompactSpace ℚ_[p] := inferInstance

instance : IsNonArchLF ℚ_[p] where
  mem_nhds_iff := sorry
  nonempty := sorry
  has_maximal_element := sorry

variable (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsNonArchLF K]
  (L : Type v) [Field L] [ValuativeRel L] [UniformSpace L] [IsNonArchLF L]

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

variable {K} in
def IsUniformiser (x : 𝒪[K]) : Prop :=
  Irreducible x

/-- An arbitrary choice of a uniformiser in a local field. -/
noncomputable def ϖ : 𝒪[K] :=
  (IsDiscreteValuationRing.exists_irreducible _).choose

@[simp] lemma isUniformiser_ϖ : IsUniformiser (ϖ K) :=
  (IsDiscreteValuationRing.exists_irreducible _).choose_spec

lemma ϖ_ne_zero : ϖ K ≠ 0 :=
  (IsDiscreteValuationRing.exists_irreducible _).choose_spec.ne_zero

lemma associated_ϖ_iff_isUniformiser (x : 𝒪[K]) :
    Associated x (ϖ K) ↔ IsUniformiser x :=
  ⟨fun h ↦ h.symm.irreducible (isUniformiser_ϖ K),
  fun h ↦ IsDiscreteValuationRing.associated_of_irreducible _ h (isUniformiser_ϖ K)⟩

theorem compact_OK : IsCompact (𝒪[K] : Set K) :=
  sorry

theorem open_OK : IsOpen (𝒪[K] : Set K) :=
  sorry

def compactOpenOK : TopologicalSpace.CompactOpens K where
  carrier := 𝒪[K]
  isCompact' := compact_OK K
  isOpen' := open_OK K

instance : Finite 𝓀[K] :=
  sorry

instance : (ringChar (𝓀[K])).Prime :=
  CharP.char_is_prime 𝓀[K] _

class HasExtension [Algebra K L] : Prop extends
  Valuation.HasExtension (Valued.v (R := K)) (Valued.v (R := L))

variable [Algebra K L] [HasExtension K L]

instance : FiniteDimensional K L :=
  sorry

instance : Algebra 𝒪[K] 𝒪[L] :=
  Valuation.HasExtension.instAlgebraInteger (R := K) (A := L) (vR := Valued.v) (vA := Valued.v)

instance : ContinuousSMul K L :=
  sorry

instance : Module.Finite 𝒪[K] 𝒪[L] :=
  sorry

@[fun_prop] lemma continuous_algebraMap : Continuous (algebraMap K L) :=
  _root_.continuous_algebraMap K L

instance : IsScalarTower 𝒪[K] K L := inferInstance

instance : IsScalarTower 𝒪[K] 𝒪[L] L := inferInstance

noncomputable def e : ℕ :=
  multiplicity (ϖ L) (algebraMap 𝒪[K] 𝒪[L] (ϖ K))

theorem e_spec : Associated (ϖ L ^ e K L) (algebraMap 𝒪[K] 𝒪[L] (ϖ K)) :=
  sorry

noncomputable def f : ℕ :=
  Module.finrank 𝓀[K] 𝓀[L]

theorem f_spec : Nat.card 𝓀[K] ^ f K L = Nat.card 𝓀[K] :=
  sorry

theorem e_pos : 0 < e K L :=
  sorry

theorem f_pos : 0 < f K L :=
  Module.finrank_pos

theorem e_mul_f_eq_n : e K L * f K L = Module.finrank K L :=
  sorry

class IsUnramified : Prop where
  e_eq_one : e K L = 1

theorem unramified_def : IsUnramified K L ↔ e K L = 1 :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

theorem unramified_iff_unramified : IsUnramified K L ↔ Algebra.Unramified 𝒪[K] 𝒪[L] :=
  sorry

section make_finite_extension

/- # Constructing a finite extension from a minimal set of assumptions. -/

variable (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]

include K in
theorem unique_hasExtension : ∃! v : ValuativeRel L, sorry := sorry

noncomputable def valuativeRelOfFiniteDimensional : ValuativeRel L :=
  (unique_hasExtension K L).choose

def of_finite_extension : @IsNonArchLF L _ (valuativeRelOfFiniteDimensional K L) sorry :=
  sorry

end make_finite_extension

end IsNonArchLF

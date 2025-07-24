import Mathlib
import ClassFieldTheory.Mathlib.RingTheory.Valuation.ValuativeRel

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
  (L : Type v) [Field L] [ValuativeRel L] [UniformSpace L] [IsNonarchLocalField L]

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

#check FiniteDimensional K L

#synth Module K L

-- TODO: MOVE
theorem _root_.Irreducible.ne_zero'
    {K S : Type*} [MonoidWithZero K] [SetLike S K] [SubmonoidClass S K]
    {s : S} {x : s} (h : Irreducible x) : (x : K) ≠ 0 := by
  obtain ⟨x, hx⟩ := x
  rintro rfl
  exact h.1 ((or_self _).mp (h.2 (a := ⟨0, hx⟩) (b := ⟨0, hx⟩) (by ext; simp)))

-- TODO: MOVE
open Filter Set in
theorem _root_.Filter.mem_iInf'' {α} {ι : Sort _} {s : ι → Filter α} {U : Set α} :
    (U ∈ ⨅ i, s i) ↔
      ∃ I : Set ι, I.Finite ∧ ∃ V : I → Set α, (∀ (i : I), V i ∈ s i) ∧ U = ⋂ i, V i := by
  constructor
  · rw [iInf_eq_generate, mem_generate_iff]
    rintro ⟨t, tsub, tfin, tinter⟩
    rcases eq_finite_iUnion_of_finite_subset_iUnion tfin tsub with ⟨I, Ifin, σ, σfin, σsub, rfl⟩
    rw [sInter_iUnion] at tinter
    set V := fun i => U ∪ ⋂₀ σ i with hV
    have V_in : ∀ (i : I), V i ∈ s i := by
      rintro i
      have : ⋂₀ σ i ∈ s i := by
        rw [sInter_mem (σfin _)]
        apply σsub
      exact mem_of_superset this subset_union_right
    refine ⟨I, Ifin, V, V_in, ?_⟩
    rwa [hV, ← union_iInter, union_eq_self_of_subset_right]
  · rintro ⟨I, Ifin, V, V_in, rfl⟩
    exact mem_iInf_of_iInter Ifin V_in Subset.rfl

open Set
theorem _root_.Filter.mem_iInf''' {α} {ι : Prop} [Decidable ι] {s : ι → Filter α} {U : Set α} :
    (U ∈ ⨅ i, s i) ↔ if i : ι then U ∈ s i else U = .univ := by
  split_ifs with h <;> simp [h]

open scoped Valued in
#synth NontriviallyNormedField K

#check NormedField.induced
#check IsDiscreteValuationRing.exists_irreducible

omit [UniformSpace K] [IsNonarchLocalField K] [UniformSpace L] [IsNonarchLocalField L] [HasExtension K L] in
@[simp]
theorem ValuationExtension.le_iff_le [ValuativeExtension K L] {a b : K} : valuation L (algebraMap K L a) ≤ valuation L (algebraMap K L b) ↔ valuation K a ≤ valuation K b := by
  rw [← Valuation.Compatible.rel_iff_le, ← Valuation.Compatible.rel_iff_le, ValuativeExtension.rel_iff_rel]

omit [UniformSpace K] [IsNonarchLocalField K] [UniformSpace L] [IsNonarchLocalField L] [HasExtension K L] in
@[simp]
theorem ValuationExtension.lt_iff_lt [ValuativeExtension K L] {a b : K} : valuation L (algebraMap K L a) < valuation L (algebraMap K L b) ↔ valuation K a < valuation K b := by
  simp only [lt_iff_le_not_ge, ValuationExtension.le_iff_le]

omit [UniformSpace K] [IsNonarchLocalField K] in
lemma valuation_of_field_surjective {K : Type _} [Field K] [ValuativeRel K] : Function.Surjective (valuation K) := by
  intro β
  obtain ⟨a, b, _⟩ := valuation_surjective β (R := K)
  use (a / b)
  rwa [Valuation.map_div (valuation K) a ↑b]

open scoped Valued in
noncomputable instance (priority := low) : NontriviallyNormedField K := inferInstance

open ValuativeExtension in
instance : FiniteDimensional K L := by
  letI : NormedField K :=
  { toUniformSpace := ‹UniformSpace K›,
    __ := NormedField.induced K L (algebraMap K L) (algebraMap K L).injective,
    uniformity_dist := ?_
  }
  letI : NontriviallyNormedField K := by
    apply NontriviallyNormedField.ofNormNeOne
    let ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    use ϖ
    constructor
    · exact Irreducible.ne_zero' hϖ
    · apply ne_of_lt
      change ‖(algebraMap K L ϖ)‖ < 1
      rw [Valued.toNormedField.norm_lt_one_iff]
      rw [← Valuation.map_one (valuation L)]
      rw [← map_one (algebraMap K L)]
      erw [ValuationExtension.lt_iff_lt]
      rw [Valuation.map_one (valuation K)]
      exact Valuation.integer.v_irreducible_lt_one hϖ
  letI : NormedSpace K L := {
    norm_smul_le a b := by
      rw [Algebra.smul_def a b]
      rw [norm_mul ((algebraMap K L) a) b]
      rfl
  }
  exact FiniteDimensional.of_locallyCompactSpace (𝕜 := K) (E := L)

  -- Showing `uniformity_dist` for `K`
  rw [uniformity_eq_comap_nhds_zero]
  refine uniformity_dist_of_mem_uniformity 0 dist ?_
  intro S
  simp only [Filter.mem_comap, ValuativeTopology.mem_nhds_iff, gt_iff_lt]
  let v : Valuation L (ValueGroupWithZero L) := Valued.v

  constructor
  · rintro ⟨t, ⟨γ, hγ⟩, hS⟩
    use (Valuation.RankOne.hom v).comp (mapValueGroupWithZero K L) γ.val,
      NNReal.coe_pos.2 (pos_of_ne_zero ((map_ne_zero _).mpr γ.ne_zero))
    intro a b hab
    apply hS
    apply hγ
    apply ((Valuation.RankOne.strictMono v).comp mapValueGroupWithZero_strictMono).lt_iff_lt.mp
    apply hab.trans_eq'
    simp only [Function.comp_apply, mapValueGroupWithZero_valuation, map_sub, NNReal.val_eq_coe]
    exact dist_comm b a

  · intro ⟨ε, hε, hS⟩
    let ⟨x, hx_pos, hx_lt_one⟩ := (isNontrivial_field_iff_exists_valuation_between_zero_one (K := K)).mp inferInstance
    let γ : (ValueGroupWithZero K)ˣ := by
      refine (IsUnit.unit (a := valuation K x) ?_)
      rw [isUnit_iff_ne_zero]
      grind
    set δ : NNReal := (Valuation.RankOne.hom v (mapValueGroupWithZero K L ↑(valuation K x)))

    have : 0 < δ := by
      have : (Valuation.RankOne.hom v) (mapValueGroupWithZero K L (valuation K 0)) = 0 := by
        rw [Valuation.RankOne.hom_eq_zero_iff v, MonoidWithZeroHom.map_eq_zero_iff, Valuation.zero_iff]
      rw [← this]
      apply Valuation.RankOne.strictMono
      simp only [mapValueGroupWithZero_valuation]
      rwa [ValuationExtension.lt_iff_lt K L, Valuation.map_zero (valuation K)]

    have : δ < 1 := by
      have : (Valuation.RankOne.hom v) ((mapValueGroupWithZero K L) (valuation K 1)) = 1 := by
        rw [mapValueGroupWithZero_valuation]
        rw [RingHom.map_one]
        rw [Valuation.map_one]
        rw [MonoidWithZeroHom.map_one]
      rw [← this]
      apply Valuation.RankOne.strictMono
      simp only [mapValueGroupWithZero_valuation]
      rwa [ValuationExtension.lt_iff_lt K L, Valuation.map_one (valuation K)]

    rw [← NNReal.coe_zero, ← Real.lt_toNNReal_iff_coe_lt] at hε
    obtain ⟨n, hx_n_pow_le_ε⟩ := NNReal.exists_pow_lt_of_lt_one hε ‹δ < 1›
    refine ⟨_, ⟨γ ^ n, subset_rfl⟩, ?_⟩
    intro ⟨a, b⟩ hab
    apply hS
    apply ((Valuation.RankOne.strictMono v).comp mapValueGroupWithZero_strictMono).lt_iff_lt.2 at hab
    apply NNReal.coe_lt_coe.2 at hab
    simp only [Function.comp_apply, mapValueGroupWithZero_valuation, map_sub] at hab
    rw [dist_comm]
    apply hab.trans_le
    rw [Units.val_pow_eq_pow_val γ n]
    rw [map_pow, map_pow]
    change ↑(δ ^ n) ≤ ε
    rw [← Real.le_toNNReal_iff_coe_le']
    grw [hx_n_pow_le_ε]
    exact pow_pos ‹_› _

#check FiniteDimensional.of_locallyCompactSpace

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

theorem f_spec : Nat.card 𝓀[K] ^ f K L = Nat.card 𝓀[K] :=
  sorry

theorem e_pos : 0 < e K L :=
  sorry

theorem f_pos : 0 < f K L :=
  sorry

theorem e_mul_f_eq_n : e K L * f K L = Module.finrank K L :=
  sorry

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

import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.Valuation.ValuativeRel
import Mathlib.Topology.Algebra.Valued.NormedValued

universe u u₀ v v'

variable {R : Type u} [CommRing R] [ValuativeRel R]
  {F : Type u₀} [Field F] [ValuativeRel F]
  {Γ : Type v} [LinearOrderedCommMonoidWithZero Γ]
  {Γ' : Type v'} [LinearOrderedCommMonoidWithZero Γ']
  (v : Valuation R Γ) [Valuation.Compatible v] (v₀ : Valuation F Γ) [Valuation.Compatible v₀]
  (x y : R) (x₀ y₀ : F)


namespace Valuation

/-- The "valuation ball" is a valuation version of the open balls centered at 0 in a metric
topology. This is used in `ValuativeTopology` for the statement that a valuative relation is
compatible with a given topology -/
def ball (v : Valuation R Γ) (γ : Γ) : Set R :=
  { x | v x < γ }

omit [ValuativeRel R] in
@[simp] lemma mem_ball_iff (x : R) (γ : Γ) :
    x ∈ v.ball γ ↔ v x < γ := by
  rw [ball, Set.mem_setOf_eq]

namespace Compatible

lemma rel_one_iff :
    x ≤ᵥ 1 ↔ v x ≤ 1 := by
  rw [← map_one v, ← Valuation.Compatible.rel_iff_le]

lemma rel_zero_iff :
    x ≤ᵥ 0 ↔ v x ≤ 0 := by
  rw [← map_zero v, ← Valuation.Compatible.rel_iff_le]

lemma one_rel_iff :
    1 ≤ᵥ x ↔ 1 ≤ v x := by
  rw [← map_one v, ← Valuation.Compatible.rel_iff_le]

section compare

-- `v` is placed first here because that's the valuation one would typically want to rewrite into.
variable (v' : Valuation R Γ') [Valuation.Compatible v']

lemma lt_iff_lt (x y : R) : v' x < v' y ↔ v x < v y := by
  simp_rw [lt_iff_le_not_ge, ← Valuation.Compatible.rel_iff_le]

lemma ball_eq_ball (x : R) :
    v'.ball (v' x) = v.ball (v x) := by
  ext y; simp_rw [mem_ball_iff, Valuation.Compatible.lt_iff_lt v v']

lemma lt_one_iff_lt_one (x : R) : v' x < 1 ↔ v x < 1 := by
  rw [← v.map_one, ← v'.map_one, lt_iff_lt v v']

lemma one_lt_iff_one_lt (x : R) : 1 < v' x ↔ 1 < v x := by
  rw [← v.map_one, ← v'.map_one, lt_iff_lt v v']

end compare

end Valuation.Compatible


namespace ValuativeRel

@[ext] theorem ext {R : Type u} [CommRing R] {v v' : ValuativeRel R}
    (h : ∀ a b, v.rel a b ↔ v'.rel a b) : v = v' := by
  cases v; cases v'; congr; ext; apply h

theorem rel_iff_div_rel_one {F : Type u} [Field F] [ValuativeRel F]
    (x : F) {y : F} (hy : y ≠ 0) : x ≤ᵥ y ↔ x / y ≤ᵥ 1 := by
  rw [Valuation.Compatible.rel_iff_le (v := ValuativeRel.valuation F),
    Valuation.Compatible.rel_iff_le (v := ValuativeRel.valuation F),
    map_div₀, map_one, div_le_one₀ (bot_lt_iff_ne_bot.2 ((map_ne_zero _).2 hy))]

theorem rel_zero_iff {F : Type u} [Field F] [ValuativeRel F] (x : F) :
    x ≤ᵥ 0 ↔ x = 0 := by
  rw [Valuation.Compatible.rel_iff_le (v := valuation F), map_zero, le_zero_iff, map_eq_zero]

/-- Two valuative relations on a field are equal iff their rings of integers are equal. -/
@[ext high] theorem ext_field {F : Type u} [Field F] {v v' : ValuativeRel F}
    (h : ∀ x, v.rel x 1 ↔ v'.rel x 1) : v = v' := by
  ext x y
  by_cases hy : y = 0
  · simp_rw [hy, rel_zero_iff]
  · rw [rel_iff_div_rel_one _ hy, @rel_iff_div_rel_one _ _ v x y hy, h]

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


namespace ValuativeTopology

open Topology ValuativeRel

theorem mk_replace {R : Type u} [CommRing R] [ValuativeRel R] [TopologicalSpace R]
    (h : ∀ s : Set R, s ∈ 𝓝 (0 : R) ↔ ∃ γ : (ValueGroupWithZero R)ˣ, (valuation R).ball γ ⊆ s) :
    ValuativeTopology R where
  mem_nhds_iff := h

theorem mk' {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {Γ₀ : Type v} [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation F Γ₀) [v.Compatible]
    (h : ∀ s : Set F, s ∈ 𝓝 (0 : F) ↔ ∃ x : F, x ≠ 0 ∧ v.ball (v x) ⊆ s) :
    ValuativeTopology F where
  mem_nhds_iff s := by
    rw [h s, Function.Surjective.exists (units_map_valuation_surjective)]
    simp_rw [Valuation.Compatible.ball_eq_ball (valuation F)]
    exact ⟨fun ⟨x, hx0, hx⟩ ↦ ⟨Units.mk0 x hx0, hx⟩, fun ⟨x, hx⟩ ↦ ⟨x.val, x.ne_zero, hx⟩⟩

end ValuativeTopology


namespace NormedField

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

variable (K) in
def toValuativeRel : ValuativeRel K :=
  .ofValuation valuation
scoped [NormedField] attribute [instance] NormedField.toValuativeRel

theorem compatible : valuation.Compatible (R := K) where
  rel_iff_le _ _ := Iff.rfl
scoped [NormedField] attribute [instance] NormedField.compatible

@[simp] theorem ball_norm_eq {K : Type u} [NormedField K] [IsUltrametricDist K] (x : K) :
    Metric.ball 0 ‖x‖ = { y : K | valuation y < valuation x } := by
  ext y
  simp_rw [mem_ball_zero_iff, Set.mem_setOf_eq, Valuation.Compatible.lt_iff_lt valuation,
    valuation_apply, ← NNReal.coe_lt_coe, coe_nnnorm]

theorem valuation_ball_eq (x : K) :
    (valuation (K := K)).ball (valuation x) = Metric.ball 0 ‖x‖ := by
  ext; simp_rw [Valuation.mem_ball_iff, valuation_apply, ← NNReal.coe_lt_coe,
    coe_nnnorm, mem_ball_zero_iff]

variable (K) in
omit [IsUltrametricDist K] in
lemma trivial_or_non_trivial : (∀ x : K, x = 0 ∨ ‖x‖ = 1) ∨ (∃ x : K, 1 < ‖x‖) := by
  by_contra h
  push_neg at h
  obtain ⟨⟨x, hx0, hx1⟩, hk⟩ := h
  obtain hx1 | h1x := lt_or_gt_of_ne hx1
  · exact absurd (hk x⁻¹) (not_le_of_gt <| by rwa [norm_inv, one_lt_inv₀ (norm_pos_iff.2 hx0)])
  · exact not_lt_of_ge (hk x) h1x

theorem nhds_zero_basis_norm {K : Type u} [NormedField K] :
    (nhds 0).HasBasis (fun x : K ↦ 0 < ‖x‖) fun x ↦ Metric.ball (0 : K) ‖x‖ where
  mem_iff' s := by
    refine ⟨fun hs0 ↦ ?_, fun ⟨x, x_pos, hxs⟩ ↦ ?_⟩
    · obtain trivial | ⟨x, h1x⟩ := trivial_or_non_trivial K
      · refine ⟨1, by simp, fun y hy1 ↦ ?_⟩
        rw [(trivial y).resolve_right (ne_of_lt (by simpa using hy1))]
        exact mem_of_mem_nhds hs0
      · have hix1 : ‖x⁻¹‖ < 1 := norm_inv x ▸ inv_lt_one_of_one_lt₀ h1x
        have ix_pos : 0 < ‖x⁻¹‖ := norm_inv x ▸ inv_pos_of_pos (one_pos.trans h1x)
        rw [(Metric.nhds_basis_ball_pow ix_pos hix1).mem_iff] at hs0
        obtain ⟨n, -, hns⟩ := hs0
        refine ⟨(x⁻¹) ^ n, norm_pow x⁻¹ n ▸ pow_pos ix_pos n, by rwa [norm_pow]⟩
    · exact Metric.nhds_basis_ball.mem_iff.2 ⟨_, x_pos, fun y hy ↦ hxs (by simpa using hy)⟩

theorem _root_.DiscreteTopology.of_trivial_norm (trivial : ∀ x : K, x = 0 ∨ ‖x‖ = 1) :
    DiscreteTopology K :=
  DiscreteTopology.of_forall_le_norm one_pos fun x hx ↦ by rw [(trivial x).resolve_left hx]

theorem valuativeTopology (K : Type u) [NormedField K] [IsUltrametricDist K] :
    ValuativeTopology K :=
  .mk' valuation fun s ↦ by simp_rw [valuation_ball_eq, nhds_zero_basis_norm.mem_iff, norm_pos_iff]

theorem isNontrivial (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] :
    ValuativeRel.IsNontrivial K := by
  obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
  refine ⟨⟨ValuativeRel.valuation K x, ?_, ?_⟩⟩
  · rw [Valuation.ne_zero_iff]
    exact norm_pos_iff.1 (one_pos.trans hx)
  · refine ne_of_gt ?_
    rwa [Valuation.Compatible.one_lt_iff_one_lt valuation, valuation_apply,
      ← NNReal.coe_lt_coe, NNReal.coe_one, coe_nnnorm]

scoped [NormedField] attribute [instance] valuativeTopology isNontrivial

end NormedField


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
    [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [IsUltrametricDist K] [CompleteSpace K] :
    NontriviallyNormedField L where
  __ := spectralNorm.normedField K L
  non_trivial :=
    let ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
    ⟨algebraMap K L x, hx.trans_eq <| (spectralNorm_extends _).symm⟩

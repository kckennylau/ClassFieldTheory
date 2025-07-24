import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Group.Units
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.Valuation.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuativeRel

open ValuativeRel Valuation

variable {R : Type _} [CommRing R] [ValuativeRel R]
variable {S : Type _} [CommRing S] [ValuativeRel S]
variable [Algebra R S] [ValuativeExtension R S]

lemma Valuation.Compatible.not_rel_iff_gt {Γ : Type _}
  [LinearOrderedCommMonoidWithZero Γ] {v : Valuation R Γ} [v.Compatible]
    (x y : R) : ¬(x ≤ᵥ y) ↔ v y < v x := by
  rw [Valuation.Compatible.rel_iff_le (v := v)]
  exact not_le

lemma ValuativeRel.rel_iff_le_of_valuation
    (x y : R) : x ≤ᵥ y ↔ valuation R x ≤ valuation R y :=
  Valuation.Compatible.rel_iff_le _ _

lemma ValuativeRel.not_rel_iff_gt_of_valuation
    (x y : R) : ¬(x ≤ᵥ y) ↔ valuation R y < valuation R x := Valuation.Compatible.not_rel_iff_gt _ _

lemma ValuativeExtension.mapValueGroupWithZero_strictMono : StrictMono (mapValueGroupWithZero R S) := by
  intro x y hxy
  obtain ⟨a, ⟨b, hb⟩, hx⟩ := valuation_surjective x (R := R)
  obtain ⟨a', ⟨b', hb'⟩, hy⟩ := valuation_surjective y (R := R)
  have hb_S : algebraMap R S b ∈ posSubmonoid S := by
    simp only [posSubmonoid_def] at hb ⊢
    rwa [← map_zero (algebraMap R S), rel_iff_rel]
  have hb'_S : algebraMap R S b' ∈ posSubmonoid S := by
    simp only [posSubmonoid_def] at hb' ⊢
    rwa [← map_zero (algebraMap R S), rel_iff_rel]
  simp only [posSubmonoid_def, not_rel_iff_gt_of_valuation, map_zero] at hb hb' hb_S hb'_S

  rw [← hx, ← hy]
  simp only [map_div₀, mapValueGroupWithZero_valuation]
  rw [div_lt_div_iff₀]
  simp only [← map_mul]
  rw [← not_rel_iff_gt_of_valuation, rel_iff_rel, Compatible.rel_iff_le (v := valuation R), ← lt_iff_not_ge]
  rw [map_mul, map_mul, ← div_lt_div_iff₀]
  grind
  all_goals assumption

attribute [grind] le_of_lt le_refl lt_iff_not_ge

lemma ValuativeExtension.mapValueGroupWithZero_monotone : Monotone (mapValueGroupWithZero R S) := by
  intro x y hxy
  rcases lt_trichotomy x y with hx_lt_y | hx_eq_y | hx_gt_y
  · exact le_of_lt (mapValueGroupWithZero_strictMono (S := S) ‹_›)
  · grind
  · grind

open Valuation.Compatible in
-- omit [UniformSpace K] [IsNonarchLocalField K] [UniformSpace L] [IsNonarchLocalField L] in
lemma ValuativeRel.algebraMap_integer_of_integer (x : 𝒪[R]) : (algebraMap R S) x ∈ 𝒪[S] := by
  rcases x with ⟨x, hx⟩
  change valuation S (algebraMap R S x) ≤ 1
  rwa [show 1 = valuation S (algebraMap R S 1) by simp only [map_one], ← rel_iff_le,
    ValuativeExtension.rel_iff_rel, rel_iff_le (v := valuation R)]

instance : Algebra 𝒪[R] 𝒪[S] := RingHom.toAlgebra <| (algebraMap R S).restrict _ _ <| fun x hx ↦
    ValuativeRel.algebraMap_integer_of_integer (S := S) ⟨x, hx⟩

lemma ValuativeRel.isNontrivial_iff_exists_lt_one :
    IsNontrivial R ↔ ∃ γ : (ValueGroupWithZero R)ˣ, γ < 1 := by
  constructor
  · intro hIsNontrivial
    let ⟨α, hα_neq_0, hα_neq_1⟩ := IsNontrivial.condition (R := R)
    by_cases hα_lt_one : α < 1
    · use IsUnit.unit <| Ne.isUnit hα_neq_0
      change α < 1
      assumption
    · use (IsUnit.unit <| Ne.isUnit hα_neq_0)⁻¹
      rw [Right.inv_lt_one_iff]
      change 1 < α
      have := lt_trichotomy α 1
      grind
  · intro ⟨γ, hγ⟩
    rw [@isNontrivial_iff_nontrivial_units]
    constructor
    use γ, 1
    grind

lemma ValuativeRel.valuation_of_field_surjective {K} [Field K] [ValuativeRel K] : Function.Surjective (valuation K) := by
  intro β
  obtain ⟨a, b, _⟩ := valuation_surjective β (R := K)
  use (a / b)
  rwa [Valuation.map_div (v := valuation K) a ↑b]

lemma ValuativeRel.isNontrivial_field_iff_exists_valuation_between_zero_one {K} [Field K] [ValuativeRel K] :
    IsNontrivial K ↔ ∃ x : K, 0 < valuation K x ∧ valuation K x < 1 := by
  constructor
  · intro hIsNontrivial
    let ⟨γ, hγ⟩ := isNontrivial_iff_exists_lt_one.mp hIsNontrivial
    have ⟨x, hx⟩ := valuation_of_field_surjective γ.val
    use x
    constructor
    · rw [hx]
      exact Units.zero_lt γ
    · rwa [hx]
  · intro ⟨x, h_0_lt_x, h_x_lt_1⟩
    rw [isNontrivial_iff_exists_lt_one]
    refine ⟨IsUnit.unit (a := valuation K x) ?_, ?_⟩
    · rw [isUnit_iff_ne_zero]
      grind
    · assumption

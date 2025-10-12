import ClassFieldTheory.Mathlib.RingTheory.Valuation.ValuativeRel
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Int.WithZero
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.Topology.Algebra.Valued.ValuativeRel

namespace ValuativeRel

open WithZero

variable (R : Type*) [CommRing R] [ValuativeRel R]
    [IsDiscrete R] [IsNontrivial R] [IsRankLeOne R]

def valueGroupWithZeroEquivWithZeroMulInt :
    ValueGroupWithZero R ≃*o ℤᵐ⁰ := sorry

end ValuativeRel

@[ext] structure Tiny (α : Type*) [LT α] [Zero α] [One α] : Type _ where
  val : ℝ
  pos : 0 < val
  lt_one : val < 1

namespace Tiny

open NNReal

def toNNReal (r : Tiny ℝ) : ℝ≥0 :=
  ⟨r.val, le_of_lt r.pos⟩

instance : Coe (Tiny ℝ) ℝ≥0 where
  coe := toNNReal

theorem coe_ne_zero {r : Tiny ℝ} : r.toNNReal ≠ 0 :=
  ne_of_gt r.pos

noncomputable def negLog (r : Tiny ℝ) : ℝ≥0 :=
  ⟨-r.val.log, neg_nonneg.2 <| (Real.log_le_iff_le_exp r.pos).2 <|
    le_of_lt <| by simpa using r.lt_one⟩

theorem negLog_ne_zero (r : Tiny ℝ) : r.negLog ≠ 0 :=
  _

end Tiny

namespace Valuation

open ValuativeRel NNReal WithZero

/-- Given a tiny real number (`0 < r < 1`), there is a unique valuation that sends a uniformiser
to `r`. -/
noncomputable def ofTiny (R : Type*) [CommRing R] [ValuativeRel R]
    [IsDiscrete R] [ValuativeRel.IsNontrivial R] [IsRankLeOne R] (r : Tiny ℝ) :
    Valuation R ℝ≥0 :=
  (valuation R).map
    (.comp (WithZeroMulInt.toNNReal _)
      (valueGroupWithZeroEquivWithZeroMulInt R : ValueGroupWithZero R →*o ℤᵐ⁰))
    _

end Valuation

#min_imports

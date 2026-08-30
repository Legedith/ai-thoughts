import LrcFormalization.SignedSwitching

/-!
# A bounded scalar law with vanishing cubic moment

The two-point law used here has value `1/2` with weight `8/9` and value `-1`
with weight `1/9`.  It is bounded by one, has positive first and second moments,
and has exactly zero third moment. Multiplying every Riesz amplitude by one
common sample from this law therefore removes the complete cubic layer without
changing positivity.
-/

namespace LonelyRunner.CorrelatedAmplitude

noncomputable section

/-- The two atoms of the cubic-cancelling scalar law. -/
inductive CubicAtom
  | half
  | negOne
  deriving DecidableEq, Fintype

/-- The bounded scalar value. -/
def cubicValue : CubicAtom → ℝ
  | .half => 1 / 2
  | .negOne => -1

/-- Expectation for weights `8/9` and `1/9`. -/
def cubicExpectation (f : CubicAtom → ℝ) : ℝ :=
  (8 / 9 : ℝ) * f .half + (1 / 9 : ℝ) * f .negOne

/-- The scalar law is normalized. -/
@[simp] theorem cubicExpectation_one :
    cubicExpectation (fun _ => 1) = 1 := by
  norm_num [cubicExpectation]

/-- The scalar is pointwise bounded by one. -/
theorem abs_cubicValue_le_one (ω : CubicAtom) :
    |cubicValue ω| ≤ 1 := by
  cases ω <;> norm_num [cubicValue]

/-- Its first moment is positive. -/
@[simp] theorem cubic_first_moment :
    cubicExpectation cubicValue = 1 / 3 := by
  norm_num [cubicExpectation, cubicValue]

/-- Its second moment equals its first moment. -/
@[simp] theorem cubic_second_moment :
    cubicExpectation (fun ω => (cubicValue ω) ^ 2) = 1 / 3 := by
  norm_num [cubicExpectation, cubicValue]

/-- Its cubic moment vanishes exactly. -/
@[simp] theorem cubic_third_moment :
    cubicExpectation (fun ω => (cubicValue ω) ^ 3) = 0 := by
  norm_num [cubicExpectation, cubicValue]

/-- Its fourth moment, useful for the first surviving error layer. -/
@[simp] theorem cubic_fourth_moment :
    cubicExpectation (fun ω => (cubicValue ω) ^ 4) = 1 / 6 := by
  norm_num [cubicExpectation, cubicValue]

/-- Every scaled cubic monomial is removed by the same law. -/
theorem cubic_scaled_term_vanishes (ρ c : ℝ) :
    cubicExpectation (fun ω => c * (ρ * cubicValue ω) ^ 3) = 0 := by
  simp [cubicExpectation, cubicValue]
  ring

/-- Multiplying a bounded amplitude by the scalar preserves its absolute bound. -/
theorem cubicValue_mul_bound {u : ℝ} (hu : |u| ≤ 1) (ω : CubicAtom) :
    |cubicValue ω * u| ≤ 1 := by
  calc
    |cubicValue ω * u| = |cubicValue ω| * |u| := abs_mul _ _
    _ ≤ 1 * 1 := mul_le_mul (abs_cubicValue_le_one ω) hu (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

end

end LonelyRunner.CorrelatedAmplitude

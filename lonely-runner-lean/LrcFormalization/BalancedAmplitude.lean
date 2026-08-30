import Mathlib

/-!
# Pair-cancelling bounded amplitudes

This file isolates the finite algebraic core of the proposed correlated-amplitude
Riesz-product construction for the Lonely Runner Conjecture.

No analytic Lonely Runner estimate is asserted here. The main theorem says that
an affine transform of centred variables with covariance `-1 / s^2` has exactly
zero mixed second moment.
-/

namespace LonelyRunner.CorrelatedAmplitude

noncomputable section

/-- The bounded affine amplitude used in the construction. -/
def amplitude (s h : ℝ) : ℝ := (1 + s * h) / (1 + s)

@[simp] theorem amplitude_one (s : ℝ) (hs : s ≠ -1) :
    amplitude s 1 = 1 := by
  simp [amplitude, hs]

theorem amplitude_neg_one (s : ℝ) :
    amplitude s (-1) = (1 - s) / (1 + s) := by
  simp [amplitude]
  ring

/-- If the input is a sign and `s ≥ 0`, the affine amplitude stays in `[-1,1]`. -/
theorem abs_amplitude_le_one {s h : ℝ} (hs : 0 ≤ s)
    (hh : h = 1 ∨ h = -1) :
    |amplitude s h| ≤ 1 := by
  rcases hh with rfl | rfl
  · rw [amplitude_one]
    · norm_num
    · linarith
  · rw [amplitude_neg_one]
    have hden : 0 < 1 + s := by linarith
    rw [abs_le]
    constructor
    · apply (div_le_iff₀ hden).2
      linarith
    · apply (le_div_iff₀ hden).2
      linarith

/-- Pointwise expansion of a product of two amplitudes. -/
theorem amplitude_mul {s h₁ h₂ : ℝ} (hden : 1 + s ≠ 0) :
    amplitude s h₁ * amplitude s h₂ =
      (1 + s * h₁ + s * h₂ + s ^ 2 * (h₁ * h₂)) / (1 + s) ^ 2 := by
  field_simp [amplitude, hden]
  ring

/--
Exact pair cancellation under a normalized linear expectation.

The assumptions are precisely the first two moments needed by the calculation;
positivity of the expectation is not needed for this identity.
-/
theorem expectation_pair_cancellation
    {Ω : Type*}
    (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (H₁ H₂ : Ω → ℝ)
    {s : ℝ}
    (hs : 0 < s)
    (hEone : E (1 : Ω → ℝ) = 1)
    (hE₁ : E H₁ = 0)
    (hE₂ : E H₂ = 0)
    (hE₁₂ : E (fun ω => H₁ ω * H₂ ω) = -(1 / s ^ 2)) :
    E (fun ω => amplitude s (H₁ ω) * amplitude s (H₂ ω)) = 0 := by
  have hden : 1 + s ≠ 0 := by linarith
  let C : Ω → ℝ := fun ω => H₁ ω * H₂ ω
  have hfun :
      (fun ω => amplitude s (H₁ ω) * amplitude s (H₂ ω)) =
        (1 / (1 + s) ^ 2) •
          ((1 : Ω → ℝ) + s • H₁ + s • H₂ + s ^ 2 • C) := by
    funext ω
    rw [amplitude_mul hden]
    simp [C]
    ring
  rw [hfun]
  simp only [map_smul, map_add]
  rw [hEone, hE₁, hE₂]
  change (1 / (1 + s) ^ 2) *
      (1 + s * 0 + s * 0 + s ^ 2 * E C) = 0
  rw [show E C = -(1 / s ^ 2) by simpa [C] using hE₁₂]
  have hs0 : s ≠ 0 := ne_of_gt hs
  field_simp [hs0, hden]

/--
The elementary square-root obstruction behind pair-cancelling families.
This is the final scalar implication after applying Cauchy--Schwarz and
orthogonality in `L²`.
-/
theorem square_root_barrier_scalar
    {q α : ℝ} (hq : 0 < q) (henergy : q ^ 2 * α ^ 2 ≤ q) :
    |α| ≤ 1 / Real.sqrt q := by
  have hsqrt : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hqeq : (Real.sqrt q) ^ 2 = q := by
    simpa using Real.sq_sqrt (le_of_lt hq)
  have hαsq : α ^ 2 ≤ 1 / q := by
    have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq
    apply (le_div_iff₀ hq2).2
    calc
      α ^ 2 * q ^ 2 = q ^ 2 * α ^ 2 := by ring
      _ ≤ q := henergy
  rw [abs_le]
  constructor
  · have hsquare : (-1 / Real.sqrt q) ^ 2 = 1 / q := by
      field_simp [ne_of_gt hsqrt, ne_of_gt hq]
      nlinarith [hqeq]
    nlinarith [sq_nonneg (α + 1 / Real.sqrt q), hαsq]
  · have hsquare : (1 / Real.sqrt q) ^ 2 = 1 / q := by
      field_simp [ne_of_gt hsqrt, ne_of_gt hq]
      nlinarith [hqeq]
    nlinarith [sq_nonneg (α - 1 / Real.sqrt q), hαsq]

end

end LonelyRunner.CorrelatedAmplitude

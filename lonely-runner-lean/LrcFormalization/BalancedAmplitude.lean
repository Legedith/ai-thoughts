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
  have hden : 1 + s ≠ 0 := by
    intro h
    apply hs
    calc
      s = (1 + s) - 1 := by ring
      _ = 0 - 1 := by rw [h]
      _ = -1 := by norm_num
  unfold amplitude
  simpa using div_self hden

theorem amplitude_neg_one (s : ℝ) :
    amplitude s (-1) = (1 - s) / (1 + s) := by
  unfold amplitude
  ring_nf

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
    · rw [le_div_iff₀ hden]
      linarith
    · rw [div_le_iff₀ hden]
      linarith

/-- Pointwise expansion of a product of two amplitudes. -/
theorem amplitude_mul {s h₁ h₂ : ℝ} (hden : 1 + s ≠ 0) :
    amplitude s h₁ * amplitude s h₂ =
      (1 + s * h₁ + s * h₂ + s ^ 2 * (h₁ * h₂)) / (1 + s) ^ 2 := by
  simp only [amplitude]
  field_simp [hden]
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
  ring

/--
The algebraic square-root obstruction behind pair-cancelling families.
After the usual energy estimate `q^2 * α^2 ≤ q`, it gives `q * α^2 ≤ 1`.
-/
theorem square_root_barrier_scalar
    {q α : ℝ} (hq : 0 < q) (henergy : q ^ 2 * α ^ 2 ≤ q) :
    q * α ^ 2 ≤ 1 := by
  by_contra hnot
  have hgt : 1 < q * α ^ 2 := lt_of_not_ge hnot
  have hpositive : 0 < q * (q * α ^ 2 - 1) :=
    mul_pos hq (sub_pos.mpr hgt)
  have hnonpos : q * (q * α ^ 2 - 1) ≤ 0 := by
    calc
      q * (q * α ^ 2 - 1) = q ^ 2 * α ^ 2 - q := by ring
      _ ≤ 0 := sub_nonpos.mpr henergy
  linarith

end

end LonelyRunner.CorrelatedAmplitude

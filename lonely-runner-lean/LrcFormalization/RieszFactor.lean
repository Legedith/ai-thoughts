import LrcFormalization.SupportColoring

/-!
# Positivity of the correlated Riesz factors
-/

namespace LonelyRunner.CorrelatedAmplitude

noncomputable section

/-- One real Riesz-product factor. -/
def rieszFactor (ρ u θ : ℝ) : ℝ := 1 - ρ * u * Real.cos θ

/-- Bounded amplitudes preserve pointwise nonnegativity of every Riesz factor. -/
theorem rieszFactor_nonneg
    {ρ u θ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hu : |u| ≤ 1) :
    0 ≤ rieszFactor ρ u θ := by
  have hcos : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  have habs : |ρ * u * Real.cos θ| ≤ 1 := by
    calc
      |ρ * u * Real.cos θ| = ρ * |u| * |Real.cos θ| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hρ₀]
      _ ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by norm_num
  have hupper : ρ * u * Real.cos θ ≤ 1 :=
    le_trans (le_abs_self (ρ * u * Real.cos θ)) habs
  simpa [rieszFactor] using sub_nonneg.mpr hupper

/-- A finite product of nonnegative correlated Riesz factors is nonnegative. -/
theorem rieszProduct_nonneg
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι)
    (ρ : ℝ) (u θ : ι → ℝ)
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hu : ∀ i ∈ S, |u i| ≤ 1) :
    0 ≤ ∏ i ∈ S, rieszFactor ρ (u i) (θ i) := by
  apply Finset.prod_nonneg
  intro i hi
  exact rieszFactor_nonneg hρ₀ hρ₁ (hu i hi)

end

end LonelyRunner.CorrelatedAmplitude

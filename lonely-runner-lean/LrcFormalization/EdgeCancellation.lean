import LrcFormalization.BalancedAmplitude

/-!
# Edgewise pair cancellation

This file records the hypothesis-transparent algebraic interface used by the
strict-vector/Lovasz-theta refinement. The probabilistic construction of the
bounded centred variables is deliberately separated from the deterministic
amplitude calculation.
-/

namespace LonelyRunner.CorrelatedAmplitude

noncomputable section

variable {V Ω : Type*}

/-- Pull a family of bounded centred variables through the affine amplitude map. -/
def transformedValue (s : ℝ) (H : V → Ω → ℝ) (v : V) : Ω → ℝ :=
  fun ω => amplitude s (H v ω)

/-- Bounded base variables give bounded transformed amplitudes. -/
theorem transformedValue_bound
    (H : V → Ω → ℝ) {s : ℝ} (hs : 0 ≤ s)
    (hbound : ∀ v ω, |H v ω| ≤ 1)
    (v : V) (ω : Ω) :
    |transformedValue s H v ω| ≤ 1 := by
  exact abs_amplitude_le_one_of_abs_le_one hs (hbound v ω)

/-- Centred base variables give the same positive mean after transformation. -/
theorem transformedValue_mean
    (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (H : V → Ω → ℝ)
    {s : ℝ} (hs : 0 < s)
    (hEone : E (1 : Ω → ℝ) = 1)
    (hcenter : ∀ v, E (H v) = 0)
    (v : V) :
    E (transformedValue s H v) = 1 / (1 + s) := by
  exact expectation_amplitude E (H v) hs hEone (hcenter v)

/--
If adjacent base variables have covariance `-β` and `s² β = 1`, the transformed
amplitudes have exactly zero mixed second moment on every edge.
-/
theorem transformedValue_edge_zero
    (adj : V → V → Prop)
    (E : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (H : V → Ω → ℝ)
    {s β : ℝ} (hs : 0 < s)
    (hEone : E (1 : Ω → ℝ) = 1)
    (hcenter : ∀ v, E (H v) = 0)
    (hcov : ∀ ⦃u v⦄, adj u v →
      E (fun ω => H u ω * H v ω) = -β)
    (hscale : s ^ 2 * β = 1)
    {u v : V} (huv : adj u v) :
    E (fun ω => transformedValue s H u ω * transformedValue s H v ω) = 0 := by
  simpa [transformedValue] using
    expectation_pair_cancellation_of_covariance
      E (H u) (H v) hs hEone (hcenter u) (hcenter v) (hcov huv) hscale

end

end LonelyRunner.CorrelatedAmplitude

import LrcFormalization.GlobalPhaseFilter

/-!
# Analytic realization of the first-harmonic phase filter

This file identifies the symbolic moments from `GlobalPhaseFilter` with the
normalized interval integral against the nonnegative density `1 + cos θ` on
`[-π, π]`.
-/

namespace LonelyRunner.CorrelatedAmplitude

noncomputable section

/-- Normalized averaging against the first-harmonic density. -/
def phaseAverage (f : ℝ → ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ θ in -Real.pi..Real.pi, firstHarmonicWeight θ * f θ

private theorem intervalIntegrable_cos_mode (k : ℤ) :
    IntervalIntegrable (fun θ : ℝ => Real.cos ((k : ℝ) * θ))
      MeasureTheory.volume (-Real.pi) Real.pi := by
  exact (by fun_prop : Continuous (fun θ : ℝ => Real.cos ((k : ℝ) * θ))).intervalIntegrable _ _

private theorem intervalIntegrable_sin_mode (k : ℤ) :
    IntervalIntegrable (fun θ : ℝ => Real.sin ((k : ℝ) * θ))
      MeasureTheory.volume (-Real.pi) Real.pi := by
  exact (by fun_prop : Continuous (fun θ : ℝ => Real.sin ((k : ℝ) * θ))).intervalIntegrable _ _

private theorem intervalIntegrable_cos_mul_cos_mode (k : ℤ) :
    IntervalIntegrable
      (fun θ : ℝ => Real.cos θ * Real.cos ((k : ℝ) * θ))
      MeasureTheory.volume (-Real.pi) Real.pi := by
  exact (by fun_prop : Continuous
    (fun θ : ℝ => Real.cos θ * Real.cos ((k : ℝ) * θ))).intervalIntegrable _ _

private theorem intervalIntegrable_cos_mul_sin_mode (k : ℤ) :
    IntervalIntegrable
      (fun θ : ℝ => Real.cos θ * Real.sin ((k : ℝ) * θ))
      MeasureTheory.volume (-Real.pi) Real.pi := by
  exact (by fun_prop : Continuous
    (fun θ : ℝ => Real.cos θ * Real.sin ((k : ℝ) * θ))).intervalIntegrable _ _

/-- Integral of an integer-frequency cosine over a full period. -/
theorem integral_cos_int_mul (k : ℤ) :
    (∫ θ in -Real.pi..Real.pi, Real.cos ((k : ℝ) * θ)) =
      if k = 0 then 2 * Real.pi else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [two_mul]
  · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have h := intervalIntegral.mul_integral_comp_mul_left
      (f := Real.cos) (c := (k : ℝ))
      (a := -Real.pi) (b := Real.pi)
    have hrhs :
        (∫ x in (k : ℝ) * (-Real.pi)..(k : ℝ) * Real.pi,
          Real.cos x) = 0 := by
      simp [mul_neg]
    rw [hrhs] at h
    have hint :
        (∫ θ in -Real.pi..Real.pi, Real.cos ((k : ℝ) * θ)) = 0 := by
      exact (mul_eq_zero.mp h).resolve_left hkR
    simp [hk, hint]

/-- Integral of an integer-frequency sine over a full period. -/
theorem integral_sin_int_mul (k : ℤ) :
    (∫ θ in -Real.pi..Real.pi, Real.sin ((k : ℝ) * θ)) = 0 := by
  by_cases hk : k = 0
  · subst k
    simp
  · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have h := intervalIntegral.mul_integral_comp_mul_left
      (f := Real.sin) (c := (k : ℝ))
      (a := -Real.pi) (b := Real.pi)
    have hrhs :
        (∫ x in (k : ℝ) * (-Real.pi)..(k : ℝ) * Real.pi,
          Real.sin x) = 0 := by
      simp [mul_neg, Real.cos_neg]
    rw [hrhs] at h
    exact (mul_eq_zero.mp h).resolve_left hkR

/-- Orthogonality of cosine modes against the first cosine. -/
theorem integral_cos_mul_cos_int (k : ℤ) :
    (∫ θ in -Real.pi..Real.pi,
      Real.cos θ * Real.cos ((k : ℝ) * θ)) =
      if k = 1 ∨ k = -1 then Real.pi else 0 := by
  have hpoint : ∀ θ : ℝ,
      Real.cos θ * Real.cos ((k : ℝ) * θ) =
        (Real.cos (((k - 1 : ℤ) : ℝ) * θ) +
          Real.cos (((k + 1 : ℤ) : ℝ) * θ)) / 2 := by
    intro θ
    rw [show (((k - 1 : ℤ) : ℝ) * θ) = (k : ℝ) * θ - θ by push_cast; ring]
    rw [show (((k + 1 : ℤ) : ℝ) * θ) = (k : ℝ) * θ + θ by push_cast; ring]
    rw [Real.cos_sub, Real.cos_add]
    ring
  calc
    (∫ θ in -Real.pi..Real.pi,
      Real.cos θ * Real.cos ((k : ℝ) * θ)) =
        ∫ θ in -Real.pi..Real.pi,
          (Real.cos (((k - 1 : ℤ) : ℝ) * θ) +
            Real.cos (((k + 1 : ℤ) : ℝ) * θ)) / 2 := by
      apply intervalIntegral.integral_congr
      intro θ _
      exact hpoint θ
    _ = ((∫ θ in -Real.pi..Real.pi,
          Real.cos (((k - 1 : ℤ) : ℝ) * θ)) +
        (∫ θ in -Real.pi..Real.pi,
          Real.cos (((k + 1 : ℤ) : ℝ) * θ))) / 2 := by
      rw [intervalIntegral.integral_div]
      rw [intervalIntegral.integral_add
        (intervalIntegrable_cos_mode (k - 1))
        (intervalIntegrable_cos_mode (k + 1))]
    _ = if k = 1 ∨ k = -1 then Real.pi else 0 := by
      rw [integral_cos_int_mul, integral_cos_int_mul]
      by_cases h1 : k = 1
      · subst k
        simp [two_mul]
      · by_cases hn1 : k = -1
        · subst k
          simp [two_mul]
        · have hkm1 : k - 1 ≠ 0 := by omega
          have hkp1 : k + 1 ≠ 0 := by omega
          simp [h1, hn1, hkm1, hkp1]

/-- Orthogonality of sine modes after multiplying by the first cosine. -/
theorem integral_cos_mul_sin_int (k : ℤ) :
    (∫ θ in -Real.pi..Real.pi,
      Real.cos θ * Real.sin ((k : ℝ) * θ)) = 0 := by
  have hpoint : ∀ θ : ℝ,
      Real.cos θ * Real.sin ((k : ℝ) * θ) =
        (Real.sin (((k + 1 : ℤ) : ℝ) * θ) +
          Real.sin (((k - 1 : ℤ) : ℝ) * θ)) / 2 := by
    intro θ
    rw [show (((k + 1 : ℤ) : ℝ) * θ) = (k : ℝ) * θ + θ by push_cast; ring]
    rw [show (((k - 1 : ℤ) : ℝ) * θ) = (k : ℝ) * θ - θ by push_cast; ring]
    rw [Real.sin_add, Real.sin_sub]
    ring
  calc
    (∫ θ in -Real.pi..Real.pi,
      Real.cos θ * Real.sin ((k : ℝ) * θ)) =
        ∫ θ in -Real.pi..Real.pi,
          (Real.sin (((k + 1 : ℤ) : ℝ) * θ) +
            Real.sin (((k - 1 : ℤ) : ℝ) * θ)) / 2 := by
      apply intervalIntegral.integral_congr
      intro θ _
      exact hpoint θ
    _ = ((∫ θ in -Real.pi..Real.pi,
          Real.sin (((k + 1 : ℤ) : ℝ) * θ)) +
        (∫ θ in -Real.pi..Real.pi,
          Real.sin (((k - 1 : ℤ) : ℝ) * θ))) / 2 := by
      rw [intervalIntegral.integral_div]
      rw [intervalIntegral.integral_add
        (intervalIntegrable_sin_mode (k + 1))
        (intervalIntegrable_sin_mode (k - 1))]
    _ = 0 := by
      rw [integral_sin_int_mul, integral_sin_int_mul]
      ring

/-- The density `1 + cos θ` realizes the symbolic first-harmonic cosine moments. -/
theorem phaseAverage_cos (k : ℤ) :
    phaseAverage (fun θ => Real.cos ((k : ℝ) * θ)) =
      firstHarmonicMoment k := by
  unfold phaseAverage firstHarmonicWeight
  have hsplit :
      (∫ θ in -Real.pi..Real.pi,
        (1 + Real.cos θ) * Real.cos ((k : ℝ) * θ)) =
        (∫ θ in -Real.pi..Real.pi, Real.cos ((k : ℝ) * θ)) +
        (∫ θ in -Real.pi..Real.pi,
          Real.cos θ * Real.cos ((k : ℝ) * θ)) := by
    calc
      (∫ θ in -Real.pi..Real.pi,
        (1 + Real.cos θ) * Real.cos ((k : ℝ) * θ)) =
          ∫ θ in -Real.pi..Real.pi,
            (Real.cos ((k : ℝ) * θ) +
              Real.cos θ * Real.cos ((k : ℝ) * θ)) := by
        apply intervalIntegral.integral_congr
        intro θ _
        ring
      _ = _ := intervalIntegral.integral_add
        (intervalIntegrable_cos_mode k)
        (intervalIntegrable_cos_mul_cos_mode k)
  rw [hsplit, integral_cos_int_mul, integral_cos_mul_cos_int]
  by_cases h0 : k = 0
  · subst k
    simp [firstHarmonicMoment]
    field_simp [Real.pi_ne_zero]
  · by_cases hpm : k = 1 ∨ k = -1
    · simp [h0, hpm, firstHarmonicMoment]
      field_simp [Real.pi_ne_zero]
    · simp [h0, hpm, firstHarmonicMoment]

/-- All sine moments of the first-harmonic density vanish. -/
theorem phaseAverage_sin (k : ℤ) :
    phaseAverage (fun θ => Real.sin ((k : ℝ) * θ)) = 0 := by
  unfold phaseAverage firstHarmonicWeight
  have hsplit :
      (∫ θ in -Real.pi..Real.pi,
        (1 + Real.cos θ) * Real.sin ((k : ℝ) * θ)) =
        (∫ θ in -Real.pi..Real.pi, Real.sin ((k : ℝ) * θ)) +
        (∫ θ in -Real.pi..Real.pi,
          Real.cos θ * Real.sin ((k : ℝ) * θ)) := by
    calc
      (∫ θ in -Real.pi..Real.pi,
        (1 + Real.cos θ) * Real.sin ((k : ℝ) * θ)) =
          ∫ θ in -Real.pi..Real.pi,
            (Real.sin ((k : ℝ) * θ) +
              Real.cos θ * Real.sin ((k : ℝ) * θ)) := by
        apply intervalIntegral.integral_congr
        intro θ _
        ring
      _ = _ := intervalIntegral.integral_add
        (intervalIntegrable_sin_mode k)
        (intervalIntegrable_cos_mul_sin_mode k)
  rw [hsplit, integral_sin_int_mul, integral_cos_mul_sin_int]
  ring

end

end LonelyRunner.CorrelatedAmplitude

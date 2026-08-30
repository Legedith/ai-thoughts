import LrcFormalization.QuarterPhase

/-!
# The first-harmonic global phase filter

Averaging a common phase against the nonnegative density `1 + cos θ` keeps
only phase imbalances `0`, `1`, and `-1`.  This file formalizes the exact
finite Fourier-selection rule used after that elementary integral calculation.

The analytic identification of `firstHarmonicMoment` with the normalized
Fourier coefficients of `1 + cos θ` is intentionally kept separate; the
selection and parity consequences below are purely finite algebra.
-/

namespace LonelyRunner.CorrelatedAmplitude

noncomputable section

/-- The nonnegative density underlying the global phase filter. -/
def firstHarmonicWeight (θ : ℝ) : ℝ := 1 + Real.cos θ

/-- The first-harmonic weight is pointwise nonnegative. -/
theorem firstHarmonicWeight_nonneg (θ : ℝ) :
    0 ≤ firstHarmonicWeight θ := by
  unfold firstHarmonicWeight
  linarith [Real.neg_one_le_cos θ]

/-- A sign selecting the positive or negative Fourier mode from one cosine. -/
inductive FourierSign
  | pos
  | neg
  deriving DecidableEq

namespace FourierSign

/-- The integer Fourier contribution of a selected sign. -/
def value : FourierSign → ℤ
  | pos => 1
  | neg => -1

@[simp] theorem value_pos : value pos = 1 := rfl
@[simp] theorem value_neg : value neg = -1 := rfl

/-- Equal signs have phase imbalance `2` or `-2`. -/
theorem add_self_not_allowed (σ : FourierSign) :
    value σ + value σ ≠ 0 ∧
    value σ + value σ ≠ 1 ∧
    value σ + value σ ≠ -1 := by
  cases σ <;> norm_num

/-- Opposite signs have phase imbalance zero. -/
theorem add_eq_zero_iff_ne (σ τ : FourierSign) :
    value σ + value τ = 0 ↔ σ ≠ τ := by
  cases σ <;> cases τ <;> simp

end FourierSign

/-- The three phase imbalances retained by the density `1 + cos θ`. -/
def AllowedImbalance (r : ℤ) : Prop := r = 0 ∨ r = 1 ∨ r = -1

/-- Its normalized Fourier moment: `1` at zero, `1/2` at `±1`, and zero elsewhere. -/
def firstHarmonicMoment (r : ℤ) : ℝ :=
  if r = 0 then 1 else if r = 1 ∨ r = -1 then 1 / 2 else 0

@[simp] theorem firstHarmonicMoment_zero : firstHarmonicMoment 0 = 1 := by
  simp [firstHarmonicMoment]

@[simp] theorem firstHarmonicMoment_one : firstHarmonicMoment 1 = 1 / 2 := by
  norm_num [firstHarmonicMoment]

@[simp] theorem firstHarmonicMoment_neg_one : firstHarmonicMoment (-1) = 1 / 2 := by
  norm_num [firstHarmonicMoment]

/-- Every disallowed phase imbalance is removed exactly. -/
theorem firstHarmonicMoment_eq_zero {r : ℤ}
    (hr : ¬ AllowedImbalance r) :
    firstHarmonicMoment r = 0 := by
  simp only [AllowedImbalance, not_or] at hr
  simp [firstHarmonicMoment, hr.1, hr.2.1, hr.2.2]

/-- The phase imbalance of a finite signed support. -/
def phaseImbalance {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (σ : ι → FourierSign) : ℤ :=
  ∑ i ∈ S, (σ i).value

/-- A term with disallowed total phase imbalance is killed by the filter. -/
theorem filtered_support_vanishes
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (σ : ι → FourierSign)
    (h : ¬ AllowedImbalance (phaseImbalance S σ)) :
    firstHarmonicMoment (phaseImbalance S σ) = 0 :=
  firstHarmonicMoment_eq_zero h

/-- At quadratic level, selecting the same Fourier sign is removed exactly. -/
theorem same_sign_quadratic_vanishes (σ : FourierSign) :
    firstHarmonicMoment (σ.value + σ.value) = 0 := by
  apply firstHarmonicMoment_eq_zero
  rcases σ.add_self_not_allowed with ⟨h0, h1, hn1⟩
  exact fun h => h.elim h0 (fun h' => h'.elim h1 hn1)

/-- At quadratic level, opposite signs survive with zero phase imbalance. -/
theorem opposite_sign_quadratic_survives
    (σ τ : FourierSign) (hστ : σ ≠ τ) :
    firstHarmonicMoment (σ.value + τ.value) = 1 := by
  rw [(σ.add_eq_zero_iff_ne τ).2 hστ]
  exact firstHarmonicMoment_zero

/--
Every even support surviving the first-harmonic filter is exactly balanced:
its positive and negative Fourier choices occur equally often.
-/
theorem even_allowed_imbalance_eq_zero {r : ℤ}
    (heven : Even r) (hallowed : AllowedImbalance r) :
    r = 0 := by
  rcases hallowed with rfl | rfl | rfl
  · rfl
  · simpa using heven
  · simpa using heven

end

end LonelyRunner.CorrelatedAmplitude

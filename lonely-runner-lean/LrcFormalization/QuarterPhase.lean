import LrcFormalization.RieszFactor

/-!
# Quarter-phase separation of quadratic Fourier terms

A common phase `π / 4` separates the two quadratic frequency types arising
from products of shifted cosines.  After pairing against a linear functional
that annihilates sine waves (for example integration against an even density),
the sum-frequency term disappears exactly, while the difference-frequency
term survives.  The level-one cosine coefficient loses only the fixed factor
`√2 / 2`.
-/

namespace LonelyRunner.CorrelatedAmplitude

noncomputable section

/-- The common phase used to remove quadratic sum frequencies. -/
def quarterPhase : ℝ := Real.pi / 4

/-- A cosine shifted by a quarter phase is the cosine-sine difference. -/
theorem cos_add_quarterPhase (x : ℝ) :
    Real.cos (x + quarterPhase) =
      (Real.sqrt 2 / 2) * (Real.cos x - Real.sin x) := by
  simp [quarterPhase, Real.cos_add]
  ring

/-- Product identity separating a difference frequency from a sum frequency. -/
theorem cos_add_quarterPhase_mul (x y : ℝ) :
    Real.cos (x + quarterPhase) * Real.cos (y + quarterPhase) =
      (Real.cos (x - y) - Real.sin (x + y)) / 2 := by
  rw [cos_add_quarterPhase, cos_add_quarterPhase]
  rw [Real.cos_sub, Real.sin_add]
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  nlinarith

/-- A real linear functional annihilates all sine waves. -/
def SineAnnihilating (L : (ℝ → ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ r : ℝ, L (fun x => Real.sin (r * x)) = 0

/-- Under an even pairing, the quarter phase costs exactly `√2 / 2` at level one. -/
theorem quarterPhase_linear_pairing
    (L : (ℝ → ℝ) →ₗ[ℝ] ℝ)
    (hL : SineAnnihilating L)
    (a : ℝ) :
    L (fun x => Real.cos (a * x + quarterPhase)) =
      (Real.sqrt 2 / 2) * L (fun x => Real.cos (a * x)) := by
  have hfun :
      (fun x => Real.cos (a * x + quarterPhase)) =
        (Real.sqrt 2 / 2) •
          ((fun x => Real.cos (a * x)) - (fun x => Real.sin (a * x))) := by
    funext x
    rw [cos_add_quarterPhase]
    simp
  rw [hfun, map_smul, map_sub, hL a]
  ring

/--
Under an even pairing, a common quarter phase removes the quadratic sum
frequency and leaves only the difference frequency.
-/
theorem quarterPhase_quadratic_pairing
    (L : (ℝ → ℝ) →ₗ[ℝ] ℝ)
    (hL : SineAnnihilating L)
    (a b : ℝ) :
    L (fun x =>
      Real.cos (a * x + quarterPhase) *
        Real.cos (b * x + quarterPhase)) =
      (1 / 2 : ℝ) * L (fun x => Real.cos ((a - b) * x)) := by
  have hfun :
      (fun x =>
        Real.cos (a * x + quarterPhase) *
          Real.cos (b * x + quarterPhase)) =
        (1 / 2 : ℝ) • (fun x => Real.cos ((a - b) * x)) -
          (1 / 2 : ℝ) • (fun x => Real.sin ((a + b) * x)) := by
    funext x
    rw [cos_add_quarterPhase_mul]
    rw [show a * x - b * x = (a - b) * x by ring]
    rw [show a * x + b * x = (a + b) * x by ring]
    simp
    ring
  rw [hfun, map_sub, map_smul, map_smul, hL (a + b)]
  ring

end

end LonelyRunner.CorrelatedAmplitude

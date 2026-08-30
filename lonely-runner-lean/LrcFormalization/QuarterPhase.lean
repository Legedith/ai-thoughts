import LrcFormalization.RieszFactor

/-!
# Quarter-phase separation of quadratic Fourier terms

A phase `π / 4` separates the two quadratic frequency types arising from
products of shifted cosines.  There are two useful forms.

* Pairing one shifted product against a sine-annihilating linear functional
  removes its sum-frequency term.
* Averaging the two phases `±π / 4` removes the sum-frequency term pointwise,
  with no symmetry hypothesis on the later pairing.

In both forms the level-one cosine coefficient loses only the fixed factor
`√2 / 2`.
-/

namespace LonelyRunner.CorrelatedAmplitude

noncomputable section

/-- The common phase used to remove quadratic sum frequencies. -/
def quarterPhase : ℝ := Real.pi / 4

/-- A cosine shifted by a positive quarter phase is a cosine-sine difference. -/
theorem cos_add_quarterPhase (x : ℝ) :
    Real.cos (x + quarterPhase) =
      (Real.sqrt 2 / 2) * (Real.cos x - Real.sin x) := by
  simp [quarterPhase, Real.cos_add]
  ring

/-- A cosine shifted by a negative quarter phase is a cosine-sine sum. -/
theorem cos_sub_quarterPhase (x : ℝ) :
    Real.cos (x - quarterPhase) =
      (Real.sqrt 2 / 2) * (Real.cos x + Real.sin x) := by
  simp [quarterPhase, Real.cos_sub]
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

/-- Symmetric quarter-phase averaging keeps the linear cosine at constant strength. -/
theorem symmetric_quarterPhase_linear (x : ℝ) :
    (Real.cos (x + quarterPhase) + Real.cos (x - quarterPhase)) / 2 =
      (Real.sqrt 2 / 2) * Real.cos x := by
  rw [cos_add_quarterPhase, cos_sub_quarterPhase]
  ring

/--
Symmetric averaging over the phases `±π / 4` removes the quadratic
sum-frequency term pointwise and leaves exactly half the difference frequency.
-/
theorem symmetric_quarterPhase_quadratic (x y : ℝ) :
    (Real.cos (x + quarterPhase) * Real.cos (y + quarterPhase) +
        Real.cos (x - quarterPhase) * Real.cos (y - quarterPhase)) / 2 =
      Real.cos (x - y) / 2 := by
  rw [cos_add_quarterPhase, cos_add_quarterPhase,
    cos_sub_quarterPhase, cos_sub_quarterPhase]
  rw [Real.cos_sub]
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

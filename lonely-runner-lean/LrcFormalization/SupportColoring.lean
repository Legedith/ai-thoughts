import LrcFormalization.BalancedAmplitude

/-!
# Support colorings and exact quadratic cancellation

A family of finite supports records the low-order arithmetic relations that must
be controlled. A coloring is proper for these supports when it is injective on
each support. Pulling a pair-cancelling amplitude family back along such a
coloring kills every mixed quadratic term inside every recorded support.
-/

namespace LonelyRunner.CorrelatedAmplitude

noncomputable section

variable {V C Ω : Type*}

/-- A coloring is proper for a family of finite supports if it is injective on each support. -/
def ProperForSupports [DecidableEq V]
    (supports : Set (Finset V)) (color : V → C) : Prop :=
  ∀ S, S ∈ supports → Set.InjOn color (S : Set V)

/-- An abstract normalized family of bounded amplitudes with exact pair cancellation. -/
structure PairCancellingFamily (C Ω : Type*) where
  expectation : (Ω → ℝ) →ₗ[ℝ] ℝ
  value : C → Ω → ℝ
  normalized : expectation (1 : Ω → ℝ) = 1
  bound : ∀ c ω, |value c ω| ≤ 1
  mean : ℝ
  commonMean : ∀ c, expectation (value c) = mean
  pairZero : ∀ ⦃c d⦄, c ≠ d →
    expectation (fun ω => value c ω * value d ω) = 0

/-- A proper support-coloring pulls pair cancellation back to every distinct pair in a support. -/
theorem pullback_pair_zero
    [DecidableEq V]
    (supports : Set (Finset V))
    (color : V → C)
    (hproper : ProperForSupports supports color)
    (A : PairCancellingFamily C Ω)
    {S : Finset V} (hS : S ∈ supports)
    {u v : V} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    A.expectation (fun ω => A.value (color u) ω * A.value (color v) ω) = 0 := by
  apply A.pairZero
  exact (hproper S hS) hu hv huv

/-- The pulled-back amplitude remains pointwise bounded by one. -/
theorem pullback_bound
    (A : PairCancellingFamily C Ω) (color : V → C) (v : V) (ω : Ω) :
    |A.value (color v) ω| ≤ 1 :=
  A.bound (color v) ω

/-- The pulled-back amplitudes retain their common mean. -/
theorem pullback_mean
    (A : PairCancellingFamily C Ω) (color : V → C) (v : V) :
    A.expectation (A.value (color v)) = A.mean :=
  A.commonMean (color v)

end

end LonelyRunner.CorrelatedAmplitude

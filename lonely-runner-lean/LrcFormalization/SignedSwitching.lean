import LrcFormalization.GlobalPhaseFilter

/-!
# Signed phase switching

A vertex switch `η_v ∈ {±1}` changes the phase contribution of a Fourier sign
`σ_v` from `σ_v` to `σ_v η_v`. If the switched signs are constant on a
relation support of size at least two, the first-harmonic phase filter removes
that relation exactly: its phase imbalance has absolute value at least two.

At quadratic level the condition that two switched signs agree is precisely
the standard signed-graph switching equation

`η_u η_v = σ_u σ_v`.

This is the finite algebraic core of the signed-switching refinement.
-/

namespace LonelyRunner.CorrelatedAmplitude

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- The Fourier sign after applying a vertex phase switch. -/
def switchedValue (σ η : FourierSign) : ℤ := σ.value * η.value

/-- Total switched phase imbalance on a finite support. -/
def switchedPhaseImbalance
    (S : Finset V) (σ η : V → FourierSign) : ℤ :=
  ∑ v ∈ S, switchedValue (σ v) (η v)

/-- All switched signs on the support point in one common direction. -/
def SwitchMonochromatic
    (S : Finset V) (σ η : V → FourierSign) : Prop :=
  ∃ τ : FourierSign, ∀ v ∈ S, switchedValue (σ v) (η v) = τ.value

/-- A switched sign is always `1` or `-1`. -/
theorem switchedValue_eq_one_or_neg_one (σ η : FourierSign) :
    switchedValue σ η = 1 ∨ switchedValue σ η = -1 := by
  cases σ <;> cases η <;> simp [switchedValue, FourierSign.value]

/--
For a pair, equality of the switched signs is exactly the signed-graph
switching equation.
-/
theorem switchedValue_eq_iff_switch_product_eq_sign_product
    (σu σv ηu ηv : FourierSign) :
    switchedValue σu ηu = switchedValue σv ηv ↔
      ηu.value * ηv.value = σu.value * σv.value := by
  cases σu <;> cases σv <;> cases ηu <;> cases ηv <;>
    norm_num [switchedValue, FourierSign.value]

/-- A monochromatic switched support has imbalance `card(S)` times one sign. -/
theorem switchedPhaseImbalance_eq_card_mul
    {S : Finset V} {σ η : V → FourierSign}
    (hmono : SwitchMonochromatic S σ η) :
    ∃ τ : FourierSign,
      switchedPhaseImbalance S σ η = (S.card : ℤ) * τ.value := by
  rcases hmono with ⟨τ, hτ⟩
  refine ⟨τ, ?_⟩
  unfold switchedPhaseImbalance
  calc
    (∑ v ∈ S, switchedValue (σ v) (η v)) =
        ∑ v ∈ S, τ.value := by
      apply Finset.sum_congr rfl
      intro v hv
      exact hτ v hv
    _ = (S.card : ℤ) * τ.value := by simp

/--
A switched-monochromatic support of size at least two has disallowed imbalance,
so it is deleted by the first-harmonic filter.
-/
theorem switchMonochromatic_not_allowed
    {S : Finset V} {σ η : V → FourierSign}
    (hcard : 2 ≤ S.card)
    (hmono : SwitchMonochromatic S σ η) :
    ¬ AllowedImbalance (switchedPhaseImbalance S σ η) := by
  rcases switchedPhaseImbalance_eq_card_mul hmono with ⟨τ, hsum⟩
  have hcardZ : (2 : ℤ) ≤ (S.card : ℤ) := by exact_mod_cast hcard
  intro hallowed
  rw [hsum] at hallowed
  cases hτ : τ with
  | pos =>
      have ha' :
          (S.card : ℤ) = 0 ∨ (S.card : ℤ) = 1 ∨ (S.card : ℤ) = -1 := by
        simpa [FourierSign.value, hτ, AllowedImbalance] using hallowed
      rcases ha' with h0 | h1 | hn1 <;> omega
  | neg =>
      have ha' :
          -(S.card : ℤ) = 0 ∨ -(S.card : ℤ) = 1 ∨ -(S.card : ℤ) = -1 := by
        simpa [FourierSign.value, hτ, AllowedImbalance] using hallowed
      rcases ha' with h0 | h1 | hn1 <;> omega

/-- The symbolic first-harmonic moment of such a support is exactly zero. -/
theorem switchMonochromatic_filtered_vanishes
    {S : Finset V} {σ η : V → FourierSign}
    (hcard : 2 ≤ S.card)
    (hmono : SwitchMonochromatic S σ η) :
    firstHarmonicMoment (switchedPhaseImbalance S σ η) = 0 :=
  firstHarmonicMoment_eq_zero
    (switchMonochromatic_not_allowed hcard hmono)

/-- A two-point support is switch-monochromatic exactly when its switched values agree. -/
theorem pair_switchMonochromatic_iff_switchedValue_eq
    (u v : V) (huv : u ≠ v)
    (σ η : V → FourierSign) :
    SwitchMonochromatic ({u, v} : Finset V) σ η ↔
      switchedValue (σ u) (η u) = switchedValue (σ v) (η v) := by
  constructor
  · rintro ⟨τ, hτ⟩
    have hu := hτ u (by simp)
    have hv := hτ v (by simp)
    exact hu.trans hv.symm
  · intro hsame
    rcases switchedValue_eq_one_or_neg_one (σ u) (η u) with huone | huneg
    · refine ⟨FourierSign.pos, ?_⟩
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · simpa [FourierSign.value] using huone
      · have hvone : switchedValue (σ v) (η v) = 1 :=
          hsame.symm.trans huone
        simpa [FourierSign.value] using hvone
    · refine ⟨FourierSign.neg, ?_⟩
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · simpa [FourierSign.value] using huneg
      · have hvneg : switchedValue (σ v) (η v) = -1 :=
          hsame.symm.trans huneg
        simpa [FourierSign.value] using hvneg

/-- The pair form translating a signed relation edge into a switch constraint. -/
theorem pair_switchMonochromatic_iff
    (u v : V) (huv : u ≠ v)
    (σ η : V → FourierSign) :
    SwitchMonochromatic ({u, v} : Finset V) σ η ↔
      (η u).value * (η v).value = (σ u).value * (σ v).value := by
  exact (pair_switchMonochromatic_iff_switchedValue_eq u v huv σ η).trans
    (switchedValue_eq_iff_switch_product_eq_sign_product
      (σ u) (σ v) (η u) (η v))

end

end LonelyRunner.CorrelatedAmplitude

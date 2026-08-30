import LrcFormalization.GlobalPhaseFilter

/-!
# Opposition colorings

For a signed relation, a coloring need only separate vertices carrying opposite
Fourier signs.  Independent first-harmonic phase filters then remove every
same-sign color collision.  Consequently every relation term that survives all
phase filters is automatically color-injective.

This is the finite combinatorial core of the refined opposition-graph Riesz
construction.
-/

namespace LonelyRunner.CorrelatedAmplitude

noncomputable section

variable {V C : Type*} [DecidableEq V] [DecidableEq C]

/-- Opposite Fourier signs are required to receive distinct colors. -/
def ProperForOpposition
    (S : Finset V) (σ : V → FourierSign) (color : V → C) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ S → v ∈ S → σ u ≠ σ v → color u ≠ color v

/-- The total phase imbalance inside one color class. -/
def colorPhaseImbalance
    (S : Finset V) (σ : V → FourierSign) (color : V → C) (c : C) : ℤ :=
  ∑ v ∈ S.filter (fun v => color v = c), (σ v).value

/-- Opposition properness forces every nonempty color fiber to have one sign. -/
theorem sign_eq_of_same_color
    {S : Finset V} {σ : V → FourierSign} {color : V → C}
    (hproper : ProperForOpposition S σ color)
    {u v : V} (hu : u ∈ S) (hv : v ∈ S)
    (hcolor : color u = color v) :
    σ u = σ v := by
  by_contra hsign
  exact (hproper hu hv hsign) hcolor

/--
If every color has allowed phase imbalance `0`, `1`, or `-1`, an opposition
proper coloring is injective on the whole signed support.
-/
theorem surviving_support_color_injective
    {S : Finset V} {σ : V → FourierSign} {color : V → C}
    (hproper : ProperForOpposition S σ color)
    (hallowed : ∀ c : C, AllowedImbalance
      (colorPhaseImbalance S σ color c)) :
    Set.InjOn color (S : Set V) := by
  intro u hu v hv hcolor
  by_contra huv
  let F : Finset V := S.filter (fun w => color w = color u)
  have huF : u ∈ F := by
    simp [F, hu]
  have hvF : v ∈ F := by
    simp [F, hv, hcolor]
  have hpair : ({u, v} : Finset V) ⊆ F := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact huF
    · exact hvF
  have hcardpair : ({u, v} : Finset V).card = 2 := by
    simp [huv]
  have hcard : 2 ≤ F.card := by
    rw [← hcardpair]
    exact Finset.card_le_card hpair
  have hsame : ∀ w ∈ F, σ w = σ u := by
    intro w hw
    have hwS : w ∈ S := by
      simpa [F] using hw
    have hwcolor : color w = color u := by
      simpa [F] using hw
    exact sign_eq_of_same_color hproper hwS hu hwcolor
  have hsum :
      colorPhaseImbalance S σ color (color u) =
        (F.card : ℤ) * (σ u).value := by
    unfold colorPhaseImbalance
    change (∑ w ∈ F, (σ w).value) = (F.card : ℤ) * (σ u).value
    calc
      (∑ w ∈ F, (σ w).value) = ∑ w ∈ F, (σ u).value := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [hsame w hw]
      _ = (F.card : ℤ) * (σ u).value := by
        simp
  have ha := hallowed (color u)
  rw [hsum] at ha
  cases hσ : σ u with
  | pos =>
      simp [FourierSign.value, hσ, AllowedImbalance] at ha
      omega
  | neg =>
      simp [FourierSign.value, hσ, AllowedImbalance] at ha
      omega

/-- Every phase-surviving opposition-colored support has no repeated color. -/
theorem surviving_support_pair_distinct
    {S : Finset V} {σ : V → FourierSign} {color : V → C}
    (hproper : ProperForOpposition S σ color)
    (hallowed : ∀ c : C, AllowedImbalance
      (colorPhaseImbalance S σ color c))
    {u v : V} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    color u ≠ color v := by
  intro hcolor
  exact huv (surviving_support_color_injective hproper hallowed hu hv hcolor)

end

end LonelyRunner.CorrelatedAmplitude

import H0mework.Versions.AE.Physics.Bell.ReadoutDetectorFiber

/-!
# Faithful realization of a source effect from independently generated atomic responses

A pulse model supplies two ionization responses in its bright/dark basis.  These primitive
responses construct an atomic effect at any lawful XZ control axis.  A supplied source effect
generates the axis and detector rates needed to realize it; two native spectral inequalities
are exactly the feasibility test.  The construction transports an existing source effect,
and does not turn that target effect into an atomic prediction.  Entire response boxes use
one monotone worst corner, and distinct feasible response pairs give distinct atomic effects
with the same reported source law.
-/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutPulseRealization

open ReadoutDetectorFiber

noncomputable section

/-- Two independently generated ionization probabilities, with the raw bright/dark order. -/
@[ext] structure Spectrum where
  bright : ℝ
  dark : ℝ
  dark_nonnegative : 0 ≤ dark
  ordered : dark < bright
  bright_le_one : bright ≤ 1

def Spectrum.gap (spectrum : Spectrum) : ℝ := spectrum.bright - spectrum.dark

theorem Spectrum.gap_positive (spectrum : Spectrum) : 0 < spectrum.gap :=
  sub_pos.mpr spectrum.ordered

/-- A channel is only the existing compact-effect constructor for this atomic spectrum. -/
def Spectrum.channel (spectrum : Spectrum) : BinaryReadoutChannel where
  error0 := 1 - spectrum.bright
  error1 := spectrum.dark
  error0_nonnegative := sub_nonneg.mpr spectrum.bright_le_one
  error0_le_one := by linarith only [spectrum.dark_nonnegative, spectrum.ordered]
  error1_nonnegative := spectrum.dark_nonnegative
  error1_le_one := spectrum.ordered.le.trans spectrum.bright_le_one

/-- Forward atomic effect from primitive pulse responses and a control axis. -/
def atomicEffect (spectrum : Spectrum) (axis : Axis) : CompactReadoutEffect :=
  CompactReadoutEffect.ofChannel spectrum.channel axis

theorem atomic_effect_coordinates (spectrum : Spectrum) (axis : Axis) :
    (atomicEffect spectrum axis).mu = spectrum.bright + spectrum.dark - 1 ∧
    (atomicEffect spectrum axis).u = spectrum.gap * axis.x ∧
    (atomicEffect spectrum axis).z = spectrum.gap * axis.z := by
  simp only [atomicEffect, CompactReadoutEffect.ofChannel, Spectrum.channel,
    BinaryReadoutChannel.bias, BinaryReadoutChannel.gain, Spectrum.gap]
  constructor
  · ring
  · constructor <;> ring

theorem atomic_effect_gain (spectrum : Spectrum) (axis : Axis) :
    (atomicEffect spectrum axis).gain = spectrum.gap := by
  rw [atomicEffect, CompactReadoutEffect.gain_of_channel]
  have channel_gain : spectrum.channel.gain = spectrum.gap := by
    simp only [Spectrum.channel, BinaryReadoutChannel.gain, Spectrum.gap]
    ring
  rw [channel_gain, abs_of_pos spectrum.gap_positive]

theorem atomic_effect_spectrum (spectrum : Spectrum) (axis : Axis) :
    maxAtomic (atomicEffect spectrum axis) = spectrum.bright ∧
    (1 + (atomicEffect spectrum axis).mu - (atomicEffect spectrum axis).gain) / 2 =
      spectrum.dark := by
  simp only [maxAtomic]
  rw [atomic_effect_gain, (atomic_effect_coordinates spectrum axis).1]
  simp only [Spectrum.gap]
  constructor <;> ring

/-- The source coordinates generate the unique oriented axis used by this realizer. -/
def realizationAxis (effect : CompactReadoutEffect) (positive : 0 < effect.gain) : Axis where
  x := -effect.u / effect.gain
  z := -effect.z / effect.gain
  unit := by
    field_simp [ne_of_gt positive]
    nlinarith only [effect.gain_sq]

def factor (effect : CompactReadoutEffect) (spectrum : Spectrum) : ℝ :=
  effect.gain / spectrum.gap

def background (effect : CompactReadoutEffect) (spectrum : Spectrum) : ℝ :=
  (1 - effect.mu - factor effect spectrum * (spectrum.bright + spectrum.dark)) / 2

/-- A native spectral test; no completed realization or output probability table is an input. -/
structure Feasible (effect : CompactReadoutEffect) (spectrum : Spectrum) : Prop where
  background_slack : effect.gain * (spectrum.bright + spectrum.dark) ≤
    (1 - effect.mu) * spectrum.gap
  detector_slack : effect.gain * (2 - spectrum.bright - spectrum.dark) ≤
    (1 + effect.mu) * spectrum.gap

theorem factor_gap (effect : CompactReadoutEffect) (spectrum : Spectrum) :
    factor effect spectrum * spectrum.gap = effect.gain := by
  simp only [factor]
  exact div_mul_cancel₀ _ (ne_of_gt spectrum.gap_positive)

theorem factor_positive (effect : CompactReadoutEffect) (spectrum : Spectrum)
    (positive : 0 < effect.gain) : 0 < factor effect spectrum :=
  div_pos positive spectrum.gap_positive

/-- The spectral test is exactly physical legality of the generated detector rates. -/
theorem feasible_iff_rates (effect : CompactReadoutEffect) (spectrum : Spectrum) :
    Feasible effect spectrum ↔ Rates (background effect spectrum) (factor effect spectrum) := by
  have gap := spectrum.gap_positive
  have nonnegative : 0 ≤ factor effect spectrum := div_nonneg effect.gain_nonnegative gap.le
  have first : factor effect spectrum * (spectrum.bright + spectrum.dark) ≤ 1 - effect.mu ↔
      effect.gain * (spectrum.bright + spectrum.dark) ≤ (1 - effect.mu) * spectrum.gap := by
    rw [factor, div_mul_eq_mul_div]
    exact div_le_iff₀ gap
  have second : factor effect spectrum * (2 - spectrum.bright - spectrum.dark) ≤ 1 + effect.mu ↔
      effect.gain * (2 - spectrum.bright - spectrum.dark) ≤ (1 + effect.mu) * spectrum.gap := by
    rw [factor, div_mul_eq_mul_div]
    exact div_le_iff₀ gap
  constructor
  · intro feasible
    have first_bound := first.mpr feasible.background_slack
    have second_bound := second.mpr feasible.detector_slack
    refine ⟨?_, nonnegative, ?_⟩
    · simp only [background]
      linarith only [first_bound]
    · simp only [background]
      nlinarith only [second_bound]
  · intro rates
    constructor
    · apply first.mp
      have bound := rates.background_nonnegative
      simp only [background] at bound
      linarith only [bound]
    · apply second.mp
      have bound := rates.total_le_one
      simp only [background] at bound
      nlinarith only [bound]

theorem realizationRates (effect : CompactReadoutEffect) (spectrum : Spectrum)
    (feasible : Feasible effect spectrum) :
    Rates (background effect spectrum) (factor effect spectrum) :=
  (feasible_iff_rates effect spectrum).mp feasible

theorem realization_background_lt_one (effect : CompactReadoutEffect) (spectrum : Spectrum)
    (positive : 0 < effect.gain) (feasible : Feasible effect spectrum) :
    background effect spectrum < 1 := by
  have rates := realizationRates effect spectrum feasible
  have factor := factor_positive effect spectrum positive
  linarith only [rates.total_le_one, factor]

theorem realization_efficiency (effect : CompactReadoutEffect) (spectrum : Spectrum)
    (positive : 0 < effect.gain) (feasible : Feasible effect spectrum) :
    0 < efficiency (background effect spectrum) (factor effect spectrum) ∧
      efficiency (background effect spectrum) (factor effect spectrum) ≤ 1 := by
  have rates := realizationRates effect spectrum feasible
  have background := realization_background_lt_one effect spectrum positive feasible
  have denominator : 0 < 1 - ReadoutPulseRealization.background effect spectrum := by
    linarith only [background]
  exact ⟨div_pos (factor_positive effect spectrum positive) denominator,
    (efficiency_bounds _ _ rates background).2⟩

/-- The primitive pulse spectrum and generated axis faithfully realize the given source effect. -/
theorem pulse_realizes (effect : CompactReadoutEffect) (spectrum : Spectrum)
    (positive : 0 < effect.gain) :
    Realizes effect (background effect spectrum) (factor effect spectrum)
      (atomicEffect spectrum (realizationAxis effect positive)) := by
  have coordinates := atomic_effect_coordinates spectrum (realizationAxis effect positive)
  simp only [Realizes]
  constructor
  · rw [coordinates.1]
    simp only [background]
    ring
  · constructor
    · rw [coordinates.2.1]
      simp only [realizationAxis, factor]
      field_simp [ne_of_gt positive, ne_of_gt spectrum.gap_positive]
    · rw [coordinates.2.2]
      simp only [realizationAxis, factor]
      field_simp [ne_of_gt positive, ne_of_gt spectrum.gap_positive]

theorem feasible_gap_lower (effect : CompactReadoutEffect) (spectrum : Spectrum)
    (feasible : Feasible effect spectrum) : effect.gain ≤ spectrum.gap := by
  nlinarith only [feasible.background_slack, feasible.detector_slack]

def realizedEffect (effect : CompactReadoutEffect) (spectrum : Spectrum)
    (positive : 0 < effect.gain) (feasible : Feasible effect spectrum) : CompactReadoutEffect :=
  detectorEffect (atomicEffect spectrum (realizationAxis effect positive))
    (background effect spectrum) (factor effect spectrum) (realizationRates effect spectrum feasible)

/-- Exact inverse fidelity of the realizer; the source effect remains an explicit target. -/
theorem realized_effect_eq (effect : CompactReadoutEffect) (spectrum : Spectrum)
    (positive : 0 < effect.gain) (feasible : Feasible effect spectrum) :
    realizedEffect effect spectrum positive feasible = effect := by
  have identity := pulse_realizes effect spectrum positive
  apply CompactReadoutEffect.ext
  · exact identity.1.symm
  · exact identity.2.1.symm
  · exact identity.2.2.symm

/-- The entire primitive response box is feasible when its worst corner is feasible. -/
theorem feasible_monotone (effect : CompactReadoutEffect) (worst actual : Spectrum)
    (feasible : Feasible effect worst) (bright : worst.bright ≤ actual.bright)
    (dark : actual.dark ≤ worst.dark) : Feasible effect actual := by
  have m_bright := mul_nonneg (show 0 ≤ 1 - effect.mu - effect.gain by
      linarith only [effect.gain_le_minus]) (sub_nonneg.mpr bright)
  have M_dark := mul_nonneg (show 0 ≤ 1 - effect.mu + effect.gain by
      linarith only [effect.mu_upper, effect.gain_nonnegative]) (sub_nonneg.mpr dark)
  have plus_bright := mul_nonneg (show 0 ≤ 1 + effect.mu + effect.gain by
      linarith only [effect.mu_lower, effect.gain_nonnegative]) (sub_nonneg.mpr bright)
  have plus_dark := mul_nonneg (show 0 ≤ 1 + effect.mu - effect.gain by
      linarith only [effect.gain_le_plus]) (sub_nonneg.mpr dark)
  have first := feasible.background_slack
  have second := feasible.detector_slack
  simp only [Spectrum.gap] at first second
  constructor
  · simp only [Spectrum.gap]
    nlinarith only [first, m_bright, M_dark]
  · simp only [Spectrum.gap]
    nlinarith only [second, plus_bright, plus_dark]

/-- Rational response intervals can use squared source coordinates without approximating gain. -/
theorem feasible_iff_squared (effect : CompactReadoutEffect) (spectrum : Spectrum) :
    Feasible effect spectrum ↔
      (effect.u ^ 2 + effect.z ^ 2) * (spectrum.bright + spectrum.dark) ^ 2 ≤
        (1 - effect.mu) ^ 2 * spectrum.gap ^ 2 ∧
      (effect.u ^ 2 + effect.z ^ 2) * (2 - spectrum.bright - spectrum.dark) ^ 2 ≤
        (1 + effect.mu) ^ 2 * spectrum.gap ^ 2 := by
  have sum_nonnegative : 0 ≤ spectrum.bright + spectrum.dark := by
    linarith only [spectrum.dark_nonnegative, spectrum.ordered]
  have sum_le_two : 0 ≤ 2 - spectrum.bright - spectrum.dark := by
    linarith only [spectrum.bright_le_one, spectrum.ordered]
  have minus_nonnegative : 0 ≤ 1 - effect.mu := sub_nonneg.mpr effect.mu_upper
  have plus_nonnegative : 0 ≤ 1 + effect.mu := by linarith only [effect.mu_lower]
  have first := sq_le_sq₀ (mul_nonneg effect.gain_nonnegative sum_nonnegative)
    (mul_nonneg minus_nonnegative spectrum.gap_positive.le)
  have second := sq_le_sq₀ (mul_nonneg effect.gain_nonnegative sum_le_two)
    (mul_nonneg plus_nonnegative spectrum.gap_positive.le)
  simp only [mul_pow, effect.gain_sq] at first second
  constructor
  · intro feasible
    exact ⟨first.mpr feasible.background_slack, second.mpr feasible.detector_slack⟩
  · intro squared
    exact ⟨first.mp squared.1, second.mp squared.2⟩

theorem atomic_effect_injective (axis : Axis) {first second : Spectrum}
    (same : atomicEffect first axis = atomicEffect second axis) : first = second := by
  have upper := congrArg maxAtomic same
  have lower := congrArg (fun atom : CompactReadoutEffect => (1 + atom.mu - atom.gain) / 2) same
  rw [(atomic_effect_spectrum first axis).1, (atomic_effect_spectrum second axis).1] at upper
  rw [(atomic_effect_spectrum first axis).2, (atomic_effect_spectrum second axis).2] at lower
  exact Spectrum.ext upper lower

/-- Different feasible pulse responses realize the same source effect with different atoms. -/
theorem two_spectra_same_effect (effect : CompactReadoutEffect) (first second : Spectrum)
    (positive : 0 < effect.gain) (first_feasible : Feasible effect first)
    (second_feasible : Feasible effect second) (different : first ≠ second) :
    atomicEffect first (realizationAxis effect positive) ≠
      atomicEffect second (realizationAxis effect positive) ∧
    realizedEffect effect first positive first_feasible = effect ∧
      realizedEffect effect second positive second_feasible = effect := by
  refine ⟨?_, realized_effect_eq effect first positive first_feasible,
    realized_effect_eq effect second positive second_feasible⟩
  intro same
  exact different (atomic_effect_injective _ same)

end
end SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutPulseRealization

import H0mework.NavierStokes.Galerkin.CriticalSerrinBudget

/-!
# Cutoff-independent high-frequency tail absorption

The critical absorption budget controls the weighted vorticity mass
`Z = sum |k|^2 |omega_k|^2`.  Consequently every frequency tail above a
positive squared-frequency threshold `R` satisfies

```text
A_theta * R * integral tail_R <= H(a) - H(b).
```

This is the spatial compactness half of the Galerkin-limit gate.  The bound
is uniform in the finite Fourier inventory and is proved on every actual
physical Galerkin interval; no cutoff, maximum frequency, tail budget, or
compactness certificate is a premise.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalHighFrequencyTail

open scoped BigOperators Topology ENNReal

open Set
open MeasureTheory
open Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalSerrinBudget
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalTimeConsumer
open ThreeDimensionalVorticityCoefficientGeneratedPathStretchingBudget
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption

noncomputable section

/-- Unweighted coefficient mass strictly above one squared-frequency
threshold. -/
def finiteStateVorticityHighFrequencyTailMass
    (modes : Finset IntegerWavevector)
    (threshold : ℝ)
    (state : ComplexVorticityHilbertState) : ℝ :=
  ∑ wave ∈ modes.filter
      (fun wave => threshold < integerWaveNormSq wave),
    complexCoordinateAmplitudeSq (state wave)

theorem finiteStateVorticityHighFrequencyTailMass_nonneg
    (modes : Finset IntegerWavevector)
    (threshold : ℝ)
    (state : ComplexVorticityHilbertState) :
    0 ≤ finiteStateVorticityHighFrequencyTailMass
      modes threshold state := by
  exact Finset.sum_nonneg fun wave waveMem =>
    complexCoordinateAmplitudeSq_nonneg (state wave)

/-- Multiplying a high-frequency tail by its threshold is bounded by the
complete vorticity-gradient mass, with constant one. -/
theorem threshold_mul_highFrequencyTailMass_le_enstrophyMass
    (modes : Finset IntegerWavevector)
    (threshold : ℝ)
    (state : ComplexVorticityHilbertState) :
    threshold *
        finiteStateVorticityHighFrequencyTailMass
          modes threshold state ≤
      finiteStateVorticityEnstrophyMass modes state := by
  unfold finiteStateVorticityHighFrequencyTailMass
    finiteStateVorticityEnstrophyMass
  rw [Finset.mul_sum]
  calc
    (∑ wave ∈ modes.filter
        (fun wave => threshold < integerWaveNormSq wave),
      threshold * complexCoordinateAmplitudeSq (state wave)) ≤
        ∑ wave ∈ modes.filter
          (fun wave => threshold < integerWaveNormSq wave),
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (state wave) := by
      apply Finset.sum_le_sum
      intro wave waveMem
      exact mul_le_mul_of_nonneg_right
        (Finset.mem_filter.mp waveMem).2.le
        (complexCoordinateAmplitudeSq_nonneg (state wave))
    _ ≤
        ∑ wave ∈ modes,
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (state wave) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun wave waveMem waveNotMem =>
          mul_nonneg (integerWaveNormSq_nonneg wave)
            (complexCoordinateAmplitudeSq_nonneg (state wave)))

private theorem continuousAt_finset_sum
    {α : Type}
    [DecidableEq α]
    (indices : Finset α)
    (summand : α → ℝ → ℝ)
    (t : ℝ)
    (continuousSummand :
      ∀ index ∈ indices, ContinuousAt (summand index) t) :
    ContinuousAt (fun time => ∑ index ∈ indices, summand index time) t := by
  induction indices using Finset.induction_on with
  | empty =>
      simpa using
        (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t)
  | @insert index indices indexNotMem inductionHypothesis =>
      simp only [Finset.sum_insert indexNotMem]
      exact
        (continuousSummand index (by simp)).add
          (inductionHypothesis fun later laterMem =>
            continuousSummand later (by simp [laterMem]))

/-- The finite high-frequency tail mass is continuous along every actual
differentiable coefficient trajectory. -/
theorem finiteStateVorticityHighFrequencyTailMass_continuousAt_of_hasDerivAt
    (modes : Finset IntegerWavevector)
    (threshold : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (tangent : ComplexVorticityHilbertState)
    (evolves : HasDerivAt trajectory tangent t) :
    ContinuousAt
      (fun time =>
        finiteStateVorticityHighFrequencyTailMass
          modes threshold (trajectory time)) t := by
  unfold finiteStateVorticityHighFrequencyTailMass
  exact continuousAt_finset_sum
    (modes.filter (fun wave => threshold < integerWaveNormSq wave))
    (fun wave time =>
      complexCoordinateAmplitudeSq (trajectory time wave)) t
    (fun wave _ =>
      complexCoordinateAmplitudeSq_continuousAt_of_hasDerivAt
        trajectory t tangent wave evolves)

/-- Integral form of the constant-one tail estimate on an actual finite
interval. -/
theorem threshold_mul_integral_highFrequencyTailMass_le_integral_enstrophyMass
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (threshold : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (a b : ℝ)
    (hab : a ≤ b)
    (evolves :
      ∀ t ∈ Icc a b,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν (trajectory t)) t) :
    threshold *
          (∫ t in a..b,
            finiteStateVorticityHighFrequencyTailMass
              modes threshold (trajectory t)) ≤
        ∫ t in a..b,
          finiteStateVorticityEnstrophyMass
            modes (trajectory t) := by
  have tailContinuousOn :
      ContinuousOn
        (fun t =>
          finiteStateVorticityHighFrequencyTailMass
            modes threshold (trajectory t))
        (Icc a b) := by
    intro t tMem
    exact
      (finiteStateVorticityHighFrequencyTailMass_continuousAt_of_hasDerivAt
        modes threshold trajectory t
          (finiteStateVorticityGenerator modes ν (trajectory t))
          (evolves t tMem)).continuousWithinAt
  have enstrophyContinuousOn :
      ContinuousOn
        (fun t =>
          finiteStateVorticityEnstrophyMass modes (trajectory t))
        (Icc a b) := by
    intro t tMem
    exact
      (finiteStateVorticityEnstrophyMass_continuousAt_of_hasDerivAt
        modes trajectory t
          (finiteStateVorticityGenerator modes ν (trajectory t))
          (evolves t tMem)).continuousWithinAt
  have tailIntegrable :
      IntervalIntegrable
        (fun t =>
          finiteStateVorticityHighFrequencyTailMass
            modes threshold (trajectory t))
        volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab tailContinuousOn
  have enstrophyIntegrable :
      IntervalIntegrable
        (fun t =>
          finiteStateVorticityEnstrophyMass modes (trajectory t))
        volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab enstrophyContinuousOn
  have scaledTailIntegrable :
      IntervalIntegrable
        (fun t =>
          threshold *
            finiteStateVorticityHighFrequencyTailMass
              modes threshold (trajectory t))
        volume a b :=
    tailIntegrable.const_mul threshold
  have integrated :=
    intervalIntegral.integral_mono_on
      hab scaledTailIntegrable enstrophyIntegrable
      (fun t _ =>
        threshold_mul_highFrequencyTailMass_le_enstrophyMass
          modes threshold (trajectory t))
  simpa only [intervalIntegral.integral_const_mul] using integrated

/-- A strict critical margin generates a cutoff-independent decay estimate
for every high-frequency tail on every actual physical Galerkin interval. -/
theorem finiteStateVorticity_criticalHighFrequencyTail_on_Icc
    (modes : Finset IntegerWavevector)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : Viscosity)
    (θ threshold : ℝ)
    (θLtOne : θ < 1)
    (thresholdPos : 0 < threshold)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (a b : ℝ)
    (hab : a ≤ b)
    (evolves :
      ∀ t ∈ Icc a b,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν.coeff (trajectory t)) t)
    (reality :
      ∀ t ∈ Icc a b,
        FiniteStateFourierReality (trajectory t))
    (transverse :
      ∀ t ∈ Icc a b,
        ∀ wave ∈ modes,
          complexWavevector wave ⬝ᵥ trajectory t wave = 0)
    (initialMargin :
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            modes (trajectory a) ≤
        θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2) :
    criticalEnstrophyAbsorptionCoefficient θ ν * threshold *
          (∫ t in a..b,
            finiteStateVorticityHighFrequencyTailMass
              modes threshold (trajectory t)) ≤
        finiteStateVorticityHalfEnstrophy
            modes (trajectory a) -
          finiteStateVorticityHalfEnstrophy
            modes (trajectory b) ∧
      (∫ t in a..b,
          finiteStateVorticityHighFrequencyTailMass
            modes threshold (trajectory t)) ≤
        finiteStateVorticityHalfEnstrophy
              modes (trajectory a) /
          (criticalEnstrophyAbsorptionCoefficient θ ν * threshold) := by
  obtain
      ⟨_pointwise, integratedAbsorption,
        _serrinAbsorption, _criticalNorm⟩ :=
    finiteStateVorticity_criticalSerrinBudget_on_Icc
      modes negClosed ν θ θLtOne trajectory a b hab
      evolves reality transverse initialMargin
  have tailIntegralLe :
      threshold *
            (∫ t in a..b,
              finiteStateVorticityHighFrequencyTailMass
                modes threshold (trajectory t)) ≤
          ∫ t in a..b,
            finiteStateVorticityEnstrophyMass
              modes (trajectory t) := by
    apply
      threshold_mul_integral_highFrequencyTailMass_le_integral_enstrophyMass
        modes ν.coeff threshold trajectory a b hab evolves
  have absorptionPos :
      0 < criticalEnstrophyAbsorptionCoefficient θ ν :=
    criticalEnstrophyAbsorptionCoefficient_pos θ θLtOne ν
  have absorbedTail :
      criticalEnstrophyAbsorptionCoefficient θ ν * threshold *
            (∫ t in a..b,
              finiteStateVorticityHighFrequencyTailMass
                modes threshold (trajectory t)) ≤
          finiteStateVorticityHalfEnstrophy
              modes (trajectory a) -
            finiteStateVorticityHalfEnstrophy
              modes (trajectory b) := by
    calc
      criticalEnstrophyAbsorptionCoefficient θ ν * threshold *
            (∫ t in a..b,
              finiteStateVorticityHighFrequencyTailMass
                modes threshold (trajectory t)) =
          criticalEnstrophyAbsorptionCoefficient θ ν *
            (threshold *
              ∫ t in a..b,
                finiteStateVorticityHighFrequencyTailMass
                  modes threshold (trajectory t)) := by ring
      _ ≤
          criticalEnstrophyAbsorptionCoefficient θ ν *
            ∫ t in a..b,
              finiteStateVorticityEnstrophyMass
                modes (trajectory t) :=
        mul_le_mul_of_nonneg_left tailIntegralLe absorptionPos.le
      _ ≤
          finiteStateVorticityHalfEnstrophy
              modes (trajectory a) -
            finiteStateVorticityHalfEnstrophy
              modes (trajectory b) := integratedAbsorption
  have terminalNonneg :
      0 ≤ finiteStateVorticityHalfEnstrophy
        modes (trajectory b) :=
    finiteStateVorticityHalfEnstrophy_nonneg modes _
  have withoutTerminal :
      criticalEnstrophyAbsorptionCoefficient θ ν * threshold *
            (∫ t in a..b,
              finiteStateVorticityHighFrequencyTailMass
                modes threshold (trajectory t)) ≤
          finiteStateVorticityHalfEnstrophy
            modes (trajectory a) :=
    absorbedTail.trans (sub_le_self _ terminalNonneg)
  have denominatorPos :
      0 < criticalEnstrophyAbsorptionCoefficient θ ν * threshold :=
    mul_pos absorptionPos thresholdPos
  refine ⟨absorbedTail, ?_⟩
  exact (le_div_iff₀ denominatorPos).2 (by
    simpa [mul_assoc, mul_comm, mul_left_comm] using withoutTerminal)

end

end ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalHighFrequencyTail
end NavierStokes
end SaturationMonoid

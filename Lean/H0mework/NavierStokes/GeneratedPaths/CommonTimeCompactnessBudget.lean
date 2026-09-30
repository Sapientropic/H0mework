import H0mework.NavierStokes.Galerkin.CommonTimeExistence
import H0mework.NavierStokes.Galerkin.CriticalHighFrequencyTail
import H0mework.NavierStokes.Galerkin.NegativeSobolevTimeBudget

/-!
# Common-time compactness budgets for generated Galerkin paths

The fixed-mode common-time producer supplies an actual physical Galerkin
trajectory on every requested finite interval.  This module consumes that
same trajectory with the cutoff-independent critical estimates:

```text
Aθ ∫ Z ≤ H(0) - H(T),
∫ M² ≤ K₃ H(0) / Aθ,
∫ tail_R ≤ H(0) / (Aθ R),
∫ ‖∂ₜω‖_{H⁻¹}²
  ≤ (4 K₃ Y(0)² + ν² (2π)² Y(0)) / Aθ.
```

All rows are returned in one dependent receipt tied to the same generated
path, initial source, requested interval, and actual trajectory.  No
trajectory, cutoff, largest frequency, target-time coverage, or analytic
budget occurs in the producer mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedPathCommonTimeCompactnessBudget

open scoped BigOperators Matrix Topology Interval ENNReal

open Set
open MeasureTheory
open Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalTimeConsumer
open ThreeDimensionalVorticityCoefficientGeneratedPathStretchingBudget
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalSerrinBudget
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalHighFrequencyTail
open ThreeDimensionalVorticityCoefficientFiniteGalerkinNegativeSobolevTimeBudget
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCommonTimeExistence

noncomputable section

/-! ## Generic time-derivative budget on one actual interval -/

private theorem continuousAt_finset_sum_negativeOne
    {α E : Type}
    [DecidableEq α]
    [TopologicalSpace E]
    [AddCommMonoid E]
    [ContinuousAdd E]
    (indices : Finset α)
    (summand : α → ℝ → E)
    (t : ℝ)
    (continuousSummand :
      ∀ index ∈ indices, ContinuousAt (summand index) t) :
    ContinuousAt (fun time => ∑ index ∈ indices, summand index time) t := by
  induction indices using Finset.induction_on with
  | empty =>
      simpa using
        (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : E)) t)
  | @insert index indices indexNotMem inductionHypothesis =>
      simp only [Finset.sum_insert indexNotMem]
      exact
        (continuousSummand index (by simp)).add
          (inductionHypothesis fun later laterMem =>
            continuousSummand later (by simp [laterMem]))

private theorem
    finiteStateVorticityGenerator_negativeOneMass_continuousAt
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (evolves :
      HasDerivAt trajectory
        (finiteStateVorticityGenerator
          modes ν (trajectory t)) t) :
    ContinuousAt
      (fun time =>
        finiteStateVorticityNegativeOneMass modes
          (finiteStateVorticityGenerator
            modes ν (trajectory time))) t := by
  unfold finiteStateVorticityNegativeOneMass
  exact continuousAt_finset_sum_negativeOne modes
    (fun output time =>
      if output = 0 then 0
      else
        ‖finiteStateVorticityGenerator
            modes ν (trajectory time) output‖ ^ 2 /
          integerWaveViscousMultiplier output) t
    (fun output _ => by
      by_cases outputZero : output = 0
      · simp only [if_pos outputZero]
        exact continuousAt_const
      · simp only [if_neg outputZero]
        have rowContinuous :
            ContinuousAt
              (fun time =>
                finiteStateVorticityGenerator
                  modes ν (trajectory time) output) t := by
          exact
            (((complexVorticityEvaluation_contDiff output).continuous.comp
              (finiteStateVorticityGenerator_contDiff
                modes ν).continuous).continuousAt.comp
                  evolves.continuousAt)
        exact (rowContinuous.norm.pow 2).div_const _)

/-- The actual Galerkin update has a cutoff-independent cumulative
`L²_t H⁻¹` budget on every physical interval carrying a strict critical
margin.  This is a readout of the displayed trajectory, not an existence
theorem. -/
theorem finiteStateVorticity_negativeOneTimeBudget_on_Icc
    (modes : Finset IntegerWavevector)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : Viscosity)
    (θ : ℝ)
    (θLtOne : θ < 1)
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
    (∫ t in a..b,
      finiteStateVorticityNegativeOneMass modes
        (finiteStateVorticityGenerator
          modes ν.coeff (trajectory t))) ≤
      (4 * criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
                modes (trajectory a) ^ 2 +
          ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
            finiteStateVorticityCoefficientEnstrophy
              modes (trajectory a)) /
        criticalEnstrophyAbsorptionCoefficient θ ν := by
  obtain
      ⟨pointwiseConclusion, integratedEnstrophy,
        _serrinAbsorption, serrinBound⟩ :=
    finiteStateVorticity_criticalSerrinBudget_on_Icc
      modes negClosed ν θ θLtOne trajectory a b hab
      evolves reality transverse initialMargin
  have generatorMassContinuousOn :
      ContinuousOn
        (fun t =>
          finiteStateVorticityNegativeOneMass modes
            (finiteStateVorticityGenerator
              modes ν.coeff (trajectory t)))
        (Icc a b) := by
    intro t tMem
    exact
      (finiteStateVorticityGenerator_negativeOneMass_continuousAt
        modes ν.coeff trajectory t
          (evolves t tMem)).continuousWithinAt
  have majorantContinuousOn :
      ContinuousOn
        (fun t =>
          finiteStateVelocityMajorant modes (trajectory t) ^ 2)
        (Icc a b) := by
    intro t tMem
    exact
      ((finiteStateVelocityMajorant_continuousAt_of_hasDerivAt
        modes trajectory t
        (finiteStateVorticityGenerator
          modes ν.coeff (trajectory t))
        (evolves t tMem)).pow 2).continuousWithinAt
  have enstrophyMassContinuousOn :
      ContinuousOn
        (fun t =>
          finiteStateVorticityEnstrophyMass modes (trajectory t))
        (Icc a b) := by
    intro t tMem
    exact
      (finiteStateVorticityEnstrophyMass_continuousAt_of_hasDerivAt
        modes trajectory t
        (finiteStateVorticityGenerator
          modes ν.coeff (trajectory t))
        (evolves t tMem)).continuousWithinAt
  have generatorMassIntegrable :
      IntervalIntegrable
        (fun t =>
          finiteStateVorticityNegativeOneMass modes
            (finiteStateVorticityGenerator
              modes ν.coeff (trajectory t)))
        volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc
      hab generatorMassContinuousOn
  have majorantIntegrable :
      IntervalIntegrable
        (fun t =>
          finiteStateVelocityMajorant modes (trajectory t) ^ 2)
        volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc
      hab majorantContinuousOn
  have enstrophyMassIntegrable :
      IntervalIntegrable
        (fun t =>
          finiteStateVorticityEnstrophyMass modes (trajectory t))
        volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc
      hab enstrophyMassContinuousOn
  have initialEnstrophyNonneg :
      0 ≤
        finiteStateVorticityCoefficientEnstrophy
          modes (trajectory a) := by
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun _ _ =>
      complexCoordinateAmplitudeSq_nonneg _
  have pointwiseGeneratorBound :
      ∀ t ∈ Icc a b,
        finiteStateVorticityNegativeOneMass modes
            (finiteStateVorticityGenerator
              modes ν.coeff (trajectory t)) ≤
          8 *
                finiteStateVorticityCoefficientEnstrophy
                  modes (trajectory a) *
                finiteStateVelocityMajorant modes (trajectory t) ^ 2 +
            2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
              finiteStateVorticityEnstrophyMass
                modes (trajectory t) := by
    intro t tMem
    have currentEnstrophyLe :
        finiteStateVorticityCoefficientEnstrophy
              modes (trajectory t) ≤
          finiteStateVorticityCoefficientEnstrophy
            modes (trajectory a) := by
      have halfLe := (pointwiseConclusion t tMem).1
      unfold finiteStateVorticityHalfEnstrophy at halfLe
      linarith
    have nonlinearLe :
        8 * finiteStateVelocityMajorant modes (trajectory t) ^ 2 *
              finiteStateVorticityCoefficientEnstrophy
                modes (trajectory t) ≤
          8 * finiteStateVelocityMajorant modes (trajectory t) ^ 2 *
              finiteStateVorticityCoefficientEnstrophy
                modes (trajectory a) :=
      mul_le_mul_of_nonneg_left currentEnstrophyLe
        (mul_nonneg (by norm_num) (sq_nonneg _))
    calc
      finiteStateVorticityNegativeOneMass modes
          (finiteStateVorticityGenerator
            modes ν.coeff (trajectory t)) ≤
        8 * finiteStateVelocityMajorant modes (trajectory t) ^ 2 *
              finiteStateVorticityCoefficientEnstrophy
                modes (trajectory t) +
          2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass
              modes (trajectory t) :=
        finiteStateVorticityGenerator_negativeOneMass_le
          modes ν.coeff (trajectory t)
          (fun wave waveMem =>
            transverse t tMem wave waveMem)
      _ ≤
        8 * finiteStateVelocityMajorant modes (trajectory t) ^ 2 *
              finiteStateVorticityCoefficientEnstrophy
                modes (trajectory a) +
          2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass
              modes (trajectory t) :=
        add_le_add_left nonlinearLe _
      _ =
        8 *
              finiteStateVorticityCoefficientEnstrophy
                modes (trajectory a) *
              finiteStateVelocityMajorant modes (trajectory t) ^ 2 +
          2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass
              modes (trajectory t) := by
        ring
  have rhsIntegrable :
      IntervalIntegrable
        (fun t =>
          8 *
                finiteStateVorticityCoefficientEnstrophy
                  modes (trajectory a) *
                finiteStateVelocityMajorant modes (trajectory t) ^ 2 +
            2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
              finiteStateVorticityEnstrophyMass
                modes (trajectory t))
        volume a b :=
    (majorantIntegrable.const_mul
      (8 *
        finiteStateVorticityCoefficientEnstrophy
          modes (trajectory a))).add
      (enstrophyMassIntegrable.const_mul
        (2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2))
  have integratedGeneratorBound :=
    intervalIntegral.integral_mono_on
      hab generatorMassIntegrable rhsIntegrable
      pointwiseGeneratorBound
  rw [intervalIntegral.integral_add
      (majorantIntegrable.const_mul
        (8 *
          finiteStateVorticityCoefficientEnstrophy
            modes (trajectory a)))
      (enstrophyMassIntegrable.const_mul
        (2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at integratedGeneratorBound
  have absorptionCoefficientPos :
      0 < criticalEnstrophyAbsorptionCoefficient θ ν :=
    criticalEnstrophyAbsorptionCoefficient_pos θ θLtOne ν
  have terminalHalfEnstrophyNonneg :
      0 ≤
        finiteStateVorticityHalfEnstrophy
          modes (trajectory b) :=
    finiteStateVorticityHalfEnstrophy_nonneg modes _
  have integratedEnstrophyWithoutTerminal :
      criticalEnstrophyAbsorptionCoefficient θ ν *
            (∫ t in a..b,
              finiteStateVorticityEnstrophyMass
                modes (trajectory t)) ≤
          finiteStateVorticityHalfEnstrophy
            modes (trajectory a) :=
    integratedEnstrophy.trans
      (sub_le_self _ terminalHalfEnstrophyNonneg)
  have enstrophyMassIntegralBound :
      (∫ t in a..b,
          finiteStateVorticityEnstrophyMass
            modes (trajectory t)) ≤
        finiteStateVorticityHalfEnstrophy
              modes (trajectory a) /
          criticalEnstrophyAbsorptionCoefficient θ ν := by
    exact
      (le_div_iff₀ absorptionCoefficientPos).2 (by
        simpa [mul_comm] using integratedEnstrophyWithoutTerminal)
  have integratedUpper :
      (∫ t in a..b,
          finiteStateVorticityNegativeOneMass modes
            (finiteStateVorticityGenerator
              modes ν.coeff (trajectory t))) ≤
        8 *
              finiteStateVorticityCoefficientEnstrophy
                modes (trajectory a) *
              (criticalEnstrophyLatticeConstant *
                    finiteStateVorticityHalfEnstrophy
                      modes (trajectory a) /
                  criticalEnstrophyAbsorptionCoefficient θ ν) +
          2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
              (finiteStateVorticityHalfEnstrophy
                    modes (trajectory a) /
                criticalEnstrophyAbsorptionCoefficient θ ν) := by
    exact integratedGeneratorBound.trans
      (add_le_add
        (mul_le_mul_of_nonneg_left serrinBound
          (mul_nonneg (by norm_num) initialEnstrophyNonneg))
        (mul_le_mul_of_nonneg_left enstrophyMassIntegralBound
          (mul_nonneg
            (mul_nonneg (by norm_num) (sq_nonneg _))
            (sq_nonneg _))))
  calc
    (∫ t in a..b,
      finiteStateVorticityNegativeOneMass modes
        (finiteStateVorticityGenerator
          modes ν.coeff (trajectory t))) ≤
        8 *
              finiteStateVorticityCoefficientEnstrophy
                modes (trajectory a) *
              (criticalEnstrophyLatticeConstant *
                    finiteStateVorticityHalfEnstrophy
                      modes (trajectory a) /
                  criticalEnstrophyAbsorptionCoefficient θ ν) +
          2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
              (finiteStateVorticityHalfEnstrophy
                    modes (trajectory a) /
                criticalEnstrophyAbsorptionCoefficient θ ν) :=
      integratedUpper
    _ =
      (4 * criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
                modes (trajectory a) ^ 2 +
          ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
            finiteStateVorticityCoefficientEnstrophy
              modes (trajectory a)) /
        criticalEnstrophyAbsorptionCoefficient θ ν := by
      unfold finiteStateVorticityHalfEnstrophy
      field_simp [ne_of_gt absorptionCoefficientPos]
      ring

/-! ## Source-generated common-time receipt -/

/-- One source-generated path, one requested time interval, and one actual
Galerkin trajectory carrying all cutoff-independent compactness budgets.

The dependent `arrival` index prevents downstream consumers from detaching
the analytic receipt from the exact generated path used to produce it. -/
structure GeneratedPathCommonTimeCompactnessBudget
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (ν : Viscosity)
    (θ requestedTime : ℝ) where
  trajectory : ℝ → ComplexVorticityHilbertState
  initial :
    trajectory 0 =
      generatedComplexVorticityState current
        (generatedSupport current)
  physicalProperties :
    ∀ t ∈ Icc (0 : ℝ) requestedTime,
      HasDerivAt trajectory
          (finiteStateVorticityGenerator
            (generatedSupport current) ν.coeff (trajectory t)) t ∧
        (∀ wave,
          wave ∉ generatedSupport current →
            trajectory t wave = 0) ∧
        (∀ wave,
          complexWavevector wave ⬝ᵥ trajectory t wave = 0) ∧
        FiniteStateFourierReality (trajectory t)
  criticalBarrier :
    ∀ t ∈ Icc (0 : ℝ) requestedTime,
      finiteStateVorticityHalfEnstrophy
          (generatedSupport current) (trajectory t) ≤
          finiteStateVorticityHalfEnstrophy
            (generatedSupport current) (trajectory 0) ∧
        finiteStateVorticityStretchingWork
              (generatedSupport current) (trajectory t) -
            ν.coeff * (2 * Real.pi) ^ 2 *
              finiteStateVorticityEnstrophyMass
                (generatedSupport current) (trajectory t) ≤
          -criticalEnstrophyAbsorptionCoefficient θ ν *
            finiteStateVorticityEnstrophyMass
              (generatedSupport current) (trajectory t)
  enstrophyAbsorption :
    criticalEnstrophyAbsorptionCoefficient θ ν *
          (∫ t in (0 : ℝ)..requestedTime,
            finiteStateVorticityEnstrophyMass
              (generatedSupport current) (trajectory t)) ≤
        finiteStateVorticityHalfEnstrophy
            (generatedSupport current) (trajectory 0) -
          finiteStateVorticityHalfEnstrophy
            (generatedSupport current) (trajectory requestedTime)
  serrinAbsorption :
    criticalEnstrophyAbsorptionCoefficient θ ν *
          (∫ t in (0 : ℝ)..requestedTime,
            finiteStateVelocityMajorant
              (generatedSupport current) (trajectory t) ^ 2) ≤
        criticalEnstrophyLatticeConstant *
          (finiteStateVorticityHalfEnstrophy
              (generatedSupport current) (trajectory 0) -
            finiteStateVorticityHalfEnstrophy
              (generatedSupport current) (trajectory requestedTime))
  serrinBound :
    (∫ t in (0 : ℝ)..requestedTime,
      finiteStateVelocityMajorant
        (generatedSupport current) (trajectory t) ^ 2) ≤
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityHalfEnstrophy
            (generatedSupport current) (trajectory 0) /
        criticalEnstrophyAbsorptionCoefficient θ ν
  highFrequencyTail :
    ∀ threshold : ℝ, 0 < threshold →
      (∫ t in (0 : ℝ)..requestedTime,
        finiteStateVorticityHighFrequencyTailMass
          (generatedSupport current) threshold (trajectory t)) ≤
        finiteStateVorticityHalfEnstrophy
              (generatedSupport current) (trajectory 0) /
          (criticalEnstrophyAbsorptionCoefficient θ ν * threshold)
  negativeOneTimeBudget :
    (∫ t in (0 : ℝ)..requestedTime,
      finiteStateVorticityNegativeOneMass
        (generatedSupport current)
        (finiteStateVorticityGenerator
          (generatedSupport current) ν.coeff (trajectory t))) ≤
      (4 * criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
                (generatedSupport current) (trajectory 0) ^ 2 +
          ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport current) (trajectory 0)) /
        criticalEnstrophyAbsorptionCoefficient θ ν

/-- An arbitrary generated finite scale path below a strict critical margin
produces, on every requested finite positive interval, one actual physical
Galerkin trajectory carrying the full cutoff-independent compactness
ledger.

The common interval is generated before any budget is read.  The target
time, cutoff inventory, trajectory, terminal state, and all analytic bounds
are absent from the premises except for the consumer-requested scalar
`requestedTime`. -/
noncomputable def
    generatedIntegerShellReachableCommonTimeCompactnessBudget
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (ν : Viscosity)
    (θ : ℝ)
    (θLtOne : θ < 1)
    (initialMargin :
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            (generatedSupport current)
            (generatedComplexVorticityState current
              (generatedSupport current)) ≤
        θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2)
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime) :
    GeneratedPathCommonTimeCompactnessBudget
      arrival ν θ requestedTime := by
  let modes := generatedSupport current
  let initialState :=
    generatedComplexVorticityState current modes
  have zeroNotMem : (0 : IntegerWavevector) ∉ modes := by
    exact zero_not_mem_generatedSupport current
  have negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes := by
    intro wave waveMem
    exact generatedSupport_waveNeg_mem current waveMem
  have supported :
      ∀ wave, wave ∉ modes → initialState wave = 0 := by
    intro wave waveNotMem
    simp [initialState, waveNotMem]
  have transverse :
      ∀ wave ∈ modes,
        complexWavevector wave ⬝ᵥ initialState wave = 0 := by
    intro wave waveMem
    simp only [initialState,
      generatedComplexVorticityState_apply, if_pos waveMem]
    exact generatedVorticityCoefficient_transverse current wave
  have reality :
      FiniteStateFourierReality initialState := by
    apply finiteStateFourierReality_of_reflection_fixed
      (fun {wave} waveMem =>
        generatedSupport_waveNeg_mem current waveMem)
      supported
    exact
      complexFourierRealityReflection_generatedSourceInitial current
  have thresholdNonneg :
      0 ≤ ν.coeff ^ 2 * (2 * Real.pi) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have criticalInitialSmall :
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            modes initialState ≤
        ν.coeff ^ 2 * (2 * Real.pi) ^ 2 := by
    have θThresholdLe :
        θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 ≤
          ν.coeff ^ 2 * (2 * Real.pi) ^ 2 := by
      simpa only [mul_assoc] using
        (mul_le_of_le_one_left thresholdNonneg θLtOne.le)
    exact initialMargin.trans θThresholdLe
  let generatedTrajectory :=
    exists_finitePhysicalTrajectory_on_Icc_of_criticalSmall
      modes zeroNotMem negClosed ν.coeff ν.coeff_pos
      initialState supported transverse reality
      criticalInitialSmall requestedTime requestedTimePos
  let trajectory := Classical.choose generatedTrajectory
  have generatedTrajectoryProperties :=
    Classical.choose_spec generatedTrajectory
  have initial := generatedTrajectoryProperties.1
  have physicalProperties := generatedTrajectoryProperties.2
  have evolves :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν.coeff (trajectory t)) t := by
    intro t tMem
    exact (physicalProperties t tMem).1
  have trajectoryReality :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        FiniteStateFourierReality (trajectory t) := by
    intro t tMem
    exact (physicalProperties t tMem).2.2.2
  have trajectoryTransverse :
      ∀ t ∈ Icc (0 : ℝ) requestedTime,
        ∀ wave ∈ modes,
          complexWavevector wave ⬝ᵥ trajectory t wave = 0 := by
    intro t tMem wave waveMem
    exact (physicalProperties t tMem).2.2.1 wave
  have initialMarginActual :
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            modes (trajectory 0) ≤
        θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 := by
    change
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            modes (Classical.choose generatedTrajectory 0) ≤
        θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2
    rw [initial]
    simpa [modes, initialState] using initialMargin
  obtain
      ⟨criticalBarrier, enstrophyAbsorption,
        serrinAbsorption, serrinBound⟩ :=
    finiteStateVorticity_criticalSerrinBudget_on_Icc
      modes negClosed ν θ θLtOne trajectory
      0 requestedTime requestedTimePos.le
      evolves trajectoryReality trajectoryTransverse
      initialMarginActual
  have highFrequencyTail :
      ∀ threshold : ℝ, 0 < threshold →
        (∫ t in (0 : ℝ)..requestedTime,
          finiteStateVorticityHighFrequencyTailMass
            modes threshold (trajectory t)) ≤
          finiteStateVorticityHalfEnstrophy
                modes (trajectory 0) /
            (criticalEnstrophyAbsorptionCoefficient θ ν * threshold) := by
    intro threshold thresholdPos
    exact
      (finiteStateVorticity_criticalHighFrequencyTail_on_Icc
        modes negClosed ν θ threshold θLtOne thresholdPos
        trajectory 0 requestedTime requestedTimePos.le
        evolves trajectoryReality trajectoryTransverse
        initialMarginActual).2
  have negativeOneTimeBudget :=
    finiteStateVorticity_negativeOneTimeBudget_on_Icc
      modes negClosed ν θ θLtOne trajectory
      0 requestedTime requestedTimePos.le
      evolves trajectoryReality trajectoryTransverse
      initialMarginActual
  exact
    { trajectory := trajectory
      initial := initial
      physicalProperties := physicalProperties
      criticalBarrier := criticalBarrier
      enstrophyAbsorption := enstrophyAbsorption
      serrinAbsorption := serrinAbsorption
      serrinBound := serrinBound
      highFrequencyTail := highFrequencyTail
      negativeOneTimeBudget := negativeOneTimeBudget }

end

end ThreeDimensionalVorticityCoefficientGeneratedPathCommonTimeCompactnessBudget
end NavierStokes
end SaturationMonoid

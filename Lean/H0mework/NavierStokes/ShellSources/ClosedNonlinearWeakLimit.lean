import H0mework.NavierStokes.Fourier.TransverseSpaceTimeNonlinearRow
import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeGradientLowerSemicontinuity

/-!
# Generated weak limits with their actual nonlinear row

This module closes the nonlinear identification left open by the initial
whole-lattice weak-limit theorem.  The same source-generated Galerkin
subsequence is lifted through the closed transverse time-`L²` carrier.
Continuity of the actual infinite Fourier nonlinearity then forces every
time-`L¹` row limit to equal the nonlinear row of that one transverse state.

The resulting receipt retains the generated whole-gradient mass bound.  It
does not assert classical continuation or a critical-norm estimate; those
are downstream consumers of the now-closed weak PDE object.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedIntegerShellClosedNonlinearWeakLimit

open scoped BigOperators ENNReal Topology

open Set
open Filter
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageCriticalPathCompactness
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageWeakSolution
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow

noncomputable section

/-- The physical punctured Galerkin trajectory installed directly in the
closed transverse time-`L²` carrier. -/
def puncturedCanonicalCriticalTransverseSpaceTimePath
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ requestedTime : ℝ)
    (θLtOne : θ < 1)
    (criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2)
    (requestedTimePos : 0 < requestedTime)
    (radius : ℕ) :
    TransverseSpaceTimeState requestedTime :=
  wholeTransverseTrajectorySpaceTimePath requestedTime
    (puncturedCanonicalCriticalTrajectory
      lineage ν θ θLtOne criticalMargin
      requestedTime requestedTimePos radius)
    (fun time timeMem =>
      ((puncturedCanonicalCriticalTrajectory_physicalProperties
        lineage ν θ θLtOne criticalMargin
        requestedTime requestedTimePos radius
        time timeMem).1).continuousAt.continuousWithinAt)
    (fun time timeMem =>
      (puncturedCanonicalCriticalTrajectory_physicalProperties
        lineage ν θ θLtOne criticalMargin
        requestedTime requestedTimePos radius
        time timeMem).2.2.1)

theorem transverseSpaceTimeInclusion_puncturedCanonicalCritical
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ requestedTime : ℝ)
    (θLtOne : θ < 1)
    (criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2)
    (requestedTimePos : 0 < requestedTime)
    (radius : ℕ) :
    transverseSpaceTimeInclusion requestedTime
        (puncturedCanonicalCriticalTransverseSpaceTimePath
          lineage ν θ requestedTime θLtOne criticalMargin
          requestedTimePos radius) =
      puncturedCanonicalCriticalSpaceTimePath
        lineage ν θ θLtOne criticalMargin
        requestedTime requestedTimePos radius := by
  unfold puncturedCanonicalCriticalTransverseSpaceTimePath
  calc
    _ = wholeTrajectorySpaceTimePath requestedTime
          (puncturedCanonicalCriticalTrajectory
            lineage ν θ θLtOne criticalMargin requestedTime
            requestedTimePos radius)
          (fun time timeMem =>
            ((puncturedCanonicalCriticalTrajectory_physicalProperties
              lineage ν θ θLtOne criticalMargin requestedTime
              requestedTimePos radius time timeMem).1).continuousAt.continuousWithinAt) :=
      transverseSpaceTimeInclusion_wholeTransverseTrajectory
        requestedTime
        (puncturedCanonicalCriticalTrajectory
          lineage ν θ θLtOne criticalMargin requestedTime
          requestedTimePos radius)
        (fun time timeMem =>
          ((puncturedCanonicalCriticalTrajectory_physicalProperties
            lineage ν θ θLtOne criticalMargin requestedTime
            requestedTimePos radius time timeMem).1).continuousAt.continuousWithinAt)
        (fun time timeMem =>
          (puncturedCanonicalCriticalTrajectory_physicalProperties
            lineage ν θ θLtOne criticalMargin requestedTime
            requestedTimePos radius time timeMem).2.2.1)
    _ = puncturedCanonicalCriticalSpaceTimePath
          lineage ν θ θLtOne criticalMargin requestedTime
          requestedTimePos radius :=
      (puncturedCanonicalCriticalSpaceTimePath_eq_wholeTrajectorySpaceTimePath
        lineage ν θ θLtOne criticalMargin requestedTime
        requestedTimePos radius).symm

/-- One source-generated weak solution whose nonlinearity is evaluated on
the same transverse state and whose whole gradient mass is finite. -/
structure ClosedNonlinearWeakLimitReceipt
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ requestedTime : ℝ)
    (θLtOne : θ < 1)
    (criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2)
    (requestedTimePos : 0 < requestedTime) where
  stateLimit : SpaceTimeState requestedTime
  transverseLimit : TransverseSpaceTimeState requestedTime
  stateLimit_mem :
    stateLimit ∈
      closure
        (generatedCriticalSpaceTimePathFamily
          (ν := ν) θLtOne requestedTimePos)
  inclusion_eq :
    transverseSpaceTimeInclusion requestedTime transverseLimit =
      stateLimit
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  state_tendsto :
    Tendsto
      (fun index =>
        puncturedCanonicalCriticalSpaceTimePath
          lineage ν θ θLtOne criticalMargin
          requestedTime requestedTimePos (subsequence index))
      atTop (𝓝 stateLimit)
  transverse_tendsto :
    Tendsto
      (fun index =>
        puncturedCanonicalCriticalTransverseSpaceTimePath
          lineage ν θ requestedTime θLtOne criticalMargin
          requestedTimePos (subsequence index))
      atTop (𝓝 transverseLimit)
  weak_action :
    ∀ wave : IntegerWavevector, wave ≠ 0 →
      ∀ (test testDerivative : ℝ → ℂ),
        ∀ (testHasDeriv :
            ∀ t ∈ Icc (0 : ℝ) requestedTime,
              HasDerivAt test (testDerivative t) t)
          (testDerivativeContinuous :
            ContinuousOn testDerivative
              (Icc (0 : ℝ) requestedTime))
          (_testZero : test 0 = 0)
          (_testRequestedTimeZero :
            test requestedTime = 0),
        fixedWaveWeakAction requestedTime ν.coeff wave
            (restrictedScalarL2 requestedTime test
              (fun time timeMem =>
                (testHasDeriv time timeMem).continuousAt.continuousWithinAt))
            (restrictedScalarL2 requestedTime testDerivative
              testDerivativeContinuous)
            (restrictedScalarLInf requestedTime test
              (fun time timeMem =>
                (testHasDeriv time timeMem).continuousAt.continuousWithinAt))
            stateLimit
            (transverseSpaceTimeNonlinearRow transverseLimit wave) =
          0
  gradient_summable :
    Summable
      (fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity
          requestedTime stateLimit wave)
  gradient_mass_le :
    wholeSpaceTimeVorticityGradientMass
        requestedTime stateLimit ≤
      ((1 / 2 : ℝ) *
          criticalCoefficientEnstrophyCeiling ν θ) /
        criticalEnstrophyAbsorptionCoefficient θ ν

/--
The source lineage generates a whole-lattice weak solution whose nonlinear
row is the actual quadratic row of the same transverse state limit.
-/
noncomputable def GeneratedIntegerShellInfiniteLineage.generates_closedNonlinearWeakLimit
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ requestedTime : ℝ)
    (θLtOne : θ < 1)
    (criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2)
    (requestedTimePos : 0 < requestedTime) :
    ClosedNonlinearWeakLimitReceipt
      lineage ν θ requestedTime θLtOne criticalMargin
      requestedTimePos := by
  let weakLimitResult :=
    GeneratedIntegerShellInfiniteLineage.exists_weakFourierLimit_with_gradientMass
      lineage ν θ requestedTime θLtOne criticalMargin
      requestedTimePos
  let stateLimit : SpaceTimeState requestedTime :=
    Classical.choose weakLimitResult
  have stateLimitSpec :=
    Classical.choose_spec weakLimitResult
  have stateLimitMem := stateLimitSpec.1
  let subsequence : ℕ → ℕ :=
    Classical.choose stateLimitSpec.2
  have subsequenceSpec :=
    Classical.choose_spec stateLimitSpec.2
  have subsequenceMono := subsequenceSpec.1
  have stateTendsto := subsequenceSpec.2.1
  have weakRows := subsequenceSpec.2.2.1
  have gradientSummable := subsequenceSpec.2.2.2.1
  have gradientMassLe := subsequenceSpec.2.2.2.2
  let transverseStates :
      ℕ → TransverseSpaceTimeState requestedTime :=
    fun index =>
      puncturedCanonicalCriticalTransverseSpaceTimePath
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos (subsequence index)
  have includedTendsto :
      Tendsto
        (fun index =>
          transverseSpaceTimeInclusion requestedTime
            (transverseStates index))
        atTop (𝓝 stateLimit) := by
    simpa only [transverseStates,
      transverseSpaceTimeInclusion_puncturedCanonicalCritical]
      using stateTendsto
  let transverseLimitResult :=
    transverseSpaceTime_limit_of_inclusion_tendsto
      requestedTime transverseStates stateLimit includedTendsto
  let transverseLimit : TransverseSpaceTimeState requestedTime :=
    Classical.choose transverseLimitResult
  have transverseLimitSpec :=
    Classical.choose_spec transverseLimitResult
  have transverseTendsto := transverseLimitSpec.1
  have inclusionEq := transverseLimitSpec.2
  have weakAction :
      ∀ wave : IntegerWavevector, wave ≠ 0 →
        ∀ (test testDerivative : ℝ → ℂ),
          ∀ (testHasDeriv :
              ∀ t ∈ Icc (0 : ℝ) requestedTime,
                HasDerivAt test (testDerivative t) t)
            (testDerivativeContinuous :
              ContinuousOn testDerivative
                (Icc (0 : ℝ) requestedTime))
            (testZero : test 0 = 0)
            (testRequestedTimeZero :
              test requestedTime = 0),
          fixedWaveWeakAction requestedTime ν.coeff wave
              (restrictedScalarL2 requestedTime test
                (fun time timeMem =>
                  (testHasDeriv time timeMem).continuousAt.continuousWithinAt))
              (restrictedScalarL2 requestedTime testDerivative
                testDerivativeContinuous)
              (restrictedScalarLInf requestedTime test
                (fun time timeMem =>
                  (testHasDeriv time timeMem).continuousAt.continuousWithinAt))
              stateLimit
              (transverseSpaceTimeNonlinearRow
                transverseLimit wave) =
            0 := by
    intro wave waveNeZero test testDerivative
      testHasDeriv testDerivativeContinuous
      testZero testRequestedTimeZero
    obtain
        ⟨nonlinearLimit, nonlinearTendsto,
          allTests⟩ :=
      weakRows wave waveNeZero
    have transverseRowTendsto :
        Tendsto
          (fun index =>
            transverseSpaceTimeNonlinearRow
              (transverseStates index) wave)
          atTop (𝓝 nonlinearLimit) := by
      apply nonlinearTendsto.congr
      intro index
      exact (transverseSpaceTimeNonlinearRow_wholeTransverseTrajectory
        requestedTime
        (puncturedCanonicalCriticalTrajectory lineage ν θ θLtOne
          criticalMargin requestedTime requestedTimePos
          (subsequence index))
        (fun time timeMem =>
          ((puncturedCanonicalCriticalTrajectory_physicalProperties
            lineage ν θ θLtOne criticalMargin requestedTime
            requestedTimePos (subsequence index) time timeMem).1).continuousAt.continuousWithinAt)
        (fun time timeMem =>
          (puncturedCanonicalCriticalTrajectory_physicalProperties
            lineage ν θ θLtOne criticalMargin requestedTime
            requestedTimePos (subsequence index) time timeMem).2.2.1)
        wave).symm
    have generatedRowTendsto :
        Tendsto
          (fun index =>
            transverseSpaceTimeNonlinearRow
              (transverseStates index) wave)
          atTop
          (𝓝
            (transverseSpaceTimeNonlinearRow
              transverseLimit wave)) :=
      tendsto_transverseSpaceTimeNonlinearRow
        transverseStates transverseLimit
        transverseTendsto wave
    have nonlinearEq :
        nonlinearLimit =
          transverseSpaceTimeNonlinearRow
            transverseLimit wave :=
      tendsto_nhds_unique transverseRowTendsto
        generatedRowTendsto
    simpa only [nonlinearEq] using
      allTests test testDerivative testHasDeriv
        testDerivativeContinuous testZero
        testRequestedTimeZero
  exact
    { stateLimit := stateLimit
      transverseLimit := transverseLimit
      stateLimit_mem := stateLimitMem
      inclusion_eq := inclusionEq
      subsequence := subsequence
      subsequence_strictMono := subsequenceMono
      state_tendsto := stateTendsto
      transverse_tendsto := by
        simpa only [transverseStates] using
          transverseTendsto
      weak_action := weakAction
      gradient_summable := gradientSummable
      gradient_mass_le := gradientMassLe }

end

end ThreeDimensionalVorticityCoefficientGeneratedIntegerShellClosedNonlinearWeakLimit
end NavierStokes
end SaturationMonoid

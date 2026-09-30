import H0mework.NavierStokes.InitialData.FinitePhysicalStateGeneratedCriticalPath
import H0mework.NavierStokes.ShellSources.InfiniteLineageHilbertCompletion
import H0mework.NavierStokes.GeneratedPaths.StrongSpaceTimeSubsequence

/-!
# Critical-path compactness for punctured canonical lineage projections

Every punctured canonical projection of an actual infinite generated shell
lineage is already a sharply supported, transverse, Fourier-real finite
physical state.  The restart compiler therefore reifies it as an
identity-reachable source path, after which the existing common-time
producer and whole space-time compactness theorem apply without an external
trajectory or Cauchy premise.

The resulting actual trajectory starts at the projected lineage endpoint,
obeys the punctured-cube Galerkin law, and carries the complete physical
invariants.  The whole sequence admits one strictly monotone subsequence
converging strongly in `L²_t ℓ²_x`; the same subsequence converges on every
fixed Fourier row.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageCriticalPathCompactness

open scoped BigOperators Topology

open Set
open Filter
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientFinitePhysicalStateRestart
open ThreeDimensionalVorticityCoefficientFinitePhysicalStateGeneratedCriticalPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion.GeneratedIntegerShellInfiniteLineage

noncomputable section

/--
The radius-`n` punctured canonical projection of an actual infinite lineage,
reified as an identity-reachable generated critical path.
-/
def puncturedCanonicalCriticalScalePath
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ : ℝ)
    (criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2)
    (radius : ℕ) :
    GeneratedCriticalScalePath ν θ :=
  generatedCriticalScalePathOfFinitePhysicalState
    (puncturedIntegerWaveFrequencyCube radius)
    (zero_not_mem_puncturedIntegerWaveFrequencyCube radius)
    (fun _wave waveMem =>
      puncturedIntegerWaveFrequencyCube_waveNeg_mem
        radius waveMem)
    ν θ
    (puncturedCanonicalInitialState lineage radius)
    (puncturedCanonicalInitialState_supported lineage radius)
    (puncturedCanonicalInitialState_transverse lineage radius)
    (puncturedCanonicalInitialState_reality lineage radius)
    (puncturedCanonicalInitialState_criticalMargin
      lineage ν θ criticalMargin radius)

@[simp] theorem puncturedCanonicalCriticalScalePath_generatedSupport
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ : ℝ)
    (criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2)
    (radius : ℕ) :
    generatedSupport
        (puncturedCanonicalCriticalScalePath
          lineage ν θ criticalMargin radius).current =
      puncturedIntegerWaveFrequencyCube radius := by
  exact
    rawSourceOfFiniteVorticityState_generatedSupport
      (puncturedIntegerWaveFrequencyCube radius)
      (zero_not_mem_puncturedIntegerWaveFrequencyCube radius)
      (fun _wave waveMem =>
        puncturedIntegerWaveFrequencyCube_waveNeg_mem
          radius waveMem)
      (puncturedCanonicalInitialState lineage radius)

theorem puncturedCanonicalCriticalScalePath_initialState
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ : ℝ)
    (criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2)
    (radius : ℕ) :
    generatedComplexVorticityState
        (puncturedCanonicalCriticalScalePath
          lineage ν θ criticalMargin radius).current
        (generatedSupport
          (puncturedCanonicalCriticalScalePath
            lineage ν θ criticalMargin radius).current) =
      puncturedCanonicalInitialState lineage radius := by
  exact
    generatedCriticalScalePathOfFinitePhysicalState_initialState
      (puncturedIntegerWaveFrequencyCube radius)
      (zero_not_mem_puncturedIntegerWaveFrequencyCube radius)
      (fun _wave waveMem =>
        puncturedIntegerWaveFrequencyCube_waveNeg_mem
          radius waveMem)
      ν θ
      (puncturedCanonicalInitialState lineage radius)
      (puncturedCanonicalInitialState_supported lineage radius)
      (puncturedCanonicalInitialState_transverse lineage radius)
      (puncturedCanonicalInitialState_reality lineage radius)
      (puncturedCanonicalInitialState_criticalMargin
        lineage ν θ criticalMargin radius)

/-- The actual common-time trajectory selected by the reified canonical path. -/
def puncturedCanonicalCriticalTrajectory
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ : ℝ)
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
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (radius : ℕ) :
    ℝ → ComplexVorticityHilbertState :=
  ((puncturedCanonicalCriticalScalePath
    lineage ν θ criticalMargin radius).commonTimeBudget
      θLtOne requestedTimePos).trajectory

@[simp] theorem puncturedCanonicalCriticalTrajectory_initial
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ : ℝ)
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
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (radius : ℕ) :
    puncturedCanonicalCriticalTrajectory
        lineage ν θ θLtOne criticalMargin
        requestedTime requestedTimePos radius 0 =
      puncturedCanonicalInitialState lineage radius := by
  exact
    ((puncturedCanonicalCriticalScalePath
        lineage ν θ criticalMargin radius).commonTimeBudget
          θLtOne requestedTimePos).initial.trans
      (puncturedCanonicalCriticalScalePath_initialState
        lineage ν θ criticalMargin radius)

theorem puncturedCanonicalCriticalTrajectory_physicalProperties
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ : ℝ)
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
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (radius : ℕ)
    (time : ℝ)
    (timeMem : time ∈ Icc (0 : ℝ) requestedTime) :
    HasDerivAt
        (puncturedCanonicalCriticalTrajectory
          lineage ν θ θLtOne criticalMargin
          requestedTime requestedTimePos radius)
        (finiteStateVorticityGenerator
          (puncturedIntegerWaveFrequencyCube radius) ν.coeff
          (puncturedCanonicalCriticalTrajectory
            lineage ν θ θLtOne criticalMargin
            requestedTime requestedTimePos radius time)) time ∧
      (∀ wave,
        wave ∉ puncturedIntegerWaveFrequencyCube radius →
          puncturedCanonicalCriticalTrajectory
            lineage ν θ θLtOne criticalMargin
            requestedTime requestedTimePos radius time wave = 0) ∧
      (∀ wave,
        complexWavevector wave ⬝ᵥ
          puncturedCanonicalCriticalTrajectory
            lineage ν θ θLtOne criticalMargin
            requestedTime requestedTimePos radius time wave = 0) ∧
      FiniteStateFourierReality
        (puncturedCanonicalCriticalTrajectory
          lineage ν θ θLtOne criticalMargin
          requestedTime requestedTimePos radius time) := by
  simpa only [
    puncturedCanonicalCriticalTrajectory,
    puncturedCanonicalCriticalScalePath_generatedSupport] using
    ((puncturedCanonicalCriticalScalePath
      lineage ν θ criticalMargin radius).commonTimeBudget
        θLtOne requestedTimePos).physicalProperties time timeMem

/-- Whole space-time realization of the actual canonical trajectory. -/
def puncturedCanonicalCriticalSpaceTimePath
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ : ℝ)
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
    (requestedTime : ℝ)
    (requestedTimePos : 0 < requestedTime)
    (radius : ℕ) :
    SpaceTimeState requestedTime :=
  generatedCriticalSpaceTimePath θLtOne requestedTimePos
    (puncturedCanonicalCriticalScalePath
      lineage ν θ criticalMargin radius)

/--
The whole punctured canonical Galerkin sequence has a source-generated
strictly monotone subsequence converging strongly in space-time `L²`, with
the same subsequence converging on every fixed Fourier row.
-/
theorem
    puncturedCanonicalCriticalSpaceTimePath_strong_subsequence_with_fixed_wave_rows
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
    ∃ limit : SpaceTimeState requestedTime,
      limit ∈
          closure
            (generatedCriticalSpaceTimePathFamily
              (ν := ν) θLtOne requestedTimePos) ∧
      ∃ subsequence : ℕ → ℕ,
        StrictMono subsequence ∧
        Tendsto
            (fun index =>
              puncturedCanonicalCriticalSpaceTimePath
                lineage ν θ θLtOne criticalMargin
                requestedTime requestedTimePos
                (subsequence index))
            atTop (𝓝 limit) ∧
        Tendsto
            (fun index =>
              ‖puncturedCanonicalCriticalSpaceTimePath
                    lineage ν θ θLtOne criticalMargin
                    requestedTime requestedTimePos
                    (subsequence index) -
                  limit‖)
            atTop (𝓝 0) ∧
        (∀ wave : IntegerWavevector,
          Tendsto
              (fun index =>
                fixedWaveSpaceTimeRestriction requestedTime wave
                  (puncturedCanonicalCriticalSpaceTimePath
                    lineage ν θ θLtOne criticalMargin
                    requestedTime requestedTimePos
                    (subsequence index)))
              atTop
              (𝓝
                (fixedWaveSpaceTimeRestriction requestedTime wave
                  limit))) ∧
        (∀ wave : IntegerWavevector,
          Tendsto
              (fun index =>
                ‖fixedWaveSpaceTimeRestriction requestedTime wave
                      (puncturedCanonicalCriticalSpaceTimePath
                        lineage ν θ θLtOne criticalMargin
                        requestedTime requestedTimePos
                        (subsequence index)) -
                    fixedWaveSpaceTimeRestriction requestedTime wave
                      limit‖)
              atTop (𝓝 0)) := by
  simpa only [puncturedCanonicalCriticalSpaceTimePath] using
    generatedCriticalSpaceTimePath_strong_subsequence_with_fixed_wave_rows
      θLtOne requestedTimePos
      (fun radius =>
        puncturedCanonicalCriticalScalePath
          lineage ν θ criticalMargin radius)

end

end ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageCriticalPathCompactness
end NavierStokes
end SaturationMonoid

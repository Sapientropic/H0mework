import H0mework.NavierStokes.Galerkin.EnstrophyBalance
import H0mework.NavierStokes.GeneratedPaths.ViscousEnstrophyCost

/-!
# Exact stretching budget forced by an arbitrary generated scale path

This module places the arbitrary-path cumulative trace lower bound and the
finite Galerkin enstrophy balance on the same source-generated trajectory.
The result is the exact responsibility ledger

```text
viscous path charge
  <= integrated stretching + initial half-enstrophy
       - terminal half-enstrophy.
```

Consequently frequency, amplitude, positive physical time, viscosity, and
vortex stretching can no longer be audited in separate carriers.  The only
remaining route to continuation is a cutoff-independent control or
absorption of the generated stretching term.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedPathStretchingBudget

open scoped BigOperators Topology ENNReal

open Set
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedPathViscousEnstrophyCost
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance

noncomputable section

theorem finiteStateVorticityHalfEnstrophy_nonneg
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    0 ≤ finiteStateVorticityHalfEnstrophy modes state := by
  unfold finiteStateVorticityHalfEnstrophy
    finiteStateVorticityCoefficientEnstrophy
  exact mul_nonneg (by norm_num) <|
    Finset.sum_nonneg fun wave waveMem =>
      complexCoordinateAmplitudeSq_nonneg _

/-- Every arbitrary generated finite scale path produces one actual
transverse, Fourier-real trajectory on which its cumulative trace charge is
paid exactly by initial enstrophy and integrated vortex stretching.

No trajectory, positive time, cutoff, target shell, amplitude bound,
stretching sign, or dissipation budget is a premise. -/
theorem generatedIntegerShellReachable_drives_stretchingBudget
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (ν : Viscosity) :
    ∃ (trajectory : ℝ → ComplexVorticityHilbertState)
        (occupancyTime : ℝ),
      0 < occupancyTime ∧
        trajectory 0 =
          generatedComplexVorticityState current
            (generatedSupport current) ∧
        (∀ t ∈ Icc (0 : ℝ) occupancyTime,
          HasDerivAt trajectory
              (finiteStateVorticityGenerator
                (generatedSupport current) ν.coeff (trajectory t)) t ∧
            (∀ wave,
              wave ∉ generatedSupport current →
                trajectory t wave = 0) ∧
            (∀ wave,
              complexWavevector wave ⬝ᵥ trajectory t wave = 0) ∧
            FiniteStateFourierReality (trajectory t)) ∧
        ν.coeff * (2 * Real.pi) ^ 2 *
              (∫ t in (0 : ℝ)..occupancyTime,
                finiteStateVorticityEnstrophyMass
                  (generatedSupport current) (trajectory t)) =
            (∫ t in (0 : ℝ)..occupancyTime,
              finiteStateVorticityStretchingWork
                (generatedSupport current) (trajectory t)) +
              finiteStateVorticityHalfEnstrophy
                (generatedSupport current) (trajectory 0) -
              finiteStateVorticityHalfEnstrophy
                (generatedSupport current) (trajectory occupancyTime) ∧
        ν.coeff * (2 * Real.pi) ^ 2 *
              (occupancyTime *
                (integerShellWeightedNormSq
                    (generatedIntegerShellCumulativeTrace arrival) /
                  2)) ≤
            (∫ t in (0 : ℝ)..occupancyTime,
              finiteStateVorticityStretchingWork
                (generatedSupport current) (trajectory t)) +
              finiteStateVorticityHalfEnstrophy
                (generatedSupport current) (trajectory 0) -
              finiteStateVorticityHalfEnstrophy
                (generatedSupport current) (trajectory occupancyTime) ∧
        ν.coeff * (2 * Real.pi) ^ 2 *
              (occupancyTime *
                (integerShellWeightedNormSq
                    (generatedIntegerShellCumulativeTrace arrival) /
                  2)) ≤
            (∫ t in (0 : ℝ)..occupancyTime,
              finiteStateVorticityStretchingWork
                (generatedSupport current) (trajectory t)) +
              finiteStateVorticityHalfEnstrophy
                (generatedSupport current) (trajectory 0) := by
  obtain
      ⟨trajectory, occupancyTime, occupancyTimePos, initial,
        physicalProperties, cumulativeTraceLower⟩ :=
    generatedIntegerShellReachable_drives_transverseRealityIntegratedEndpointEnstrophyCost
      arrival ν.coeff
  let modes := generatedSupport current
  have negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes := by
    intro wave waveMem
    exact generatedSupport_waveNeg_mem current waveMem
  have evolves :
      ∀ t ∈ Icc (0 : ℝ) occupancyTime,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν.coeff (trajectory t)) t := by
    intro t timeMem
    exact (physicalProperties t timeMem).1
  have reality :
      ∀ t ∈ Icc (0 : ℝ) occupancyTime,
        FiniteStateFourierReality (trajectory t) := by
    intro t timeMem
    exact (physicalProperties t timeMem).2.2.2
  have enstrophyContinuousOn :
      ContinuousOn
        (fun t =>
          finiteStateVorticityEnstrophyMass modes (trajectory t))
        (Icc (0 : ℝ) occupancyTime) := by
    intro t timeMem
    exact
      (finiteStateVorticityEnstrophyMass_continuousAt_of_hasDerivAt
        modes trajectory t
        (finiteStateVorticityGenerator
          modes ν.coeff (trajectory t))
        (evolves t timeMem)).continuousWithinAt
  have nonlinearContinuousOn :
      ContinuousOn
        (fun t =>
          finiteStateVorticityNonlinearWork modes (trajectory t))
        (Icc (0 : ℝ) occupancyTime) := by
    intro t timeMem
    exact
      (finiteStateVorticityNonlinearWork_continuousAt_of_hasDerivAt
        modes trajectory t
        (finiteStateVorticityGenerator
          modes ν.coeff (trajectory t))
        (evolves t timeMem)).continuousWithinAt
  have stretchingContinuousOn :
      ContinuousOn
        (fun t =>
          finiteStateVorticityStretchingWork modes (trajectory t))
        (Icc (0 : ℝ) occupancyTime) := by
    apply nonlinearContinuousOn.congr
    intro t timeMem
    exact
      (finiteStateVorticityNonlinearWork_eq_stretchingWork
        modes negClosed (trajectory t) (reality t timeMem)).symm
  have enstrophyIntegrable :
      IntervalIntegrable
        (fun t =>
          finiteStateVorticityEnstrophyMass modes (trajectory t))
        volume 0 occupancyTime :=
    ContinuousOn.intervalIntegrable_of_Icc
      occupancyTimePos.le enstrophyContinuousOn
  have stretchingIntegrable :
      IntervalIntegrable
        (fun t =>
          finiteStateVorticityStretchingWork modes (trajectory t))
        volume 0 occupancyTime :=
    ContinuousOn.intervalIntegrable_of_Icc
      occupancyTimePos.le stretchingContinuousOn
  have weightedEnstrophyIntegrable :
      IntervalIntegrable
        (fun t =>
          ν.coeff * (2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass modes (trajectory t))
        volume 0 occupancyTime :=
    enstrophyIntegrable.const_mul
      (ν.coeff * (2 * Real.pi) ^ 2)
  have balance :=
    finiteStateVorticityHalfEnstrophy_integral_stretchingWork
      modes negClosed ν.coeff trajectory 0 occupancyTime
      occupancyTimePos.le evolves reality
  have expandedBalance :
      (∫ t in (0 : ℝ)..occupancyTime,
          finiteStateVorticityStretchingWork modes (trajectory t)) -
          ν.coeff * (2 * Real.pi) ^ 2 *
            (∫ t in (0 : ℝ)..occupancyTime,
              finiteStateVorticityEnstrophyMass modes (trajectory t)) =
        finiteStateVorticityHalfEnstrophy modes
            (trajectory occupancyTime) -
          finiteStateVorticityHalfEnstrophy modes (trajectory 0) := by
    rw [intervalIntegral.integral_sub
      stretchingIntegrable weightedEnstrophyIntegrable,
      intervalIntegral.integral_const_mul] at balance
    exact balance
  have exactStretchingBudget :
      ν.coeff * (2 * Real.pi) ^ 2 *
            (∫ t in (0 : ℝ)..occupancyTime,
              finiteStateVorticityEnstrophyMass modes (trajectory t)) =
          (∫ t in (0 : ℝ)..occupancyTime,
            finiteStateVorticityStretchingWork modes (trajectory t)) +
            finiteStateVorticityHalfEnstrophy modes (trajectory 0) -
            finiteStateVorticityHalfEnstrophy modes
              (trajectory occupancyTime) := by
    linarith
  have viscousFactorNonneg :
      0 ≤ ν.coeff * (2 * Real.pi) ^ 2 :=
    mul_nonneg ν.coeff_pos.le (sq_nonneg _)
  have pathChargeLower :
      ν.coeff * (2 * Real.pi) ^ 2 *
            (occupancyTime *
              (integerShellWeightedNormSq
                  (generatedIntegerShellCumulativeTrace arrival) /
                2)) ≤
          ν.coeff * (2 * Real.pi) ^ 2 *
            (∫ t in (0 : ℝ)..occupancyTime,
              finiteStateVorticityEnstrophyMass modes (trajectory t)) :=
    mul_le_mul_of_nonneg_left cumulativeTraceLower viscousFactorNonneg
  have pathStretchingBudget :
      ν.coeff * (2 * Real.pi) ^ 2 *
            (occupancyTime *
              (integerShellWeightedNormSq
                  (generatedIntegerShellCumulativeTrace arrival) /
                2)) ≤
          (∫ t in (0 : ℝ)..occupancyTime,
            finiteStateVorticityStretchingWork modes (trajectory t)) +
            finiteStateVorticityHalfEnstrophy modes (trajectory 0) -
            finiteStateVorticityHalfEnstrophy modes
              (trajectory occupancyTime) := by
    rw [← exactStretchingBudget]
    exact pathChargeLower
  have terminalNonneg :
      0 ≤ finiteStateVorticityHalfEnstrophy modes
        (trajectory occupancyTime) :=
    finiteStateVorticityHalfEnstrophy_nonneg modes _
  have pathStretchingBudgetWithoutTerminal :
      ν.coeff * (2 * Real.pi) ^ 2 *
            (occupancyTime *
              (integerShellWeightedNormSq
                  (generatedIntegerShellCumulativeTrace arrival) /
                2)) ≤
          (∫ t in (0 : ℝ)..occupancyTime,
            finiteStateVorticityStretchingWork modes (trajectory t)) +
            finiteStateVorticityHalfEnstrophy modes (trajectory 0) := by
    linarith
  exact
    ⟨trajectory, occupancyTime, occupancyTimePos, initial,
      physicalProperties, exactStretchingBudget,
      pathStretchingBudget, pathStretchingBudgetWithoutTerminal⟩

end

end ThreeDimensionalVorticityCoefficientGeneratedPathStretchingBudget
end NavierStokes
end SaturationMonoid

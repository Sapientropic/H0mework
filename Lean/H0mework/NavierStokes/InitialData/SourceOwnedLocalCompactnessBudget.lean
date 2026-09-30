import H0mework.NavierStokes.InitialData.SourceOwnedLocalCommonTimeExistence
import H0mework.NavierStokes.Galerkin.NegativeSobolevTimeBudget
import H0mework.NavierStokes.WholeSpace.WholeStateSourceOwnedLocalBarrier

/-!
# Source-owned local compactness budgets

The source-owned local barrier is integrated on the same actual unforced
Galerkin trajectory.  It yields, uniformly in the finite carrier:

* a pointwise coefficient-enstrophy ceiling;
* a physical vorticity-gradient integral budget;
* an actual velocity-majorant square integral budget.

These are the supercritical local replacements for the global small-data
compactness rows.  No cutoff, tail estimate, continuation certificate, or
analytic budget is accepted by the theorem mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientSourceOwnedLocalCompactnessBudget

open scoped BigOperators Topology Interval ENNReal

open Set
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalTimeConsumer
open ThreeDimensionalVorticityCoefficientGeneratedPathStretchingBudget
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinNegativeSobolevTimeBudget
open
  ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption
open
  ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier

noncomputable section

/-- Integrated local H1/Serrin budget on one actual finite Galerkin orbit
under a common source-generated whole-state ceiling. -/
theorem finiteStateVorticity_sourceOwnedWholeStateCompactnessBudget_on_Icc
    (modes : Finset IntegerWavevector)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : Viscosity)
    (ceiling : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (b : ℝ)
    (bNonneg : 0 ≤ b)
    (initialFits :
      finiteStateVorticityCoefficientEnstrophy
            modes (trajectory 0) + 1 ≤
        ceiling)
    (bLeDuration :
      b ≤ sourceOwnedWholeStateDuration ν ceiling)
    (evolves :
      ∀ t ∈ Icc (0 : ℝ) b,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν.coeff (trajectory t)) t)
    (reality :
      ∀ t ∈ Icc (0 : ℝ) b,
        FiniteStateFourierReality (trajectory t))
    (transverse :
      ∀ t ∈ Icc (0 : ℝ) b,
        ∀ wave ∈ modes,
          complexWavevector wave ⬝ᵥ trajectory t wave = 0) :
    (∀ t ∈ Icc (0 : ℝ) b,
        finiteStateVorticityCoefficientEnstrophy
            modes (trajectory t) ≤
          ceiling) ∧
      (3 * ν.coeff / 8) * (2 * Real.pi) ^ 2 *
            (∫ t in (0 : ℝ)..b,
              finiteStateVorticityEnstrophyMass
                modes (trajectory t)) ≤
        finiteStateVorticityHalfEnstrophy modes (trajectory 0) +
          sourceOwnedLocalQuadraticCoefficient ν ceiling *
            ceiling ^ 2 * b ∧
      (∫ t in (0 : ℝ)..b,
          finiteStateVelocityMajorant modes (trajectory t) ^ 2) ≤
        2 * sourceOwnedLocalCoreVelocityCoefficient ν ceiling *
            ceiling * b +
          2 * biotSavartSerrinConstant *
            sourceOwnedKernelTailTolerance ν ceiling *
            (∫ t in (0 : ℝ)..b,
              finiteStateVorticityEnstrophyMass
                modes (trajectory t)) ∧
      (∫ t in (0 : ℝ)..b,
          finiteStateVorticityNegativeOneMass modes
            (finiteStateVorticityGenerator
              modes ν.coeff (trajectory t))) ≤
        8 * ceiling *
            (∫ t in (0 : ℝ)..b,
              finiteStateVelocityMajorant modes (trajectory t) ^ 2) +
          2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
            (∫ t in (0 : ℝ)..b,
              finiteStateVorticityEnstrophyMass
                modes (trajectory t)) := by
  let quadratic := sourceOwnedLocalQuadraticCoefficient ν ceiling
  let gradientMass : ℝ → ℝ := fun t =>
    finiteStateVorticityEnstrophyMass modes (trajectory t)
  let velocitySq : ℝ → ℝ := fun t =>
    finiteStateVelocityMajorant modes (trajectory t) ^ 2
  let exactRate : ℝ → ℝ := fun t =>
    finiteStateVorticityStretchingWork modes (trajectory t) -
      ν.coeff * (2 * Real.pi) ^ 2 * gradientMass t
  let generatorMass : ℝ → ℝ := fun t =>
    finiteStateVorticityNegativeOneMass modes
      (finiteStateVorticityGenerator
        modes ν.coeff (trajectory t))
  have barrier :=
    finiteStateVorticity_sourceOwnedWholeStateBarrier_on_Icc
      modes negClosed ν ceiling trajectory b initialFits bLeDuration
      evolves reality transverse
  have enstrophyCeiling :
      ∀ t ∈ Icc (0 : ℝ) b,
        finiteStateVorticityCoefficientEnstrophy
            modes (trajectory t) ≤ ceiling := by
    intro t tMem
    exact (barrier t tMem).2
  have gradientContinuous : ContinuousOn gradientMass (Icc (0 : ℝ) b) := by
    intro t tMem
    exact
      (finiteStateVorticityEnstrophyMass_continuousAt_of_hasDerivAt
        modes trajectory t
        (finiteStateVorticityGenerator
          modes ν.coeff (trajectory t))
        (evolves t tMem)).continuousWithinAt
  have velocityContinuous : ContinuousOn velocitySq (Icc (0 : ℝ) b) := by
    intro t tMem
    exact
      ((finiteStateVelocityMajorant_continuousAt_of_hasDerivAt
        modes trajectory t
        (finiteStateVorticityGenerator
          modes ν.coeff (trajectory t))
        (evolves t tMem)).pow 2).continuousWithinAt
  have stretchingContinuous :
      ContinuousOn
        (fun t => finiteStateVorticityStretchingWork modes (trajectory t))
        (Icc (0 : ℝ) b) := by
    have nonlinearContinuous :
        ContinuousOn
          (fun t => finiteStateVorticityNonlinearWork modes (trajectory t))
          (Icc (0 : ℝ) b) := by
      intro t tMem
      exact
        (finiteStateVorticityNonlinearWork_continuousAt_of_hasDerivAt
          modes trajectory t
          (finiteStateVorticityGenerator
            modes ν.coeff (trajectory t))
          (evolves t tMem)).continuousWithinAt
    exact nonlinearContinuous.congr fun t tMem =>
      (finiteStateVorticityNonlinearWork_eq_stretchingWork
        modes negClosed (trajectory t) (reality t tMem)).symm
  have generatorContinuous :
      ContinuousOn generatorMass (Icc (0 : ℝ) b) := by
    intro t tMem
    exact
      (finiteStateVorticityGenerator_negativeOneMass_continuousAt
        modes ν.coeff trajectory t (evolves t tMem)).continuousWithinAt
  have gradientIntegrable :
      IntervalIntegrable gradientMass volume 0 b :=
    ContinuousOn.intervalIntegrable_of_Icc bNonneg gradientContinuous
  have velocityIntegrable :
      IntervalIntegrable velocitySq volume 0 b :=
    ContinuousOn.intervalIntegrable_of_Icc bNonneg velocityContinuous
  have stretchingIntegrable :
      IntervalIntegrable
        (fun t => finiteStateVorticityStretchingWork modes (trajectory t))
        volume 0 b :=
    ContinuousOn.intervalIntegrable_of_Icc bNonneg stretchingContinuous
  have generatorIntegrable :
      IntervalIntegrable generatorMass volume 0 b :=
    ContinuousOn.intervalIntegrable_of_Icc bNonneg generatorContinuous
  have exactRateIntegrable : IntervalIntegrable exactRate volume 0 b :=
    stretchingIntegrable.sub
      (gradientIntegrable.const_mul
        (ν.coeff * (2 * Real.pi) ^ 2))
  have initialEnstrophyNonneg :
      0 ≤ finiteStateVorticityCoefficientEnstrophy
        modes (trajectory 0) := by
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave waveMem =>
      complexCoordinateAmplitudeSq_nonneg (trajectory 0 wave)
  have ceilingPos : 0 < ceiling := by
    linarith
  have quadraticNonneg : 0 ≤ quadratic :=
    sourceOwnedLocalQuadraticCoefficient_nonneg ν ceiling
  have pointwiseRate :
      ∀ t ∈ Icc (0 : ℝ) b,
        exactRate t ≤
          -(3 * ν.coeff / 8 * (2 * Real.pi) ^ 2) *
              gradientMass t +
            quadratic * ceiling ^ 2 := by
    intro t tMem
    have localRate :=
      finiteStateVorticityHalfEnstrophy_hasDerivAt_and_le_sourceOwnedLocal
        modes negClosed ν ceiling trajectory t
        (evolves t tMem) (reality t tMem)
        (transverse t tMem) (enstrophyCeiling t tMem)
    have currentEnstrophyNonneg :
        0 ≤ finiteStateVorticityCoefficientEnstrophy
          modes (trajectory t) := by
      unfold finiteStateVorticityCoefficientEnstrophy
      exact Finset.sum_nonneg fun wave waveMem =>
        complexCoordinateAmplitudeSq_nonneg (trajectory t wave)
    have squareLe :
        finiteStateVorticityCoefficientEnstrophy
              modes (trajectory t) ^ 2 ≤ ceiling ^ 2 := by
      nlinarith [enstrophyCeiling t tMem]
    calc
      exactRate t ≤
          -(3 * ν.coeff / 8) *
                ((2 * Real.pi) ^ 2 * gradientMass t) +
            quadratic *
              finiteStateVorticityCoefficientEnstrophy
                modes (trajectory t) ^ 2 := localRate.2
      _ ≤
          -(3 * ν.coeff / 8) *
                ((2 * Real.pi) ^ 2 * gradientMass t) +
            quadratic * ceiling ^ 2 := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left squareLe quadraticNonneg)
      _ =
          -(3 * ν.coeff / 8 * (2 * Real.pi) ^ 2) *
              gradientMass t + quadratic * ceiling ^ 2 := by ring
  have rateUpperIntegrable :
      IntervalIntegrable
        (fun t =>
          -(3 * ν.coeff / 8 * (2 * Real.pi) ^ 2) * gradientMass t +
            quadratic * ceiling ^ 2)
        volume 0 b :=
    (gradientIntegrable.const_mul
      (-(3 * ν.coeff / 8 * (2 * Real.pi) ^ 2))).add
      intervalIntegrable_const
  have integratedRate :=
    intervalIntegral.integral_mono_on
      bNonneg exactRateIntegrable rateUpperIntegrable pointwiseRate
  have exactLedger :=
    finiteStateVorticityHalfEnstrophy_integral_stretchingWork
      modes negClosed ν.coeff trajectory 0 b bNonneg evolves reality
  have gradientBudget :
      (3 * ν.coeff / 8) * (2 * Real.pi) ^ 2 *
            (∫ t in (0 : ℝ)..b, gradientMass t) ≤
        finiteStateVorticityHalfEnstrophy modes (trajectory 0) +
          quadratic * ceiling ^ 2 * b := by
    rw [show (∫ t in (0 : ℝ)..b, exactRate t) =
        finiteStateVorticityHalfEnstrophy modes (trajectory b) -
          finiteStateVorticityHalfEnstrophy modes (trajectory 0) by
      exact exactLedger] at integratedRate
    rw [intervalIntegral.integral_add
        (gradientIntegrable.const_mul
          (-(3 * ν.coeff / 8 * (2 * Real.pi) ^ 2)))
        intervalIntegrable_const,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const] at integratedRate
    have terminalNonneg :
        0 ≤ finiteStateVorticityHalfEnstrophy modes (trajectory b) :=
      finiteStateVorticityHalfEnstrophy_nonneg modes _
    simp only [sub_zero, smul_eq_mul] at integratedRate
    nlinarith
  have pointwiseVelocity :
      ∀ t ∈ Icc (0 : ℝ) b,
        velocitySq t ≤
          2 * sourceOwnedLocalCoreVelocityCoefficient ν ceiling * ceiling +
            2 * biotSavartSerrinConstant *
              sourceOwnedKernelTailTolerance ν ceiling * gradientMass t := by
    intro t tMem
    have localBound :=
      sourceOwnedLocal_velocityMajorant_sq_le
        ν ceiling modes (trajectory t)
    have coefficientNonneg :
        0 ≤ 2 * sourceOwnedLocalCoreVelocityCoefficient ν ceiling :=
      mul_nonneg (by norm_num)
        (sourceOwnedLocalCoreVelocityCoefficient_nonneg ν ceiling)
    exact localBound.trans <| add_le_add
      (mul_le_mul_of_nonneg_left
        (enstrophyCeiling t tMem) coefficientNonneg) le_rfl
  have velocityUpperIntegrable :
      IntervalIntegrable
        (fun t =>
          2 * sourceOwnedLocalCoreVelocityCoefficient ν ceiling * ceiling +
            2 * biotSavartSerrinConstant *
              sourceOwnedKernelTailTolerance ν ceiling * gradientMass t)
        volume 0 b :=
    intervalIntegrable_const.add
      (gradientIntegrable.const_mul
        (2 * biotSavartSerrinConstant *
          sourceOwnedKernelTailTolerance ν ceiling))
  have integratedVelocity :=
    intervalIntegral.integral_mono_on
      bNonneg velocityIntegrable velocityUpperIntegrable pointwiseVelocity
  have velocityBudget :
      (∫ t in (0 : ℝ)..b, velocitySq t) ≤
        2 * sourceOwnedLocalCoreVelocityCoefficient ν ceiling * ceiling * b +
          2 * biotSavartSerrinConstant *
            sourceOwnedKernelTailTolerance ν ceiling *
            (∫ t in (0 : ℝ)..b, gradientMass t) := by
    rw [intervalIntegral.integral_add
        intervalIntegrable_const
        (gradientIntegrable.const_mul
          (2 * biotSavartSerrinConstant *
            sourceOwnedKernelTailTolerance ν ceiling)),
      intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul] at integratedVelocity
    simp only [sub_zero, smul_eq_mul] at integratedVelocity
    nlinarith
  have pointwiseGenerator :
      ∀ t ∈ Icc (0 : ℝ) b,
        generatorMass t ≤
          8 * ceiling * velocitySq t +
            2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 * gradientMass t := by
    intro t tMem
    have rawBound :=
      finiteStateVorticityGenerator_negativeOneMass_le
        modes ν.coeff (trajectory t)
        (fun wave waveMem => transverse t tMem wave waveMem)
    have nonlinearLe :
        8 * velocitySq t *
              finiteStateVorticityCoefficientEnstrophy
                modes (trajectory t) ≤
          8 * velocitySq t * ceiling :=
      mul_le_mul_of_nonneg_left
        (enstrophyCeiling t tMem)
        (mul_nonneg (by norm_num) (sq_nonneg _))
    calc
      generatorMass t ≤
          8 * velocitySq t *
                finiteStateVorticityCoefficientEnstrophy
                  modes (trajectory t) +
            2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 * gradientMass t := by
        simpa [generatorMass, velocitySq, gradientMass] using rawBound
      _ ≤
          8 * velocitySq t * ceiling +
            2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 * gradientMass t :=
        add_le_add nonlinearLe le_rfl
      _ =
          8 * ceiling * velocitySq t +
            2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 * gradientMass t := by
        ring
  have generatorUpperIntegrable :
      IntervalIntegrable
        (fun t =>
          8 * ceiling * velocitySq t +
            2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 * gradientMass t)
        volume 0 b :=
    (velocityIntegrable.const_mul (8 * ceiling)).add
      (gradientIntegrable.const_mul
        (2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2))
  have integratedGenerator :=
    intervalIntegral.integral_mono_on
      bNonneg generatorIntegrable generatorUpperIntegrable
      pointwiseGenerator
  have generatorBudget :
      (∫ t in (0 : ℝ)..b, generatorMass t) ≤
        8 * ceiling * (∫ t in (0 : ℝ)..b, velocitySq t) +
          2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
            (∫ t in (0 : ℝ)..b, gradientMass t) := by
    rw [intervalIntegral.integral_add
        (velocityIntegrable.const_mul (8 * ceiling))
        (gradientIntegrable.const_mul
          (2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2)),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at integratedGenerator
    exact integratedGenerator
  exact
    ⟨enstrophyCeiling,
      by simpa [quadratic, gradientMass] using gradientBudget,
      by simpa [velocitySq, gradientMass] using velocityBudget,
      by simpa [generatorMass, velocitySq, gradientMass] using
        generatorBudget⟩

/-- Existing finite-state specialization.  Its historical theorem mouth is
preserved while the proof now factors through the common-ceiling result. -/
theorem finiteStateVorticity_sourceOwnedLocalCompactnessBudget_on_Icc
    (modes : Finset IntegerWavevector)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : Viscosity)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (b : ℝ)
    (bNonneg : 0 ≤ b)
    (bLeDuration :
      b ≤ sourceOwnedLocalDuration ν modes (trajectory 0))
    (evolves :
      ∀ t ∈ Icc (0 : ℝ) b,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν.coeff (trajectory t)) t)
    (reality :
      ∀ t ∈ Icc (0 : ℝ) b,
        FiniteStateFourierReality (trajectory t))
    (transverse :
      ∀ t ∈ Icc (0 : ℝ) b,
        ∀ wave ∈ modes,
          complexWavevector wave ⬝ᵥ trajectory t wave = 0) :
    (∀ t ∈ Icc (0 : ℝ) b,
        finiteStateVorticityCoefficientEnstrophy
            modes (trajectory t) ≤
          sourceOwnedLocalEnstrophyCeiling modes (trajectory 0)) ∧
      (3 * ν.coeff / 8) * (2 * Real.pi) ^ 2 *
            (∫ t in (0 : ℝ)..b,
              finiteStateVorticityEnstrophyMass
                modes (trajectory t)) ≤
        finiteStateVorticityHalfEnstrophy modes (trajectory 0) +
          sourceOwnedLocalQuadraticCoefficient ν
              (sourceOwnedLocalEnstrophyCeiling modes (trajectory 0)) *
            sourceOwnedLocalEnstrophyCeiling
                modes (trajectory 0) ^ 2 * b ∧
      (∫ t in (0 : ℝ)..b,
          finiteStateVelocityMajorant modes (trajectory t) ^ 2) ≤
        2 * sourceOwnedLocalCoreVelocityCoefficient ν
              (sourceOwnedLocalEnstrophyCeiling modes (trajectory 0)) *
            sourceOwnedLocalEnstrophyCeiling modes (trajectory 0) * b +
          2 * biotSavartSerrinConstant *
            sourceOwnedKernelTailTolerance ν
              (sourceOwnedLocalEnstrophyCeiling modes (trajectory 0)) *
            (∫ t in (0 : ℝ)..b,
              finiteStateVorticityEnstrophyMass
                modes (trajectory t)) ∧
      (∫ t in (0 : ℝ)..b,
          finiteStateVorticityNegativeOneMass modes
            (finiteStateVorticityGenerator
              modes ν.coeff (trajectory t))) ≤
        8 * sourceOwnedLocalEnstrophyCeiling
              modes (trajectory 0) *
            (∫ t in (0 : ℝ)..b,
              finiteStateVelocityMajorant modes (trajectory t) ^ 2) +
          2 * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 *
            (∫ t in (0 : ℝ)..b,
              finiteStateVorticityEnstrophyMass
                modes (trajectory t)) := by
  let ceiling := sourceOwnedLocalEnstrophyCeiling modes (trajectory 0)
  have initialFits :
      finiteStateVorticityCoefficientEnstrophy
            modes (trajectory 0) + 1 ≤
        ceiling := by
    rfl
  have durationEq :
      sourceOwnedWholeStateDuration ν ceiling =
        sourceOwnedLocalDuration ν modes (trajectory 0) := by
    rfl
  have commonBound :
      b ≤ sourceOwnedWholeStateDuration ν ceiling := by
    rw [durationEq]
    exact bLeDuration
  simpa [ceiling] using
    finiteStateVorticity_sourceOwnedWholeStateCompactnessBudget_on_Icc
      modes negClosed ν ceiling trajectory b bNonneg initialFits commonBound
      evolves reality transverse

end

end
    ThreeDimensionalVorticityCoefficientSourceOwnedLocalCompactnessBudget
end NavierStokes
end SaturationMonoid

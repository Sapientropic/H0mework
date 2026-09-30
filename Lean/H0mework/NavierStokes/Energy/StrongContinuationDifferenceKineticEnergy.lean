import H0mework.NavierStokes.Energy.StrongContinuationDifferenceEnergy
import H0mework.NavierStokes.Galerkin.KineticEnergyLedger

/-!
# Kinetic-scale energy transport for strong-continuation differences

The exact all-wave difference-energy ledger is reweighted by the genuine
nonzero Fourier Laplacian multiplier.  This produces the kinetic-scale
carrier required by the Navier--Stokes uniqueness argument:

```text
sum_{k ≠ 0} |omega_left(k,t) - omega_right(k,t)|² / ((2*pi)² |k|²).
```

The weight is not supplied by a cutoff or a frequency inventory.  Every
nonzero integer wave generates its own positive multiplier, and the complete
weighted family is summable because the integer lattice has a uniform
nonzero spectral gap.  At every physical time, the weighted actual work is
exactly the endpoint kinetic-scale difference mass.

No path equality, finite cutoff, terminal frequency, kinetic-energy
certificate, or uniqueness conclusion is accepted from a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy

open scoped BigOperators

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuation
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceEnergy

noncomputable section

/-! ## The lattice-generated kinetic weight -/

/-- A nonzero integer wave has squared frequency at least one. -/
theorem one_le_integerWaveNormSq
    (wave : NonzeroIntegerWavevector) :
    1 ≤ integerWaveNormSq wave.1 := by
  obtain ⟨coordinate, coordinateNe⟩ :=
    Function.ne_iff.mp wave.2
  have absOne :
      (1 : ℤ) ≤ |wave.1 coordinate| :=
    Int.one_le_abs coordinateNe
  have absOneReal :
      (1 : ℝ) ≤ |(wave.1 coordinate : ℝ)| := by
    exact_mod_cast absOne
  have coordinateSq :
      (1 : ℝ) ≤ (wave.1 coordinate : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (|(wave.1 coordinate : ℝ)| - 1),
      sq_abs (wave.1 coordinate : ℝ)]
  unfold integerWaveNormSq
  exact coordinateSq.trans <|
    Finset.single_le_sum
      (fun index _ => sq_nonneg (wave.1 index : ℝ))
      (Finset.mem_univ coordinate)

/-- The actual viscous multiplier has a uniform positive spectral gap on
the complete nonzero integer-frequency carrier. -/
theorem twoPiSq_le_integerWaveViscousMultiplier
    (wave : NonzeroIntegerWavevector) :
    (2 * Real.pi) ^ 2 ≤
      integerWaveViscousMultiplier wave.1 := by
  unfold integerWaveViscousMultiplier
  simpa only [mul_one] using
    (mul_le_mul_of_nonneg_left
      (one_le_integerWaveNormSq wave)
      (sq_nonneg (2 * Real.pi)))

theorem integerWaveViscousMultiplier_pos
    (wave : NonzeroIntegerWavevector) :
    0 < integerWaveViscousMultiplier wave.1 := by
  unfold integerWaveViscousMultiplier
  exact mul_pos
    (sq_pos_of_pos (by positivity))
    (integerWaveNormSq_pos wave.2)

/-- Complete kinetic-scale vorticity mass on all nonzero integer waves. -/
def puncturedWholeVorticityKineticMass
    (state : ComplexVorticityHilbertState) : ℝ :=
  ∑' wave : NonzeroIntegerWavevector,
    complexCoordinateAmplitudeSq (state wave.1) /
      integerWaveViscousMultiplier wave.1

/-- The actual spectral gap makes every whole kinetic-scale mass summable. -/
theorem summable_puncturedWholeVorticityKineticMass
    (state : ComplexVorticityHilbertState) :
    Summable fun wave : NonzeroIntegerWavevector =>
      complexCoordinateAmplitudeSq (state wave.1) /
        integerWaveViscousMultiplier wave.1 := by
  have amplitudeSummable :=
    summable_puncturedWholeVorticityEuclideanMass state
  have majorantSummable :
      Summable fun wave : NonzeroIntegerWavevector =>
        complexCoordinateAmplitudeSq (state wave.1) /
          (2 * Real.pi) ^ 2 :=
    amplitudeSummable.div_const ((2 * Real.pi) ^ 2)
  exact
    Summable.of_nonneg_of_le
      (fun wave =>
        div_nonneg
          (complexCoordinateAmplitudeSq_nonneg _)
          (integerWaveViscousMultiplier_pos wave).le)
      (fun wave =>
        div_le_div_of_nonneg_left
          (complexCoordinateAmplitudeSq_nonneg _)
          (sq_pos_of_pos (by positivity))
          (twoPiSq_le_integerWaveViscousMultiplier wave))
      majorantSummable

section SameHorizon

variable
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}

/-- One actual nonzero-wave difference work entry at kinetic scale. -/
def actualWaveDifferenceKineticWork
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (terminal : Icc (0 : ℝ) requestedTime)
    (wave : NonzeroIntegerWavevector) : ℝ :=
  actualWaveDifferenceEnergyWork left right terminal wave /
    integerWaveViscousMultiplier wave.1

/-- Exact kinetic-scale row identity at every physical time. -/
theorem actualWaveDifferenceKineticWork_eq
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (terminal : Icc (0 : ℝ) requestedTime)
    (wave : NonzeroIntegerWavevector) :
    actualWaveDifferenceKineticWork left right terminal wave =
      complexCoordinateAmplitudeSq
          (left.wholePath terminal wave.1 -
            right.wholePath terminal wave.1) /
        integerWaveViscousMultiplier wave.1 := by
  rw [actualWaveDifferenceKineticWork,
    actualWaveDifferenceEnergyWork_eq]

/-- Exact finite-family kinetic-scale difference energy. -/
theorem finiteWaveDifferenceKinetic_endpointEnergy_identity
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (terminal : Icc (0 : ℝ) requestedTime)
    (waves : Finset NonzeroIntegerWavevector) :
    (∑ wave ∈ waves,
        actualWaveDifferenceKineticWork
          left right terminal wave) =
      ∑ wave ∈ waves,
        complexCoordinateAmplitudeSq
            (left.wholePath terminal wave.1 -
              right.wholePath terminal wave.1) /
          integerWaveViscousMultiplier wave.1 := by
  apply Finset.sum_congr rfl
  intro wave waveMem
  exact actualWaveDifferenceKineticWork_eq
    left right terminal wave

/-- The complete actual kinetic-scale difference work is summable. -/
theorem summable_actualWaveDifferenceKineticWork
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (terminal : Icc (0 : ℝ) requestedTime) :
    Summable
      (actualWaveDifferenceKineticWork
        left right terminal) := by
  have endpointSummable :=
    summable_puncturedWholeVorticityKineticMass
      (left.wholePath terminal - right.wholePath terminal)
  exact endpointSummable.congr fun wave => by
    rw [actualWaveDifferenceKineticWork_eq]
    rfl

/--
All nonzero rows assemble into the exact kinetic-scale mass of the actual
whole endpoint difference.
-/
theorem tsum_actualWaveDifferenceKineticWork_eq
    (left right :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (terminal : Icc (0 : ℝ) requestedTime) :
    (∑' wave : NonzeroIntegerWavevector,
        actualWaveDifferenceKineticWork
          left right terminal wave) =
      puncturedWholeVorticityKineticMass
        (left.wholePath terminal - right.wholePath terminal) := by
  rw [show
      (fun wave : NonzeroIntegerWavevector =>
        actualWaveDifferenceKineticWork
          left right terminal wave) =
        fun wave =>
          complexCoordinateAmplitudeSq
              ((left.wholePath terminal -
                right.wholePath terminal) wave.1) /
            integerWaveViscousMultiplier wave.1 by
      funext wave
      rw [actualWaveDifferenceKineticWork_eq]
      rfl]
  rfl

end SameHorizon

end

end ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
end NavierStokes
end SaturationMonoid

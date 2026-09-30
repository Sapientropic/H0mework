import H0mework.NavierStokes.VelocityEndpoint.MacroKineticEnergyAtom
import H0mework.NavierStokes.Galerkin.AmbientNorm
import H0mework.NavierStokes.Fourier.PuncturedEuclideanWholeCarrierMorphism
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Weighted Biot--Savart morphism on the whole endpoint carrier

The kinetic and physical endpoint compilers observe the same actual
whole-restart contacts in two complete `lp²` carriers.  This module installs
the concrete wavewise map between them: undo the inverse-square-root kinetic
weight, then apply the actual Biot--Savart velocity operator.

The resulting bounded complex-linear map commutes with every actual contact
and, by the two generated weak-limit laws on their shared subsequence, sends
the source-selected kinetic endpoint to the physical velocity endpoint.
No endpoint, subsequence, faithfulness law, or target vector is supplied by
a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open scoped ENNReal

open Filter Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open
  ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint.GeneratedWholeRestartVelocityWeakEndpointAtAccumulation

noncomputable section

/-- At one nonzero wave, undo the kinetic inverse-square-root weight and
apply the actual Biot--Savart velocity operator. -/
def wholeRestartKineticToVelocityRowCLM
    (wave : NonzeroIntegerWavevector) :
    ComplexCoordinateEuclidean →L[ℂ] ComplexCoordinateEuclidean :=
  (PiLp.continuousLinearEquiv
      2 ℂ (fun _ : Coordinate => ℂ)).symm.toContinuousLinearMap.comp
    ((biotSavartVelocityLinearMap wave.1).toContinuousLinearMap.comp
      (((Real.sqrt (integerWaveViscousMultiplier wave.1) : ℂ)) •
        (PiLp.continuousLinearEquiv
          2 ℂ (fun _ : Coordinate => ℂ)).toContinuousLinearMap))

@[simp] theorem wholeRestartKineticToVelocityRowCLM_apply
    (wave : NonzeroIntegerWavevector)
    (row : ComplexCoordinateEuclidean) :
    wholeRestartKineticToVelocityRowCLM wave row =
      euclideanCoordinateRow
        (biotSavartVelocityCoefficient wave.1
          ((Real.sqrt
            (integerWaveViscousMultiplier wave.1) : ℂ) •
              WithLp.ofLp row)) := rfl

/-- The weighted Biot--Savart row map is a contraction on the ambient row
carrier.  It is an isometry on the generated transverse subspace, but the
uniform contraction is what is needed to lift it to complete `lp²`. -/
theorem wholeRestartKineticToVelocityRowCLM_norm_sq_le
    (wave : NonzeroIntegerWavevector)
    (row : ComplexCoordinateEuclidean) :
    ‖wholeRestartKineticToVelocityRowCLM wave row‖ ^ 2 ≤
      ‖row‖ ^ 2 := by
  rw [wholeRestartKineticToVelocityRowCLM_apply,
    euclideanCoordinateRow_norm_sq]
  have multiplierPos :
      0 < integerWaveViscousMultiplier wave.1 :=
    integerWaveViscousMultiplier_pos wave
  have sourceNorm :
      complexCoordinateVectorNormSq (WithLp.ofLp row) =
        ‖row‖ ^ 2 := by
    simpa only [euclideanCoordinateRow,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using
      (euclideanCoordinateRow_norm_sq (WithLp.ofLp row)).symm
  calc
    complexCoordinateVectorNormSq
        (biotSavartVelocityCoefficient wave.1
          ((Real.sqrt
            (integerWaveViscousMultiplier wave.1) : ℂ) •
              WithLp.ofLp row)) ≤
      complexCoordinateVectorNormSq
          ((Real.sqrt
            (integerWaveViscousMultiplier wave.1) : ℂ) •
              WithLp.ofLp row) /
        integerWaveViscousMultiplier wave.1 := by
          simpa only [integerWaveViscousMultiplier] using
            biotSavartVelocityCoefficient_normSq_le
              wave.1
              ((Real.sqrt
                (integerWaveViscousMultiplier wave.1) : ℂ) •
                  WithLp.ofLp row)
              wave.2
    _ = ‖row‖ ^ 2 := by
      rw [complexCoordinateVectorNormSq_smul,
        Complex.normSq_ofReal,
        Real.mul_self_sqrt multiplierPos.le, sourceNorm]
      field_simp

/-- Uniform operator-norm bound for the wavewise weighted Biot--Savart
compiler. -/
theorem wholeRestartKineticToVelocityRowCLM_norm_le_one
    (wave : NonzeroIntegerWavevector) :
    ‖wholeRestartKineticToVelocityRowCLM wave‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro row
  have squareLe :=
    wholeRestartKineticToVelocityRowCLM_norm_sq_le wave row
  nlinarith [norm_nonneg
      (wholeRestartKineticToVelocityRowCLM wave row),
    norm_nonneg row]

/-- Concrete whole-carrier residual morphism from weighted vorticity
kinetic rows to physical Biot--Savart velocity rows. -/
def wholeRestartKineticToVelocityCLM :
    WholeRestartKineticEndpointState →L[ℂ]
      WholeRestartVelocityEndpointState :=
  lp.mapCLM 2 wholeRestartKineticToVelocityRowCLM zero_le_one
    wholeRestartKineticToVelocityRowCLM_norm_le_one

@[simp] theorem wholeRestartKineticToVelocityCLM_apply
    (state : WholeRestartKineticEndpointState)
    (wave : NonzeroIntegerWavevector) :
    wholeRestartKineticToVelocityCLM state wave =
      wholeRestartKineticToVelocityRowCLM wave (state wave) := rfl

/-- On every actual source contact, the concrete whole-carrier morphism
commutes with the generated kinetic and physical velocity readouts. -/
theorem wholeRestartKineticToVelocityCLM_contact
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    wholeRestartKineticToVelocityCLM
        (wholeRestartContactKineticState initial index) =
      wholeRestartContactVelocityState initial index := by
  apply lp.ext
  funext wave
  rw [wholeRestartKineticToVelocityCLM_apply]
  change
    wholeRestartKineticToVelocityRowCLM wave
        (puncturedWholeVorticityKineticEuclideanCoefficient
          (run initial index).contact.physicalState wave) =
      puncturedWholeVelocityEuclideanCoefficient
        (run initial index).contact.physicalState wave
  rw [wholeRestartKineticToVelocityRowCLM_apply]
  ext coordinate
  have multiplierPos :
      0 < integerWaveViscousMultiplier wave.1 :=
    integerWaveViscousMultiplier_pos wave
  have sqrtNe :
      Real.sqrt (integerWaveViscousMultiplier wave.1) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 multiplierPos)
  simp [
    puncturedWholeVorticityKineticEuclideanCoefficient,
    puncturedWholeVelocityEuclideanCoefficient,
    euclideanCoordinateRow, sqrtNe]

/-- The same concrete morphism carries the generated kinetic weak endpoint
to the physical velocity weak endpoint on their shared actual subsequence. -/
theorem wholeRestartKineticToVelocityCLM_endpoint
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    {elapsedBounded : BddAbove (Set.range (elapsedTime initial))}
    (receipt :
      GeneratedWholeRestartVelocityWeakEndpointAtAccumulation
        initial elapsedBounded) :
    wholeRestartKineticToVelocityCLM
        receipt.kineticReceipt.endpoint =
      receipt.velocityEndpoint := by
  have mappedWeak
      (test : WholeRestartVelocityEndpointState) :
      Tendsto
        (fun index =>
          inner ℂ
            (wholeRestartKineticToVelocityCLM
              (wholeRestartContactKineticState
                initial (receipt.subsequence index)))
            test)
        atTop
        (nhds
          (inner ℂ
            (wholeRestartKineticToVelocityCLM
              receipt.kineticReceipt.endpoint)
            test)) := by
    have weak :=
      receipt.kinetic_weak_tendsto
        (ContinuousLinearMap.adjoint
          wholeRestartKineticToVelocityCLM test)
    simpa only [
      ContinuousLinearMap.adjoint_inner_right] using weak
  have mappedContactWeak
      (test : WholeRestartVelocityEndpointState) :
      Tendsto
        (fun index =>
          inner ℂ
            (wholeRestartContactVelocityState
              initial (receipt.subsequence index))
            test)
        atTop
        (nhds
          (inner ℂ
            (wholeRestartKineticToVelocityCLM
              receipt.kineticReceipt.endpoint)
            test)) := by
    simpa only [wholeRestartKineticToVelocityCLM_contact] using
      mappedWeak test
  have innerEq
      (test : WholeRestartVelocityEndpointState) :
      inner ℂ
          (wholeRestartKineticToVelocityCLM
            receipt.kineticReceipt.endpoint)
          test =
        inner ℂ receipt.velocityEndpoint test :=
    tendsto_nhds_unique
      (mappedContactWeak test)
      (receipt.velocity_weak_tendsto_shared test)
  let difference :=
    wholeRestartKineticToVelocityCLM
        receipt.kineticReceipt.endpoint -
      receipt.velocityEndpoint
  have selfZero : inner ℂ difference difference = 0 := by
    calc
      inner ℂ difference difference =
          inner ℂ
              (wholeRestartKineticToVelocityCLM
                receipt.kineticReceipt.endpoint)
              difference -
            inner ℂ receipt.velocityEndpoint difference := by
        dsimp only [difference]
        rw [inner_sub_left]
      _ = inner ℂ receipt.velocityEndpoint difference -
            inner ℂ receipt.velocityEndpoint difference := by
        rw [innerEq difference]
      _ = 0 := sub_self _
  have normSqZero : ‖difference‖ ^ 2 = 0 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    exact congrArg Complex.re selfZero
  have differenceZero : difference = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg difference]
  exact sub_eq_zero.mp differenceZero

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid

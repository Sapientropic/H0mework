import H0mework.NavierStokes.PairRestart.SourcePairOccurrence
import H0mework.NavierStokes.Restart.VelocityWeakEndpoint

/-!
# Actual kinetic flux work on one whole restart receipt

This module reads the exact enstrophy work already carried by an actual
`WholeContinuousMildSerrinReceipt` through the rowwise Biot--Savart map.
For a nonzero output, division by the source-owned Laplacian multiplier is
exactly the kinetic pairing.  The resulting net work is the difference of
the terminal and initial velocity-row amplitudes, and its viscous and
bilinear pieces retain the same-receipt balance before any output quotient.

The finite inventory below is a readout parameter.  No analytic bound,
cutoff witness, target state, continuation, or correction premise is used.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualKineticFluxWork

open scoped BigOperators ENNReal

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPreQuotientNonlinearWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence

noncomputable section

/-! ## Same-receipt kinetic row work -/

/-- Net kinetic work of one nonzero output row of the actual receipt. -/
def actualWholeRowKineticNetWork
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt
        nu initialState requestedTime)
    (wave : NonzeroIntegerWavevector) : Real :=
  actualWholeRowNetWork receipt wave.1 /
    integerWaveViscousMultiplier wave.1

/-- The actual positive viscous kinetic work on the identical receipt row. -/
def actualWholeRowKineticViscousWork
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt
        nu initialState requestedTime)
    (wave : NonzeroIntegerWavevector) : Real :=
  actualWholeRowViscousPayment receipt wave.1 /
    integerWaveViscousMultiplier wave.1

/-- The actual whole-bilinear kinetic work before the output is quotiented. -/
def actualWholeRowBilinearKineticWork
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt
        nu initialState requestedTime)
    (wave : NonzeroIntegerWavevector) : Real :=
  actualWholeRowBilinearWork receipt wave.1 /
    integerWaveViscousMultiplier wave.1

/-- One actual row pays exactly its Biot--Savart velocity-amplitude change.
The endpoint transverse laws come from the same continuous whole receipt. -/
theorem actualWholeRowKineticNetWork_eq_terminal_sub_initial
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt
        nu initialState requestedTime)
    (wave : NonzeroIntegerWavevector) :
    actualWholeRowKineticNetWork receipt wave =
      complexCoordinateAmplitudeSq
          (biotSavartVelocityCoefficient wave.1
            (receipt.wholePath
              ⟨requestedTime,
                ⟨receipt.requestedTimePos.le, le_rfl⟩⟩ wave.1)) -
        complexCoordinateAmplitudeSq
          (biotSavartVelocityCoefficient wave.1
            (initialState wave.1)) := by
  let terminal : Set.Icc (0 : Real) requestedTime :=
    ⟨requestedTime, ⟨receipt.requestedTimePos.le, le_rfl⟩⟩
  let initial : Set.Icc (0 : Real) requestedTime :=
    ⟨0, ⟨le_rfl, receipt.requestedTimePos.le⟩⟩
  have terminalTransverse :
      complexWavevector wave.1 ⬝ᵥ
          receipt.wholePath terminal wave.1 = 0 :=
    wholePath_transverse receipt terminal wave.1
  have initialTransverse :
      complexWavevector wave.1 ⬝ᵥ initialState wave.1 = 0 := by
    have transverseAtInitial :=
      wholePath_transverse receipt initial wave.1
    simpa only [initial, receipt.wholePath_initial] using transverseAtInitial
  have terminalVelocitySq :
      complexCoordinateAmplitudeSq
          (receipt.wholePath terminal wave.1) /
          integerWaveViscousMultiplier wave.1 =
        complexCoordinateAmplitudeSq
          (biotSavartVelocityCoefficient wave.1
            (receipt.wholePath terminal wave.1)) := by
    symm
    simpa only [complexCoordinateRealInner_self,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using
      complexCoordinateRealInner_biotSavartVelocityCoefficient
        wave.1 wave.2
        (receipt.wholePath terminal wave.1)
        (receipt.wholePath terminal wave.1)
        terminalTransverse
  have initialVelocitySq :
      complexCoordinateAmplitudeSq (initialState wave.1) /
          integerWaveViscousMultiplier wave.1 =
        complexCoordinateAmplitudeSq
          (biotSavartVelocityCoefficient wave.1
            (initialState wave.1)) := by
    symm
    simpa only [complexCoordinateRealInner_self,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using
      complexCoordinateRealInner_biotSavartVelocityCoefficient
        wave.1 wave.2
        (initialState wave.1) (initialState wave.1)
        initialTransverse
  rw [actualWholeRowKineticNetWork,
    actualWholeRowNetWork_eq_terminal_sub_initial, sub_div,
    show
      receipt.wholePath
          ⟨requestedTime,
            ⟨receipt.requestedTimePos.le, le_rfl⟩⟩ =
        receipt.wholePath terminal by rfl,
    terminalVelocitySq, initialVelocitySq]

/-- Net, viscous, and whole-bilinear kinetic work retain the exact unforced
same-receipt balance. -/
theorem actualWholeRowKineticNetWork_add_viscousWork
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt
        nu initialState requestedTime)
    (wave : NonzeroIntegerWavevector) :
    actualWholeRowKineticNetWork receipt wave +
        actualWholeRowKineticViscousWork receipt wave =
      actualWholeRowBilinearKineticWork receipt wave := by
  unfold actualWholeRowKineticNetWork
    actualWholeRowKineticViscousWork
    actualWholeRowBilinearKineticWork
  rw [← add_div, actualWholeRowNetWork_add_viscousPayment,
    actualWholeRowNonlinearWork_eq_bilinearWork]

/-! ## Finite output inventory -/

/-- Net kinetic work on a finite inventory of actual nonzero output rows. -/
def actualWholeFiniteKineticNetWork
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt
        nu initialState requestedTime)
    (outputs : Finset NonzeroIntegerWavevector) : Real :=
  ∑ wave ∈ outputs, actualWholeRowKineticNetWork receipt wave

/-- Actual positive viscous kinetic work on the identical finite inventory. -/
def actualWholeFiniteKineticViscousWork
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt
        nu initialState requestedTime)
    (outputs : Finset NonzeroIntegerWavevector) : Real :=
  ∑ wave ∈ outputs, actualWholeRowKineticViscousWork receipt wave

/-- Actual whole-bilinear kinetic work on the identical finite inventory. -/
def actualWholeFiniteBilinearKineticWork
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt
        nu initialState requestedTime)
    (outputs : Finset NonzeroIntegerWavevector) : Real :=
  ∑ wave ∈ outputs, actualWholeRowBilinearKineticWork receipt wave

/-- The canonical finite observation of the actual Biot--Savart velocity
carrier.  The output inventory only selects already generated rows. -/
def actualWholeFiniteVelocityObservation
    (outputs : Finset NonzeroIntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    WholeRestartVelocityEndpointState :=
  ∑ wave ∈ outputs,
    lp.single 2 wave
      (puncturedWholeVelocityEuclideanCoefficient state wave)

/-- The finite `lp.single` observation has exactly the sum of the selected
Biot--Savart row-amplitude squares. -/
theorem actualWholeFiniteVelocityObservation_norm_sq
    (outputs : Finset NonzeroIntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    ‖actualWholeFiniteVelocityObservation outputs state‖ ^ 2 =
      ∑ wave ∈ outputs,
        complexCoordinateAmplitudeSq
          (biotSavartVelocityCoefficient wave.1
            (state wave.1)) := by
  classical
  have normSum :=
    lp.norm_sum_single
      (p := (2 : ENNReal)) (by norm_num)
      (fun wave : NonzeroIntegerWavevector =>
        puncturedWholeVelocityEuclideanCoefficient state wave)
      outputs
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at normSum
  simpa only [actualWholeFiniteVelocityObservation,
    puncturedWholeVelocityEuclideanCoefficient,
    euclideanCoordinateRow_norm_sq] using normSum

/-- Finite output rows sum to the exact velocity-amplitude inventory change. -/
theorem actualWholeFiniteKineticNetWork_eq_terminal_sub_initial
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt
        nu initialState requestedTime)
    (outputs : Finset NonzeroIntegerWavevector) :
    actualWholeFiniteKineticNetWork receipt outputs =
      (∑ wave ∈ outputs,
          complexCoordinateAmplitudeSq
            (biotSavartVelocityCoefficient wave.1
              (receipt.wholePath
                ⟨requestedTime,
                  ⟨receipt.requestedTimePos.le, le_rfl⟩⟩ wave.1))) -
        ∑ wave ∈ outputs,
          complexCoordinateAmplitudeSq
            (biotSavartVelocityCoefficient wave.1
              (initialState wave.1)) := by
  unfold actualWholeFiniteKineticNetWork
  simp_rw [actualWholeRowKineticNetWork_eq_terminal_sub_initial]
  rw [Finset.sum_sub_distrib]

/-- The finite kinetic net work is the exact norm-square change of the
terminal and initial Biot--Savart `lp.single` observations of this receipt. -/
theorem actualWholeFiniteKineticNetWork_eq_velocityObservation_norm_sq_sub
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt
        nu initialState requestedTime)
    (outputs : Finset NonzeroIntegerWavevector) :
    actualWholeFiniteKineticNetWork receipt outputs =
      ‖actualWholeFiniteVelocityObservation outputs
          (receipt.wholePath
            ⟨requestedTime,
              ⟨receipt.requestedTimePos.le, le_rfl⟩⟩)‖ ^ 2 -
        ‖actualWholeFiniteVelocityObservation outputs initialState‖ ^ 2 := by
  rw [actualWholeFiniteKineticNetWork_eq_terminal_sub_initial,
    actualWholeFiniteVelocityObservation_norm_sq,
    actualWholeFiniteVelocityObservation_norm_sq]

/-- The exact rowwise kinetic balance survives finite output aggregation. -/
theorem actualWholeFiniteKineticNetWork_add_viscousWork
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt
        nu initialState requestedTime)
    (outputs : Finset NonzeroIntegerWavevector) :
    actualWholeFiniteKineticNetWork receipt outputs +
        actualWholeFiniteKineticViscousWork receipt outputs =
      actualWholeFiniteBilinearKineticWork receipt outputs := by
  unfold actualWholeFiniteKineticNetWork
    actualWholeFiniteKineticViscousWork
    actualWholeFiniteBilinearKineticWork
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro wave _waveMem
  exact actualWholeRowKineticNetWork_add_viscousWork receipt wave

end
end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualKineticFluxWork
end NavierStokes
end SaturationMonoid

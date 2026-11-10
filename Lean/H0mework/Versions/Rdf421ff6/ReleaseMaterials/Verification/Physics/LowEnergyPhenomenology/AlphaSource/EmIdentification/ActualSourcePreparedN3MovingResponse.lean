import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedN3EMConsumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualMovingSourceFullLightReturn

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedN3MovingResponse
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualEMAction
open ActualDressedSylvester
open ActualSourcePreparedNoetherPi ActualSourcePreparedStaticCorrectedReturn
open ActualSourcePreparedEMEnclosure ActualSourcePreparedN3EMConsumer
open ActualMovingSourceFullLightReturnProducer
open PreparationVacuumPhysicalCharacteristic PreparationPhysicalNativePhotonFluxReturn
open ActualCompositeFieldCurrent PhysicalN3SourceEnergy ActualEMResponseSplit
open scoped Matrix BigOperators

def sourceNativeStaticMatrix (epsilon : ℝ) (n : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) ℂ :=
  Matrix.of (sourceWholePhotonGreen epsilon 0 n)

def sourcePreparedNativeConstraint (epsilon : ℝ) (n : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) ℂ :=
  1 - emOriginalJacobi (frequencyRay epsilon 0 n) * sourceNativeStaticMatrix epsilon n

def sourcePreparedClockQuantumMatrix (fieldEvent : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) ℂ :=
  (sigma : ℂ) • Matrix.of (fun i j => sourcePreparedPiEntry fieldEvent ((epsilon^2 : ℝ) • n) (sigma : ℂ) i j)

private theorem full_response_identity {R : Type*} [Ring R] (G J Q N : R)
    (inverse : G * (J-Q) = 1) : G-N = G*Q*N+G*(1-J*N) := by
  have restored := congrArg (fun A : R => A*N) inverse
  rw [mul_sub, sub_mul, one_mul] at restored
  have distribute : G*Q*N+G*(1-J*N) = G-(G*J*N-G*Q*N) := by noncomm_ring
  rw [distribute, restored]

/-- Full corrected-minus-native propagation keeps the original source constraint
deficit. No inverse of the constrained native propagator is assumed. -/
theorem source_prepared_full_native_response (fieldEvent : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma)
    (regular : correctedDet fieldEvent epsilon 0 sigma n ≠ 0) :
    sourcePreparedFullGreenRead fieldEvent epsilon sigma n-sourceNativeStaticMatrix epsilon n =
      sourcePreparedFullGreenRead fieldEvent epsilon sigma n *
        sourcePreparedClockQuantumMatrix fieldEvent epsilon sigma n *
          sourceNativeStaticMatrix epsilon n +
        sourcePreparedFullGreenRead fieldEvent epsilon sigma n * sourcePreparedNativeConstraint epsilon n := by
  have inverse := (source_prepared_static_green_inverse fieldEvent epsilon sigma n positive regular).2
  rw [← source_prepared_full_green_original fieldEvent epsilon sigma n positive regular] at inverse
  change sourcePreparedFullGreenRead fieldEvent epsilon sigma n *
    (emOriginalJacobi (frequencyRay epsilon 0 n) -
      sourcePreparedClockQuantumMatrix fieldEvent epsilon sigma n) = 1 at inverse
  exact full_response_identity _ _ _ _ inverse

def sourcePreparedMovingLightMatrix (fieldEvent : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (reference : SourceCoordinateSlice) (bits : ℕ) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j => movingLightWindow (fieldEvent.momentum-(epsilon^2 : ℝ) • n) fieldEvent.momentum reference
    fieldEvent ((epsilon^2 : ℝ) • n) (sigma : ℂ) bits i j

def sourcePreparedMovingHeavyMatrix (fieldEvent : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (reference : SourceCoordinateSlice) (bits : ℕ) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j => movingHeavyWindow (fieldEvent.momentum-(epsilon^2 : ℝ) • n) fieldEvent.momentum reference
    fieldEvent ((epsilon^2 : ℝ) • n) (sigma : ℂ) bits i j

def sourcePreparedMovingOutsideMatrix (fieldEvent : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (bits : ℕ) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j => movingCrossOutsideWindow fieldEvent ((epsilon^2 : ℝ) • n) (sigma : ℂ) bits i j

def sourcePreparedMovingTailMatrix (fieldEvent : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (bits : ℕ) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j => movingQuantumTail fieldEvent ((epsilon^2 : ℝ) • n) (sigma : ℂ) bits i j

theorem source_prepared_moving_pi_partition (fieldEvent : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (reference : SourceCoordinateSlice) (bits : ℕ) (positive : 0 < sigma) :
    (fun i j => sourcePreparedPiEntry fieldEvent ((epsilon^2 : ℝ) • n) (sigma : ℂ) i j : Matrix (Fin 289) (Fin 289) ℂ) =
      sourcePreparedMovingLightMatrix fieldEvent epsilon sigma n reference bits +
        sourcePreparedMovingHeavyMatrix fieldEvent epsilon sigma n reference bits +
        sourcePreparedMovingOutsideMatrix fieldEvent epsilon sigma n bits +
        sourcePreparedMovingTailMatrix fieldEvent epsilon sigma n bits := by
  ext i j
  have owner := ActualMovingSourceFullLightReturn.of_source
    (fieldEvent.momentum-(epsilon^2 : ℝ) • n) fieldEvent.momentum reference
    fieldEvent ((epsilon^2 : ℝ) • n) (sigma : ℂ) bits i j
  have partition := owner.full_light_partition
  rw [owner.ordinaryFull_from_source, owner.lightResponse_from_source, owner.heavyResponse_from_source,
    owner.crossOutsideResponse_from_source, owner.quantumTail_from_source] at partition
  rw [source_prepared_pi_actual fieldEvent ((epsilon^2 : ℝ) • n) (sigma : ℂ) (by simpa using positive) i j]
  change dressedStaticPolarization fieldEvent ((epsilon^2 : ℝ) • n) (sigma : ℂ) i j = _
  simp only [Matrix.add_apply, sourcePreparedMovingLightMatrix, sourcePreparedMovingHeavyMatrix,
    sourcePreparedMovingOutsideMatrix, sourcePreparedMovingTailMatrix]
  linear_combination partition

def sourcePreparedN3NativeRead (detector source : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) : ℂ :=
  emCurrentObservation (sourceNativeStaticMatrix epsilon n)
    (physicalN3PoleCurrent detector dLeg dPoles) (physicalN3PoleCurrent source sLeg sPoles)

def sourcePreparedN3MovingArm (fieldEvent detector source : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) (A : Matrix (Fin 289) (Fin 289) ℂ) : ℂ :=
  emCurrentObservation
    (sourcePreparedFullGreenRead fieldEvent epsilon sigma n * ((sigma : ℂ) • A) * sourceNativeStaticMatrix epsilon n)
    (physicalN3PoleCurrent detector dLeg dPoles) (physicalN3PoleCurrent source sLeg sPoles)

/-- The actual two-current propagation read consumes all moving polarization
arms and the constrained native response. Contact stays inside the source arms. -/
theorem source_prepared_n3_moving_response (fieldEvent detector source : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (reference : SourceCoordinateSlice) (bits : ℕ) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg)
    (positive : 0 < sigma) (regular : correctedDet fieldEvent epsilon 0 sigma n ≠ 0) :
    sourcePreparedN3Read fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles-
      sourcePreparedN3NativeRead detector source epsilon n dLeg sLeg dPoles sPoles =
    sourcePreparedN3MovingArm fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles
        (sourcePreparedMovingLightMatrix fieldEvent epsilon sigma n reference bits) +
      sourcePreparedN3MovingArm fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles
        (sourcePreparedMovingHeavyMatrix fieldEvent epsilon sigma n reference bits) +
      sourcePreparedN3MovingArm fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles
        (sourcePreparedMovingOutsideMatrix fieldEvent epsilon sigma n bits) +
      sourcePreparedN3MovingArm fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles
        (sourcePreparedMovingTailMatrix fieldEvent epsilon sigma n bits) +
      emCurrentObservation
        (sourcePreparedFullGreenRead fieldEvent epsilon sigma n * sourcePreparedNativeConstraint epsilon n)
        (physicalN3PoleCurrent detector dLeg dPoles) (physicalN3PoleCurrent source sLeg sPoles) := by
  have response := source_prepared_full_native_response fieldEvent epsilon sigma n positive regular
  have quantum : sourcePreparedClockQuantumMatrix fieldEvent epsilon sigma n =
      (sigma : ℂ) • (sourcePreparedMovingLightMatrix fieldEvent epsilon sigma n reference bits +
        sourcePreparedMovingHeavyMatrix fieldEvent epsilon sigma n reference bits +
        sourcePreparedMovingOutsideMatrix fieldEvent epsilon sigma n bits +
        sourcePreparedMovingTailMatrix fieldEvent epsilon sigma n bits) := by
    unfold sourcePreparedClockQuantumMatrix
    change (sigma : ℂ) • (fun i j => sourcePreparedPiEntry fieldEvent ((epsilon^2 : ℝ) • n) (sigma : ℂ) i j : Matrix (Fin 289) (Fin 289) ℂ) = _
    rw [source_prepared_moving_pi_partition fieldEvent epsilon sigma n reference bits positive]
  rw [quantum] at response
  unfold sourcePreparedN3Read sourcePreparedN3NativeRead sourcePreparedN3MovingArm emCurrentObservation
  rw [← dotProduct_sub, ← Matrix.sub_mulVec, response]
  simp only [smul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mulVec, dotProduct_add]

end LowEnergy.GaussComposite.ActualSourcePreparedN3MovingResponse

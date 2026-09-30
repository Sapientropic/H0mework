import H0mework.NavierStokes.CofinalAction.CofinalPairedCurrent
import H0mework.NavierStokes.CofinalAction.CofinalUnifiedControl

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeCofinalCurrentResponse

open Set Filter MeasureTheory UnitAddTorus
open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.Stage9CU.Fluid.CurrentReadout
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open NativePhysicalFourier NativePairedCurrentFourier NativeCofinalPairedCurrent
open NativeCofinalStress NativeStressSource NativeFullOrderSynthesis NativeFullOrderNext
open NativeCofinalUnifiedField (target)
open NativeFluidSpatialOperators (slice)

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {nu : Viscosity}

def regeneratedVelocity (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) : ComplexVorticityHilbertState :=
  NativeCofinalUnifiedAction.velocity initial actual

theorem regenerated_reality (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) :
    FiniteStateFourierReality (regeneratedVelocity initial actual) :=
  NativePhysicalSource.velocity_reality _ (NativePhysicalSource.receipt_reality _ _)

def regenerated (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) (direction : Fin 4) (wave : IntegerWavevector) : ℂ :=
  mFourierCoeff (fun point => (field (regeneratedVelocity initial actual) direction point : ℂ)) wave

def regenerationStress (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) : NativeFluidStressFourierState :=
  quadraticFlux (regeneratedVelocity initial actual) - (sourceGeneratedCofinalStress initial).stress

theorem spatial_response (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) (direction : Fin 3) (wave : IntegerWavevector) :
    regenerated initial actual direction.succ wave - source initial direction.succ wave =
      regeneratedVelocity initial actual wave direction - NativeCofinalMomentumAction.endpointVelocity initial wave direction := by
  rw [regenerated, current_fourier _ (regenerated_reality initial actual)]
  rfl

theorem temporal_response (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) (wave : IntegerWavevector) :
    regenerated initial actual 0 wave - source initial 0 wave = -trace (regenerationStress initial actual) wave / 8 := by
  rw [regenerated, current_fourier _ (regenerated_reality initial actual)]
  change (baseline wave - trace (quadraticFlux (regeneratedVelocity initial actual)) wave / 8) -
    (baseline wave - trace (sourceGeneratedCofinalStress initial).stress wave / 8) = _
  simp only [regenerationStress, trace, Pi.sub_apply, Finset.sum_sub_distrib]
  ring

theorem regenerated_paid (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) :
    Summable fun wave => Real.sqrt (complexCoordinateAmplitudeSq (regeneratedVelocity initial actual wave)) := by
  let time := projIcc (0 : ℝ) (wholeRestartDuration (target initial).contact)
    (NativeCofinalUnifiedField.receipt initial).requestedTimePos.le actual
  have paid := (NativeCofinalUnifiedField.window initial).paid 2 time time.2
  change Summable (fun wave => (NativeFullOrderAction.frequencySize wave ^ 2) ^ 2 *
    ThreeDimensionalVorticityCoefficientStretchingPairTable.complexCoordinateVectorNormSq
      (regeneratedVelocity initial actual wave)) at paid
  have squared : Summable fun wave => NativeFullOrderAction.frequencySize wave ^ (2 * (0 + 2)) *
      complexCoordinateAmplitudeSq (regeneratedVelocity initial actual wave) := by
    simpa only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq, ← pow_mul] using paid
  simpa only [pow_zero, one_mul, NativeFullOrderAction.amplitude,
    ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity.vorticityRowAmplitude] using
      summable_moment_of_square (regeneratedVelocity initial actual) 0 squared

def continuousCurrent (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) (direction : Fin 4) (point : Torus) : ℝ :=
  value (NativePhysicalContinuous.continuousField (regeneratedVelocity initial actual) point) direction

theorem current_ae_original (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) (direction : Fin 4) :
    field (regeneratedVelocity initial actual) direction =ᵐ[volume] continuousCurrent initial actual direction :=
  field_ae_continuous _ (regenerated_paid initial actual) direction

theorem controlled_current_read (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) (direction : Fin 4) (space : PhysicalSpace) :
    current (NativeCofinalUnifiedField.matter initial) (NativeCofinalUnifiedField.dual initial) direction (slice actual space) =
      continuousCurrent initial actual direction (circlePoint space) := by
  change value (NativeCofinalUnifiedField.field initial (slice actual space)) direction = _
  rw [NativeCofinalUnifiedAction.field_velocity]
  rfl

theorem controlled_current_fourier (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ) (direction : Fin 4) (wave : IntegerWavevector) :
    mFourierCoeff (fun point => (continuousCurrent initial actual direction point : ℂ)) wave = regenerated initial actual direction wave := by
  unfold regenerated mFourierCoeff
  apply integral_congr_ae
  filter_upwards [current_ae_original initial actual direction] with point same
  rw [same]

theorem regenerated_next_velocity (initial : GeneratedWholeRestartCurrent nu) :
    regeneratedVelocity initial (target initial).next.contact.time.1 =
      wholeBiotSavartVelocityState (target initial).next.contact.physicalState := by
  unfold regeneratedVelocity NativeCofinalUnifiedAction.velocity NativeReceiptSpacetime.velocity
  rw [NativeReceiptSpacetime.state_on_interval (NativeCofinalUnifiedField.receipt initial) (target initial).next.contact.time]
  rfl

theorem generated_next_current (initial : GeneratedWholeRestartCurrent nu) (direction : Fin 4) (wave : IntegerWavevector) :
    regenerated initial (target initial).next.contact.time.1 direction wave =
      mFourierCoeff (fun point =>
        (field (wholeBiotSavartVelocityState (target initial).next.contact.physicalState) direction point : ℂ)) wave := by
  rw [regenerated, regenerated_next_velocity]

theorem source_mean_defect_nonnegative (initial : GeneratedWholeRestartCurrent nu) :
    0 ≤ (source initial 0 0 - mFourierCoeff
      (fun point => (field (NativeCofinalMomentumAction.endpointVelocity initial) 0 point : ℂ)) 0).re := by
  rw [show source initial = inherited (sourceGeneratedCofinalStress initial) from rfl,
    inherited_temporal_mean_defect]
  apply div_nonneg _ (by norm_num)
  exact ge_of_tendsto' (NativeCofinalKineticIdentity.cofinal_fluctuation_mass_tendsto (sourceGeneratedCofinalStress initial))
    (fun _ => sq_nonneg _)

end
end SaturationMonoid.NavierStokes.NativeCofinalCurrentResponse

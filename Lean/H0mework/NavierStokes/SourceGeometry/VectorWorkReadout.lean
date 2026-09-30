import H0mework.NavierStokes.SourceGeometry.VectorWorkIntegration
import H0mework.NavierStokes.InitialData.FiniteSupportCriticalSobolev

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceFieldRenewal

open MeasureTheory
open scoped Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicLocalEnergyAlgebra
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicUnitCellDivergence
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFinitePhysicalStateRestart
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger

noncomputable section

variable (modes : Finset IntegerWavevector) (zeroNotMem : 0 ∉ modes)
  (negClosed : ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
  (state : ComplexVorticityHilbertState)
  (supported : ∀ wave, wave ∉ modes → state wave = 0)
  (transverse : ∀ wave ∈ modes, complexWavevector wave ⬝ᵥ state wave = 0)
  (reality : FiniteStateFourierReality state)

include zeroNotMem negClosed supported transverse reality

theorem finiteSource_coefficient_eq (wave : IntegerWavevector) :
    generatedVorticityCoefficient (rawSourceOfFiniteVorticityState modes state) wave =
      state wave := by
  have supportEq := rawSourceOfFiniteVorticityState_generatedSupport
    modes zeroNotMem negClosed state
  have compiledEq := generatedComplexVorticityState_rawSourceOfFinitePhysicalState
    modes zeroNotMem negClosed state supported transverse reality
  by_cases inside : wave ∈ modes
  · have supportMem : wave ∈ generatedSupport (rawSourceOfFiniteVorticityState modes state) := by
      rwa [supportEq]
    have applied := congrArg (fun compiled : ComplexVorticityHilbertState => compiled wave) compiledEq
    simpa only [generatedComplexVorticityState_apply, if_pos supportMem] using applied
  · rw [generatedVorticityCoefficient_eq_zero_of_not_mem]
    · exact (supported wave inside).symm
    · rwa [supportEq]

theorem finiteSource_velocity_eq :
    physicalVelocity (rawSourceOfFiniteVorticityState modes state) =
      finiteStateVelocityRealPartField modes state := by
  unfold physicalVelocity finiteStateVelocityRealPartField
  rw [rawSourceOfFiniteVorticityState_generatedSupport modes zeroNotMem negClosed state]
  congr 1
  funext wave
  rw [generatedVelocityCoefficient,
    finiteSource_coefficient_eq modes zeroNotMem negClosed state supported transverse reality]
  rfl

theorem finiteSource_vorticity_parseval :
    (∫ x in physicalUnitCell,
      ‖physicalVorticity (rawSourceOfFiniteVorticityState modes state) x‖ ^ 2) =
      finiteStateVorticityCoefficientEnstrophy modes state := by
  have pointwise (x : PhysicalSpace) :
      ‖physicalVorticity (rawSourceOfFiniteVorticityState modes state) x‖ ^ 2 =
        velocityDot (physicalVorticity (rawSourceOfFiniteVorticityState modes state))
          (physicalVorticity (rawSourceOfFiniteVorticityState modes state)) x := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [velocityDot, pow_two]
  simp_rw [pointwise]
  rw [physicalUnitCell_physicalVorticity_parseval,
    rawSourceOfFiniteVorticityState_generatedSupport modes zeroNotMem negClosed state]
  unfold finiteStateVorticityCoefficientEnstrophy
  apply Finset.sum_congr rfl
  intro wave _
  rw [finiteSource_coefficient_eq modes zeroNotMem negClosed state supported transverse reality,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]

theorem finiteSource_gradient_parseval :
    (∫ x in physicalUnitCell,
      gradientDissipation (physicalVorticity (rawSourceOfFiniteVorticityState modes state)) x) =
      (2 * Real.pi) ^ 2 * finiteStateVorticityEnstrophyMass modes state := by
  rw [physicalUnitCell_physicalVorticity_gradient_parseval,
    rawSourceOfFiniteVorticityState_generatedSupport modes zeroNotMem negClosed state]
  unfold finiteStateVorticityEnstrophyMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro wave _
  rw [finiteSource_coefficient_eq modes zeroNotMem negClosed state supported transverse reality,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  ring

end
end SaturationMonoid.NavierStokes.SourceFieldRenewal

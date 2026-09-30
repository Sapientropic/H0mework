import H0mework.Versions.X.NavierStokes.EscapeAction.EscapeCurrentAction
import H0mework.Versions.X.NavierStokes.RecoveryAction.RecoveryCurrentJets
import H0mework.Versions.X.NavierStokes.SourceAction.JointFilter

set_option autoImplicit false
open scoped BigOperators ENNReal ContDiff Topology

namespace SaturationMonoid.NavierStokes.NativeRecoveryJointCurrent

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open NativeRecoveryUnifiedCurrent NativeRecoveryAEWindows NativeStressSource
open NativeRecoveryEscapeStress NativeRecoveryEscapeCarrier NativeEndpointVelocityCarrier
open NativeTimeJetCarrier NativeStressCurlAlgebra

noncomputable section

variable {nu : Viscosity}

abbrev Time (initial : GeneratedWholeRestartCurrent nu) := Ioo (0 : ℝ) (terminal initial)

def clock (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) : Icc (0 : ℝ) 1 :=
  ⟨time.1, time.2.1.le, time.2.2.le.trans (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.2⟩

def stress (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) : NativeFluidStressFourierState := by
  classical
  exact if regular : time.1 ∈ regularSet (receipt initial) (terminal initial) then quadraticFlux (velocity initial time.1)
    else (sourceStress initial time.1 time.2 regular).stress

theorem stress_regular (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (regular : time.1 ∈ regularSet (receipt initial) (terminal initial)) :
    stress initial time = quadraticFlux (velocity initial time.1) := dif_pos regular

theorem stress_uncovered (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (uncovered : time.1 ∉ regularSet (receipt initial) (terminal initial)) :
    stress initial time = (sourceStress initial time.1 time.2 uncovered).stress := dif_neg uncovered

def current (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) (direction : Fin 4) (wave : IntegerWavevector) : ℂ :=
  NativePairedCurrentFourier.coefficient (velocity initial time.1) (stress initial time) direction wave

def momentum (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) (wave : IntegerWavevector) : ComplexCoordinateVector :=
  projectedDivergenceCLM wave (stress initial time wave) - (nu.coeff * integerWaveViscousMultiplier wave) • velocity initial time.1 wave

def pressure (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) (wave : IntegerWavevector) : ℂ :=
  stressPressureCoefficient wave (stress initial time wave)

def correction (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) (modes : Finset IntegerWavevector) :
    PhysicalSpace → PhysicalSpace := NativeJointStressFilterControl.physicalField modes (velocity initial time.1) (stress initial time)

def budget (initial : GeneratedWholeRestartCurrent nu) : ℝ :=
  ‖(sourceGeneratedNativeTemporalUniformKineticViscousLedgerCore initial).family.endpointReceipt.velocityEndpoint‖ ^ 2

theorem velocity_read (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) :
    velocity initial time.1 = (receipt initial).wholePath (clock initial time) :=
  NativeRecoveryRowAction.velocity_on_interval (receipt initial) (clock initial time)

theorem velocity_mass_le (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) :
    wholeVorticityEuclideanMass (velocity initial time.1) ≤ budget initial := by
  rw [velocity_read]
  have physical := NativeRecoveryPhysical.wholeMild_physical_identity _ (receipt initial) (clock initial time)
  exact (NativePhysicalFourier.realField_norm_sq _ (NativeRecoveryPhysical.wholeMild_reality _ _ _)).symm.trans_le physical.2.2.1

theorem stress_bound (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) (wave : IntegerWavevector) (output input : Coordinate) :
    ‖stress initial time wave output input‖ ≤ budget initial := by
  by_cases regular : time.1 ∈ regularSet (receipt initial) (terminal initial)
  · rw [stress_regular initial time regular]
    exact (quadraticFlux_norm_le_mass _ wave output input).trans (velocity_mass_le initial time)
  · rw [stress_uncovered initial time regular]
    exact (sourceStress initial time.1 time.2 regular).stress_bound wave output input

theorem current_spatial (initial : GeneratedWholeRestartCurrent nu) (time : Time initial) (direction : Fin 3) (wave : IntegerWavevector) :
    current initial time direction.succ wave = NativeRecoveryCurrentAction.physicalCoefficient initial time.1 direction.succ wave := by
  rw [NativeRecoveryCurrentAction.physicalCoefficient_eq]
  rfl

theorem current_regular (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (regular : time.1 ∈ regularSet (receipt initial) (terminal initial)) (direction : Fin 4) (wave : IntegerWavevector) :
    current initial time direction wave = NativeRecoveryCurrentAction.physicalCoefficient initial time.1 direction wave := by
  rw [current, stress_regular initial time regular, NativeRecoveryCurrentAction.physicalCoefficient_eq]

theorem current_uncovered (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (uncovered : time.1 ∉ regularSet (receipt initial) (terminal initial)) (direction : Fin 4) (wave : IntegerWavevector) :
    current initial time direction wave = NativeEscapePairedCurrent.source initial time.1 time.2 uncovered direction wave := by
  rw [current, stress_uncovered initial time uncovered, velocity_read]
  unfold NativeEscapePairedCurrent.source NativeEscapePairedCurrent.inherited
  rw [fixedEndpoint_reads_original]
  rfl

theorem momentum_regular (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (regular : time.1 ∈ regularSet (receipt initial) (terminal initial)) (wave : IntegerWavevector) :
    momentum initial time wave = NativeRecoveryCurrentAction.momentum initial time.1 wave := by
  rw [NativeRecoveryCurrentAction.momentum_row initial time.1 regular, momentum, stress_regular initial time regular]
  rfl

theorem momentum_uncovered (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (uncovered : time.1 ∉ regularSet (receipt initial) (terminal initial)) (wave : IntegerWavevector) :
    momentum initial time wave = NativeRecoveryEscapeMomentum.momentum (sourceStress initial time.1 time.2 uncovered)
      (clock initial time).2.2 wave := by
  rw [momentum, stress_uncovered initial time uncovered, velocity_read]
  unfold NativeRecoveryEscapeMomentum.momentum
  have same : wholeVelocity (fixedEndpoint (NativeRecoveryCoverage.sourceUncoveredAction initial time.1 time.2 uncovered)
      (clock initial time).2.2) = (receipt initial).wholePath (clock initial time) := fixedEndpoint_reads_original _ _
  exact congrArg (fun value : ComplexVorticityHilbertState =>
    projectedDivergenceCLM wave ((sourceStress initial time.1 time.2 uncovered).stress wave) -
      (nu.coeff * integerWaveViscousMultiplier wave) • value wave) same.symm

theorem source_correction_all_order_control (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (modes : Finset IntegerWavevector) :
    ContDiff ℝ ∞ (correction initial time modes) ∧
      ∀ order place, ‖iteratedFDeriv ℝ order (correction initial time modes) place‖ ≤
        NativeJointStressFilterControl.spatialBudget modes (budget initial) order :=
  NativeJointStressFilterControl.spatial_control modes _ _ _ (sq_nonneg _) (stress_bound initial time) (velocity_mass_le initial time)

theorem source_correction_all_order_Lp (initial : GeneratedWholeRestartCurrent nu) (time : Time initial)
    (modes : Finset IntegerWavevector) (order : ℕ) (exponent : ℝ≥0∞) {domain : Set PhysicalSpace} (compact : IsCompact domain) :
    MemLp (iteratedFDeriv ℝ order (correction initial time modes)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (correction initial time modes)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal (NativeJointStressFilterControl.spatialBudget modes (budget initial) order) * volume domain ^ (1 / exponent.toReal) :=
  NativeJointStressFilterControl.spatial_Lp modes _ _ _ (sq_nonneg _) (stress_bound initial time) (velocity_mass_le initial time)
    order exponent compact

end
end SaturationMonoid.NavierStokes.NativeRecoveryJointCurrent

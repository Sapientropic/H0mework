import H0mework.NavierStokes.SourceAction.FinitePrefixChart
import H0mework.NavierStokes.Fourier.NonlinearOutputCompiler
import H0mework.NavierStokes.InitialData.FinitePhysicalStateRestart

set_option autoImplicit false
open scoped BigOperators

namespace SaturationMonoid.NavierStokes.NativeResolvedNonlinearReadout

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFullVorticityStretching
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFinitePhysicalStateRestart
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientNonlinearOutputCompiler
open ThreeDimensionalVorticityCoefficientNonlinearPhysicalBridge
open ThreeDimensionalVorticityCoefficientStretchingOutputCarrier
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw

noncomputable section

def source (radius : ℕ) (state : ComplexVorticityHilbertState) : RawVorticityFourierSource :=
  rawSourceOfFiniteVorticityState (wholeRestartModes radius) (complexSharpSupportProjection (wholeRestartModes radius) state)

theorem source_support (radius : ℕ) (state : ComplexVorticityHilbertState) :
    generatedSupport (source radius state) = wholeRestartModes radius :=
  rawSourceOfFiniteVorticityState_generatedSupport _ (zero_not_mem_puncturedIntegerWaveFrequencyCube radius)
    (fun _ member => puncturedIntegerWaveFrequencyCube_waveNeg_mem radius member) _

theorem source_compiles (radius : ℕ) (state : ComplexVorticityHilbertState)
    (transverse : WholeStateTransverse state) (reality : FiniteStateFourierReality state) :
    generatedComplexVorticityState (source radius state) (generatedSupport (source radius state)) =
      complexSharpSupportProjection (wholeRestartModes radius) state := by
  apply generatedComplexVorticityState_rawSourceOfFinitePhysicalState _
    (zero_not_mem_puncturedIntegerWaveFrequencyCube radius)
    (fun _ member => puncturedIntegerWaveFrequencyCube_waveNeg_mem radius member)
  · intro wave outside
    change wave ∉ wholeRestartModes radius at outside
    simp [complexSharpSupportProjection_apply, outside]
  · intro wave member
    change wave ∈ wholeRestartModes radius at member
    rw [complexSharpSupportProjection_apply, if_pos member]
    exact transverse wave
  · exact complexSharpSupportProjection_reality _ state
      (fun _ member => puncturedIntegerWaveFrequencyCube_waveNeg_mem radius member) reality

theorem source_vorticity_row (radius : ℕ) (state : ComplexVorticityHilbertState)
    (transverse : WholeStateTransverse state) (reality : FiniteStateFourierReality state)
    (wave : IntegerWavevector) (member : wave ∈ wholeRestartModes radius) :
    generatedVorticityCoefficient (source radius state) wave = state wave := by
  have same := congrArg (fun value : ComplexVorticityHilbertState => value wave) (source_compiles radius state transverse reality)
  rwa [generatedComplexVorticityState_apply, source_support, if_pos member,
    complexSharpSupportProjection_apply, if_pos member] at same

theorem velocity_read (radius : ℕ) (state : ComplexVorticityHilbertState)
    (transverse : WholeStateTransverse state) (reality : FiniteStateFourierReality state) :
    physicalVelocity (source radius state) =
      finiteRealComplexFourierField (wholeRestartModes radius)
        (fun wave => biotSavartVelocityCoefficient wave (state wave)) := by
  rw [physicalVelocity, source_support]
  funext space
  apply Finset.sum_congr rfl
  intro wave member
  rw [generatedVelocityCoefficient, source_vorticity_row radius state transverse reality wave member]

theorem vorticity_read (radius : ℕ) (state : ComplexVorticityHilbertState)
    (transverse : WholeStateTransverse state) (reality : FiniteStateFourierReality state) :
    physicalVorticity (source radius state) = finiteRealComplexFourierField (wholeRestartModes radius) state := by
  rw [physicalVorticity, source_support]
  funext space
  apply Finset.sum_congr rfl
  intro wave member
  rw [source_vorticity_row radius state transverse reality wave member]

theorem nonlinear_row (radius : ℕ) (state : ComplexVorticityHilbertState)
    (transverse : WholeStateTransverse state) (reality : FiniteStateFourierReality state) (wave : IntegerWavevector) :
    generatedVorticityNonlinearCoefficientAt (source radius state) wave =
      wholeStateVorticityNonlinearCoefficientAt (complexSharpSupportProjection (wholeRestartModes radius) state) wave := by
  have generated := finiteStateVorticityNonlinearCoefficientAt_generatedSource (source radius state) wave
  rw [source_compiles radius state transverse reality, source_support,
    finiteStateVorticityNonlinearCoefficientAt_projection_of_subset (Finset.Subset.refl _) state wave] at generated
  exact generated.symm.trans (wholeStateVorticityNonlinearCoefficientAt_projection_eq_finite _ state wave).symm

theorem resolved_nonlinear_read (radius : ℕ) (state : ComplexVorticityHilbertState)
    (transverse : WholeStateTransverse state) (reality : FiniteStateFourierReality state) :
    resolvedWholeNonlinearField (wholeRestartModes radius) state =
      -vorticityAdvection (physicalVelocity (source radius state)) + vortexStretching (physicalVelocity (source radius state)) := by
  have coefficients : wholeStateVorticityNonlinearCoefficientAt (complexSharpSupportProjection (wholeRestartModes radius) state) =
      generatedVorticityNonlinearCoefficientAt (source radius state) :=
    funext fun wave => (nonlinear_row radius state transverse reality wave).symm
  change finiteRealComplexFourierField (generatedStretchingOutputInventory (source radius state)) _ = _
  rw [coefficients]
  change generatedVorticityNonlinearOutputField (source radius state) = _
  rw [← generatedVorticityNonlinearPairField_eq_outputField]
  exact generatedVorticityNonlinearPairField_eq_physicalNonlinearity _

theorem source_resolved_nonlinear (index radius : ℕ) (actual : ℝ) :
    let state := NativeReceiptSpacetime.state (NativeFinitePrefixTimeChart.receipt index) actual
    resolvedWholeNonlinearField (wholeRestartModes radius) state =
      -vorticityAdvection (physicalVelocity (source radius state)) + vortexStretching (physicalVelocity (source radius state)) := by
  apply resolved_nonlinear_read _ _
    (NativeReceiptSpacetime.state_transverse (NativeFinitePrefixTimeChart.receipt index) actual)
  exact NativePhysicalSource.receipt_reality _ _

end
end SaturationMonoid.NavierStokes.NativeResolvedNonlinearReadout

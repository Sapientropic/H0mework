import H0mework.Versions.X.NavierStokes.NativeAction.Carrier
import H0mework.Versions.X.NavierStokes.NativeAction.Write
import H0mework.Versions.X.NavierStokes.NativeAction.Correction

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeCompleteEvolution

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeCompleteStressAction NativeEndpointVelocityCarrier
open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.StageNineCanonicalCauchyState
open PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

noncomputable section

def nativeRow (nu : Viscosity) (modes : Finset IntegerWavevector) (value : FullSpace)
    (wave : IntegerWavevector) : ComplexCoordinateVector :=
  NativeCompleteAction.resolvedGenerator nu modes value wave +
    NativeWholeVelocityFilterControl.coefficient modes (wholeVelocity value.fst) wave +
    nativeFluidConstitutiveVorticityAction
      (NativeRecoveryEscapeCorrection.projectStress modes (NativeCompleteCorrectionRead.residual value)) wave

theorem nativeRow_is_complete_action (nu : Viscosity) (modes : Finset IntegerWavevector)
    (value : FullSpace) (wave : IntegerWavevector) :
    nativeRow nu modes value wave = NativeCompleteAction.filteredAction nu modes value wave := by
  have correction := congrFun (NativeCompleteCorrectionRead.correction_action modes value) wave
  change NativeCompleteAction.correction modes value wave =
    NativeWholeVelocityFilterControl.coefficient modes (wholeVelocity value.fst) wave +
      nativeFluidConstitutiveVorticityAction
        (NativeRecoveryEscapeCorrection.projectStress modes (NativeCompleteCorrectionRead.residual value)) wave at correction
  rw [nativeRow, add_assoc, ← correction]
  exact (NativeCompleteAction.full_native_action nu modes value wave).symm

def nativeRHS (nu : Viscosity) (modes : Finset IntegerWavevector) (value : FullSpace) :
    ComplexVorticityHilbertState :=
  finiteComplexVorticityState (NativeFixedFilterGlobalControl.outputInventory modes)
    (nativeRow nu modes value)

theorem nativeRHS_apply (nu : Viscosity) (modes : Finset IntegerWavevector)
    (value : FullSpace) (wave : IntegerWavevector) :
    nativeRHS nu modes value wave = nativeRow nu modes value wave := by
  rw [nativeRHS, finiteComplexVorticityState_apply]
  split_ifs with inside
  · rfl
  · have outside : wave ∉ modes := fun member => inside (Finset.mem_union_left _ member)
    rw [nativeRow_is_complete_action, NativeCompleteAction.filteredAction, if_neg outside]

variable {nu : Viscosity}

theorem source_nativeRHS (modes : Finset IntegerWavevector) (seed : GeneratedWholeRestartCurrent nu)
    (time : ℝ) :
    nativeRHS nu modes (NativeUnifiedCompleteSource.source seed time) =
      NativeCompleteFilteredWrite.action modes seed time := by
  apply lp.ext
  funext wave
  rw [nativeRHS_apply, nativeRow_is_complete_action, NativeCompleteFilteredWrite.action_apply]
  rfl

theorem source_hasDerivAt_ae (modes : Finset IntegerWavevector) (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 < time →
      HasDerivAt (NativeCompleteFilteredWrite.state modes seed)
        (nativeRHS nu modes (NativeUnifiedCompleteSource.source seed time)) time := by
  simpa only [source_nativeRHS] using NativeCompleteFilteredWrite.source_hasDerivAt_ae modes seed

theorem source_integral (modes : Finset IntegerWavevector) (seed : GeneratedWholeRestartCurrent nu)
    (a b : ℝ) (a_nonnegative : 0 ≤ a) (b_nonnegative : 0 ≤ b) :
    NativeCompleteFilteredWrite.state modes seed b - NativeCompleteFilteredWrite.state modes seed a =
      ∫ time in a..b, nativeRHS nu modes (NativeUnifiedCompleteSource.source seed time) := by
  simp only [source_nativeRHS]
  exact NativeCompleteFilteredWrite.source_integral modes seed a b a_nonnegative b_nonnegative

/-- The original writer consumes all three native action channels. -/
def generatedState (modes : Finset IntegerWavevector) (seed : GeneratedWholeRestartCurrent nu)
    (point : BasePoint) : ComplexVorticityHilbertState :=
  NativeCompleteFilteredWrite.state modes seed 0 +
    canonicalTimePrimitive (fun point =>
      nativeRHS nu modes (NativeUnifiedCompleteSource.source seed (canonicalTimeProjection point))) point

theorem source_primitive (modes : Finset IntegerWavevector) (seed : GeneratedWholeRestartCurrent nu)
    (time : ℝ) (nonnegative : 0 ≤ time) (space : StageNineSpatialPoint) :
    generatedState modes seed (canonicalCauchySlicePoint time space) =
      NativeCompleteFilteredWrite.state modes seed time := by
  simp only [generatedState, source_nativeRHS]
  exact NativeCompleteFilteredWrite.source_primitive modes seed time nonnegative space

theorem complete_source_generated_next (modes : Finset IntegerWavevector)
    (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    (nativeRHS nu modes (NativeUnifiedCompleteSource.source seed (response.2.clockAdvance + time)),
      NativeCompleteCorrectionRead.residual (NativeUnifiedCompleteSource.source seed (response.2.clockAdvance + time))) =
    (nativeRHS nu modes (NativeUnifiedCompleteSource.source response.1 time),
      NativeCompleteCorrectionRead.residual (NativeUnifiedCompleteSource.source response.1 time)) := by
  rw [NativeUnifiedCompleteSource.source_generated_next seed response generated time nonnegative]

theorem generatedState_next (modes : Finset IntegerWavevector) (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) (space : StageNineSpatialPoint) :
    generatedState modes seed (canonicalCauchySlicePoint (response.2.clockAdvance + time) space) =
      generatedState modes response.1 (canonicalCauchySlicePoint time space) := by
  rw [source_primitive modes seed _ (add_nonneg response.2.clockAdvance_pos.le nonnegative),
    source_primitive modes response.1 time nonnegative,
    NativeCompleteFilteredWrite.state_generated_next modes seed response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeCompleteEvolution

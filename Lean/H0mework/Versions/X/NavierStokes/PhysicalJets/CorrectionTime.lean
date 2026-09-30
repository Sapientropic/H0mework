import H0mework.Versions.X.NavierStokes.TimeJets.TimeSource
import H0mework.Versions.X.NavierStokes.PhysicalJets.Correction

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeCorrectionTime

open Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeStressCurlAlgebra NativeStressSource NativeHigherTimeJets NativeHigherTimeJetsSource
open NativeFullOrderCorrection

noncomputable section

def projectionCLM (modes : Finset IntegerWavevector) :
    ComplexVorticityHilbertState →L[ℝ] ComplexVorticityHilbertState :=
  ∑ wave ∈ modes,
    (lp.singleContinuousLinearMap ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).comp
      (lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave)

@[simp] theorem projectionCLM_apply (modes : Finset IntegerWavevector) (state : ComplexVorticityHilbertState) :
    projectionCLM modes state = complexSharpSupportProjection modes state := by
  simp only [projectionCLM, sum_apply, ContinuousLinearMap.comp_apply,
    lp.singleContinuousLinearMap_apply, complexSharpSupportProjection,
    finiteComplexVorticityState]
  rfl

theorem velocity_projection_commutes (modes : Finset IntegerWavevector) (state : ComplexVorticityHilbertState) :
    wholeBiotSavartVelocityState (complexSharpSupportProjection modes state) =
      complexSharpSupportProjection modes (wholeBiotSavartVelocityState state) := by
  apply lp.ext
  funext wave
  by_cases inside : wave ∈ modes <;>
    simp [wholeBiotSavartVelocityState_apply, finiteStateVelocityCoefficient,
      complexSharpSupportProjection_apply, inside]

def quadraticRate (velocity rate : ComplexVorticityHilbertState) : NativeFluidStressFourierState :=
  mixedFlux rate velocity + mixedFlux velocity rate

def correctionRateStress (modes : Finset IntegerWavevector)
    (velocity rate : ComplexVorticityHilbertState) : NativeFluidStressFourierState :=
  (fun wave => if wave ∈ modes then quadraticRate velocity rate wave else 0) -
    quadraticRate (complexSharpSupportProjection modes velocity) (complexSharpSupportProjection modes rate)

def correctionRate (modes : Finset IntegerWavevector) (index : ℕ) (actual : ℝ) : NativeFluidVorticityTangent :=
  nativeFluidConstitutiveVorticityAction
    (correctionRateStress modes (sourceVelocity index actual) (sourceRate index actual))

def sourceState (index : ℕ) (actual : ℝ) : ComplexVorticityHilbertState :=
  (run stackedShortCurrent index).receipt.wholePath
    (projIcc (0 : ℝ) _ (run stackedShortCurrent index).receipt.requestedTimePos.le actual)

theorem sourceState_on_interval (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    sourceState index time.1 = (run stackedShortCurrent index).receipt.wholePath time := by
  unfold sourceState
  rw [projIcc_of_mem (run stackedShortCurrent index).receipt.requestedTimePos.le time.2]

theorem source_correction_tensor_hasDerivWithinAt (modes : Finset IntegerWavevector) (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) (wave : IntegerWavevector) :
    HasDerivWithinAt (fun actual => correctionStress modes (sourceState index actual) wave)
      (correctionRateStress modes (sourceVelocity index time.1) (sourceRate index time.1) wave)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 := by
  have original := sourceVelocity_hasDerivWithinAt index time
  have projected := (projectionCLM modes).hasFDerivAt.comp_hasDerivWithinAt time.1 original
  apply hasDerivWithinAt_pi.mpr
  intro output
  apply hasDerivWithinAt_pi.mpr
  intro input
  have first := source_quadraticFlux_hasDerivWithinAt index time wave output input
  have second := mixedFlux_hasDerivWithinAt projected projected wave output input
  simp only [projectionCLM_apply, Function.comp_def, mixedFlux_diagonal] at second
  by_cases inside : wave ∈ modes
  · convert! first.sub second using 1 <;>
      simp only [correctionStress, velocity_projection_commutes, correctionRateStress, quadraticRate,
        Pi.add_apply, Pi.sub_apply, if_pos inside, sourceState, sourceVelocity]
    rfl
  · convert! (hasDerivWithinAt_const time.1 (Icc (0 : ℝ) (run stackedShortCurrent index).duration)
      (0 : ℂ)).sub second using 1 <;>
      simp only [correctionStress, velocity_projection_commutes, correctionRateStress, quadraticRate,
        Pi.add_apply, Pi.sub_apply, if_neg inside, Pi.zero_apply, sourceState, sourceVelocity]
    rfl

theorem source_native_correction_hasDerivWithinAt (modes : Finset IntegerWavevector) (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) (wave : IntegerWavevector) :
    HasDerivWithinAt (fun actual => nativeTurbulenceCorrectionAt modes (sourceState index actual) wave)
      (correctionRate modes index time.1 wave)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 := by
  let action := ((fourierCurlCoefficientContinuousLinearMap wave).comp
    (stressDivergenceCLM wave)).restrictScalars ℝ
  have derivative := action.hasFDerivAt.comp_hasDerivWithinAt time.1
    (source_correction_tensor_hasDerivWithinAt modes index time wave)
  have same : (fun actual => action (correctionStress modes (sourceState index actual) wave)) =
      fun actual => nativeTurbulenceCorrectionAt modes (sourceState index actual) wave := by
    funext actual
    exact correctionStress_action modes _
      ((run stackedShortCurrent index).receipt.wholePath_zero_row _) (wholePath_transverse _ _) wave
  change HasDerivWithinAt (fun actual => action (correctionStress modes (sourceState index actual) wave))
    (correctionRate modes index time.1 wave) _ _ at derivative
  rwa [same] at derivative

end
end SaturationMonoid.NavierStokes.NativeCorrectionTime

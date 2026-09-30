import H0mework.NavierStokes.PhysicalJets.CurlCross
import H0mework.NavierStokes.ResolvedAction.ResolvedViscousReadout
import H0mework.NavierStokes.WholeHistory.WholeHistoryPhysicalAction

set_option autoImplicit false
open scoped ContDiff Topology

namespace SaturationMonoid.NavierStokes.NativeResolvedSpacetime

open Set Filter
open PhysicsCore.ProofFreeRicherAnholonomicSource
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open NativeFullOrderSynthesis NativeSpacetimeControl NativeReceiptTimeProfile
open NativeWholeHistoryClock NativeWholeHistoryField
open NativeFinitePrefixTimeChart (spatialRead spatialRead_contDiff)

noncomputable section

theorem receipt_state_contDiffOn (length : ℕ) :
    ContDiffOn ℝ ∞ (NativeReceiptSpacetime.state (receipt length))
      (Icc (0 : ℝ) (NativeWholeHistoryClock.duration length)) := by
  have original := observed_chain_smooth (NativeReceiptSpacetime.vorticityFamily (window length))
    (NativePolynomialObservations.curl_evolves (jets (window length)) (jets_evolve (window length)))
    (ContinuousLinearMap.id ℝ ComplexVorticityHilbertState)
  simp only [ContinuousLinearMap.id_apply] at original
  have coordinate : ContDiff ℝ ∞ (NativeReceiptSpacetime.inverse (window length)) :=
    (contDiff_id.sub contDiff_const).div_const _
  have composed := original.comp coordinate.contDiffOn (NativeReceiptSpacetime.inverse_mem (window length))
  exact composed.congr fun actual inside => (NativeReceiptSpacetime.vorticity_read (window length) actual inside).symm

theorem vorticity_contDiff : ContDiff ℝ ∞ vorticity := by
  apply contDiff_iff_contDiffAt.mpr
  intro parameter
  have original := (receipt_state_contDiffOn (cover parameter)).contDiffAt
    (Icc_mem_nhds (physicalTime_pos parameter) (cover_spec parameter))
  exact (original.comp parameter physicalTime_contDiff.contDiffAt).congr_of_eventuallyEq
    (NativeWholeHistoryAction.vorticity_locally parameter)

theorem coefficientReal_contDiff : ContDiff ℝ ∞ coefficientReal := by
  apply (contDiff_piLp 2).mpr
  intro direction
  exact Complex.reCLM.contDiff.comp (ContinuousLinearMap.proj direction : ComplexCoordinateVector →L[ℝ] ℂ).contDiff

theorem coefficientImag_contDiff : ContDiff ℝ ∞ coefficientImag := by
  apply (contDiff_piLp 2).mpr
  intro direction
  exact Complex.imCLM.contDiff.comp (ContinuousLinearMap.proj direction : ComplexCoordinateVector →L[ℝ] ℂ).contDiff

def observation (modes : Finset IntegerWavevector)
    (read : IntegerWavevector → ComplexVorticityHilbertState →L[ℝ] ComplexCoordinateVector)
    (point : BasePoint) : PhysicalSpace :=
  finiteRealComplexFourierField modes (fun wave => read wave (vorticity (point 0))) (spatialRead point)

theorem observation_contDiff (modes : Finset IntegerWavevector)
    (read : IntegerWavevector → ComplexVorticityHilbertState →L[ℝ] ComplexCoordinateVector) :
    ContDiff ℝ ∞ (observation modes read) := by
  have stateSmooth : ContDiff ℝ ∞ (fun point : BasePoint => vorticity (point 0)) :=
    vorticity_contDiff.comp (contDiff_piLp_apply 2)
  apply ContDiff.sum
  intro wave _
  have coefficient := (read wave).contDiff.comp stateSmooth
  exact (((ThreeDimensionalPeriodicIntegerCharacterUnitCellMean.integerCosine_contDiff wave).comp spatialRead_contDiff).smul
    (coefficientReal_contDiff.comp coefficient)).sub
      (((ThreeDimensionalPeriodicIntegerCharacterUnitCellMean.integerSine_contDiff wave).comp spatialRead_contDiff).smul
        (coefficientImag_contDiff.comp coefficient))

def resolvedVorticity (modes : Finset IntegerWavevector) : BasePoint → PhysicalSpace :=
  observation modes (fun wave => lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave)

def resolvedVelocity (modes : Finset IntegerWavevector) : BasePoint → PhysicalSpace :=
  observation modes (fun wave => (ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger.biotSavartVelocityCLM wave).comp
    (lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave))

theorem resolvedVorticity_contDiff (modes : Finset IntegerWavevector) : ContDiff ℝ ∞ (resolvedVorticity modes) :=
  observation_contDiff modes _

theorem resolvedVelocity_contDiff (modes : Finset IntegerWavevector) : ContDiff ℝ ∞ (resolvedVelocity modes) :=
  observation_contDiff modes _

theorem slice_vorticity (modes : Finset IntegerWavevector) (parameter : ℝ) :
    NativeFluidSpatialOperators.restrict (resolvedVorticity modes) parameter =
      finiteRealComplexFourierField modes (vorticity parameter) := by
  funext space
  have spatial : spatialRead (NativeFluidSpatialOperators.slice parameter space) = space := by
    apply PiLp.ext
    intro direction
    exact NativeFluidSpatialOperators.slice_spatial parameter space direction
  unfold NativeFluidSpatialOperators.restrict resolvedVorticity observation
  rw [Function.comp_apply, NativeFluidSpatialOperators.slice_time, spatial]
  rfl

theorem slice_velocity (modes : Finset IntegerWavevector) (parameter : ℝ) :
    NativeFluidSpatialOperators.restrict (resolvedVelocity modes) parameter =
      finiteRealComplexFourierField modes (fun wave => biotSavartVelocityCoefficient wave (vorticity parameter wave)) := by
  funext space
  have spatial : spatialRead (NativeFluidSpatialOperators.slice parameter space) = space := by
    apply PiLp.ext
    intro direction
    exact NativeFluidSpatialOperators.slice_spatial parameter space direction
  unfold NativeFluidSpatialOperators.restrict resolvedVelocity observation
  rw [Function.comp_apply, NativeFluidSpatialOperators.slice_time, spatial]
  rfl

end
end SaturationMonoid.NavierStokes.NativeResolvedSpacetime

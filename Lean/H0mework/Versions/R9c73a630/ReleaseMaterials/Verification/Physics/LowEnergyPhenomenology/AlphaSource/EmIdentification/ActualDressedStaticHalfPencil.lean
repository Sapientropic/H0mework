import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticPolarization
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNativeSignalLaplaceReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMAction

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedStaticResponse
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open PreparationVacuumCurrentNativeLaplaceBridge PreparationVacuumOriginalGreenFeedback
open SourcePropagationNativeActionHessian
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualDressedSylvester ActualEMAction
open Filter Set MeasureTheory
open scoped Topology Matrix BigOperators Interval
attribute [local irreducible] dressedSignalWindow dressedSignalHalfOperator dressedWindowPolarization
  dressedStaticPolarization dressedClassicalTimeFactor dressedNativeWindowPencil nativeHessian emOriginalJacobi

/-- The original constant-input factor is generated before any response amputation. -/
theorem static_classical_time_factor (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) :
    dressedClassicalTimeFactor p lambda T=sourcePlaneWindowScalar (p 0) lambda T := by
  unfold dressedClassicalTimeFactor sourcePlaneWindowScalar
  apply intervalIntegral.integral_congr
  intro t _
  change laplaceWeight lambda t*Complex.exp ((t:ℂ)*p 0)=Complex.exp ((p 0-lambda)*(t:ℂ))
  rw [laplaceWeight,←Complex.exp_add]
  congr 1
  ring

theorem static_classical_time_factor_limit (p : Fin 4→ℂ) (static : p 0=0)
    (lambda : ℂ) (positive : 0<lambda.re) :
    Tendsto (dressedClassicalTimeFactor p lambda) atTop (𝓝 (lambda⁻¹)) := by
  have original:=sourcePlaneWindowScalar_limit (p 0) lambda
    (show (p 0).re<lambda.re by simpa only [static,Complex.zero_re] using positive)
  have same : dressedClassicalTimeFactor p lambda=sourcePlaneWindowScalar (p 0) lambda :=
    funext (static_classical_time_factor p lambda)
  rw [same]
  simpa only [static,sub_zero] using! original

theorem static_polarization_window_limit (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (static : p 0=0) (lambda : ℂ) (positive : 0<lambda.re) :
    Tendsto (dressedWindowPolarization event transfer p lambda) atTop
      (𝓝 (dressedStaticPolarization event transfer lambda)) := by
  have off : sourceClockGrowth p<lambda.re := by
    simpa only [sourceClockGrowth,static,Complex.zero_re,max_self] using positive
  have operators:=dressed_signal_window_operator_norm event transfer p lambda off
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  have applied:=((ContinuousLinearMap.apply ℝ (Fin 289→ℂ) (Pi.single j 1)).continuous.tendsto
    (dressedSignalHalfOperator event transfer p lambda)).comp operators
  have coordinate:=((continuous_apply i).tendsto
    (dressedSignalHalfOperator event transfer p lambda (Pi.single j 1))).comp applied
  have finite (T : ℝ) : dressedSignalWindow event transfer p lambda T (Pi.single j 1) i=
      dressedWindowPolarization event transfer p lambda T i j := by
    simpa only [Matrix.mulVec_single_one,Matrix.col_apply] using!
      congrFun (dressed_window_polarization_actual event transfer p lambda T (Pi.single j 1)) i
  simpa only [Function.comp_def,ContinuousLinearMap.apply_apply,finite,
    dressed_static_polarization_actual event transfer p static lambda positive i j] using! coordinate

/-- The halfline pencil keeps the original action and the complete actual quantum response. -/
def staticHalfPencil (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  lambda⁻¹ • emOriginalJacobi p-dressedStaticPolarization event transfer lambda

attribute [local irreducible] staticHalfPencil

theorem static_half_pencil_limit (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (static : p 0=0) (lambda : ℂ) (positive : 0<lambda.re) :
    Tendsto (dressedNativeWindowPencil event transfer p lambda) atTop
      (𝓝 (staticHalfPencil event transfer p lambda)) := by
  have classical:=static_classical_time_factor_limit p static lambda positive
  have quantum:=static_polarization_window_limit event transfer p static lambda positive
  have action : nativeFourierHessian nativeHessian p=emOriginalJacobi p :=
    (nativeActionFourierHessian_original p).trans (em_jacobi_source p).symm
  have combined:=(classical.smul (tendsto_const_nhds (x:=emOriginalJacobi p))).sub quantum
  unfold staticHalfPencil dressedNativeWindowPencil
  simpa only [action] using! combined

end LowEnergy.GaussComposite.ActualDressedStaticResponse

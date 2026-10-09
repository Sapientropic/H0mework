import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticAmputation

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedFrequencyHalf
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open PreparationVacuumPhysicalHalfAxis PreparationVacuumCurrentNativeLaplaceBridge
open SourcePropagationNativeActionHessian
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualDressedSylvester ActualDressedStaticResponse ActualEMAction
open Filter Set MeasureTheory
open scoped Topology Matrix BigOperators Interval
attribute [local irreducible] dressedSignalHalfOperator dressedSignalWindow dressedSignalWeighted
  dressedSignalQuadrature dressedSignalMatrix dressedWindowPolarization dressedNativeWindowPencil
  dressedClassicalTimeFactor emOriginalJacobi nativeHessian

/-- Every halfline entry reads the same complete actual quantum operator. -/
def frequencyHalfPolarization (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j=>dressedSignalHalfOperator event transfer p lambda (Pi.single j 1) i

attribute [local irreducible] frequencyHalfPolarization

theorem frequency_half_polarization_integral (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (off : sourceClockGrowth p<lambda.re) (i j : Fin 289) :
    frequencyHalfPolarization event transfer p lambda i j=
      ∫t in Ioi (0:ℝ),laplaceWeight lambda t*dressedSignalMatrix event transfer p t i j := by
  have integrable:=dressed_signal_weighted_integrable event transfer p lambda off
  have applied:=(ContinuousLinearMap.apply ℝ (Fin 289→ℂ) (Pi.single j 1)).integrable_comp integrable
  have coordinate:=(ContinuousLinearMap.proj i : (Fin 289→ℂ)→L[ℝ]ℂ).integral_comp_comm applied
  simp only [ContinuousLinearMap.proj_apply,ContinuousLinearMap.apply_apply] at coordinate
  have first : frequencyHalfPolarization event transfer p lambda i j=
      (∫t in Ioi (0:ℝ),dressedSignalWeighted event transfer p lambda t (Pi.single j 1)) i := by
    unfold frequencyHalfPolarization dressedSignalHalfOperator
    exact congrFun (ContinuousLinearMap.integral_apply integrable (Pi.single j 1)) i
  have last : (∫t in Ioi (0:ℝ),dressedSignalWeighted event transfer p lambda t (Pi.single j 1)) i=
      ∫t in Ioi (0:ℝ),laplaceWeight lambda t*dressedSignalMatrix event transfer p t i j := by
    simpa only [dressedSignalWeighted,smul_apply,Pi.smul_apply,smul_eq_mul,
      dressedSignalMatrix,dressed_signal_complex_original] using! coordinate.symm
  exact first.trans last

theorem frequency_polarization_window_limit (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (off : sourceClockGrowth p<lambda.re) :
    Tendsto (dressedWindowPolarization event transfer p lambda) atTop
      (𝓝 (frequencyHalfPolarization event transfer p lambda)) := by
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
    frequencyHalfPolarization] using! coordinate

theorem frequency_polarization_tail (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (off : sourceClockGrowth p<lambda.re)
    (T : ℝ) (future : 0≤T) (i j : Fin 289) :
    ‖frequencyHalfPolarization event transfer p lambda i j-
      dressedWindowPolarization event transfer p lambda T i j‖ ≤
        dressedSignalTailPrice event transfer p lambda T := by
  have window:=congrFun
    (dressed_window_polarization_actual event transfer p lambda T (Pi.single j 1)) i
  simp only [Matrix.mulVec_single_one,Matrix.col_apply] at window
  let A:=dressedSignalHalfOperator event transfer p lambda-dressedSignalWindow event transfer p lambda T
  have difference : frequencyHalfPolarization event transfer p lambda i j-
      dressedWindowPolarization event transfer p lambda T i j=(A (Pi.single j 1)) i :=
    congrArg₂ (fun x y : ℂ=>x-y) (by unfold frequencyHalfPolarization;rfl) window.symm
  refine (congrArg norm difference).le.trans ((norm_le_pi_norm (A (Pi.single j 1)) i).trans ?_)
  have applied : ‖A (Pi.single j 1)‖≤‖A‖ := by
    simpa only [Pi.norm_single,norm_one,mul_one] using A.le_opNorm (Pi.single j 1)
  exact applied.trans (dressed_signal_half_operator_tail event transfer p lambda off T future)

def frequencyHalfPencil (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  (lambda-p 0)⁻¹ • emOriginalJacobi p-frequencyHalfPolarization event transfer p lambda

attribute [local irreducible] frequencyHalfPencil

theorem frequency_half_pencil_limit (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (off : sourceClockGrowth p<lambda.re) :
    Tendsto (dressedNativeWindowPencil event transfer p lambda) atTop
      (𝓝 (frequencyHalfPencil event transfer p lambda)) := by
  have inputOff : (p 0).re<lambda.re := (le_max_right 0 (p 0).re).trans_lt off
  have classical:=sourcePlaneWindowScalar_limit (p 0) lambda inputOff
  have same : dressedClassicalTimeFactor p lambda=sourcePlaneWindowScalar (p 0) lambda :=
    funext (static_classical_time_factor p lambda)
  rw [←same] at classical
  have quantum:=frequency_polarization_window_limit event transfer p lambda off
  have action : nativeFourierHessian nativeHessian p=emOriginalJacobi p :=
    (nativeActionFourierHessian_original p).trans (em_jacobi_source p).symm
  have combined:=(classical.smul (tendsto_const_nhds (x:=emOriginalJacobi p))).sub quantum
  unfold frequencyHalfPencil dressedNativeWindowPencil
  simpa only [action] using! combined

end LowEnergy.GaussComposite.ActualDressedFrequencyHalf

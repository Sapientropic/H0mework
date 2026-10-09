import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMStaticReaderRecognition
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePhysicalPoleLaplace
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualPreparedDetector

/-! Actual static window: the original `fiveKernel`-shaped material
kernel at gauge slots `21`/`34` splits into the local mode kernel plus
the retained compensation kernel, so the actual origin weight returns
`-c ∫ (raw)` as the full `-c ∫ full` plus `+c ∫ correction` age windows
over the ORIGINAL `physicalTime`/`jointResolvent` legs. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalEMActualStaticWindow
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumFullFieldRiesz PreparationVacuumFieldConstraintResponse
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open PreparationPhysicalStaticCompositeProjectionReturn PreparationVacuumSourceActionJets
open PreparationVacuumGaugeSourceInjection PreparationVacuumJointFieldResponse
open PreparationVacuumPhysicalFeedback PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumStaticPoleResponse
open PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalQuantumLockedCharge
open PreparationPhysicalActualGaussChargeCurrent PreparationVacuumFullOriginResponse
open CanonicalGradedSpatialSource PreparationVacuumActionFieldLift
open GaussComposite.PhysicalEMStaticReaderRecognition
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier
open GaussUnitaryHistory (Index)
open MeasureTheory Filter Set
open scoped BigOperators Topology Matrix InnerProductSpace

attribute [local irreducible] currentVertex CanonicalPhysicalYResolvent.finiteFull
  frameVector frameTest rawForm nativeFieldJets coframeFieldJets fiberFieldJets fieldJets
  physicalTime jointResolvent fiveKernel sourcePoleRead sourcePoleActionEuler
  emStaticReaderModeReader emStaticReaderCompensation currentRestriction
  sourcePoleCurrentWindow sourcePolePrepared

/-- The original uncut material kernel: `physicalTime`/`jointResolvent`
legs with the raw unit-`i` reader, i.e. `fiveKernel (fieldUnit i)`. -/
def emActualJointKernel (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (t : ℝ) (i : Fin 289) : H→L[ℂ] H :=
  fiveKernel (fieldUnit i) pR (pL-pR) q.F q.z q.w t 0

/-- The local mode kernel keeps the same `physicalTime`/`jointResolvent`
legs with the raw mode reader in the middle. -/
def emStaticModeKernel (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) : H→L[ℂ] H :=
  physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0*
    emStaticReaderModeReader pR q.F*jointResolvent pR q.F q.w 0*physicalTime pR q.F t 0

/-- The full kernel keeps the complete `currentRestriction` of the
composite gauge field in the middle. -/
def emFullStaticKernel (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) : H→L[ℂ] H :=
  physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0*
    currentRestriction sourceStaticCompositeGauge pR q.F 0*
      jointResolvent pR q.F q.w 0*physicalTime pR q.F t 0

/-- The correction kernel keeps only the retained source compensation
operator in the middle. -/
def emCompensationStaticKernel (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) :
    H→L[ℂ] H :=
  physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0*
    emStaticReaderCompensation pR q.F*jointResolvent pR q.F q.w 0*physicalTime pR q.F t 0

/-- `fiveKernel` at transfer `pL-pR` has `pL` legs. -/
theorem em_jointKernel_expanded (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ)
    (i : Fin 289) :
    emActualJointKernel q pL pR t i=
      physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0*rawReader (fieldUnit i) pR q.F 0*
        jointResolvent pR q.F q.w 0*physicalTime pR q.F t 0 := by
  unfold emActualJointKernel fiveKernel
  have leftMomentum : pR+(pL-pR)=pL:=by ext i;simp
  rw [leftMomentum]

/-- Slot `21` is `gaugeSlot 1 0`, slot `34` is `gaugeSlot 2 1`; the joint
kernel difference over the two gauge slots is the mode kernel. -/
theorem em_static_kernel_slots (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) :
    emActualJointKernel q pL pR t 21-emActualJointKernel q pL pR t 34=
      emStaticModeKernel q pL pR t := by
  rw [em_jointKernel_expanded,em_jointKernel_expanded]
  rw [show fieldUnit (21 : Fin 289)=gaugeField 1 0 from rfl,
      show fieldUnit (34 : Fin 289)=gaugeField 2 1 from rfl]
  unfold emStaticModeKernel emStaticReaderModeReader
  rw [mul_sub,sub_mul,sub_mul]

/-- The operator-distribution identity: full minus correction is the
mode kernel pointwise in age. -/
theorem em_static_kernel_distribution (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (t : ℝ) :
    emFullStaticKernel q pL pR t-emCompensationStaticKernel q pL pR t=emStaticModeKernel q pL pR t := by
  unfold emFullStaticKernel emCompensationStaticKernel emStaticModeKernel
  rw [em_static_reader_currentRestriction_generated]
  simp only [mul_add,add_mul]
  rw [add_sub_cancel_right]

/-- The Euler output at gauge slot `i` is minus the source pole read of
the original joint kernel. -/
theorem em_euler_jointKernel (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) (i : Fin 289) :
    sourcePoleActionEuler q pL pR left right 0 t i=
      -sourcePoleRead q.epsilon q.precision pL pR left right (emActualJointKernel q pL pR t i) :=
  sourcePoleActionEuler_source q pL pR left right t i

/-- The common-source consumer: the source pole read of the full kernel
is the complete retained configuration on the actual time-evolved pole
legs with uncut `jointResolvent`/`physicalTime` factors transported
through the original adjoint, never relabeled as completed legs. -/
theorem em_fullKernel_poleRead_config (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) :
    sourcePoleRead q.epsilon q.precision pL pR left right (emFullStaticKernel q pL pR t)=
      sourceStaticCompositeConfiguration pR
        (sourceTestApprox q.F ((physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0).adjoint
          (sourcePolePrepared q.epsilon q.precision pL left)))
        (sourceTestApprox q.F ((jointResolvent pR q.F q.w 0*physicalTime pR q.F t 0)
          (sourcePolePrepared q.epsilon q.precision pR right))) := by
  unfold emFullStaticKernel
  rw [sourcePoleRead_actual]
  rw [show (physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0*
        currentRestriction sourceStaticCompositeGauge pR q.F 0*
        jointResolvent pR q.F q.w 0*physicalTime pR q.F t 0)
        (sourcePolePrepared q.epsilon q.precision pR right)=
      (physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0)
        (currentRestriction sourceStaticCompositeGauge pR q.F 0
          ((jointResolvent pR q.F q.w 0*physicalTime pR q.F t 0)
            (sourcePolePrepared q.epsilon q.precision pR right))) from rfl]
  rw [←ContinuousLinearMap.adjoint_inner_left,currentRestriction_original_pair,
    sourceStaticCompositeConfiguration_generated]

/-- `physicalTime` is continuous in age on the left leg. -/
theorem em_physicalTime_left_continuous (q : PhysicalResponsePoint) (pL : PhysicalMomentum) :
    Continuous (fun t : ℝ=>physicalTime pL q.F (-t) 0) := by
  have paid:=(physicalTimeJets_continuous pL q.F 0 (-1) 0).1
  have same : (fun t : ℝ=>(physicalTimeJet pL q.F 0 (-1) 0 t).value)=
      (fun t : ℝ=>physicalTime pL q.F (-t) 0):=by
    funext t
    simp only [physicalTimeJet,timeJet,neg_one_mul,add_zero]
    unfold physicalTime
    rfl
  exact (congrArg (fun f : ℝ→(H→L[ℂ] H)=>Continuous f) same).mp paid

/-- `physicalTime` is continuous in age on the right leg. -/
theorem em_physicalTime_right_continuous (q : PhysicalResponsePoint) (pR : PhysicalMomentum) :
    Continuous (fun t : ℝ=>physicalTime pR q.F t 0) := by
  have paid:=(physicalTimeJets_continuous pR q.F 0 (1:ℝ) 0).1
  have same : (fun t : ℝ=>(physicalTimeJet pR q.F 0 (1:ℝ) 0 t).value)=
      (fun t : ℝ=>physicalTime pR q.F t 0):=by
    funext t
    simp only [physicalTimeJet,timeJet,one_mul,add_zero]
    unfold physicalTime
    rfl
  exact (congrArg (fun f : ℝ→(H→L[ℂ] H)=>Continuous f) same).mp paid

/-- The full kernel is continuous in age. -/
theorem em_fullKernel_continuous (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) :
    Continuous (fun t : ℝ=>emFullStaticKernel q pL pR t) := by
  unfold emFullStaticKernel
  exact (((em_physicalTime_left_continuous q pL).mul continuous_const).mul
    continuous_const).mul continuous_const |>.mul (em_physicalTime_right_continuous q pR)

/-- The correction kernel is continuous in age. -/
theorem em_compKernel_continuous (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) :
    Continuous (fun t : ℝ=>emCompensationStaticKernel q pL pR t) := by
  unfold emCompensationStaticKernel
  exact (((em_physicalTime_left_continuous q pL).mul continuous_const).mul
    continuous_const).mul continuous_const |>.mul (em_physicalTime_right_continuous q pR)

/-- The full age-window read: minus the original spatial coefficient
times the `laplaceWeight` window of the source pole read of the full
kernel. -/
def emFullStaticWindow (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (T : ℝ) : ℂ :=
  -(3/10:ℂ)*rootTwo*∫t in (0:ℝ)..T,laplaceWeight lambda t*
    sourcePoleRead q.epsilon q.precision pL pR left right (emFullStaticKernel q pL pR t)

/-- The correction age-window read: plus the original spatial
coefficient times the `laplaceWeight` window of the correction kernel. -/
def emCompensationStaticWindow (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (T : ℝ) : ℂ :=
  (3/10:ℂ)*rootTwo*∫t in (0:ℝ)..T,laplaceWeight lambda t*
    sourcePoleRead q.epsilon q.precision pL pR left right (emCompensationStaticKernel q pL pR t)

private theorem em_laplace_continuous (lambda : ℂ) :
    Continuous (fun t : ℝ=>laplaceWeight lambda t) := by
  unfold laplaceWeight
  exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

/-- The full age window is the `laplaceWeight`-weighted integral of the
ORIGINAL retained configuration evaluated on the actual time-evolved
pole legs, with `lambda`/`T` kept as generated inputs. -/
theorem em_fullStaticWindow_config (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (T : ℝ) :
    emFullStaticWindow q pL pR left right lambda T=
      -(3/10:ℂ)*rootTwo*∫t in (0:ℝ)..T,laplaceWeight lambda t*
        sourceStaticCompositeConfiguration pR
          (sourceTestApprox q.F ((physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0).adjoint
            (sourcePolePrepared q.epsilon q.precision pL left)))
          (sourceTestApprox q.F ((jointResolvent pR q.F q.w 0*physicalTime pR q.F t 0)
            (sourcePolePrepared q.epsilon q.precision pR right))) := by
  unfold emFullStaticWindow
  apply congrArg (fun x : ℂ=>-(3/10:ℂ)*rootTwo*x)
  apply intervalIntegral.integral_congr
  intro t _
  exact congrArg (fun x : ℂ=>laplaceWeight lambda t*x)
    (em_fullKernel_poleRead_config q pL pR left right t)

private theorem em_euler_integrable (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (T : ℝ) (i : Fin 289) :
    IntervalIntegrable (fun t=>laplaceWeight lambda t*sourcePoleActionEuler q pL pR left right 0 t i)
      volume 0 T :=
  ((em_laplace_continuous lambda).mul
    (sourcePoleActionEuler_continuous q pL pR left right i)).intervalIntegrable 0 T

/-- Per-rest-pair actual-origin scalar return: the actual origin weight
equals the full window plus the correction window. -/
theorem em_actual_origin_window_split (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (T : ℝ) :
    actualOriginWeight q pL pR left right lambda T=
      emFullStaticWindow q pL pR left right lambda T+
        emCompensationStaticWindow q pL pR left right lambda T := by
  have integrableFull : IntervalIntegrable (fun t=>laplaceWeight lambda t*
      sourcePoleRead q.epsilon q.precision pL pR left right (emFullStaticKernel q pL pR t))
        volume 0 T:=
    ((em_laplace_continuous lambda).mul
      ((sourcePoleRead q.epsilon q.precision pL pR left right).continuous.comp
        (em_fullKernel_continuous q pL pR))).intervalIntegrable 0 T
  have integrableCorr : IntervalIntegrable (fun t=>laplaceWeight lambda t*
      sourcePoleRead q.epsilon q.precision pL pR left right (emCompensationStaticKernel q pL pR t))
        volume 0 T:=
    ((em_laplace_continuous lambda).mul
      ((sourcePoleRead q.epsilon q.precision pL pR left right).continuous.comp
        (em_compKernel_continuous q pL pR))).intervalIntegrable 0 T
  have difference : (∫t in (0:ℝ)..T,laplaceWeight lambda t*
        sourcePoleActionEuler q pL pR left right 0 t 21)-
      (∫t in (0:ℝ)..T,laplaceWeight lambda t*sourcePoleActionEuler q pL pR left right 0 t 34)=
      ∫t in (0:ℝ)..T,(laplaceWeight lambda t*
        (sourcePoleActionEuler q pL pR left right 0 t 21-
          sourcePoleActionEuler q pL pR left right 0 t 34)):=by
    rw [←intervalIntegral.integral_sub (em_euler_integrable q pL pR left right lambda T 21)
      (em_euler_integrable q pL pR left right lambda T 34)]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [mul_sub]
  have euler_eq : ∀t : ℝ,sourcePoleActionEuler q pL pR left right 0 t 21-
      sourcePoleActionEuler q pL pR left right 0 t 34=
      -sourcePoleRead q.epsilon q.precision pL pR left right (emStaticModeKernel q pL pR t):=by
    intro t
    rw [em_euler_jointKernel,em_euler_jointKernel,←em_static_kernel_slots,map_sub]
    have neg_alg : ∀a b : ℂ,-a- -b=-(a-b):=fun _ _=>by ring
    rw [neg_alg]
  have mode_eq : ∀t : ℝ,-sourcePoleRead q.epsilon q.precision pL pR left right
      (emStaticModeKernel q pL pR t)=
      -(sourcePoleRead q.epsilon q.precision pL pR left right (emFullStaticKernel q pL pR t)-
        sourcePoleRead q.epsilon q.precision pL pR left right (emCompensationStaticKernel q pL pR t)):=by
    intro t
    exact (congrArg (fun x : H→L[ℂ] H=>
        -(sourcePoleRead q.epsilon q.precision pL pR left right x))
      (em_static_kernel_distribution q pL pR t).symm).trans
      (congrArg Neg.neg (map_sub _ _ _))
  unfold actualOriginWeight
  unfold actualCurrent sourcePoleCurrentWindow
  rw [difference]
  have point : (fun t=>laplaceWeight lambda t*
        (sourcePoleActionEuler q pL pR left right 0 t 21-
          sourcePoleActionEuler q pL pR left right 0 t 34))=
      (fun t=>-(laplaceWeight lambda t*
        sourcePoleRead q.epsilon q.precision pL pR left right (emFullStaticKernel q pL pR t)-
        laplaceWeight lambda t*
          sourcePoleRead q.epsilon q.precision pL pR left right
            (emCompensationStaticKernel q pL pR t))):=by
    funext t
    exact (congrArg (fun x : ℂ=>laplaceWeight lambda t*x) (euler_eq t)).trans
      ((congrArg (fun x : ℂ=>laplaceWeight lambda t*x) (mode_eq t)).trans
        ((mul_neg _ _).trans (congrArg Neg.neg (mul_sub _ _ _))))
  rw [point,intervalIntegral.integral_neg,
    intervalIntegral.integral_sub integrableFull integrableCorr]
  unfold emFullStaticWindow emCompensationStaticWindow
  ring

/-- All64 weighted actual-origin scalar return, keeping every source
weight and both source legs. -/
theorem em_actual_origin_window_weighted (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (sideL edgeL sideR edgeR : Fin 2) (lambda : ℂ) (T : ℝ) :
    ∑left : RestStateIndex,∑right : RestStateIndex,
      sourceActualPreparedWeight pL pR sideL edgeL sideR edgeR left right*
        actualOriginWeight q pL pR left right lambda T=
    ∑left : RestStateIndex,∑right : RestStateIndex,
      sourceActualPreparedWeight pL pR sideL edgeL sideR edgeR left right*
        emFullStaticWindow q pL pR left right lambda T+
    ∑left : RestStateIndex,∑right : RestStateIndex,
      sourceActualPreparedWeight pL pR sideL edgeL sideR edgeR left right*
        emCompensationStaticWindow q pL pR left right lambda T := by
  simp_rw [em_actual_origin_window_split,mul_add,Finset.sum_add_distrib]

/-- At zero window length all three reads return zero. -/
theorem em_actual_origin_window_zero (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) :
    actualOriginWeight q pL pR left right lambda 0=0∧
      emFullStaticWindow q pL pR left right lambda 0=0∧
        emCompensationStaticWindow q pL pR left right lambda 0=0:=by
  refine ⟨?_,?_,?_⟩
  · unfold actualOriginWeight
    unfold actualCurrent sourcePoleCurrentWindow
    simp only [intervalIntegral.integral_same,sub_self,mul_zero]
  · unfold emFullStaticWindow
    rw [intervalIntegral.integral_same,mul_zero]
  · unfold emCompensationStaticWindow
    rw [intervalIntegral.integral_same,mul_zero]

end LowEnergy.GaussComposite.PhysicalEMActualStaticWindow

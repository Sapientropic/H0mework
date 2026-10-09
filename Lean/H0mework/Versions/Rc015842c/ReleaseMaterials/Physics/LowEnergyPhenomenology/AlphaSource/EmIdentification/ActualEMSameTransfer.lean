import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMMovingIR
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualPreparedDetector

set_option autoImplicit false
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCarrierOwn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumWholeOrigin PreparationVacuumFullSlowFieldResponse
open PreparationVacuumNativeSlowCoupling PreparationVacuumNativePoleTensor
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumSoftPoleSelection
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePolarizationEmitter
open PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalCurvatureSheetLimit
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumFullPoleContinuation PreparationPhysicalActualGaussChargeCurrent
open PreparationVacuumPhysicalQuantumLockedCharge PreparationVacuumElectromagneticIdentity
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumGaugeSourceInjection PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumActionFieldLift PreparationVacuumMixedFieldReturn
open CanonicalGradedSpatialSource Filter Set MeasureTheory
open scoped Matrix BigOperators Topology
attribute [local irreducible] sourceActualPreparedCurrent sourceActualPreparedDetector
  sourceActualPreparedKernel sourceQuantumChargedRead returnedCurrentWindow actualJointKernel fiveKernel

/-- One existing actual preparation and its own finite observation window. -/
structure ActualEMObservationEnd where
  q : PhysicalResponsePoint
  momentum : PhysicalMomentum
  sideL : Fin 2
  edgeL : Fin 2
  sideR : Fin 2
  edgeR : Fin 2
  window : ℝ

/-- The two orientations restrict one source-generated transfer; only the base preparation is independent. -/
def emTransferLeft (endpoint : ActualEMObservationEnd) (orientation : ℝ)
    (epsilon : ℝ) (n : PhysicalMomentum) : PhysicalMomentum :=
  endpoint.momentum + orientation • (epsilon^2 • n)

def emTransferClock (orientation : ℝ) (epsilon s : ℝ) : ℂ :=
  -(orientation:ℂ) * sheetLambda epsilon s

/-- All64 actual current, on the generated momentum and time restriction. -/
def emActualTransferCurrent (endpoint : ActualEMObservationEnd) (orientation : ℝ)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) : Fin 289 → ℂ :=
  sourceActualPreparedCurrent endpoint.q (emTransferLeft endpoint orientation e.val n) endpoint.momentum
    endpoint.sideL endpoint.edgeL endpoint.sideR endpoint.edgeR
    (emTransferClock orientation e.val (sourceSheet branch n unit e.val)) endpoint.window

def emActualTransferOrigin (endpoint : ActualEMObservationEnd) : Fin 289 → ℂ :=
  sourceActualPreparedCurrent endpoint.q endpoint.momentum endpoint.momentum
    endpoint.sideL endpoint.edgeL endpoint.sideR endpoint.edgeR 0 endpoint.window

/-- Source and detector are opposite Fourier restrictions of this exact physical sheet. -/
theorem em_actual_transfer_same_fourier (detector source : ActualEMObservationEnd)
    (epsilon s : ℝ) (n : PhysicalMomentum) :
    actualMomentum (emTransferLeft source (-1) epsilon n) source.momentum (emTransferClock (-1) epsilon s) =
        frequencyRay epsilon s n ∧
    actualMomentum (emTransferLeft detector 1 epsilon n) detector.momentum (emTransferClock 1 epsilon s) =
        -(frequencyRay epsilon s n) ∧
    emTransferLeft source (-1) epsilon n-source.momentum = -(epsilon^2 • n) ∧
    emTransferLeft detector 1 epsilon n-detector.momentum = epsilon^2 • n := by
  have sourceLeft : emTransferLeft source (-1) epsilon n = sheetLeft epsilon n source.momentum := by
    simp [emTransferLeft,sheetLeft,sub_eq_add_neg]
  have sourceClock : emTransferClock (-1) epsilon s = sheetLambda epsilon s := by
    simp [emTransferClock]
  refine ⟨?_,?_,?_,?_⟩
  · rw [sourceLeft,sourceClock]
    exact sheetMomentum_actual epsilon s n source.momentum
  · unfold actualMomentum fullMomentum sourcePhysicalTransfer emTransferLeft emTransferClock
      PreparationVacuumPhysicalFeedback.physicalSpatial frequencyRay physicalFrequencyMomentum sheetLambda sourceFrequency
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cases_zero,Pi.neg_apply]
      push_cast
      ring
    · simp only [Fin.cases_succ,Pi.neg_apply,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      push_cast
      ring
  · simp [emTransferLeft]
  · simp [emTransferLeft]

/-- The source's Laplace convention fixes both time signs; independent detector/source ages remain independent. -/
theorem em_actual_transfer_time_weights (epsilon s detectorAge sourceAge : ℝ) :
    laplaceWeight (emTransferClock 1 epsilon s) detectorAge *
      laplaceWeight (emTransferClock (-1) epsilon s) sourceAge =
    Complex.exp (Complex.I*(sourceFrequency epsilon s:ℂ)*((sourceAge-detectorAge:ℝ):ℂ)) := by
  unfold laplaceWeight emTransferClock sheetLambda
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The unchanged original five-factor kernel sees the generated spatial shift at each end. -/
theorem em_actual_transfer_kernel (endpoint : ActualEMObservationEnd) (orientation epsilon age : ℝ)
    (n : PhysicalMomentum) (i : Fin 289) :
    fiveKernel (fieldUnit i) endpoint.momentum (orientation • (epsilon^2 • n))
      endpoint.q.F endpoint.q.z endpoint.q.w age 0 =
    actualJointKernel endpoint.q (emTransferLeft endpoint orientation epsilon n) endpoint.momentum age i := by
  have shift : emTransferLeft endpoint orientation epsilon n-endpoint.momentum = orientation • (epsilon^2 • n) := by
    simp [emTransferLeft]
  rw [←shift]
  exact actualJointKernel_original endpoint.q _ endpoint.momentum age i

private theorem em_prepared_current_joint_continuous (endpoint : ActualEMObservationEnd)
    (hz : endpoint.q.z.im≠0) (hw : endpoint.q.w.im≠0) :
    Continuous (fun p : PhysicalMomentum × PhysicalMomentum × ℂ =>
      sourceActualPreparedCurrent endpoint.q p.1 p.2.1 endpoint.sideL endpoint.edgeL endpoint.sideR endpoint.edgeR
        p.2.2 endpoint.window) := by
  unfold sourceActualPreparedCurrent
  apply continuous_finsetSum
  intro a _
  apply continuous_finsetSum
  intro b _
  exact (returnedCurrentWindow_joint_continuous endpoint.q a b endpoint.window hz hw).const_smul
    (sourceActualPreparedWeight 0 0 endpoint.sideL endpoint.edgeL endpoint.sideR endpoint.edgeR a b)

/-- Continuity is paid by both moving original Green/time legs and the complete all64 preparation. -/
theorem em_actual_transfer_current_limit (endpoint : ActualEMObservationEnd) (orientation : ℝ)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (hz : endpoint.q.z.im≠0) (hw : endpoint.q.w.im≠0) :
    Tendsto (emActualTransferCurrent endpoint orientation branch n unit) scaleApproach
      (𝓝 (emActualTransferOrigin endpoint)) := by
  have shift := (scaleVal_tendsto.pow 2).smul (tendsto_const_nhds (x:=n))
  have left : Tendsto (fun e : scaleDomain => emTransferLeft endpoint orientation e.val n)
      scaleApproach (𝓝 endpoint.momentum) := by
    have result := (tendsto_const_nhds (x:=endpoint.momentum)).add ((tendsto_const_nhds (x:=orientation)).smul shift)
    simpa only [emTransferLeft,zero_pow (by decide : 2≠0),zero_smul,smul_zero,add_zero] using result
  have clock : Tendsto (fun e : scaleDomain => sheetLambda e.val (sourceSheet branch n unit e.val))
      scaleApproach (𝓝 (0:ℂ)) := by
    have result := tendsto_pi_nhds.mp (sourceRay_soft_limit branch n unit) 0
    simpa only [frequencyRay,physicalFrequencyMomentum,sheetLambda,sourceFrequency,mul_comm,
      Fin.cases_zero,Pi.zero_apply] using result
  have time : Tendsto (fun e : scaleDomain => emTransferClock orientation e.val (sourceSheet branch n unit e.val))
      scaleApproach (𝓝 (0:ℂ)) := by
    simpa only [emTransferClock,mul_zero] using (tendsto_const_nhds (x:=-(orientation:ℂ))).mul clock
  have args := left.prodMk_nhds ((tendsto_const_nhds (x:=endpoint.momentum)).prodMk_nhds time)
  have result := (em_prepared_current_joint_continuous endpoint hz hw).tendsto
    (endpoint.momentum,endpoint.momentum,(0:ℂ)) |>.comp args
  exact result

/-- One same-transfer finite-window observation uses two independent actual preparations. -/
def emActualTransferInteraction (detector source : ActualEMObservationEnd)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) : ℂ :=
  dotProduct (emActualTransferCurrent detector 1 branch n unit e)
    (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *ᵥ
      emActualTransferCurrent source (-1) branch n unit e)

/-- The original actual charged ordinary read on precisely the same detector/source transfer. -/
def emActualTransferOrdinary (detector source : ActualEMObservationEnd)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) : ℂ :=
  sourceQuantumChargedRead detector.q detector.sideL detector.edgeL detector.sideR detector.edgeR
    (sourceActualPreparedKernel detector.q (emTransferLeft detector 1 e.val n) detector.momentum
      (emTransferClock 1 e.val (sourceSheet branch n unit e.val)) detector.window
      (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *ᵥ
        emActualTransferCurrent source (-1) branch n unit e))

theorem em_actual_transfer_ordinary (detector source : ActualEMObservationEnd)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain)
    (hz : detector.q.z.im≠0) (hw : detector.q.w.im≠0) :
    emActualTransferInteraction detector source branch n unit e = -emActualTransferOrdinary detector source branch n unit e := by
  have current := sourceActualPreparedDetector_current detector.q (emTransferLeft detector 1 e.val n) detector.momentum
    detector.sideL detector.edgeL detector.sideR detector.edgeR
    (emTransferClock 1 e.val (sourceSheet branch n unit e.val)) detector.window
    (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *ᵥ
      emActualTransferCurrent source (-1) branch n unit e)
  have action := sourceActualPreparedDetector_action detector.q (emTransferLeft detector 1 e.val n) detector.momentum
    detector.sideL detector.edgeL detector.sideR detector.edgeR
    (emTransferClock 1 e.val (sourceSheet branch n unit e.val)) detector.window
    (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *ᵥ
      emActualTransferCurrent source (-1) branch n unit e) hz hw
  exact current.symm.trans action

/-- The moving source family, not a frozen forcing, feeds the genuine EM infrared read. -/
theorem em_actual_transfer_em_ir (source : ActualEMObservationEnd)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (mu : Fin 4)
    (hz : source.q.z.im≠0) (hw : source.q.w.im≠0) :
    Tendsto (fun e : scaleDomain => (2*(sourceSheet branch n unit e.val:ℂ))*
      (emInsertion.transpose *ᵥ (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *ᵥ
        emActualTransferCurrent source (-1) branch n unit e)) mu)
      scaleApproach (𝓝 (sourceCurvatureEmitterInput (emActualTransferOrigin source) (residueIndex branch)*
        emInfraredJet (physicalFrequencyMomentum (sourceSpeed branch) n) mu (fiveIndex (residueIndex branch))*
        (softCoefficient branch:ℂ))) :=
  em_moving_current_response_ir branch n unit _ _ (em_actual_transfer_current_limit source (-1) branch n unit hz hw) mu

/-- Both independent moving ends are consumed before the same frequency-normalized full observable limit. -/
theorem em_actual_transfer_interaction_ir (detector source : ActualEMObservationEnd)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (hzd : detector.q.z.im≠0) (hwd : detector.q.w.im≠0)
    (hzs : source.q.z.im≠0) (hws : source.q.w.im≠0) :
    Tendsto (fun e : scaleDomain => (2*(sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ))*
      emActualTransferInteraction detector source branch n unit e)
      scaleApproach (𝓝 (dotProduct (emActualTransferOrigin detector) (leadingNativeResponse branch (emActualTransferOrigin source)))) := by
  have d := em_actual_transfer_current_limit detector 1 branch n unit hzd hwd
  have s := em_moving_whole_response_ir branch n unit _ _
    (em_actual_transfer_current_limit source (-1) branch n unit hzs hws)
  have cont : Continuous (fun p : (Fin 289 → ℂ) × (Fin 289 → ℂ) => dotProduct p.1 p.2) :=
    continuous_fst.dotProduct continuous_snd
  have result := (cont.tendsto _).comp (d.prodMk_nhds s)
  apply result.congr'
  filter_upwards [] with e
  change dotProduct _ (_ • _) = _
  rw [dotProduct_smul]
  rfl

end LowEnergy.GaussComposite.ActualEMCarrierOwn

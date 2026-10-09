import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMSameTransfer
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMCurrentPacket
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualWholeStaticUniform

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCarrierOwn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert Stage10 CanonicalGradedSpatialSource PreparationVacuumPhysicalFeedback PreparationVacuumElectromagneticIdentity
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalQuantumLockedCharge
open PreparationVacuumFullPoleContinuation PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumGaugeSourceInjection PreparationVacuumMixedFieldReturn
open PreparationPhysicalActualGaussChargeCurrent PreparationPhysicalActualLegNormalization
open PreparationPhysicalStaticSpatialCouplingReturn PreparationVacuumOriginalGreenFeedback
open ActualWholeStatic ActualEMObservable ActualElectronOwnerTest MeasureTheory Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] actualJointKernel sourceActualPreparedKernel sourceActualPreparedCurrent
  sourceActualUnitLegRead sourceActualUnitDual sourceActualUnitPrimal wholeStaticLimit sourceGreen sourceActualPreparedDetector sourceActualLegNormalization
  sourceActualLegCorrection sourceQuantumChargedRead

/-- The original independent unit dual/primal read, including all four actual charged/neutral preparations. -/
def emMovingUnitOperator (endpoint : ActualEMObservationEnd) : (H→L[ℂ]H)→L[ℂ]ℂ :=
  -((sourceActualUnitDual endpoint.q endpoint.sideL endpoint.edgeL endpoint.q.z).comp
    (ContinuousLinearMap.apply ℂ H (sourceActualUnitPrimal endpoint.q endpoint.sideR endpoint.edgeR endpoint.q.w)))

private theorem movingUnitOperator_actual (endpoint : ActualEMObservationEnd) (A : H→L[ℂ]H) :
    emMovingUnitOperator endpoint A =
      -sourceActualUnitLegRead endpoint.q endpoint.sideL endpoint.edgeL endpoint.sideR endpoint.edgeR A := by
  unfold emMovingUnitOperator sourceActualUnitLegRead
  rfl

/-- All full289 columns of the original moving five-factor kernel, before any physical projection. -/
def emMovingFieldKernel (endpoint : ActualEMObservationEnd) (pL pR : PhysicalMomentum) (lambda : ℂ) :
    (Fin 289→ℂ)→L[ℂ](H→L[ℂ]H) :=
  ∑i : Fin 289,(ContinuousLinearMap.proj i).smulRight
    (∫t in (0:ℝ)..endpoint.window,laplaceWeight lambda t • actualJointKernel endpoint.q pL pR t i)

attribute [local irreducible] emMovingUnitOperator emMovingFieldKernel

private theorem movingKernel_column_continuous (endpoint : ActualEMObservationEnd)
    (hz : endpoint.q.z.im≠0) (hw : endpoint.q.w.im≠0) (i : Fin 289) :
    Continuous (fun p : PhysicalMomentum × PhysicalMomentum × ℂ =>
      ∫t in (0:ℝ)..endpoint.window,laplaceWeight p.2.2 t • actualJointKernel endpoint.q p.1 p.2.1 t i) := by
  have args : Continuous (fun x : (PhysicalMomentum × PhysicalMomentum × ℂ) × ℝ =>(x.1.1,x.1.2.1,x.2)) :=
    continuous_fst.fst.prodMk (continuous_fst.snd.fst.prodMk continuous_snd)
  have kernel := (actualJointKernel_continuous endpoint.q i hz hw).comp args
  have weight : Continuous (fun x : (PhysicalMomentum × PhysicalMomentum × ℂ) × ℝ=>laplaceWeight x.1.2.2 x.2) := by
    unfold laplaceWeight
    fun_prop
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (weight.smul kernel) 0 endpoint.window

/-- Both actual resolvents, both physical times and every native reader jointly generate operator-norm continuity. -/
theorem em_moving_kernel_joint_continuous (endpoint : ActualEMObservationEnd)
    (hz : endpoint.q.z.im≠0) (hw : endpoint.q.w.im≠0) :
    Continuous (fun p : PhysicalMomentum × PhysicalMomentum × ℂ =>emMovingFieldKernel endpoint p.1 p.2.1 p.2.2) := by
  let _ : NormedAddCommGroup ((Fin 289→ℂ)→L[ℂ](H→L[ℂ]H)) := inferInstance
  unfold emMovingFieldKernel
  apply continuous_finsetSum
  intro i _
  exact (ContinuousLinearMap.smulRightL ℂ (Fin 289→ℂ) (H→L[ℂ]H) (ContinuousLinearMap.proj i)).continuous.comp
    (movingKernel_column_continuous endpoint hz hw i)

theorem em_moving_kernel_actual (endpoint : ActualEMObservationEnd) (pL pR : PhysicalMomentum) (lambda : ℂ)
    (hz : endpoint.q.z.im≠0) (hw : endpoint.q.w.im≠0) (V : Fin 289→ℂ) :
    emMovingFieldKernel endpoint pL pR lambda V=sourceActualPreparedKernel endpoint.q pL pR lambda endpoint.window V := by
  have continuous (i : Fin 289) : Continuous (fun t : ℝ=>laplaceWeight lambda t • actualJointKernel endpoint.q pL pR t i) := by
    have args : Continuous (fun t : ℝ=>(pL,pR,t)) := by fun_prop
    have kernel := (actualJointKernel_continuous endpoint.q i hz hw).comp args
    have weight : Continuous (laplaceWeight lambda) := by unfold laplaceWeight;fun_prop
    exact weight.smul kernel
  have commuting (t : ℝ) (i : Fin 289) :
      laplaceWeight lambda t • (V i • actualJointKernel endpoint.q pL pR t i)=
        V i • (laplaceWeight lambda t • actualJointKernel endpoint.q pL pR t i) := smul_comm _ _ _
  simp only [emMovingFieldKernel,sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply,sourceActualPreparedKernel,Finset.smul_sum,commuting]
  have exchange:=intervalIntegral.integral_finsetSum (s:=Finset.univ) (fun i _=>
    ((continuous i).intervalIntegrable (μ:=volume) 0 endpoint.window).smul (V i))
  simpa only [Pi.smul_apply,intervalIntegral.integral_smul] using exchange.symm

/-- One complete moving finite-window unit test, before the single action normalization. -/
def emMovingUnitTest (endpoint : ActualEMObservationEnd) (pL pR : PhysicalMomentum) (lambda : ℂ) :
    (Fin 289→ℂ)→L[ℂ]ℂ := (emMovingUnitOperator endpoint).comp (emMovingFieldKernel endpoint pL pR lambda)

def emMovingUnitCurrent (endpoint : ActualEMObservationEnd) (pL pR : PhysicalMomentum) (lambda : ℂ) : Fin 289→ℂ :=
  fun i=>emMovingUnitTest endpoint pL pR lambda (Pi.single i 1)

/-- The unit-current functional is exactly the original moving kernel read by its independent actual unit legs. -/
theorem em_moving_unit_original (endpoint : ActualEMObservationEnd) (pL pR : PhysicalMomentum) (lambda : ℂ)
    (hz : endpoint.q.z.im≠0) (hw : endpoint.q.w.im≠0) (V : Fin 289→ℂ) :
    emMovingUnitTest endpoint pL pR lambda V=
      -sourceActualUnitLegRead endpoint.q endpoint.sideL endpoint.edgeL endpoint.sideR endpoint.edgeR
        (sourceActualPreparedKernel endpoint.q pL pR lambda endpoint.window V) := by
  simp only [emMovingUnitTest,ContinuousLinearMap.comp_apply,
    em_moving_kernel_actual endpoint pL pR lambda hz hw V,movingUnitOperator_actual]

/-- The generated moving unit test retains all64 prepared weights and the complete original left/right/cross correction. -/
theorem em_moving_unit_full_return (endpoint : ActualEMObservationEnd) (pL pR : PhysicalMomentum) (lambda : ℂ)
    (hz : endpoint.q.z.im≠0) (hw : endpoint.q.w.im≠0) (V : Fin 289→ℂ) :
    emMovingUnitTest endpoint pL pR lambda V=
      sourceActualLegNormalization endpoint.q endpoint.sideL endpoint.edgeL endpoint.sideR endpoint.edgeR*
        (sourceActualPreparedDetector endpoint.q pL pR endpoint.sideL endpoint.edgeL endpoint.sideR endpoint.edgeR lambda endpoint.window V-
          sourceActualLegCorrection endpoint.q endpoint.sideL endpoint.edgeL endpoint.sideR endpoint.edgeR
            (sourceActualPreparedKernel endpoint.q pL pR lambda endpoint.window V)) := by
  rw [em_moving_unit_original endpoint pL pR lambda hz hw V,sourceActualUnitLegRead_return,
    sourceActualPreparedDetector_action endpoint.q pL pR endpoint.sideL endpoint.edgeL endpoint.sideR endpoint.edgeR lambda endpoint.window V hz hw]
  ring

/-- Finite-dimensional duality preserves the complete moving current rather than selecting one preparation row. -/
theorem em_moving_unit_current_read (endpoint : ActualEMObservationEnd) (pL pR : PhysicalMomentum) (lambda : ℂ)
    (V : Fin 289→ℂ) :
    dotProduct (emMovingUnitCurrent endpoint pL pR lambda) V=emMovingUnitTest endpoint pL pR lambda V := by
  have basis : (∑i : Fin 289,V i • (Pi.single i 1:Fin 289→ℂ))=V := by
    ext j
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul,mul_ite]
  conv_rhs => rw [←basis]
  simp only [map_sum,map_smul,smul_eq_mul,emMovingUnitCurrent,dotProduct,mul_comm]

/-- A single Fourier transfer controls both spatial momentum and the original time-frequency sign. -/
def emUnitTransferTest (endpoint : ActualEMObservationEnd) (orientation : ℝ)
    (transfer : PhysicalMomentum × ℂ) : (Fin 289→ℂ)→L[ℂ]ℂ :=
  emMovingUnitTest endpoint (endpoint.momentum+orientation • transfer.1) endpoint.momentum
    (-(orientation:ℂ)*transfer.2)

def emUnitTransferCurrent (endpoint : ActualEMObservationEnd) (orientation : ℝ)
    (transfer : PhysicalMomentum × ℂ) : Fin 289→ℂ :=
  fun i=>emUnitTransferTest endpoint orientation transfer (Pi.single i 1)

theorem em_unit_transfer_test_continuous (endpoint : ActualEMObservationEnd) (orientation : ℝ)
    (hz : endpoint.q.z.im≠0) (hw : endpoint.q.w.im≠0) : Continuous (emUnitTransferTest endpoint orientation) := by
  have args : Continuous (fun transfer : PhysicalMomentum × ℂ =>
      (endpoint.momentum+orientation • transfer.1,endpoint.momentum,-(orientation:ℂ)*transfer.2)) := by fun_prop
  exact continuous_const.clm_comp ((em_moving_kernel_joint_continuous endpoint hz hw).comp args)

theorem em_unit_transfer_current_continuous (endpoint : ActualEMObservationEnd) (orientation : ℝ)
    (hz : endpoint.q.z.im≠0) (hw : endpoint.q.w.im≠0) : Continuous (emUnitTransferCurrent endpoint orientation) := by
  apply continuous_pi
  intro i
  exact (em_unit_transfer_test_continuous endpoint orientation hz hw).clm_apply continuous_const

/-- One generated radius controls the full current and its operator-norm test in every spatial and temporal transfer direction. -/
theorem em_unit_transfer_uniform (endpoint : ActualEMObservationEnd) (orientation : ℝ)
    (hz : endpoint.q.z.im≠0) (hw : endpoint.q.w.im≠0) (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ radius : ℝ, 0<radius ∧ ∀ transfer : PhysicalMomentum × ℂ, ‖transfer‖<radius →
      ‖emUnitTransferTest endpoint orientation transfer-emUnitTransferTest endpoint orientation 0‖≤epsilon ∧
      ‖emUnitTransferCurrent endpoint orientation transfer-emUnitTransferCurrent endpoint orientation 0‖≤epsilon := by
  have continuous := (em_unit_transfer_test_continuous endpoint orientation hz hw).prodMk
    (em_unit_transfer_current_continuous endpoint orientation hz hw)
  have near := continuous.continuousAt.tendsto.eventually (Metric.ball_mem_nhds
    (emUnitTransferTest endpoint orientation 0,emUnitTransferCurrent endpoint orientation 0) positive)
  obtain ⟨radius,rp,inside⟩:=Metric.mem_nhds_iff.mp near
  refine ⟨radius,rp,?_⟩
  intro transfer small
  have paid:=inside (show transfer∈Metric.ball 0 radius by simpa only [Metric.mem_ball,dist_zero_right] using small)
  change dist (emUnitTransferTest endpoint orientation transfer,emUnitTransferCurrent endpoint orientation transfer)
    (emUnitTransferTest endpoint orientation 0,emUnitTransferCurrent endpoint orientation 0)<epsilon at paid
  rw [Prod.dist_eq,max_lt_iff,dist_eq_norm,dist_eq_norm] at paid
  exact ⟨paid.1.le,paid.2.le⟩

/-- The complete source-generated budget is a norm of its own zero-transfer test/current, with no normalizer premise. -/
def emMovingUnitBudget (endpoint : ActualEMObservationEnd) (orientation : ℝ) : ℝ :=
  1+max ‖emUnitTransferTest endpoint orientation 0‖ ‖emUnitTransferCurrent endpoint orientation 0‖

theorem em_moving_unit_budget_positive (endpoint : ActualEMObservationEnd) (orientation : ℝ) :
    0<emMovingUnitBudget endpoint orientation := by
  unfold emMovingUnitBudget
  positivity

/-- The source joint continuity pays an actual all-direction dominating current/test budget. -/
theorem em_unit_transfer_domination (endpoint : ActualEMObservationEnd) (orientation : ℝ)
    (hz : endpoint.q.z.im≠0) (hw : endpoint.q.w.im≠0) :
    ∃ radius : ℝ, 0<radius ∧ ∀ transfer : PhysicalMomentum × ℂ, ‖transfer‖<radius →
      ‖emUnitTransferTest endpoint orientation transfer‖≤emMovingUnitBudget endpoint orientation ∧
      ‖emUnitTransferCurrent endpoint orientation transfer‖≤emMovingUnitBudget endpoint orientation := by
  obtain ⟨radius,rp,paid⟩:=em_unit_transfer_uniform endpoint orientation hz hw 1 (by norm_num)
  refine ⟨radius,rp,?_⟩
  intro transfer small
  have result:=paid transfer small
  constructor
  · calc
      _ ≤ ‖emUnitTransferTest endpoint orientation transfer-emUnitTransferTest endpoint orientation 0‖+
        ‖emUnitTransferTest endpoint orientation 0‖ := norm_le_norm_sub_add _ _
      _ ≤ 1+max ‖emUnitTransferTest endpoint orientation 0‖ ‖emUnitTransferCurrent endpoint orientation 0‖ :=
        add_le_add result.1 (le_max_left _ _)
  · calc
      _ ≤ ‖emUnitTransferCurrent endpoint orientation transfer-emUnitTransferCurrent endpoint orientation 0‖+
        ‖emUnitTransferCurrent endpoint orientation 0‖ := norm_le_norm_sub_add _ _
      _ ≤ 1+max ‖emUnitTransferTest endpoint orientation 0‖ ‖emUnitTransferCurrent endpoint orientation 0‖ :=
        add_le_add result.2 (le_max_right _ _)

end LowEnergy.GaussComposite.ActualEMCarrierOwn

import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMMovingUnitUniform
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualWholeStaticPair

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCarrierOwn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumPhysicalFeedback
open PreparationVacuumStaticPoleResponse
open PreparationVacuumFullOriginResponse PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open PreparationVacuumFullPoleContinuation PreparationVacuumElectromagneticIdentity
open PreparationPhysicalActualGaussChargeCurrent PreparationPhysicalActualLegNormalization
open PreparationPhysicalStaticSpatialCouplingReturn PreparationVacuumOriginalGreenFeedback
open ActualWholeStatic ActualEMObservable ActualElectronOwnerTest MeasureTheory Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] sourceActualPreparedKernel sourceActualPreparedCurrent sourceActualPreparedDetector
  sourceActualLegNormalization sourceActualLegCorrection sourceActualUnitLegRead
  emUnitTransferTest emUnitTransferCurrent emMovingUnitTest emMovingUnitCurrent
  wholeStaticLimit sourceGreen actualElectronFieldTest emUnitSourceTest emUnitSourceCurrent actualWholeMatrixRead

/-- Every unit-current coefficient contains the unchanged all64 original preparation and its full leg correction. -/
def emMovingCorrectedCurrent (endpoint : ActualEMObservationEnd) (pL pR : PhysicalMomentum) (lambda : ℂ) : Fin 289→ℂ :=
  sourceActualPreparedCurrent endpoint.q pL pR endpoint.sideL endpoint.edgeL endpoint.sideR endpoint.edgeR lambda endpoint.window-
    fun i=>sourceActualLegCorrection endpoint.q endpoint.sideL endpoint.edgeL endpoint.sideR endpoint.edgeR
      (sourceActualPreparedKernel endpoint.q pL pR lambda endpoint.window (Pi.single i 1))

theorem em_moving_unit_current_return (endpoint : ActualEMObservationEnd) (pL pR : PhysicalMomentum) (lambda : ℂ)
    (hz : endpoint.q.z.im≠0) (hw : endpoint.q.w.im≠0) :
    emMovingUnitCurrent endpoint pL pR lambda=
      sourceActualLegNormalization endpoint.q endpoint.sideL endpoint.edgeL endpoint.sideR endpoint.edgeR •
        emMovingCorrectedCurrent endpoint pL pR lambda := by
  ext i
  rw [emMovingUnitCurrent,em_moving_unit_full_return endpoint pL pR lambda hz hw,
    sourceActualPreparedDetector_current]
  simp only [Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    Pi.smul_apply,Pi.sub_apply,smul_eq_mul,emMovingCorrectedCurrent]

/-- The original action divides the true dual-unit response once; both endpoint preparations/windows stay independent. -/
def emMovingWholeRead (detector source : ActualEMObservationEnd) (branch : Fin 2)
    (transfer : PhysicalMomentum × ℂ) (M : WholeMatrix) : ℂ :=
  (((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)⁻¹)*
    emUnitTransferTest detector 1 transfer (M*ᵥemUnitTransferCurrent source (-1) transfer)

/-- The same moving source and detector restrictions are opposite original static Fourier transfers. -/
theorem em_moving_static_same_fourier (detector source : ActualEMObservationEnd) (r : ℝ) (n : PhysicalMomentum) :
    actualMomentum (source.momentum+(-1:ℝ) • (r • n)) source.momentum 0=sourceStaticSpatialMomentum n r ∧
    actualMomentum (detector.momentum+(1:ℝ) • (r • n)) detector.momentum 0= -sourceStaticSpatialMomentum n r := by
  constructor
  all_goals
    unfold actualMomentum fullMomentum sourcePhysicalTransfer PreparationVacuumPhysicalFeedback.physicalSpatial sourceStaticSpatialMomentum
    funext i
    fin_cases i <;> simp [Fin.cases,Fin.induction,Fin.induction.go,Pi.smul_apply,smul_eq_mul]

/-- All64 moving dual/source currents and both original corrections are retained by the single-hc matrix response. -/
theorem em_moving_whole_once_action (detector source : ActualEMObservationEnd) (branch : Fin 2)
    (transfer : PhysicalMomentum × ℂ) (M : WholeMatrix)
    (hzd : detector.q.z.im≠0) (hwd : detector.q.w.im≠0) (hzs : source.q.z.im≠0) (hws : source.q.w.im≠0) :
    emMovingWholeRead detector source branch transfer M=
      (sourceActualLegNormalization detector.q detector.sideL detector.edgeL detector.sideR detector.edgeR*
        sourceActualLegNormalization source.q source.sideL source.edgeL source.sideR source.edgeR)/
          ((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)*
      dotProduct (emMovingCorrectedCurrent detector (detector.momentum+transfer.1) detector.momentum (-transfer.2))
        (M*ᵥemMovingCorrectedCurrent source (source.momentum-transfer.1) source.momentum transfer.2) := by
  have detectorTest : emUnitTransferTest detector 1 transfer=
      emMovingUnitTest detector (detector.momentum+transfer.1) detector.momentum (-transfer.2) := by
    simp only [emUnitTransferTest,one_smul,Complex.ofReal_one,neg_one_mul]
  have sourceCurrent : emUnitTransferCurrent source (-1) transfer=
      emMovingUnitCurrent source (source.momentum-transfer.1) source.momentum transfer.2 := by
    ext i
    simp [emUnitTransferCurrent,emUnitTransferTest,emMovingUnitCurrent,sub_eq_add_neg]
  rw [emMovingWholeRead,detectorTest,sourceCurrent,
    ←em_moving_unit_current_read detector (detector.momentum+transfer.1) detector.momentum (-transfer.2)]
  rw [em_moving_unit_current_return detector _ _ _ hzd hwd,em_moving_unit_current_return source _ _ _ hzs hws]
  simp only [Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

private theorem movingWhole_continuous (detector source : ActualEMObservationEnd) (branch : Fin 2)
    (hzd : detector.q.z.im≠0) (hwd : detector.q.w.im≠0) (hzs : source.q.z.im≠0) (hws : source.q.w.im≠0) :
    Continuous (fun p : (PhysicalMomentum × ℂ) × WholeMatrix=>emMovingWholeRead detector source branch p.1 p.2) := by
  have detectorContinuous : Continuous (fun p : (PhysicalMomentum × ℂ) × WholeMatrix=>emUnitTransferTest detector 1 p.1) :=
    (em_unit_transfer_test_continuous detector 1 hzd hwd).comp continuous_fst
  have sourceContinuous : Continuous (fun p : (PhysicalMomentum × ℂ) × WholeMatrix=>emUnitTransferCurrent source (-1) p.1) :=
    (em_unit_transfer_current_continuous source (-1) hzs hws).comp continuous_fst
  exact (detectorContinuous.clm_apply (continuous_snd.matrix_mulVec sourceContinuous)).const_mul _

private theorem moving_direction_bound (n : PhysicalMomentum) (unit : spatialSquare n=1) : ‖n‖≤1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
  intro j
  have paid:=sourceStaticSpatialMomentum_price n unit 1 (by norm_num) j.succ
  fin_cases j
  all_goals simpa [sourceStaticSpatialMomentum] using paid

private theorem moving_transfer_bound (r : ℝ) (positive : 0<r) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ‖((r • n,(0:ℂ)):PhysicalMomentum × ℂ)‖≤r := by
  rw [Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _),norm_smul,Real.norm_eq_abs,abs_of_pos positive]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (moving_direction_bound n unit) positive.le

/-- The real same-transfer moving pair consumes the original full289 uniform limit before any Fourier integration. -/
theorem em_moving_whole_static_uniform (detector source : ActualEMObservationEnd) (branch : Fin 2)
    (hzd : detector.q.z.im≠0) (hwd : detector.q.w.im≠0) (hzs : source.q.z.im≠0) (hws : source.q.w.im≠0)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ radius : ℝ, 0<radius ∧ ∀ r : staticDomain, r.val<radius →
      ∀ n : PhysicalMomentum, ∀ unit : spatialSquare n=1,
        ‖emMovingWholeRead detector source branch (r.val • n,0)
          ((r.val^2:ℝ) • sourceGreen (sourceSpatialStaticRegularPoint n unit r))-
            emMovingWholeRead detector source branch 0 wholeStaticLimit‖≤epsilon := by
  have continuous:=movingWhole_continuous detector source branch hzd hwd hzs hws
  have near:=(continuous.continuousAt (x:=(0,wholeStaticLimit))).tendsto.eventually
    (Metric.ball_mem_nhds (emMovingWholeRead detector source branch 0 wholeStaticLimit) positive)
  obtain ⟨rho,rhop,inside⟩:=Metric.mem_nhds_iff.mp near
  obtain ⟨matrixRadius,mrp,matrixPaid⟩:=whole_static_green_uniform (rho/2) (by positivity)
  refine ⟨min matrixRadius (rho/2),lt_min mrp (by positivity),?_⟩
  intro r small n unit
  have matrixBound := matrixPaid r (lt_of_lt_of_le small (min_le_left _ _)) n unit
  have transferBound := (moving_transfer_bound r.val r.property.1 n unit).trans_lt
    (lt_of_lt_of_le small (min_le_right _ _))
  have membership : (((r.val • n,(0:ℂ)),(r.val^2:ℝ) • sourceGreen (sourceSpatialStaticRegularPoint n unit r)):
      (PhysicalMomentum × ℂ) × WholeMatrix)∈Metric.ball (0,wholeStaticLimit) rho := by
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff,dist_zero_right,dist_eq_norm]
    exact ⟨transferBound.trans (by linarith),matrixBound.trans_lt (by linarith)⟩
  have paid:=inside membership
  change dist (emMovingWholeRead detector source branch (r.val • n,0)
    ((r.val^2:ℝ) • sourceGreen (sourceSpatialStaticRegularPoint n unit r)))
    (emMovingWholeRead detector source branch 0 wholeStaticLimit)<epsilon at paid
  exact (show ‖_ - _‖<epsilon by simpa only [dist_eq_norm] using paid).le

/-- This source-fixed budget contains both original independent unit-current prices and the full289 Green price. -/
def emMovingWholeBudget (detector source : ActualEMObservationEnd) (branch : Fin 2) : ℝ :=
  ‖((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)⁻¹‖*
    emMovingUnitBudget detector 1*wholeStaticBudget*emMovingUnitBudget source (-1)

/-- A shared source radius pays the complete moving response uniformly over the physical unit sphere. -/
theorem em_moving_whole_static_domination (detector source : ActualEMObservationEnd) (branch : Fin 2)
    (hzd : detector.q.z.im≠0) (hwd : detector.q.w.im≠0) (hzs : source.q.z.im≠0) (hws : source.q.w.im≠0) :
    ∃ radius : ℝ, 0<radius ∧ ∀ r : staticDomain, r.val<radius →
      ∀ n : PhysicalMomentum, ∀ unit : spatialSquare n=1,
        ‖emMovingWholeRead detector source branch (r.val • n,0)
          ((r.val^2:ℝ) • sourceGreen (sourceSpatialStaticRegularPoint n unit r))‖≤
            emMovingWholeBudget detector source branch := by
  obtain ⟨rd,rdp,detectorPaid⟩:=em_unit_transfer_domination detector 1 hzd hwd
  obtain ⟨rs,rsp,sourcePaid⟩:=em_unit_transfer_domination source (-1) hzs hws
  obtain ⟨rg,rgp,greenPaid⟩:=whole_static_green_domination
  refine ⟨min rg (min rd rs),lt_min rgp (lt_min rdp rsp),?_⟩
  intro r small n unit
  have rgreen:=lt_of_lt_of_le small (min_le_left _ _)
  have rlegs:=lt_of_lt_of_le small (min_le_right _ _)
  have rdetector:=lt_of_lt_of_le rlegs (min_le_left _ _)
  have rsource:=lt_of_lt_of_le rlegs (min_le_right _ _)
  have transferBound:=moving_transfer_bound r.val r.property.1 n unit
  have d:=(detectorPaid _ (transferBound.trans_lt rdetector)).1
  have s:=(sourcePaid _ (transferBound.trans_lt rsource)).2
  have g:=greenPaid r rgreen n unit
  unfold emMovingWholeRead
  rw [norm_mul]
  calc
    _ ≤ ‖((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)⁻¹‖*
        (‖emUnitTransferTest detector 1 (r.val • n,0)‖*
          (‖(r.val^2:ℝ) • sourceGreen (sourceSpatialStaticRegularPoint n unit r)‖*
            ‖emUnitTransferCurrent source (-1) (r.val • n,0)‖)) :=
      mul_le_mul_of_nonneg_left ((emUnitTransferTest detector 1 _).le_opNorm _ |>.trans
        (mul_le_mul_of_nonneg_left (Matrix.linfty_opNorm_mulVec _ _) (norm_nonneg _))) (norm_nonneg _)
    _ ≤ ‖((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)⁻¹‖*
        (emMovingUnitBudget detector 1*(wholeStaticBudget*emMovingUnitBudget source (-1))) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact mul_le_mul d (mul_le_mul g s (norm_nonneg _) whole_static_budget_nonnegative)
        (by positivity) (em_moving_unit_budget_positive detector 1).le
    _ = emMovingWholeBudget detector source branch := by unfold emMovingWholeBudget;ring

/-- The scaled operator response equals kappa^2 times the actual moving observation, without freezing either current. -/
theorem em_moving_whole_static_scale (detector source : ActualEMObservationEnd) (branch : Fin 2)
    (transfer : PhysicalMomentum × ℂ) (M : WholeMatrix) (r : ℝ) :
    emMovingWholeRead detector source branch transfer ((r^2:ℝ) • M)=
      (r:ℂ)^2*emMovingWholeRead detector source branch transfer M := by
  simp only [emMovingWholeRead,Matrix.smul_mulVec,ContinuousLinearMap.map_smul_of_tower,Complex.real_smul,Complex.ofReal_pow]
  ring

/-- Charged rest preparation is a restriction of the moving unit test at zero transfer. -/
theorem em_moving_unit_rest_test (q : PhysicalResponsePoint) (sL sR : Fin 2) (T orientation : ℝ) :
    emUnitTransferTest ⟨q,0,sL,0,sR,0,T⟩ orientation 0=emUnitSourceTest q sL sR 0 T := by
  simp only [emUnitTransferTest,Prod.fst_zero,Prod.snd_zero,smul_zero,add_zero,mul_zero,
    emMovingUnitTest,emMovingUnitOperator,emMovingFieldKernel,emUnitSourceTest,
    actualElectronOperatorTest,actualElectronFieldKernel]

/-- The limit endpoint is the existing actual unit source current, generated from the moving family itself. -/
theorem em_moving_unit_rest_current (q : PhysicalResponsePoint) (sL sR : Fin 2) (T orientation : ℝ) :
    emUnitTransferCurrent ⟨q,0,sL,0,sR,0,T⟩ orientation 0=emUnitSourceCurrent q sL sR 0 T := by
  funext i
  simp only [emUnitTransferCurrent,em_moving_unit_rest_test,emUnitSourceCurrent]

/-- The true moving-pair zero-transfer value consumes the already generated original rest coefficient when both base momenta are zero. -/
theorem em_moving_whole_origin_rest (branch : Fin 2) (qd qs : PhysicalResponsePoint)
    (dL dR sL sR : Fin 2) (T S : ℝ) :
    emMovingWholeRead ⟨qd,0,dL,0,dR,0,T⟩ ⟨qs,0,sL,0,sR,0,S⟩ branch 0 wholeStaticLimit=
      ActualMasslessStaticPair.actualStaticPairSeed*
        ActualMasslessCurrent.actualUnitMasslessWeight qd dL dR 0 T*
        ActualMasslessCurrent.actualUnitMasslessWeight qs sL sR 0 S/
        ((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ) := by
  rw [←actual_whole_matrix_read_origin branch qd qs dL dR sL sR 0 0 T S]
  rw [emMovingWholeRead,em_moving_unit_rest_test,em_moving_unit_rest_current]
  unfold actualWholeMatrixRead
  change _=actualElectronFieldTest branch qd dL dR 0 T (wholeStaticLimit*ᵥemUnitSourceCurrent qs sL sR 0 S)
  simp only [actualElectronFieldTest,smul_apply,emUnitSourceTest,ContinuousLinearMap.comp_apply,smul_eq_mul]

end LowEnergy.GaussComposite.ActualEMCarrierOwn

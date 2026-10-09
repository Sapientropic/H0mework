import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMResponseSplit
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualElectronOwnerTest

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMObservable
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 CanonicalGradedSpatialSource ProofFreeRicherAnholonomicSource
open ActualEMCarrierOwn ActualEMCurrentSplit ActualEMResponseSplit ActualElectronOwnerTest
open PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalQuantumLockedCharge PreparationPhysicalActualPhaseChargeReturn
open PreparationPhysicalActualGaussChargeCurrent PreparationPhysicalActualLegNormalization
open PreparationPhysicalGaugeMomentumCoupling
open PreparationPhysicalNativePhotonFluxReturn PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open scoped Matrix BigOperators Topology

/-- The bare source vertex fixes the same diagonal four-current at every source point. -/
theorem em_bare_diagonal_current (point : BasePoint) (side edge : Fin 2) :
    emCurrent (actualRestNativeComplexForcingCovector point
      (sourceChargedRestIndex side edge) (sourceChargedRestIndex side edge))=
      ((ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge edge:ℂ)) • emBareRestDirection side := by
  have same : emCurrent (actualRestNativeComplexForcingCovector point
      (sourceChargedRestIndex side edge) (sourceChargedRestIndex side edge))=
      emCurrent (actualRestNativeComplexForcingCovector 0
        (sourceChargedRestIndex side edge) (sourceChargedRestIndex side edge)) := by
    funext mu
    rw [em_rest_current_vertex,em_rest_current_vertex]
  rw [same,em_rest_diagonal_current]

/-- This is the bare charge kernel of the complete source tensor; no static or 1/r limit is asserted. -/
def emBareChargeKernel (G : Matrix (Fin 289) (Fin 289) ℂ) (sideD sideS : Fin 2) : ℂ :=
  (16/9:ℂ)*(ActionNormalization.phaseMomentum:ℂ)^2*
    dotProduct (emBareRestDirection sideD) (emResponseTensor G*ᵥemBareRestDirection sideS)

/-- Actual bare electron/neutral charges factor the pure EM piece while every other response remains in the four-piece carrier. -/
theorem em_bare_pure_charge_product (G : Matrix (Fin 289) (Fin 289) ℂ)
    (pointD pointS : BasePoint) (sideD edgeD sideS edgeS : Fin 2) :
    emPureObservation G
      (actualRestNativeComplexForcingCovector pointD (sourceChargedRestIndex sideD edgeD)
        (sourceChargedRestIndex sideD edgeD))
      (actualRestNativeComplexForcingCovector pointS (sourceChargedRestIndex sideS edgeS)
        (sourceChargedRestIndex sideS edgeS))=
      (sourceActualPhaseCharge edgeD:ℂ)*(sourceActualPhaseCharge edgeS:ℂ)*emBareChargeKernel G sideD sideS := by
  simp only [emPureObservation,emCoordinateCurrent,em_bare_diagonal_current,smul_smul,
    Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul,emBareChargeKernel]
  ring

/-- The actual full source-frequency observation factors its bare charges and retains both mixed terms and the complete rest response. -/
theorem em_bare_frequency_charge_split (epsilon s : ℝ) (n : PhysicalMomentum)
    (pointD pointS : BasePoint) (sideD edgeD sideS edgeS : Fin 2) :
    sourceRestFieldDensityRead pointD
      (sourceChargedRestIndex sideD edgeD,sourceChargedRestIndex sideD edgeD)
      (sourceWholePhotonFrequencyResidue epsilon s n*ᵥactualRestNativeComplexForcingCovector pointS
        (sourceChargedRestIndex sideS edgeS) (sourceChargedRestIndex sideS edgeS))=
      (sourceActualPhaseCharge edgeD:ℂ)*(sourceActualPhaseCharge edgeS:ℂ)*
        emBareChargeKernel (sourceWholePhotonFrequencyResidue epsilon s n) sideD sideS+
      emCurrentObservation (sourceWholePhotonFrequencyResidue epsilon s n)
        (emCurrentForce (actualRestNativeComplexForcingCovector pointD
          (sourceChargedRestIndex sideD edgeD) (sourceChargedRestIndex sideD edgeD)))
        (emCurrentResidual (actualRestNativeComplexForcingCovector pointS
          (sourceChargedRestIndex sideS edgeS) (sourceChargedRestIndex sideS edgeS)))+
      emCurrentObservation (sourceWholePhotonFrequencyResidue epsilon s n)
        (emCurrentResidual (actualRestNativeComplexForcingCovector pointD
          (sourceChargedRestIndex sideD edgeD) (sourceChargedRestIndex sideD edgeD)))
        (emCurrentForce (actualRestNativeComplexForcingCovector pointS
          (sourceChargedRestIndex sideS edgeS) (sourceChargedRestIndex sideS edgeS)))+
      emCurrentObservation (sourceWholePhotonFrequencyResidue epsilon s n)
        (emCurrentResidual (actualRestNativeComplexForcingCovector pointD
          (sourceChargedRestIndex sideD edgeD) (sourceChargedRestIndex sideD edgeD)))
        (emCurrentResidual (actualRestNativeComplexForcingCovector pointS
          (sourceChargedRestIndex sideS edgeS) (sourceChargedRestIndex sideS edgeS))) := by
  rw [em_rest_density_four_parts (sourceWholePhotonFrequencyResidue epsilon s n) pointD pointS
    (sourceChargedRestIndex sideD edgeD,sourceChargedRestIndex sideD edgeD)
    (sourceChargedRestIndex sideS edgeS,sourceChargedRestIndex sideS edgeS),em_bare_pure_charge_product]

/-- The actual normalized detector, as the dual covector of its original full289 test. -/
def emUnitDetectorCovector (branch : Fin 2) (q : PhysicalResponsePoint)
    (sideL sideR : Fin 2) (lambda : ℂ) (T : ℝ) : Fin 289→ℂ :=
  fun i=>actualElectronFieldTest branch q sideL sideR lambda T (Pi.single i 1)

theorem em_unit_detector_actual (branch : Fin 2) (q : PhysicalResponsePoint)
    (sideL sideR : Fin 2) (lambda : ℂ) (T : ℝ) (V : Fin 289→ℂ) :
    dotProduct (emUnitDetectorCovector branch q sideL sideR lambda T) V=
      actualElectronFieldTest branch q sideL sideR lambda T V := by
  have basis : (∑i : Fin 289,V i • (Pi.single i 1:Fin 289→ℂ))=V := by
    funext j
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul,mul_ite]
  calc
    _=actualElectronFieldTest branch q sideL sideR lambda T
        (∑i : Fin 289,V i • (Pi.single i 1:Fin 289→ℂ)) := by
      simp only [map_sum,map_smul,smul_eq_mul,emUnitDetectorCovector,dotProduct]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _=_ := congrArg _ basis

/-- The measured EM four-current is the original actual normalized test on each literal EM insertion column. -/
theorem em_unit_detector_current (branch : Fin 2) (q : PhysicalResponsePoint)
    (sideL sideR : Fin 2) (lambda : ℂ) (T : ℝ) (mu : Fin 4) :
    emCurrent (emUnitDetectorCovector branch q sideL sideR lambda T) mu=
      actualElectronFieldTest branch q sideL sideR lambda T (fun j=>emInsertion j mu) := by
  rw [←em_unit_detector_actual]
  unfold emCurrent
  simp only [Matrix.mulVec,Matrix.transpose_apply,dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Filtering, independent unit normalization and every full-field leg correction remain in this EM current. -/
theorem em_unit_detector_current_return (branch : Fin 2) (q : PhysicalResponsePoint)
    (sideL sideR : Fin 2) (lambda : ℂ) (T : ℝ) (mu : Fin 4)
    (hz : q.z.im≠0) (hw : q.w.im≠0) :
    emCurrent (emUnitDetectorCovector branch q sideL sideR lambda T) mu=
      sourceActualLegNormalization q sideL 0 sideR 0*
        (sourceActualPreparedDetector q 0 0 sideL 0 sideR 0 lambda T (fun j=>emInsertion j mu)-
          sourceActualLegCorrection q sideL 0 sideR 0
            (sourceActualPreparedKernel q 0 0 lambda T (fun j=>emInsertion j mu)))/
        ((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ) := by
  rw [em_unit_detector_current,actualElectronFieldTest_actual branch q sideL sideR lambda T hz hw]
  exact sourceGaugeCouplingRead_generated branch q sideL 0 sideR 0 lambda T _ hz hw

/-- The original actual unit/hc observable directly consumes the complete EM+cross+rest response. -/
theorem em_unit_observable_four_parts (G : Matrix (Fin 289) (Fin 289) ℂ)
    (branch : Fin 2) (qd qs : PhysicalResponsePoint) (dSL dSR sSL sSR : Fin 2)
    (lambda mu : ℂ) (T S : ℝ) (hzd : qd.z.im≠0) (hwd : qd.w.im≠0) :
    sourceGaugeCouplingRead branch qd dSL 0 dSR 0 lambda T
      (G*ᵥsourceActualPreparedCurrent qs 0 0 sSL 0 sSR 0 mu S)=
      emPureObservation G
        (emUnitDetectorCovector branch qd dSL dSR lambda T)
        (sourceActualPreparedCurrent qs 0 0 sSL 0 sSR 0 mu S)+
      emCurrentObservation G
        (emCurrentForce (emUnitDetectorCovector branch qd dSL dSR lambda T))
        (emCurrentResidual (sourceActualPreparedCurrent qs 0 0 sSL 0 sSR 0 mu S))+
      emCurrentObservation G
        (emCurrentResidual (emUnitDetectorCovector branch qd dSL dSR lambda T))
        (emCurrentForce (sourceActualPreparedCurrent qs 0 0 sSL 0 sSR 0 mu S))+
      emCurrentObservation G
        (emCurrentResidual (emUnitDetectorCovector branch qd dSL dSR lambda T))
        (emCurrentResidual (sourceActualPreparedCurrent qs 0 0 sSL 0 sSR 0 mu S)) := by
  rw [←actualElectronFieldTest_actual branch qd dSL dSR lambda T hzd hwd,
    ←em_unit_detector_actual]
  exact em_response_four_parts G _ _

/-- The source-fixed physical-frequency residue is directly consumed by the original normalized electron observable. -/
theorem em_unit_frequency_observable_four_parts (epsilon s : ℝ) (n : PhysicalMomentum)
    (branch : Fin 2) (qd qs : PhysicalResponsePoint) (dSL dSR sSL sSR : Fin 2)
    (lambda mu : ℂ) (T S : ℝ) (hzd : qd.z.im≠0) (hwd : qd.w.im≠0) :
    sourceGaugeCouplingRead branch qd dSL 0 dSR 0 lambda T
      ((sourceWholePhotonFrequencyResidue epsilon s n)*ᵥsourceActualPreparedCurrent qs 0 0 sSL 0 sSR 0 mu S)=
      emPureObservation (sourceWholePhotonFrequencyResidue epsilon s n)
        (emUnitDetectorCovector branch qd dSL dSR lambda T)
        (sourceActualPreparedCurrent qs 0 0 sSL 0 sSR 0 mu S)+
      emCurrentObservation (sourceWholePhotonFrequencyResidue epsilon s n)
        (emCurrentForce (emUnitDetectorCovector branch qd dSL dSR lambda T))
        (emCurrentResidual (sourceActualPreparedCurrent qs 0 0 sSL 0 sSR 0 mu S))+
      emCurrentObservation (sourceWholePhotonFrequencyResidue epsilon s n)
        (emCurrentResidual (emUnitDetectorCovector branch qd dSL dSR lambda T))
        (emCurrentForce (sourceActualPreparedCurrent qs 0 0 sSL 0 sSR 0 mu S))+
      emCurrentObservation (sourceWholePhotonFrequencyResidue epsilon s n)
        (emCurrentResidual (emUnitDetectorCovector branch qd dSL dSR lambda T))
        (emCurrentResidual (sourceActualPreparedCurrent qs 0 0 sSL 0 sSR 0 mu S)) := by
  exact em_unit_observable_four_parts (sourceWholePhotonFrequencyResidue epsilon s n)
    branch qd qs dSL dSR sSL sSR lambda mu T S hzd hwd

/-- The source emitter uses the same original kernel and its own independent unit dual/primal. -/
def emUnitSourceTest (q : PhysicalResponsePoint) (sideL sideR : Fin 2) (mu : ℂ) (S : ℝ) :
    (Fin 289→ℂ)→L[ℂ]ℂ :=
  (actualElectronOperatorTest q sideL sideR).comp (actualElectronFieldKernel q mu S)

def emUnitSourceCurrent (q : PhysicalResponsePoint) (sideL sideR : Fin 2) (mu : ℂ) (S : ℝ) : Fin 289→ℂ :=
  fun i=>emUnitSourceTest q sideL sideR mu S (Pi.single i 1)

def emUnitSourceCorrection (q : PhysicalResponsePoint) (sideL sideR : Fin 2) (mu : ℂ) (S : ℝ) : Fin 289→ℂ :=
  fun i=>sourceActualLegCorrection q sideL 0 sideR 0
    (sourceActualPreparedKernel q 0 0 mu S (Pi.single i 1))

theorem em_unit_source_test_actual (q : PhysicalResponsePoint) (sideL sideR : Fin 2)
    (mu : ℂ) (S : ℝ) (hz : q.z.im≠0) (hw : q.w.im≠0) (V : Fin 289→ℂ) :
    emUnitSourceTest q sideL sideR mu S V=sourceActualUnitFieldRead q sideL 0 sideR 0 mu S V := by
  simp only [emUnitSourceTest,ContinuousLinearMap.comp_apply,
    actualElectronFieldKernel_actual q mu S hz hw V,actualElectronOperatorTest_actual,sourceActualUnitFieldRead]

/-- The actual independently normalized emitter returns its complete original current correction. -/
theorem em_unit_source_current_return (q : PhysicalResponsePoint) (sideL sideR : Fin 2)
    (mu : ℂ) (S : ℝ) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    emUnitSourceCurrent q sideL sideR mu S=sourceActualLegNormalization q sideL 0 sideR 0 •
      (sourceActualPreparedCurrent q 0 0 sideL 0 sideR 0 mu S-emUnitSourceCorrection q sideL sideR mu S) := by
  funext i
  rw [emUnitSourceCurrent,em_unit_source_test_actual q sideL sideR mu S hz hw,
    sourceActualUnitField_return q sideL 0 sideR 0 mu S _ hz hw,
    PreparationPhysicalActualGaussChargeCurrent.sourceActualPreparedDetector_current]
  simp only [Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    Pi.smul_apply,Pi.sub_apply,smul_eq_mul,emUnitSourceCorrection]

/-- Both actual independently normalized electron ends consume the same source-frequency EM tensor and all other terms. -/
theorem em_unit_pair_frequency_observable (epsilon s : ℝ) (n : PhysicalMomentum)
    (branch : Fin 2) (qd qs : PhysicalResponsePoint) (dSL dSR sSL sSR : Fin 2)
    (lambda mu : ℂ) (T S : ℝ) (hzd : qd.z.im≠0) (hwd : qd.w.im≠0) :
    sourceGaugeCouplingRead branch qd dSL 0 dSR 0 lambda T
      (sourceWholePhotonFrequencyResidue epsilon s n*ᵥemUnitSourceCurrent qs sSL sSR mu S)=
      emPureObservation (sourceWholePhotonFrequencyResidue epsilon s n)
        (emUnitDetectorCovector branch qd dSL dSR lambda T) (emUnitSourceCurrent qs sSL sSR mu S)+
      emCurrentObservation (sourceWholePhotonFrequencyResidue epsilon s n)
        (emCurrentForce (emUnitDetectorCovector branch qd dSL dSR lambda T))
        (emCurrentResidual (emUnitSourceCurrent qs sSL sSR mu S))+
      emCurrentObservation (sourceWholePhotonFrequencyResidue epsilon s n)
        (emCurrentResidual (emUnitDetectorCovector branch qd dSL dSR lambda T))
        (emCurrentForce (emUnitSourceCurrent qs sSL sSR mu S))+
      emCurrentObservation (sourceWholePhotonFrequencyResidue epsilon s n)
        (emCurrentResidual (emUnitDetectorCovector branch qd dSL dSR lambda T))
        (emCurrentResidual (emUnitSourceCurrent qs sSL sSR mu S)) := by
  rw [←actualElectronFieldTest_actual branch qd dSL dSR lambda T hzd hwd,←em_unit_detector_actual]
  exact em_response_four_parts (sourceWholePhotonFrequencyResidue epsilon s n) _ _

/-- Source generator/field coordinate reweighting leaves the actual EM/rest split unchanged. -/
theorem em_rescaled_projection (a : ℂ) (nonzero : a≠0) :
    (a⁻¹ • emCoordinateDual)*(a • emInsertion).transpose=emCoordinateProjection := by
  simp only [Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    mul_inv_cancel₀ nonzero,one_smul,emCoordinateProjection]

/-- Field/generator coordinate rescaling cancels against its dual coordinates on the same EM observable. -/
theorem em_rescaled_observable (G : Matrix (Fin 289) (Fin 289) ℂ)
    (a : ℂ) (nonzero : a≠0) (jd js : Fin 4→ℂ) :
    dotProduct (a⁻¹ • jd)
      (((a • emInsertion).transpose*G*(a • emInsertion))*ᵥ(a⁻¹ • js))=
      dotProduct jd (emResponseTensor G*ᵥjs) := by
  simp only [Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mulVec,
    Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul,emResponseTensor]
  field_simp [nonzero]

end LowEnergy.GaussComposite.ActualEMObservable

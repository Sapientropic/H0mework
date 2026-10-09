import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMActualElectronOrdinary

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualElectronOwnerTest
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace YangMills.FullPairing
open PreparationVacuumPhysicalFeedback PreparationVacuumElectromagneticIdentity
open PreparationVacuumGaugeSourceInjection
open Stage10 GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumFullPoleContinuation PreparationVacuumFullOriginResponse
open PreparationVacuumStaticPoleResponse PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumRawJointFeedback PreparationPhysicalActualGaussChargeCurrent
open PreparationPhysicalActualLegNormalization PreparationPhysicalGaugeMomentumCoupling
open PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativePolarizationEmitter
open GaussComposite.PhysicalEMActualElectronOrdinary
open MeasureTheory Filter
open scoped BigOperators Matrix Topology InnerProductSpace
attribute [local irreducible] actualJointKernel sourceActualPreparedKernel
  sourceActualUnitDual sourceActualUnitPrimal sourceActualUnitLegRead sourceActualUnitFieldRead
  sourceGaugeCouplingRead sourceActualPreparedCurrent sourceWholePhotonFrequencyResidue
  sourceGreen originalChange originalReadback contactInverse extendedKernel activeProjection

/-- This functional uses the original independently normalized actual charged legs. -/
def actualElectronOperatorTest (q : PhysicalResponsePoint) (sideL sideR : Fin 2) :
    (H→L[ℂ]H)→L[ℂ]ℂ :=
  -((sourceActualUnitDual q sideL 0 q.z).comp
    (ContinuousLinearMap.apply ℂ H (sourceActualUnitPrimal q sideR 0 q.w)))

theorem actualElectronOperatorTest_actual (q : PhysicalResponsePoint) (sideL sideR : Fin 2)
    (A : H→L[ℂ]H) : actualElectronOperatorTest q sideL sideR A=
      -sourceActualUnitLegRead q sideL 0 sideR 0 A := by
  unfold actualElectronOperatorTest sourceActualUnitLegRead
  rfl

/-- Source-owned finite-age field response before any spectral split. -/
def actualElectronFieldKernel (q : PhysicalResponsePoint) (lambda : ℂ) (T : ℝ) :
    (Fin 289→ℂ)→L[ℂ](H→L[ℂ]H) :=
  ∑i : Fin 289,(ContinuousLinearMap.proj i).smulRight
    (∫t in (0:ℝ)..T,laplaceWeight lambda t • actualJointKernel q 0 0 t i)

private theorem actualKernel_integrable (q : PhysicalResponsePoint) (lambda : ℂ) (T : ℝ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (i : Fin 289) :
    IntervalIntegrable (fun t : ℝ=>laplaceWeight lambda t • actualJointKernel q 0 0 t i)
      volume 0 T := by
  have argument : Continuous (fun t : ℝ=>((0:PhysicalMomentum),(0:PhysicalMomentum),t)) :=
    continuous_const.prodMk (continuous_const.prodMk continuous_id)
  have kernel:=(actualJointKernel_continuous q i hz hw).comp argument
  have weight : Continuous (laplaceWeight lambda) := by unfold laplaceWeight;fun_prop
  exact (weight.smul kernel).intervalIntegrable _ _

theorem actualElectronFieldKernel_actual (q : PhysicalResponsePoint) (lambda : ℂ) (T : ℝ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (V : Fin 289→ℂ) :
    actualElectronFieldKernel q lambda T V=sourceActualPreparedKernel q 0 0 lambda T V := by
  have commuting (t : ℝ) (i : Fin 289) :
      laplaceWeight lambda t • (V i • actualJointKernel q 0 0 t i)=
        V i • (laplaceWeight lambda t • actualJointKernel q 0 0 t i) := smul_comm _ _ _
  simp only [actualElectronFieldKernel,sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply,sourceActualPreparedKernel,Finset.smul_sum,commuting]
  have exchange:=intervalIntegral.integral_finsetSum (s:=Finset.univ) (fun i _=>
    (actualKernel_integrable q lambda T hz hw i).smul (V i))
  simpa only [Pi.smul_apply,intervalIntegral.integral_smul] using exchange.symm

/-- The actual electronic observer is a continuous linear test on the full289 field. -/
def actualElectronFieldTest (branch : Fin 2) (q : PhysicalResponsePoint)
    (sideL sideR : Fin 2) (lambda : ℂ) (T : ℝ) : (Fin 289→ℂ)→L[ℂ]ℂ :=
  (((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)⁻¹) •
    ((actualElectronOperatorTest q sideL sideR).comp (actualElectronFieldKernel q lambda T))

theorem actualElectronFieldTest_actual (branch : Fin 2) (q : PhysicalResponsePoint)
    (sideL sideR : Fin 2) (lambda : ℂ) (T : ℝ) (hz : q.z.im≠0) (hw : q.w.im≠0)
    (V : Fin 289→ℂ) :
    actualElectronFieldTest branch q sideL sideR lambda T V=
      sourceGaugeCouplingRead branch q sideL 0 sideR 0 lambda T V := by
  simp only [actualElectronFieldTest,smul_apply,ContinuousLinearMap.comp_apply,
    actualElectronFieldKernel_actual q lambda T hz hw V,actualElectronOperatorTest_actual,
    sourceGaugeCouplingRead,sourceActualUnitFieldRead,smul_eq_mul,div_eq_mul_inv]
  ring

/-- The owner test acts on precisely the actual ordinary event, including its source reader factor. -/
theorem actualElectronFieldTest_ordinary (branch : Fin 2) (qd qs : PhysicalResponsePoint)
    (dSL dSR sL sR : Fin 2) (lambda mu : ℂ) (T S : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (hzd : qd.z.im≠0) (hwd : qd.w.im≠0) :
    ∀ᶠ e in scaleApproach,
      actualElectronFieldTest branch qd dSL dSR lambda T
        (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
          sourceActualPreparedCurrent qs 0 0 sL 0 sR 0 mu S)=
      sourceActualLegNormalization qd dSL 0 dSR 0*
        (sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
            (sourceActualPreparedCurrent qs 0 0 sL 0 sR 0 mu S)*
          sourceActualPreparedDetector qd 0 0 dSL 0 dSR 0 lambda T
            (sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n)-
          sourceActualLegCorrection qd dSL 0 dSR 0
            (sourceActualPreparedKernel qd 0 0 lambda T
              (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
                sourceActualPreparedCurrent qs 0 0 sL 0 sR 0 mu S)))/
        ((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ) := by
  simpa only [actualElectronFieldTest_actual branch qd dSL dSR lambda T hzd hwd] using
    actualElectronOrdinary_generated branch qd qs dSL dSR sL sR lambda mu T S n unit hzd hwd

/-- The original Green's algebraic contact is evaluated on the same actual source and detector. -/
def actualElectronGreenContact (branch : Fin 2) (qd qs : PhysicalResponsePoint)
    (dSL dSR sL sR : Fin 2) (lambda mu : ℂ) (T S : ℝ) (p : Fin 4→ℂ) : ℂ :=
  actualElectronFieldTest branch qd dSL dSR lambda T
    (originalChange p*ᵥ(contactInverse p*ᵥ
      (originalReadback p*ᵥsourceActualPreparedCurrent qs 0 0 sL 0 sR 0 mu S)))

/-- Full original Green response minus its original propagating part is the generated contact. -/
theorem actualElectronGreen_contact_generated (branch : Fin 2) (qd qs : PhysicalResponsePoint)
    (dSL dSR sL sR : Fin 2) (lambda mu : ℂ) (T S : ℝ) (p : regularSource) :
    actualElectronFieldTest branch qd dSL dSR lambda T
      (sourceGreen p*ᵥsourceActualPreparedCurrent qs 0 0 sL 0 sR 0 mu S)-
    actualElectronFieldTest branch qd dSL dSR lambda T
      (originalChange p.val*ᵥ((activeProjection*(extendedKernel p.val)⁻¹)*ᵥ
        (originalReadback p.val*ᵥsourceActualPreparedCurrent qs 0 0 sL 0 sR 0 mu S)))=
      actualElectronGreenContact branch qd qs dSL dSR sL sR lambda mu T S p.val := by
  unfold actualElectronGreenContact
  have split : sourceGreen p*ᵥsourceActualPreparedCurrent qs 0 0 sL 0 sR 0 mu S=
      originalChange p.val*ᵥ(contactInverse p.val*ᵥ
        (originalReadback p.val*ᵥsourceActualPreparedCurrent qs 0 0 sL 0 sR 0 mu S))+
      originalChange p.val*ᵥ((activeProjection*(extendedKernel p.val)⁻¹)*ᵥ
        (originalReadback p.val*ᵥsourceActualPreparedCurrent qs 0 0 sL 0 sR 0 mu S)) := by
    simp only [sourceGreen,mul_add,add_mul,Matrix.add_mulVec,Matrix.mulVec_mulVec,mul_assoc]
  rw [split,map_add,add_sub_cancel_right]

end LowEnergy.GaussComposite.ActualElectronOwnerTest

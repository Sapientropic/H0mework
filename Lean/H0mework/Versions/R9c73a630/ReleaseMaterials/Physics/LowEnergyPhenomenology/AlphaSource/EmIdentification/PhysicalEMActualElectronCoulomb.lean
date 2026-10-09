import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMActualCoulombScalar
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCoframeChargeObservation

/-! Actual raw Coulomb scalar: the once-Coulomb `sourceGaugeStaticCEM`
contraction of the original `sourceCommonCoulombTensor` by the actual
detector returns `K*D_actual*W_cf` minus the complete leg correction,
with `K` the paid spatial inverse sum.  The detector projection is the
original `actual_origin_kernel_read`/`returnedCurrentWindow_zero` pair;
the source side consumes `sourceNativeSimple_prepared`. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalEMActualElectronCoulomb
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10
open PreparationVacuumFullOriginResponse PreparationVacuumStaticPoleResponse
open PreparationVacuumFullPoleContinuation PreparationVacuumNativeSlowCoupling
open PreparationVacuumPhysicalCharacteristic PreparationVacuumWholeOrigin
open PreparationVacuumFullSlowFieldResponse PreparationVacuumStaticSimpleCoupling
open PreparationVacuumChargedSpatialResponse PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalPoleSheet PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumElectromagneticIdentity
open PreparationPhysicalCommonCurrentStaticRead PreparationPhysicalCommonObservableUnits
open PreparationPhysicalActualGaussChargeCurrent PreparationPhysicalActualLegNormalization
open PreparationPhysicalGaugeMomentumCoupling PreparationPhysicalGaugePreparedStaticCEM
open PreparationPhysicalGaugeSpatialChannelExpansion PreparationPhysicalCoframePreparedReturn
open GaussComposite.PhysicalEMActualStaticWindow
open CanonicalGradedSpatialSource
open GaussUnitaryHistory (Index)
open MeasureTheory Filter Set
open scoped BigOperators Matrix Topology InnerProductSpace

attribute [local irreducible]
  emActualJointKernel sourcePoleRead sourcePolePrepared
  actualCurrent returnedCurrentWindow
  sourceCommonDetector sourceActualPreparedDetector sourceActualPreparedKernel
  sourceActualPreparedWeight
  sourceActualLegNormalization sourceActualLegCorrection sourceGaugeActualCoulombField
  sourceGaugeStaticCEM sourceGaugeStaticAlpha sourceCoframePreparedStatic
  sourceNativeSimple sourceActualPreparedCurrent
  emStaticModeKernel emFullStaticKernel emCompensationStaticKernel
  emFullStaticWindow emCompensationStaticWindow


open GaussComposite.PhysicalEMActualCoulombScalar
open PreparationPhysicalCoframeChargeSelection PreparationPhysicalCoframeChargeExchange
open PreparationPhysicalActualPhaseChargeReturn PreparationVacuumPhysicalQuantumLockedCharge
open FullQuantum FullSpace YangMills.FullPairing

/-- The paid all64 source scalar is the actual source preparation itself. -/
theorem coframeScalar_actual (q : PhysicalResponsePoint)
    (sL eL sR eR : Fin 2) (n : PhysicalMomentum) :
    emCoframeStaticScalar q sL eL sR eR n=
      sourceQuantumChargedRead q sL eL sR eR (sourceCoframePreparedStatic q n) := by
  exact (sourceActualGaussRead_poles q 0 0 sL eL sR eR (sourceCoframePreparedStatic q n)).symm

/-- Same-charge preparations read the complete signed material exchange. -/
theorem coframeScalar_sameCharge (q : PhysicalResponsePoint)
    (sL sR edge : Fin 2) (n : PhysicalMomentum) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    emCoframeStaticScalar q sL edge sR edge n=
      sourceQuantumChargedRead q sL edge sR edge
        (sourceCoframeStaticExchange false q n-sourceCoframeStaticExchange true q n) := by
  rw [coframeScalar_actual,sourceCoframePreparedStatic_charge]
  exact sourceCoframePreparedStatic_sameCharge q n sL sR edge hz hw

/-- Original CEM with independently prepared electron charge ends, before any new inverse. -/
theorem rawCEM_electron_generated (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dSR sL sR : Fin 2) (T : ℝ) (n : PhysicalMomentum)
    (hzd : qd.z.im≠0) (hwd : qd.w.im≠0) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    sourceGaugeStaticCEM branch qd q dSL 0 dSR 0 sL 0 sR 0 T n=
      sourceActualLegNormalization qd dSL 0 dSR 0*
        (((9023/9000:ℂ)*rootTwo*rootFifteen)*
          emActualOriginScalar qd dSL 0 dSR 0 T*
          sourceQuantumChargedRead q sL 0 sR 0
            (sourceCoframeStaticExchange false q n-sourceCoframeStaticExchange true q n)-
          sourceActualLegCorrection qd dSL 0 dSR 0
            (sourceActualPreparedKernel qd 0 0 0 T
              (sourceGaugeActualCoulombField q sL 0 sR 0 n))) := by
  rw [em_staticCEM_scalar_generated branch qd q dSL 0 dSR 0 sL 0 sR 0 T n hzd hwd hz hw,
    coframeScalar_sameCharge q sL sR 0 n hz hw]

/-- Unit source legs consume the same-charge exchange with all source defects. -/
theorem coframeScalar_unit_sameCharge (q : PhysicalResponsePoint)
    (sL sR edge : Fin 2) (n : PhysicalMomentum) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    sourceActualLegNormalization q sL edge sR edge*emCoframeStaticScalar q sL edge sR edge n=
      sourceActualUnitLegRead q sL edge sR edge
        (sourceCoframeStaticExchange false q n-sourceCoframeStaticExchange true q n)-
        sourceActualLegNormalization q sL edge sR edge*
          sourceActualLegCorrection q sL edge sR edge
            (sourceCoframeStaticExchange false q n-sourceCoframeStaticExchange true q n) := by
  rw [coframeScalar_sameCharge q sL sR edge n hz hw,sourceActualUnitLegRead_return]
  ring

/-- Independently normalized actual electron ends retain both complete corrections. -/
theorem rawCEM_bothElectronLegs_generated (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dSR sL sR : Fin 2) (T : ℝ) (n : PhysicalMomentum)
    (hzd : qd.z.im≠0) (hwd : qd.w.im≠0) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    sourceActualLegNormalization q sL 0 sR 0*
      sourceGaugeStaticCEM branch qd q dSL 0 dSR 0 sL 0 sR 0 T n=
      sourceActualLegNormalization qd dSL 0 dSR 0*
        (((9023/9000:ℂ)*rootTwo*rootFifteen)*emActualOriginScalar qd dSL 0 dSR 0 T*
          (sourceActualUnitLegRead q sL 0 sR 0
              (sourceCoframeStaticExchange false q n-sourceCoframeStaticExchange true q n)-
            sourceActualLegNormalization q sL 0 sR 0*
              sourceActualLegCorrection q sL 0 sR 0
                (sourceCoframeStaticExchange false q n-sourceCoframeStaticExchange true q n))-
          sourceActualLegNormalization q sL 0 sR 0*
            sourceActualLegCorrection qd dSL 0 dSR 0
              (sourceActualPreparedKernel qd 0 0 0 T
                (sourceGaugeActualCoulombField q sL 0 sR 0 n))) := by
  rw [em_staticCEM_scalar_generated branch qd q dSL 0 dSR 0 sL 0 sR 0 T n hzd hwd hz hw,
    ←coframeScalar_unit_sameCharge q sL sR 0 n hz hw]
  ring

/-- The original alpha read divides the actual same-electron CEM once by its source h*c. -/
theorem rawAlpha_electron_generated (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dSR sL sR : Fin 2) (T : ℝ) (n : PhysicalMomentum)
    (hzd : qd.z.im≠0) (hwd : qd.w.im≠0) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    sourceGaugeStaticAlpha branch qd q dSL 0 dSR 0 sL 0 sR 0 T n=
      (((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)⁻¹)*
        (sourceActualLegNormalization qd dSL 0 dSR 0*
          (((9023/9000:ℂ)*rootTwo*rootFifteen)*emActualOriginScalar qd dSL 0 dSR 0 T*
            sourceQuantumChargedRead q sL 0 sR 0
              (sourceCoframeStaticExchange false q n-sourceCoframeStaticExchange true q n)-
            sourceActualLegCorrection qd dSL 0 dSR 0
              (sourceActualPreparedKernel qd 0 0 0 T
                (sourceGaugeActualCoulombField q sL 0 sR 0 n)))) := by
  unfold sourceGaugeStaticAlpha
  rw [rawCEM_electron_generated branch qd q dSL dSR sL sR T n hzd hwd hz hw]

end LowEnergy.GaussComposite.PhysicalEMActualElectronCoulomb

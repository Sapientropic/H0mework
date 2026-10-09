import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMActualElectronCoulomb

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
namespace LowEnergy.GaussComposite.PhysicalEMActualElectronOrdinary
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


open PreparationPhysicalNativePolarizationEmitter PreparationPhysicalNativePhotonFluxReturn

attribute [local irreducible] sourceGaugeCouplingRead sourceNativeFrequencyPolarization
  sourceWholePhotonFrequencyResidue sourcePhotonLeftReader

/-- Both original charged preparations feed the full photon residue before matching. -/
theorem actualElectronOrdinary_generated (branch : Fin 2)
    (qd qs : PhysicalResponsePoint) (dSL dSR sL sR : Fin 2)
    (lambda mu : ℂ) (T S : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (hzd : qd.z.im≠0) (hwd : qd.w.im≠0) :
    ∀ᶠ e in scaleApproach,
      sourceGaugeCouplingRead branch qd dSL 0 dSR 0 lambda T
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
  have generated:=sourceActualPreparedDetector_frequency qd 0 0 dSL 0 dSR 0 lambda T
    qs 0 0 sL 0 sR 0 mu S branch n unit
  filter_upwards [generated] with e he
  rw [sourceGaugeCouplingRead_generated branch qd dSL 0 dSR 0 lambda T _ hzd hwd,he]

end LowEnergy.GaussComposite.PhysicalEMActualElectronOrdinary

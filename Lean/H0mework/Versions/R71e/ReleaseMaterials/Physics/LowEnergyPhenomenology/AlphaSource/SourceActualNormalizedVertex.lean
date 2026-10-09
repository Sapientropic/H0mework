import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualLegNorm

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalActualLegNormalization
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open PreparationPhysicalNormalizedFullField PreparationPhysicalChargedEnergyVariation
open PreparationPhysicalChargedEnergyPoleReturn PreparationPhysicalChargedPacketQuantumReturn
open PreparationPhysicalChargedPacketVoltage PreparationVacuumVoltageGaussGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalChargedFieldFactor
open PreparationVacuumChargedLongRangeRead PreparationVacuumCausalPoleResponse
open PreparationVacuumChargedSpatialResponse PreparationVacuumNativeSlowCoupling
open PreparationVacuumFullSlowFieldResponse PreparationVacuumQuantumSlowResidue
open PreparationVacuumPhysicalFeedback PreparationVacuumChargedPacketGreen
open PreparationVacuumPhysicalQuantumLockedCharge PreparationVacuumElectromagneticIdentity
open CanonicalGradedSpatialSource FullQuantum.CoframeResponse FullQuantum.StateGreen
open GaussHistoryHilbert PreparationVacuumStaticVoltageSource
open MeasureTheory Filter
open scoped BigOperators Matrix Topology InnerProductSpace
local instance actualLegVertexIndex : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open Stage10 DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open PreparationPhysicalEnergyWeightsReturn PreparationPhysicalFilteredChargeVoltage
open PreparationPhysicalVoltageEnergyIdentity

open PreparationPhysicalEnergyPoleChargeReturn
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource StageNineHolonomicField
open FullQuantum.Triangular

open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalJointGeneratorEnergyReturn
open PreparationVacuumMixedFieldReturn GaussComposite.PhysicalFullFieldScattering
open Electromagnetic.CanonicalCoframe

open PreparationPhysicalChargedHamiltonianRead PreparationPhysicalChargedScatteringPoleReturn

open PreparationPhysicalChargedVertexDomainReturn PreparationPhysicalChargedScatteringFourierReturn

open PreparationPhysicalChargedScatteringDomainPrice

open PreparationVacuumSoftPoleSelection PreparationVacuumNativePoleTensor PreparationVacuumSharedPoleCarrier
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic PreparationVacuumWholeOrigin

open PreparationPhysicalChargedSoftScatteringReturn PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalScatteringFrequencyWard

open Stage10.CanonicalMatter StageNineCurrentCoframeMatterTemporalPrincipal
open PreparationVacuumGaugeSourceInjection GaussNativeMatter SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates SU7MotherLieAlgebra


open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace YangMills.FullPairing Stage9C.Material.SpinPair
open PreparationPhysicalNativeOriginPhaseWard PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalChargedSoftObservable
open PreparationPhysicalChargedPacketQuantumReturn PreparationPhysicalChargedSoftScatteringReturn
open PreparationPhysicalNormalizedFullField PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open Electromagnetic.CanonicalCoframe FullQuantum.Triangular
open MeasureTheory Filter
open scoped Topology InnerProductSpace

open PreparationPhysicalNativeSoftWardBoundary
open Set

open PreparationPhysicalFinitePoleVertices PreparationPhysicalFiniteOriginCovariance
open PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativeWardFiniteObservation
open PreparationPhysicalNativePolarizationEmitter

open PreparationVacuumFullPoleContinuation PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationPhysicalFiniteObservationSoftReturn PreparationVacuumSoftPoleSelection

open PreparationPhysicalCommonCurrentStaticRead PreparationPhysicalNativePhaseChargeInventory
open SU7MotherGaugeTheory SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction

open PreparationPhysicalActualPhaseChargeReturn
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussCoreHilbert GaussFockLift
open GaussQuantumMultiplier GaussHalfDensity CanonicalGradedCharge GaussHistoryHilbert
open SourceQuantumGaugeSliceCoordinates
local instance : DecidableEq Mode:=Classical.decEq _

open PreparationPhysicalActualGaussChargeCurrent
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumCurrentRegularAnchor PreparationVacuumPhysicalPoleAmputation

open PreparationPhysicalActualNoetherVertexReturn PreparationVacuumPhysicalPoleLegDynamics
open Stage9DEF Stage9DEF.Compatibility
attribute [local irreducible] jointGenerator jointResolvent sourceChargedGaussPrepared

open PreparationPhysicalCommonSpatialGreen
open scoped SchwartzMap

def sourceActualLegNormalization (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) : ℂ :=
  (‖sourceActualAmputatedDual q sL eL q.z‖:ℂ)⁻¹*
    (‖sourceActualAmputatedPrimal q sR eR q.w‖:ℂ)⁻¹

def sourceActualUnitLegRead (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (A : H→L[ℂ]H) : ℂ :=
  sourceActualUnitDual q sL eL q.z (A (sourceActualUnitPrimal q sR eR q.w))

/-- Unit norm is generated from the actual independently dressed dual and primal. -/
theorem sourceActualUnitLegRead_bound (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (left : q.z.im≠0) (right : q.w.im≠0) (A : H→L[ℂ]H) :
    ‖sourceActualUnitLegRead q sL eL sR eR A‖≤‖A‖ := by
  have d:=(sourceActualUnitDual q sL eL q.z).le_opNorm (A (sourceActualUnitPrimal q sR eR q.w))
  rw [sourceActualUnitDual_norm q sL eL q.z left,one_mul] at d
  have a:=A.le_opNorm (sourceActualUnitPrimal q sR eR q.w)
  rw [sourceActualUnitPrimal_norm q sR eR q.w right,mul_one] at a
  exact d.trans a

/-- All single-defect and cross-defect terms are kept on the complete original material generators. -/
def sourceActualLegCorrection (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (A : H→L[ℂ]H) : ℂ :=
  -(sourceActualDualDefect q.epsilon q.precision sL eL q.F)
      (jointResolvent 0 q.F q.z 0 (A (sourceChargedGaussPrepared q.epsilon q.precision sR eR)))-
    sourceActualLegDual q.epsilon q.precision sL eL
      (A (jointResolvent 0 q.F q.w 0 (sourceActualColumnDefect q.epsilon q.precision sR eR q.F)))+
    (sourceActualDualDefect q.epsilon q.precision sL eL q.F)
      (jointResolvent 0 q.F q.z 0
        (A (jointResolvent 0 q.F q.w 0 (sourceActualColumnDefect q.epsilon q.precision sR eR q.F))))

theorem sourceActualUnitLegRead_return (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (A : H→L[ℂ]H) :
    sourceActualUnitLegRead q sL eL sR eR A=
      sourceActualLegNormalization q sL eL sR eR*
        (sourceQuantumChargedRead q sL eL sR eR A+sourceActualLegCorrection q sL eL sR eR A) := by
  simp only [sourceActualUnitLegRead,sourceActualUnitDual,sourceActualUnitPrimal,
    sourceActualAmputatedDual,sourceActualAmputatedPrimal,sourceActualLegNormalization,
    sourceActualLegCorrection,sourceQuantumChargedRead,sourceActualLegDual,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,smul_apply,sub_apply,
    map_smul,map_sub,smul_eq_mul,innerSL_apply_apply]
  ring

/-- The independently normalized dual and primal retain their actual pairing; it is not set to one. -/
theorem sourceActualUnitLeg_pairing (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) :
    sourceActualUnitLegRead q sL eL sR eR 1=
      sourceActualLegNormalization q sL eL sR eR*
        ((if sourceChargedRestIndex sL eL=sourceChargedRestIndex sR eR then 1 else 0)+
          sourceActualLegCorrection q sL eL sR eR 1) := by
  rw [sourceActualUnitLegRead_return]
  simp only [sourceQuantumChargedRead,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,
    one_apply_eq_self,innerSL_apply_apply,sourceChargedGauss_gram]

/-- This is the original doubleGreen vertex on the actual four source columns, with its measured leg factors. -/
theorem sourceActualUnitLegRead_vertex (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (left : q.z.im≠0) (right : q.w.im≠0) (A : H→L[ℂ]H) :
    sourceActualUnitLegRead q sL eL sR eR A=
      sourceActualLegNormalization q sL eL sR eR*
        ((sourceActualChargedRestEnergy sL:ℂ)-q.z)*((sourceActualChargedRestEnergy sR:ℂ)-q.w)*
          sourceQuantumChargedRead q sL eL sR eR
            (jointResolvent 0 q.F q.z 0*A*jointResolvent 0 q.F q.w 0) := by
  simp only [sourceActualUnitLegRead,sourceActualUnitDual,sourceActualUnitPrimal,
    sourceActualPrimal_amputated q sR eR q.w right,sourceActualDual_amputated q sL eL q.z left,
    sourceActualLegNormalization,sourceQuantumChargedRead,sourceActualLegDual,
    smul_apply,map_smul,smul_eq_mul,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,
    mul_apply_eq_comp,innerSL_apply_apply]
  ring

/-- Full charge-transfer response survives the actual external-leg normalization. -/
theorem sourceActualUnitNoether_ward (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    (q.z-q.w)*sourceActualUnitLegRead q sL eL sR eR sourceAbsoluteCharge=
      sourceActualLegNormalization q sL eL sR eR*
        ((sourceActualChargedRestEnergy sL:ℂ)-q.z)*((sourceActualChargedRestEnergy sR:ℂ)-q.w)*
        ((Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge eR:ℂ)*
            sourceQuantumChargedRead q sL eL sR eR (jointResolvent 0 q.F q.z 0)-
          (Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge eL:ℂ)*
            sourceQuantumChargedRead q sL eL sR eR (jointResolvent 0 q.F q.w 0)+
          sourceQuantumChargedRead q sL eL sR eR (sourceAbsoluteNoetherResponse q 0 0)) := by
  rw [sourceActualUnitLegRead_vertex q sL eL sR eR left right]
  have generated:=sourceAbsoluteNoether_prepared q 0 0 sL eL sR eR left right
  unfold sourceAbsoluteNoetherVertex at generated
  linear_combination (sourceActualLegNormalization q sL eL sR eR*
    ((sourceActualChargedRestEnergy sL:ℂ)-q.z)*((sourceActualChargedRestEnergy sR:ℂ)-q.w))*generated

/-- The bare hq Gram is refunded explicitly; every actual leg correction remains in the source-normalized charge vertex. -/
theorem sourceActualUnitCharge_return (q : PhysicalResponsePoint) (i j : ActualPreparedIndex) :
    (Stage10.ActionNormalization.phaseMomentum:ℂ)⁻¹*
      sourceActualUnitLegRead q i.1 i.2 j.1 j.2 sourceAbsoluteCharge=
    sourceActualLegNormalization q i.1 i.2 j.1 j.2*
      (sourcePreparedChargeUnitMatrix i j+(Stage10.ActionNormalization.phaseMomentum:ℂ)⁻¹*
        sourceActualLegCorrection q i.1 i.2 j.1 j.2 sourceAbsoluteCharge) := by
  have gram:=congrArg (fun M : Matrix ActualPreparedIndex ActualPreparedIndex ℂ=>M i j)
    (sourcePreparedChargeUnit_generated q)
  change sourceQuantumChargedRead q i.1 i.2 j.1 j.2 sourceAbsoluteCharge=
    (Stage10.ActionNormalization.phaseMomentum:ℂ)*sourcePreparedChargeUnitMatrix i j at gram
  rw [sourceActualUnitLegRead_return,gram]
  have nonzero : (Stage10.ActionNormalization.phaseMomentum:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr Stage10.ActionNormalization.phaseMomentum_positive.ne'
  field_simp

/-- The same normalized legs read the original full289 field kernel. -/
def sourceActualUnitFieldRead (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (lambda : ℂ) (T : ℝ) (V : Fin 289→ℂ) : ℂ :=
  -sourceActualUnitLegRead q sL eL sR eR (sourceActualPreparedKernel q 0 0 lambda T V)

theorem sourceActualUnitField_return (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (lambda : ℂ) (T : ℝ) (V : Fin 289→ℂ) (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceActualUnitFieldRead q sL eL sR eR lambda T V=
      sourceActualLegNormalization q sL eL sR eR*
        (sourceActualPreparedDetector q 0 0 sL eL sR eR lambda T V-
          sourceActualLegCorrection q sL eL sR eR (sourceActualPreparedKernel q 0 0 lambda T V)) := by
  rw [sourceActualUnitFieldRead,sourceActualUnitLegRead_return,
    sourceActualPreparedDetector_action q 0 0 sL eL sR eR lambda T V left right]
  ring

/-- Spatial source and detector weights remain complete, and the leg correction is evaluated on that actual field. -/
theorem sourceActualUnitSpatial_return (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T c eta : ℝ) (nonzero : c≠0) (positive : 0<eta)
    (left : qd.z.im≠0) (right : qd.w.im≠0)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
      (sourceActualSpatialField q sL eL sR eR c eta test x)=
      sourceActualLegNormalization qd dSL dEL dSR dER*
        (sourceActualSpatialAmplitude q sL eL sR eR c eta test x*
          sourceActualPreparedGaussWeight qd dSL dEL dSR dER T-
        sourceActualLegCorrection qd dSL dEL dSR dER
          (sourceActualPreparedKernel qd 0 0 0 T (sourceActualSpatialField q sL eL sR eR c eta test x))) := by
  rw [sourceActualUnitField_return qd dSL dEL dSR dER 0 T _ left right,
    sourceActualSpatialDetector_generated qd q dSL dEL dSR dER sL eL sR eR T c eta nonzero positive left right]
  rfl

end LowEnergy.PreparationPhysicalActualLegNormalization

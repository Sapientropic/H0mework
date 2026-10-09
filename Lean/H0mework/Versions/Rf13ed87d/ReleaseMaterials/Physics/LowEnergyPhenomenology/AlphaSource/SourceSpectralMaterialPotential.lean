import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceMomentumResonanceTorque

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalMaterialSpectralCharge
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
local instance SpectralPotentialIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

open PreparationVacuumStaticPoleResponse PreparationVacuumFullOriginResponse

open PreparationVacuumStaticSpatialSource PreparationVacuumStaticSimpleCoupling

open PreparationPhysicalCommonCurrentStaticRead PreparationPhysicalActualRetardedWard

open PreparationPhysicalCommonObservableUnits PreparationVacuumPhysicalPinnedVelocity
open PreparationVacuumGaugeSlowFrequency PreparationVacuumQuantumSlowResidue
open PreparationVacuumPhysicalSlowBlock PreparationVacuumSharedPoleCarrier
open PreparationVacuumObservedPoleTensor
open PreparationVacuumActualSpatialPacket
open scoped Matrix.Norms.Operator SchwartzMap

open PreparationPhysicalCommonSpatialGreen PreparationPhysicalActualGaussChargeCurrent
open PreparationPhysicalActualNoetherVertexReturn PreparationPhysicalActualPhaseChargeReturn

open Set GaussianFourier


open PreparationPhysicalChannelGreen


open PreparationPhysicalChannelRadialJet PreparationVacuumObservedStaticResidue


open GaussCoreHilbert SourceJointResidualEnergy PreparationVacuumQuantumSlowResponse
open PreparationPhysicalJointRadialForcing

open PreparationVacuumPhysicalHalfAxis CanonicalGradedCurrent GaussUnitaryHistory
open PreparationPhysicalRetainerResolventSquare PreparationVacuumStaticSpatialSource
open PreparationPhysicalCausalSpatialDilation
open PreparationPhysicalMasterCorrectionReturn PreparationPhysicalPhaseGaugeRealization
open PreparationPhysicalGaugeSeedNull PreparationVacuumFullFieldRiesz PreparationVacuumSourceActionJets
open PreparationPhysicalActionSeedReduction PreparationVacuumLowerClassical PreparationVacuumJointFieldResponse
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumFockGrade56
open GaussCoreDifferential GaussCoreLabel NativeHistoryGrade GaussFockLabel GaussYukawaGrade
open PreparationVacuumPropagationPencil PreparationVacuumRawJointFeedback
open PreparationVacuumPhysicalNumberOneRead PreparationVacuumPhysicalPoleLegDynamics PreparationVacuumPhysicalGradeZeroRead
open PreparationPhysicalLorentzSeedReturn
open PreparationVacuumYukawaTransport

open PreparationPhysicalTriangularSeedReturn PreparationVacuumPhysicalModeContact
open PreparationVacuumPhysicalGaussMaterialContact PreparationVacuumNativeLocalWard
open SourceQuantumResidualGaugeSlice SourceQuantumScalarChart


open PreparationPhysicalOriginConfigurationReturn PreparationVacuumRestModeCoupling
open PreparationPhysicalActionUnits

open PreparationPhysicalCoframeOriginPolynomial
open Stage9DEF Stage9DEF.Compatibility Stage10.ChargedPreparation.Dynamics
open GaussQuantumMultiplier GaussFockLift CanonicalGradedCharge

open PreparationPhysicalCoframePreparedReturn PreparationPhysicalActualGaussChargeCurrent
open PreparationPhysicalNativePhaseChargeInventory PreparationVacuumPhysicalGaussMaterialContact
open PreparationVacuumNativeFieldInjection
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

open PreparationPhysicalGaugeMomentumCoupling PreparationPhysicalActualLegNormalization
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
attribute [local irreducible] sourcePoleRead sourceProjection jointResolvent sourceEqualProjection
  sourceResonanceProjection frameVector frameTest finiteRiesz


open PreparationVacuumFieldConstraintResponse
open PreparationPhysicalCoframeChargeSelection GaussFockPair
open scoped ContDiff
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional


open PreparationPhysicalCoframeChargeExchange PreparationVacuumPhysicalGaussColorTorque
open GaussDiagonalHistory GaussCoframeSpin GaussLiveMomentum

open PreparationVacuumGradedTransport PreparationVacuumUncutYukawa
open CanonicalPhysicalSpatial CanonicalPhysicalWardCore

open PreparationPhysicalMaterialChargeTorque

attribute [local irreducible] sourceChargeOffEnergy

def sourceOffEnergyConfigurationRead (F : GaussUnitaryHistory.Index) (x y : H) : ℂ :=
  ∑i : Channel F,∑j : Channel F,if channelValue F i=channelValue F j then 0 else
    (((channelValue F i-channelValue F j:ℝ):ℂ)⁻¹)*
      sourceC0ConfigurationRead F ((sourceChannelOp F i).adjoint x) (sourceChannelOp F j y)

theorem sourceOffEnergyConfigurationRead_return (F : GaussUnitaryHistory.Index) (x y : H) :
    inner ℂ x (sourceChargeOffEnergy F y)=sourceOffEnergyConfigurationRead F x y :=
  sourceChargeOffEnergy_read F x y

private theorem equal_pair (F : GaussUnitaryHistory.Index) (A : SourceOp) (x y : H) :
    inner ℂ x (sourceEqualProjection F A y)=
      ∑i : Channel F,inner ℂ ((sourceChannelOp F i).adjoint x) (A (sourceEnergyWindow F i y)) := by
  rw [sourceEqualProjection_grouped,sum_apply,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [mul_apply_eq_comp] using
    (ContinuousLinearMap.adjoint_inner_left (sourceChannelOp F i) (A (sourceEnergyWindow F i y)) x).symm

def sourceEqualConfigurationRead (F : GaussUnitaryHistory.Index) (A : SourceOp) (x y : H) : ℂ :=
  sourceOffEnergyConfigurationRead F x (sourceEqualProjection F A y)-
    sourceOffEnergyConfigurationRead F ((sourceEqualProjection F A).adjoint x) y-
    ∑i : Channel F,
      (sourceOffEnergyConfigurationRead F ((sourceChannelOp F i).adjoint x) (A (sourceEnergyWindow F i y))-
        sourceOffEnergyConfigurationRead F (A.adjoint ((sourceChannelOp F i).adjoint x)) (sourceEnergyWindow F i y))

theorem sourceEqualConfigurationRead_return (F : GaussUnitaryHistory.Index) (A : SourceOp) (x y : H) :
    inner ℂ x (sourceEqualMaterialExchange F A y)=sourceEqualConfigurationRead F A x y := by
  simp only [sourceEqualConfigurationRead,←sourceOffEnergyConfigurationRead_return,
    ContinuousLinearMap.adjoint_inner_left,sourceEqualMaterialExchange,sub_apply,mul_apply_eq_comp,
    inner_sub_right,equal_pair]

def sourcePinnedConfigurationRead (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (x y : H) : ℂ :=
  (∑i : Channel F,sourceVelocityChargeRead F n ((sourceChannelOp F i).adjoint x) (sourceEnergyWindow F i y))-
    sourceEqualConfigurationRead F (sourceVelocityLinear F n) x y

theorem sourcePinnedConfigurationRead_return (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (x y : H) :
    inner ℂ x (sourcePinnedMaterialTorque F n y)=sourcePinnedConfigurationRead F n x y := by
  rw [sourcePinnedMaterialTorque,sub_apply,inner_sub_right,equal_pair,sourceEqualConfigurationRead_return]
  simp only [sourceVelocityChargeRead_return,sourcePinnedConfigurationRead]

def sourceResonanceConfigurationRead (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (x y : H) : ℂ :=
  sourcePinnedConfigurationRead F n ((sourceReducedVelocityInverse F n).adjoint x) (sourceResonanceProjection F n 0 y)+
    sourcePinnedConfigurationRead F n ((sourceResonanceProjection F n 0).adjoint x) (sourceReducedVelocityInverse F n y)

theorem sourceResonanceConfigurationRead_return (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (x y : H) :
    inner ℂ x (sourceResonanceMaterialExchange F n y)=sourceResonanceConfigurationRead F n x y := by
  simp only [sourceResonanceConfigurationRead,←sourcePinnedConfigurationRead_return,
    ContinuousLinearMap.adjoint_inner_left,sourceResonanceMaterialExchange,add_apply,mul_apply_eq_comp,inner_add_right]

/-- All spectral insertions now read the same actual native/matter and finite-span configuration objects. -/
def sourceSpectralPreparedStatic (positive : Bool) (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (sL eL sR eR : Fin 2) : ℂ :=
  sourceResonanceConfigurationRead q.F n
    (sourceChargedGaussPrepared q.epsilon q.precision sL eL)
    (sourceEqualProjection q.F (sourceCoframeProjectedChannel positive q)
      (sourceChargedGaussPrepared q.epsilon q.precision sR eR))+
  sourceEqualConfigurationRead q.F (sourceCoframeProjectedChannel positive q)
    ((sourceResonanceProjection q.F n 0).adjoint (sourceChargedGaussPrepared q.epsilon q.precision sL eL))
    (sourceChargedGaussPrepared q.epsilon q.precision sR eR)+
  ∑i : Channel q.F,sourceMaterialChannelRead positive q
    ((sourceResonanceProjection q.F n 0*sourceChannelOp q.F i*sourceProjection).adjoint
      (sourceChargedGaussPrepared q.epsilon q.precision sL eL))
    ((sourceProjection*sourceEnergyWindow q.F i) (sourceChargedGaussPrepared q.epsilon q.precision sR eR))

theorem sourceSpectralPreparedStatic_original (positive : Bool) (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (sL eL sR eR : Fin 2) :
    sourceSpectralPreparedStatic positive q n sL eL sR eR=sourceMaterialPreparedStatic positive q n sL eL sR eR := by
  simp only [sourceSpectralPreparedStatic,←sourceResonanceConfigurationRead_return,
    ←sourceEqualConfigurationRead_return,ContinuousLinearMap.adjoint_inner_left,
    sourceResonanceMaterialExchange_original,sourceEqualMaterialExchange_original,
    sourceMaterialPreparedStatic,sourceQuantumChargedRead,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply,innerSL_apply_apply,add_apply,inner_add_right,mul_apply_eq_comp]

/-- Complete joint pricing is preserved; the component inverse-gap expressions are not separately integrated. -/
theorem sourceSpectralPreparedStatic_integrable (q : PhysicalResponsePoint)
    (sL sR edge : Fin 2) (c eta : ℝ) (frequency : c≠0) (causal : 0<eta)
    (left : q.z.im≠0) (right : q.w.im≠0) (i : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Integrable (fun n : PhysicalMomentum=>sourceSpatialPhase n x*test n*((sourcePoleSide c eta)⁻¹*
      (sourceChargedDenominator (sourceSpatialMomentum n) 0 i)⁻¹*
      sourceSlowRead (sourceOriginPair
        (sourceSpectralPreparedStatic false q (sourceSpatialMomentum n) sL edge sR edge-
          sourceSpectralPreparedStatic true q (sourceSpatialMomentum n) sL edge sR edge)) ⟨i.val,by omega⟩)) volume := by
  simp only [sourceSpectralPreparedStatic_original]
  exact sourceMaterialStaticTorque_integrable q sL sR edge c eta frequency causal left right i test x

theorem sourceSpectralRadialCoupling_return (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL sR edge : Fin 2) (T : ℝ) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (causal : 0<eta) (sourceLeft : q.z.im≠0) (sourceRight : q.w.im≠0)
    (left : qd.z.im≠0) (right : qd.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>(d:ℂ)*sourceGaugeCouplingRead branch qd dSL dEL dSR dER 0 T
      (sourceActualRadialPotential q sL edge sR edge branch negative eta d test x))
      (𝓝[>] 0) (𝓝 (sourceGaugeCouplingRead branch qd dSL dEL dSR dER 0 T
        (∑i : Fin 3,(∫n : PhysicalMomentum,sourceSpatialPhase n x*test n*
          ((sourcePoleSide (sourceSignedSpeed branch negative) eta)⁻¹*
          (sourceChargedDenominator (sourceSpatialMomentum n) 0 i)⁻¹*
          sourceSlowRead (sourceOriginPair
            (sourceSpectralPreparedStatic false q (sourceSpatialMomentum n) sL edge sR edge-
              sourceSpectralPreparedStatic true q (sourceSpatialMomentum n) sL edge sR edge)) ⟨i.val,by omega⟩)) • sourceCommonOriginColumn i))) := by
  simp only [sourceSpectralPreparedStatic_original]
  exact sourceMaterialRadialCoupling_return qd q dSL dEL dSR dER sL sR edge T branch negative eta
    causal sourceLeft sourceRight left right test x

/-- The same generated configuration torque is inserted between the actual two external Green legs and their independent normalizations. -/
def sourceUnitOffEnergyRead (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) : ℂ :=
  sourceActualLegNormalization q sL eL sR eR*
    ((sourceActualChargedRestEnergy sL:ℂ)-q.z)*((sourceActualChargedRestEnergy sR:ℂ)-q.w)*
      sourceOffEnergyConfigurationRead q.F
        ((jointResolvent 0 q.F q.z 0).adjoint (sourceChargedGaussPrepared q.epsilon q.precision sL eL))
        (jointResolvent 0 q.F q.w 0 (sourceChargedGaussPrepared q.epsilon q.precision sR eR))

theorem sourceUnitOffEnergyRead_generated (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceActualUnitLegRead q sL eL sR eR (sourceChargeOffEnergy q.F)=sourceUnitOffEnergyRead q sL eL sR eR := by
  rw [sourceActualUnitLegRead_vertex q sL eL sR eR left right]
  unfold sourceUnitOffEnergyRead
  congr 1
  have paid:=(ContinuousLinearMap.adjoint_inner_left (jointResolvent 0 q.F q.z 0)
    (sourceChargeOffEnergy q.F (jointResolvent 0 q.F q.w 0 (sourceChargedGaussPrepared q.epsilon q.precision sR eR)))
    (sourceChargedGaussPrepared q.epsilon q.precision sL eL)).symm.trans
      (sourceOffEnergyConfigurationRead_return q.F
        ((jointResolvent 0 q.F q.z 0).adjoint (sourceChargedGaussPrepared q.epsilon q.precision sL eL))
        (jointResolvent 0 q.F q.w 0 (sourceChargedGaussPrepared q.epsilon q.precision sR eR)))
  simpa only [sourceQuantumChargedRead,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply,innerSL_apply_apply,mul_apply_eq_comp] using paid

/-- The same independently normalized external vertex inherits the actual finite spectral torque price. -/
theorem sourceUnitOffEnergyRead_bound (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    ‖sourceUnitOffEnergyRead q sL eL sR eR‖ ≤ sourceEnergyChargePrice q.F*‖sourceC0ChargeTorque q.F‖ := by
  rw [←sourceUnitOffEnergyRead_generated q sL eL sR eR left right]
  exact (sourceActualUnitLegRead_bound q sL eL sR eR left right (sourceChargeOffEnergy q.F)).trans
    (sourceChargeOffEnergy_price q.F)

/-- The original h-unit charge read keeps its full source leg correction while exposing the actual energy-transfer contribution. -/
theorem sourceUnitEnergyCharge_balance (q : PhysicalResponsePoint) (i j : ActualPreparedIndex)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceActualUnitLegRead q i.1 i.2 j.1 j.2 (sourceEqualProjection q.F sourceActualGaussCharge)=
      sourceActualLegNormalization q i.1 i.2 j.1 j.2*
        (sourcePreparedChargeUnitMatrix i j+(Stage10.ActionNormalization.phaseMomentum:ℂ)⁻¹*
          sourceActualLegCorrection q i.1 i.2 j.1 j.2 sourceAbsoluteCharge)-sourceUnitOffEnergyRead q i.1 i.2 j.1 j.2 := by
  have unit : (Stage10.ActionNormalization.phaseMomentum:ℂ)⁻¹*
      sourceActualUnitLegRead q i.1 i.2 j.1 j.2 sourceAbsoluteCharge=
      sourceActualUnitLegRead q i.1 i.2 j.1 j.2 sourceActualGaussCharge := by
    simp only [sourceAbsoluteCharge,sourceActualUnitLegRead,smul_apply,map_smul,smul_eq_mul]
    rw [←mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr Stage10.ActionNormalization.phaseMomentum_positive.ne'),one_mul]
  have decomposition : sourceActualUnitLegRead q i.1 i.2 j.1 j.2 sourceActualGaussCharge=
      sourceActualUnitLegRead q i.1 i.2 j.1 j.2 (sourceEqualProjection q.F sourceActualGaussCharge)+
        sourceActualUnitLegRead q i.1 i.2 j.1 j.2 (sourceChargeOffEnergy q.F) := by
    conv_lhs => rw [←sourceChargeEnergy_resolution q.F]
    simp only [sourceActualUnitLegRead,add_apply,map_add]
  have paid:=sourceActualUnitCharge_return q i j
  rw [unit,decomposition,sourceUnitOffEnergyRead_generated q i.1 i.2 j.1 j.2 left right] at paid
  exact eq_sub_of_add_eq paid

end LowEnergy.PreparationPhysicalMaterialSpectralCharge

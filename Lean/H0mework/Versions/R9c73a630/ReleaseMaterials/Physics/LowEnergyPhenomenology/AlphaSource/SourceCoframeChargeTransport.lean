import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCoframeChargeCore

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalCoframeChargeExchange
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
local instance CoframeExchangeTransportIndex : DecidableEq Quantum.Index:=Classical.decEq _
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


open PreparationVacuumFieldConstraintResponse PreparationVacuumPhysicalPoleAmputation
open PreparationPhysicalCoframeChargeSelection GaussFockPair

private def coreReader (F : GaussUnitaryHistory.Index) (M : QuantumTest→ₗ[ℂ]QuantumTest) : SourceOp :=
  finiteRiesz F (fun i j=>sourcePair (frameTest F i) (M (frameTest F j)))

private theorem coreReader_return (F : GaussUnitaryHistory.Index)
    (M : QuantumTest→ₗ[ℂ]QuantumTest) (y : H) :
    coreReader F M y=sourceApprox F (embed (M (sourceTestApprox F y))) := by
  unfold coreReader finiteRiesz
  rw [sourceTestApprox_frame]
  simp only [map_sum,map_smul]
  simp_rw [sourceApprox_frame]
  simp only [Finset.smul_sum,sum_apply,smul_apply,InnerProductSpace.rankOne_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold sourcePair
  rw [frameTest_embed]
  simp only [smul_smul]
  congr 1
  ring

/-- The two finite frame defects are generated by the original core charge before compression. -/
def sourceCoframeCompressionExchange (positive : Bool) (F : GaussUnitaryHistory.Index) : SourceOp :=
  (sourceActualGaussCharge*sourceCoframeChannelReader positive F-
    coreReader F (sourceCoframeChargeCore.comp (sourceCoframeChannelCore positive)))+
  (coreReader F ((sourceCoframeChannelCore positive).comp sourceCoframeChargeCore)-
    sourceCoframeChannelReader positive F*sourceActualGaussCharge)

theorem sourceCoframeCompressionExchange_return (positive : Bool) (F : GaussUnitaryHistory.Index) (y : H) :
    sourceCoframeCompressionExchange positive F y=
      (sourceActualGaussCharge (sourceApprox F (embed (sourceCoframeChannelCore positive (sourceTestApprox F y))))-
        sourceApprox F (sourceActualGaussCharge (embed (sourceCoframeChannelCore positive (sourceTestApprox F y)))))+
      sourceApprox F (embed (sourceCoframeChannelCore positive
        (sourceCoframeChargeCore (sourceTestApprox F y)-sourceTestApprox F (sourceActualGaussCharge y)))) := by
  simp only [sourceCoframeCompressionExchange,add_apply,sub_apply,mul_apply_eq_comp,
    coreReader_return,LinearMap.comp_apply,sourceCoframeChannelReader_return,map_sub,
    sourceCoframeChargeCore_embed]

theorem sourceCoframeChannelReader_ward (positive : Bool) (F : GaussUnitaryHistory.Index) :
    sourceActualGaussCharge*sourceCoframeChannelReader positive F-
      sourceCoframeChannelReader positive F*sourceActualGaussCharge=
      (if positive then (1:ℂ) else -1) • sourceCoframeChannelReader positive F+
        sourceCoframeCompressionExchange positive F := by
  apply ContinuousLinearMap.ext
  intro y
  simp only [sub_apply,mul_apply_eq_comp,add_apply,smul_apply,sourceCoframeCompressionExchange_return]
  simpa only [add_assoc] using sourceCoframeChannelReader_charge positive F y

/-- Both original material inverse identities retain the full joint-generator charge torque. -/
def sourceCoframeGreenExchange (F : GaussUnitaryHistory.Index) (z : ℂ) : SourceOp :=
  jointResolvent 0 F z 0*(jointGenerator 0 F 0 0*sourceActualGaussCharge-
    sourceActualGaussCharge*jointGenerator 0 F 0 0)*jointResolvent 0 F z 0

theorem sourceCoframeGreenExchange_return (F : GaussUnitaryHistory.Index) (z : ℂ) (nonreal : z.im≠0) :
    sourceActualGaussCharge*jointResolvent 0 F z 0-jointResolvent 0 F z 0*sourceActualGaussCharge=
      sourceCoframeGreenExchange F z := by
  have l:=sourceMaterialInverse_left 0 F z nonreal
  have r:=sourceMaterialInverse_right 0 F z nonreal
  have left : jointResolvent 0 F z 0*jointGenerator 0 F 0 0=1+z • jointResolvent 0 F z 0 := by
    rw [mul_sub,mul_smul_comm,mul_one] at l
    exact sub_eq_iff_eq_add.mp l
  have right : jointGenerator 0 F 0 0*jointResolvent 0 F z 0=1+z • jointResolvent 0 F z 0 := by
    rw [sub_mul,smul_mul_assoc,one_mul] at r
    exact sub_eq_iff_eq_add.mp r
  unfold sourceCoframeGreenExchange
  calc
    _=(jointResolvent 0 F z 0*jointGenerator 0 F 0 0)*sourceActualGaussCharge*jointResolvent 0 F z 0-
        jointResolvent 0 F z 0*sourceActualGaussCharge*(jointGenerator 0 F 0 0*jointResolvent 0 F z 0) := by
      rw [left,right]
      simp only [add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,mul_smul_comm]
      abel
    _=_ := by simp only [mul_sub,sub_mul,mul_assoc]

def sourceCoframeGreenChannel (positive : Bool) (q : PhysicalResponsePoint) : SourceOp :=
  jointResolvent 0 q.F q.z 0*((-(gaugeScale/2:ℝ):ℂ) • sourceCoframeChannelReader positive q.F)*
    jointResolvent 0 q.F q.w 0

def sourceCoframeGreenChannelExchange (positive : Bool) (q : PhysicalResponsePoint) : SourceOp :=
  sourceCoframeGreenExchange q.F q.z*((-(gaugeScale/2:ℝ):ℂ) • sourceCoframeChannelReader positive q.F)*jointResolvent 0 q.F q.w 0+
  jointResolvent 0 q.F q.z 0*((-(gaugeScale/2:ℝ):ℂ) • sourceCoframeCompressionExchange positive q.F)*jointResolvent 0 q.F q.w 0+
  jointResolvent 0 q.F q.z 0*((-(gaugeScale/2:ℝ):ℂ) • sourceCoframeChannelReader positive q.F)*sourceCoframeGreenExchange q.F q.w

private theorem product_degree (Q L A R DL DA DR : SourceOp) (s : ℂ)
    (hl : Q*L-L*Q=DL) (ha : Q*A-A*Q=s • A+DA) (hr : Q*R-R*Q=DR) :
    Q*(L*A*R)-(L*A*R)*Q=s • (L*A*R)+(DL*A*R+L*DA*R+L*A*DR) := by
  have middle : DA=Q*A-A*Q-s • A := by rw [ha]; abel
  rw [←hl,←hr,middle]
  simp only [mul_sub,sub_mul,smul_mul_assoc,mul_smul_comm]
  noncomm_ring

theorem sourceCoframeGreenChannel_ward (positive : Bool) (q : PhysicalResponsePoint)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceActualGaussCharge*sourceCoframeGreenChannel positive q-
      sourceCoframeGreenChannel positive q*sourceActualGaussCharge=
      (if positive then (1:ℂ) else -1) • sourceCoframeGreenChannel positive q+
        sourceCoframeGreenChannelExchange positive q := by
  apply product_degree
  · exact sourceCoframeGreenExchange_return q.F q.z left
  · have scaled:=congrArg (fun A : SourceOp=>(-(gaugeScale/2:ℝ):ℂ) • A)
      (sourceCoframeChannelReader_ward positive q.F)
    simpa only [mul_smul_comm,smul_mul_assoc,smul_sub,smul_add,
      smul_comm (if positive then (1:ℂ) else -1) (-(gaugeScale/2:ℝ):ℂ)] using scaled
  · exact sourceCoframeGreenExchange_return q.F q.w right

/-- Actual C0 equal-energy windows retain both spectral charge commutators. -/
def sourceCoframeEqualExchange (F : GaussUnitaryHistory.Index) (A : SourceOp) : SourceOp :=
  ∑i : Channel F,
    ((sourceActualGaussCharge*sourceChannelOp F i-sourceChannelOp F i*sourceActualGaussCharge)*A*sourceEnergyWindow F i+
    sourceChannelOp F i*A*(sourceActualGaussCharge*sourceEnergyWindow F i-sourceEnergyWindow F i*sourceActualGaussCharge))

theorem sourceCoframeEqualExchange_return (F : GaussUnitaryHistory.Index) (A : SourceOp) :
    sourceActualGaussCharge*sourceEqualProjection F A-sourceEqualProjection F A*sourceActualGaussCharge=
      sourceEqualProjection F (sourceActualGaussCharge*A-A*sourceActualGaussCharge)+sourceCoframeEqualExchange F A := by
  simp only [sourceEqualProjection_grouped,sourceCoframeEqualExchange,Finset.mul_sum,
    Finset.sum_mul,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_sub,sub_mul,mul_assoc]
  abel

def sourceCoframeProjectedChannel (positive : Bool) (q : PhysicalResponsePoint) : SourceOp :=
  sourceProjection*sourceCoframeGreenChannel positive q*sourceProjection

def sourceCoframeProjectedExchange (positive : Bool) (q : PhysicalResponsePoint) : SourceOp :=
  (sourceActualGaussCharge*sourceProjection-sourceProjection*sourceActualGaussCharge)*sourceCoframeGreenChannel positive q*sourceProjection+
  sourceProjection*sourceCoframeGreenChannelExchange positive q*sourceProjection+
  sourceProjection*sourceCoframeGreenChannel positive q*(sourceActualGaussCharge*sourceProjection-sourceProjection*sourceActualGaussCharge)

/-- The original zero-velocity spectral surfaces are kept in the actual finite resonance sum. -/
def sourceCoframeResonanceExchange (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) : SourceOp :=
  ∑i : Channel F,if sourceVelocityGap F n 0 i=0 then
    sourceActualGaussCharge*sourcePinnedChannel F n i-sourcePinnedChannel F n i*sourceActualGaussCharge else 0

theorem sourceCoframeResonanceExchange_return (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    sourceActualGaussCharge*sourceResonanceProjection F n 0-
      sourceResonanceProjection F n 0*sourceActualGaussCharge=sourceCoframeResonanceExchange F n := by
  classical
  unfold sourceResonanceProjection sourceCoframeResonanceExchange
  rw [Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp only [mul_zero,zero_mul,sub_self]

def sourceCoframeStaticChannel (positive : Bool) (q : PhysicalResponsePoint) (n : PhysicalMomentum) : SourceOp :=
  sourceResonanceProjection q.F n 0*sourceEqualProjection q.F (sourceCoframeProjectedChannel positive q)

def sourceCoframeStaticExchange (positive : Bool) (q : PhysicalResponsePoint) (n : PhysicalMomentum) : SourceOp :=
  sourceCoframeResonanceExchange q.F n*
    sourceEqualProjection q.F (sourceCoframeProjectedChannel positive q)+
  sourceResonanceProjection q.F n 0*(sourceCoframeEqualExchange q.F (sourceCoframeProjectedChannel positive q)+
    sourceEqualProjection q.F (sourceCoframeProjectedExchange positive q))

theorem sourceCoframeStaticChannel_ward (positive : Bool) (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceActualGaussCharge*sourceCoframeStaticChannel positive q n-
      sourceCoframeStaticChannel positive q n*sourceActualGaussCharge=
      (if positive then (1:ℂ) else -1) • sourceCoframeStaticChannel positive q n+
        sourceCoframeStaticExchange positive q n := by
  have proj : sourceActualGaussCharge*sourceCoframeProjectedChannel positive q-
      sourceCoframeProjectedChannel positive q*sourceActualGaussCharge=
        (if positive then (1:ℂ) else -1) • sourceCoframeProjectedChannel positive q+
          sourceCoframeProjectedExchange positive q :=
    product_degree _ _ _ _ _ _ _ _ rfl (sourceCoframeGreenChannel_ward positive q left right) rfl
  have eqn:=sourceCoframeEqualExchange_return q.F (sourceCoframeProjectedChannel positive q)
  rw [proj,map_add,map_smul] at eqn
  have eqn' : sourceCoframeEqualExchange q.F (sourceCoframeProjectedChannel positive q)+
      sourceEqualProjection q.F (sourceCoframeProjectedExchange positive q)=
      sourceActualGaussCharge*sourceEqualProjection q.F (sourceCoframeProjectedChannel positive q)-
        sourceEqualProjection q.F (sourceCoframeProjectedChannel positive q)*sourceActualGaussCharge-
        (if positive then (1:ℂ) else -1) • sourceEqualProjection q.F (sourceCoframeProjectedChannel positive q) := by
    rw [eqn]
    abel
  unfold sourceCoframeStaticChannel sourceCoframeStaticExchange
  simp only [eqn',←sourceCoframeResonanceExchange_return q.F n,mul_sub,sub_mul,
    mul_smul_comm,mul_assoc]
  abel


theorem sourceCoframeChannelForm_total (a b : QuantumTest) :
    sourceCoframeChannelForm true a b+sourceCoframeChannelForm false a b=sourceCoframeChargeForm a b := by
  rw [sourceCoframeChannelForm,sourceCoframeChannelForm,
    ←integral_add (sourceCoframeChannelForm_integrable true a b) (sourceCoframeChannelForm_integrable false a b)]
  apply integral_congr_ae
  filter_upwards with z
  simp only [sourceCoframeChargeInsertion,pairSample,PiLp.add_apply,mul_add,Finset.sum_add_distrib]

theorem sourceCoframeChannelReader_total (F : GaussUnitaryHistory.Index) :
    sourceCoframeChannelReader true F+sourceCoframeChannelReader false F=sourceCoframeChargeReader F := by
  unfold sourceCoframeChannelReader sourceCoframeChargeReader finiteRiesz
  simp only [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [←sourceCoframeChannelForm_total (frameTest F i) (frameTest F j)]
  exact (add_smul (sourceCoframeChannelForm true (frameTest F i) (frameTest F j))
    (sourceCoframeChannelForm false (frameTest F i) (frameTest F j))
    (InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j))).symm

theorem sourceCoframeStaticChannel_total (q : PhysicalResponsePoint) (n : PhysicalMomentum) :
    sourceCoframeStaticChannel true q n+sourceCoframeStaticChannel false q n=sourceCoframeChargeStatic q n := by
  have generated:=congrArg (fun A : SourceOp=>sourceResonanceProjection q.F n 0*
    sourceEqualProjection q.F (sourceProjection*(jointResolvent 0 q.F q.z 0*
      ((-(gaugeScale/2:ℝ):ℂ) • A)*jointResolvent 0 q.F q.w 0)*sourceProjection))
    (sourceCoframeChannelReader_total q.F)
  simp only [smul_add,mul_add,add_mul,map_add] at generated
  exact generated

/-- The complete original static source is returned through both charge commutators and every generated exchange term. -/
theorem sourceCoframeStaticChannel_return (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceCoframeChargeStatic q n=
      (sourceActualGaussCharge*sourceCoframeStaticChannel true q n-
        sourceCoframeStaticChannel true q n*sourceActualGaussCharge-sourceCoframeStaticExchange true q n)-
      (sourceActualGaussCharge*sourceCoframeStaticChannel false q n-
        sourceCoframeStaticChannel false q n*sourceActualGaussCharge-sourceCoframeStaticExchange false q n) := by
  rw [sourceCoframeStaticChannel_ward true q n left right,sourceCoframeStaticChannel_ward false q n left right]
  simp only [Bool.false_eq_true,if_false,if_true,one_smul]
  rw [←sourceCoframeStaticChannel_total]
  module

end LowEnergy.PreparationPhysicalCoframeChargeExchange

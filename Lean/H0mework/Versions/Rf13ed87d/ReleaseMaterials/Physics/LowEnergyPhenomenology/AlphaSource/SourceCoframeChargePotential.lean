import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCoframeChargeChannels

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalCoframeChargeSelection
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
local instance CoframeChargePotentialIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

/-- Both signed source channels stay together before finite compression and both original Green inverses. -/
def sourceCoframeChargeInsertion (z : SourceCoordinateSlice) (v : FockFiber) : FockFiber :=
  sourceCoframeChargeFiberChannel true z v+sourceCoframeChargeFiberChannel false z v

theorem sourceCoframeFiber_charge (z : SourceCoordinateSlice) (v : FockFiber) :
    sourceCoframeModeFiber z v=sourceCoframeChargeInsertion z v := by
  have generated:=congrArg (fun A : FockFiber→L[ℂ]FockFiber=>A v) (sourceCoframeChargeFiberChannel_total z)
  exact generated.symm

/-- The complete channel sum is the same original Q²A−2QAQ+AQ² insertion, including every input. -/
theorem sourceCoframeChargeInsertion_noether (z : SourceCoordinateSlice) (v : FockFiber) :
    sourceCoframeChargeInsertion z v=
      quantized sourceActualGaussChargeMatrix (quantized sourceActualGaussChargeMatrix (sourceCoframeModeFiber z v))-
      (2:ℂ) • quantized sourceActualGaussChargeMatrix (sourceCoframeModeFiber z (quantized sourceActualGaussChargeMatrix v))+
        sourceCoframeModeFiber z (quantized sourceActualGaussChargeMatrix (quantized sourceActualGaussChargeMatrix v)) := by
  rw [←sourceCoframeFiber_charge]
  have generated:=congrArg (fun A : FockFiber→L[ℂ]FockFiber=>A v) (sourceCoframeCharge_fiber z)
  simp only [sub_apply,mul_apply_eq_comp,map_sub] at generated
  conv_lhs=>rw [←generated]
  module

/-- The complete charge law includes the previously computed four-input part and its entire original full-CAR complement. -/
theorem sourceCoframeChargeInsertion_complete (z : SourceCoordinateSlice) (v : FockFiber) :
    sourceCoframeChargeInsertion z v=sourceCoframePreparedOutput z v+sourceCoframeComplementOutput z v := by
  rw [←sourceCoframeFiber_charge,sourceCoframeFiber_complete]

/-- The whole original configuration form consumes Q²A−2QAQ+AQ² before any compression; no charge-invariant frame is assumed. -/
def sourceCoframeChargeForm (a b : QuantumTest) : ℂ :=
  ∫z,pairSample z (a z) (sourceCoframeChargeInsertion z (b z)) ∂GaussHistoryHilbert.configurationMeasure

theorem sourceCoframeModeForm_charge (a b : QuantumTest) :
    sourceCoframeModeForm a b=sourceCoframeChargeForm a b := by
  unfold sourceCoframeModeForm sourceCoframeChargeForm
  apply integral_congr_ae
  filter_upwards with z
  rw [sourceCoframeFiber_charge]

def sourceCoframeChargeReader (F : GaussUnitaryHistory.Index) : SourceOp :=
  finiteRiesz F (fun i j=>sourceCoframeChargeForm (frameTest F i) (frameTest F j))

theorem sourceCoframePreparedReader_charge (F : GaussUnitaryHistory.Index) :
    sourceCoframePreparedReader F=sourceCoframeChargeReader F := by
  rw [←sourceCoframeModeReader_prepared]
  unfold sourceCoframeModeReader sourceCoframeChargeReader
  simp only [sourceCoframeModeForm_charge]

/-- Q remains inside the original configuration read. FiniteF, both independent Green inverses, C0 equal-energy and angular resonance remain in their exact order. -/
def sourceCoframeChargeStatic (q : PhysicalResponsePoint) (n : PhysicalMomentum) : SourceOp :=
  sourceResonanceProjection q.F n 0*sourceEqualProjection q.F
    (sourceProjection*(jointResolvent 0 q.F q.z 0*
      ((-(gaugeScale/2:ℝ):ℂ) • sourceCoframeChargeReader q.F)*jointResolvent 0 q.F q.w 0)*sourceProjection)

theorem sourceCoframePreparedStatic_charge (q : PhysicalResponsePoint) (n : PhysicalMomentum) :
    sourceCoframePreparedStatic q n=sourceCoframeChargeStatic q n := by
  unfold sourceCoframePreparedStatic sourceCoframeChargeStatic
  rw [sourceCoframePreparedReader_charge]

theorem sourceNativeSimple_charge (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (l r : RestStateIndex) (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceNativeSimple q n l r=sourceOriginPair
      (sourcePoleRead q.epsilon q.precision 0 0 l r (sourceCoframeChargeStatic q n)) := by
  rw [sourceNativeSimple_prepared q n l r left right,sourceCoframePreparedStatic_charge]

/-- The original three-channel spatial read uses the complete source charge-insertion form. -/
def sourceCoframeChargeSimpleChannel (q : PhysicalResponsePoint) (c eta : ℝ)
    (l r : RestStateIndex) (i : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℂ :=
  ∫n : PhysicalMomentum,sourceSpatialPhase n x*test n*
    ((sourcePoleSide c eta)⁻¹*(sourceChargedDenominator (sourceSpatialMomentum n) 0 i)⁻¹*
      sourceSlowRead (sourceOriginPair (sourcePoleRead q.epsilon q.precision 0 0 l r
        (sourceCoframeChargeStatic q (sourceSpatialMomentum n)))) ⟨i.val,by omega⟩)

def sourceCoframeChargeSimpleField (q : PhysicalResponsePoint) (c eta : ℝ)
    (l r : RestStateIndex) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∑i : Fin 3,sourceCoframeChargeSimpleChannel q c eta l r i test x • sourceCommonOriginColumn i

def sourceActualCoframeChargeSimple (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (c eta : ℝ) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∑l : RestStateIndex,∑r : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR l r •
    sourceCoframeChargeSimpleField q c eta l r test x

theorem sourceActualCoframePreparedSimple_charge (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (c eta : ℝ) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceActualCoframePreparedSimple q sL eL sR eR c eta test x=
      sourceActualCoframeChargeSimple q sL eL sR eR c eta test x := by
  simp only [sourceActualCoframePreparedSimple,sourceActualCoframeChargeSimple,
    sourceCoframePreparedSimpleField,sourceCoframeChargeSimpleField,
    sourceCoframePreparedSimpleChannel,sourceCoframeChargeSimpleChannel,sourceCoframePreparedStatic_charge]

/-- The complete original finite potential returns this full-source Noether charge law without subtracting a layer. -/
theorem sourceActualRadialPotential_charge (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (branch : Fin 2) (negative : Bool) (eta : ℝ) (causal : 0<eta)
    (left : q.z.im≠0) (right : q.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>(d:ℂ) • sourceActualRadialPotential q sL eL sR eR branch negative eta d test x)
      (𝓝[>] 0) (𝓝 (sourceActualCoframeChargeSimple q sL eL sR eR (sourceSignedSpeed branch negative) eta test x)) := by
  rw [←sourceActualCoframePreparedSimple_charge]
  exact sourceActualRadialPotential_prepared q sL eL sR eR branch negative eta causal left right test x

/-- Every original independent leg normalization and correction remains in the actual unit observation. -/
theorem sourceActualUnitRadialPotential_charge (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (causal : 0<eta) (sourceLeft : q.z.im≠0) (sourceRight : q.w.im≠0)
    (left : qd.z.im≠0) (right : qd.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>(d:ℂ)*sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
      (sourceActualRadialPotential q sL eL sR eR branch negative eta d test x))
      (𝓝[>] 0) (𝓝 (sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
        (sourceActualCoframeChargeSimple q sL eL sR eR (sourceSignedSpeed branch negative) eta test x))) := by
  rw [←sourceActualCoframePreparedSimple_charge]
  exact sourceActualUnitRadialPotential_prepared qd q dSL dEL dSR dER sL eL sR eR T branch negative eta
    causal sourceLeft sourceRight left right test x

/-- The same source phase momentum and propagation speed read this complete charge-selected potential. -/
theorem sourceGaugeRadialCoupling_charge (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (causal : 0<eta) (sourceLeft : q.z.im≠0) (sourceRight : q.w.im≠0)
    (left : qd.z.im≠0) (right : qd.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>(d:ℂ)*sourceGaugeCouplingRead branch qd dSL dEL dSR dER 0 T
      (sourceActualRadialPotential q sL eL sR eR branch negative eta d test x))
      (𝓝[>] 0) (𝓝 (sourceGaugeCouplingRead branch qd dSL dEL dSR dER 0 T
        (sourceActualCoframeChargeSimple q sL eL sR eR (sourceSignedSpeed branch negative) eta test x))) := by
  rw [←sourceActualCoframePreparedSimple_charge]
  exact sourceGaugeRadialCoupling_prepared qd q dSL dEL dSR dER sL eL sR eR T branch negative eta
    causal sourceLeft sourceRight left right test x

end LowEnergy.PreparationPhysicalCoframeChargeSelection

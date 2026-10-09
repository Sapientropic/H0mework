import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCoframeModePolynomial

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalCoframeOriginPolynomial
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
local instance CoframePotentialIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

open PreparationPhysicalGaugeMomentumCoupling PreparationPhysicalActualLegNormalization
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
attribute [local irreducible] sourcePoleRead sourceProjection jointResolvent sourceEqualProjection
  sourceResonanceProjection frameVector frameTest finiteRiesz sourceOriginConfigurationReader

/-- This integral uses the actual three quadratic coframe weights and full original configuration measure. -/
def sourceCoframeModeForm (a b : QuantumTest) : ℂ :=
  ∫z,pairSample z (a z) (sourceCoframeModeFiber z (b z)) ∂GaussHistoryHilbert.configurationMeasure

theorem sourceModeForm_polynomial (a b : QuantumTest) :
    sourceModeForm a b=sourceCoframeModeForm a b := by
  unfold sourceModeForm sourceCoframeModeForm sourceModeSample
  apply integral_congr_ae
  filter_upwards with z
  by_cases inside : z∈tsupport a
  · rw [sourceModeFiber_polynomial ⟨z,a.tsupport_subset inside⟩]
  · simp only [image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left]

def sourceCoframeModeReader (F : GaussUnitaryHistory.Index) : SourceOp :=
  finiteRiesz F (fun i j=>sourceCoframeModeForm (frameTest F i) (frameTest F j))

theorem sourceModeReader_polynomial (F : GaussUnitaryHistory.Index) :
    sourceModeReader F=sourceCoframeModeReader F := by
  unfold sourceModeReader sourceCoframeModeReader
  simp only [sourceModeForm_polynomial]

/-- Actual material Noether minus configuration deviation is the explicitly computed coframe polynomial vertex. -/
theorem sourceOriginConfigurationReader_polynomial (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    sourceOriginConfigurationReader p F=(-(gaugeScale/2:ℝ):ℂ) • sourceCoframeModeReader F := by
  rw [sourceOriginConfigurationReader_mode,sourceModeReader_generated,sourceModeReader_polynomial]

/-- The same two Green inverses and angular/material projections act on the generated polynomial, in their original order. -/
def sourceCoframeOriginStatic (q : PhysicalResponsePoint) (n : PhysicalMomentum) : SourceOp :=
  sourceResonanceProjection q.F n 0*sourceEqualProjection q.F
    (sourceProjection*(jointResolvent 0 q.F q.z 0*
      ((-(gaugeScale/2:ℝ):ℂ) • sourceCoframeModeReader q.F)*jointResolvent 0 q.F q.w 0)*sourceProjection)

theorem sourceOriginConfigurationStatic_polynomial (q : PhysicalResponsePoint) (n : PhysicalMomentum) :
    sourceOriginConfigurationStatic q n=sourceCoframeOriginStatic q n := by
  unfold sourceOriginConfigurationStatic sourceOriginConfigurationBase sourceCoframeOriginStatic
  rw [sourceOriginConfigurationReader_polynomial]

theorem sourceNativeSimple_polynomial (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (l r : RestStateIndex) (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceNativeSimple q n l r=sourceOriginPair
      (sourcePoleRead q.epsilon q.precision 0 0 l r (sourceCoframeOriginStatic q n)) := by
  rw [sourceNativeSimple_configuration q n l r left right,sourceOriginConfigurationAmplitude_read,
    sourceOriginConfigurationStatic_polynomial]

/-- Original three-channel Fourier read of the computed full configuration polynomial. -/
def sourceCoframeOriginSimpleChannel (q : PhysicalResponsePoint) (c eta : ℝ)
    (l r : RestStateIndex) (i : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℂ :=
  ∫n : PhysicalMomentum,sourceSpatialPhase n x*test n*
    ((sourcePoleSide c eta)⁻¹*(sourceChargedDenominator (sourceSpatialMomentum n) 0 i)⁻¹*
      sourceSlowRead (sourceOriginPair (sourcePoleRead q.epsilon q.precision 0 0 l r
        (sourceCoframeOriginStatic q (sourceSpatialMomentum n)))) ⟨i.val,by omega⟩)

def sourceCoframeOriginSimpleField (q : PhysicalResponsePoint) (c eta : ℝ)
    (l r : RestStateIndex) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∑i : Fin 3,sourceCoframeOriginSimpleChannel q c eta l r i test x • sourceCommonOriginColumn i

/-- The complete actual source64 preparation is preserved under the spatial Fourier read. -/
def sourceActualCoframeOriginSimple (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (c eta : ℝ) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∑l : RestStateIndex,∑r : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR l r •
    sourceCoframeOriginSimpleField q c eta l r test x

theorem sourceActualOriginConfigurationSimple_polynomial (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (c eta : ℝ) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceActualOriginConfigurationSimple q sL eL sR eR c eta test x=
      sourceActualCoframeOriginSimple q sL eL sR eR c eta test x := by
  simp only [sourceActualOriginConfigurationSimple,sourceActualCoframeOriginSimple,
    sourceOriginConfigurationSimpleField,sourceCoframeOriginSimpleField,
    sourceOriginConfigurationSimpleChannel,sourceCoframeOriginSimpleChannel,
    sourceOriginConfigurationStatic_polynomial]

/-- The un-subtracted original whole potential has this source-generated polynomial configuration numerator. -/
theorem sourceActualRadialPotential_polynomial (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (branch : Fin 2) (negative : Bool) (eta : ℝ) (causal : 0<eta)
    (left : q.z.im≠0) (right : q.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>(d:ℂ) • sourceActualRadialPotential q sL eL sR eR branch negative eta d test x)
      (𝓝[>] 0) (𝓝 (sourceActualCoframeOriginSimple q sL eL sR eR (sourceSignedSpeed branch negative) eta test x)) := by
  rw [←sourceActualOriginConfigurationSimple_polynomial]
  exact sourceActualRadialPotential_configuration q sL eL sR eR branch negative eta causal left right test x

/-- Independent unit preparation retains all leg normalization and correction terms in this same whole-potential read. -/
theorem sourceActualUnitRadialPotential_polynomial (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (causal : 0<eta) (sourceLeft : q.z.im≠0) (sourceRight : q.w.im≠0)
    (left : qd.z.im≠0) (right : qd.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>(d:ℂ)*sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
      (sourceActualRadialPotential q sL eL sR eR branch negative eta d test x))
      (𝓝[>] 0) (𝓝 (sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
        (sourceActualCoframeOriginSimple q sL eL sR eR (sourceSignedSpeed branch negative) eta test x))) := by
  rw [←sourceActualOriginConfigurationSimple_polynomial]
  exact sourceActualUnitRadialPotential_configuration qd q dSL dEL dSR dER sL eL sR eR T branch negative eta
    causal sourceLeft sourceRight left right test x

/-- The same source clock and propagation speed read the actual polynomial numerator through the original h*c coupling. -/
theorem sourceGaugeRadialCoupling_polynomial (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (causal : 0<eta) (sourceLeft : q.z.im≠0) (sourceRight : q.w.im≠0)
    (left : qd.z.im≠0) (right : qd.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>(d:ℂ)*sourceGaugeCouplingRead branch qd dSL dEL dSR dER 0 T
      (sourceActualRadialPotential q sL eL sR eR branch negative eta d test x))
      (𝓝[>] 0) (𝓝 (sourceGaugeCouplingRead branch qd dSL dEL dSR dER 0 T
        (sourceActualCoframeOriginSimple q sL eL sR eR (sourceSignedSpeed branch negative) eta test x))) := by
  rw [←sourceActualOriginConfigurationSimple_polynomial]
  exact sourceGaugeRadialCoupling_configuration qd q dSL dEL dSR dER sL eL sR eR T branch negative eta
    causal sourceLeft sourceRight left right test x

end LowEnergy.PreparationPhysicalCoframeOriginPolynomial

import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceOriginConfigurationNumerator
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceGaugeCouplingObservation
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativePoleBalance

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalOriginConfigurationReturn
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
local instance OriginPotentialIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
open PreparationPhysicalGaugeMomentumCoupling
open PreparationPhysicalActualLegNormalization

-- Match the original symbolic grade resolution; do not enumerate its 28,785 labels.
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _

attribute [local irreducible] sourcePoleRead sourceProjection jointResolvent sourceEqualProjection
  sourceResonanceProjection frameVector frameTest finiteRiesz sourceOriginConfigurationReader

open Lean Elab Term in
elab "paidOriginConfigurationScale%" : term => do
  let wanted:=`LowEnergy.PreparationVacuumPoleConstraintReturn.source_scale
  let all:=(←getEnv).constants.toList
  let candidates:=all.filter fun (name,_)=>name.toString.startsWith "_private.H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativePoleBalance." && privateToUserName name==wanted
  match candidates with
  | [(name,_)]=>logInfo m!"Original private payer: {name}";return mkConst name
  | _=>throwError "Expected unique original SourceNativePoleBalance.source_scale; actual candidates: {all.filterMap (fun (name,_)=>if privateToUserName name==wanted then some name else none)}"

/-- The actual source-mode coefficient cancels the original reference-gauge scale exactly. -/
theorem sourceOriginConfigurationAmplitude_read (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (l r : RestStateIndex) : sourceOriginConfigurationAmplitude q n l r=
      sourcePoleRead q.epsilon q.precision 0 0 l r (sourceOriginConfigurationStatic q n) := by
  unfold sourceOriginConfigurationAmplitude
  rw [←(paidOriginConfigurationScale%)]
  have nonzero : ((gaugeScale/2:ℝ):ℂ)≠0:=Complex.ofReal_ne_zero.mpr
    (div_ne_zero gaugeScale_pos.ne' (by norm_num))
  rw [mul_inv_cancel₀ nonzero,one_mul]

/-- Both integrals remain the actual whole Gauss configuration forms, with W*S quantized before the Noether commutator. -/
def sourceOriginConfigurationEntry (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (i j : FrameIndex F) : ℂ :=
  (4*Complex.I)*sourceQuantumCommForm p (frameTest F i) (frameTest F j)-
    sourceDeviationForm p (frameTest F i) (frameTest F j)

theorem sourceOriginConfigurationReader_entries (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    sourceOriginConfigurationReader p F=finiteRiesz F (sourceOriginConfigurationEntry p F) := by
  unfold sourceOriginConfigurationReader sourceQuantumCommReader sourceDeviationReader finiteRiesz sourceOriginConfigurationEntry
  simp only [Finset.smul_sum,Finset.sum_sub_distrib,sub_smul,mul_smul]

attribute [local irreducible] sourceOriginConfigurationEntry sourceQuantumCommForm sourceDeviationForm

/-- Exact original Fourier numerator, preserving the original phase, three denominators and material/angular projection order. -/
def sourceOriginConfigurationSimpleChannel (q : PhysicalResponsePoint) (c eta : ℝ)
    (l r : RestStateIndex) (i : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℂ :=
  ∫n : PhysicalMomentum,sourceSpatialPhase n x*test n*
    ((sourcePoleSide c eta)⁻¹*(sourceChargedDenominator (sourceSpatialMomentum n) 0 i)⁻¹*
      sourceSlowRead (sourceOriginPair (sourcePoleRead q.epsilon q.precision 0 0 l r
        (sourceOriginConfigurationStatic q (sourceSpatialMomentum n)))) ⟨i.val,by omega⟩)

theorem sourceMasterSpatialSimpleChannel_configuration (q : PhysicalResponsePoint) (c eta : ℝ)
    (l r : RestStateIndex) (left : q.z.im≠0) (right : q.w.im≠0) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceMasterSpatialSimpleChannel q c eta l r i test x=sourceOriginConfigurationSimpleChannel q c eta l r i test x := by
  unfold sourceMasterSpatialSimpleChannel sourceOriginConfigurationSimpleChannel
  apply integral_congr_ae
  filter_upwards with n
  rw [sourceNativeSimple_configuration q _ l r left right,sourceOriginConfigurationAmplitude_read]

def sourceOriginConfigurationSimpleField (q : PhysicalResponsePoint) (c eta : ℝ)
    (l r : RestStateIndex) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∑i : Fin 3,sourceOriginConfigurationSimpleChannel q c eta l r i test x • sourceCommonOriginColumn i

theorem sourceMasterSpatialSimpleField_configuration (q : PhysicalResponsePoint) (c eta : ℝ)
    (l r : RestStateIndex) (left : q.z.im≠0) (right : q.w.im≠0)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceMasterSpatialSimpleField q c eta l r test x=sourceOriginConfigurationSimpleField q c eta l r test x := by
  simp only [sourceMasterSpatialSimpleField,sourceOriginConfigurationSimpleField,
    sourceMasterSpatialSimpleChannel_configuration q c eta l r left right]

/-- The original actual source64 preparation coefficients retain the same whole configuration numerator. -/
def sourceActualOriginConfigurationSimple (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (c eta : ℝ) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∑l : RestStateIndex,∑r : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR l r •
    sourceOriginConfigurationSimpleField q c eta l r test x

theorem sourceActualMasterSpatialSimple_configuration (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (c eta : ℝ) (left : q.z.im≠0) (right : q.w.im≠0)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceActualMasterSpatialSimple q sL eL sR eR c eta test x=
      sourceActualOriginConfigurationSimple q sL eL sR eR c eta test x := by
  simp only [sourceActualMasterSpatialSimple,sourceActualOriginConfigurationSimple,
    sourceMasterSpatialSimpleField_configuration q c eta _ _ left right]

/-- The same complete finite radial forcing/potential returns this computed whole configuration numerator, with no added subtraction or change of observation. -/
theorem sourceActualRadialPotential_configuration (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (branch : Fin 2) (negative : Bool) (eta : ℝ) (causal : 0<eta)
    (left : q.z.im≠0) (right : q.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>(d:ℂ) • sourceActualRadialPotential q sL eL sR eR branch negative eta d test x)
      (𝓝[>] 0) (𝓝 (sourceActualOriginConfigurationSimple q sL eL sR eR (sourceSignedSpeed branch negative) eta test x)) := by
  rw [←sourceActualMasterSpatialSimple_configuration q sL eL sR eR _ eta left right]
  exact sourceActualRadialPotential_simple q sL eL sR eR branch negative eta causal left right test x

/-- Independent actual unit legs retain every norm and correction when they read the configuration-generated whole-potential limit. -/
theorem sourceActualUnitRadialPotential_configuration (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (causal : 0<eta) (sourceLeft : q.z.im≠0) (sourceRight : q.w.im≠0)
    (left : qd.z.im≠0) (right : qd.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>(d:ℂ)*sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
      (sourceActualRadialPotential q sL eL sR eR branch negative eta d test x))
      (𝓝[>] 0) (𝓝 (sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
        (sourceActualOriginConfigurationSimple q sL eL sR eR (sourceSignedSpeed branch negative) eta test x))) := by
  rw [←sourceActualMasterSpatialSimple_configuration q sL eL sR eR _ eta sourceLeft sourceRight]
  exact sourceActualUnitRadialPotential_simple qd q dSL dEL dSR dER sL eL sR eR T branch negative eta causal
    sourceLeft sourceRight left right test x

/-- The original action-clock and propagation-speed consumer reads the same complete potential and computed configuration numerator. -/
theorem sourceGaugeRadialCoupling_configuration (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (causal : 0<eta) (sourceLeft : q.z.im≠0) (sourceRight : q.w.im≠0)
    (left : qd.z.im≠0) (right : qd.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun d : ℝ=>(d:ℂ)*sourceGaugeCouplingRead branch qd dSL dEL dSR dER 0 T
      (sourceActualRadialPotential q sL eL sR eR branch negative eta d test x))
      (𝓝[>] 0) (𝓝 (sourceGaugeCouplingRead branch qd dSL dEL dSR dER 0 T
        (sourceActualOriginConfigurationSimple q sL eL sR eR (sourceSignedSpeed branch negative) eta test x))) := by
  have original:=(sourceActualUnitRadialPotential_configuration qd q dSL dEL dSR dER sL eL sR eR T
    branch negative eta causal sourceLeft sourceRight left right test x).div_const
      (((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ))
  simpa only [sourceGaugeCouplingRead,mul_div_assoc] using original

end LowEnergy.PreparationPhysicalOriginConfigurationReturn

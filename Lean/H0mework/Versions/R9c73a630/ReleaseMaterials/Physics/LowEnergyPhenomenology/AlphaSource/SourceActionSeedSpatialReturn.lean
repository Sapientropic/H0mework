import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActionSeedSupport

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalActionSeedReduction
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
local instance ActionSpatialIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
open PreparationPhysicalGaugeSeedNull

attribute [local irreducible] sourceMasterSpatialChannel sourceActualMasterSpatialField sourceActualPreparedWeight
  sourceMasterNative sourceActionSlowSeed sourcePoleRead

/-- Original physical Fourier phase and all remaining source columns define the same spatial master. -/
def sourceActionSpatialChannel (q : PhysicalResponsePoint) (zeta : ℂ) (l r : RestStateIndex) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℂ :=
  ∫n : PhysicalMomentum,sourceSpatialPhase n x*test n*
    sourceActionMasterChannel q (sourceSpatialMomentum n) zeta l r i

theorem sourceMasterSpatialChannel_action (q : PhysicalResponsePoint) (zeta : ℂ) (l r : RestStateIndex)
    (left : q.z.im≠0) (right : q.w.im≠0) (i : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceMasterSpatialChannel q zeta l r i test x=sourceActionSpatialChannel q zeta l r i test x := by
  unfold sourceMasterSpatialChannel sourceActionSpatialChannel
  apply integral_congr_ae
  filter_upwards with n
  change sourceSpatialPhase n x*test n*sourceMasterChannel q (sourceSpatialMomentum n) zeta l r i=_
  rw [sourceMasterChannel_action q _ zeta l r left right i]

/-- The actual remaining seed is integrable in the original Schwartz observation on the same source causal side. -/
theorem sourceActionSpatial_integrable (q : PhysicalResponsePoint) (c eta : ℝ) (frequency : c≠0)
    (causal : 0<eta) (l r : RestStateIndex) (left : q.z.im≠0) (right : q.w.im≠0) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Integrable (fun n : PhysicalMomentum=>sourceSpatialPhase n x*test n*
      sourceActionMasterChannel q (sourceSpatialMomentum n) (sourcePoleSide c eta) l r i) := by
  have paid:=(paidDilationMaster% master_integrable) q c eta frequency causal l r i test x
  apply paid.congr
  filter_upwards with n
  change sourceSpatialPhase n x*test n*sourceMasterChannel q (sourceSpatialMomentum n) (sourcePoleSide c eta) l r i=_
  rw [sourceMasterChannel_action q _ _ l r left right i]

/-- Gauge-seed cancellation preserves the already generated whole spatial master derivative, including every remaining source term. -/
theorem sourceActionSpatial_derivative (q : PhysicalResponsePoint) (c eta : ℝ) (frequency : c≠0)
    (causal : 0<eta) (l r : RestStateIndex) (left : q.z.im≠0) (right : q.w.im≠0) (i : Fin 3)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    HasDerivAt (fun z : ℂ=>sourceActionSpatialChannel q z l r i test x)
      (sourceMasterSpatialChannelDerivative q (sourcePoleSide c eta) l r i test x) (sourcePoleSide c eta) := by
  have paid:=sourceMasterSpatialChannel_derivative q c eta frequency causal l r i test x
  exact paid.congr_of_eventuallyEq (Eventually.of_forall (fun z=>
    (sourceMasterSpatialChannel_action q z l r left right i test x).symm))

def sourceActionSpatialField (q : PhysicalResponsePoint) (zeta : ℂ) (l r : RestStateIndex)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∑i : Fin 3,sourceActionSpatialChannel q zeta l r i test x • sourceCommonOriginColumn i

theorem sourceMasterSpatialField_action (q : PhysicalResponsePoint) (zeta : ℂ) (l r : RestStateIndex)
    (left : q.z.im≠0) (right : q.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceMasterSpatialField q zeta l r test x=sourceActionSpatialField q zeta l r test x := by
  simp only [sourceMasterSpatialField,sourceActionSpatialField,sourceMasterSpatialChannel_action q zeta l r left right]

def sourceActualActionSpatialField (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (zeta : ℂ)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : Fin 289→ℂ :=
  ∑l : RestStateIndex,∑r : RestStateIndex,sourceActualPreparedWeight 0 0 sL eL sR eR l r •
    sourceActionSpatialField q zeta l r test x

/-- All actual source64 weights consume the source-generated 49-column action seed, with every original external preparation unchanged. -/
theorem sourceActualMasterSpatialField_action (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (zeta : ℂ)
    (left : q.z.im≠0) (right : q.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceActualMasterSpatialField q sL eL sR eR zeta test x=
      sourceActualActionSpatialField q sL eL sR eR zeta test x := by
  simp only [sourceActualMasterSpatialField,sourceActualActionSpatialField,sourceMasterSpatialField_action q zeta _ _ left right]

open PreparationPhysicalActualLegNormalization

/-- The same independently normalized detector reads the original complete physical spatial response through the computed remaining master seed. -/
theorem sourceActualUnitAction_derivative (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T c eta : ℝ) (frequency : c≠0) (causal : 0<eta)
    (sourceLeft : q.z.im≠0) (sourceRight : q.w.im≠0) (left : qd.z.im≠0) (right : qd.w.im≠0)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    HasDerivAt (fun z : ℂ=>sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
      (sourceActualActionSpatialField q sL eL sR eR z test x))
      (sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T (sourceActualSpatialField q sL eL sR eR c eta test x)-
        sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
          (sourceActualMasterSpatialCorrection q sL eL sR eR (sourcePoleSide c eta) test x)) (sourcePoleSide c eta) := by
  have paid:=sourceActualUnitMaster_derivative qd q dSL dEL dSR dER sL eL sR eR T c eta frequency causal left right test x
  apply paid.congr_of_eventuallyEq
  filter_upwards with z
  rw [sourceActualMasterSpatialField_action q sL eL sR eR z sourceLeft sourceRight test x]

/-- The original finite radial potential and complete correction are directly consumed after the actual192 action-reader and48 gauge-seed cancellation. -/
theorem sourceActualUnitAction_radialDerivative (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (causal : 0<eta) (d : ℝ) (radial : 0<d)
    (sourceLeft : q.z.im≠0) (sourceRight : q.w.im≠0) (left : qd.z.im≠0) (right : qd.w.im≠0)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    HasDerivAt (fun s : ℝ=>sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
      (sourceActualActionSpatialField q sL eL sR eR ((s:ℂ)*sourcePoleSide (sourceSignedSpeed branch negative) eta) test x))
      (sourcePoleSide (sourceSignedSpeed branch negative) eta*
        (sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T (sourceActualRadialPotential q sL eL sR eR branch negative eta d test x)-
          sourceActualUnitFieldRead qd dSL dEL dSR dER 0 T
            (sourceActualMasterSpatialCorrection q sL eL sR eR ((d:ℂ)*sourcePoleSide (sourceSignedSpeed branch negative) eta) test x))) d := by
  have paid:=sourceActualUnitMaster_radialDerivative qd q dSL dEL dSR dER sL eL sR eR T branch negative eta causal d radial left right test x
  apply paid.congr_of_eventuallyEq
  filter_upwards with s
  rw [sourceActualMasterSpatialField_action q sL eL sR eR _ sourceLeft sourceRight test x]

/-- The fixed-side dilation carrier also retains precisely the same original 49-column action remainder. -/
theorem sourceActionSpatial_dilation (q : PhysicalResponsePoint) (c eta : ℝ) (frequency : c≠0)
    (causal : 0<eta) (s : ℝ) (positive : 0<s) (l r : RestStateIndex)
    (left : q.z.im≠0) (right : q.w.im≠0) (i : Fin 3) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    sourceActionSpatialChannel q (sourcePoleSide (s*c) (s*eta)) l r i test x=
      (s:ℂ)*sourceActionSpatialChannel q (sourcePoleSide c eta) l r i (sourceDilatedTest s positive.ne' test) (s • x) := by
  rw [←sourceMasterSpatialChannel_action q _ l r left right,←sourceMasterSpatialChannel_action q _ l r left right]
  exact sourceMasterSpatialChannel_dilation q c eta frequency causal s positive l r i test x

end LowEnergy.PreparationPhysicalActionSeedReduction

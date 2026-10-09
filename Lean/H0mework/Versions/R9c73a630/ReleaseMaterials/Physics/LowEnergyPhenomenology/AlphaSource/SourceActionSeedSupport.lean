import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActionReaderNull

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
local instance ActionSupportIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
attribute [local irreducible] sourceRetainerSeed sourceNonGaugeSeed sourceNativeReaderFirst sourcePoleRead slowFastFrame

/-- This support is the original scalar9, coframe16 and Lorentz24 coordinate set. -/
def sourceActionSeedSupport : Finset (Fin 289) :=
  Finset.univ.filter (fun j=>j.val<9 ∨ (57≤j.val ∧ j.val<73) ∨ (121≤j.val ∧ j.val<145))

theorem sourceActionSeedSupport_card : sourceActionSeedSupport.card=49 := by decide

def sourceActionSeed (q : PhysicalResponsePoint) (j : Fin 289) : SourceOp :=
  if j∈sourceActionSeedSupport then sourceRetainerSeed q j else 0

/-- The full source retainer has exactly the computed physical action support; original external state coordinates remain independent. -/
theorem sourceRetainerSeed_action (q : PhysicalResponsePoint) (left : q.z.im≠0) (right : q.w.im≠0)
    (j : Fin 289) : sourceRetainerSeed q j=sourceActionSeed q j := by
  unfold sourceActionSeed
  split_ifs with active
  · rfl
  · have outside : ¬(j.val<9 ∨ (57≤j.val ∧ j.val<73) ∨ (121≤j.val ∧ j.val<145)) := by
      simpa only [sourceActionSeedSupport,Finset.mem_filter,Finset.mem_univ,true_and] using active
    by_cases gauge : 9≤j.val ∧ j.val<57
    · obtain ⟨mu,a,rfl⟩:=(sourceGaugeSlot_range j).mp gauge
      exact sourceRetainerSeed_gauge_zero q mu a left right
    · exact sourceRetainerSeed_unseen q j (by omega)

theorem sourceNonGaugeSeed_action (q : PhysicalResponsePoint) (left : q.z.im≠0) (right : q.w.im≠0)
    (j : Fin 289) : sourceNonGaugeSeed q j=sourceActionSeed q j :=
  (sourceRetainerSeed_nongauge q left right j).symm.trans (sourceRetainerSeed_action q left right j)

/-- The original full effective reader contracts only the49 computed source action columns. -/
def sourceActionNativeSeed (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ) (row : Fin 289) : SourceOp :=
  ∑j∈sourceActionSeedSupport,sourceNativeReaderFirst (fixedMomentum n zeta) row j • sourceRetainerSeed q j

def sourceActionSlowSeed (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ) (i : Fin 3) : SourceOp :=
  ∑j∈sourceActionSeedSupport,(slowFastFrame.transpose*sourceNativeReaderFirst (fixedMomentum n zeta))
    (fiveIndex ⟨i.val,by omega⟩) j • sourceRetainerSeed q j

private theorem zero_source_smul (z : ℂ) : z • (0:SourceOp)=0 := by
  apply ContinuousLinearMap.ext
  intro x
  change z • (0:GaussCoreHilbert.H)=0
  exact smul_zero z

theorem sourceNonGaugeNativeSeed_action (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (left : q.z.im≠0) (right : q.w.im≠0) (row : Fin 289) :
    sourceNonGaugeNativeSeed q n zeta row=sourceActionNativeSeed q n zeta row := by
  simp only [sourceNonGaugeNativeSeed,sourceNonGaugeSeed_action q left right,sourceActionSeed,sourceActionNativeSeed]
  simp only [smul_ite,zero_source_smul,Finset.sum_ite_mem,Finset.univ_inter]

theorem sourceNonGaugeSlowSeed_action (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (left : q.z.im≠0) (right : q.w.im≠0) (i : Fin 3) :
    sourceNonGaugeSlowSeed q n zeta i=sourceActionSlowSeed q n zeta i := by
  simp only [sourceNonGaugeSlowSeed,sourceNonGaugeSeed_action q left right,sourceActionSeed,sourceActionSlowSeed]
  simp only [smul_ite,zero_source_smul,Finset.sum_ite_mem,Finset.univ_inter]

/-- All full289 native field rows keep the complete source matrix and same pinned inverse. -/
theorem sourceMasterNative_action (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) (left : q.z.im≠0) (right : q.w.im≠0) (row : Fin 289) :
    sourceMasterNative q n zeta l r row=-Complex.I*sourcePoleRead q.epsilon q.precision 0 0 l r
      (sourcePinnedResolvent q.F n zeta*sourceActionNativeSeed q n zeta row) := by
  rw [sourceMasterNative_nongauge q n zeta l r left right row,sourceNonGaugeNativeSeed_action q n zeta left right row]

def sourceActionMasterChannel (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) (i : Fin 3) : ℂ :=
  (sourceChargedDenominator n zeta i)⁻¹*(-Complex.I)*sourcePoleRead q.epsilon q.precision 0 0 l r
    (sourcePinnedResolvent q.F n zeta*sourceActionSlowSeed q n zeta i)

theorem sourceMasterChannel_action (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) (left : q.z.im≠0) (right : q.w.im≠0) (i : Fin 3) :
    sourceMasterChannel q n zeta l r i=sourceActionMasterChannel q n zeta l r i := by
  rw [sourceMasterChannel_nongauge q n zeta l r left right i,sourceNonGaugeMasterChannel,
    sourceNonGaugeSlowSeed_action q n zeta left right i]
  rfl

/-- The original static double forcing retains every surviving scalar/coframe/Lorentz seed and exact P0 geometry. -/
theorem sourceStaticNative_action (q : PhysicalResponsePoint) (n : PhysicalMomentum) (l r : RestStateIndex)
    (left : q.z.im≠0) (right : q.w.im≠0) (i : Fin 3) :
    sourceSlowRead (sourceStaticNative q n l r) ⟨i.val,by omega⟩=
      Complex.I*sourcePoleRead q.epsilon q.precision 0 0 l r
        (sourceResonanceProjection q.F n 0*sourceActionSlowSeed q n 0 i) := by
  rw [sourceStaticNative_nongauge q n l r left right i,sourceNonGaugeSlowSeed_action q n 0 left right i]

theorem sourceActionSlowSeed_split (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (left : q.z.im≠0) (right : q.w.im≠0) (i : Fin 3) :
    sourceActionSlowSeed q n zeta i=sourceActionSlowSeed q n 0 i+zeta • sourceActionSlowSeed q 0 1 i := by
  rw [←sourceNonGaugeSlowSeed_action q n zeta left right i,sourceNonGaugeSlowSeed_split,
    sourceNonGaugeSlowSeed_action q n 0 left right i,sourceNonGaugeSlowSeed_action q 0 1 left right i]

end LowEnergy.PreparationPhysicalActionSeedReduction

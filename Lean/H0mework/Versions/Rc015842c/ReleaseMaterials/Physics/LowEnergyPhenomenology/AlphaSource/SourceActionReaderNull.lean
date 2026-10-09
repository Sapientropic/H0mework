import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceGaugeComplementSpatialReturn

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
local instance ActionSeedIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
open PreparationVacuumPropagationPencil PreparationVacuumRawJointFeedback PreparationVacuumLowerClassical
open PreparationVacuumJointFieldResponse SourceQuantumConfigurationHilbert

attribute [local irreducible] PreparationVacuumRawJointFeedback.rawReader rawInitial rawForm rawFiber rawSample sourceRetainerSeed sourceFullInitialUpper
  sourceFullInitialBase sourceEqualProjection sourcePoleRead sourceMasterCurrent sourceFullCurrentResidue

/-- These original coordinates remain independent field/state data but have zero direction in the actual three-component action reader. -/
theorem sourceActionDirection_unseen (j : Fin 289) (outside : (73≤j.val ∧ j.val<121) ∨ 145≤j.val) :
    fieldDirection (fieldUnit j)=0 := by
  have scalar (a : Fin 9) : fieldUnit j (scalarSlot a)=0 := by
    simp only [fieldUnit,Pi.single_apply]
    apply if_neg
    intro same
    have equal:=congrArg Fin.val same
    dsimp [scalarSlot] at equal
    omega
  have gauge (mu : Fin 4) (a : Fin 12) : fieldUnit j (gaugeSlot mu a)=0 := by
    simp only [fieldUnit,Pi.single_apply]
    apply if_neg
    intro same
    have equal:=congrArg Fin.val same
    dsimp [gaugeSlot] at equal
    omega
  have coframe (a mu : Fin 4) : fieldUnit j (coframeSlot a mu)=0 := by
    simp only [fieldUnit,Pi.single_apply]
    apply if_neg
    intro same
    have equal:=congrArg Fin.val same
    dsimp [coframeSlot] at equal
    omega
  have lorentz (mu : Fin 4) (a : Fin 6) : fieldUnit j (lorentzSlot mu a)=0 := by
    simp only [fieldUnit,Pi.single_apply]
    apply if_neg
    intro same
    have equal:=congrArg Fin.val same
    dsimp [lorentzSlot] at equal
    omega
  have source : sourceData (fieldUnit j)=0 := by
    apply Prod.ext
    · change fieldScalar (fieldUnit j)=0
      simp only [fieldScalar,scalar,zero_smul,Finset.sum_const_zero]
    apply Prod.ext
    · funext mu
      change (∑a : Fin 12,fieldUnit j (gaugeSlot mu a) • originalUnit a)=0
      simp only [gauge,zero_smul,Finset.sum_const_zero]
    apply Prod.ext
    · funext a mu
      exact coframe a mu
    · funext mu a
      exact lorentz mu a
  rw [←stateDirection_source,source,map_zero]

private theorem density_zero (f : Field289) (zero : fieldDirection f=0) (s : ActionState) (i : Fin 4) :
    densityVariation f s i=0 := by
  simp only [densityVariation,lowerVariation,principalVariation,zero,map_zero,zero_mul,smul_zero]
  refine Fin.cases ?_ (fun j=>?_) i <;> simp only [Fin.cases_zero,Fin.cases_succ,zero_sub,neg_zero]

private theorem rawSymbol_zero (f : Field289) (zero : fieldDirection f=0) (p : PhysicalMomentum) (s : ActionState) :
    rawActionSymbol f p s=0 := by
  simp only [rawActionSymbol,density_zero f zero,mul_zero]
  exact (rawFourier p).map_zero

/-- Vanishing source action direction reaches the exact original raw field operator, before compression or external-state selection. -/
theorem sourceRawReader_direction_zero (f : Field289) (zero : fieldDirection f=0)
    (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) : PreparationVacuumRawJointFeedback.rawReader f p F h=0 := by
  have fiber (u : JointParameter) : rawFiber f p u=0 := by
    rw [rawFiber,rawSymbol_zero f zero,map_zero]
  have sample (a b : _) (u : JointParameter) : rawSample f p a b u=0 := by
    rw [rawSample,fiber,zero_apply]
    simp only [pairSample,WithLp.ofLp_zero,Pi.zero_apply,mul_zero,Finset.sum_const_zero]
  have form (a b : _) : rawForm f p a b h=0 := by
    simp only [rawForm,sample,integral_zero]
  simp only [PreparationVacuumRawJointFeedback.rawReader,finiteRiesz,form,zero_smul,Finset.sum_const_zero]

/-- Both original Green inverses and every grade-changing matrix entry are retained when the actual reader computes zero. -/
theorem sourceRawInitial_direction_zero (q : PhysicalResponsePoint) (f : Field289) (zero : fieldDirection f=0) :
    rawInitial q f=0 := by
  simp only [rawInitial,sourceRawReader_direction_zero f zero,mul_zero,zero_mul]

theorem sourceFullInitialUpper_unseen (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (j : Fin 289)
    (outside : (73≤j.val ∧ j.val<121) ∨ 145≤j.val) : sourceFullInitialUpper q pL pR j=0 := by
  simp only [sourceFullInitialUpper,sourceRawInitial_direction_zero _ _ (sourceActionDirection_unseen j outside),mul_zero,zero_mul]

theorem sourceFullInitialBase_unseen (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (j : Fin 289)
    (outside : (73≤j.val ∧ j.val<121) ∨ 145≤j.val) : sourceFullInitialBase q pL pR j=0 := by
  simp only [sourceFullInitialBase,sourceRawInitial_direction_zero _ _ (sourceActionDirection_unseen j outside),mul_zero,zero_mul]

/-- All192 original action-invisible columns have zero complete source retainer seed. -/
theorem sourceRetainerSeed_unseen (q : PhysicalResponsePoint) (j : Fin 289)
    (outside : (73≤j.val ∧ j.val<121) ∨ 145≤j.val) : sourceRetainerSeed q j=0 := by
  simp only [sourceRetainerSeed,sourceFullInitialUpper_unseen q 0 0 j outside,map_zero,zero_mul]

theorem sourceMasterCurrent_unseen (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) (j : Fin 289) (outside : (73≤j.val ∧ j.val<121) ∨ 145≤j.val) :
    sourceMasterCurrent q n zeta l r j=0 := by
  simp only [sourceMasterCurrent,sourceRetainerSeed_unseen q j outside,mul_zero,map_zero]

theorem sourceFullCurrentResidue_unseen (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (causal : 0<zeta.re) (l r : RestStateIndex) (j : Fin 289)
    (outside : (73≤j.val ∧ j.val<121) ∨ 145≤j.val) : sourceFullCurrentResidue q n zeta l r j=0 := by
  rw [sourceFullCurrentResidue_square q n zeta causal]
  simp only [sourceRetainerSeed_unseen q j outside,mul_zero,map_zero]

theorem sourceStaticCurrent_unseen (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (l r : RestStateIndex) (j : Fin 289) (outside : (73≤j.val ∧ j.val<121) ∨ 145≤j.val) :
    sourceStaticCurrent q n l r j=0 := by
  rw [sourceStaticCurrent_seed]
  simp only [sourceRetainerSeed_unseen q j outside,mul_zero,map_zero]

end LowEnergy.PreparationPhysicalActionSeedReduction

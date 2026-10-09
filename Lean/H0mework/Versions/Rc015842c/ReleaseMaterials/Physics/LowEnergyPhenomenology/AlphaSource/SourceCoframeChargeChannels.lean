import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCoframeChargeDegree

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
local instance CoframeChannelsIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

local instance : DecidableEq Mode:=Classical.decEq _

/-- The actual three-level source spectrum and the generated double commutator constrain every full252 entry. -/
theorem sourceCoframeCharge_entry (z : SourceCoordinateSlice) (i j : Quantum.Index) :
    (((sourceWholeWeight i:ℂ)-(sourceWholeWeight j:ℂ))^2-1)*sourceCoframeModeCoefficient z i j=0 := by
  have generated:=sourceCoframeCharge_matrix z
  change Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)*
    (Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)*sourceCoframeModeCoefficient z-
      sourceCoframeModeCoefficient z*Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether))-
    (Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)*sourceCoframeModeCoefficient z-
      sourceCoframeModeCoefficient z*Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether))*
        Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)=sourceCoframeModeCoefficient z at generated
  rw [sourcePhaseNoether_matrix] at generated
  have entry:=congrArg (fun A : SourceMatrix=>A i j) generated
  simp only [Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal] at entry
  linear_combination entry

/-- Half-charge and same-charge entries vanish by the actual source spectrum, without a chosen external sector. -/
theorem sourceCoframeCharge_forbidden (z : SourceCoordinateSlice) (i j : Quantum.Index)
    (absent : ¬((sourceWholeWeight i= -1 ∧ sourceWholeWeight j=0) ∨
      (sourceWholeWeight i=0 ∧ sourceWholeWeight j= -1))) : sourceCoframeModeCoefficient z i j=0 := by
  have coefficient : (((sourceWholeWeight i:ℂ)-(sourceWholeWeight j:ℂ))^2-1)≠0 := by
    rcases sourceWholeWeight_range i with hi|hi|hi <;> rcases sourceWholeWeight_range j with hj|hj|hj
    all_goals first
      | exact False.elim (absent (Or.inl ⟨hi,hj⟩))
      | exact False.elim (absent (Or.inr ⟨hi,hj⟩))
      | norm_num [hi,hj]
  exact (mul_eq_zero.mp (sourceCoframeCharge_entry z i j)).resolve_left coefficient

/-- Original unit/neutral projectors act on the complete source matrix before any quantization. -/
def sourceCoframePrimalChannel (positive : Bool) (z : SourceCoordinateSlice) : SourceMatrix :=
  if positive then sourcePhaseProjectionMatrix 0*sourceCoframeModeCoefficient z*sourcePhaseProjectionMatrix 2
  else sourcePhaseProjectionMatrix 2*sourceCoframeModeCoefficient z*sourcePhaseProjectionMatrix 0

/-- The original full252 matrix is exactly the two source-generated unit-neutral channels. -/
theorem sourceCoframePrimalChannel_total (z : SourceCoordinateSlice) :
    sourceCoframePrimalChannel true z+sourceCoframePrimalChannel false z=sourceCoframeModeCoefficient z := by
  ext i j
  simp only [sourceCoframePrimalChannel,Bool.false_eq_true,if_true,if_false,sourcePhaseProjectionMatrix,
    Matrix.add_apply,Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases present : (sourceWholeWeight i= -1 ∧ sourceWholeWeight j=0) ∨
      (sourceWholeWeight i=0 ∧ sourceWholeWeight j= -1)
  · rcases present with ⟨hi,hj⟩|⟨hi,hj⟩ <;> norm_num [hi,hj,sourcePhaseLevel]
  · simp only [sourceCoframeCharge_forbidden z i j present,mul_zero,zero_mul,zero_add]

/-- Signs are the original absolute Noether charge differences of the unit and neutral spectral sectors. -/
theorem sourceCoframePrimalChannel_degree (positive : Bool) (z : SourceCoordinateSlice) :
    Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)*sourceCoframePrimalChannel positive z-
      sourceCoframePrimalChannel positive z*Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)=
        (if positive then (1:ℂ) else -1) • sourceCoframePrimalChannel positive z := by
  rw [sourcePhaseNoether_matrix]
  ext i j
  cases positive <;>
    simp only [sourceCoframePrimalChannel,Bool.false_eq_true,if_true,if_false,sourcePhaseProjectionMatrix,
      Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.smul_apply,smul_eq_mul]
  · by_cases hi : sourceWholeWeight i=0 <;> by_cases hj : sourceWholeWeight j= -1 <;>
      norm_num [hi,hj,sourcePhaseLevel]
  · by_cases hi : sourceWholeWeight i= -1 <;> by_cases hj : sourceWholeWeight j=0 <;>
      norm_num [hi,hj,sourcePhaseLevel]

/-- The dual blocks are exchanged: the original independent dual carries the opposite charge. -/
def sourceCoframeChargeChannel (positive : Bool) (z : SourceCoordinateSlice) : FullMatrix :=
  Matrix.fromBlocks (sourceCoframePrimalChannel positive z) 0 0
    ((sourceCoframePrimalChannel (!positive) z).map (starRingEnd ℂ))

theorem sourceCoframeChargeChannel_total (z : SourceCoordinateSlice) :
    sourceCoframeChargeChannel true z+sourceCoframeChargeChannel false z=sourceCoframeModeSymbol z := by
  rw [sourceCoframeSymbol_branches]
  simp only [sourceCoframeChargeChannel,Bool.not_true,Bool.not_false,Matrix.fromBlocks_add,
    zero_add,sourceCoframePrimalChannel_total]
  congr 1
  rw [←Matrix.map_add _ (fun a b=>map_add (starRingEnd ℂ) a b),add_comm,sourceCoframePrimalChannel_total]

private theorem star_neg (A : SourceMatrix) : (-A).map (starRingEnd ℂ)=-(A.map (starRingEnd ℂ)) :=
  Matrix.map_neg _ (fun a=>map_neg (starRingEnd ℂ) a) A

/-- The two complete full504 channels have opposite signed source charge, including every dual entry. -/
theorem sourceCoframeChargeChannel_degree (positive : Bool) (z : SourceCoordinateSlice) :
    sourceActualGaussChargeMatrix*sourceCoframeChargeChannel positive z-
      sourceCoframeChargeChannel positive z*sourceActualGaussChargeMatrix=
        (if positive then (1:ℂ) else -1) • sourceCoframeChargeChannel positive z := by
  let Q:=Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)
  have up : Q*sourceCoframePrimalChannel true z-sourceCoframePrimalChannel true z*Q=
      sourceCoframePrimalChannel true z := by
    simpa only [if_true,one_smul] using sourceCoframePrimalChannel_degree true z
  have down : Q*sourceCoframePrimalChannel false z-sourceCoframePrimalChannel false z*Q=
      -sourceCoframePrimalChannel false z := by
    simpa only [Bool.false_eq_true,if_false,neg_smul,one_smul] using sourceCoframePrimalChannel_degree false z
  have dup:=congrArg (fun A : SourceMatrix=>A.map (starRingEnd ℂ)) up
  have ddown:=congrArg (fun A : SourceMatrix=>A.map (starRingEnd ℂ)) down
  simp only [Matrix.map_sub _ (fun a b=>map_sub (starRingEnd ℂ) a b),Matrix.map_mul,star_neg] at dup ddown
  have dualUp : (-(Q.map (starRingEnd ℂ)))*(sourceCoframePrimalChannel false z).map (starRingEnd ℂ)-
      (sourceCoframePrimalChannel false z).map (starRingEnd ℂ)*(-(Q.map (starRingEnd ℂ)))=
        (sourceCoframePrimalChannel false z).map (starRingEnd ℂ) := by
    calc
      _= -((Q.map (starRingEnd ℂ))*(sourceCoframePrimalChannel false z).map (starRingEnd ℂ)-
        (sourceCoframePrimalChannel false z).map (starRingEnd ℂ)*(Q.map (starRingEnd ℂ))) := by noncomm_ring
      _=_ := by rw [ddown,neg_neg]
  have dualDown : (-(Q.map (starRingEnd ℂ)))*(sourceCoframePrimalChannel true z).map (starRingEnd ℂ)-
      (sourceCoframePrimalChannel true z).map (starRingEnd ℂ)*(-(Q.map (starRingEnd ℂ)))=
        -((sourceCoframePrimalChannel true z).map (starRingEnd ℂ)) := by
    calc
      _= -((Q.map (starRingEnd ℂ))*(sourceCoframePrimalChannel true z).map (starRingEnd ℂ)-
        (sourceCoframePrimalChannel true z).map (starRingEnd ℂ)*(Q.map (starRingEnd ℂ))) := by noncomm_ring
      _=_ := by rw [dup]
  change Matrix.fromBlocks Q 0 0 (-(Q.map (starRingEnd ℂ)))*sourceCoframeChargeChannel positive z-
      sourceCoframeChargeChannel positive z*Matrix.fromBlocks Q 0 0 (-(Q.map (starRingEnd ℂ)))=_
  unfold sourceCoframeChargeChannel
  rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
  simp only [zero_mul,mul_zero,add_zero,zero_add]
  cases positive
  · simp only [Bool.not_false,Bool.false_eq_true,if_false,neg_smul,one_smul]
    ext i j
    cases i with
    | inl i=>cases j with
      | inl j=>exact congrArg (fun A : SourceMatrix=>A i j) down
      | inr j=>simp [Matrix.fromBlocks]
    | inr i=>cases j with
      | inl j=>simp [Matrix.fromBlocks]
      | inr j=>exact congrArg (fun A : SourceMatrix=>A i j) dualDown
  · simp only [Bool.not_true,if_true,one_smul]
    ext i j
    cases i with
    | inl i=>cases j with
      | inl j=>exact congrArg (fun A : SourceMatrix=>A i j) up
      | inr j=>simp [Matrix.fromBlocks]
    | inr i=>cases j with
      | inl j=>simp [Matrix.fromBlocks]
      | inr j=>exact congrArg (fun A : SourceMatrix=>A i j) dualUp

/-- Quantization is applied to the original matrix channel as a whole; products of quantized projectors are not substituted. -/
def sourceCoframeChargeFiberChannel (positive : Bool) (z : SourceCoordinateSlice) : FockFiber→L[ℂ]FockFiber :=
  quantized (sourceCoframeChargeChannel positive z)

theorem sourceCoframeChargeFiberChannel_total (z : SourceCoordinateSlice) :
    sourceCoframeChargeFiberChannel true z+sourceCoframeChargeFiberChannel false z=sourceCoframeModeFiber z := by
  have generated:=congrArg quantizer (sourceCoframeChargeChannel_total z)
  rw [map_add] at generated
  exact generated

/-- Complete full CAR preserves each signed source charge transfer on arbitrary Fock input. -/
theorem sourceCoframeChargeFiberChannel_degree (positive : Bool) (z : SourceCoordinateSlice) :
    quantized sourceActualGaussChargeMatrix*sourceCoframeChargeFiberChannel positive z-
      sourceCoframeChargeFiberChannel positive z*quantized sourceActualGaussChargeMatrix=
        (if positive then (1:ℂ) else -1) • sourceCoframeChargeFiberChannel positive z := by
  have generated:=congrArg quantizer (sourceCoframeChargeChannel_degree positive z)
  rw [paidCoframeQuantizerComm%,map_smul] at generated
  exact generated

end LowEnergy.PreparationPhysicalCoframeChargeSelection

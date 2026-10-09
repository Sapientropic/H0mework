import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualPolarizationRead
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstMaterialVertexReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceSpectralMaterialPotential

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFirstTemporalChargeReturn
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
local instance firstTemporalQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
local instance firstTemporalModeIndex : DecidableEq Mode:=Classical.decEq _

open PreparationPhysicalActualGaussChargeCurrent
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumCurrentRegularAnchor PreparationVacuumPhysicalPoleAmputation

open PreparationPhysicalActualNoetherVertexReturn PreparationVacuumPhysicalPoleLegDynamics
open Stage9DEF Stage9DEF.Compatibility
attribute [local irreducible] jointGenerator jointResolvent sourceChargedGaussPrepared

open PreparationPhysicalCommonSpatialGreen
open scoped SchwartzMap

open PreparationPhysicalActualLegNormalization PreparationVacuumPhysicalTailPrice
local instance firstTemporalOperatorReal : NormedAlgebra ℝ (H→L[ℂ]H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointVertex mixedVertex jointCurrent jointHessian

attribute [local irreducible] physicalTime timeSlope PreparationVacuumRawJointFeedback.rawReader rawReaderContact


open PreparationPhysicalActualUnitFourPointReturn PreparationPhysicalUnitCurrentFieldReturn
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalFirstPoleGaugeRemainder
open PreparationPhysicalFirstGaugeBackgroundReturn PreparationPhysicalMaterialChargeTorque
open PreparationPhysicalFinitePoleVertices PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalNativePhotonFluxReturn PreparationVacuumActionFieldLift

open GaussCoreDifferential PreparationVacuumSourceActionJets PreparationVacuumFullFieldRiesz
open scoped Matrix.Norms.L2Operator

local instance firstTemporalCoframeNorm : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance firstTemporalCoframeSemi : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance firstTemporalCoframeReal : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
local instance firstTemporalMatrixReal : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance firstTemporalFullReal : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _

open PreparationPhysicalActualPolarizationResponse PreparationPhysicalFirstGaugeMaterialDifference
open PreparationPhysicalMaterialSpectralCharge PreparationPhysicalCoframeChargeSelection

open PreparationVacuumFullElectricWard

/-- The source table generates the single temporal connection at every coframe. -/
theorem sourceFirstTemporal_connection (mu : Fin 4) :
    sourceFirstGaugeConnection 0 mu=if mu=0 then sourceFirstTemporalLie else 0 := by
  by_cases same : mu=0
  · subst mu
    rw [if_pos rfl]
    rfl
  · rw [if_neg same]
    simp only [sourceFirstGaugeConnection,sourceFirstGaugeCoefficients]
    norm_num [same,Fin.ext_iff]

/-- The original principal cancels before any configuration or prepared-state restriction. -/
theorem sourceFirstTemporal_energy (s : ActionState) (valid : s∈validStates) :
    sourcePolarizationAxisEnergy s 0=Quantum.operatorMatrix sourceFirstTemporalCharge := by
  have lower : sourcePolarizationAxisLower s 0=principalMatrix s.1*nativePrimal sourceFirstTemporalLie := by
    simp only [sourcePolarizationAxisLower,sourceFirstTemporal_connection,apply_ite,map_zero,mul_zero,
      Finset.sum_ite_eq',Finset.mem_univ,if_true,principalMatrix_coefficient]
  rw [sourcePolarizationAxisEnergy,lower,Ring.inverse_mul_cancel_left _ _ (principalMatrix_regular s.1 valid.2)]
  rw [sourceFirstTemporalCharge,map_smul,sourceFirstTemporal_native]

/-- Both independent Dirac branches return the same full first-pole charge. -/
theorem sourceFirstTemporal_symbol (s : ActionState) (valid : s∈validStates) (p : PhysicalMomentum) :
    symbolFirst p s (fieldDirection (sourceEnergyAxisField 1 0))=sourceFirstChargeMatrix := by
  rw [sourcePolarizationAxis_symbol s valid,sourceFirstTemporal_energy s valid,sourceFirstCharge_branches]

/-- The density weight is the original action weight, including its sign and factor four. -/
def sourceFirstTemporalWeight (s : ActionState) : FullMatrix := -(4:ℂ) • sourceActionWeight s

theorem sourceFirstTemporal_raw (s : ActionState) (valid : s∈validStates) (p : PhysicalMomentum) :
    rawActionSymbol (sourceEnergyAxisField 1 0) p s=sourceFirstTemporalWeight s*sourceFirstChargeMatrix := by
  rw [sourcePolarizationAxis_raw s valid,sourceFirstTemporal_energy s valid,←sourceFirstCharge_branches]
  exact (smul_mul_assoc _ _ _).symm

theorem sourceFirstTemporal_chargeSplit :
    sourceFirstChargeMatrix=sourceActualGaussChargeMatrix+sourceFirstDifferenceMatrix := by
  unfold sourceFirstDifferenceMatrix
  abel

/-- The complete CAR normal-order terms survive separately for actualQ and the full GT difference. -/
theorem sourceFirstTemporal_fullCAR (s : ActionState) (valid : s∈validStates) (p : PhysicalMomentum) :
    quantizer (rawActionSymbol (sourceEnergyAxisField 1 0) p s)=
      quantizer (sourceFirstTemporalWeight s)*quantizer sourceActualGaussChargeMatrix+
      quantizer (sourceFirstTemporalWeight s)*quantizer sourceFirstDifferenceMatrix-
      pairFiber (sourceFirstTemporalWeight s) sourceActualGaussChargeMatrix-
      pairFiber (sourceFirstTemporalWeight s) sourceFirstDifferenceMatrix := by
  have actual:=quantized_normal_order (sourceFirstTemporalWeight s) sourceActualGaussChargeMatrix
  have difference:=quantized_normal_order (sourceFirstTemporalWeight s) sourceFirstDifferenceMatrix
  change quantizer (sourceFirstTemporalWeight s)*quantizer sourceActualGaussChargeMatrix=
    quantizer (sourceFirstTemporalWeight s*sourceActualGaussChargeMatrix)+
      pairFiber (sourceFirstTemporalWeight s) sourceActualGaussChargeMatrix at actual
  change quantizer (sourceFirstTemporalWeight s)*quantizer sourceFirstDifferenceMatrix=
    quantizer (sourceFirstTemporalWeight s*sourceFirstDifferenceMatrix)+
      pairFiber (sourceFirstTemporalWeight s) sourceFirstDifferenceMatrix at difference
  rw [sourceFirstTemporal_raw s valid,sourceFirstTemporal_chargeSplit,mul_add,map_add]
  rw [actual,difference]
  abel

end LowEnergy.PreparationPhysicalFirstTemporalChargeReturn

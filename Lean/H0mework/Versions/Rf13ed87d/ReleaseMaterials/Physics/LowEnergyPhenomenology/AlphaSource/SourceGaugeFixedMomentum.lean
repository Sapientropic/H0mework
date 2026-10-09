import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePhaseGaugeObservation
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceVoltageFixedMomentumCharge

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalGaugeMomentumCoupling
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
open scoped BigOperators Matrix Topology InnerProductSpace Matrix.Norms.L2Operator
local instance actualGaugeMomentumIndex : DecidableEq Quantum.Index:=Classical.decEq _
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
local instance : DecidableEq Mode:=Classical.decEq _

open PreparationPhysicalActualGaussChargeCurrent
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumCurrentRegularAnchor PreparationVacuumPhysicalPoleAmputation

open PreparationPhysicalActualNoetherVertexReturn PreparationVacuumPhysicalPoleLegDynamics
open Stage9DEF Stage9DEF.Compatibility
attribute [local irreducible] jointGenerator jointResolvent sourceChargedGaussPrepared

open PreparationPhysicalCommonSpatialGreen
open scoped SchwartzMap

open PreparationPhysicalActualLegNormalization PreparationVacuumPhysicalTailPrice
local instance : NormedAlgebra ℝ (Operator) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointVertex mixedVertex jointCurrent jointHessian sourceAbsoluteCharge

open PreparationPhysicalActualUnitFourPointReturn PreparationPhysicalSourceHarmonicReturn

open PreparationPhysicalActualFieldNoetherResponse PreparationVacuumPhysicalModeChargeRead
open SU7ExteriorMatterGaugeCovariantJet StageNineFullDiracAdjointLocalOperator
open GaussComposite GaussComposite.PhysicalModeEMCurrent SourceQuantumScalarChart

open PreparationVacuumPhysicalElectromagneticDirection PreparationVacuumLowerClassical
open PreparationVacuumOriginalDensity SourceQuantumScalarOrbitDimensions PreparationCoordinates StageNineDynamicBreakingVacuum

open PreparationPhysicalPhaseGaugeRealization PreparationVacuumNoetherChart
open PreparationPhysicalVoltageNoether PreparationPhysicalActionUnits
open PreparationPhysicalVoltageNoetherChargeReturn PreparationVacuumNoetherOrdinaryWard
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _

private theorem phase_principal (s : ActionState) (valid : s∈validStates) :
    statePhase s*(stateVolume s • coefficientMatrix 0 s.1)=Complex.I • (1:SourceMatrix) := by
  rw [←principalMatrix_coefficient,statePhase,smul_mul_smul,
    Ring.inverse_mul_cancel _ (principalMatrix_regular s.1 valid.2)]
  have volume : stateVolume s≠0:=Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr valid.1)
  congr 1
  field_simp

def sourceGaugeFixedCoefficient (base : ActionState) : SourceMatrix :=
  rawMomentumMatrix base*Quantum.operatorMatrix sourcePhaseGaugeCharge

/-- The original momentum weight is retained in the unit current; it is not silently replaced by identity. -/
def sourceGaugeMomentumWeight (base : ActionState) : SourceMatrix :=
  Quantum.operatorMatrix YangMills.FullPairing.flipMatter*inversePhase base

def sourceGaugeUnitCoefficient (base : ActionState) : SourceMatrix :=
  sourceGaugeMomentumWeight base*Quantum.operatorMatrix sourcePhaseGaugeCharge

theorem sourceGaugeFixedCoefficient_momentum (base : ActionState) :
    sourceGaugeFixedCoefficient base=(ActionNormalization.phaseMomentum:ℂ) • sourceGaugeUnitCoefficient base := by
  simp only [sourceGaugeFixedCoefficient,sourceGaugeUnitCoefficient,sourceGaugeMomentumWeight,rawMomentumMatrix,
    sourceDensityActionMatrix_momentum,smul_mul_assoc]

/-- Fixed original Pi cancels the actual moving volume/principal factors for the source-generated gauge direction. -/
theorem sourceGaugeTransportedDensity (base candidate : ActionState) (valid : candidate∈validStates) (row : Fin 4) :
    transportedDensity (sourcePhaseGaugeField 0) base candidate row=
      if row=0 then sourceGaugeFixedCoefficient base else 0 := by
  rw [transportedDensity,sourcePhaseGaugeField_density 0 candidate valid.1 row]
  split_ifs with zero
  · have canceled : rawMomentumInverse candidate*densityActionMatrix=statePhase candidate := by
      rw [rawMomentumInverse,mul_assoc,densityAction_two_sided.2,mul_one]
    calc
      _=rawMomentumMatrix base*(rawMomentumInverse candidate*densityActionMatrix)*
          ((stateVolume candidate • coefficientMatrix 0 candidate.1)*Quantum.operatorMatrix sourcePhaseGaugeGenerator) := by
        rw [smul_mul_assoc]
        noncomm_ring
      _=rawMomentumMatrix base*(statePhase candidate*(stateVolume candidate • coefficientMatrix 0 candidate.1))*
          Quantum.operatorMatrix sourcePhaseGaugeGenerator := by rw [canceled];noncomm_ring
      _=sourceGaugeFixedCoefficient base := by
        rw [phase_principal candidate valid,mul_assoc,smul_mul_assoc,one_mul]
        have charge : Quantum.operatorMatrix sourcePhaseGaugeCharge=
            Complex.I • Quantum.operatorMatrix sourcePhaseGaugeGenerator :=
          Quantum.operatorMatrix.toLinearEquiv.map_smul Complex.I sourcePhaseGaugeGenerator
        rw [sourceGaugeFixedCoefficient,charge,mul_smul_comm]
  · exact mul_zero _

def sourceGaugeUnitSymbol (base : ActionState) (p : PhysicalMomentum) : FullMatrix :=
  rawFourier p (fun row=>if row=0 then sourceGaugeUnitCoefficient base else 0)

theorem sourceGaugeTransportedSymbol (base candidate : ActionState) (valid : candidate∈validStates) (p : PhysicalMomentum) :
    transportedRawSymbol (sourcePhaseGaugeField 0) base candidate p=
      ActionNormalization.phaseMomentum • sourceGaugeUnitSymbol base p := by
  rw [transportedRawSymbol]
  have coefficients : transportedDensity (sourcePhaseGaugeField 0) base candidate=
      ActionNormalization.phaseMomentum • (fun row : Fin 4=>if row=0 then sourceGaugeUnitCoefficient base else 0) := by
    funext row
    rw [sourceGaugeTransportedDensity base candidate valid row]
    simp only [Pi.smul_apply]
    split_ifs
    · rw [sourceGaugeFixedCoefficient_momentum,RCLike.real_smul_eq_coe_smul (K:=ℂ)]
      rfl
    · exact (smul_zero _).symm
  rw [coefficients,map_smul]
  rfl

/-- The source chart produces the valid variation neighbourhood; no zero-contact condition is supplied. -/
theorem sourceGaugeNoetherContactCoefficient (force : Field289) (z : physicalChart) (row : Fin 4) :
    noetherContactCoefficient (sourcePhaseGaugeField 0) force (sourceState z.val) row=0 := by
  have near : ∀ᶠr : ℝ in 𝓝 0,sourceState z.val+r • fieldDirection force∈validStates:=
    (state_line (sourceState z.val) (fieldDirection force)).continuousAt.preimage_mem_nhds
      (by simpa only [zero_smul,add_zero] using validStates_open.mem_nhds (sourceState_valid z))
  have same : (fun r : ℝ=>transportedDensity (sourcePhaseGaugeField 0) (sourceState z.val)
      (sourceState z.val+r • fieldDirection force) row)=ᶠ[𝓝 0]
      (fun _=>if row=0 then sourceGaugeFixedCoefficient (sourceState z.val) else 0) := by
    filter_upwards [near] with r valid
    exact sourceGaugeTransportedDensity _ _ valid row
  exact (transportedDensity_generated (sourcePhaseGaugeField 0) force z row).unique
    ((hasDerivAt_const (0:ℝ) (if row=0 then sourceGaugeFixedCoefficient (sourceState z.val) else 0)).congr_of_eventuallyEq same)

theorem sourceGaugeNoetherContactSymbol (force : Field289) (z : physicalChart) (p : PhysicalMomentum) :
    noetherContactSymbol (sourcePhaseGaugeField 0) force (sourceState z.val) p=0 := by
  rw [noetherContactSymbol]
  have zero : noetherContactCoefficient (sourcePhaseGaugeField 0) force (sourceState z.val)=0 := by
    funext row
    exact sourceGaugeNoetherContactCoefficient force z row
  rw [zero,map_zero]

end LowEnergy.PreparationPhysicalGaugeMomentumCoupling

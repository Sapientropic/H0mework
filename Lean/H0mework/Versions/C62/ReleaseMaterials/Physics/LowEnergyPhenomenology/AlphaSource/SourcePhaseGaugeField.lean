import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePhaseGaugeGenerator

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalPhaseGaugeRealization
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
local instance actualPhaseGaugeFieldIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

/-- The same native Lie direction generates an actual four-component gauge potential in full289 coordinates. -/
def sourcePhaseGaugeField (mu : Fin 4) : Field289 :=
  ∑a : Fin 12,rawCoordinates sourcePhaseGaugeLie a • gaugeField mu a

open Lean Elab Term in
elab "paidPhaseGaugeDensitySum%" : term => do
  let wanted := `LowEnergy.PreparationVacuumPhysicalQuantumLockedCharge.density_sum
  let names := (← getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.startsWith "_private.H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceQuantumLockedPoleCharge." && privateToUserName name == wanted then some name else none
  match names with
  | [name] =>
    logInfo m!"Original private payer: {name}"
    return mkConst name
  | _ => throwError "Expected unique original qualified SourceQuantumLockedPoleCharge.density_sum"

private abbrev sourceGaugeDensitySum := paidPhaseGaugeDensitySum%

theorem sourcePhaseGaugeField_density (mu : Fin 4) (s : ActionState)
    (nondegenerate : s.1.det≠0) (row : Fin 4) :
    densityVariation (sourcePhaseGaugeField mu) s row=
      if row=0 then stateVolume s •
        (coefficientMatrix mu s.1*Quantum.operatorMatrix sourcePhaseGaugeGenerator) else 0 := by
  unfold sourcePhaseGaugeField
  rw [sourceGaugeDensitySum]
  simp only [gauge_density mu _ s nondegenerate row]
  by_cases zero : row=0
  · simp only [zero,ite_true]
    rw [sourcePhaseGaugeGenerator_native]
    have native:=congrArg GaussNativeMatter.nativePrimal (raw_original_expansion sourcePhaseGaugeLie)
    simp only [map_sum,map_smul] at native
    rw [native,Finset.mul_sum,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [mul_smul_comm,smul_comm]
  · simp [zero]

private theorem gaugeField_complex (mu : Fin 4) :
    (fun j=>(sourcePhaseGaugeField mu j:ℂ))=
      ∑a : Fin 12,(rawCoordinates sourcePhaseGaugeLie a:ℂ) • (fun j=>(gaugeField mu a j:ℂ)) := by
  funext j
  simp only [sourcePhaseGaugeField,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Complex.ofReal_sum,Complex.ofReal_mul]

theorem sourcePhaseGaugeField_connection (mu nu : Fin 4) :
    sourceModeConnection nu (fun j=>(sourcePhaseGaugeField mu j:ℂ))=
      if nu=mu then Quantum.operatorMatrix sourcePhaseGaugeGenerator else 0 := by
  rw [gaugeField_complex]
  simp only [map_sum,map_smul,sourceModeConnection_real,gauge_connection]
  by_cases same : nu=mu
  · simp only [same,ite_true]
    rw [sourcePhaseGaugeGenerator_native]
    have native:=congrArg GaussNativeMatter.nativePrimal (raw_original_expansion sourcePhaseGaugeLie)
    simp only [map_sum,map_smul] at native
    rw [native]
    apply Finset.sum_congr rfl
    intro a _
    ext i j
    simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul]
  · simp [same]

/-- The scalar orbit carried by the same native generator is retained separately from a pure gauge-potential variation. -/
def sourcePhaseGaugeScalarVariation : SourceQuantumScalarChart.Scalar :=
  SourceQuantumScalarChart.orbit sourcePhaseGaugeLie

theorem sourcePhaseGaugeScalarVariation_return :
    sourcePhaseGaugeScalarVariation= -(1/2:ℝ) • SourceQuantumScalarChart.orbit nativeY := by
  simp only [sourcePhaseGaugeScalarVariation,sourcePhaseGaugeLie,map_sub,map_neg,map_smul,
    sourceScalar_color_locked,neg_zero,zero_sub,neg_smul]

/-- Every temporal density coefficient contains the full252 phase-to-gauge difference. -/
theorem sourcePhaseGaugeField_densityDifference (mu : Fin 4) (s : ActionState)
    (nondegenerate : s.1.det≠0) :
    densityVariation (sourcePhaseGaugeField mu) s 0=
      stateVolume s • (coefficientMatrix mu s.1*Quantum.operatorMatrix sourceNativeOriginGenerator)-
      stateVolume s • (coefficientMatrix mu s.1*Quantum.operatorMatrix sourcePhaseGaugeDifference) := by
  rw [sourcePhaseGaugeField_density mu s nondegenerate 0,if_pos rfl,sourcePhaseGaugeGenerator_full]
  simp only [map_add,mul_add,smul_add,add_sub_cancel_right]

/-- The original full real-scalar Fock density keeps the independent dual block. -/
theorem sourcePhaseGaugeField_raw (mu : Fin 4) (p : PhysicalMomentum)
    (s : ActionState) (nondegenerate : s.1.det≠0) :
    rawActionSymbol (sourcePhaseGaugeField mu) p s=
      oppositeDual*SourceRealScalarFock.branches
        (densityActionMatrix*(stateVolume s •
          (coefficientMatrix mu s.1*Quantum.operatorMatrix sourcePhaseGaugeGenerator))) := by
  unfold rawActionSymbol rawFourier
  simp only [sourcePhaseGaugeField_density mu s nondegenerate]
  change oppositeDual*realFourierMatrix
    (fun row=>densityActionMatrix*(if row=0 then stateVolume s •
      (coefficientMatrix mu s.1*Quantum.operatorMatrix sourcePhaseGaugeGenerator) else 0)) p=_
  simp [realFourierMatrix,affineMatrix,SourceRealScalarFock.branches]

/-- The same source scalar variation generates its actual full Yukawa commutator. -/
theorem sourcePhaseGaugeScalarVariation_yukawa :
    scalarLinear sourcePhaseGaugeScalarVariation=
      Quantum.operatorMatrix sourcePhaseGaugeGenerator*scalarLinear SourceQuantumScalarChart.vacuum-
        scalarLinear SourceQuantumScalarChart.vacuum*Quantum.operatorMatrix sourcePhaseGaugeGenerator := by
  rw [sourcePhaseGaugeGenerator_native]
  exact PreparationVacuumNativeFieldInjection.originalScalar_commutator sourcePhaseGaugeLie SourceQuantumScalarChart.vacuum

/-- Scalar orbit is read through the original exterior action at the fixed source vacuum. -/
theorem sourcePhaseGaugeScalarVariation_original :
    scalarCoordinateEquiv.symm sourcePhaseGaugeScalarVariation=
      exteriorMotherLieAction 4 (p286LieBlockEmbed (p286CoordinateEquiv.symm sourcePhaseGaugeLie))
        (scalarCoordinateEquiv.symm SourceQuantumScalarChart.vacuum) :=
  PreparationVacuumNativeFieldInjection.scalarAction_mother sourcePhaseGaugeLie SourceQuantumScalarChart.vacuum

end LowEnergy.PreparationPhysicalPhaseGaugeRealization

import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCommonPhysicalObservation

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalCommonSpatialGreen
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
local instance CommonSpatialIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

/- Resolve only the already-paid original private owner; the emitted term is its actual imported constant. -/
open Lean Elab Term in
elab "paidSpatial% " id:ident : term => do
  let wanted := `LowEnergy.PreparationVacuumChargedSpatialResponse ++ id.getId
  let payerCandidates := (← getEnv).constants.toList.filter fun (name,_) =>
    name.toString.startsWith "_private.H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceChargedSecondUniform." && privateToUserName name == wanted
  match payerCandidates with
  | [(name,_)] =>
    logInfo m!"Original private payer: {name}"
    return mkConst name
  | _ => throwError "Expected one original SourceChargedSecondUniform private payer for {wanted}"

def sourceCommonCausalChannel (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) (i : Fin 3) : ℂ :=
  (sourceChargedDenominator n zeta i)⁻¹*
    sourceSlowRead (sourceActualNativeResidue q n zeta l r) ⟨i.val,by omega⟩

def sourceCommonChannelPrice (q : PhysicalResponsePoint) (c eta : ℝ) (l r : RestStateIndex)
    (i : Fin 3) : ℝ :=
  ‖slowFastFrame.transpose‖*(sourceChargedDenominatorPrice c eta i*sourceSpatialGaugePrice q eta l r+
    ‖sourceReaderLinear‖*(sourceChargedDenominatorPrice c eta i+sourceChargedQuadraticPrice c eta i)*
      sourceSpatialCurrentPrice q eta l r)

/-- Full source forcing and all three field denominators pay a momentum-uniform price. -/
theorem sourceCommonChannel_bound (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex) (i : Fin 3) :
    ‖sourceCommonCausalChannel q n (sourcePoleSide c eta) l r i‖≤ sourceCommonChannelPrice q c eta l r i := by
  let zeta:=sourcePoleSide c eta
  have realPart : zeta.re=eta := by simp [zeta,sourcePoleSide]
  have causal : 0<zeta.re := by rwa [realPart]
  have native : ‖sourceActualNativeResidue q n zeta l r‖≤ sourceSpatialGaugePrice q eta l r+
      ‖sourceReaderLinear‖*(‖zeta‖+‖n‖)*sourceSpatialCurrentPrice q eta l r := by
    unfold sourceActualNativeResidue
    apply (norm_add_le _ _).trans
    apply add_le_add
    · simpa only [realPart] using (paidSpatial% origin_bound) q n zeta causal l r
    · apply (Matrix.linfty_opNorm_mulVec _ _).trans
      exact mul_le_mul (sourceReaderLinear_bound n zeta)
        (by simpa only [realPart] using (paidSpatial% current_bound) q n zeta causal l r)
        (norm_nonneg _) (by positivity)
  have slow : ‖sourceSlowRead (sourceActualNativeResidue q n zeta l r) ⟨i.val,by omega⟩‖≤
      ‖slowFastFrame.transpose‖*‖sourceActualNativeResidue q n zeta l r‖ := (paidSpatial% slow_bound) _ _
  have inverse:=sourceChargedDenominator_bound n c eta frequency positive i
  have linear:=(paidSpatial% linear_denominator_bound) n c eta frequency positive i
  rw [sourceCommonCausalChannel,norm_mul]
  apply (mul_le_mul_of_nonneg_left (slow.trans (mul_le_mul_of_nonneg_left native (norm_nonneg _))) (norm_nonneg _)).trans
  calc
    _=‖slowFastFrame.transpose‖*(‖(sourceChargedDenominator n zeta i)⁻¹‖*sourceSpatialGaugePrice q eta l r+
        ‖sourceReaderLinear‖*((‖zeta‖+‖n‖)*‖(sourceChargedDenominator n zeta i)⁻¹‖)*sourceSpatialCurrentPrice q eta l r) := by ring
    _≤ sourceCommonChannelPrice q c eta l r i := by
      unfold sourceCommonChannelPrice
      have gp : 0≤ sourceSpatialGaugePrice q eta l r := by unfold sourceSpatialGaugePrice;positivity
      have cp : 0≤ sourceSpatialCurrentPrice q eta l r := by unfold sourceSpatialCurrentPrice;positivity
      gcongr

theorem sourceCommonChannel_continuous (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex) (i : Fin 3) :
    Continuous (fun n : PhysicalMomentum=>sourceCommonCausalChannel q n (sourcePoleSide c eta) l r i) := by
  let zeta:=sourcePoleSide c eta
  have causal : 0<zeta.re := by simpa [zeta,sourcePoleSide] using positive
  have point : Continuous (fun n : PhysicalMomentum=>fixedMomentum n zeta) := (paidSpatial% physical_point_continuous) zeta
  have reader : Continuous (fun n : PhysicalMomentum=>sourceNativeReaderFirst (fixedMomentum n zeta)) := by
    simp_rw [←sourceReaderLinear_generated]
    exact sourceReaderLinear.continuous.comp point
  have native : Continuous (fun n : PhysicalMomentum=>sourceActualNativeResidue q n zeta l r) :=
    ((paidSpatial% origin_continuous) q zeta causal l r).add
      (reader.matrix_mulVec ((paidSpatial% current_continuous) q zeta causal l r))
  have slow : Continuous (fun n : PhysicalMomentum=>sourceSlowRead (sourceActualNativeResidue q n zeta l r) ⟨i.val,by omega⟩) := by
    unfold sourceSlowRead
    split_ifs <;> fun_prop
  have denominator : Continuous (fun n : PhysicalMomentum=>sourceChargedDenominator n zeta i) := by
    unfold sourceChargedDenominator spatialSquare
    fun_prop
  exact (denominator.inv₀ (fun n=>sourceChargedDenominator_nonzero n c eta frequency positive i)).mul slow

def sourceCommonFieldPrice (q : PhysicalResponsePoint) (c eta : ℝ) (l r : RestStateIndex) : ℝ :=
  ∑i : Fin 3,sourceCommonChannelPrice q c eta l r i*‖sourceCommonOriginColumn i‖

theorem sourceCommonField_bound (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex) :
    ‖sourceJointFieldResidue q n (sourcePoleSide c eta) l r‖≤ sourceCommonFieldPrice q c eta l r := by
  rw [sourceCommonJoint_channels q n ⟨_,sourcePoleSide_field_domain n c eta frequency positive⟩]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (sourceCommonChannel_bound q n c eta frequency positive l r i) (norm_nonneg _)

theorem sourceCommonField_continuous (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex) :
    Continuous (fun n : PhysicalMomentum=>sourceJointFieldResidue q n (sourcePoleSide c eta) l r) := by
  have same : (fun n : PhysicalMomentum=>sourceJointFieldResidue q n (sourcePoleSide c eta) l r)=
      fun n=>∑i : Fin 3,sourceCommonCausalChannel q n (sourcePoleSide c eta) l r i • sourceCommonOriginColumn i := by
    funext n
    exact sourceCommonJoint_channels q n ⟨_,sourcePoleSide_field_domain n c eta frequency positive⟩ l r
  rw [same]
  exact continuous_finsetSum _ (fun i _=>(sourceCommonChannel_continuous q c eta frequency positive l r i).smul continuous_const)

end LowEnergy.PreparationPhysicalCommonSpatialGreen

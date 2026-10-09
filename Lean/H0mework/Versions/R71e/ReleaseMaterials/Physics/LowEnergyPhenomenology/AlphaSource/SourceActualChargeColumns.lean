import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCommonPropagationRead
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePhaseChargeActual

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalActualPhaseChargeReturn
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
local instance actualPhaseChargeIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

/-- Charge follows the original four source columns, including the neutral edge. -/
def sourceActualPhaseCharge (edge : Fin 2) : ℝ := if edge=0 then 1 else 0

theorem sourceActualColumn_weight (side edge : Fin 2) :
    (sourceWholeWeight (sourceChargedQuantumIndex side edge):ℂ)= -(sourceActualPhaseCharge edge:ℂ) := by
  change (sourcePhaseWeight (sourceColorDoubletIndex edge):ℂ)=_
  rw [sourcePhaseWeight_subset]
  fin_cases edge <;>
    norm_num [sourceActualPhaseCharge,sourceColorDoubletIndex,hyperPlusIndex,Fin.castLE,Sum.inl_ne_inr]

private theorem actual_basis (side edge : Fin 2) :
    Quantum.wholeBasis (sourceChargedQuantumIndex side edge)=
      Stage9DEF.Compatibility.embed (Pi.single (sourceChargedBasisIndex side edge) 1) := by
  unfold Quantum.wholeBasis sourceChargedQuantumIndex
  rw [Pi.basis_apply]
  funext spin
  by_cases same : spin=(sourceChargedBasisIndex side edge).1
  · rw [same]
    fin_cases edge <;>
      simp [Quantum.internalBasis,Module.Basis.prod_apply,Stage9DEF.Compatibility.embed,
        sourceColorDiracMatter,sourceColorDoubletMatter,Pi.single_apply,Prod.mk.injEq,
        sourceChargedBasisIndex]
  · fin_cases edge <;>
      simp [Quantum.internalBasis,Module.Basis.prod_apply,Stage9DEF.Compatibility.embed,
        sourceColorDiracMatter,sourceColorDoubletMatter,Pi.single_apply,Prod.mk.injEq,
        sourceChargedBasisIndex] at same ⊢

/-- The generator acts on the actual source restriction used by both Gauss and spatial preparations. -/
theorem sourceActualRestriction_generator (side edge : Fin 2) :
    sourceNativeOriginGenerator (sourceChargedRestriction side edge)=
      (-(sourceActualPhaseCharge edge:ℂ)*Complex.I) • sourceChargedRestriction side edge := by
  rw [sourceChargedRestriction_basis,←actual_basis,map_smul,sourcePhaseGenerator_basis,sourceActualColumn_weight]
  exact smul_comm _ _ _

theorem sourceActualRestriction_noether (side edge : Fin 2) :
    (phaseInverse.comp sourcePhaseNoether) (sourceChargedRestriction side edge)=
      (sourceActualPhaseCharge edge:ℂ) • sourceChargedRestriction side edge := by
  rw [sourcePhaseNoether_canonical,LinearMap.smul_apply,sourceActualRestriction_generator,smul_smul]
  congr 1
  calc
    Complex.I*(-(sourceActualPhaseCharge edge:ℂ)*Complex.I)=
      -(sourceActualPhaseCharge edge:ℂ)*(Complex.I*Complex.I) := by ring
    _=_ := by rw [Complex.I_mul_I];ring

/-- The phase inverse and source preparation are the actual operators of the original current reader. -/
theorem sourceActualPrepared_noether (side edge : Fin 2) :
    operator (phaseInverse.comp sourcePhaseNoether)
      (operator (actualRestStatePreparation (sourceChargedRestIndex side edge)) (YangMills.FullPairing.prepared 0))=
      (sourceActualPhaseCharge edge:ℂ) •
        operator (actualRestStatePreparation (sourceChargedRestIndex side edge)) (YangMills.FullPairing.prepared 0) := by
  have generated:=congrArg naturalCoordinates (sourceActualRestriction_noether side edge)
  simpa only [operator_coordinates,YangMills.FullPairing.prepared,sourceChargedRestriction,map_smul] using generated

/-- The independent original Dirac dual returns the source h times the actual column charge. -/
theorem sourceActualIndependent_current (side edge : Fin 2) :
    actual.conjugateMatter 0
      (canonicalDual (actualRestStatePreparation (sourceChargedRestIndex side edge))
        (sourcePhaseNoether
          (actualRestStatePreparation (sourceChargedRestIndex side edge) (actual.matter 0))))=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge edge:ℂ) := by
  rw [sourcePhaseNoether_original]
  have acted:=sourceActualPrepared_noether side edge
  have composition : operator ((phaseInverse.comp sourcePhaseNoether).comp
      (actualRestStatePreparation (sourceChargedRestIndex side edge))) (YangMills.FullPairing.prepared 0)=
      operator (phaseInverse.comp sourcePhaseNoether)
        (operator (actualRestStatePreparation (sourceChargedRestIndex side edge)) (YangMills.FullPairing.prepared 0)) := by
    change operator ((phaseInverse.comp sourcePhaseNoether)*
      (actualRestStatePreparation (sourceChargedRestIndex side edge))) _=_
    rw [operator_mul]
    rfl
  rw [composition,acted,inner_smul_right,actualRestState_orthonormal,if_pos rfl,mul_one,
    Stage10.ActionNormalization.phaseMomentum_source]
  push_cast
  ring

end LowEnergy.PreparationPhysicalActualPhaseChargeReturn

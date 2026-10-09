import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedCoupledSoftScattering
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativeOriginAction

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedSoftObservable
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
local instance chargedSoftCoefficientQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

/-- The lower matrix reads the source's actual spatial stabilizer connection on the complete matter carrier. -/
def sourceSoftConnectionLower (branch : Fin 2) : SourceMatrix :=
  ∑mu : Fin 4,coefficientMatrix mu (actual.coframe 0)*sourceNativeOriginConnection branch mu

def sourceSoftDensityMatrix (branch : Fin 2) : SourceMatrix := sourceVolume • sourceSoftConnectionLower branch

def sourceSoftFrequencyMatrix (branch : Fin 2) : SourceMatrix :=
  (-Complex.I) • (Ring.inverse (principalMatrix (actual.coframe 0))*sourceSoftConnectionLower branch)

private theorem coframe_density_zero (k : Fin 4) : coframeDensityCoefficients 0 k=0 := by
  cases k using Fin.cases <;>
    simp [coframeDensityCoefficients,densitizedLowerDirection,densitizedPrincipalDirection,
      principalDirection,lowerDirection,densitySpatialJet,coefficientJet,volumeDirection]

/-- Every frequency component is obtained from the same full normalized Hamiltonian variation. -/
theorem sourceSoftHamiltonianCoefficients (branch : Fin 2) (k : Fin 4) :
    fieldHamiltonianCoefficients (PreparationVacuumMixedFieldReturn.sourceField (sourceNativeOriginReal branch)) k=
      if k=0 then sourceSoftFrequencyMatrix branch else 0 := by
  rw [sourceScatteringHamiltonianCoefficients,sourceNativeOriginAction_state,sourceHamiltonianJet_connection]
  change (if k=0 then (-Complex.I) • (Ring.inverse (principalMatrix (sourceState sourcePoint.val).1)*
    (∑mu : Fin 4,coefficientMatrix mu (sourceState sourcePoint.val).1*sourceNativeOriginConnection branch mu)) else 0)=_
  rw [sourceState_event]
  rfl

/-- The original density reader keeps its true source volume and principal coefficient rather than substituting the Hamiltonian reader. -/
theorem sourceSoftDensityCoefficients (branch : Fin 2) (k : Fin 4) :
    fieldDensityCoefficients (PreparationVacuumMixedFieldReturn.sourceField (sourceNativeOriginReal branch)) k=
      if k=0 then sourceSoftDensityMatrix branch else 0 := by
  have coframe : (PreparationVacuumMixedFieldReturn.sourceField (sourceNativeOriginReal branch)).coframe=0 :=
    (sourceNativeOriginReal_remaining branch).2.1
  have connection (mu : Fin 4) :
      connectionDirection (PreparationVacuumMixedFieldReturn.sourceField (sourceNativeOriginReal branch)) mu=
        sourceNativeOriginConnection branch mu :=
    congrArg (fun state : ActionState=>state.2.1 mu) (sourceNativeOriginAction_state branch)
  have scalar : scalarDirection (PreparationVacuumMixedFieldReturn.sourceField (sourceNativeOriginReal branch))=0 :=
    congrArg (fun state : ActionState=>state.2.2) (sourceNativeOriginAction_state branch)
  rw [fieldDensityCoefficients,coframe,coframe_density_zero,zero_add]
  simp only [connection,scalar,add_zero,sourceSoftDensityMatrix,sourceSoftConnectionLower]

/-- The original two-direction density and shell Hessian is evaluated on the actual vanishing coframe directions. -/
theorem sourceSoftMixedCoefficients (left right : Fin 2) (k : Fin 4) :
    mixedCoefficients (PreparationVacuumMixedFieldReturn.sourceField (sourceNativeOriginReal left))
      (PreparationVacuumMixedFieldReturn.sourceField (sourceNativeOriginReal right)) k=0 := by
  have leftZero : (PreparationVacuumMixedFieldReturn.sourceField (sourceNativeOriginReal left)).coframe=0 :=
    (sourceNativeOriginReal_remaining left).2.1
  have rightZero : (PreparationVacuumMixedFieldReturn.sourceField (sourceNativeOriginReal right)).coframe=0 :=
    (sourceNativeOriginReal_remaining right).2.1
  cases k using Fin.cases <;>
    simp [mixedCoefficients,mixedDensityCoefficients,mixedLowerZero,shellContactCoefficients,
    densityPrincipalSecond,densityPrincipalJet,coefficientSecond,coefficientJet,
    volumeSecond,volumeDirection,leftZero,rightZero]

/-- The complete native endpoint is real; its non-action matter, dual and auxiliary entries remain in the source vector. -/
theorem sourceSoftComplexDirection (branch : Fin 2) :
    originalComplexDirection (nativeBranchVector branch)=
      ⟨PreparationVacuumMixedFieldReturn.sourceField (sourceNativeOriginReal branch),
        PreparationVacuumMixedFieldReturn.sourceField 0⟩ := by
  unfold originalComplexDirection
  change (⟨PreparationVacuumMixedFieldReturn.sourceField (sourceNativeOriginReal branch),
    PreparationVacuumMixedFieldReturn.sourceField (sourceNativeOriginImag branch)⟩ : ComplexDirection)=_
  rw [sourceNativeOriginImag_zero]

end LowEnergy.PreparationPhysicalChargedSoftObservable

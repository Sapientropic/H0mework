import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteWard.Readback
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteWard.Effect
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteWard.Writeback

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWard
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex MeasureTheory Set Filter
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

local instance feedbackGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

def updatedRInput (ordinal : Nat) : BurnolL2 :=
  packetTotal (actionPacket observation nontrivial half depth ordinal) +
    actualDelta (actionPacket observation nontrivial half depth ordinal)

def sourceWriteRead (ordinal : Nat) : BurnolL2 × BurnolL2 :=
  directions (CF.collapseValue (actionPacket observation nontrivial half depth ordinal).1
    (WB.oldPaid (actionPacket observation nontrivial half depth ordinal).2.1.1
      (configuration observation nontrivial half depth ordinal) +
      Native.nativeValue (factory observation nontrivial half)
        (actionPacket observation nontrivial half depth ordinal)))

-- This is a dependent read of the actual write, retaining its source increment.
def actualSelfRead (ordinal : Nat) : BurnolL2 × BurnolL2 :=
  sourceWriteRead observation nontrivial half depth ordinal -
    wardSourceValue observation nontrivial half (updatedRInput observation nontrivial half depth ordinal)

private theorem actual_material_value (ordinal : Nat) :
    (material observation nontrivial half depth ordinal).raw.eval
      (material observation nontrivial half depth ordinal).environment =
      (receipt observation nontrivial half depth ordinal).2.2.1 := by
  exact (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (S.baseRoot (actionPacket observation nontrivial half depth ordinal).2.1.1
      (configuration observation nontrivial half depth ordinal)).toAuthoritativeRoot
    (R.actionReader (actionPacket observation nontrivial half depth ordinal).2.1.1
      (configuration observation nontrivial half depth ordinal))
    (S.actualOccurrence (actionPacket observation nontrivial half depth ordinal).2.1.1)).symm

theorem actual_source_write_read (ordinal : Nat) :
    sourceWriteRead observation nontrivial half depth ordinal =
      wardSourceValue observation nontrivial half (updatedRInput observation nontrivial half depth ordinal) +
        selfSourceValue observation nontrivial half := by
  have write := congrArg (fun value => directions
    (CF.collapseValue (actionPacket observation nontrivial half depth ordinal).1 value))
    (actual_action_write observation nontrivial half depth ordinal)
  have old : directions (CF.collapseValue (actionPacket observation nontrivial half depth ordinal).1
      ((material observation nontrivial half depth ordinal).raw.eval
        (material observation nontrivial half depth ordinal).environment)) =
      wardSourceValue observation nontrivial half
        (packetTotal (actionPacket observation nontrivial half depth ordinal)) + selfSourceValue observation nontrivial half :=
    (congrArg (fun value => directions
      (CF.collapseValue (actionPacket observation nontrivial half depth ordinal).1 value))
      (actual_material_value observation nontrivial half depth ordinal)).trans
        (actual_admitted_directions observation nontrivial half depth ordinal)
  have effect : directions (CF.collapseValue (actionPacket observation nontrivial half depth ordinal).1
      ((material observation nontrivial half depth ordinal).raw.effect
        (material observation nontrivial half depth ordinal).environment
        (material observation nontrivial half depth ordinal).increment)) =
      wardSourceValue observation nontrivial half (actualDelta (actionPacket observation nontrivial half depth ordinal)) :=
    actual_material_source_effect observation nontrivial half depth ordinal
  have evaluated : directions (CF.collapseValue (actionPacket observation nontrivial half depth ordinal).1
      ((material observation nontrivial half depth ordinal).raw.eval
        (material observation nontrivial half depth ordinal).environment +
        (material observation nontrivial half depth ordinal).raw.effect
          (material observation nontrivial half depth ordinal).environment
          (material observation nontrivial half depth ordinal).increment)) =
      (wardSourceValue observation nontrivial half
        (packetTotal (actionPacket observation nontrivial half depth ordinal)) + selfSourceValue observation nontrivial half) +
        wardSourceValue observation nontrivial half (actualDelta (actionPacket observation nontrivial half depth ordinal)) := by
    rw [collapse_add, directions_add, old, effect]
  exact (write.trans evaluated).trans (by rw [updatedRInput, wardSourceValue_add]; abel)

theorem actual_self_source_feedback (ordinal : Nat) :
    actualSelfRead observation nontrivial half depth ordinal = selfSourceValue observation nontrivial half := by
  unfold actualSelfRead
  rw [actual_source_write_read]
  abel

theorem actual_self_K_price (ordinal : Nat) :
    inner ℂ (Prior.originalK observation nontrivial half) (actualSelfRead observation nontrivial half depth ordinal).1 =
      inner ℂ (Prior.originalK observation nontrivial half) (finiteForcePair observation nontrivial half) *
        inner ℂ (Prior.originalK observation nontrivial half) (Prior.originalK observation nontrivial half) := by
  rw [actual_self_source_feedback]
  exact K_read_price observation nontrivial half _

theorem actual_self_FourierK_price (ordinal : Nat) :
    inner ℂ (Prior.originalFourierK observation nontrivial half) (actualSelfRead observation nontrivial half depth ordinal).2 =
      inner ℂ (Prior.originalFourierK observation nontrivial half) (fourierL2 (finiteForcePair observation nontrivial half)) *
        inner ℂ (Prior.originalFourierK observation nontrivial half) (Prior.originalFourierK observation nontrivial half) := by
  rw [actual_self_source_feedback]
  exact FourierK_read_price observation nontrivial half _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWard
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

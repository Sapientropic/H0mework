import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteReaction.Readback
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteReaction.Effect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteReaction
open Complex MeasureTheory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
local instance actionGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

-- This new occurrence has its own material increment, distinct from the inherited 147 Rδ.
def actualDelta (ordinal : Nat) : BurnolL2 :=
  fieldReader (incrementEnvironment (reactionPacket observation nontrivial half depth ordinal) () ())
def actualValue (ordinal : Nat) : Branches :=
  finiteFields RSource.sourceShift (returnedField observation nontrivial half depth ordinal)+
    reaction_source (RSource.coordinate observation nontrivial half) RSource.sourceShift
def actualEffect (ordinal : Nat) : Branches := finiteFields RSource.sourceShift (actualDelta observation nontrivial half depth ordinal)

theorem actual_complete_source_effect (ordinal : Nat) :
  CF.collapseValue (reactionPacket observation nontrivial half depth ordinal).1
    ((material observation nontrivial half depth ordinal).raw.effect
      (material observation nontrivial half depth ordinal).environment
      (material observation nontrivial half depth ordinal).increment) = actualEffect observation nontrivial half depth ordinal := by
  rw [actual_material_source_effect,source_code_effect]
  rfl

theorem actual_reaction_source_value (ordinal : Nat) :
    CF.collapseValue (reactionPacket observation nontrivial half depth ordinal).1
      (receipt observation nontrivial half depth ordinal).2.2.1 = actualValue observation nontrivial half depth ordinal :=
  actual_complete_source_value observation nontrivial half depth ordinal

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteReaction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

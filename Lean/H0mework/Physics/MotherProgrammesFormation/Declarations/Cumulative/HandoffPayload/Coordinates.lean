import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffPayload.Factory
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AuthorityCoordinates.Restriction
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffEvents.Coverage

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffPayload
open MotherHandoffRestriction
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeAuthoritativeRootClosure N V} {events : EventFamily root.source}
    {emit : ∀ index, events index} (next : EventPoint events → NextRoot N)
    (parent : MotherArenaHigher.Material rank) (parentOutput : MotherAuthorityCoordinates.Output)
    (parentFormed : MotherArenaTheory.formTheory parent = some parentOutput)
    (parentPresentation : MotherAuthorityRoot.Presentation root parentOutput.1.1 parentOutput.1.2 parentOutput.2)
    (eventValue : MotherHandoffEvents.Value rank)
    (eventPresentation : MotherHandoffEvents.Presentation (Index root.source) events emit eventValue)
    (children : EventPoint events → MotherArenaHigher.Material rank)
    (outputs : EventPoint events → MotherAuthorityCoordinates.Output)
    (childrenFormed : ∀ point, MotherArenaTheory.formTheory (children point) = some (outputs point))
    (childPresentation : ∀ point, MotherAuthorityRoot.Presentation (next point).2
      (outputs point).1.1 (outputs point).1.2 (outputs point).2)

/-- Every coordinate is read from an actual formed event graph or actual
root output and then pulled back through its paid complete presentation.
No independent address condition is introduced for CP or debt programs. -/
def coordinatesOfFormedRoots : Coordinates (rank := rank) next where
  point := (Equiv.sigmaCongr eventPresentation.context eventPresentation.event).toEmbedding.trans
    (MotherHandoffEvents.pointAddress eventValue.1)
  event := fun index => (eventPresentation.event index).toEmbedding.trans
    ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  initialOccurrence := fun point => MotherAuthorityCoordinates.occurrence (children point) (outputs point)
    (childrenFormed point) (childPresentation point) (next point).2.toRoot.source.initial
  entry := MotherAuthorityCoordinates.entry parent parentOutput parentFormed parentPresentation

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffPayload

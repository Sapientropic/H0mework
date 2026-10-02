import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffPayload.Consumer
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffPayload.Coordinates
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffRoots.Coverage
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffRoots.Coordinates

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffPayload
open MotherHandoffRestriction
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeAuthoritativeRootClosure N V} {events : EventFamily root.source}
    (declaration : Declaration root.source events)
    (parent : MotherArenaHigher.Material rank) (parentOutput : MotherAuthorityCoordinates.Output)
    (parentFormed : MotherArenaTheory.formTheory parent = some parentOutput)
    (parentPresentation : MotherAuthorityRoot.Presentation root parentOutput.1.1 parentOutput.1.2 parentOutput.2)
    (rootsMaterial : MotherArenaHigher.Material rank) (rootsValue : MotherHandoffRoots.Value rank)
    (rootsFormed : MotherHandoffRoots.formRoots rootsMaterial = some rootsValue)
    (rootsPresentation : MotherHandoffRoots.Presentation (Index root.source) events declaration.emit N
      (fun point => (declaration.continuation point).next.1)
      (fun point => (declaration.continuation point).next.2) rootsValue)

/-- All addresses are obtained by eliminating the actual parent and complete
child-family outputs. This closes the payload coordinate obligation. -/
def coordinatesOfHandoffRoots : Coordinates (rank := rank) (fun point => (declaration.continuation point).next) :=
  coordinatesOfFormedRoots (fun point => (declaration.continuation point).next)
    parent parentOutput parentFormed parentPresentation rootsValue.1 rootsPresentation.event
    (fun point => MotherHandoffRoots.childMaterial rootsMaterial rootsValue (MotherHandoffRoots.pointEquiv rootsPresentation.event point))
    (fun point => rootsValue.2 (MotherHandoffRoots.pointEquiv rootsPresentation.event point))
    (fun point => MotherHandoffRoots.child_formed rootsMaterial rootsValue rootsFormed
      (MotherHandoffRoots.pointEquiv rootsPresentation.event point))
    rootsPresentation.root

def restrictEmit : ∀ index, events index :=
  fun index => (rootsPresentation.event.event index).symm
    (rootsValue.1.2 (rootsPresentation.event.context index))

theorem restrictEmit_eq : restrictEmit declaration rootsValue rootsPresentation = declaration.emit := by
  funext index
  exact (congrArg (rootsPresentation.event.event index).symm (rootsPresentation.event.emit_eq index)).trans
    ((rootsPresentation.event.event index).symm_apply_apply (declaration.emit index))

/-- Both payload functions and the emitter are read from actual material
outputs. Every event, entire child initial-occurrence fiber, and complete
old/target ledger participates in the exact sealed-law recovery. -/
theorem payload_on_formed_roots :
    ∃ material : MotherArenaHigher.Material rank,
      ∃ available : (formValues (fun point => (declaration.continuation point).next)
        (coordinatesOfHandoffRoots declaration parent parentOutput parentFormed parentPresentation
          rootsMaterial rootsValue rootsFormed rootsPresentation) material).isSome,
        let actual := (formValues (fun point => (declaration.continuation point).next)
          (coordinatesOfHandoffRoots declaration parent parentOutput parentFormed parentPresentation
            rootsMaterial rootsValue rootsFormed rootsPresentation) material).get available
        ∃ same : actual = valuesOf declaration,
          assembleLaw (assembleRestored (fun point => (declaration.continuation point).next)
            rootsPresentation.restrictRoots rootsPresentation.restrictRoots_eq
            (restrictEmit declaration rootsValue rootsPresentation) actual
            (recovered_laws declaration actual same)) = assembleLaw declaration := by
  obtain ⟨material, available, same, _⟩ := every_original_payload declaration
    (coordinatesOfHandoffRoots declaration parent parentOutput parentFormed parentPresentation
      rootsMaterial rootsValue rootsFormed rootsPresentation)
  exact ⟨material, available, same, congrArg assembleLaw
    (assembleRestored_recovers declaration rootsPresentation.restrictRoots rootsPresentation.restrictRoots_eq
      (restrictEmit declaration rootsValue rootsPresentation)
      (restrictEmit_eq declaration rootsValue rootsPresentation) _ same)⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffPayload

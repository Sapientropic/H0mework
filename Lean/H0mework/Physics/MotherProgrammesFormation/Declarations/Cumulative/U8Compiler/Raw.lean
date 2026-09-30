import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Revision.Consumer

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Compiler
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open ObstructionGeneratedMinimalCoface TypedSemanticWorldNetworkU8
open MotherInquiryAnswerOperands MotherU8Revision
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {U7 : U7ProducerCalculus N} (calculus : U7ObstructionEvolutionCalculus N U7)
    {Query : Type} (query : Query)
    (entry : OpenResponsibilityAt N (Support root visit))
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry)
    (obstruction : N.ObstructionAt (Support root visit))
    (faceCalculus : U7ObstructionEvolutionCalculus N U7) (projection : Projection root)
    (header : LivingHeader) {rank : Ordinal.{0}}
    (oldCoordinates : Coordinates (rank := rank) N)
    (oldOccurrence : ∀ current, root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current ↪ MotherArenaHigher.Base rank)
    (newCoordinates : HeaderCoordinates rank header)
local notation "M" => MotherArenaHigher.Material rank

/-- Every part of the original requiresU8 branch is assembled on its exact
indices. The two U7 calculi stay separate, and original source generators
supply the failure, successor, first write and row data. -/
def form (material : M) : Option (Compilation query entry authority calculus) :=
  (MotherU8Revision.uniqueMember (A := SourceNativeU7TheoryAuditAt calculus (calculus.generated obstruction).1)).bind (fun gate =>
  (formFailure root visit obstruction).bind (fun failure =>
  (formFrontier calculus query (InquiryEvent (root := root) (visit := visit)) entry authority gate failure faceCalculus projection).bind (fun frontier =>
  (formRevision (rooted := frontier.rooted) header.2.2 oldCoordinates newCoordinates.1
    (oldOccurrence frontier.rooted.oldSuccessor.next) newCoordinates.2 material).map (fun revision =>
      .requiresU8 obstruction gate failure ⟨frontier, revision⟩))))

omit faceCalculus projection header oldCoordinates oldOccurrence newCoordinates in
theorem every_core
    (gate : SourceNativeU7TheoryAuditAt calculus (calculus.generated obstruction).1)
    (failure : ActualExpressibilityFailure (Theory root) obstruction)
    (core : SourceGeneratedInquiryU8RevisionCoreAt root visit U7 calculus (Theory root) query
      (InquiryEvent (root := root) (visit := visit)) entry authority obstruction gate failure)
    (oldCoordinates : Coordinates (rank := rank) N)
    (oldOccurrence : ∀ current, root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current ↪ MotherArenaHigher.Base rank)
    (newCoordinates : HeaderCoordinates rank
      ⟨core.revision.generate.NewN, core.revision.generate.NewV, core.revision.generate.newLivingRoot⟩) :
    ∃ material : M,
      form calculus query entry authority obstruction core.frontier.face.calculus core.frontier.face.projection
        ⟨core.revision.generate.NewN, core.revision.generate.NewV, core.revision.generate.newLivingRoot⟩
        oldCoordinates oldOccurrence newCoordinates material = some (.requiresU8 obstruction gate failure core) := by
  obtain ⟨material, formed⟩ := every_revision core.revision oldCoordinates newCoordinates.1
    (oldOccurrence core.frontier.rooted.oldSuccessor.next) newCoordinates.2
  refine ⟨material, ?_⟩
  simp only [form, MotherU8Revision.uniqueMember_recovers gate, Option.bind_some]
  erw [formFailure_recovers root visit obstruction failure]
  dsimp only [Option.bind_some]
  erw [formFrontier_recovers calculus query (InquiryEvent (root := root) (visit := visit)) entry authority gate failure core.frontier]
  dsimp only [Option.bind_some]
  erw [formed]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Compiler

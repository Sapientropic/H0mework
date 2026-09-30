import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Revision.Occurrence

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Revision
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open ObstructionGeneratedMinimalCoface TypedSemanticWorldNetworkU8
open scoped Classical
noncomputable section
variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N V}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    {rooted : RootedActualExpressibilityFailureAt oldWorld oldVisit U7 failure}

/-- The original two grounding laws are checked on the entire actual
formed revision. Their proof-only packaging is the original sealed one. -/
def ground (occurrence : GeneratedTypedSemanticWorldNetworkRevisionAt rooted) :
    Option (FieldGroundedTypedSemanticWorldNetworkRevisionAt rooted) :=
  if exactGrounding : occurrence.ExactFieldGrounding then
    some (.ofGeneratedOccurrence occurrence exactGrounding)
  else if richer : occurrence.SourceGeneratedFaithfulRicherCofaceRestructuringAt then
    some (.ofSourceGeneratedRestructuring occurrence richer)
  else none

theorem ground_recovers (original : FieldGroundedTypedSemanticWorldNetworkRevisionAt rooted) :
    ground original.generate = some original := by
  unfold ground
  by_cases exactGrounding : original.generate.ExactFieldGrounding
  · rw [dif_pos exactGrounding]
    exact congrArg some (FieldGroundedTypedSemanticWorldNetworkRevisionAt.eq_of_generate_eq rfl)
  · have richer : original.generate.SourceGeneratedFaithfulRicherCofaceRestructuringAt := by
      cases original.revisionGrounding with
      | exact proof => exact (exactGrounding proof).elim
      | richer proof => exact proof
    rw [dif_neg exactGrounding, dif_pos richer]
    exact congrArg some (FieldGroundedTypedSemanticWorldNetworkRevisionAt.eq_of_generate_eq rfl)

variable {rank : Ordinal.{0}} {NewN : WorldRelationNetwork.{0}} {NewV : ConstructiveRoot.Vocabulary.{0}}
    (newRoot : SourceNativeLivingRootClosure NewN NewV)
    (oldCoordinates : Coordinates (rank := rank) N)
    (newCoordinates : Coordinates (rank := rank) NewN)
    (oldOccurrence : OldOccurrence rooted ↪ MotherArenaHigher.Base rank)
    (newOccurrence : NewOccurrence newRoot ↪ MotherArenaHigher.Base rank)
local notation "M" => MotherArenaHigher.Material rank

def formRevision (material : M) : Option (FieldGroundedTypedSemanticWorldNetworkRevisionAt rooted) :=
  (formOccurrence rooted newRoot oldCoordinates newCoordinates oldOccurrence newOccurrence material).bind ground

omit newRoot oldCoordinates newCoordinates oldOccurrence newOccurrence in
theorem every_revision (original : FieldGroundedTypedSemanticWorldNetworkRevisionAt rooted)
    (oldCoordinates : Coordinates (rank := rank) N)
    (newCoordinates : Coordinates (rank := rank) original.generate.NewN)
    (oldOccurrence : OldOccurrence rooted ↪ MotherArenaHigher.Base rank)
    (newOccurrence : NewOccurrence original.generate.newLivingRoot ↪ MotherArenaHigher.Base rank) :
    ∃ material : M, formRevision original.generate.newLivingRoot oldCoordinates newCoordinates oldOccurrence newOccurrence material = some original := by
  obtain ⟨material, formed⟩ := every_occurrence rooted original.generate oldCoordinates newCoordinates oldOccurrence newOccurrence
  exact ⟨material, by rw [formRevision, formed, Option.bind_some, ground_recovers]⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Revision

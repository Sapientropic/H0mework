import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Revision.Face

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Revision
open MotherInquiryAnswerOperands
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open ObstructionGeneratedMinimalCoface
open scoped Classical
noncomputable section
variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {U7 : U7ProducerCalculus N}
    (calculus : U7ObstructionEvolutionCalculus N U7)
    {Query : Type} (query : Query) {Event : Type 1} (event : Event)
    (entry : OpenResponsibilityAt N (Support root visit))
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry)
    {obstruction : N.ObstructionAt (Support root visit)}
    (gate : SourceNativeU7TheoryAuditAt calculus (calculus.generated obstruction).1)
    (failure : ActualExpressibilityFailure (Theory root) obstruction)

instance nonterminalSubsingleton :
    Subsingleton (CausalEntryNonterminalAt root.toAuthoritativeRoot.toLedgerRoot visit) := by
  unfold CausalEntryNonterminalAt
  split <;> infer_instance

abbrev Frontier := SourceNativeInquiryCofaceFrontierAt root visit U7 calculus (Theory root)
  query event entry authority obstruction gate failure

/-- The face's own calculus can differ from the outer inquiry calculus.
The original nonterminal root branch supplies the complete successor token. -/
def formFrontier (faceCalculus : U7ObstructionEvolutionCalculus N U7)
    (projection : Projection root) : Option (Frontier calculus query event entry authority gate failure) :=
  (formFailureFace failure faceCalculus entry projection).bind (fun face =>
    if same : face.rootEntry = entry then
      (uniqueMember (A := CausalEntrySuccessorAt root.toAuthoritativeRoot.toLedgerRoot visit face.rootEntry)).map
        (fun successor => SourceNativeInquiryCofaceFrontierAt.ofRootFailureFace face same successor)
    else none)

theorem formFrontier_recovers (frontier : Frontier calculus query event entry authority gate failure) :
    formFrontier calculus query event entry authority gate failure frontier.face.calculus frontier.face.projection =
      some frontier := by
  cases frontier
  rename_i face same successor
  cases same
  simp only [formFrontier, formFailureFace_recovers, Option.bind_some,
    uniqueMember_recovers successor, Option.map_some]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Revision

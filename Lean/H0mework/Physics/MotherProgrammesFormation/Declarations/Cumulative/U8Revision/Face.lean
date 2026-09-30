import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Revision.Failure

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
    {obstruction : N.ObstructionAt (Support root visit)}
    (failure : ActualExpressibilityFailure (Theory root) obstruction)

abbrev FailureFace := SourceNativeRootExpressibilityFailureFaceAt root.toAuthoritativeRoot visit (U7 := U7) failure

/-- The face's own complete U7 calculus is retained. Its exact emitted
event and the full active projection are supplied by the original sources. -/
def formFailureFace (calculus : U7ObstructionEvolutionCalculus N U7)
    (entry : OpenResponsibilityAt N (Support root visit)) (projection : Projection root) : Option (FailureFace (U7 := U7) failure) :=
  (MotherNativeFaces.semanticFace root visit projection).bind (fun face =>
    (uniqueMember (A := SourceNativeU7TheoryAuditAt calculus (calculus.source.emit obstruction))).bind (fun audit =>
      if entrySame : entry = U7ActualSuccessorSource.demandEntry (calculus.source.emit obstruction) then
        if commutes : U7DemandEntryRootDispositionCommutesAt calculus (calculus.source.emit obstruction) entry
            ((root.toAuthoritativeRoot.toLedgerRoot.source.ledgerCompiler.compile
              (root.emitted visit.current)).entryDisposition entry) then
          if installed : HEq face.rootRead (SourceNativeRootExpressibilityFailureTokenAt.canonical
              (failure := failure) (calculus := calculus) (event := calculus.source.emit obstruction)) then
            some {
              lawSurface_eq := rfl
              projection := face.projection
              active := face.active
              classifier_eq := face.classifier_eq
              calculus := calculus
              u7Event := calculus.source.emit obstruction
              u7Event_eq_emit := rfl
              theoryAudit := audit
              support_eq := rfl
              rootEntry := entry
              rootEntryAtFailure_eq := entrySame
              rootDispositionCommutes := commutes
              project_heq := installed }
          else none
        else none
      else none))

theorem formFailureFace_recovers (face : FailureFace (U7 := U7) failure) :
    formFailureFace failure face.calculus face.rootEntry face.projection = some face := by
  cases face with
  | mk lawEq projection active classified calculus event emitted audit supportEq entry entrySame commutes installed =>
    cases emitted
    change entry = U7ActualSuccessorSource.demandEntry (calculus.source.emit obstruction) at entrySame
    have selected := MotherNativeFaces.semanticFace_recovers
      (root := root) (visit := visit) ⟨projection, active, classified⟩
    simp only [formFailureFace, selected, Option.bind_some, uniqueMember_recovers audit]
    split_ifs with entryCondition dispositionCondition installationCondition
    · rfl
    · exact False.elim (installationCondition installed)
    · exact False.elim (dispositionCondition commutes)
    · exact False.elim (entryCondition entrySame)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Revision

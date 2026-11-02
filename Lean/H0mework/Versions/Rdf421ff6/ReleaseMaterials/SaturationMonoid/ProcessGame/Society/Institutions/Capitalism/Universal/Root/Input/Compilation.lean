import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Input.Legacy
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeRevisionCoface

/-!
# One source-fixed compiler for legacy and programme input

The full input is read only from the sealed source germ.  A nonempty raw
programme generates its actual material revision; legacy and empty words
retain the pre-existing canonical revision.  No revision, result or next is
accepted after activation.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.InputSource

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open ConstructiveRoot.TypedSemanticWorldNetworkU8
open M9ProofCarryingRenewalInquiryRoot M14SourceGeneratedContributionMergeActionSource

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (datum : Datum Party Good Port Technology Instrument)
  (oldVisit : OldVisit) (sourceIndex boundary : Nat)

def chosenInput (query : Query datum oldVisit sourceIndex boundary) :
    Option { raw : RawInput Party Good Port Technology Instrument // 0 < (ProgrammeSource.registrationSize raw) } :=
  match query.raw with
  | .legacy => none
  | .programme raw => if nonempty : 0 < (ProgrammeSource.registrationSize raw) then some ⟨raw, nonempty⟩ else none

def selectedInput := chosenInput datum oldVisit sourceIndex boundary
  (germAt datum ((root datum).emitted (visit datum oldVisit sourceIndex boundary).current))

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem chosen_is_source_selected (query : Query datum oldVisit sourceIndex boundary) :
    chosenInput datum oldVisit sourceIndex boundary query =
      selectedInput datum oldVisit sourceIndex boundary := by
  rw [germ_unique datum _ query]
  rfl

def producedRevision (query : Query datum oldVisit sourceIndex boundary) :
    FieldGroundedTypedSemanticWorldNetworkRevisionAt
      (frontier datum oldVisit sourceIndex boundary).rooted :=
  match chosenInput datum oldVisit sourceIndex boundary query with
  | none => legacyRevision datum oldVisit sourceIndex boundary
  | some raw => ProgrammeRevisionCoface.fieldGroundedForCoface
      raw.val (component datum) (visit datum oldVisit sourceIndex boundary)
      (frontier datum oldVisit sourceIndex boundary).rooted raw.property

def core (query : Query datum oldVisit sourceIndex boundary) :
    SourceGeneratedInquiryU8RevisionCoreAt
      (root datum) (visit datum oldVisit sourceIndex boundary)
      RootInquiryU8CompletionRegression.U7 RootInquiryU8CompletionRegression.theoryAuditCalculus
      RootInquiryU8CompletionRegression.oldTheory query
      (ULift.up.{1, 0} ((root datum).emitted (visit datum oldVisit sourceIndex boundary).current))
      M9ProofCarryingRenewalU8Failure.entry (authority datum oldVisit sourceIndex boundary)
      RootInquiryU8CompletionRegression.obstruction RootInquiryU8CompletionRegression.u7Gate
      RootInquiryU8CompletionRegression.failure := by
  have same := germ_unique datum _ query
  cases same
  exact ⟨frontier datum oldVisit sourceIndex boundary,
    producedRevision datum oldVisit sourceIndex boundary
      (germAt datum ((root datum).emitted (visit datum oldVisit sourceIndex boundary).current))⟩

def compilation (query : Query datum oldVisit sourceIndex boundary) :
    SourceNativeInquiryCompilationAt
      (root datum) (visit datum oldVisit sourceIndex boundary)
      RootInquiryU8CompletionRegression.U7 RootInquiryU8CompletionRegression.theoryAuditCalculus
      RootInquiryU8CompletionRegression.oldTheory query
      (ULift.up.{1, 0} ((root datum).emitted (visit datum oldVisit sourceIndex boundary).current))
      M9ProofCarryingRenewalU8Failure.entry (authority datum oldVisit sourceIndex boundary) :=
  .requiresU8 RootInquiryU8CompletionRegression.obstruction RootInquiryU8CompletionRegression.u7Gate
    RootInquiryU8CompletionRegression.failure (core datum oldVisit sourceIndex boundary query)

def compilationProgram (query : Query datum oldVisit sourceIndex boundary) :
    SourceNativeInquiryCompilationProgramAt
      (root datum) (visit datum oldVisit sourceIndex boundary)
      RootInquiryU8CompletionRegression.U7 RootInquiryU8CompletionRegression.theoryAuditCalculus
      RootInquiryU8CompletionRegression.oldTheory query
      (ULift.up.{1, 0} ((root datum).emitted (visit datum oldVisit sourceIndex boundary).current))
      M9ProofCarryingRenewalU8Failure.entry (authority datum oldVisit sourceIndex boundary) where
  compile := fun _ => compilation datum oldVisit sourceIndex boundary query

def compilationFace (query : Query datum oldVisit sourceIndex boundary) :
    SourceNativeRootInquiryCompilationFaceCoreAt
      (root datum) (visit datum oldVisit sourceIndex boundary) query
      (ULift.up.{1, 0} ((root datum).emitted (visit datum oldVisit sourceIndex boundary).current))
      M9ProofCarryingRenewalU8Failure.entry (authority datum oldVisit sourceIndex boundary)
      (compilationProgram datum oldVisit sourceIndex boundary query).generate.output where
  projection := (installation datum).embed .compilation
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := by
    have same := germ_unique datum _ query
    cases same
    exact HEq.rfl

def sourceState : RootInquiryStateAt N V where
  root := root datum
  visit := visit datum oldVisit sourceIndex boundary
  U7 := RootInquiryU8CompletionRegression.U7
  calculus := RootInquiryU8CompletionRegression.theoryAuditCalculus
  Query := Query datum oldVisit sourceIndex boundary
  entryAt := fun _ => M9ProofCarryingRenewalU8Failure.entry
  authorityAt := fun _ => authority datum oldVisit sourceIndex boundary
  compilationProgramAt := compilationProgram datum oldVisit sourceIndex boundary
  compilationFaceAt := compilationFace datum oldVisit sourceIndex boundary
  u7RootDisposition_commutes := by
    intro _ _ _ audit
    cases audit
    exact (failureFace datum oldVisit sourceIndex boundary).rootDispositionCommutes

def presentation : RootInquiryStatePresentation where
  N := N
  V := V
  state := RootInquiryEngineStateAt.create (sourceState datum oldVisit sourceIndex boundary)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.InputSource

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission.Target

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat) (datum : Datum input (frame input depth count))

def compilationAt (query : Query input (frame input depth count) datum)
    (event : ExactTemporalCausalRootEventAt
      (root input (frame input depth count) datum).toAuthoritativeRoot.toLedgerRoot
      (visit input (frame input depth count) datum)) :
    SourceNativeInquiryCompilationAt (root input (frame input depth count) datum)
      (visit input (frame input depth count) datum) (frame input depth count).installed.U7
      (frame input depth count).installed.calculus (root input (frame input depth count) datum).source.base.lawSurface
      query (ULift.up.{1, 0} (originalOccurrence input depth count))
      (Continuation.sourceEntry input (frame input depth count))
      (authority input (frame input depth count) datum) :=
  .actualAction ((program input depth count datum).generate event)

def compilationFace (query : Query input (frame input depth count) datum) :
    SourceNativeRootInquiryCompilationFaceCoreAt (root input (frame input depth count) datum)
      (visit input (frame input depth count) datum) query (ULift.up.{1, 0} (originalOccurrence input depth count))
      (Continuation.sourceEntry input (frame input depth count))
      (authority input (frame input depth count) datum)
      (compilationAt input depth count datum query (sourceEvent input depth count datum)) := by
  cases germ_unique input (frame input depth count) datum (originalOccurrence input depth count) query
  exact {
    projection := (installation input (frame input depth count) datum).embed .compilation
    active := ()
    classifier_eq := rfl
    project_heq := HEq.rfl }

def state : RootInquiryStateAt (frame input depth count).native.N (frame input depth count).native.V where
  root := root input (frame input depth count) datum
  visit := visit input (frame input depth count) datum
  U7 := (frame input depth count).installed.U7
  calculus := (frame input depth count).installed.calculus
  Query := Query input (frame input depth count) datum
  entryAt := fun _ => Continuation.sourceEntry input (frame input depth count)
  authorityAt := fun _ => authority input (frame input depth count) datum
  compilationProgramAt := fun query => { compile := compilationAt input depth count datum query }
  compilationFaceAt := compilationFace input depth count datum
  u7RootDisposition_commutes := by
    intro query obstruction audit audited
    cases audited

def presentation : RootInquiryStatePresentation :=
  ⟨(frame input depth count).native.N, (frame input depth count).native.V,
    RootInquiryEngineStateAt.create (state input depth count datum)⟩

theorem original_source_compiles_actual_action (query : (presentation input depth count datum).Query) :
    (state input depth count datum).compileInquiry query = .actualAction (generated input depth count datum) := rfl

theorem compiled_answer_is_the_original_attempt (query : (presentation input depth count datum).Query) :
    (compilationAt input depth count datum query (sourceEvent input depth count datum)).answerReadout =
      result input depth count datum := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeHistory
import H0mework.Versions.Rdf421ff6.Foundation.Runtime.Inquiry

/-! Ordinary inquiry continues on the literal programme root.  These
presentations enter the enclosing input registry; no second registry or
one-shot answered state is created here. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeInquiry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open ProgrammeWorld ProgrammeSource ProgrammeLiving ProgrammeHistory

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : Input Party Good Port Technology Instrument)

def initialRow :
    ((livingRoot input).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite (livingRoot input).toAuthoritativeRoot.toRoot.initialVisit)).GeneratedEntryRowAt
        (inquiryEntryAt input (emitted input .bootstrap)) :=
  (((livingRoot input).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (.finite (livingRoot input).toAuthoritativeRoot.toRoot.initialVisit)).canonicalGeneratedEntryRow?
      (inquiryEntryAt input (emitted input .bootstrap))).get (by rfl)

def initialAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt (livingRoot input)
    (temporalVisit input 0) (inquiryEntryAt input (emitted input .bootstrap)) :=
  .generatedFromInitialRow (livingRoot input) (inquiryEntryAt input (emitted input .bootstrap))
    (initialRow input)

theorem canonical_entry_next (current : (V input).Current) :
    (livingRoot input).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
      (current := current) (next := next input current) rfl
      (inquiryEntryAt input (emitted input current)) =
        inquiryEntryAt input (emitted input (next input current)) := by
  cases current <;> rfl

def authorityAt : (index : Nat) →
    SourceNativeLivingTemporalCausalEntryAuthorityAt (livingRoot input) (temporalVisit input index)
      (inquiryEntryAt input (emitted input (visitAt input index).current))
  | 0 => initialAuthority input
  | index + 1 =>
      canonical_entry_next input (visitAt input index).current ▸ (authorityAt index).next rfl

def answerFaceAt (index : Nat) : SourceNativeRootSemanticFaceAt (livingRoot input)
    (temporalVisit input index) where
  projection := .execution
  active := ()
  classifier_eq := rfl

def consumerAt (index : Nat) : SourceNativeInquiryAnswerConsumerAt
    PUnit.unit (ULift.up.{1, 0} (emitted input (visitAt input index).current))
      (inquiryEntryAt input (emitted input (visitAt input index).current)) (answerFaceAt input index) where
  projection := .consumer
  active := ()
  classifier_eq := rfl
  project_heq := HEq.rfl

def compilationAt (index : Nat) : SourceNativeInquiryCompilationAt
    (livingRoot input) (temporalVisit input index) (inquiryU7 input) (inquiryCalculus input)
    (TheoryState.rootSemantic (N input)) PUnit.unit
    (ULift.up.{1, 0} (emitted input (visitAt input index).current))
    (inquiryEntryAt input (emitted input (visitAt input index).current)) (authorityAt input index) :=
  .answered (answerFaceAt input index) (consumerAt input index)

def stateAt (index : Nat) : RootInquiryStateAt (N input) (V input) where
  root := livingRoot input
  visit := temporalVisit input index
  U7 := inquiryU7 input
  calculus := inquiryCalculus input
  Query := PUnit
  entryAt := fun _ => inquiryEntryAt input (emitted input (visitAt input index).current)
  authorityAt := fun _ => authorityAt input index
  compilationProgramAt := fun query => by
    cases query
    exact { compile := fun _exactOccurrence => compilationAt input index }
  compilationFaceAt := fun query => by
    cases query
    exact { projection := .inquiry
            active := ()
            classifier_eq := rfl
            project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro query obstruction audit auditEq
    cases query
    cases auditEq

def presentationAt (index : Nat) : RootInquiryStatePresentation where
  N := N input
  V := V input
  state := RootInquiryEngineStateAt.create (stateAt input index)

def queryAt (index : Nat) : (RootInquiryProcessNode.active (presentationAt input index)).Query :=
  PUnit.unit

theorem query_unique (index : Nat)
    (candidate : (RootInquiryProcessNode.active (presentationAt input index)).Query) :
    candidate = queryAt input index := by
  cases candidate
  rfl

theorem presentation_keeps_literal_root (index : Nat) :
    (presentationAt input index).state.base.root = livingRoot input := rfl

theorem presentation_keeps_original_visit (index : Nat) :
    (presentationAt input index).state.base.visit = temporalVisit input index := rfl

set_option linter.defProp false in
def native_successor_valid (index : Nat) :=
  RootInquiryProcessNode.active_directlyAnswered_successor_valid
    (presentationAt input index) (presentationAt input (index + 1)) (queryAt input index)
    (answerFaceAt input index) (consumerAt input index) rfl rfl HEq.rfl

theorem presentation_erase_injective : Function.Injective (fun index => (presentationAt input index).erase) := by
  intro first second same
  have labels := congrArg
    (fun state : AnyAuthoritativeRootCurrent =>
      (⟨state.current.V.Current, state.current.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
  have currents : (visitAt input first).current = (visitAt input second).current :=
    eq_of_heq (Sigma.mk.inj labels).2
  exact visit_current_injective input currents

set_option linter.defProp false in
def inquiry_answer_is_actual_execution (index : Nat) :=
  RootInquiryProcessNode.active_answer_heq_directlyAnswered (presentationAt input index)
    (queryAt input index) (answerFaceAt input index) (consumerAt input index) rfl

#print axioms native_successor_valid
#print axioms inquiry_answer_is_actual_execution

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeInquiry

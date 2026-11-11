import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.LivingLawRootInquiryCompletionRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.LivingLawOperationalSeparationSourceNativeRootRegression

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootInquiryCompletion
namespace CompositeFieldAuthorityRegression

open RootInquiryCompletionRegression
open RootInquiryCompletionRegression.Base
open OperationalU7RootLedgerRegression

inductive Projection
  | inquiry
  | answer (value : Bool)
  | consumer (value : Bool)

def inquiryAudit :
    SourceNativeInquiryFrontAuditAt Base.U7 Base.calculus Base.theory true :=
  .answered

def entry : OpenResponsibilityAt Base.N true := ⟨(), ()⟩

def projectionLaw : SourceNativeProjectionLaw
    OperationalU7RootLedgerRegression.restructuringSource.toLedgerSource where
  Projection := Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ =>
    match projection with
    | .inquiry => SourceNativeInquiryCompilationTokenAt
        entry (query := ()) (event := ULift.up.{1, 0} occurrence)
          (audit := inquiryAudit) Bool
    | .answer _ => Bool
    | .consumer value => SourceNativeInquiryAnswerConsumerTokenAt
        () (ULift.up.{1, 0} occurrence) Base.entry value
  project := fun projection {_} _ _ => by
    cases projection with
    | inquiry => exact .canonical false
    | answer value => exact value
    | consumer _ => exact .canonical

def authoritySource : SourceNativeAuthoritySource Base.N Base.V where
  restructuringSource := OperationalU7RootLedgerRegression.restructuringSource
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal
      OperationalU7RootLedgerRegression.restructuringSource
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := Base.theory
  projectionLaw := projectionLaw

def root : SourceNativeLivingRootClosure Base.N Base.V where
  source :=
    { base := authoritySource
      terminalHandoff := authoritySource.emptyFaithfulTerminalHandoff
        (fun _ => ⟨fun terminal => nomatch terminal⟩) }
  emitted := OperationalU7RootLedgerRegression.emitted
  compiler_commutes := fun _ => rfl

abbrev visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot :=
  .finite root.toAuthoritativeRoot.toRoot.initialVisit

def fixedInquiryEvent :=
  ULift.up.{1, 0} (root.emitted visit.current)

def authority :
    SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry :=
  ((SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial?
    root entry .initial).get (by rfl)).2

def answerFace (value : Bool) :
    SourceNativeRootSemanticFaceAt root visit where
  projection := .answer value
  active := PUnit.unit
  classifier_eq := rfl

def consumer (value : Bool) :
    SourceNativeInquiryAnswerConsumerAt
      () (ULift.up.{1, 0} (root.emitted visit.current)) entry
        (answerFace value) where
  projection := .consumer value
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def compilation (value : Bool) :
    SourceNativeInquiryCompilationAt root visit Base.U7 Base.calculus
      Base.theory () (ULift.up.{1, 0} (root.emitted visit.current))
        entry authority :=
  .answered (answerFace value) (consumer value)

def state : RootInquiryStateAt Base.N Base.V where
  root := root
  visit := visit
  U7 := Base.U7
  calculus := Base.calculus
  Query := Unit
  entryAt := fun _ => entry
  authorityAt := fun _ => authority
  compilationProgramAt := fun _ =>
    { compile := fun _exactOccurrence => compilation false }
  compilationFaceAt := fun _ =>
    { projection := .inquiry
      active := PUnit.unit
      classifier_eq := rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _ _ _ equality
    cases equality

def fixedInquiryFace :
    SourceNativeRootInquiryCompilationFaceAt state () :=
  state.compilationFaceAt ()

def fixedEngineState : RootInquiryEngineStateAt Base.N Base.V :=
  RootInquiryEngineStateAt.create state

/- A gearbox no longer exposes a field through which an alias old-root face
can replace the compilation face owned by `state`. -/
/-- error: Invalid field `inquiryFaceAt` -/
#guard_msgs (substring := true) in
#check fixedEngineState.inquiryFaceAt


def fixedPresentation : RootInquiryStatePresentation where
  N := Base.N
  V := Base.V
  state := fixedEngineState

/-- The same fixed root projection cannot authenticate a compiler that
silently changes the answer bit.  Such a compiler can be described as a
model, but it cannot enter `RootInquiryStateAt`. -/
theorem sibling_answer_field_has_no_root_authority :
    IsEmpty { face : SourceNativeRootInquiryCompilationFaceCoreAt root visit ()
      (ULift.up.{1, 0} (root.emitted visit.current))
      entry authority (compilation true) //
        face.projection = Projection.inquiry } := by
  constructor
  rintro ⟨⟨projection, active, _, identity⟩, projection_eq⟩
  cases projection_eq
  cases active
  change HEq
    (SourceNativeInquiryCompilationTokenAt.canonical
      (entry := entry) (query := ()) (event := fixedInquiryEvent)
      (audit := inquiryAudit) false)
    (SourceNativeInquiryCompilationTokenAt.canonical
      (entry := entry) (query := ()) (event := fixedInquiryEvent)
      (audit := inquiryAudit) true) at identity
  cases identity

theorem sibling_root_reads_are_distinct :
    (answerFace false).rootRead ≠ (answerFace true).rootRead := by
  change false ≠ true
  decide

/-! ## Answer-to-ledger incidence is not contagious -/

def rowInquiryAudit : SourceNativeInquiryFrontAuditAt
    OperationalSearchSourceNativeRootRegression.u7
    OperationalSearchSourceNativeRootRegression.u7Calculus
    (.rootSemantic OperationalSearchSourceNativeRootRegression.N) () :=
  .answered

def falseEntryInquiryToken : SourceNativeInquiryCompilationTokenAt
    (OperationalSearchSourceNativeRootRegression.entry false)
    (query := ()) (event := fixedInquiryEvent)
    (audit := rowInquiryAudit) Bool :=
  .canonical false

/-- The root-installed inquiry token itself retains the exact responsibility
row even when its answer carrier and value are otherwise identical. -/
def sibling_entry_cannot_borrow_inquiry_root_authority : PUnit := by
  fail_if_success
    exact (falseEntryInquiryToken : SourceNativeInquiryCompilationTokenAt
      (OperationalSearchSourceNativeRootRegression.entry true)
      (query := ()) (event := fixedInquiryEvent)
      (audit := rowInquiryAudit) Bool)
  exact PUnit.unit

def falseEntryConsumerToken : SourceNativeInquiryAnswerConsumerTokenAt
    () fixedInquiryEvent
      (OperationalSearchSourceNativeRootRegression.entry false) false :=
  .canonical

/-- A consumer token grounded on one exact live-ledger entry cannot be
retyped onto a sibling responsibility row. -/
def sibling_entry_cannot_borrow_answer_authority : PUnit := by
  fail_if_success
    exact (falseEntryConsumerToken : SourceNativeInquiryAnswerConsumerTokenAt
      () fixedInquiryEvent
        (OperationalSearchSourceNativeRootRegression.entry true) false)
  exact PUnit.unit


/-! ## Public execution is engine-owned -/

/-- Raw resolution grammar may describe a sibling answer, but it is not the
resolution generated by the fixed compiler. -/
def counterfeitResolution : InternalInquiryResolutionAt fixedPresentation () :=
  .directlyAnswered (answerFace true) (consumer true)

def process : SourceNativeInquiryEngineProcess.{0} :=
  fixedPresentation.oneShotProcess

def engine : Engine process := Engine.initial process

def activation : Engine.SourceNativeInquiryActivationAt engine :=
  engine.uniqueInquiryActivation () (by
    intro candidate
    change Unit at candidate
    cases candidate
    rfl)

def occurrence : Engine.ExactRootInquiryOccurrenceAt engine () :=
  engine.ask activation

theorem fixed_inquiry_field_reads_its_source_answer :
    occurrence.resolution =
      .directlyAnswered (answerFace false) (consumer false) :=
  rfl

def generatedAnswer : Bool := occurrence.answer

/- Raw state and resolution executors are not public authority mouths. -/
/-- error: Unknown constant -/
#guard_msgs (substring := true) in
#check RootInquiryStatePresentation.resolve

/-- error: Unknown constant -/
#guard_msgs (substring := true) in
#check InternalInquiryResolutionAt.answer

/-- error: Unknown constant -/
#guard_msgs (substring := true) in
#check InternalInquiryResolutionAt.receipt

/-- error: Unknown constant -/
#guard_msgs (substring := true) in
#check InternalInquiryResolutionAt.nextRootCurrent

/-- error: Unknown constant -/
#guard_msgs (substring := true) in
#check RootInquiryProcessNode.resolve

/-- error: Unknown constant -/
#guard_msgs (substring := true) in
#check RootInquiryProcessNode.answer

/-- error: Unknown constant -/
#guard_msgs (substring := true) in
#check RootInquiryProcessNode.receipt

/-- error: Unknown constant -/
#guard_msgs (substring := true) in
#check RootInquiryProcessNode.nextRootCurrent

#print axioms sibling_answer_field_has_no_root_authority

end CompositeFieldAuthorityRegression
end RootInquiryCompletion
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission.Target
import H0mework.Versions.Rdf421ff6.Foundation.Runtime.Inquiry

/-! Installed inquiry coordinates of the actual accounting source.  These
fields read existing projections; the runtime's source action selects the
compiler branch and its generated successor. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def entry (frame : NativeFrame input) (current : frame.V.Current) :=
  frame.entrySupport (frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
    (frame.root.emitted current))

def NotIssue (frame : NativeFrame input) (current : frame.V.Current) : Prop :=
  ∀ claim, Cursor.action input (frame.cursor current) ≠ .issue claim

def answerFace (frame : NativeFrame input)
    (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot) :
    SourceNativeRootSemanticFaceAt frame.root visit :=
  ⟨frame.projection, frame.active visit.current, frame.classify_eq visit.current⟩

structure Installed (frame : NativeFrame input) where
  U7 : U7ProducerCalculus frame.N
  calculus : U7ObstructionEvolutionCalculus frame.N U7
  compilationProjection : frame.root.toAuthoritativeRoot.source.projectionLaw.Projection
  compilationActive : ∀ current, frame.root.toAuthoritativeRoot.source.projectionLaw.ActiveAt
    compilationProjection (frame.root.emitted current)
  compilationClassify : ∀ current,
    frame.root.toAuthoritativeRoot.source.projectionLaw.classify compilationProjection
      (frame.root.emitted current) = .inl (compilationActive current)
  compilationRead : ∀ current, HEq
    (frame.root.toAuthoritativeRoot.source.projectionLaw.project compilationProjection
      (frame.root.emitted current) (compilationActive current))
    (SourceNativeInquiryCompilationTokenAt.canonical
      (entry := entry input frame current) (query := PUnit.unit)
      (event := ULift.up.{1, 0} (frame.root.emitted current))
      (audit := (.answered : SourceNativeInquiryFrontAuditAt U7 calculus
        frame.root.toAuthoritativeRoot.source.lawSurface _)) (observe input (frame.cursor current)))
  consumerProjection : frame.root.toAuthoritativeRoot.source.projectionLaw.Projection
  consumerActive : ∀ current, NotIssue input frame current →
    frame.root.toAuthoritativeRoot.source.projectionLaw.ActiveAt consumerProjection (frame.root.emitted current)
  consumerClassify : ∀ current safe,
    frame.root.toAuthoritativeRoot.source.projectionLaw.classify consumerProjection
      (frame.root.emitted current) = .inl (consumerActive current safe)
  consumerRead : ∀ current safe, HEq
    (frame.root.toAuthoritativeRoot.source.projectionLaw.project consumerProjection
      (frame.root.emitted current) (consumerActive current safe))
    (SourceNativeInquiryAnswerConsumerTokenAt.canonical
      (query := PUnit.unit) (event := ULift.up.{1, 0} (frame.root.emitted current))
      (entry := entry input frame current) (answer := observe input (frame.cursor current)))

private theorem consumerToken_heq {N : WorldRelationNetwork} {support : N.Support}
    (original : OpenResponsibilityAt N support) {Query : Type} (query : Query)
    {Event : Type 1} (event : Event) {A B : Type} (left : A) (right : B) (same : HEq left right) :
    HEq (SourceNativeInquiryAnswerConsumerTokenAt.canonical
      (entry := original) (query := query) (event := event) (answer := left))
      (SourceNativeInquiryAnswerConsumerTokenAt.canonical
        (entry := original) (query := query) (event := event) (answer := right)) := by
  cases same
  rfl

def Installed.consumer {frame : NativeFrame input} (installed : Installed input frame)
    (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
    (safe : NotIssue input frame visit.current) :
    SourceNativeInquiryAnswerConsumerAt PUnit.unit (ULift.up.{1, 0} (frame.root.emitted visit.current))
      (entry input frame visit.current) (answerFace input frame visit) where
  projection := installed.consumerProjection
  active := installed.consumerActive visit.current safe
  classifier_eq := installed.consumerClassify visit.current safe
  project_heq := (installed.consumerRead visit.current safe).trans
    (consumerToken_heq (entry input frame visit.current) PUnit.unit
      (ULift.up.{1, 0} (frame.root.emitted visit.current)) _ _
      (frame.observation_heq visit.current).symm)

def baseInstalled (start : Cursor.State input) (positive : 0 < Cursor.physicalVisitIndex input start) :
    Installed input (AccountSource.nativeFrame input start positive) where
  U7 := AccountSource.inquiryU7 input start
  calculus := AccountSource.inquiryCalculus input start
  compilationProjection := .compilation
  compilationActive := fun _ => ()
  compilationClassify := fun _ => rfl
  compilationRead := fun _ => HEq.rfl
  consumerProjection := .consumer
  consumerActive := fun current safe => ⟨by
    intro issue
    unfold AccountSource.IsIssue at issue
    cases selected : Cursor.action input current.cursor with
    | issue claim => exact safe claim selected
    | movement _ _ | retain => simp only [selected] at issue⟩
  consumerClassify := by
    intro current safe
    change AccountSource.classify input start positive .consumer _ = _
    unfold AccountSource.classify
    split_ifs with issue
    · unfold AccountSource.IsIssue at issue
      cases selected : Cursor.action input current.cursor with
      | issue claim => exact (safe claim selected).elim
      | movement _ _ | retain => simp only [selected] at issue
    · rfl
  consumerRead := fun _ _ => HEq.rfl

def childInstalled (frame : NativeFrame input) {origin : frame.V.Current}
    (registered : Registration input frame origin) :
    Installed input (Admission.nativeFrame input frame registered) where
  U7 := Admission.inquiryU7 input frame registered
  calculus := Admission.inquiryCalculus input frame registered
  compilationProjection := .inr .compilation
  compilationActive := fun _ => ()
  compilationClassify := fun _ => rfl
  compilationRead := fun _ => HEq.rfl
  consumerProjection := .inr .consumer
  consumerActive := fun current safe => ⟨by
    intro issue
    unfold Admission.IsIssue at issue
    cases selected : Cursor.action input (frame.cursor current.1) with
    | issue claim => exact safe claim selected
    | movement _ _ | retain => simp only [selected] at issue⟩
  consumerClassify := by
    intro current safe
    change Admission.classify input frame registered (.inr .consumer) _ = _
    unfold Admission.classify
    split_ifs with issue
    · unfold Admission.IsIssue at issue
      cases selected : Cursor.action input (frame.cursor current.1) with
      | issue claim => exact (safe claim selected).elim
      | movement _ _ | retain => simp only [selected] at issue
    · rfl
  consumerRead := fun _ _ => HEq.rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime

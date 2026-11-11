import H0mework.Foundation.Inquiry.Engine
import H0mework.Checks.Runtime.U7Ledger
import H0mework.Arithmetic.PrimeShadow.LivingLawRootEffectDynamicalClosureRegression
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.LivingLawObstructionLineageEvolutionRegression

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootInquiryCompletionRegression

open RootInquiryCompletion

namespace Base

open OperationalU7RootLedgerRegression

abbrev N := OperationalU7RootLedgerRegression.N
abbrev V := OperationalU7RootLedgerRegression.V
abbrev U7 := OperationalU7RootLedgerRegression.U7
abbrev calculus := OperationalSeparationRegression.u7Calculus

def inventory : LawInventory N where
  Version := Unit
  version := ()
  Law := Unit
  RealizationAt := fun _ => Unit
  RealizationWithoutAt := fun _ _ _ => Unit

def theory : TheoryState N where
  inventory := inventory
  ExpressionAt := fun _ => Unit
  denotes := fun _ => ()
  TheoremAt := fun _ => Unit
  theoremPresentation := fun _ => ConstructivePresentation.refl Unit

def obstruction : N.ObstructionAt true := ()

def inquiryAudit :
    SourceNativeInquiryFrontAuditAt U7 calculus theory true :=
  .answered

def entry : OpenResponsibilityAt N true := ⟨(), ()⟩

inductive Projection
  | inquiry
  | answer
  | consumer

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
          (audit := inquiryAudit) PUnit
    | .answer => PUnit
    | .consumer => SourceNativeInquiryAnswerConsumerTokenAt
        () (ULift.up.{1, 0} occurrence) entry PUnit.unit
  project := fun projection {_} _occurrence _ => by
    cases projection with
    | inquiry => exact .canonical PUnit.unit
    | answer => exact PUnit.unit
    | consumer => exact .canonical

def authoritySource : SourceNativeAuthoritySource N V where
  restructuringSource := OperationalU7RootLedgerRegression.restructuringSource
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal
      OperationalU7RootLedgerRegression.restructuringSource
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := theory
  projectionLaw := projectionLaw

def operationalLaw : SourceNativeOperationalSearchLaw
    authoritySource.restructuringSource.toLedgerSource :=
  OperationalU7RootLedgerRegression.operationalLaw

def root : SourceNativeLivingRootClosure N V where
  source :=
    { base := authoritySource.withOperationalSearch operationalLaw
      terminalHandoff :=
        (authoritySource.withOperationalSearch operationalLaw)
          |>.emptyFaithfulTerminalHandoff
            (fun _ => ⟨fun terminal => nomatch terminal⟩) }
  emitted := OperationalU7RootLedgerRegression.emitted
  compiler_commutes := fun _ => rfl

def recognition : SourceNativeOperationalSearchRecognitionAt root where
  operationalLaw := operationalLaw
  installation := SourceNativeProjectionLaw.InstallationAt.operationalComponent
    authoritySource operationalLaw

def operationalObstructionAt
    (visit : RootVisit root.toAuthoritativeRoot.toRoot) :
    SourceNativeOperationalObstructionAt recognition.operationalLaw
      (root.emitted visit.current) := by
  match outcome_eq : recognition.generatedTemporalOutcomeAt (.finite visit) with
  | .inl _ => cases outcome_eq
  | .inr (.inl obstruction) => exact obstruction
  | .inr (.inr _) => cases outcome_eq

theorem entry_eq (candidate : OpenResponsibilityAt N true) :
    entry = candidate := by
  rcases candidate with ⟨responsibility, openReceipt⟩
  cases responsibility
  cases openReceipt
  rfl

def initialAuthority :
    SourceNativeLivingTemporalCausalEntryAuthorityAt root
      (.finite root.toAuthoritativeRoot.toRoot.initialVisit) entry :=
  ((SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial?
    root entry .initial).get (by rfl)).2

def authorityAtHistory :
    {current : V.Current} ->
    (history : root.toAuthoritativeRoot.toRoot.ReachableAt current) ->
    SourceNativeLivingTemporalCausalEntryAuthorityAt root
      (.finite ⟨current, history⟩) entry
  | _, .initial => initialAuthority
  | _, .step prior next_eq => by
      let priorAuthority := authorityAtHistory prior
      let nextAuthority := priorAuthority.next next_eq
      exact entry_eq _ ▸ nextAuthority

def authorityAtVisit (visit : RootVisit root.toAuthoritativeRoot.toRoot) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt root (.finite visit) entry :=
  authorityAtHistory visit.history

def answerFaceAt (visit : RootVisit root.toAuthoritativeRoot.toRoot) :
    SourceNativeRootSemanticFaceAt root (.finite visit) where
  projection := SourceNativeOperationalProjection.inherited .answer
  active := PUnit.unit
  classifier_eq := rfl

def answerConsumerAt (visit : RootVisit root.toAuthoritativeRoot.toRoot) :
    SourceNativeInquiryAnswerConsumerAt
      () (ULift.up.{1, 0} (root.emitted visit.current)) entry
        (answerFaceAt visit) where
  projection := SourceNativeOperationalProjection.inherited .consumer
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def inquiryCompilationAt (visit : RootVisit root.toAuthoritativeRoot.toRoot) :
    SourceNativeInquiryCompilationAt root (.finite visit) U7 calculus theory
      () (ULift.up.{1, 0} (root.emitted visit.current)) entry
        (authorityAtVisit visit) :=
  .answered (answerFaceAt visit) (answerConsumerAt visit)

def baseStateAt (visit : RootVisit root.toAuthoritativeRoot.toRoot) :
    RootInquiryStateAt N V where
  root := root
  visit := .finite visit
  U7 := U7
  calculus := calculus
  Query := Unit
  entryAt := fun _ => entry
  authorityAt := fun _ => authorityAtVisit visit
  compilationProgramAt := fun _ =>
    { compile := fun _exactOccurrence => inquiryCompilationAt visit }
  compilationFaceAt := fun _ =>
    { projection := SourceNativeOperationalProjection.inherited .inquiry
      active := PUnit.unit
      classifier_eq := rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _query _obstruction _audit audit_eq
    cases audit_eq

def inquiryFaceAt (visit : RootVisit root.toAuthoritativeRoot.toRoot) :
    SourceNativeRootInquiryCompilationFaceAt (baseStateAt visit) () :=
  (baseStateAt visit).compilationFaceAt ()

/-- The authority state has no caller-owned event argument left. -/
def caller_event_cannot_select_inquiry_compiler : PUnit := by
  fail_if_success
    let _ := (baseStateAt root.toAuthoritativeRoot.toRoot.initialVisit
      ).compileInquiry () (ULift.up.{1, 0} ())
  exact PUnit.unit

def inquiryInstallation : SourceNativeProjectionLaw.InstallationAt
    projectionLaw root.toAuthoritativeRoot.source.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedByOperational
    authoritySource operationalLaw

theorem operationalEntry_eq_queryEntry
    (visit : RootVisit root.toAuthoritativeRoot.toRoot) :
    (operationalObstructionAt visit).rootDemandEntry = entry :=
  (entry_eq _).symm

set_option linter.defProp false in
def operational_and_inquiry_are_same_root_faces
    (visit : RootVisit root.toAuthoritativeRoot.toRoot) :=
  (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (.finite visit)).installedJointFaceReadout_heq_componentOutcomes
      recognition.installation inquiryInstallation
      PUnit.unit .inquiry

theorem operationalOutcomeAt_eq
    (visit : RootVisit root.toAuthoritativeRoot.toRoot) :
    recognition.generatedTemporalOutcomeAt (.finite visit) =
      .inr (.inl (operationalObstructionAt visit)) :=
  (operationalObstructionAt visit).rootOutcome_eq

def engineStateAt (visit : RootVisit root.toAuthoritativeRoot.toRoot) :
    RootInquiryEngineStateAt N V :=
  RootInquiryEngineStateAt.create (baseStateAt visit)

def presentationAt (visit : RootVisit root.toAuthoritativeRoot.toRoot) :
    RootInquiryStatePresentation where
  N := N
  V := V
  state := engineStateAt visit

end Base

open Base

def process : SourceNativeInquiryEngineProcess.{0} where
  State := RootVisit root.toAuthoritativeRoot.toRoot
  stateAt := fun visit => .active (presentationAt visit)
  erase_injective := by
    intro left right leftState rightState leftActive rightActive equality
    cases leftActive
    cases rightActive
    injection equality with _ currentEq
    change
      ((⟨V, root.toAuthoritativeRoot,
          SourceNativeTemporalVisitAt.finite left⟩ :
        SourceNativeAuthoritativeRootCurrentAt N) =
       (⟨V, root.toAuthoritativeRoot,
          SourceNativeTemporalVisitAt.finite right⟩ :
        SourceNativeAuthoritativeRootCurrentAt N)) at currentEq
    injection currentEq with _ _ visitHEq
    have visitEq : SourceNativeTemporalVisitAt.finite left =
        SourceNativeTemporalVisitAt.finite right := visitHEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := root.toAuthoritativeRoot.toRoot.initialVisit
  successorAt := by
    intro visit query
    change Unit at query
    cases query
    let nextVisit := visit.next (by rfl)
    refine ⟨nextVisit, ?_⟩
    exact ⟨rfl, HEq.rfl⟩

def engine : Engine process := Engine.initial process

def query : engine.Query := by
  change Unit
  exact ()

def activation : Engine.SourceNativeInquiryActivationAt engine :=
  engine.uniqueInquiryActivation query (by
    intro candidate
    change Unit at candidate
    cases candidate
    rfl)

def firstOccurrence : Engine.ExactRootInquiryOccurrenceAt engine query :=
  engine.ask activation

/-- A raw query value no longer enters the exact-occurrence authority mouth. -/
def raw_query_cannot_activate_inquiry : PUnit := by
  fail_if_success
    let _ := engine.ask query
  exact PUnit.unit

/-- The public answer is a restriction of the exact inquiry occurrence. -/
def firstPublicAnswer : PUnit := firstOccurrence.answer

set_option linter.defProp false in
def firstCompilationFactorization :=
  (engineStateAt root.toAuthoritativeRoot.toRoot.initialVisit
    ).generatedCompilation_factorizes ()

theorem first_query_is_exact_operational_answer :
    let initialVisit := root.toAuthoritativeRoot.toRoot.initialVisit
    (Base.baseStateAt initialVisit).compileInquiry () =
        .answered (Base.answerFaceAt initialVisit)
          (Base.answerConsumerAt initialVisit) ∧
      (Base.baseStateAt initialVisit).entryAt () =
        (Base.operationalObstructionAt initialVisit).rootDemandEntry := by
  dsimp only
  exact ⟨rfl,
    (Base.operationalEntry_eq_queryEntry _).symm⟩

set_option linter.defProp false in
def firstOperationalInquiryJointFace :=
  Base.operational_and_inquiry_are_same_root_faces
    root.toAuthoritativeRoot.toRoot.initialVisit

/-- The raw operational redirect has no theory-audit gate.  The inquiry
answer is read directly from the exact root occurrence; a neutral redirect
does not obtain answer authority. -/
theorem raw_redirect_cannot_open_u8 :
    IsEmpty ((Base.baseStateAt
      Base.root.toAuthoritativeRoot.toRoot.initialVisit)
        |>.U7RequestsTheoryAuditAt Base.obstruction) := by
  constructor
  intro gate
  exact nomatch gate

/-- A source-owned redirect that merely preserves the exact demand entry has
no inquiry-answer authority.  The raw U7 evolution remains available as a
model, but `0 < 0` cannot be minted by its transfer receipt. -/
theorem neutral_redirect_cannot_answer :
    IsEmpty (SourceNativeU7AnswersAt Base.calculus Base.obstruction) := by
  constructor
  intro answer
  exact (Nat.lt_irrefl _) answer.down.down

theorem first_answer_is_direct_root_generated :
    firstOccurrence.resolution =
      InternalInquiryResolutionAt.directlyAnswered
        (state := presentationAt process.initial)
        (Base.answerFaceAt process.initial)
        (Base.answerConsumerAt process.initial) :=
  rfl

set_option linter.defProp false in
def firstNextIsExactRootSuccessor :=
  firstOccurrence.next_erases_to_generated

/-- A continuing inquiry step retains the complete living root, including its
terminal-handoff law; equality of the authoritative erasure alone no longer
pays this transition. -/
theorem first_next_preserves_complete_living_root :
    HEq
      (presentationAt (process.initial.next rfl)).state.base.root
      (presentationAt process.initial).state.base.root :=
  firstOccurrence.next_preservesGeneratedLivingLaw


namespace Effect

open RootEffectDynamicalClosureRegression

def effectLaw : SourceNativeEffectDynamicalClosureLaw
    Base.authoritySource.restructuringSource.toLedgerSource :=
  cutLaw

def root : SourceNativeLivingRootClosure Base.N Base.V where
  source :=
    { base := effectLaw.toAuthoritySource Base.authoritySource
      terminalHandoff :=
        (effectLaw.toAuthoritySource Base.authoritySource)
          |>.emptyFaithfulTerminalHandoff
            (fun _ => ⟨fun terminal => nomatch terminal⟩) }
  emitted := OperationalU7RootLedgerRegression.emitted
  compiler_commutes := fun _ => rfl

def recognition : SourceNativeEffectDynamicalRecognitionAt root where
  effectLaw := effectLaw
  installation :=
    SourceNativeProjectionLaw.InstallationAt.effectDynamicalComponent
      Base.authoritySource effectLaw

def entry : OpenResponsibilityAt Base.N true :=
  OperationalU7RootLedgerRegression.rootEntry

theorem entry_eq (candidate : OpenResponsibilityAt Base.N true) :
    entry = candidate :=
  OperationalU7RootLedgerRegression.rootEntry_eq candidate

def initialAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt root
    (.finite root.toAuthoritativeRoot.toRoot.initialVisit) entry :=
  ((SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial?
    root entry .initial).get (by rfl)).2

def authorityAtHistory :
    {current : Base.V.Current} ->
    (history : root.toAuthoritativeRoot.toRoot.ReachableAt current) ->
    SourceNativeLivingTemporalCausalEntryAuthorityAt root
      (.finite ⟨current, history⟩) entry
  | _, .initial => initialAuthority
  | _, .step prior next_eq => by
      let priorAuthority := authorityAtHistory prior
      let nextAuthority := priorAuthority.next next_eq
      exact entry_eq _ ▸ nextAuthority

def authorityAtVisit (visit : RootVisit root.toAuthoritativeRoot.toRoot) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt root (.finite visit) entry :=
  authorityAtHistory visit.history

def rootedActiveAt (visit : RootVisit root.toAuthoritativeRoot.toRoot) :
    recognition.RootedActiveOutcomeAt (.finite visit) :=
  recognition.generatedRootedActiveAtVisit (.finite visit) () rfl
    (authorityAtVisit visit)

def cutClosureAt (visit : RootVisit root.toAuthoritativeRoot.toRoot) :
    (rootedActiveAt visit).CausalCutClosureAt := by
  change (rootedActiveAt visit).CausalClosureAt
  exact (rootedActiveAt visit).generatedCausalClosure

def inquiryInstallation : SourceNativeProjectionLaw.InstallationAt
    Base.projectionLaw root.toAuthoritativeRoot.source.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedByEffectDynamical
    Base.authoritySource effectLaw

set_option linter.defProp false in
def effect_and_inquiry_are_same_root_faces
    (visit : RootVisit root.toAuthoritativeRoot.toRoot) :=
  (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (.finite visit)).installedJointFaceReadout_heq_componentOutcomes
      recognition.installation inquiryInstallation
      PUnit.unit .inquiry

def stateAt (visit : RootVisit root.toAuthoritativeRoot.toRoot) :
    RootInquiryStateAt Base.N Base.V where
  root := root
  visit := .finite visit
  U7 := Base.U7
  calculus := Base.calculus
  Query := Unit
  entryAt := fun _ => entry
  authorityAt := fun _ => authorityAtVisit visit
  compilationProgramAt := fun _ =>
    { compile := fun _exactOccurrence =>
        .answered
          { projection := SourceNativeEffectDynamicalProjection.inherited .answer
            active := PUnit.unit
            classifier_eq := rfl }
          { projection := SourceNativeEffectDynamicalProjection.inherited .consumer
            active := PUnit.unit
            classifier_eq := rfl
            project_heq := HEq.rfl } }
  compilationFaceAt := fun _ =>
    { projection := SourceNativeEffectDynamicalProjection.inherited .inquiry
      active := PUnit.unit
      classifier_eq := rfl
      project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _query _obstruction _audit audit_eq
    cases audit_eq

def inquiryFaceAt (visit : RootVisit root.toAuthoritativeRoot.toRoot) :
    SourceNativeRootInquiryCompilationFaceAt (stateAt visit) () :=
  (stateAt visit).compilationFaceAt ()

def engineStateAt (visit : RootVisit root.toAuthoritativeRoot.toRoot) :
    RootInquiryEngineStateAt Base.N Base.V :=
  RootInquiryEngineStateAt.create (stateAt visit)

def presentationAt (visit : RootVisit root.toAuthoritativeRoot.toRoot) :
    RootInquiryStatePresentation where
  N := Base.N
  V := Base.V
  state := engineStateAt visit

def process : SourceNativeInquiryEngineProcess.{0} where
  State := RootVisit root.toAuthoritativeRoot.toRoot
  stateAt := fun visit => .active (presentationAt visit)
  erase_injective := by
    intro left right leftState rightState leftActive rightActive equality
    cases leftActive
    cases rightActive
    injection equality with _ currentEq
    change
      ((⟨Base.V, root.toAuthoritativeRoot,
          SourceNativeTemporalVisitAt.finite left⟩ :
        SourceNativeAuthoritativeRootCurrentAt Base.N) =
       (⟨Base.V, root.toAuthoritativeRoot,
          SourceNativeTemporalVisitAt.finite right⟩ :
        SourceNativeAuthoritativeRootCurrentAt Base.N)) at currentEq
    injection currentEq with _ _ visitHEq
    have visitEq : SourceNativeTemporalVisitAt.finite left =
        SourceNativeTemporalVisitAt.finite right := visitHEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := root.toAuthoritativeRoot.toRoot.initialVisit
  successorAt := by
    intro visit query
    change Unit at query
    cases query
    let nextVisit := visit.next (by rfl)
    refine ⟨nextVisit, ?_⟩
    exact ⟨rfl, HEq.rfl⟩

def engine : Engine process := Engine.initial process

def query : engine.Query := ()

def activation : Engine.SourceNativeInquiryActivationAt engine :=
  engine.uniqueInquiryActivation query (by
    intro candidate
    change Unit at candidate
    cases candidate
    rfl)

def firstOccurrence : Engine.ExactRootInquiryOccurrenceAt engine query :=
  engine.ask activation

def firstPublicAnswer : PUnit := firstOccurrence.answer

theorem first_answer_is_effect_cut_directly_generated :
    firstOccurrence.resolution =
      InternalInquiryResolutionAt.directlyAnswered
        (state := presentationAt process.initial)
        { projection := SourceNativeEffectDynamicalProjection.inherited .answer
          active := PUnit.unit
          classifier_eq := rfl }
        { projection := SourceNativeEffectDynamicalProjection.inherited .consumer
          active := PUnit.unit
          classifier_eq := rfl
          project_heq := HEq.rfl } :=
  rfl

set_option linter.defProp false in
def firstNextIsExactRootSuccessor :=
  firstOccurrence.next_erases_to_generated

theorem first_effect_next_preserves_complete_living_root :
    HEq
      (presentationAt (process.initial.next rfl)).state.base.root
      (presentationAt process.initial).state.base.root :=
  firstOccurrence.next_preservesGeneratedLivingLaw

set_option linter.defProp false in
def firstEffectInquiryJointFace :=
  effect_and_inquiry_are_same_root_faces
    root.toAuthoritativeRoot.toRoot.initialVisit

end Effect

#print axioms RootInquiryStateAt.u7Disposition_heq_root
#print axioms RootInquiryStateAt.emitInquiry_eq_rootOccurrence
#print axioms Engine.uniqueInquiryActivation_query
#print axioms OperationalU7RootLedgerRegression.settled_u7_cannot_share_continuing_root_row
#print axioms neutral_redirect_cannot_answer

end RootInquiryCompletionRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

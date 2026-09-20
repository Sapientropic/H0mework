import H0mework.Foundation.Ledger.ProofRelevantRestructuring
import H0mework.Foundation.Authority.CausalEntry
import H0mework.Foundation.Authority.EntryDisposition
import H0mework.Foundation.Inquiry.MinimalCoface
import H0mework.Foundation.Inquiry.Protocol
import H0mework.Foundation.Semantics.TheoryEvolution
import H0mework.Arithmetic.FockResponsibility.DebtU7AuditSource

/-!
# Target living root for the occurrence-debt U7 row

The failure-indexed audit source is upgraded without changing its event,
whole-ledger compiler or emitted occurrence.  Its projection payload reads the
actual recurrence residual carried by the parent-linked debt U7 admission.
The exact debt row in the source-generated initial patch then yields living
causal authority through the existing `generatedFromInitialRow` constructor.

No terminal, U8 revision, residual classifier or caller row is accepted.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFockOccurrenceDebtU7LivingRoot

open ObstructionGeneratedMinimalCoface
open CanonicalUnitArithmeticGlobalGoldbachDisposition
open CanonicalUnitArithmeticOperationalFirstResidualProducer
open ParticleWaveFockOccurrenceDebtU7Admission
open ParticleWaveFockOccurrenceDebtU7AuditSource
open ParticleWaveFockOccurrenceResponsibility
open ParticleWaveFockOperationalProvenanceRecurrence
open RootInquiryCompletion
open RootGeneratedProofRelevantRestructuring

noncomputable section

def restructuringLaw (failure : FirstResidualOccurrence) :
    SourceNativeLedgerRestructuringLaw (source failure) :=
  RootGeneratedProofRelevantRestructuring.law
    (DebtN failure) (activeSupport failure) (source failure)

def restructuringCertification
    (failure : FirstResidualOccurrence)
    {current : (AuditV failure).Current}
    (occurrence : (source failure).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt
      (restructuringLaw failure)
      ((ledgerCompiler failure).compile occurrence) := by
  cases current
  rcases occurrence with ⟨support, event⟩
  cases event
  exact ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right equality =>
      (generatedPatch_origin_eq failure left).symm.trans
        (equality.trans (generatedPatch_origin_eq failure right)))
    (fun left right equality =>
      (generatedPatch_destination_eq failure left).symm.trans
        (equality.trans (generatedPatch_destination_eq failure right)))

def restructuringCompiler (failure : FirstResidualOccurrence) :
    SourceNativeRestructuringLedgerCompiler (source failure) where
  ledgerCompiler := ledgerCompiler failure
  restructuringLaw := restructuringLaw failure
  certifyRestructuring := restructuringCertification failure

def restructuringSource (failure : FirstResidualOccurrence) :
    SourceNativeRestructuringLedgerSource (DebtN failure) (AuditV failure) where
  source := source failure
  compiler := restructuringCompiler failure

/-- Low-universe dependent face of the exact U7 occurrence.  The failure index
fixes the high-universe admission, while this payload retains the actual
recurrence residual, including its effect and generated target. -/
structure AuditPayloadAt (failure : FirstResidualOccurrence) : Type where
  recurrence : ProjectionRecurrenceResidualAt
    (returnedHistoryState failure)
  recurrence_eq : recurrence = projectionRecurrenceResidual failure

def auditPayload (failure : FirstResidualOccurrence) :
    AuditPayloadAt failure where
  recurrence := projectionRecurrenceResidual failure
  recurrence_eq := rfl

theorem recurrenceU7Answers_isEmpty (failure : FirstResidualOccurrence) :
    IsEmpty (SourceNativeU7AnswersAt (debtU7Calculus failure)
      (recurrenceObstruction failure)) := by
  constructor
  intro answer
  unfold SourceNativeU7AnswersAt at answer
  dsimp only [U7ObstructionEvolutionCalculus.generated] at answer
  have disposition := recurrenceU7Event_disposition failure
  unfold recurrenceU7Event at disposition
  rw [disposition] at answer
  exact nomatch answer

/-- An inherited claim remains addressable.  Any expression of the live debt
claim must instead carry the exact U7 answer type generated at this
obstruction; that fibre is empty for a theory-audit disposition. -/
def OperationalClaimWitnessAt (failure : FirstResidualOccurrence) :
    (DebtN failure).Claim → Type
  | .inl _ => PUnit
  | .inr _ => SourceNativeU7AnswersAt (debtU7Calculus failure)
      (recurrenceObstruction failure)

abbrev OperationalExpressionAt
    (failure : FirstResidualOccurrence) (_support : (DebtN failure).Support) :=
  Sigma (OperationalClaimWitnessAt failure)

def operationalTheory (failure : FirstResidualOccurrence) :
    TheoryState (DebtN failure) where
  inventory :=
    { Version := PUnit
      version := PUnit.unit
      Law := PEmpty
      RealizationAt := fun {_support} obstruction =>
        SourceNativeU7AnswersAt (debtU7Calculus failure) obstruction
      RealizationWithoutAt := fun law => nomatch law }
  ExpressionAt := OperationalExpressionAt failure
  denotes := Sigma.fst
  TheoremAt := fun {support} expression =>
    (DebtN failure).HoldsAt support expression.1
  theoremPresentation := fun _ => ConstructivePresentation.refl _

def operationalTheory_rootSemantic
    (failure : FirstResidualOccurrence) :
    ConservativeTheoryTranslation (operationalTheory failure)
      (TheoryState.rootSemantic (DebtN failure)) where
  compile := fun expression => expression.1
  commuting := fun _expression => rfl

def recurrenceOperationalFailure
    (failure : FirstResidualOccurrence) :
    ActualExpressibilityFailure (operationalTheory failure)
      (recurrenceObstruction failure) where
  notExpressible := by
    constructor
    rintro ⟨⟨claim, witness⟩, denotes_eq⟩
    cases claim with
    | inl oldClaim => cases denotes_eq
    | inr debtClaim =>
        exact (recurrenceU7Answers_isEmpty failure).false witness
  noLawfulRealization := recurrenceU7Answers_isEmpty failure

inductive AuditProjection
  | recurrenceEffect
  | expressibilityFailure
  | inquiryCompilation

def recurrenceInquiryAudit (failure : FirstResidualOccurrence) :
    SourceNativeInquiryFrontAuditAt (debtU7 failure) (debtU7Calculus failure)
      (operationalTheory failure) (activeSupport failure) :=
  .obstructed (recurrenceObstruction failure)
    (.requiresU8 (recurrenceU7TheoryAudit failure)
      (recurrenceOperationalFailure failure))

/-- The installed inventory exposes three sibling coordinates of the same root
occurrence: its actual recurrence/effect and the exact operational failure
generated from that residual, plus the exact inquiry compiler readout. -/
def projectionLaw (failure : FirstResidualOccurrence) :
    SourceNativeProjectionLaw (restructuringSource failure).toLedgerSource where
  Projection := AuditProjection
  ActiveAt := fun _ {_current} _occurrence => PUnit
  InactiveAt := fun _ {_current} _occurrence => PEmpty
  classify := fun _ {_current} _occurrence => .inl PUnit.unit
  PayloadAt := fun projection {_current} occurrence _active =>
    match projection with
    | .recurrenceEffect => AuditPayloadAt failure
    | .expressibilityFailure =>
        SourceNativeRootExpressibilityFailureTokenAt
          (recurrenceOperationalFailure failure)
          (debtU7Calculus failure) (recurrenceU7Event failure)
    | .inquiryCompilation =>
        SourceNativeInquiryCompilationTokenAt
          (recurrenceDebtEntry failure) PUnit.unit
          (ULift.up.{1, 0} occurrence)
          (recurrenceInquiryAudit failure) PUnit
  project := fun projection {_current} _occurrence _active =>
    match projection with
    | .recurrenceEffect => auditPayload failure
    | .expressibilityFailure =>
        SourceNativeRootExpressibilityFailureTokenAt.canonical
    | .inquiryCompilation =>
        SourceNativeInquiryCompilationTokenAt.canonical PUnit.unit

def authoritySource (failure : FirstResidualOccurrence) :
    SourceNativeAuthoritySource (DebtN failure) (AuditV failure) where
  restructuringSource := restructuringSource failure
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal (restructuringSource failure)
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := operationalTheory failure
  projectionLaw := projectionLaw failure

def authoritativeRoot (failure : FirstResidualOccurrence) :
    SourceNativeAuthoritativeRootClosure (DebtN failure) (AuditV failure) where
  source := authoritySource failure
  emitted := emitted failure
  compiler_commutes := (ledgerRoot failure).compiler_commutes

/-- Canonical read of the occurrence-owned recurrence through the installed
root projection, not through a sibling domain package. -/
def rootAuditPayload (failure : FirstResidualOccurrence) :
    AuditPayloadAt failure :=
  (authoritativeRoot failure).source.projectionLaw.project
    .recurrenceEffect ((authoritativeRoot failure).emitted PUnit.unit)
      PUnit.unit

@[simp] theorem rootAuditPayload_recurrence_eq
    (failure : FirstResidualOccurrence) :
    (rootAuditPayload failure).recurrence =
      projectionRecurrenceResidual failure :=
  rfl

def rootFailureToken (failure : FirstResidualOccurrence) :
    SourceNativeRootExpressibilityFailureTokenAt
      (recurrenceOperationalFailure failure)
      (debtU7Calculus failure) (recurrenceU7Event failure) :=
  (authoritativeRoot failure).source.projectionLaw.project
    .expressibilityFailure ((authoritativeRoot failure).emitted PUnit.unit)
      PUnit.unit

def livingRoot (failure : FirstResidualOccurrence) :
    SourceNativeLivingRootClosure (DebtN failure) (AuditV failure) :=
  (authoritativeRoot failure).toLivingWithoutFaithfulTerminal
    (fun _ => ⟨fun terminal => nomatch terminal⟩)

def initialVisit (failure : FirstResidualOccurrence) :
    SourceNativeTemporalVisitAt
      (authoritativeRoot failure).toLedgerRoot :=
  .finite (authoritativeRoot failure).toRoot.initialVisit

def initialGenerated (failure : FirstResidualOccurrence) :=
  (authoritativeRoot failure).toLedgerRoot.generatedAtTemporalVisit
    (initialVisit failure)

def initialDebtRow (failure : FirstResidualOccurrence) :
    (initialGenerated failure).GeneratedEntryRowAt
      (recurrenceDebtEntry failure) :=
  ((initialGenerated failure).canonicalGeneratedEntryRow?
    (recurrenceDebtEntry failure)).get (by rfl)

def authoritativeDebtCausalAuthority
    (failure : FirstResidualOccurrence) :
    SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt
      (authoritativeRoot failure) (initialVisit failure)
      (recurrenceDebtEntry failure) :=
  SourceNativeAuthoritativeTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    (authoritativeRoot failure) (recurrenceDebtEntry failure)
      (initialDebtRow failure)

def livingDebtCausalAuthority
    (failure : FirstResidualOccurrence) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (livingRoot failure) (initialVisit failure)
      (recurrenceDebtEntry failure) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    (livingRoot failure) (recurrenceDebtEntry failure)
      (initialDebtRow failure)

def debtAnswerAndNext (failure : FirstResidualOccurrence) :
    SourceNativeLivingCausalEntryAnswerAndNextAt
      (livingRoot failure) (initialVisit failure)
      (recurrenceDebtEntry failure) (livingDebtCausalAuthority failure) :=
  (livingRoot failure).generatedCausalEntryAnswerAndNextAt
    (initialVisit failure) (recurrenceDebtEntry failure)
      (livingDebtCausalAuthority failure)

def debtSuccessor (failure : FirstResidualOccurrence) :
    CausalEntrySuccessorAt (authoritativeRoot failure).toLedgerRoot
      (initialVisit failure) (recurrenceDebtEntry failure) :=
  CausalEntrySuccessorAt.ofNonterminal rfl

theorem rootDispositionCommutes (failure : FirstResidualOccurrence) :
    U7DemandEntryRootDispositionCommutesAt
      (debtU7Calculus failure) (recurrenceU7Event failure)
      (recurrenceDebtEntry failure)
      ((initialGenerated failure).wholeLedgerWriteBack.entryDisposition
        (recurrenceDebtEntry failure)) := by
  constructor
  · exact heq_of_eq (recurrenceU7Event_entry failure).symm
  · exact HEq.rfl

def recurrenceFailureFace (failure : FirstResidualOccurrence) :
    SourceNativeRootExpressibilityFailureFaceAt
      (authoritativeRoot failure) (initialVisit failure)
      (U7 := debtU7 failure) (recurrenceOperationalFailure failure) where
  lawSurface_eq := rfl
  projection := .expressibilityFailure
  active := PUnit.unit
  classifier_eq := rfl
  calculus := debtU7Calculus failure
  u7Event := recurrenceU7Event failure
  u7Event_eq_emit := rfl
  theoryAudit := recurrenceU7TheoryAudit failure
  support_eq := rfl
  rootEntry := recurrenceDebtEntry failure
  rootEntryAtFailure_eq := (recurrenceU7Event_entry failure).symm
  rootDispositionCommutes := rootDispositionCommutes failure
  project_heq := HEq.rfl

def rootedRecurrenceFailure (failure : FirstResidualOccurrence) :
    RootedActualExpressibilityFailureAt
      (authoritativeRoot failure) (initialVisit failure)
      (debtU7 failure) (recurrenceOperationalFailure failure) :=
  RootedActualExpressibilityFailureAt.ofRootFailureFace
    (recurrenceFailureFace failure)
    (authoritativeDebtCausalAuthority failure) (debtSuccessor failure)

def recurrenceMinimalCoface (failure : FirstResidualOccurrence) :
    GeneratedMinimalCofaceAt (rootedRecurrenceFailure failure) :=
  root_obstruction_generates_minimal_coface
    (rootedRecurrenceFailure failure)

theorem targetRoot_reuses_generated_source
    (failure : FirstResidualOccurrence) :
    (authoritativeRoot failure).toLedgerRoot.source = ledgerSource failure ∧
      (authoritativeRoot failure).emitted = emitted failure :=
  ⟨rfl, rfl⟩

end

end ParticleWaveFockOccurrenceDebtU7LivingRoot
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

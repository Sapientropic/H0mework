import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Observer.SourceGeneratedContributionCapacityFinitePrefixAuthorityObserver
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Universal.Producer.SourceGeneratedUniversalSocietyRootGrammar

/-!
# Installed-trace-generated finite-prefix representation

At boundary `n`, the already existing post-settlement Society trace at the
literal prefix occurrence supplies the exact actual-ledger point from which a
downstream deterministic compiler generates the prefix readout.  Its language is
the ordinary function space from the finite visible carrier to actual
authority; this syntax is inhabited and exactly represents every replay
already inside the prefix.

No later replay, kernel pair, failure, U7 branch, target or future table is
stored in this source face.  A later file asks whether this positive prefix
representation extends to the open paid tail.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceInstalledContributionCapacityFinitePrefixRepresentation

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer UniversalRootGrammar
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityJointSettlementConsumer
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementPaidReplay
open M14SourceGeneratedContributionCapacityFinitePrefixAuthorityObserver
open M14SourceGeneratedPostSettlementSocietyFaceTrace
open M14SourceGeneratedUniversalSocietyRootGrammar

abbrev PrefixRootAt (oldVisit : OldVisit) (sourceIndex : Nat) :=
  UniversalSocietyRootAt oldVisit sourceIndex

def prefixVisitAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeTemporalVisitAt
      (PrefixRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot :=
  contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
    boundary

@[simp] theorem prefixVisit_current_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (show Nat from (prefixVisitAt oldVisit sourceIndex boundary).current) =
      contributionCapacityPostSettlementRenewalInitialCurrentAt sourceIndex +
        boundary := by
  unfold prefixVisitAt
  exact contributionCapacityPostSettlementRenewalVisit_current_exact oldVisit
    sourceIndex boundary

def prefixOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  contributionCapacityPostSettlementRenewalEmitted oldVisit sourceIndex
    (prefixVisitAt oldVisit sourceIndex boundary).current

def prefixInstalledTraceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (universalSocietyRecognitionAt oldVisit sourceIndex).installedPayloadAt
    (prefixVisitAt oldVisit sourceIndex boundary)

/-- The finite syntax retains one source-installed Society grammar coordinate
beside the boundary-visible replay slot. -/
abbrev FinitePrefixInstalledVisibleAt (boundary : Nat) :=
  FinitePrefixReplayVisibleAt boundary × PostSettlementSocietyGrammarIndex

def finitePrefixInstalledAuthorityObserverAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    AuthorityObserver
      (AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex)
      (FinitePrefixInstalledVisibleAt boundary)
      AnyPeriodicActualServiceExit where
  forget := fun replay =>
    ⟨(finitePrefixReplayAuthorityObserverAt oldVisit sourceIndex boundary
      ).forget replay, (.actual, .ledger)⟩
  authorityK := fun replay =>
    (finitePrefixReplayAuthorityObserverAt oldVisit sourceIndex boundary
      ).authorityK replay

/-- Raw operational expressions are ordinary functions, not an empty fibre
and not an `AuthorityFactorization` alias. -/
abbrev FinitePrefixOperationalExpressionAt
    (_oldVisit : OldVisit) (_sourceIndex boundary : Nat) :=
  FinitePrefixInstalledVisibleAt boundary → AnyPeriodicActualServiceExit

/-- A law expression is valid on the already generated prefix only. -/
structure FinitePrefixHistoricalRepresentationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (expression :
      FinitePrefixOperationalExpressionAt oldVisit sourceIndex boundary) :
    Prop where
  preservesPrefix : ∀ replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
    replay.1 ≤ boundary →
      expression
          ((finitePrefixInstalledAuthorityObserverAt oldVisit sourceIndex
            boundary).forget replay) =
        (finitePrefixInstalledAuthorityObserverAt oldVisit sourceIndex
          boundary).authorityK replay

/-- A proposed extension to the whole open paid tail.  Its emptiness is a
later, difference-generated fact rather than the definition of syntax. -/
structure FinitePrefixCompleteRepresentationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (expression :
      FinitePrefixOperationalExpressionAt oldVisit sourceIndex boundary) :
    Prop where
  preservesEveryReplay : ∀ replay :
      AnyContributionCapacityPostSettlementPaidReplay oldVisit sourceIndex,
    expression
        ((finitePrefixInstalledAuthorityObserverAt oldVisit sourceIndex
          boundary).forget replay) =
      (finitePrefixInstalledAuthorityObserverAt oldVisit sourceIndex
        boundary).authorityK replay

def prefixActualLedgerPointAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (universalSocietyRecognitionAt oldVisit sourceIndex).PointAt
      (prefixVisitAt oldVisit sourceIndex boundary) :=
  ((universalSocietyRecognitionAt oldVisit sourceIndex).traceAt
    (prefixVisitAt oldVisit sourceIndex boundary)).root

@[simp] theorem prefixActualLedgerPoint_scenario
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (prefixActualLedgerPointAt oldVisit sourceIndex boundary).scenario =
      PostSettlementSocietyScenario.actual :=
  rfl

@[simp] theorem prefixActualLedgerPoint_face
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (prefixActualLedgerPointAt oldVisit sourceIndex boundary).face =
      PostSettlementSocietyBearingFace.ledger :=
  rfl

theorem prefixActualLedgerPoint_mem
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    prefixActualLedgerPointAt oldVisit sourceIndex boundary ∈
      (prefixInstalledTraceAt oldVisit sourceIndex boundary).trace.trace := by
  exact
    ((universalSocietyRecognitionAt oldVisit sourceIndex).traceAt
      (prefixVisitAt oldVisit sourceIndex boundary)).root_mem_trace

/-- The source compiler reads the installed actual-ledger point.  On that
coordinate it reconstructs the canonical prefix authority; all other trace
coordinates remain ordinary syntax but carry no authority promise. -/
def finitePrefixOperationalExpressionOfPointAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (point : (universalSocietyRecognitionAt oldVisit sourceIndex).PointAt
      (prefixVisitAt oldVisit sourceIndex boundary)) :
    FinitePrefixOperationalExpressionAt oldVisit sourceIndex boundary := by
  classical
  exact fun visible =>
    match point.scenario with
    | .actual =>
        (finitePrefixInstalledAuthorityObserverAt oldVisit sourceIndex boundary
          ).authorityK
          (contributionCapacityPostSettlementPaidReplayAt oldVisit sourceIndex
            visible.1.1.val)
    | .fullCaptureSearch => periodicActualServiceExitOccurrenceAt 0

theorem canonicalPointExpression_preservesPrefix
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FinitePrefixHistoricalRepresentationAt oldVisit sourceIndex boundary
      (finitePrefixOperationalExpressionOfPointAt oldVisit sourceIndex
        boundary
        (prefixActualLedgerPointAt oldVisit sourceIndex boundary)) := by
  constructor
  rintro ⟨index, replay⟩ index_le
  have replay_eq :=
    SourceGeneratedContributionCapacityPostSettlementPaidReplayAt.eq_generated
      replay
  subst replay
  unfold finitePrefixOperationalExpressionOfPointAt
    finitePrefixInstalledAuthorityObserverAt
  rw [prefixActualLedgerPoint_scenario]
  change
    (sourceGeneratedContributionCapacityPostSettlementPaidReplayAt oldVisit
      sourceIndex
      (finitePrefixHistorySlotAt boundary index).val).authorityK =
      (sourceGeneratedContributionCapacityPostSettlementPaidReplayAt oldVisit
        sourceIndex index).authorityK
  rw [finitePrefixHistorySlot_exact_of_le index_le]

/-- Exact installed trace and its unique actual-ledger point determine the
downstream prefix expression.  The receipt proves point provenance and
compiler commuting; it does not claim that the root projection already
contained this later representation type. -/
structure SourceInstalledFinitePrefixRepresentationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type 29 where
  private mk ::
  trace : type_of% (prefixInstalledTraceAt oldVisit sourceIndex boundary)
  traceExact : trace = prefixInstalledTraceAt oldVisit sourceIndex boundary
  actualLedgerPoint :
    (universalSocietyRecognitionAt oldVisit sourceIndex).PointAt
      (prefixVisitAt oldVisit sourceIndex boundary)
  actualLedgerPointExact : actualLedgerPoint =
    prefixActualLedgerPointAt oldVisit sourceIndex boundary
  actualLedgerPointMem : actualLedgerPoint ∈ trace.trace.trace
  actualLedgerScenarioExact :
    actualLedgerPoint.scenario = PostSettlementSocietyScenario.actual
  actualLedgerFaceExact :
    actualLedgerPoint.face = PostSettlementSocietyBearingFace.ledger
  expression :
    FinitePrefixOperationalExpressionAt oldVisit sourceIndex boundary
  expressionCompilerCommutes : expression =
    finitePrefixOperationalExpressionOfPointAt oldVisit sourceIndex boundary
      actualLedgerPoint
  historicalRepresentation :
    FinitePrefixHistoricalRepresentationAt oldVisit sourceIndex boundary
      expression
  traceAuthorityFactorizes :
    type_of%
      ((universalSocietyRecognitionAt oldVisit sourceIndex
        ).installedTraceAuthority_factorizes
          (prefixVisitAt oldVisit sourceIndex boundary))
  actualLedgerPointExactlyOnce :
    ∃! point :
        (universalSocietyRecognitionAt oldVisit sourceIndex).PointAt
          (prefixVisitAt oldVisit sourceIndex boundary),
      point ∈
          ((universalSocietyRecognitionAt oldVisit sourceIndex).traceAt
            (prefixVisitAt oldVisit sourceIndex boundary)).trace ∧
        point.scenario = PostSettlementSocietyScenario.actual ∧
        point.face = PostSettlementSocietyBearingFace.ledger

def sourceInstalledFinitePrefixRepresentationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceInstalledFinitePrefixRepresentationAt oldVisit sourceIndex boundary :=
  let point := prefixActualLedgerPointAt oldVisit sourceIndex boundary
  { trace := prefixInstalledTraceAt oldVisit sourceIndex boundary
    traceExact := rfl
    actualLedgerPoint := point
    actualLedgerPointExact := rfl
    actualLedgerPointMem :=
      prefixActualLedgerPoint_mem oldVisit sourceIndex boundary
    actualLedgerScenarioExact := rfl
    actualLedgerFaceExact := rfl
    expression := finitePrefixOperationalExpressionOfPointAt oldVisit
      sourceIndex boundary point
    expressionCompilerCommutes := rfl
    historicalRepresentation :=
      canonicalPointExpression_preservesPrefix oldVisit sourceIndex boundary
    traceAuthorityFactorizes :=
      (universalSocietyRecognitionAt oldVisit sourceIndex
        ).installedTraceAuthority_factorizes
          (prefixVisitAt oldVisit sourceIndex boundary)
    actualLedgerPointExactlyOnce :=
      (universalSocietyRecognitionAt oldVisit sourceIndex
        ).scenario_face_exactlyOnce
          (prefixVisitAt oldVisit sourceIndex boundary) .actual .ledger }

theorem sourceInstalledFinitePrefixRepresentation_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let face :=
      sourceInstalledFinitePrefixRepresentationAt oldVisit sourceIndex boundary
    Nonempty
        (SourceInstalledFinitePrefixRepresentationAt oldVisit sourceIndex
          boundary) ∧
      type_of% face.traceExact ∧
      type_of% face.actualLedgerPointMem ∧
      type_of% face.expressionCompilerCommutes ∧
      Nonempty
        (FinitePrefixOperationalExpressionAt oldVisit sourceIndex boundary) ∧
      type_of% face.historicalRepresentation ∧
      type_of% face.traceAuthorityFactorizes ∧
      type_of% face.actualLedgerPointExactlyOnce := by
  dsimp
  let face :=
    sourceInstalledFinitePrefixRepresentationAt oldVisit sourceIndex boundary
  exact
    ⟨⟨face⟩, face.traceExact, face.actualLedgerPointMem,
      face.expressionCompilerCommutes, ⟨face.expression⟩,
      face.historicalRepresentation, face.traceAuthorityFactorizes,
      face.actualLedgerPointExactlyOnce⟩

end
end M14SourceInstalledContributionCapacityFinitePrefixRepresentation
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceInstalledContributionCapacityFinitePrefixRepresentation.canonicalPointExpression_preservesPrefix
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceInstalledContributionCapacityFinitePrefixRepresentation.sourceInstalledFinitePrefixRepresentationAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceInstalledContributionCapacityFinitePrefixRepresentation.sourceInstalledFinitePrefixRepresentation_directConsumer

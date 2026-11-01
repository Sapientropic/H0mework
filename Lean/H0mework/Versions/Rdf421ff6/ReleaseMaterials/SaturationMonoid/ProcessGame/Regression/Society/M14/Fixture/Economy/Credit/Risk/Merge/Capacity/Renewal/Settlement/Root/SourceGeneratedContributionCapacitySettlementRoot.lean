import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Compiler.SourceGeneratedContributionCapacitySettlementCompiler
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Handoff.Root.SourceGeneratedContributionCapacitySettlementSurvivorRoot

/-!
# Source-generated contribution-capacity settlement root

The exact reopening occurrence generates a two-current root.  Its first
current conservatively re-emits all three rows; its second current is an
inventory-complete faithful terminal.  The terminal handoff is fixed before
the emitter and lands on the existing two-row old face, where fresh UBI exit
renewal continues.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacitySettlementRoot

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningRoot
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementActionSource
open M14SourceGeneratedContributionCapacitySettlementCompiler
open M14SourceGeneratedContributionCapacitySettlementSurvivorCompiler
open M14SourceGeneratedContributionCapacitySettlementSurvivorRoot

def contributionCapacitySettlementResidualAt
    (oldVisit : OldVisit) :
    (contributionCapacitySettlementFullLedger oldVisit).Entry :=
  contributionCapacityReopeningResidualEntryAt oldVisit true

def contributionCapacitySettlementResidualAtOccurrence
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : SettlementSourceEventAt oldVisit sourceIndex)
    {current : Bool}
    (occurrence :
      (contributionCapacitySettlementSource oldVisit sourceIndex sourceEvent)
        |>.toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt (SettlementNAt oldVisit) occurrence.1 := by
  rcases occurrence with ⟨support, event⟩
  cases event
  · exact contributionCapacitySettlementResidualAt oldVisit
  · exact contributionCapacitySettlementResidualAt oldVisit

def contributionCapacitySettlementAnswerPayloadAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : SettlementSourceEventAt oldVisit sourceIndex)
    {current : Bool}
    (occurrence :
      (contributionCapacitySettlementSource oldVisit sourceIndex sourceEvent)
        |>.toRootSource.actual.OccurrenceAt current) : Type :=
  match current with
  | false => PUnit
  | true =>
      (contributionCapacitySettlementTerminalPatch oldVisit sourceIndex
        sourceEvent occurrence).CanonicalGeneratedEntryAt
          (contributionCapacitySettlementResidualAtOccurrence oldVisit
            sourceIndex sourceEvent occurrence)

def contributionCapacitySettlementAnswerPayload
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : SettlementSourceEventAt oldVisit sourceIndex)
    {current : Bool}
    (occurrence :
      (contributionCapacitySettlementSource oldVisit sourceIndex sourceEvent)
        |>.toRootSource.actual.OccurrenceAt current) :
    contributionCapacitySettlementAnswerPayloadAt oldVisit sourceIndex
      sourceEvent occurrence := by
  cases current with
  | false => exact PUnit.unit
  | true =>
      exact
        ((contributionCapacitySettlementTerminalPatch oldVisit sourceIndex
          sourceEvent occurrence).canonicalGeneratedEntryAt
            (contributionCapacitySettlementResidualAtOccurrence oldVisit
              sourceIndex sourceEvent occurrence))

inductive ContributionCapacitySettlementProjection
  | ledger
  | settlement
  | inquiry
  | answer
  | consumer

abbrev contributionCapacitySettlementProjectionLaw
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : SettlementSourceEventAt oldVisit sourceIndex) :
    SourceNativeProjectionLaw
      (contributionCapacitySettlementRestructuringSource oldVisit sourceIndex
        sourceEvent).toLedgerSource where
  Projection := ContributionCapacitySettlementProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_current} occurrence _ =>
    match projection with
    | .ledger => SourceNativeLedgerEvolutionAt
        (contributionCapacitySettlementSource oldVisit sourceIndex sourceEvent)
        occurrence
    | .settlement => contributionCapacitySettlementAnswerPayloadAt oldVisit
        sourceIndex sourceEvent occurrence
    | .inquiry => SourceNativeInquiryCompilationTokenAt
        (contributionCapacitySettlementResidualAtOccurrence oldVisit
          sourceIndex sourceEvent occurrence) ()
        (ULift.up.{1, 0} occurrence)
        (contributionCapacityReopeningInquiryAudit oldVisit occurrence.1)
        (contributionCapacitySettlementAnswerPayloadAt oldVisit sourceIndex
          sourceEvent occurrence)
    | .answer => contributionCapacitySettlementAnswerPayloadAt oldVisit
        sourceIndex sourceEvent occurrence
    | .consumer => SourceNativeInquiryAnswerConsumerTokenAt ()
        (ULift.up.{1, 0} occurrence)
        (contributionCapacitySettlementResidualAtOccurrence oldVisit
          sourceIndex sourceEvent occurrence)
        (contributionCapacitySettlementAnswerPayload oldVisit sourceIndex
          sourceEvent occurrence)
  project := by
    intro projection current occurrence active
    cases projection with
    | ledger =>
        exact (contributionCapacitySettlementLedgerCompiler oldVisit
          sourceIndex sourceEvent).compile occurrence
    | settlement =>
        exact contributionCapacitySettlementAnswerPayload oldVisit
          sourceIndex sourceEvent occurrence
    | inquiry =>
        exact .canonical
          (contributionCapacitySettlementAnswerPayload oldVisit sourceIndex
            sourceEvent occurrence)
    | answer =>
        exact contributionCapacitySettlementAnswerPayload oldVisit
          sourceIndex sourceEvent occurrence
    | consumer =>
        exact .canonical

theorem contributionCapacitySettlementTerminalExhaustsActualInventory
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : SettlementSourceEventAt oldVisit sourceIndex) :
    {current : Bool} →
    (occurrence :
      (contributionCapacitySettlementSource oldVisit sourceIndex sourceEvent)
        |>.toRootSource.actual.OccurrenceAt current) →
    (terminal : (SettlementVAt oldVisit).FaithfulTerminalAt current) →
    ((contributionCapacitySettlementSource oldVisit sourceIndex sourceEvent)
        |>.toRootSource.actual.compile occurrence) =
      .faithfulTerminal terminal →
    IsEmpty (SourceNativeActualOutgoingEventAt
      (contributionCapacitySettlementRestructuringSource oldVisit sourceIndex
        sourceEvent).toLedgerSource current) := by
  intro current occurrence terminal terminal_eq
  cases current with
  | false => exact nomatch terminal
  | true =>
      constructor
      rintro ⟨outOccurrence, successor⟩
      rcases outOccurrence with ⟨support, event⟩
      cases event
      exact nomatch successor

def contributionCapacitySettlementAuthoritySource
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : SettlementSourceEventAt oldVisit sourceIndex) :
    SourceNativeAuthoritySource (SettlementNAt oldVisit)
      (SettlementVAt oldVisit) where
  restructuringSource := contributionCapacitySettlementRestructuringSource
    oldVisit sourceIndex sourceEvent
  eventInventoryAdmission := .refl
    (contributionCapacitySettlementRestructuringSource oldVisit sourceIndex
      sourceEvent)
    (contributionCapacitySettlementTerminalExhaustsActualInventory oldVisit
      sourceIndex sourceEvent)
  lawSurface := contributionCapacityReopeningTheory oldVisit
  projectionLaw := contributionCapacitySettlementProjectionLaw oldVisit
    sourceIndex sourceEvent

def contributionCapacitySettlementTerminalHandoff
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : SettlementSourceEventAt oldVisit sourceIndex) :
    SourceNativeTerminalHandoffLaw
      (contributionCapacitySettlementAuthoritySource oldVisit sourceIndex
        sourceEvent) :=
  SourceNativeTerminalHandoffLaw.create
    (fun {_current} _history {_occurrence} _terminal => Unit)
    (fun {_current} _history {_occurrence} _terminal => ())
    (fun _event => ContributionCapacitySettlementSurvivorVAt oldVisit)
    (fun _event =>
      contributionCapacitySettlementSurvivorAuthoritativeRoot oldVisit
        sourceIndex sourceEvent)
    (fun _event =>
      contributionCapacitySettlementSurvivorOccurrenceUnitPresentation
        oldVisit sourceIndex sourceEvent)
    (by intros; rfl)
    (by intros; rfl)
    (by
      intro current history occurrence terminal event targetEntry
      cases terminal.terminal
      rcases occurrence with ⟨support, sourceOccurrence⟩
      cases sourceOccurrence
      exact .inl
        (contributionCapacitySettlementSurvivorDebtOrigin oldVisit targetEntry))
    (by
      intro current history occurrence terminal event sourceEntry targetEntry
        sameDebt
      cases terminal.terminal
      rcases occurrence with ⟨support, sourceOccurrence⟩
      cases sourceOccurrence
      change (contributionCapacitySettlementFullLedger oldVisit).Entry at sourceEntry
      change (contributionCapacitySettlementSurvivorLedger oldVisit).Entry at targetEntry
      have targetZero :=
        contributionCapacitySettlementSurvivorEntry_budget_zero oldVisit
          targetEntry
      exact Nat.le_trans (Nat.le_of_eq targetZero)
        (Nat.zero_le sourceEntry.progressBudget))
    (by
      intro current history occurrence terminal event sourceEntry left right
        leftDebt rightDebt
      cases terminal.terminal
      rcases occurrence with ⟨support, sourceOccurrence⟩
      cases sourceOccurrence
      exact contributionCapacitySettlementSameDebtTarget_unique oldVisit
        sourceEntry left right leftDebt rightDebt)

def contributionCapacitySettlementLivingRoot
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : SettlementSourceEventAt oldVisit sourceIndex) :
    SourceNativeLivingRootClosure (SettlementNAt oldVisit)
      (SettlementVAt oldVisit) where
  source :=
    { base := contributionCapacitySettlementAuthoritySource oldVisit
        sourceIndex sourceEvent
      terminalHandoff := contributionCapacitySettlementTerminalHandoff
        oldVisit sourceIndex sourceEvent }
  emitted := fun current => contributionCapacitySettlementEmitted oldVisit
    sourceIndex sourceEvent current
  compiler_commutes := by
    intro current
    cases current with
    | false => rfl
    | true => exact True.intro

abbrev ContributionCapacitySettlementRootAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : SettlementSourceEventAt oldVisit sourceIndex) :=
  contributionCapacitySettlementLivingRoot oldVisit sourceIndex sourceEvent

def contributionCapacitySettlementInitialVisit
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : SettlementSourceEventAt oldVisit sourceIndex) :
    SourceNativeTemporalVisitAt
      ((ContributionCapacitySettlementRootAt oldVisit sourceIndex sourceEvent)
        |>.toAuthoritativeRoot.toLedgerRoot) :=
  .finite ((ContributionCapacitySettlementRootAt oldVisit sourceIndex
    sourceEvent) |>.toAuthoritativeRoot.toRoot.initialVisit)

def contributionCapacitySettlementTerminalVisit
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : SettlementSourceEventAt oldVisit sourceIndex) :
    SourceNativeTemporalVisitAt
      ((ContributionCapacitySettlementRootAt oldVisit sourceIndex sourceEvent)
        |>.toAuthoritativeRoot.toLedgerRoot) :=
  (contributionCapacitySettlementInitialVisit oldVisit sourceIndex
    sourceEvent).next rfl

def contributionCapacitySettlementInitialGenerated
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : SettlementSourceEventAt oldVisit sourceIndex) :=
  (ContributionCapacitySettlementRootAt oldVisit sourceIndex sourceEvent)
    |>.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (contributionCapacitySettlementInitialVisit oldVisit sourceIndex
        sourceEvent)

def contributionCapacitySettlementInitialResidualRow
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : SettlementSourceEventAt oldVisit sourceIndex) :
    (contributionCapacitySettlementInitialGenerated oldVisit sourceIndex
      sourceEvent).GeneratedEntryRowAt
        (contributionCapacitySettlementResidualAt oldVisit) :=
  ((contributionCapacitySettlementInitialGenerated oldVisit sourceIndex
    sourceEvent).canonicalGeneratedEntryRow?
      (contributionCapacitySettlementResidualAt oldVisit)).get (by rfl)

def contributionCapacitySettlementFirstSuccessor
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : SettlementSourceEventAt oldVisit sourceIndex) :
    SourceNativeLedgerGeneratedSuccessorAt
      (contributionCapacitySettlementInitialGenerated oldVisit sourceIndex
        sourceEvent).occurrence
      (contributionCapacitySettlementInitialGenerated oldVisit sourceIndex
        sourceEvent).wholeLedgerWriteBack :=
  PUnit.unit

def contributionCapacitySettlementExactTerminal
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : SettlementSourceEventAt oldVisit sourceIndex) :
    SourceFaithfulTerminalOccurrenceAt
      (ContributionCapacitySettlementRootAt oldVisit sourceIndex
        sourceEvent).source.base
      ((ContributionCapacitySettlementRootAt oldVisit sourceIndex
        sourceEvent).emitted true) where
  terminal := .settled
  structural_eq := rfl
  ledgerEvolution := contributionCapacitySettlementTerminalEvolution oldVisit
    sourceIndex sourceEvent
    (contributionCapacitySettlementEmitted oldVisit sourceIndex sourceEvent
      true)
  generated_eq := rfl

@[simp] theorem contributionCapacitySettlementGeneratedHandoff_exact
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (sourceEvent : SettlementSourceEventAt oldVisit sourceIndex) :
    (ContributionCapacitySettlementRootAt oldVisit sourceIndex sourceEvent
      |>.generatedTerminalHandoffAt
        (contributionCapacitySettlementTerminalVisit oldVisit sourceIndex
          sourceEvent)
        (contributionCapacitySettlementExactTerminal oldVisit sourceIndex
          sourceEvent)) =
      ⟨ContributionCapacitySettlementSurvivorVAt oldVisit,
        contributionCapacitySettlementSurvivorAuthoritativeRoot oldVisit
          sourceIndex sourceEvent,
        contributionCapacitySettlementSurvivorInitialVisit oldVisit sourceIndex
          sourceEvent⟩ := by
  unfold SourceNativeLivingRootClosure.generatedTerminalHandoffAt
  rfl

end
end M14SourceGeneratedContributionCapacitySettlementRoot
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementRoot.contributionCapacitySettlementLivingRoot
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementRoot.contributionCapacitySettlementExactTerminal

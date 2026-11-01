import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Identity.Death.Field.Source.SourceGeneratedContributionCapacityDeathFieldDemand

/-!
# Living survivor root after contribution-capacity settlement

The root is installed on the existing two-row old face and keeps ledger,
renewal, inquiry, answer and consumer coordinates separate.  It has no local
terminal fibre: later currents are generated recursively and each carries a
fresh actual-service exit occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacitySettlementSurvivorRoot

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningRoot
open M14SourceGeneratedContributionCapacitySettlementSupport
open M14SourceGeneratedContributionCapacitySettlementActionSource
open M14SourceGeneratedContributionCapacitySettlementSurvivorCompiler
open M14SourceGeneratedContributionCapacityDeathFieldDemand
open M14UBIPeriodicActualServiceCapacity

def contributionCapacitySettlementSurvivorEntryAtOccurrence
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex)
    {current : Nat}
    (occurrence :
      (contributionCapacitySettlementSurvivorSource oldVisit sourceIndex
        settlementSource).toRootSource.actual.OccurrenceAt current)
    (entryIndex : Fin 2) :
    OpenResponsibilityAt (ReopeningNAt oldVisit) occurrence.1 := by
  rcases occurrence with ⟨support, event⟩
  cases event.supportExact.down
  exact contributionCapacitySettlementSurvivorEntryAt oldVisit entryIndex

inductive ContributionCapacitySettlementSurvivorProjection
  | ledger
  | renewal
  | deathField
  | inquiry (entryIndex : Fin 2)
  | answer (entryIndex : Fin 2)
  | consumer (entryIndex : Fin 2)

inductive ContributionCapacitySettlementSurvivorAnswer
  | canonical (entryIndex : Fin 2)

abbrev contributionCapacitySettlementSurvivorProjectionLaw
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex) :
    SourceNativeProjectionLaw
      (contributionCapacitySettlementSurvivorRestructuringSource oldVisit
        sourceIndex settlementSource).toLedgerSource where
  Projection := ContributionCapacitySettlementSurvivorProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {current} occurrence _ =>
    match projection with
    | .ledger => SourceNativeLedgerEvolutionAt
        (contributionCapacitySettlementSurvivorSource oldVisit sourceIndex
          settlementSource) occurrence
    | .renewal => PLift (Nonempty (PeriodicActualServiceExitAt
        (contributionCapacitySettlementSurvivorDepthAt sourceIndex
          (show Nat from current))))
    | .deathField =>
        SourceGeneratedContributionCapacityDeathFieldDemandAt oldVisit
          sourceIndex settlementSource occurrence
    | .inquiry entryIndex => SourceNativeInquiryCompilationTokenAt
        (contributionCapacitySettlementSurvivorEntryAtOccurrence oldVisit
          sourceIndex settlementSource occurrence entryIndex) ()
        (ULift.up.{1, 0} occurrence)
        (contributionCapacityReopeningInquiryAudit oldVisit occurrence.1)
        ContributionCapacitySettlementSurvivorAnswer
    | .answer _entryIndex =>
        ContributionCapacitySettlementSurvivorAnswer
    | .consumer entryIndex => SourceNativeInquiryAnswerConsumerTokenAt ()
        (ULift.up.{1, 0} occurrence)
        (contributionCapacitySettlementSurvivorEntryAtOccurrence oldVisit
          sourceIndex settlementSource occurrence entryIndex)
        (ContributionCapacitySettlementSurvivorAnswer.canonical entryIndex)
  project := by
    intro projection current occurrence active
    cases projection with
    | ledger =>
        exact (contributionCapacitySettlementSurvivorLedgerCompiler oldVisit
          sourceIndex settlementSource).compile occurrence
    | renewal => exact PLift.up occurrence.2.periodicExitGenerated
    | deathField =>
        exact SourceGeneratedContributionCapacityDeathFieldDemandAt.generate
          oldVisit sourceIndex settlementSource occurrence
    | inquiry entryIndex =>
        exact .canonical
          (ContributionCapacitySettlementSurvivorAnswer.canonical entryIndex)
    | answer entryIndex =>
        exact ContributionCapacitySettlementSurvivorAnswer.canonical
          entryIndex
    | consumer entryIndex => exact .canonical

def contributionCapacitySettlementSurvivorAuthoritySource
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex) :
    SourceNativeAuthoritySource (ReopeningNAt oldVisit)
      (ContributionCapacitySettlementSurvivorVAt oldVisit) where
  restructuringSource :=
    contributionCapacitySettlementSurvivorRestructuringSource oldVisit
      sourceIndex settlementSource
  eventInventoryAdmission := .reflOfNoFaithfulTerminal
    (contributionCapacitySettlementSurvivorRestructuringSource oldVisit
      sourceIndex settlementSource)
    (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := contributionCapacityReopeningTheory oldVisit
  projectionLaw := contributionCapacitySettlementSurvivorProjectionLaw
    oldVisit sourceIndex settlementSource

def contributionCapacitySettlementSurvivorAuthoritativeRoot
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex) :
    SourceNativeAuthoritativeRootClosure (ReopeningNAt oldVisit)
      (ContributionCapacitySettlementSurvivorVAt oldVisit) where
  source := contributionCapacitySettlementSurvivorAuthoritySource oldVisit
    sourceIndex settlementSource
  emitted := contributionCapacitySettlementSurvivorEmitted oldVisit
    sourceIndex settlementSource
  compiler_commutes := fun _ => rfl

def contributionCapacitySettlementSurvivorLivingRoot
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex) :
    SourceNativeLivingRootClosure (ReopeningNAt oldVisit)
      (ContributionCapacitySettlementSurvivorVAt oldVisit) :=
  (contributionCapacitySettlementSurvivorAuthoritativeRoot oldVisit
    sourceIndex settlementSource).toLivingWithoutFaithfulTerminal
      (fun _ => ⟨fun terminal => nomatch terminal⟩)

abbrev ContributionCapacitySettlementSurvivorRootAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex) :=
  contributionCapacitySettlementSurvivorLivingRoot oldVisit sourceIndex
    settlementSource

def contributionCapacitySettlementSurvivorInitialVisit
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex) :
    SourceNativeTemporalVisitAt
      (ContributionCapacitySettlementSurvivorRootAt oldVisit sourceIndex
        settlementSource).toAuthoritativeRoot.toLedgerRoot :=
  .finite
    (ContributionCapacitySettlementSurvivorRootAt oldVisit sourceIndex
      settlementSource).toAuthoritativeRoot.toRoot.initialVisit

def contributionCapacitySettlementSurvivorInitialGenerated
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex) :=
  (ContributionCapacitySettlementSurvivorRootAt oldVisit sourceIndex
    settlementSource).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (contributionCapacitySettlementSurvivorInitialVisit oldVisit sourceIndex
        settlementSource)

def contributionCapacitySettlementSurvivorInitialContributionRow
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex) :
    (contributionCapacitySettlementSurvivorInitialGenerated oldVisit
      sourceIndex settlementSource).GeneratedEntryRowAt
        (contributionCapacitySettlementSurvivorContribution oldVisit) :=
  ((contributionCapacitySettlementSurvivorInitialGenerated oldVisit
    sourceIndex settlementSource).canonicalGeneratedEntryRow?
      (contributionCapacitySettlementSurvivorContribution oldVisit)).get
        (by rfl)

def contributionCapacitySettlementSurvivorInitialAuthority
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt
      (ContributionCapacitySettlementSurvivorRootAt oldVisit sourceIndex
        settlementSource)
      (contributionCapacitySettlementSurvivorInitialVisit oldVisit sourceIndex
        settlementSource)
      (contributionCapacitySettlementSurvivorContribution oldVisit) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    (ContributionCapacitySettlementSurvivorRootAt oldVisit sourceIndex
      settlementSource)
    (contributionCapacitySettlementSurvivorContribution oldVisit)
    (contributionCapacitySettlementSurvivorInitialContributionRow oldVisit
      sourceIndex settlementSource)

/-- The death-field demand is installed before emission as one coordinate of
the existing survivor root. -/
def contributionCapacitySettlementSurvivorDeathFieldFaceAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex)
    (visit : SourceNativeTemporalVisitAt
      (ContributionCapacitySettlementSurvivorRootAt oldVisit sourceIndex
        settlementSource).toAuthoritativeRoot.toLedgerRoot) :
    SourceNativeRootSemanticFaceAt
      (ContributionCapacitySettlementSurvivorRootAt oldVisit sourceIndex
        settlementSource) visit where
  projection := ContributionCapacitySettlementSurvivorProjection.deathField
  active := PUnit.unit
  classifier_eq := rfl

/-- Root-owned readout of the installed finite-field demand. -/
def contributionCapacitySettlementSurvivorRootGeneratedDeathFieldDemandAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex)
    (visit : SourceNativeTemporalVisitAt
      (ContributionCapacitySettlementSurvivorRootAt oldVisit sourceIndex
        settlementSource).toAuthoritativeRoot.toLedgerRoot) :=
  (contributionCapacitySettlementSurvivorDeathFieldFaceAt oldVisit sourceIndex
    settlementSource visit).rootRead

def contributionCapacitySettlementSurvivorOccurrenceUnitPresentation
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex) :
    ConstructivePresentation
      ((ContributionCapacitySettlementSurvivorRootAt oldVisit sourceIndex
        settlementSource).toAuthoritativeRoot.toRoot.actual.OccurrenceAt
          (ContributionCapacitySettlementSurvivorRootAt oldVisit sourceIndex
            settlementSource).toAuthoritativeRoot.toRoot.source.initial)
      Unit where
  forward := fun _ => ()
  backward := fun _ =>
    (ContributionCapacitySettlementSurvivorRootAt oldVisit sourceIndex
      settlementSource).emitted
        (ContributionCapacitySettlementSurvivorRootAt oldVisit sourceIndex
          settlementSource).toAuthoritativeRoot.toRoot.source.initial
  backward_forward := by
    intro occurrence
    exact (contributionCapacitySettlementSurvivorOccurrence_eq_emitted
      oldVisit sourceIndex settlementSource occurrence).symm
  forward_backward := by intro value; cases value; rfl

theorem contributionCapacitySettlementSurvivorRootGeneratedRenewalAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (settlementSource :
      ContributionCapacitySettlementSourceEventAt oldVisit sourceIndex)
    (current : Nat) :
    Nonempty (PeriodicActualServiceExitAt
      (contributionCapacitySettlementSurvivorDepthAt sourceIndex current)) := by
  let occurrence := contributionCapacitySettlementSurvivorEmitted oldVisit
    sourceIndex settlementSource current
  exact occurrence.2.periodicExitGenerated

end
end M14SourceGeneratedContributionCapacitySettlementSurvivorRoot
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementSurvivorRoot.contributionCapacitySettlementSurvivorLivingRoot
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacitySettlementSurvivorRoot.contributionCapacitySettlementSurvivorInitialAuthority

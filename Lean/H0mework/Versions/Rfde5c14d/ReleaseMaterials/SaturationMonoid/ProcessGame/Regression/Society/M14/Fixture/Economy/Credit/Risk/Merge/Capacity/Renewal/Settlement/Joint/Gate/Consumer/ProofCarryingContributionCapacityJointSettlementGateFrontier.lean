import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Gate.Producer.SourceGeneratedContributionCapacityJointSettlementGateFrontier
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Consumer.SourceGeneratedContributionCapacityJointSettlementConsumer

/-!
# Direct consumer of the joint-settlement gate / death frontier

The canonical survivor current 12 remains inquiry/search.  The distinct actual
action generated at that same source root/visit enters A13 (root-local
`false`), where both live rows continue, and then A14 (`true`), where both rows
receive their exact terminal receipts.  A14 has substantive entry-indexed
death but no local successor; the empty post-settlement ledger has no
substantive death and therefore cannot satisfy the theorem vacuously.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityJointSettlementGateFrontier

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M9ProofCarryingRenewalInquiryRuntime
open M14SourceGeneratedContributionCapacitySettlementState
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementMaterial
open M14SourceGeneratedContributionCapacityJointSettlementCompiler
open M14SourceGeneratedContributionCapacityJointSettlementRoot
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedSequentialContributionCapacityJointSettlement
open M14SourceGeneratedContributionCapacityJointSettlementConsumer
open M14SourceGeneratedContributionCapacityJointSettlementGateFrontier

def contributionCapacityPostSettlementInitialGateDeathFrontier :=
  sourceGeneratedCompleteLedgerGateDeathFrontierAt
    (ContributionCapacityPostSettlementRenewalRootAt canonicalOldVisit 1
      ).toAuthoritativeRoot.toLedgerRoot
    (contributionCapacityPostSettlementRenewalInitialVisit canonicalOldVisit 1)

theorem contributionCapacityPostSettlementEmptyLedger_hasNoSubstantiveDeath :
    IsEmpty
      contributionCapacityPostSettlementInitialGateDeathFrontier.SubstantiveDeathAt := by
  apply
    contributionCapacityPostSettlementInitialGateDeathFrontier
      |>.substantiveDeath_isEmpty_of_entry_isEmpty
  exact contributionCapacityJointSettlementEmptyLedger_isEmpty canonicalOldVisit

theorem canonicalJointSettlementTerminalReceiptsExact
    (entryIndex : Fin 2) :
    Nonempty
      { death :
          (contributionCapacityJointSettlementTerminalFrontierAt
            canonicalOldVisit 1).DeathAt
              (contributionCapacityJointSettlementLiveEntryAt
                canonicalOldVisit entryIndex) //
        death.receipt =
          (contributionCapacityJointSettlementTerminalEvolution
            canonicalOldVisit 1
            (CanonicalGateMaterialAt canonicalOldVisit 1)
            (contributionCapacityJointSettlementEmitted canonicalOldVisit 1
              (CanonicalGateMaterialAt canonicalOldVisit 1) true)
            ).discharge
              (contributionCapacityJointSettlementLiveEntryAt
                canonicalOldVisit entryIndex) } :=
  ⟨⟨PUnit.unit,
    contributionCapacityJointSettlementTerminalDeath_receipt_exact
      canonicalOldVisit 1 entryIndex PUnit.unit⟩⟩

theorem canonicalJointSettlementActualAction_generatesGateRoot :
    (generatedContributionCapacityJointSettlementActionAt canonicalOldVisit 1
      (CanonicalGateMaterialAt canonicalOldVisit 1)).target.targetRoot =
        CanonicalGateRootAt canonicalOldVisit 1 :=
  rfl

theorem canonicalJointSettlementActualAction_firstSuccessor_isA14 :
    (generatedContributionCapacityJointSettlementActionAt canonicalOldVisit 1
      (CanonicalGateMaterialAt canonicalOldVisit 1)
      ).target.firstSuccessor.targetCurrent = true :=
  rfl

theorem bareTag_receipt_orEmptyLedger_cannot_retype_asGateFrontier : True := by
  fail_if_success
    exact (PUnit.unit :
      SourceGeneratedContributionCapacityJointSettlementGateFrontierAt
        canonicalOldVisit 1)
  fail_if_success
    exact (ContributionCapacityJointSettlementFaithfulTerminal.settled :
      SourceGeneratedContributionCapacityJointSettlementGateFrontierAt
        canonicalOldVisit 1)
  fail_if_success
    exact ((contributionCapacityJointSettlementTerminalEvolution
      canonicalOldVisit 1 (CanonicalGateMaterialAt canonicalOldVisit 1)
      (contributionCapacityJointSettlementEmitted canonicalOldVisit 1
        (CanonicalGateMaterialAt canonicalOldVisit 1) true)).discharge
          (contributionCapacityJointSettlementLiveEntryAt canonicalOldVisit 0) :
      SourceGeneratedContributionCapacityJointSettlementGateFrontierAt
        canonicalOldVisit 1)
  fail_if_success
    exact (contributionCapacityJointSettlementEmptySupport canonicalOldVisit :
      SourceGeneratedContributionCapacityJointSettlementGateFrontierAt
        canonicalOldVisit 1)
  trivial

structure ProofCarryingContributionCapacityJointSettlementGateFrontier : Prop where
  runtimeSeparation :
    ProofCarryingContributionCapacityJointSettlementRuntimeCertificate
  sourceDepthTwelve : contributionCapacityJointSettlementDepthAt 1 = 12
  actualActionGeneratesGateRoot :
    (generatedContributionCapacityJointSettlementActionAt canonicalOldVisit 1
      (CanonicalGateMaterialAt canonicalOldVisit 1)).target.targetRoot =
        CanonicalGateRootAt canonicalOldVisit 1
  actualActionFirstSuccessorIsA14 :
    (generatedContributionCapacityJointSettlementActionAt canonicalOldVisit 1
      (CanonicalGateMaterialAt canonicalOldVisit 1)
      ).target.firstSuccessor.targetCurrent = true
  generatedFrontier :
    SourceGeneratedContributionCapacityJointSettlementGateFrontierAt
      canonicalOldVisit 1
  everyA13EntryContinues : ∀ entryIndex : Fin 2,
    Nonempty
      ((contributionCapacityJointSettlementInitialFrontierAt canonicalOldVisit
        1).GateAt
          (contributionCapacityJointSettlementLiveEntryAt canonicalOldVisit
            entryIndex))
  everyA13EntrySurvivesAtSameRow : ∀ (entryIndex : Fin 2)
    (gate :
      (contributionCapacityJointSettlementInitialFrontierAt canonicalOldVisit
        1).GateAt
          (contributionCapacityJointSettlementLiveEntryAt canonicalOldVisit
            entryIndex)),
      gate.destination.2.1 =
        contributionCapacityJointSettlementLiveEntryAt canonicalOldVisit
          entryIndex
  everyA13EntryHasNoDeath : ∀ entryIndex : Fin 2,
    IsEmpty
      ((contributionCapacityJointSettlementInitialFrontierAt canonicalOldVisit
        1).DeathAt
          (contributionCapacityJointSettlementLiveEntryAt canonicalOldVisit
            entryIndex))
  everyA14EntryDies : ∀ entryIndex : Fin 2,
    Nonempty
      ((contributionCapacityJointSettlementTerminalFrontierAt canonicalOldVisit
        1).DeathAt
          (contributionCapacityJointSettlementLiveEntryAt canonicalOldVisit
            entryIndex))
  everyA14ReceiptExact : ∀ entryIndex : Fin 2,
    Nonempty
      { death :
          (contributionCapacityJointSettlementTerminalFrontierAt
            canonicalOldVisit 1).DeathAt
              (contributionCapacityJointSettlementLiveEntryAt
                canonicalOldVisit entryIndex) //
        death.receipt =
          (contributionCapacityJointSettlementTerminalEvolution
            canonicalOldVisit 1
            (CanonicalGateMaterialAt canonicalOldVisit 1)
            (contributionCapacityJointSettlementEmitted canonicalOldVisit 1
              (CanonicalGateMaterialAt canonicalOldVisit 1) true)
            ).discharge
              (contributionCapacityJointSettlementLiveEntryAt
                canonicalOldVisit entryIndex) }
  everyA14EntryHasNoGate : ∀ entryIndex : Fin 2,
    IsEmpty
      ((contributionCapacityJointSettlementTerminalFrontierAt canonicalOldVisit
        1).GateAt
          (contributionCapacityJointSettlementLiveEntryAt canonicalOldVisit
            entryIndex))
  a14SubstantiveDeath : Nonempty
    (contributionCapacityJointSettlementTerminalFrontierAt canonicalOldVisit
      1).SubstantiveDeathAt
  a14NoLocalSuccessor : IsEmpty
    (SourceNativeLedgerGeneratedSuccessorAt
      (contributionCapacityJointSettlementTerminalFrontierAt canonicalOldVisit
        1).event.occurrence
      (contributionCapacityJointSettlementTerminalFrontierAt canonicalOldVisit
        1).event.wholeLedgerWriteBack)
  emptyPostSettlementHasNoSubstantiveDeath : IsEmpty
    contributionCapacityPostSettlementInitialGateDeathFrontier.SubstantiveDeathAt

theorem proofCarryingContributionCapacityJointSettlementGateFrontier :
    ProofCarryingContributionCapacityJointSettlementGateFrontier where
  runtimeSeparation :=
    generatedContributionCapacityJointSettlement_runtimeSeparation
  sourceDepthTwelve := contributionCapacityJointSettlementDepthAt_one
  actualActionGeneratesGateRoot :=
    canonicalJointSettlementActualAction_generatesGateRoot
  actualActionFirstSuccessorIsA14 :=
    canonicalJointSettlementActualAction_firstSuccessor_isA14
  generatedFrontier :=
    sourceGeneratedContributionCapacityJointSettlementGateFrontier
      canonicalOldVisit 1
  everyA13EntryContinues :=
    contributionCapacityJointSettlementInitialGate_exists canonicalOldVisit 1
  everyA13EntrySurvivesAtSameRow :=
    contributionCapacityJointSettlementInitialGate_destination_exact
      canonicalOldVisit 1
  everyA13EntryHasNoDeath :=
    contributionCapacityJointSettlementInitialDeath_isEmpty canonicalOldVisit 1
  everyA14EntryDies :=
    contributionCapacityJointSettlementTerminalDeath_exists canonicalOldVisit 1
  everyA14ReceiptExact := canonicalJointSettlementTerminalReceiptsExact
  everyA14EntryHasNoGate :=
    contributionCapacityJointSettlementTerminalGate_isEmpty canonicalOldVisit 1
  a14SubstantiveDeath :=
    contributionCapacityJointSettlementTerminalDeath_substantive
      canonicalOldVisit 1
  a14NoLocalSuccessor :=
    contributionCapacityJointSettlementTerminalGate_noLocalSuccessor
      canonicalOldVisit 1
  emptyPostSettlementHasNoSubstantiveDeath :=
    contributionCapacityPostSettlementEmptyLedger_hasNoSubstantiveDeath

end
end M14ProofCarryingContributionCapacityJointSettlementGateFrontier
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityJointSettlementGateFrontier.proofCarryingContributionCapacityJointSettlementGateFrontier
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityJointSettlementGateFrontier.contributionCapacityPostSettlementEmptyLedger_hasNoSubstantiveDeath

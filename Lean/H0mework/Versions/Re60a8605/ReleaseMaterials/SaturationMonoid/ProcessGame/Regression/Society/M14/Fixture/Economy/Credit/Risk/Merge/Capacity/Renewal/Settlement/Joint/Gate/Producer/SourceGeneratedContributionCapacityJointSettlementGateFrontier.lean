import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.LivingLaw.Inventory.Gate.SourceGeneratedCausalEntryGateDeathFrontierKernel
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Root.SourceGeneratedContributionCapacityJointSettlementRoot

/-!
# Joint-settlement generated gate / death frontier

The action-generated joint-settlement root supplies both sides of a genuine
current-relative frontier.  Its initial `false` occurrence continues every
row of the complete `Fin 2` ledger.  Its next `true` occurrence faithfully
terminates every one of those same rows and has no local successor.

No caller submits a gate family, coverage proof, chosen failed row or death
mode.  Both classifications are computed by the generic zero-field frontier
from the two exact compiler visits.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityJointSettlementGateFrontier

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementMaterial
open M14SourceGeneratedContributionCapacityJointSettlementCompiler
open M14SourceGeneratedContributionCapacityJointSettlementRoot

abbrev CanonicalGateMaterialAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  sourceGeneratedContributionCapacityJointSettlementMaterialAt oldVisit
    sourceIndex

abbrev CanonicalGateRootAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :=
  ContributionCapacityJointSettlementRootAt oldVisit sourceIndex
    (CanonicalGateMaterialAt oldVisit sourceIndex)

def contributionCapacityJointSettlementInitialFrontierAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceGeneratedCompleteLedgerGateDeathFrontierAt
      (CanonicalGateRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityJointSettlementInitialVisit oldVisit sourceIndex
        (CanonicalGateMaterialAt oldVisit sourceIndex)) :=
  sourceGeneratedCompleteLedgerGateDeathFrontierAt
    (CanonicalGateRootAt oldVisit sourceIndex
      ).toAuthoritativeRoot.toLedgerRoot
    (contributionCapacityJointSettlementInitialVisit oldVisit sourceIndex
      (CanonicalGateMaterialAt oldVisit sourceIndex))

def contributionCapacityJointSettlementTerminalFrontierAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceGeneratedCompleteLedgerGateDeathFrontierAt
      (CanonicalGateRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot
      (contributionCapacityJointSettlementTerminalVisit oldVisit sourceIndex
        (CanonicalGateMaterialAt oldVisit sourceIndex)) :=
  sourceGeneratedCompleteLedgerGateDeathFrontierAt
    (CanonicalGateRootAt oldVisit sourceIndex
      ).toAuthoritativeRoot.toLedgerRoot
    (contributionCapacityJointSettlementTerminalVisit oldVisit sourceIndex
      (CanonicalGateMaterialAt oldVisit sourceIndex))

theorem contributionCapacityJointSettlementInitialGate_exists
    (oldVisit : OldVisit) (sourceIndex : Nat) (entryIndex : Fin 2) :
    Nonempty
      ((contributionCapacityJointSettlementInitialFrontierAt oldVisit
        sourceIndex).GateAt
          (contributionCapacityJointSettlementLiveEntryAt oldVisit
            entryIndex)) := by
  exact ⟨PUnit.unit⟩

theorem contributionCapacityJointSettlementInitialGate_destination_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) (entryIndex : Fin 2)
    (gate :
      (contributionCapacityJointSettlementInitialFrontierAt oldVisit
        sourceIndex).GateAt
          (contributionCapacityJointSettlementLiveEntryAt oldVisit
            entryIndex)) :
    gate.destination.2.1 =
      contributionCapacityJointSettlementLiveEntryAt oldVisit entryIndex := by
  apply contributionCapacityJointSettlementWriteEvolution_destination

theorem contributionCapacityJointSettlementInitialDeath_isEmpty
    (oldVisit : OldVisit) (sourceIndex : Nat) (entryIndex : Fin 2) :
    IsEmpty
      ((contributionCapacityJointSettlementInitialFrontierAt oldVisit
        sourceIndex).DeathAt
          (contributionCapacityJointSettlementLiveEntryAt oldVisit
            entryIndex)) := by
  change IsEmpty PEmpty
  infer_instance

theorem contributionCapacityJointSettlementTerminalGate_isEmpty
    (oldVisit : OldVisit) (sourceIndex : Nat) (entryIndex : Fin 2) :
    IsEmpty
      ((contributionCapacityJointSettlementTerminalFrontierAt oldVisit
        sourceIndex).GateAt
          (contributionCapacityJointSettlementLiveEntryAt oldVisit
            entryIndex)) := by
  constructor
  intro gate
  exact PEmpty.elim gate

theorem contributionCapacityJointSettlementTerminalDeath_exists
    (oldVisit : OldVisit) (sourceIndex : Nat) (entryIndex : Fin 2) :
    Nonempty
      ((contributionCapacityJointSettlementTerminalFrontierAt oldVisit
        sourceIndex).DeathAt
          (contributionCapacityJointSettlementLiveEntryAt oldVisit
            entryIndex)) := by
  exact ⟨PUnit.unit⟩

theorem contributionCapacityJointSettlementTerminalDeath_receipt_exact
    (oldVisit : OldVisit) (sourceIndex : Nat) (entryIndex : Fin 2)
    (death :
      (contributionCapacityJointSettlementTerminalFrontierAt oldVisit
        sourceIndex).DeathAt
          (contributionCapacityJointSettlementLiveEntryAt oldVisit
            entryIndex)) :
    death.receipt =
      (contributionCapacityJointSettlementTerminalEvolution oldVisit
        sourceIndex (CanonicalGateMaterialAt oldVisit sourceIndex)
        (contributionCapacityJointSettlementEmitted oldVisit sourceIndex
          (CanonicalGateMaterialAt oldVisit sourceIndex) true)
        ).discharge
          (contributionCapacityJointSettlementLiveEntryAt oldVisit
            entryIndex) :=
  rfl

theorem contributionCapacityJointSettlementTerminalGate_noLocalSuccessor
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    IsEmpty
      (SourceNativeLedgerGeneratedSuccessorAt
        (contributionCapacityJointSettlementTerminalFrontierAt oldVisit
          sourceIndex).event.occurrence
        (contributionCapacityJointSettlementTerminalFrontierAt oldVisit
          sourceIndex).event.wholeLedgerWriteBack) := by
  constructor
  intro successor
  exact PEmpty.elim successor

theorem contributionCapacityJointSettlementTerminalDeath_substantive
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    Nonempty
      (contributionCapacityJointSettlementTerminalFrontierAt oldVisit
        sourceIndex).SubstantiveDeathAt :=
  ⟨⟨contributionCapacityJointSettlementLiveEntryAt oldVisit (0 : Fin 2),
    PUnit.unit⟩⟩

theorem contributionCapacityJointSettlementGate_entriesDistinct
    (oldVisit : OldVisit) :
    contributionCapacityJointSettlementLiveEntryAt oldVisit (0 : Fin 2) ≠
      contributionCapacityJointSettlementLiveEntryAt oldVisit (1 : Fin 2) := by
  intro entries_eq
  have indices_eq := (contributionCapacityJointSettlementLiveEntryEquiv
    oldVisit).injective entries_eq
  exact Fin.zero_ne_one indices_eq

structure SourceGeneratedContributionCapacityJointSettlementGateFrontierAt
    (oldVisit : OldVisit) (sourceIndex : Nat) : Prop where
  private mk ::
  initialComplete : ∀ entryIndex : Fin 2,
    Nonempty
      ((contributionCapacityJointSettlementInitialFrontierAt oldVisit
        sourceIndex).GateAt
          (contributionCapacityJointSettlementLiveEntryAt oldVisit entryIndex))
  initialNoDeath : ∀ entryIndex : Fin 2,
    IsEmpty
      ((contributionCapacityJointSettlementInitialFrontierAt oldVisit
        sourceIndex).DeathAt
          (contributionCapacityJointSettlementLiveEntryAt oldVisit entryIndex))
  terminalComplete : ∀ entryIndex : Fin 2,
    Nonempty
      ((contributionCapacityJointSettlementTerminalFrontierAt oldVisit
        sourceIndex).DeathAt
          (contributionCapacityJointSettlementLiveEntryAt oldVisit entryIndex))
  terminalNoGate : ∀ entryIndex : Fin 2,
    IsEmpty
      ((contributionCapacityJointSettlementTerminalFrontierAt oldVisit
        sourceIndex).GateAt
          (contributionCapacityJointSettlementLiveEntryAt oldVisit entryIndex))
  substantiveDeath : Nonempty
    (contributionCapacityJointSettlementTerminalFrontierAt oldVisit
      sourceIndex).SubstantiveDeathAt
  terminalNoLocalSuccessor : IsEmpty
    (SourceNativeLedgerGeneratedSuccessorAt
      (contributionCapacityJointSettlementTerminalFrontierAt oldVisit
        sourceIndex).event.occurrence
      (contributionCapacityJointSettlementTerminalFrontierAt oldVisit
        sourceIndex).event.wholeLedgerWriteBack)
  twoActualRows :
    contributionCapacityJointSettlementLiveEntryAt oldVisit (0 : Fin 2) ≠
      contributionCapacityJointSettlementLiveEntryAt oldVisit (1 : Fin 2)

theorem sourceGeneratedContributionCapacityJointSettlementGateFrontier
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceGeneratedContributionCapacityJointSettlementGateFrontierAt oldVisit
      sourceIndex where
  initialComplete :=
    contributionCapacityJointSettlementInitialGate_exists oldVisit sourceIndex
  initialNoDeath :=
    contributionCapacityJointSettlementInitialDeath_isEmpty oldVisit
      sourceIndex
  terminalComplete :=
    contributionCapacityJointSettlementTerminalDeath_exists oldVisit
      sourceIndex
  terminalNoGate :=
    contributionCapacityJointSettlementTerminalGate_isEmpty oldVisit
      sourceIndex
  substantiveDeath :=
    contributionCapacityJointSettlementTerminalDeath_substantive oldVisit
      sourceIndex
  terminalNoLocalSuccessor :=
    contributionCapacityJointSettlementTerminalGate_noLocalSuccessor oldVisit
      sourceIndex
  twoActualRows :=
    contributionCapacityJointSettlementGate_entriesDistinct oldVisit

end
end M14SourceGeneratedContributionCapacityJointSettlementGateFrontier
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementGateFrontier.sourceGeneratedContributionCapacityJointSettlementGateFrontier
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementGateFrontier.contributionCapacityJointSettlementTerminalDeath_receipt_exact

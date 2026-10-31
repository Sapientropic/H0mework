import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Compiler.SourceGeneratedContributionCapacityCutCompiler
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Lifecycle.SourceGeneratedContributionCapacityCutLifecycle

/-!
# Source-generated contribution-capacity restructuring

The first capacity write is a one-to-one whole-ledger transition.  The
contribution row spends its remaining progress budget and the obstruction
row is transported unchanged; neither row splits or merges.  Every later
write is the identity on the exact cut target.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityCutRestructuring

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ObstructionGeneratedMinimalCoface
open M14SourceGeneratedLossAllocationWorld
open M14SourceGeneratedContributionMergeWorld
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutCompiler
open M14SourceGeneratedContributionCapacityCutLifecycle

variable
    {OldV : ConstructiveRoot.Vocabulary}
    {oldWorld : SourceNativeAuthoritativeRootClosure
      M14SourceGeneratedLossAllocationWorld.OldN OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus M14SourceGeneratedLossAllocationWorld.OldN}
    {oldTheory : TheoryState M14SourceGeneratedLossAllocationWorld.OldN}
    {support : M14SourceGeneratedLossAllocationWorld.OldN.Support}
    {obstruction :
      M14SourceGeneratedLossAllocationWorld.OldN.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}

local notation "RootedFailure" => RootedActualExpressibilityFailureAt
  oldWorld oldVisit U7 failure

/-! ## Source-fixed one-to-one law -/

def contributionCapacityCutRestructuringVocabulary
    (rooted : RootedFailure) : RestructuringVocabulary where
  base := ContributionCapacityCutLifecycleV rooted
  DescendantAt := fun _ parentIncidence parentContent
      childIncidence childContent =>
    PLift (parentIncidence = childIncidence) ×
      PLift (parentContent = childContent)
  SplitCoverageAt := fun _ _ _ => PEmpty
  MergeCoverageAt := fun _ _ _ => PEmpty
  LocalDischargePreservedAt := fun _ parentContent childContent =>
    PLift (parentContent = childContent)
  RenameAt := fun _ oldContent newContent =>
    PLift (oldContent = newContent)

abbrev ContributionCapacityCutRestructuringV (rooted : RootedFailure) :=
  contributionCapacityCutRestructuringVocabulary rooted

def contributionCapacityCutRestructuringLaw
    (rooted : RootedFailure) :
    SourceNativeLedgerRestructuringLaw
      (contributionCapacityCutSource rooted) where
  vocabulary := ContributionCapacityCutRestructuringV rooted
  sourceEventAt := fun occurrence =>
    ((contributionCapacityCutSource rooted).toRootSource.account.supportOf
        occurrence,
      occurrence.2.materialWitness)
  obligationAt := by
    intro current occurrence indexedSupport entry
    exact contributionCapacityCutObligationAt rooted
      occurrence.2.materialWitness entry
  responsibilityKey := AdmittedObligation.content
  anchorKey := fun _ => ()
  incidenceKey := id
  lineageKey := id
  responsibility_commutes := by
    intro current occurrence indexedSupport entry
    rfl
  anchor_commutes := by
    intro current occurrence indexedSupport entry
    rfl
  incidence_commutes := by
    intro current occurrence indexedSupport entry
    rfl
  lineage_commutes := by
    intro current occurrence indexedSupport entry
    rfl
  obligationAt_injective := by
    intro current occurrence indexedSupport left right obligation_eq
    exact contributionCapacityCutObligationAt_injective rooted
      occurrence.2.materialWitness obligation_eq

/-! ## Exact first-write injectivity -/

theorem initialCapacityEntries_distinct
    (rooted : RootedFailure) :
    initialContribution rooted ≠ initialObstruction rooted := by
  intro equality
  have responsibility_eq := congrArg Sigma.fst equality
  exact nomatch responsibility_eq

theorem contributionCapacityFirst_origin_injective
    (rooted : RootedFailure)
    (occurrence :
      (contributionCapacityCutSource rooted).toRootSource.actual.OccurrenceAt
        0)
    (left right : (contributionCapacityCutTargetLedger rooted).Entry)
    (origin_eq :
      ((contributionCapacityFirstEvolution rooted occurrence).origin left).1 =
        ((contributionCapacityFirstEvolution rooted occurrence).origin
          right).1) :
    left = right := by
  rcases contributionCapacityCutTargetEntry_cases rooted left with
      left_eq | left_eq <;>
    rcases contributionCapacityCutTargetEntry_cases rooted right with
      right_eq | right_eq
  · exact left_eq.trans right_eq.symm
  · subst left
    subst right
    exact False.elim (initialCapacityEntries_distinct rooted <|
      (contributionCapacityFirst_origin_contribution
        rooted occurrence).symm.trans
        (origin_eq.trans
          (contributionCapacityFirst_origin_obstruction rooted occurrence)))
  · subst left
    subst right
    exact False.elim (initialCapacityEntries_distinct rooted <|
      (contributionCapacityFirst_origin_contribution
        rooted occurrence).symm.trans
        (origin_eq.symm.trans
          (contributionCapacityFirst_origin_obstruction rooted occurrence)))
  · exact left_eq.trans right_eq.symm

theorem contributionCapacityFirst_destination_injective
    (rooted : RootedFailure)
    (occurrence :
      (contributionCapacityCutSource rooted).toRootSource.actual.OccurrenceAt
        0)
    (left right : (contributionCapacityCutInitialLedger rooted).Entry)
    (destination_eq :
      ((contributionCapacityFirstEvolution rooted occurrence).destination
          left).1 =
        ((contributionCapacityFirstEvolution rooted occurrence).destination
          right).1) :
    left = right := by
  rcases contributionCapacityCutInitialEntry_cases rooted left with
      left_eq | left_eq <;>
    rcases contributionCapacityCutInitialEntry_cases rooted right with
      right_eq | right_eq
  · exact left_eq.trans right_eq.symm
  · subst left
    subst right
    exact False.elim (contributionCapacityCutTargetEntries_distinct rooted <|
      (contributionCapacityFirst_destination_contribution
        rooted occurrence).symm.trans
        (destination_eq.trans
          (contributionCapacityFirst_destination_obstruction
            rooted occurrence)))
  · subst left
    subst right
    exact False.elim (contributionCapacityCutTargetEntries_distinct rooted <|
      (contributionCapacityFirst_destination_contribution
        rooted occurrence).symm.trans
        (destination_eq.symm.trans
          (contributionCapacityFirst_destination_obstruction
            rooted occurrence)))
  · exact left_eq.trans right_eq.symm

/-! ## Whole-source certification -/

def contributionCapacityFirstRestructuringCertification
    (rooted : RootedFailure)
    (occurrence :
      (contributionCapacityCutSource rooted).toRootSource.actual.OccurrenceAt
        0) :
    ExactLedgerRestructuringCertificationAt
      (contributionCapacityCutRestructuringLaw rooted) occurrence
      (contributionCapacityFirstEvolution rooted occurrence) :=
  ExactLedgerRestructuringCertificationAt.ofInjective
    (contributionCapacityFirst_origin_injective rooted occurrence)
    (contributionCapacityFirst_destination_injective rooted occurrence)

def contributionCapacityTargetIdentityCertification
    (rooted : RootedFailure)
    (current : Nat)
    (occurrence :
      (contributionCapacityCutSource rooted).toRootSource.actual.OccurrenceAt
        (Nat.succ current)) :
    SourceNativeLedgerRestructuringCertificationAt
      (contributionCapacityCutRestructuringLaw rooted)
      ((contributionCapacityCutLedgerCompiler rooted).compile occurrence) := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  exact ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right origin_eq => origin_eq)
    (fun left right destination_eq => destination_eq)

def contributionCapacityCutRestructuringCertification
    (rooted : RootedFailure)
    {current : (TargetV rooted).Current}
    (occurrence :
      (contributionCapacityCutSource rooted).toRootSource.actual.OccurrenceAt
        current) :
    SourceNativeLedgerRestructuringCertificationAt
      (contributionCapacityCutRestructuringLaw rooted)
      ((contributionCapacityCutLedgerCompiler rooted).compile occurrence) := by
  cases current with
  | zero =>
      rcases occurrence with ⟨indexedSupport, event⟩
      cases event.supportExact.down
      exact contributionCapacityFirstRestructuringCertification rooted
        ⟨contributionCapacityCutInitialSupport rooted, event⟩
  | succ current =>
      exact contributionCapacityTargetIdentityCertification
        rooted current occurrence

def contributionCapacityCutRestructuringCompiler
    (rooted : RootedFailure) :
    SourceNativeRestructuringLedgerCompiler
      (contributionCapacityCutSource rooted) where
  ledgerCompiler := contributionCapacityCutLedgerCompiler rooted
  restructuringLaw := contributionCapacityCutRestructuringLaw rooted
  certifyRestructuring :=
    contributionCapacityCutRestructuringCertification rooted

def contributionCapacityCutRestructuringSource
    (rooted : RootedFailure) :
    SourceNativeRestructuringLedgerSource
      (CutN rooted) (TargetV rooted) where
  source := contributionCapacityCutSource rooted
  compiler := contributionCapacityCutRestructuringCompiler rooted

end
end M14SourceGeneratedContributionCapacityCutRestructuring
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCutRestructuring.contributionCapacityFirstRestructuringCertification
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityCutRestructuring.contributionCapacityCutRestructuringSource

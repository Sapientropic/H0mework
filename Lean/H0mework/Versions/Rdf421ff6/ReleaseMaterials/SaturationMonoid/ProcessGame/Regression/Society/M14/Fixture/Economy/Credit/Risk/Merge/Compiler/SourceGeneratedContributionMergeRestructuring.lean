import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Compiler.SourceGeneratedContributionMergeCompiler
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Lifecycle.SourceGeneratedContributionMergeLifecycle

/-!
# Source-generated contribution-merge restructuring

The contribution-merge compiler's exact first whole-ledger image is
classified by one existing SourceNativeMergeCoverageAt.  Its parents are
literally the translated A/B child obligations, its target is the merged
contribution obligation, and every parent retains source ownership,
descendant incidence, anchor, lineage and local discharge.

The obstruction remains outside the repeated-destination fibre.  The first
write has injective origins, hence no simultaneous split.  No root, runtime,
new receipt type, bearer or registry is introduced here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionMergeRestructuring

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ObstructionGeneratedMinimalCoface
open M14SourceGeneratedLossAllocationWorld
open M14SourceGeneratedLossAllocationRestructuring
open M14SourceGeneratedContributionMergeWorld
open M14SourceGeneratedContributionMergeCompiler
open M14SourceGeneratedContributionMergeLifecycle

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

/-! ## Source-fixed merge law -/

def contributionMergeRestructuringVocabulary
    (rooted : RootedFailure) : RestructuringVocabulary where
  base := ContributionMergeLifecycleV rooted
  DescendantAt := fun _ parentIncidence parentContent
      childIncidence childContent =>
    PLift (parentIncidence = childIncidence) ×
      PLift (parentContent = childContent)
  SplitCoverageAt := fun _ _ _ => PEmpty
  MergeCoverageAt := fun _ parentContents targetContent =>
    PLift (parentContents = [targetContent, targetContent])
  LocalDischargePreservedAt := fun _ parentContent childContent =>
    PLift (parentContent = childContent)
  RenameAt := fun _ oldContent newContent =>
    PLift (oldContent = newContent)

abbrev ContributionMergeRestructuringV (rooted : RootedFailure) :=
  contributionMergeRestructuringVocabulary rooted

def contributionMergeRestructuringLaw
    (rooted : RootedFailure) :
    SourceNativeLedgerRestructuringLaw
      (contributionMergeSource rooted) where
  vocabulary := ContributionMergeRestructuringV rooted
  sourceEventAt := fun occurrence =>
    ((contributionMergeSource rooted).toRootSource.account.supportOf occurrence,
      occurrence.2.materialWitness)
  obligationAt := by
    intro current occurrence indexedSupport entry
    exact contributionMergeObligationAt rooted
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
    exact contributionMergeObligationAt_injective rooted
      occurrence.2.materialWitness obligation_eq

abbrev initialChildAObligation
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0) :=
  (contributionMergeRestructuringLaw rooted).obligationAt occurrence
    (initialChildA rooted)

abbrev initialChildBObligation
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0) :=
  (contributionMergeRestructuringLaw rooted).obligationAt occurrence
    (initialChildB rooted)

abbrev initialObstructionObligation
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0) :=
  (contributionMergeRestructuringLaw rooted).obligationAt occurrence
    (initialObstruction rooted)

abbrev mergedContributionObligation
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0) :=
  (contributionMergeRestructuringLaw rooted).obligationAt occurrence
    (mergedContributionEntry rooted)

/-! ## Exact A/B merge receipt and coverage -/

def contributionMergeReceiptParentAt
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0) :
    Fin 2 → (ContributionMergeRestructuringV rooted).Obligation :=
  Fin.cases (initialChildAObligation rooted occurrence)
    (fun _ => initialChildBObligation rooted occurrence)

def contributionMergeReceiptParentIndexAt
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0)
    (parent : (ContributionMergeRestructuringV rooted).Obligation)
    (member : parent ∈
      [initialChildAObligation rooted occurrence,
        initialChildBObligation rooted occurrence]) :
    { index : Fin 2 //
      contributionMergeReceiptParentAt rooted occurrence index = parent } := by
  let indexed := List.get_of_mem member
  let index := Classical.choose indexed
  have index_eq := Classical.choose_spec indexed
  change Fin 2 at index
  change
    [initialChildAObligation rooted occurrence,
      initialChildBObligation rooted occurrence].get index = parent at index_eq
  have get_eq :
      [initialChildAObligation rooted occurrence,
        initialChildBObligation rooted occurrence].get index =
        contributionMergeReceiptParentAt rooted occurrence index := by
    refine Fin.cases rfl (fun tail => ?_) index
    change Fin 1 at tail
    have tail_eq : tail = (0 : Fin 1) := Subsingleton.elim _ _
    subst tail
    rfl
  exact ⟨index, get_eq.symm.trans index_eq⟩

def contributionMergeFirstReceipt
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0) :
    MergeReceipt (contributionMergeRestructuringLaw rooted).vocabulary where
  sourceEvent :=
    (contributionMergeInitialSupport rooted, occurrence.2.materialWitness)
  parents :=
    [initialChildAObligation rooted occurrence,
      initialChildBObligation rooted occurrence]
  parents_nonempty := by simp
  target := mergedContributionObligation rooted occurrence
  sourceOwnership := ⟨rfl, rfl⟩
  coverage := PLift.up rfl
  ancestor := by
    intro parent member
    rcases contributionMergeReceiptParentIndexAt
        rooted occurrence parent member with ⟨index, parent_eq⟩
    subst parent
    refine Fin.cases ?_ (fun tail => ?_) index
    · exact ⟨PLift.up rfl, PLift.up rfl⟩
    · change Fin 1 at tail
      have tail_eq : tail = (0 : Fin 1) := Subsingleton.elim _ _
      subst tail
      exact ⟨PLift.up rfl, PLift.up rfl⟩
  anchorTransport := fun _ _ => SourceAnchorTransport.refl _
  lineage := by
    intro parent member
    rcases contributionMergeReceiptParentIndexAt
        rooted occurrence parent member with ⟨index, parent_eq⟩
    subst parent
    refine Fin.cases rfl (fun tail => ?_) index
    change Fin 1 at tail
    have tail_eq : tail = (0 : Fin 1) := Subsingleton.elim _ _
    subst tail
    rfl
  localDischarge := by
    intro parent member
    rcases contributionMergeReceiptParentIndexAt
        rooted occurrence parent member with ⟨index, parent_eq⟩
    subst parent
    refine Fin.cases (PLift.up rfl) (fun tail => ?_) index
    change Fin 1 at tail
    have tail_eq : tail = (0 : Fin 1) := Subsingleton.elim _ _
    subst tail
    exact PLift.up rfl

/-- Every listed parent, not only the merged target, is owned by the exact
first source event. -/
def contributionMergeFirstParentOwnership
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0)
    (parent : (ContributionMergeRestructuringV rooted).Obligation)
    (member : parent ∈
      (contributionMergeFirstReceipt rooted occurrence).parents) :
    SourceOwnsResponsibilityIncidence
      (ContributionMergeRestructuringV rooted).base
      (contributionMergeFirstReceipt rooted occurrence).sourceEvent parent := by
  rcases contributionMergeReceiptParentIndexAt
      rooted occurrence parent member with ⟨index, parent_eq⟩
  subst parent
  refine Fin.cases ?_ (fun tail => ?_) index
  · exact ⟨rfl, rfl⟩
  · change Fin 1 at tail
    have tail_eq : tail = (0 : Fin 1) := Subsingleton.elim _ _
    subst tail
    exact ⟨rfl, rfl⟩

def contributionMergeFirstCoverage
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0) :
    SourceNativeMergeCoverageAt
      (contributionMergeRestructuringLaw rooted) occurrence
      (contributionMergeFirstEvolution rooted occurrence)
      (initialChildA rooted) (initialChildB rooted)
      (contributionMergeFirst_children_repeatedDestination rooted occurrence) := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  let canonicalOccurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0 :=
    ⟨contributionMergeInitialSupport rooted, event⟩
  apply SourceNativeMergeCoverageAt.ofReceipt
    (receipt := contributionMergeFirstReceipt rooted canonicalOccurrence)
  · rfl
  · exact congrArg
      ((contributionMergeRestructuringLaw rooted).obligationAt
        canonicalOccurrence)
      (contributionMergeFirst_destination_childA
        rooted canonicalOccurrence).symm
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  · intro sourceEntry destination_eq
    rcases contributionMergeInitialEntry_cases rooted sourceEntry with
        source_eq | source_eq | source_eq
    · subst sourceEntry
      exact List.mem_cons_self
    · subst sourceEntry
      exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    · subst sourceEntry
      exact False.elim
        (mergedEntries_distinct rooted <|
          (contributionMergeFirst_destination_childA
            rooted canonicalOccurrence).symm.trans
            (destination_eq.symm.trans
              (contributionMergeFirst_destination_obstruction
                rooted canonicalOccurrence)))
  · intro parent member
    apply Classical.choice
    rcases List.mem_cons.mp member with parent_eq | member
    · exact ⟨⟨initialChildA rooted, parent_eq.symm, rfl⟩⟩
    · rcases List.mem_cons.mp member with parent_eq | member
      · exact ⟨⟨initialChildB rooted, parent_eq.symm,
          (contributionMergeFirst_children_repeatedDestination
            rooted canonicalOccurrence).symm⟩⟩
      · exact nomatch member

def contributionMergeFirstCoverageBA
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0) :
    SourceNativeMergeCoverageAt
      (contributionMergeRestructuringLaw rooted) occurrence
      (contributionMergeFirstEvolution rooted occurrence)
      (initialChildB rooted) (initialChildA rooted)
      (contributionMergeFirst_children_repeatedDestination
        rooted occurrence).symm := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  let canonicalOccurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0 :=
    ⟨contributionMergeInitialSupport rooted, event⟩
  apply SourceNativeMergeCoverageAt.ofReceipt
    (receipt := contributionMergeFirstReceipt rooted canonicalOccurrence)
  · rfl
  · exact congrArg
      ((contributionMergeRestructuringLaw rooted).obligationAt
        canonicalOccurrence)
      (contributionMergeFirst_destination_childB
        rooted canonicalOccurrence).symm
  · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  · exact List.mem_cons_self
  · intro sourceEntry destination_eq
    rcases contributionMergeInitialEntry_cases rooted sourceEntry with
        source_eq | source_eq | source_eq
    · subst sourceEntry
      exact List.mem_cons_self
    · subst sourceEntry
      exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    · subst sourceEntry
      exact False.elim
        (mergedEntries_distinct rooted <|
          (contributionMergeFirst_destination_childB
            rooted canonicalOccurrence).symm.trans
            (destination_eq.symm.trans
              (contributionMergeFirst_destination_obstruction
                rooted canonicalOccurrence)))
  · intro parent member
    apply Classical.choice
    rcases List.mem_cons.mp member with parent_eq | member
    · exact ⟨⟨initialChildA rooted, parent_eq.symm,
        contributionMergeFirst_children_repeatedDestination
          rooted canonicalOccurrence⟩⟩
    · rcases List.mem_cons.mp member with parent_eq | member
      · exact ⟨⟨initialChildB rooted, parent_eq.symm, rfl⟩⟩
      · exact nomatch member

/-! ## Exact exclusion and no-split controls -/

theorem initialObstruction_ne_childA
    (rooted : RootedFailure) :
    initialObstruction rooted ≠ initialChildA rooted := by
  intro equality
  have responsibility_eq := congrArg Sigma.fst equality
  exact nomatch responsibility_eq

theorem initialObstruction_ne_childB
    (rooted : RootedFailure) :
    initialObstruction rooted ≠ initialChildB rooted := by
  intro equality
  have responsibility_eq := congrArg Sigma.fst equality
  exact nomatch responsibility_eq

theorem contributionMergeFirst_obstruction_not_parent
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0) :
    initialObstructionObligation rooted occurrence ∉
      (contributionMergeFirstReceipt rooted occurrence).parents := by
  intro member
  rcases List.mem_cons.mp member with member | member
  · exact initialObstruction_ne_childA rooted
      ((contributionMergeRestructuringLaw rooted).obligationAt_injective
        occurrence member)
  · rcases List.mem_cons.mp member with member | member
    · exact initialObstruction_ne_childB rooted
        ((contributionMergeRestructuringLaw rooted).obligationAt_injective
          occurrence member)
    · exact nomatch member

theorem contributionMergeFirst_obstruction_destination_ne
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0) :
    ((contributionMergeFirstEvolution rooted occurrence).destination
        (initialObstruction rooted)).1 ≠
      ((contributionMergeFirstEvolution rooted occurrence).destination
        (initialChildA rooted)).1 := by
  intro destination_eq
  exact (mergedEntries_distinct rooted).symm
    ((contributionMergeFirst_destination_obstruction
      rooted occurrence).symm.trans
      (destination_eq.trans
        (contributionMergeFirst_destination_childA rooted occurrence)))

theorem contributionMergeFirst_origin_injective
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0)
    (left right : (contributionMergeTargetLedger rooted).Entry)
    (origin_eq :
      ((contributionMergeFirstEvolution rooted occurrence).origin left).1 =
        ((contributionMergeFirstEvolution rooted occurrence).origin right).1) :
    left = right := by
  rcases contributionMergeTargetEntry_cases rooted left with
      left_eq | left_eq <;>
    rcases contributionMergeTargetEntry_cases rooted right with
      right_eq | right_eq
  · exact left_eq.trans right_eq.symm
  · subst left
    subst right
    exact False.elim (initialObstruction_ne_childA rooted <|
      (contributionMergeFirst_origin_obstruction
        rooted occurrence).symm.trans
        (origin_eq.symm.trans
          (contributionMergeFirst_origin_contribution rooted occurrence)))
  · subst left
    subst right
    exact False.elim (initialObstruction_ne_childA rooted <|
      (contributionMergeFirst_origin_obstruction
        rooted occurrence).symm.trans
        (origin_eq.trans
          (contributionMergeFirst_origin_contribution rooted occurrence)))
  · exact left_eq.trans right_eq.symm

theorem contributionMergeFirst_no_simultaneous_split
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0)
    (left right : (contributionMergeTargetLedger rooted).Entry)
    (origin_eq :
      ((contributionMergeFirstEvolution rooted occurrence).origin left).1 =
        ((contributionMergeFirstEvolution rooted occurrence).origin right).1) :
    IsEmpty
      (SourceNativeSplitCoverageAt
        (contributionMergeRestructuringLaw rooted) occurrence
        (contributionMergeFirstEvolution rooted occurrence)
        left right origin_eq × PLift (left ≠ right)) := by
  refine ⟨fun paired => ?_⟩
  exact paired.2.down
    (contributionMergeFirst_origin_injective
      rooted occurrence left right origin_eq)

/-! ## Exact restructuring certification -/

def contributionMergeFirstRestructuringCertification
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0) :
    ExactLedgerRestructuringCertificationAt
      (contributionMergeRestructuringLaw rooted) occurrence
      (contributionMergeFirstEvolution rooted occurrence) where
  split := fun left right origin_eq =>
    .identity
      (contributionMergeFirst_origin_injective
        rooted occurrence left right origin_eq)
  merge := by
    intro left right destination_eq
    generalize leftIndex_eq :
      contributionMergeInitialEntryIndex rooted left = leftIndex
    generalize rightIndex_eq :
      contributionMergeInitialEntryIndex rooted right = rightIndex
    have left_eq := contributionMergeFirstSourceEntryAt_index rooted left
    have right_eq := contributionMergeFirstSourceEntryAt_index rooted right
    rw [leftIndex_eq] at left_eq
    rw [rightIndex_eq] at right_eq
    subst left
    subst right
    revert destination_eq
    refine Fin.cases ?_ (fun leftTail => ?_) leftIndex
    · refine Fin.cases ?_ (fun rightTail => ?_) rightIndex
      · intro destination_eq
        exact .identity rfl
      · change Fin 2 at rightTail
        refine Fin.cases ?_ (fun rightLast => ?_) rightTail
        · intro destination_eq
          change SourceNativeMergeClassificationAt
            (contributionMergeRestructuringLaw rooted) occurrence
            (contributionMergeFirstEvolution rooted occurrence)
            (initialChildA rooted) (initialChildB rooted) destination_eq
          exact .merge (by
            simpa only [] using
              contributionMergeFirstCoverage rooted occurrence)
        · change Fin 1 at rightLast
          have rightLast_eq : rightLast = (0 : Fin 1) :=
            Subsingleton.elim _ _
          subst rightLast
          intro destination_eq
          exact False.elim
            (contributionMergeFirst_obstruction_destination_ne
              rooted occurrence destination_eq.symm)
    · change Fin 2 at leftTail
      refine Fin.cases ?_ (fun leftLast => ?_) leftTail
      · refine Fin.cases ?_ (fun rightTail => ?_) rightIndex
        · intro destination_eq
          change SourceNativeMergeClassificationAt
            (contributionMergeRestructuringLaw rooted) occurrence
            (contributionMergeFirstEvolution rooted occurrence)
            (initialChildB rooted) (initialChildA rooted) destination_eq
          exact .merge (by
            simpa only [] using
              contributionMergeFirstCoverageBA rooted occurrence)
        · change Fin 2 at rightTail
          refine Fin.cases ?_ (fun rightLast => ?_) rightTail
          · intro destination_eq
            exact .identity rfl
          · change Fin 1 at rightLast
            have rightLast_eq : rightLast = (0 : Fin 1) :=
              Subsingleton.elim _ _
            subst rightLast
            intro destination_eq
            exact False.elim
              (contributionMergeFirst_obstruction_destination_ne
                rooted occurrence
                ((contributionMergeFirst_children_repeatedDestination
                  rooted occurrence).trans destination_eq).symm)
      · change Fin 1 at leftLast
        have leftLast_eq : leftLast = (0 : Fin 1) := Subsingleton.elim _ _
        subst leftLast
        refine Fin.cases ?_ (fun rightTail => ?_) rightIndex
        · intro destination_eq
          exact False.elim
            (contributionMergeFirst_obstruction_destination_ne
              rooted occurrence destination_eq)
        · change Fin 2 at rightTail
          refine Fin.cases ?_ (fun rightLast => ?_) rightTail
          · intro destination_eq
            exact False.elim
              (contributionMergeFirst_obstruction_destination_ne
                rooted occurrence
                (destination_eq.trans
                  (contributionMergeFirst_children_repeatedDestination
                    rooted occurrence).symm))
          · change Fin 1 at rightLast
            have rightLast_eq : rightLast = (0 : Fin 1) :=
              Subsingleton.elim _ _
            subst rightLast
            intro destination_eq
            exact .identity rfl

def contributionMergeTargetIdentityCertification
    (rooted : RootedFailure)
    (current : Nat)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt
        (Nat.succ current)) :
    SourceNativeLedgerRestructuringCertificationAt
      (contributionMergeRestructuringLaw rooted)
      ((contributionMergeLedgerCompiler rooted).compile occurrence) := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  exact ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right origin_eq => origin_eq)
    (fun left right destination_eq => destination_eq)

def contributionMergeRestructuringCertification
    (rooted : RootedFailure)
    {current : (TargetV rooted).Current}
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt
        current) :
    SourceNativeLedgerRestructuringCertificationAt
      (contributionMergeRestructuringLaw rooted)
      ((contributionMergeLedgerCompiler rooted).compile occurrence) := by
  cases current with
  | zero =>
      rcases occurrence with ⟨indexedSupport, event⟩
      cases event.supportExact.down
      exact contributionMergeFirstRestructuringCertification rooted
        ⟨contributionMergeInitialSupport rooted, event⟩
  | succ current =>
      exact contributionMergeTargetIdentityCertification
        rooted current occurrence

def contributionMergeRestructuringCompiler
    (rooted : RootedFailure) :
    SourceNativeRestructuringLedgerCompiler
      (contributionMergeSource rooted) where
  ledgerCompiler := contributionMergeLedgerCompiler rooted
  restructuringLaw := contributionMergeRestructuringLaw rooted
  certifyRestructuring := contributionMergeRestructuringCertification rooted

def contributionMergeRestructuringSource
    (rooted : RootedFailure) :
    SourceNativeRestructuringLedgerSource
      (TargetN rooted) (TargetV rooted) where
  source := contributionMergeSource rooted
  compiler := contributionMergeRestructuringCompiler rooted

theorem contributionMergeCompiler_selects_exact_first_merge
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0) :
    (contributionMergeFirstRestructuringCertification
      rooted occurrence).merge
        (initialChildA rooted) (initialChildB rooted)
        (contributionMergeFirst_children_repeatedDestination
          rooted occurrence) =
      SourceNativeMergeClassificationAt.merge
        (contributionMergeFirstCoverage rooted occurrence) :=
  rfl

theorem contributionMergeFirst_exact_coverage
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0) :
    (sourceEntry : (contributionMergeInitialLedger rooted).Entry) →
    ((contributionMergeFirstEvolution rooted occurrence).destination
        sourceEntry).1 =
      ((contributionMergeFirstEvolution rooted occurrence).destination
        (initialChildA rooted)).1 →
    (contributionMergeRestructuringLaw rooted).obligationAt
        occurrence sourceEntry ∈
      (contributionMergeFirstCoverage rooted occurrence).receipt.parents :=
  (contributionMergeFirstCoverage rooted occurrence).covers_source

def contributionMergeFirst_no_phantom
    (rooted : RootedFailure)
    (occurrence :
      (contributionMergeSource rooted).toRootSource.actual.OccurrenceAt 0) :=
  (contributionMergeFirstCoverage rooted occurrence).no_phantom_parent

end
end M14SourceGeneratedContributionMergeRestructuring
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeRestructuring.contributionMergeFirstCoverage
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeRestructuring.contributionMergeFirstRestructuringCertification
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeRestructuring.contributionMergeCompiler_selects_exact_first_merge
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionMergeRestructuring.contributionMergeFirst_no_simultaneous_split

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Lifecycle.SourceGeneratedLossAllocationLifecycle

/-!
# M14 source-generated loss-allocation restructuring

The exact three-row first write is presented to the existing responsibility
lifecycle without a loss-share carrier.  Parent and children retain the same
world responsibility and claim.  The only child distinction is the existing
proof-relevant exchange `Leg` admission, whose bearer is read from the
zero-choice C4/C5 loss-allocation material.

The source-fixed compiler classifies the repeated parent origin by one exact
`SplitReceipt`; complete target coverage and the strict `2 -> 1` debits are
checked against the same whole-ledger evolution.  Merge authority remains
empty in this first-write fixture.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedLossAllocationRestructuring

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ObstructionGeneratedMinimalCoface TypedSemanticWorldNetworkU8
open ComplementObservation Lifecycle Universal Relations Exchange
open M3FiniteExchangeFixture
open M14SourceGeneratedClearingBackstopActivation
open M14SourceClearingBackstopCreditStanding
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedLossAllocationWorld
open M14SourceGeneratedLossAllocationCompiler

variable
    {OldV : ConstructiveRoot.Vocabulary}
    {oldWorld : SourceNativeAuthoritativeRootClosure OldN OldV}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus OldN}
    {oldTheory : TheoryState OldN}
    {support : OldN.Support}
    {obstruction : OldN.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}

local notation "RootedFailure" => RootedActualExpressibilityFailureAt
  oldWorld oldVisit U7 failure
/-! ## Source-fixed split vocabulary and law -/

def lossAllocationRestructuringVocabulary (rooted : RootedFailure) :
    RestructuringVocabulary where
  base := LossLifecycleV rooted
  DescendantAt := fun _ parentIncidence parentContent
      childIncidence childContent =>
    PLift (parentIncidence = childIncidence) ×
      PLift (parentContent = childContent)
  SplitCoverageAt := fun _ parentContent childContents =>
    PLift (childContents = [parentContent, parentContent])
  MergeCoverageAt := fun _ _ _ => PEmpty
  LocalDischargePreservedAt := fun _ parentContent childContent =>
    PLift (parentContent = childContent)
  RenameAt := fun _ oldContent newContent => PLift (oldContent = newContent)

abbrev LossRestructuringV (rooted : RootedFailure) :=
  lossAllocationRestructuringVocabulary rooted

def lossAllocationRestructuringLaw (rooted : RootedFailure) :
    SourceNativeLedgerRestructuringLaw (lossAllocationSource rooted) where
  vocabulary := LossRestructuringV rooted
  sourceEventAt := fun occurrence =>
    ((lossAllocationSource rooted).toRootSource.account.supportOf occurrence,
      occurrence.2.materialWitness)
  obligationAt := by
    intro current occurrence indexedSupport entry
    exact lossAllocationObligationAt rooted occurrence.2.materialWitness entry
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
    exact lossAllocationObligationAt_injective rooted
      occurrence.2.materialWitness obligation_eq

theorem lossAllocationLifecycle_source_reads_actual_material
    (rooted : RootedFailure)
    {current : (LossV rooted).Current}
    (occurrence :
      (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt current)
    {indexedSupport : (LossN rooted).Support}
    (entry : OpenResponsibilityAt (LossN rooted) indexedSupport) :
    (lossAllocationRestructuringLaw rooted).sourceEventAt occurrence =
        ((lossAllocationSource rooted).toRootSource.account.supportOf occurrence,
          occurrence.2.materialWitness) ∧
      ((lossAllocationRestructuringLaw rooted).obligationAt occurrence entry
        ).admission.sourceEvent =
        (indexedSupport, occurrence.2.materialWitness) ∧
      sourceGeneratedLossAllocationMaterial.activationSeed =
        sourceGeneratedClearingBackstopExactSeed ∧
      HEq sourceGeneratedLossAllocationMaterial.standing
        sourceGeneratedClearingBackstopCreditStanding :=
  ⟨rfl, rfl, occurrence.2.materialWitness.activationSeedExact,
    occurrence.2.materialWitness.standingExact⟩

theorem lossAllocationChildren_obligations_distinct
    (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) :
    (lossAllocationRestructuringLaw rooted).obligationAt occurrence
        (lossAllocationTargetChildA rooted) ≠
      (lossAllocationRestructuringLaw rooted).obligationAt occurrence
        (lossAllocationTargetChildB rooted) :=
  fun obligation_eq =>
    lossAllocationChildren_distinct rooted
      ((lossAllocationRestructuringLaw rooted).obligationAt_injective occurrence
        obligation_eq)

/-! ## Exact first-write split receipt and complete coverage -/

theorem lossAllocationInitialObstruction_ne_parent
    (rooted : RootedFailure) :
    lossAllocationInitialObstruction rooted ≠
      lossAllocationInitialParent rooted := by
  intro equality
  have responsibility_eq := congrArg Sigma.fst equality
  exact nomatch responsibility_eq

theorem lossAllocationTargetEntry_cases
    (rooted : RootedFailure)
    (entry : (lossAllocationTargetLedger rooted).Entry) :
    entry = lossAllocationTargetChildA rooted ∨
      entry = lossAllocationTargetChildB rooted ∨
      entry = lossAllocationTargetObstruction rooted := by
  rcases entry with ⟨responsibility, isOpen⟩
  cases responsibility with
  | inl oldResponsibility =>
      cases oldResponsibility
      rcases isOpen with ⟨leg, admitted⟩
      rcases admitted with admitted | admitted
      · cases admitted
        exact .inl rfl
      · cases admitted
        exact .inr (.inl rfl)
  | inr responsibilityDirection =>
      cases isOpen
      exact .inr (.inr rfl)

def lossAllocationParentObligation (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) : (LossRestructuringV rooted).Obligation :=
  (lossAllocationRestructuringLaw rooted).obligationAt occurrence
    (lossAllocationInitialParent rooted)

def lossAllocationChildAObligation (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) : (LossRestructuringV rooted).Obligation :=
  (lossAllocationRestructuringLaw rooted).obligationAt occurrence
    (lossAllocationTargetChildA rooted)

def lossAllocationChildBObligation (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) : (LossRestructuringV rooted).Obligation :=
  (lossAllocationRestructuringLaw rooted).obligationAt occurrence
    (lossAllocationTargetChildB rooted)

def lossAllocationReceiptChildAt (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) : Fin 2 → (LossRestructuringV rooted).Obligation :=
  Fin.cases
    ((lossAllocationRestructuringLaw rooted).obligationAt occurrence
      (lossAllocationTargetChildA rooted))
    (fun _ => (lossAllocationRestructuringLaw rooted).obligationAt occurrence
      (lossAllocationTargetChildB rooted))

def lossAllocationReceiptChildIndexAt
    (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0)
    (child : (LossRestructuringV rooted).Obligation)
    (member : child ∈
      [(lossAllocationRestructuringLaw rooted).obligationAt occurrence
          (lossAllocationTargetChildA rooted),
        (lossAllocationRestructuringLaw rooted).obligationAt occurrence
          (lossAllocationTargetChildB rooted)]) :
    { index : Fin 2 //
      lossAllocationReceiptChildAt rooted occurrence index = child } := by
  let indexed := List.get_of_mem member
  let index := Classical.choose indexed
  have index_eq := Classical.choose_spec indexed
  change Fin 2 at index
  change
    [(lossAllocationRestructuringLaw rooted).obligationAt occurrence
        (lossAllocationTargetChildA rooted),
      (lossAllocationRestructuringLaw rooted).obligationAt occurrence
        (lossAllocationTargetChildB rooted)].get index = child at index_eq
  have get_eq :
      [(lossAllocationRestructuringLaw rooted).obligationAt occurrence
          (lossAllocationTargetChildA rooted),
        (lossAllocationRestructuringLaw rooted).obligationAt occurrence
          (lossAllocationTargetChildB rooted)].get index =
        lossAllocationReceiptChildAt rooted occurrence index := by
    refine Fin.cases rfl (fun tail => ?_) index
    change Fin 1 at tail
    have tail_eq : tail = (0 : Fin 1) := Subsingleton.elim _ _
    subst tail
    rfl
  exact ⟨index, get_eq.symm.trans index_eq⟩

theorem lossAllocationFirst_parentContent_eq_childA
    (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) :
    ((lossAllocationRestructuringLaw rooted).obligationAt occurrence
      ((lossAllocationFirstEvolution rooted occurrence).origin
        (lossAllocationTargetChildA rooted)).1).content =
      ((lossAllocationRestructuringLaw rooted).obligationAt occurrence
        (lossAllocationTargetChildA rooted)).content := by
  rw [lossAllocationFirst_origin_childA]
  rfl

theorem lossAllocationFirst_parentContent_eq_childB
    (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) :
    ((lossAllocationRestructuringLaw rooted).obligationAt occurrence
      ((lossAllocationFirstEvolution rooted occurrence).origin
        (lossAllocationTargetChildA rooted)).1).content =
      ((lossAllocationRestructuringLaw rooted).obligationAt occurrence
        (lossAllocationTargetChildB rooted)).content := by
  rw [lossAllocationFirst_origin_childA]
  rfl

theorem lossAllocationFirst_parentBContent_eq_childA
    (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) :
    ((lossAllocationRestructuringLaw rooted).obligationAt occurrence
      ((lossAllocationFirstEvolution rooted occurrence).origin
        (lossAllocationTargetChildB rooted)).1).content =
      ((lossAllocationRestructuringLaw rooted).obligationAt occurrence
        (lossAllocationTargetChildA rooted)).content := by
  rw [lossAllocationFirst_origin_childB]
  rfl

theorem lossAllocationFirst_parentBContent_eq_childB
    (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) :
    ((lossAllocationRestructuringLaw rooted).obligationAt occurrence
      ((lossAllocationFirstEvolution rooted occurrence).origin
        (lossAllocationTargetChildB rooted)).1).content =
      ((lossAllocationRestructuringLaw rooted).obligationAt occurrence
        (lossAllocationTargetChildB rooted)).content := by
  rw [lossAllocationFirst_origin_childB]
  rfl

def lossAllocationFirstSplitReceipt (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) :
    SplitReceipt (lossAllocationRestructuringLaw rooted).vocabulary
      ((lossAllocationRestructuringLaw rooted).obligationAt occurrence
        ((lossAllocationFirstEvolution rooted occurrence).origin
          (lossAllocationTargetChildA rooted)).1) where
  sourceEvent :=
    (lossAllocationInitialSupport rooted, occurrence.2.materialWitness)
  sourceOwnership := by
    rcases occurrence with ⟨indexedSupport, event⟩
    cases event.supportExact.down
    exact ⟨rfl, rfl⟩
  children :=
    [(lossAllocationRestructuringLaw rooted).obligationAt occurrence
        (lossAllocationTargetChildA rooted),
      (lossAllocationRestructuringLaw rooted).obligationAt occurrence
        (lossAllocationTargetChildB rooted)]
  children_nonempty := by simp
  coverage := by
    apply PLift.up
    apply congrArg₂ List.cons
    · exact (lossAllocationFirst_parentContent_eq_childA
        rooted occurrence).symm
    · apply congrArg₂ List.cons
      · exact (lossAllocationFirst_parentContent_eq_childB
          rooted occurrence).symm
      · rfl
  descendant := by
    intro child member
    rcases lossAllocationReceiptChildIndexAt rooted occurrence child member with
      ⟨index, child_eq⟩
    subst child
    refine Fin.cases ?_ (fun tail => ?_) index
    · exact ⟨PLift.up rfl,
        PLift.up (lossAllocationFirst_parentContent_eq_childA
          rooted occurrence)⟩
    · change Fin 1 at tail
      have tail_eq : tail = (0 : Fin 1) := Subsingleton.elim _ _
      subst tail
      exact ⟨PLift.up rfl,
        PLift.up (lossAllocationFirst_parentContent_eq_childB
          rooted occurrence)⟩
  anchorTransport := fun _ _ => SourceAnchorTransport.refl _
  lineage := fun _ _ => rfl
  localDischarge := by
    intro child member
    rcases lossAllocationReceiptChildIndexAt rooted occurrence child member with
      ⟨index, child_eq⟩
    subst child
    refine Fin.cases ?_ (fun tail => ?_) index
    · exact PLift.up
        (lossAllocationFirst_parentContent_eq_childA rooted occurrence)
    · change Fin 1 at tail
      have tail_eq : tail = (0 : Fin 1) := Subsingleton.elim _ _
      subst tail
      exact PLift.up
        (lossAllocationFirst_parentContent_eq_childB rooted occurrence)

theorem lossAllocationFirstOriginEq (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) :
    ((lossAllocationFirstEvolution rooted occurrence).origin
        (lossAllocationTargetChildA rooted)).1 =
      ((lossAllocationFirstEvolution rooted occurrence).origin
        (lossAllocationTargetChildB rooted)).1 := by
  rw [lossAllocationFirst_origin_childA,
    lossAllocationFirst_origin_childB]

def lossAllocationFirstSplitCoverage (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) :
    SourceNativeSplitCoverageAt (lossAllocationRestructuringLaw rooted)
      occurrence (lossAllocationFirstEvolution rooted occurrence)
      (lossAllocationTargetChildA rooted)
      (lossAllocationTargetChildB rooted)
      (lossAllocationFirstOriginEq rooted occurrence) := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  apply SourceNativeSplitCoverageAt.ofReceipt
    (receipt := lossAllocationFirstSplitReceipt rooted
      ⟨lossAllocationInitialSupport rooted, event⟩)
  · rfl
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  · intro targetEntry targetOrigin_eq
    rcases lossAllocationTargetEntry_cases rooted targetEntry with
      target_eq | target_eq | target_eq
    · subst targetEntry
      exact List.mem_cons_self
    · subst targetEntry
      exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    · subst targetEntry
      have obstructionOrigin :
          ((lossAllocationFirstEvolution rooted
            ⟨lossAllocationInitialSupport rooted, event⟩).origin
              (lossAllocationTargetObstruction rooted)).1 =
            lossAllocationInitialObstruction rooted := by
        rfl
      have childOrigin :
          ((lossAllocationFirstEvolution rooted
            ⟨lossAllocationInitialSupport rooted, event⟩).origin
              (lossAllocationTargetChildA rooted)).1 =
            lossAllocationInitialParent rooted := by
        rfl
      exact False.elim (lossAllocationInitialObstruction_ne_parent rooted <|
        obstructionOrigin.symm.trans (targetOrigin_eq.trans childOrigin))
  · intro targetEntry targetOrigin_eq
    rcases lossAllocationTargetEntry_cases rooted targetEntry with
      target_eq | target_eq | target_eq
    · subst targetEntry
      calc
        (lossAllocationTargetChildA rooted).progressBudget = 1 := rfl
        _ < 2 := Nat.one_lt_two
        _ = ((lossAllocationFirstEvolution rooted
          ⟨lossAllocationInitialSupport rooted, event⟩).origin
            (lossAllocationTargetChildA rooted)).1.progressBudget := by
              rfl
    · subst targetEntry
      calc
        (lossAllocationTargetChildB rooted).progressBudget = 1 := rfl
        _ < 2 := Nat.one_lt_two
        _ = ((lossAllocationFirstEvolution rooted
          ⟨lossAllocationInitialSupport rooted, event⟩).origin
            (lossAllocationTargetChildA rooted)).1.progressBudget := by
              rfl
    · subst targetEntry
      have obstructionOrigin :
          ((lossAllocationFirstEvolution rooted
            ⟨lossAllocationInitialSupport rooted, event⟩).origin
              (lossAllocationTargetObstruction rooted)).1 =
            lossAllocationInitialObstruction rooted := by
        rfl
      have childOrigin :
          ((lossAllocationFirstEvolution rooted
            ⟨lossAllocationInitialSupport rooted, event⟩).origin
              (lossAllocationTargetChildA rooted)).1 =
            lossAllocationInitialParent rooted := by
        rfl
      exact False.elim (lossAllocationInitialObstruction_ne_parent rooted <|
        obstructionOrigin.symm.trans (targetOrigin_eq.trans childOrigin))
  · intro child member
    let indexed := List.get_of_mem member
    let index := Classical.choose indexed
    have index_eq := Classical.choose_spec indexed
    change Fin 2 at index
    change
      [lossAllocationChildAObligation rooted
          ⟨lossAllocationInitialSupport rooted, event⟩,
        lossAllocationChildBObligation rooted
          ⟨lossAllocationInitialSupport rooted, event⟩].get index = child at index_eq
    let targetAt : Fin 2 → (lossAllocationTargetLedger rooted).Entry :=
      Fin.cases (lossAllocationTargetChildA rooted)
        (fun _ => lossAllocationTargetChildB rooted)
    have indexedObligation_eq :
        [lossAllocationChildAObligation rooted
            ⟨lossAllocationInitialSupport rooted, event⟩,
          lossAllocationChildBObligation rooted
            ⟨lossAllocationInitialSupport rooted, event⟩].get index =
          (lossAllocationRestructuringLaw rooted).obligationAt
            ⟨lossAllocationInitialSupport rooted, event⟩
              (targetAt index) := by
      refine Fin.cases rfl (fun tail => ?_) index
      change Fin 1 at tail
      have tail_eq : tail = (0 : Fin 1) := Subsingleton.elim _ _
      subst tail
      rfl
    have targetObligation_eq :
        (lossAllocationRestructuringLaw rooted).obligationAt
            ⟨lossAllocationInitialSupport rooted, event⟩ (targetAt index) =
          child := by
      exact indexedObligation_eq.symm.trans index_eq
    have targetOrigin_eq :
        ((lossAllocationFirstEvolution rooted
          ⟨lossAllocationInitialSupport rooted, event⟩).origin
            (targetAt index)).1 =
          ((lossAllocationFirstEvolution rooted
            ⟨lossAllocationInitialSupport rooted, event⟩).origin
              (lossAllocationTargetChildA rooted)).1 := by
      refine Fin.cases rfl (fun tail => ?_) index
      change Fin 1 at tail
      have tail_eq : tail = (0 : Fin 1) := Subsingleton.elim _ _
      subst tail
      exact (lossAllocationFirstOriginEq rooted
        ⟨lossAllocationInitialSupport rooted, event⟩).symm
    exact ⟨targetAt index, targetObligation_eq, targetOrigin_eq⟩

theorem lossAllocationFirstSplitCoverage_exact_bearers
    (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) :
    ((lossAllocationFirstSplitReceipt rooted occurrence).children[0]?).map
        AdmittedObligation.bearer =
        some (sourceGeneratedLossAllocationMaterial.childBearerAt .a) ∧
      ((lossAllocationFirstSplitReceipt rooted occurrence).children[1]?).map
        AdmittedObligation.bearer =
        some (sourceGeneratedLossAllocationMaterial.childBearerAt .b) := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  exact ⟨rfl, rfl⟩

def lossAllocationFirstSplitReceiptFromChildB (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) :
    SplitReceipt (lossAllocationRestructuringLaw rooted).vocabulary
      ((lossAllocationRestructuringLaw rooted).obligationAt occurrence
        ((lossAllocationFirstEvolution rooted occurrence).origin
          (lossAllocationTargetChildB rooted)).1) where
  sourceEvent :=
    (lossAllocationInitialSupport rooted, occurrence.2.materialWitness)
  sourceOwnership := by
    rcases occurrence with ⟨indexedSupport, event⟩
    cases event.supportExact.down
    exact ⟨rfl, rfl⟩
  children :=
    [(lossAllocationRestructuringLaw rooted).obligationAt occurrence
        (lossAllocationTargetChildA rooted),
      (lossAllocationRestructuringLaw rooted).obligationAt occurrence
        (lossAllocationTargetChildB rooted)]
  children_nonempty := by simp
  coverage := by
    apply PLift.up
    apply congrArg₂ List.cons
    · exact (lossAllocationFirst_parentBContent_eq_childA
        rooted occurrence).symm
    · apply congrArg₂ List.cons
      · exact (lossAllocationFirst_parentBContent_eq_childB
          rooted occurrence).symm
      · rfl
  descendant := by
    intro child member
    rcases lossAllocationReceiptChildIndexAt rooted occurrence child member with
      ⟨index, child_eq⟩
    subst child
    refine Fin.cases ?_ (fun tail => ?_) index
    · exact ⟨PLift.up rfl,
        PLift.up (lossAllocationFirst_parentBContent_eq_childA
          rooted occurrence)⟩
    · change Fin 1 at tail
      have tail_eq : tail = (0 : Fin 1) := Subsingleton.elim _ _
      subst tail
      exact ⟨PLift.up rfl,
        PLift.up (lossAllocationFirst_parentBContent_eq_childB
          rooted occurrence)⟩
  anchorTransport := fun _ _ => SourceAnchorTransport.refl _
  lineage := fun _ _ => rfl
  localDischarge := by
    intro child member
    rcases lossAllocationReceiptChildIndexAt rooted occurrence child member with
      ⟨index, child_eq⟩
    subst child
    refine Fin.cases ?_ (fun tail => ?_) index
    · exact PLift.up
        (lossAllocationFirst_parentBContent_eq_childA rooted occurrence)
    · change Fin 1 at tail
      have tail_eq : tail = (0 : Fin 1) := Subsingleton.elim _ _
      subst tail
      exact PLift.up
        (lossAllocationFirst_parentBContent_eq_childB rooted occurrence)

def lossAllocationFirstSplitCoverageSwapped (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) :
    SourceNativeSplitCoverageAt (lossAllocationRestructuringLaw rooted)
      occurrence (lossAllocationFirstEvolution rooted occurrence)
      (lossAllocationTargetChildB rooted)
      (lossAllocationTargetChildA rooted)
      (lossAllocationFirstOriginEq rooted occurrence).symm := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  let canonical := lossAllocationFirstSplitCoverage rooted
    ⟨lossAllocationInitialSupport rooted, event⟩
  apply SourceNativeSplitCoverageAt.ofReceipt
    (receipt := lossAllocationFirstSplitReceiptFromChildB rooted
      ⟨lossAllocationInitialSupport rooted, event⟩)
  · rfl
  · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  · exact List.mem_cons_self
  · intro targetEntry targetOrigin_eq
    exact canonical.covers_target targetEntry (by
      exact targetOrigin_eq.trans
        (lossAllocationFirstOriginEq rooted
          ⟨lossAllocationInitialSupport rooted, event⟩).symm)
  · intro targetEntry targetOrigin_eq
    exact canonical.childProgressBudget_strictlyDebited targetEntry (by
      exact targetOrigin_eq.trans
        (lossAllocationFirstOriginEq rooted
          ⟨lossAllocationInitialSupport rooted, event⟩).symm)
  · intro child member
    rcases canonical.no_phantom_child child member with
      ⟨targetEntry, obligation_eq, targetOrigin_eq⟩
    exact ⟨targetEntry, obligation_eq,
      targetOrigin_eq.trans
        (lossAllocationFirstOriginEq rooted
          ⟨lossAllocationInitialSupport rooted, event⟩)⟩

theorem lossAllocationInitialEntry_cases
    (rooted : RootedFailure)
    (entry : (lossAllocationInitialLedger rooted).Entry) :
    entry = lossAllocationInitialParent rooted ∨
      entry = lossAllocationInitialObstruction rooted := by
  rcases entry with ⟨responsibility, isOpen⟩
  cases responsibility with
  | inl oldResponsibility =>
      cases oldResponsibility
      cases isOpen
      exact .inl rfl
  | inr responsibilityDirection =>
      cases isOpen
      exact .inr rfl

theorem lossAllocationTargetObstruction_ne_childA
    (rooted : RootedFailure) :
    lossAllocationTargetObstruction rooted ≠
      lossAllocationTargetChildA rooted := by
  intro equality
  have responsibility_eq := congrArg Sigma.fst equality
  exact nomatch responsibility_eq

@[simp] theorem lossAllocationFirstTargetEntryAt_zero
    (rooted : RootedFailure) :
    lossAllocationFirstTargetEntryAt rooted ⟨0, by decide⟩ =
      lossAllocationTargetChildA rooted :=
  rfl

@[simp] theorem lossAllocationFirstTargetEntryAt_one
    (rooted : RootedFailure) :
    lossAllocationFirstTargetEntryAt rooted ⟨1, by decide⟩ =
      lossAllocationTargetChildB rooted :=
  rfl

@[simp] theorem lossAllocationFirstTargetEntryAt_two
    (rooted : RootedFailure) :
    lossAllocationFirstTargetEntryAt rooted ⟨2, by decide⟩ =
      lossAllocationTargetObstruction rooted :=
  rfl

def lossAllocationFirstRestructuringCertification
    (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) :
    ExactLedgerRestructuringCertificationAt
      (lossAllocationRestructuringLaw rooted) occurrence
      (lossAllocationFirstEvolution rooted occurrence) where
  split := by
    intro left right origin_eq
    generalize leftIndex_eq :
      lossAllocationTargetEntryIndex rooted left = leftIndex
    generalize rightIndex_eq :
      lossAllocationTargetEntryIndex rooted right = rightIndex
    have left_eq := lossAllocationFirstTargetEntryAt_index rooted left
    have right_eq := lossAllocationFirstTargetEntryAt_index rooted right
    rw [leftIndex_eq] at left_eq
    rw [rightIndex_eq] at right_eq
    subst left
    subst right
    revert origin_eq
    refine Fin.cases ?_ (fun leftTail => ?_) leftIndex
    · refine Fin.cases ?_ (fun rightTail => ?_) rightIndex
      · intro origin_eq
        exact .identity rfl
      · change Fin 2 at rightTail
        refine Fin.cases ?_ (fun rightLast => ?_) rightTail
        · intro origin_eq
          change SourceNativeSplitClassificationAt
            (lossAllocationRestructuringLaw rooted) occurrence
            (lossAllocationFirstEvolution rooted occurrence)
            (lossAllocationTargetChildA rooted)
            (lossAllocationTargetChildB rooted) origin_eq
          exact .split (by
            simpa only [] using
              lossAllocationFirstSplitCoverage rooted occurrence)
        · change Fin 1 at rightLast
          have rightLast_eq : rightLast = (0 : Fin 1) :=
            Subsingleton.elim _ _
          subst rightLast
          intro origin_eq
          change SourceNativeSplitClassificationAt
            (lossAllocationRestructuringLaw rooted) occurrence
            (lossAllocationFirstEvolution rooted occurrence)
            (lossAllocationTargetChildA rooted)
            (lossAllocationTargetObstruction rooted) origin_eq
          exact False.elim
            (lossAllocationInitialObstruction_ne_parent rooted <|
              (lossAllocationFirst_origin_obstruction rooted occurrence).symm.trans
                (origin_eq.symm.trans
                  (lossAllocationFirst_origin_childA rooted occurrence)))
    · change Fin 2 at leftTail
      refine Fin.cases ?_ (fun leftLast => ?_) leftTail
      · refine Fin.cases ?_ (fun rightTail => ?_) rightIndex
        · intro origin_eq
          change SourceNativeSplitClassificationAt
            (lossAllocationRestructuringLaw rooted) occurrence
            (lossAllocationFirstEvolution rooted occurrence)
            (lossAllocationTargetChildB rooted)
            (lossAllocationTargetChildA rooted) origin_eq
          exact .split (by
            simpa only [] using
              lossAllocationFirstSplitCoverageSwapped rooted occurrence)
        · change Fin 2 at rightTail
          refine Fin.cases ?_ (fun rightLast => ?_) rightTail
          · intro origin_eq
            exact .identity rfl
          · change Fin 1 at rightLast
            have rightLast_eq : rightLast = (0 : Fin 1) :=
              Subsingleton.elim _ _
            subst rightLast
            intro origin_eq
            change SourceNativeSplitClassificationAt
              (lossAllocationRestructuringLaw rooted) occurrence
              (lossAllocationFirstEvolution rooted occurrence)
              (lossAllocationTargetChildB rooted)
              (lossAllocationTargetObstruction rooted) origin_eq
            exact False.elim
              (lossAllocationInitialObstruction_ne_parent rooted <|
                (lossAllocationFirst_origin_obstruction
                  rooted occurrence).symm.trans
                  (origin_eq.symm.trans
                    (lossAllocationFirst_origin_childB rooted occurrence)))
      · change Fin 1 at leftLast
        have leftLast_eq : leftLast = (0 : Fin 1) := Subsingleton.elim _ _
        subst leftLast
        refine Fin.cases ?_ (fun rightTail => ?_) rightIndex
        · intro origin_eq
          change SourceNativeSplitClassificationAt
            (lossAllocationRestructuringLaw rooted) occurrence
            (lossAllocationFirstEvolution rooted occurrence)
            (lossAllocationTargetObstruction rooted)
            (lossAllocationTargetChildA rooted) origin_eq
          exact False.elim
            (lossAllocationInitialObstruction_ne_parent rooted <|
              (lossAllocationFirst_origin_obstruction rooted occurrence).symm.trans
                (origin_eq.trans
                  (lossAllocationFirst_origin_childA rooted occurrence)))
        · change Fin 2 at rightTail
          refine Fin.cases ?_ (fun rightLast => ?_) rightTail
          · intro origin_eq
            change SourceNativeSplitClassificationAt
              (lossAllocationRestructuringLaw rooted) occurrence
              (lossAllocationFirstEvolution rooted occurrence)
              (lossAllocationTargetObstruction rooted)
              (lossAllocationTargetChildB rooted) origin_eq
            exact False.elim
              (lossAllocationInitialObstruction_ne_parent rooted <|
                (lossAllocationFirst_origin_obstruction
                  rooted occurrence).symm.trans
                  (origin_eq.trans
                    (lossAllocationFirst_origin_childB rooted occurrence)))
          · change Fin 1 at rightLast
            have rightLast_eq : rightLast = (0 : Fin 1) :=
              Subsingleton.elim _ _
            subst rightLast
            intro origin_eq
            exact .identity rfl
  merge := by
    rintro ⟨leftResponsibility, leftOpen⟩
      ⟨rightResponsibility, rightOpen⟩ destination_eq
    cases leftResponsibility with
    | inl leftOld =>
        cases leftOld
        cases leftOpen
        cases rightResponsibility with
        | inl rightOld =>
            cases rightOld
            cases rightOpen
            exact .identity rfl
        | inr rightDirection =>
            cases rightOpen
            exact False.elim (lossAllocationTargetObstruction_ne_childA rooted <|
              (lossAllocationFirst_destination_obstruction rooted occurrence).symm.trans
                (destination_eq.symm.trans
                  (lossAllocationFirst_destination_parent rooted occurrence)))
    | inr leftDirection =>
        cases leftOpen
        cases rightResponsibility with
        | inl rightOld =>
            cases rightOld
            cases rightOpen
            exact False.elim (lossAllocationTargetObstruction_ne_childA rooted <|
              (lossAllocationFirst_destination_obstruction rooted occurrence).symm.trans
                (destination_eq.trans
                  (lossAllocationFirst_destination_parent rooted occurrence)))
        | inr rightDirection =>
            cases rightOpen
            exact .identity rfl

def lossAllocationTargetIdentityCertification
    (rooted : RootedFailure)
    (current : Nat)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      (Nat.succ current)) :
    SourceNativeLedgerRestructuringCertificationAt
      (lossAllocationRestructuringLaw rooted)
      ((lossAllocationLedgerCompiler rooted).compile occurrence) := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  exact ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right origin_eq => by
      exact origin_eq)
    (fun left right destination_eq => by
      exact destination_eq)

def lossAllocationRestructuringCertification
    (rooted : RootedFailure)
    {current : (LossV rooted).Current}
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      current) :
    SourceNativeLedgerRestructuringCertificationAt
      (lossAllocationRestructuringLaw rooted)
      ((lossAllocationLedgerCompiler rooted).compile occurrence) := by
  cases current with
  | zero =>
      rcases occurrence with ⟨indexedSupport, event⟩
      cases event.supportExact.down
      exact lossAllocationFirstRestructuringCertification rooted
        ⟨lossAllocationInitialSupport rooted, event⟩
  | succ current =>
      exact lossAllocationTargetIdentityCertification rooted current occurrence

def lossAllocationRestructuringCompiler (rooted : RootedFailure) :
    SourceNativeRestructuringLedgerCompiler
      (lossAllocationSource rooted) where
  ledgerCompiler := lossAllocationLedgerCompiler rooted
  restructuringLaw := lossAllocationRestructuringLaw rooted
  certifyRestructuring := lossAllocationRestructuringCertification rooted

def lossAllocationRestructuringSource (rooted : RootedFailure) :
    SourceNativeRestructuringLedgerSource (LossN rooted) (LossV rooted) where
  source := lossAllocationSource rooted
  compiler := lossAllocationRestructuringCompiler rooted

theorem lossAllocationCompiler_selects_exact_first_split
    (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) :
    (lossAllocationFirstRestructuringCertification rooted occurrence).split
        (lossAllocationTargetChildA rooted)
        (lossAllocationTargetChildB rooted)
        (lossAllocationFirstOriginEq rooted occurrence) =
      SourceNativeSplitClassificationAt.split
        (lossAllocationFirstSplitCoverage rooted occurrence) :=
  rfl

end
end M14SourceGeneratedLossAllocationRestructuring
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedLossAllocationRestructuring.lossAllocationRestructuringLaw
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedLossAllocationRestructuring.lossAllocationChildren_obligations_distinct
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedLossAllocationRestructuring.lossAllocationLifecycle_source_reads_actual_material

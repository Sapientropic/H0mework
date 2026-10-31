import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalU8RevisedLedger
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ReflexiveClaimLifecycle
import H0mework.Foundation.Inquiry.RootRicherCofaceRestructuringKernelSource

/-!
# Unique richer revised living world for the joint U8 fixture

The established M9 revised-world facade is upgraded in place to the
source-generated loss-allocation world.  Its first actual occurrence has the
translated old parent and canonical obstruction row; its exact first compiler
image generates the two existing-leg continuations plus obstruction
continuity.  The same root retains inquiry/answer and claim lifecycle
projections at Nat visits `0` and `1`.

The phase-`true` old-face supports belong only to the total world
representation; the emitter never selects them.  No-dormant initial coverage
and target-origin coverage below quantify the two actual compiler ledgers and
therefore prevent those representation faces from becoming hidden rows.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M9ProofCarryingRenewalU8RevisedWorld

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open ConstructiveRoot.TypedSemanticWorldNetworkU8
open ConstructiveRoot.SourceGeneratedRicherCofaceRestructuring
open M9ProofCarryingRenewalInquiryRoot
open M9ProofCarryingRenewalU8Failure
open M9ProofCarryingRenewalU8RevisedLedger
open M13ReflexiveClaimLifecycleFixture
open M3ExchangeSettlementPriceRegression
open M14ClearingConsumerDeath
open M14SourceGeneratedClearingBackstopActivation
open M14SourceClearingBackstopCreditStanding
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedLossAllocationWorld
open M14SourceGeneratedLossAllocationCompiler
open M14SourceGeneratedLossAllocationRestructuring

abbrev N := M9ProofCarryingRenewalU8Failure.N
abbrev NewNAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :=
  M9ProofCarryingRenewalU8RevisedLedger.NewNAt visit
abbrev NewVAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :=
  M9ProofCarryingRenewalU8RevisedLedger.NewVAt visit

def revisedDefaultEntryAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot)
    (support : (NewNAt visit).Support) :
    OpenResponsibilityAt (NewNAt visit) support := by
  rcases support with ⟨worldSupport, phase⟩
  cases worldSupport with
  | inl oldSupport =>
      cases phase <;> cases oldSupport <;> exact ⟨.inl (), ()⟩
  | inr direction =>
      cases direction
      cases phase with
      | false => exact oldRevisedEntryAt visit
      | true => exact revisedTargetObstructionAt visit

def revisedU7At
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    U7ProducerCalculus (NewNAt visit) where
  DemandAt := fun _ => Unit
  generateDemand := fun _ => ()

def revisedU7SourceAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    U7ActualSuccessorSource (NewNAt visit) (revisedU7At visit) where
  EventAt := SourceGeneratedU7DemandAt (revisedU7At visit)
  emit := fun obstruction => .canonical obstruction
  demandGeneratedAt := fun event => event
  demandEntryAt := fun {support} {_obstruction} {_demand} _ =>
    revisedDefaultEntryAt visit support

def revisedCalculusAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    U7ObstructionEvolutionCalculus (NewNAt visit) (revisedU7At visit) where
  source := revisedU7SourceAt visit
  compile := by
    intro indexedSupport indexedObstruction demand event
    rcases indexedSupport with ⟨worldSupport, phase⟩
    cases worldSupport with
    | inl oldSupport =>
        exact
          { disposition := .redirected ⟨(), rfl⟩
            demandEntryDisposition :=
              ⟨LedgerEntryEvolutionAt.transferred () rfl rfl
                (Nat.le_refl _), rfl⟩ }
    | inr direction =>
        cases direction
        exact
          { disposition := .redirected
              ⟨GeneratedMinimalCofaceAt.CofaceTargetDispositionAt.ofTarget (),
                rfl⟩
            demandEntryDisposition :=
              ⟨LedgerEntryEvolutionAt.transferred
                (GeneratedMinimalCofaceAt.CofaceTargetDispositionAt.ofTarget ())
                rfl rfl (Nat.le_refl _), rfl⟩ }

def revisedTheoryAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    TheoryState (NewNAt visit) :=
  TheoryState.rootSemantic (NewNAt visit)

def revisedInquiryEntryAtVisit
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot)
    (current : (NewVAt visit).Current) :
    OpenResponsibilityAt (NewNAt visit)
      (lossAllocationSupportAt (rootedAt visit) current) :=
  match current with
  | 0 => newRevisedEntryAt visit
  | _ + 1 => revisedTargetObstructionAt visit

def revisedInquiryAuditAtVisit
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot)
    (current : (NewVAt visit).Current) :
    SourceNativeInquiryFrontAuditAt
    (revisedU7At visit) (revisedCalculusAt visit) (revisedTheoryAt visit)
      (lossAllocationSupportAt (rootedAt visit) current) :=
  .answered

/-! The initial aliases below retain the established M9/M13 vocabulary while
the source/world constructors downstream are indexed by an arbitrary old
root visit. -/

abbrev initialOldVisit := jointRoot.toAuthoritativeRoot.toRoot.initialVisit
abbrev NewN := NewNAt initialOldVisit
abbrev NewV := NewVAt initialOldVisit
def revisedDefaultEntry := revisedDefaultEntryAt initialOldVisit
def revisedU7 := revisedU7At initialOldVisit
def revisedU7Source := revisedU7SourceAt initialOldVisit
def revisedCalculus := revisedCalculusAt initialOldVisit
def revisedTheory := revisedTheoryAt initialOldVisit
def revisedInquiryEntryAt := revisedInquiryEntryAtVisit initialOldVisit
def revisedInquiryAuditAt := revisedInquiryAuditAtVisit initialOldVisit

abbrev revisedInquiryAudit := revisedInquiryAuditAt 0

inductive RevisedProjection
  | ledger
  | inquiry
  | answer
  | consumer
  | claimMigration
  | claimRetirement

def revisedProjectionLawAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeProjectionLaw
      (revisedRestructuringSourceAt visit).toLedgerSource where
  Projection := RevisedProjection
  ActiveAt := fun projection {current} _ =>
    match projection with
    | .ledger | .inquiry | .answer | .consumer => PUnit
    | .claimMigration => PLift (current = (0 : Nat))
    | .claimRetirement => PLift (current = (1 : Nat))
  InactiveAt := fun projection {current} _ =>
    match projection with
    | .ledger | .inquiry | .answer | .consumer => PEmpty
    | .claimMigration => PLift (current ≠ (0 : Nat))
    | .claimRetirement => PLift (current ≠ (1 : Nat))
  classify := by
    intro projection current occurrence
    cases projection with
    | ledger | inquiry | answer | consumer => exact .inl PUnit.unit
    | claimMigration =>
        by_cases current_eq : current = (0 : Nat)
        · exact .inl ⟨current_eq⟩
        · exact .inr ⟨current_eq⟩
    | claimRetirement =>
        by_cases current_eq : current = (1 : Nat)
        · exact .inl ⟨current_eq⟩
        · exact .inr ⟨current_eq⟩
  PayloadAt := fun projection {current} occurrence _ =>
    match projection with
    | .ledger => SourceNativeLedgerEvolutionAt
        (revisedSourceAt visit) occurrence
    | .inquiry => SourceNativeInquiryCompilationTokenAt
        (revisedInquiryEntryAtVisit visit current) ()
          (ULift.up.{1, 0} occurrence)
          (revisedInquiryAuditAtVisit visit current) PUnit
    | .answer => PUnit
    | .consumer => SourceNativeInquiryAnswerConsumerTokenAt
        () (ULift.up.{1, 0} occurrence)
          (revisedInquiryEntryAtVisit visit current) PUnit.unit
    | .claimMigration => RootClaimMigrationFaceAtVisit visit occurrence
    | .claimRetirement => RootClaimRetirementFaceAtVisit visit occurrence
  project := fun projection {current} occurrence active => by
    cases projection with
    | ledger => exact (revisedLedgerCompilerAt visit).compile occurrence
    | inquiry => exact .canonical PUnit.unit
    | answer => exact PUnit.unit
    | consumer => exact .canonical
    | claimMigration =>
        rcases active with ⟨current_eq⟩
        have occurrence_eq := revisedOccurrence_eq_emitted_at visit occurrence
        exact RootClaimMigrationFaceAtVisit.generate occurrence (by
          cases current_eq
          cases occurrence_eq
          rfl)
    | claimRetirement =>
        rcases active with ⟨current_eq⟩
        have occurrence_eq := revisedOccurrence_eq_emitted_at visit occurrence
        exact RootClaimRetirementFaceAtVisit.generate occurrence (by
          cases current_eq
          cases occurrence_eq
          rfl)

def revisedAuthoritySourceAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeAuthoritySource (NewNAt visit) (NewVAt visit) where
  restructuringSource := revisedRestructuringSourceAt visit
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal (revisedRestructuringSourceAt visit)
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := revisedTheoryAt visit
  projectionLaw := revisedProjectionLawAt visit

def revisedAuthoritativeRootAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeAuthoritativeRootClosure (NewNAt visit) (NewVAt visit) where
  source := revisedAuthoritySourceAt visit
  emitted := revisedEmittedAt visit
  compiler_commutes := lossAllocationCompiler_commutes (rootedAt visit)

def revisedLivingRootAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeLivingRootClosure (NewNAt visit) (NewVAt visit) where
  source :=
    { base := revisedAuthoritySourceAt visit
      terminalHandoff :=
        (revisedAuthoritySourceAt visit).emptyFaithfulTerminalHandoff
        (fun _ => ⟨fun terminal => nomatch terminal⟩) }
  emitted := revisedEmittedAt visit
  compiler_commutes := lossAllocationCompiler_commutes (rootedAt visit)

def revisedOccurrencePresentationAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    ConstructivePresentation
    (jointRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
      (rootedAt visit).oldSuccessor.next)
    ((revisedAuthoritativeRootAt visit).toRoot.actual.OccurrenceAt
      (0 : Nat)) where
  forward := by
    rintro ⟨support, event⟩
    cases support with
    | false => exact nomatch event
    | true => exact revisedEmittedAt visit 0
  backward := fun _ => jointRoot.emitted (rootedAt visit).oldSuccessor.next
  backward_forward := by
    rintro ⟨support, event⟩
    cases support with
    | false => exact nomatch event
    | true => cases event; rfl
  forward_backward := by
    intro occurrence
    exact
      (lossAllocationOccurrence_eq_emitted (rootedAt visit) occurrence).symm

def revisedFirstWriteAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    CanonicalFirstRootWriteAt
      (revisedAuthoritativeRootAt visit).toLedgerRoot :=
  PUnit.unit

def revisedInitialGeneratedEvolutionAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeTemporalVisitGeneratedEvolutionAt
      (revisedAuthoritativeRootAt visit).toLedgerRoot
      (.finite (revisedAuthoritativeRootAt visit).toRoot.initialVisit) :=
  (revisedAuthoritativeRootAt visit).toLedgerRoot.generatedAtTemporalVisit
    (.finite (revisedAuthoritativeRootAt visit).toRoot.initialVisit)

def revisedOldEntryRowAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    (revisedInitialGeneratedEvolutionAt visit).GeneratedEntryRowAt
      (oldRevisedEntryAt visit) :=
  ((revisedInitialGeneratedEvolutionAt visit).canonicalGeneratedEntryRow?
    (oldRevisedEntryAt visit)).get (by rfl)

def revisedNewEntryRowAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    (revisedInitialGeneratedEvolutionAt visit).GeneratedEntryRowAt
      (newRevisedEntryAt visit) :=
  ((revisedInitialGeneratedEvolutionAt visit).canonicalGeneratedEntryRow?
    (newRevisedEntryAt visit)).get (by rfl)

theorem oldEntry_eq_target_at
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot)
    (oldEntry : OpenResponsibilityAt N
      (jointRoot.toAuthoritativeRoot.toRoot.supportAt
        (rootedAt visit).oldSuccessor.next)) :
    oldEntry = (rootedAt visit).oldTargetEntry := by
  rcases oldEntry with ⟨responsibility, isOpen⟩
  rcases (rootedAt visit).oldTargetEntry with
    ⟨targetResponsibility, targetOpen⟩
  cases responsibility
  cases targetResponsibility
  cases isOpen
  cases targetOpen
  rfl

def revisedOldEntryRowsAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot)
    (oldEntry : OpenResponsibilityAt N
      (jointRoot.toAuthoritativeRoot.toRoot.supportAt
        (rootedAt visit).oldSuccessor.next)) :
    (revisedInitialGeneratedEvolutionAt visit).GeneratedEntryRowAt
      ((lossAllocationOldTargetOpenLedger (rootedAt visit)).forward
        oldEntry) := by
  rw [oldEntry_eq_target_at visit oldEntry]
  exact revisedOldEntryRowAt visit

def generatedTypedRevisionAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    GeneratedTypedSemanticWorldNetworkRevisionAt (rootedAt visit) where
  NewN := NewNAt visit
  translation := lossAllocationTranslation (rootedAt visit)
  NewV := NewVAt visit
  newLivingRoot := revisedLivingRootAt visit
  new_support_restricts := rfl
  oldTargetOpenLedger := lossAllocationOldTargetOpenLedger (rootedAt visit)
  oldTargetOpenClaim_commutes := fun _ => rfl
  oldTargetOpenProgressBudget_not_refilled := fun _ => Nat.le_refl _
  occurrencePresentation := revisedOccurrencePresentationAt visit
  occurrence_commutes := rfl
  firstWrite := revisedFirstWriteAt visit
  newOnlyEntry := newRevisedEntryAt visit
  newOnlyProgressBudget_eq_zero := rfl
  revisedClaimHolds := (cofaceAt visit).obstructionClaimHolds
  semanticChange := (cofaceAt visit).obstructionSemanticChange
  revisedClaim_hasNoOldPreimage :=
    (cofaceAt visit).obstructionClaim_hasNoOldPreimage
  newOnlyIncidence_hasNoOldPreimage :=
    (cofaceAt visit).obstructionIncidence_hasNoOldPreimage
  oldEntryRows := revisedOldEntryRowsAt visit
  newOnlyEntry_hasNoOldPreimage := by
    constructor
    rintro ⟨oldEntry, equality⟩
    have responsibility_eq := congrArg Sigma.fst equality.down
    exact nomatch responsibility_eq
  newOnlyEntryRow := revisedNewEntryRowAt visit

def revisedFirstSuccessorAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeLedgerGeneratedSuccessorAt
    (generatedTypedRevisionAt visit).initialRestructuringGenerated.occurrence
    (generatedTypedRevisionAt visit).initialRestructuringGenerated.wholeLedgerWriteBack :=
  PUnit.unit

def generatedFirstWriteGenuineSplitAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    (generatedTypedRevisionAt visit).SourceGeneratedFirstWriteGenuineSplitAt :=
  GeneratedTypedSemanticWorldNetworkRevisionAt.SourceGeneratedFirstWriteGenuineSplitAt.ofCompilerSelectedSplit
      (generatedTypedRevisionAt visit) (revisedFirstSuccessorAt visit)
      (revisedLossChildAAt visit) (revisedLossChildBAt visit)
      (lossAllocationChildren_distinct (rootedAt visit))
      (lossAllocationFirstOriginEq (rootedAt visit)
        (revisedEmittedAt visit 0))
      rfl (revisedFirstSplitCoverageAt visit)
      (revisedFirstCompiler_selects_exact_split_at visit)
      (by
        intro entry
        rcases lossAllocationInitialEntry_cases (rootedAt visit) entry with
          entry_eq | entry_eq
        · subst entry
          exact .inl ⟨⟨(rootedAt visit).oldTargetEntry, PLift.up rfl⟩⟩
        · subst entry
          exact .inr rfl)
      (by
        intro targetEntry
        rcases lossAllocationTargetEntry_cases (rootedAt visit) targetEntry with
          target_eq | target_eq | target_eq
        · subst targetEntry
          exact .inl ⟨⟨(rootedAt visit).oldTargetEntry, PLift.up rfl⟩⟩
        · subst targetEntry
          exact .inl ⟨⟨(rootedAt visit).oldTargetEntry, PLift.up rfl⟩⟩
        · subst targetEntry
          exact .inr rfl)

theorem generatedFirstWrite_children_bearers_distinct_at
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    (((generatedTypedRevisionAt visit).sourceFixedRestructuringLaw).obligationAt
        (generatedTypedRevisionAt visit).initialRestructuringGenerated.occurrence
        (generatedFirstWriteGenuineSplitAt visit).left).bearer ≠
      (((generatedTypedRevisionAt visit).sourceFixedRestructuringLaw).obligationAt
        (generatedTypedRevisionAt visit).initialRestructuringGenerated.occurrence
        (generatedFirstWriteGenuineSplitAt visit).right).bearer := by
  change sourceGeneratedLossAllocationMaterial.childBearerAt .a ≠
    sourceGeneratedLossAllocationMaterial.childBearerAt .b
  exact sourceGeneratedLossAllocationMaterial.childBearersDistinct

def generatedDefaultSideLossAllocationAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    SourceGeneratedDefaultSideLossAllocationAt
      (generatedTypedRevisionAt visit) :=
  SourceGeneratedDefaultSideLossAllocationAt.ofGroundedFirstWriteSplit
    (generatedTypedRevisionAt visit)
      (generatedFirstWriteGenuineSplitAt visit) HEq.rfl
      (generatedFirstWrite_children_bearers_distinct_at visit)

theorem generatedTypedRevision_richerGrounding_at
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    (generatedTypedRevisionAt visit).SourceGeneratedFaithfulRicherCofaceRestructuringAt :=
  (generatedDefaultSideLossAllocationAt visit).richerGrounding

def typedRevisionSourceAt
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    FieldGroundedTypedSemanticWorldNetworkRevisionAt (rootedAt visit) :=
  (generatedDefaultSideLossAllocationAt visit).fieldGroundedRevision

theorem revisedEmitter_ne_phaseTrueOldFace_at
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot)
    (current : (NewVAt visit).Current) (oldSupport : N.Support) :
    (revisedEmittedAt visit current).1 ≠ (.inl oldSupport, true) := by
  intro equality
  have worldSupport_eq := congrArg Prod.fst equality
  cases current with
  | zero => exact nomatch worldSupport_eq
  | succ current => exact nomatch worldSupport_eq

theorem revisedActual_initialLedger_noDormant_at
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    (entry : OpenResponsibilityAt (generatedTypedRevisionAt visit).NewN
      (generatedTypedRevisionAt visit).initialSupport) →
      Nonempty (Sigma fun oldEntry : OpenResponsibilityAt N
        (jointRoot.toAuthoritativeRoot.toRoot.supportAt
          (rootedAt visit).oldSuccessor.next) =>
        PLift ((generatedTypedRevisionAt visit).oldTargetOpenLedger.forward
          oldEntry = entry)) ∨
      entry = (generatedTypedRevisionAt visit).newOnlyEntry :=
  (generatedFirstWriteGenuineSplitAt visit).initialLedgerNoDormant

theorem revisedActual_targetOrigins_covered_at
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    (targetEntry : OpenResponsibilityAt (generatedTypedRevisionAt visit).NewN
      ((generatedTypedRevisionAt visit).newRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          (generatedFirstWriteGenuineSplitAt visit).successor.targetOccurrence)) →
      Nonempty (Sigma fun oldEntry : OpenResponsibilityAt N
        (jointRoot.toAuthoritativeRoot.toRoot.supportAt
          (rootedAt visit).oldSuccessor.next) =>
        PLift (((generatedFirstWriteGenuineSplitAt visit).successor.ledgerEvolution.origin
          targetEntry).1 =
            (generatedTypedRevisionAt visit).oldTargetOpenLedger.forward
              oldEntry)) ∨
      ((generatedFirstWriteGenuineSplitAt visit).successor.ledgerEvolution.origin
        targetEntry).1 = (generatedTypedRevisionAt visit).newOnlyEntry :=
  (generatedFirstWriteGenuineSplitAt visit).targetOriginsCovered

theorem revisedOccurrence_whole_material_exact_at
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot)
    (current : (NewVAt visit).Current) :
    sourceGeneratedLossAllocationMaterial.defaultOccurrence =
        sourceGeneratedClearingConsumerDeath ∧
      sourceGeneratedLossAllocationMaterial.activationSeed =
        sourceGeneratedClearingBackstopExactSeed ∧
      HEq sourceGeneratedLossAllocationMaterial.standing
        sourceGeneratedClearingBackstopCreditStanding ∧
      sourceGeneratedLossAllocationMaterial.parentBearer =
        partialOpenB.obligation.bearer ∧
      sourceGeneratedLossAllocationMaterial.childBearerAt =
        existingLossBearerAt ∧
      sourceGeneratedLossAllocationMaterial.childBearerAt .a ≠
        sourceGeneratedLossAllocationMaterial.childBearerAt .b :=
  lossAllocationOccurrence_whole_material_exact
    (rootedAt visit) (revisedEmittedAt visit current)

def revisedVisitAtFrom
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot) :
    Nat → RootVisit (revisedAuthoritativeRootAt visit).toRoot
  | 0 => (revisedAuthoritativeRootAt visit).toRoot.initialVisit
  | index + 1 => (revisedVisitAtFrom visit index).next rfl

@[simp] theorem revisedVisitAtFrom_current
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot)
    (index : Nat) :
    (revisedVisitAtFrom visit index).current = index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      change Nat.succ (revisedVisitAtFrom visit index).current =
        Nat.succ index
      exact congrArg Nat.succ inductionHypothesis

/-- The richer first split and every later identity write generate the next
visit of this same revised root.  This is the concrete continuation law used
by the inquiry runtime; no target root or visit is supplied at that mouth. -/
theorem revisedLivingRoot_generatedNextCurrentAt_eq_at
    (visit : RootVisit jointRoot.toAuthoritativeRoot.toRoot)
    (index : Nat) :
    (revisedLivingRootAt visit).generatedNextCurrentAt
        (.finite (revisedVisitAtFrom visit index)) =
      ⟨NewVAt visit, revisedAuthoritativeRootAt visit,
        .finite (revisedVisitAtFrom visit (index + 1))⟩ := by
  cases index <;> rfl

/-! ## Definitionally specialized initial-visit facade -/

def revisedProjectionLaw := revisedProjectionLawAt initialOldVisit
def revisedAuthoritySource := revisedAuthoritySourceAt initialOldVisit
def revisedAuthoritativeRoot := revisedAuthoritativeRootAt initialOldVisit
def revisedLivingRoot := revisedLivingRootAt initialOldVisit
def revisedOccurrencePresentation :=
  revisedOccurrencePresentationAt initialOldVisit
def revisedFirstWrite := revisedFirstWriteAt initialOldVisit
def revisedInitialGeneratedEvolution :=
  revisedInitialGeneratedEvolutionAt initialOldVisit
def revisedOldEntryRow := revisedOldEntryRowAt initialOldVisit
def revisedNewEntryRow := revisedNewEntryRowAt initialOldVisit

theorem oldEntry_eq_target
    (oldEntry : OpenResponsibilityAt N
      (jointRoot.toAuthoritativeRoot.toRoot.supportAt
        rooted.oldSuccessor.next)) :
    oldEntry = rooted.oldTargetEntry :=
  oldEntry_eq_target_at initialOldVisit oldEntry

def revisedOldEntryRows
    (oldEntry : OpenResponsibilityAt N
      (jointRoot.toAuthoritativeRoot.toRoot.supportAt
        rooted.oldSuccessor.next)) :
    revisedInitialGeneratedEvolution.GeneratedEntryRowAt
      ((lossAllocationOldTargetOpenLedger rooted).forward oldEntry) :=
  revisedOldEntryRowsAt initialOldVisit oldEntry

def generatedTypedRevision := generatedTypedRevisionAt initialOldVisit
def revisedFirstSuccessor := revisedFirstSuccessorAt initialOldVisit
def generatedFirstWriteGenuineSplit :=
  generatedFirstWriteGenuineSplitAt initialOldVisit

theorem generatedFirstWrite_children_bearers_distinct :
    ((generatedTypedRevision.sourceFixedRestructuringLaw).obligationAt
        generatedTypedRevision.initialRestructuringGenerated.occurrence
        generatedFirstWriteGenuineSplit.left).bearer ≠
      ((generatedTypedRevision.sourceFixedRestructuringLaw).obligationAt
        generatedTypedRevision.initialRestructuringGenerated.occurrence
        generatedFirstWriteGenuineSplit.right).bearer :=
  generatedFirstWrite_children_bearers_distinct_at initialOldVisit

def generatedDefaultSideLossAllocation :=
  generatedDefaultSideLossAllocationAt initialOldVisit

theorem generatedTypedRevision_richerGrounding :
    generatedTypedRevision.SourceGeneratedFaithfulRicherCofaceRestructuringAt :=
  generatedTypedRevision_richerGrounding_at initialOldVisit

def typedRevisionSource := typedRevisionSourceAt initialOldVisit

theorem revisedEmitter_ne_phaseTrueOldFace
    (current : NewV.Current) (oldSupport : N.Support) :
    (revisedEmitted current).1 ≠ (.inl oldSupport, true) :=
  revisedEmitter_ne_phaseTrueOldFace_at initialOldVisit current oldSupport

theorem revisedActual_initialLedger_noDormant :
    (entry : OpenResponsibilityAt generatedTypedRevision.NewN
      generatedTypedRevision.initialSupport) →
      Nonempty (Sigma fun oldEntry : OpenResponsibilityAt N
        (jointRoot.toAuthoritativeRoot.toRoot.supportAt
          rooted.oldSuccessor.next) =>
        PLift (generatedTypedRevision.oldTargetOpenLedger.forward oldEntry =
          entry)) ∨
      entry = generatedTypedRevision.newOnlyEntry :=
  revisedActual_initialLedger_noDormant_at initialOldVisit

theorem revisedActual_targetOrigins_covered :
    (targetEntry : OpenResponsibilityAt generatedTypedRevision.NewN
      (generatedTypedRevision.newRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          generatedFirstWriteGenuineSplit.successor.targetOccurrence)) →
      Nonempty (Sigma fun oldEntry : OpenResponsibilityAt N
        (jointRoot.toAuthoritativeRoot.toRoot.supportAt
          rooted.oldSuccessor.next) =>
        PLift ((generatedFirstWriteGenuineSplit.successor.ledgerEvolution.origin
          targetEntry).1 =
            generatedTypedRevision.oldTargetOpenLedger.forward oldEntry)) ∨
      (generatedFirstWriteGenuineSplit.successor.ledgerEvolution.origin
        targetEntry).1 = generatedTypedRevision.newOnlyEntry :=
  revisedActual_targetOrigins_covered_at initialOldVisit

theorem revisedOccurrence_whole_material_exact
    (current : NewV.Current) :
    sourceGeneratedLossAllocationMaterial.defaultOccurrence =
        sourceGeneratedClearingConsumerDeath ∧
      sourceGeneratedLossAllocationMaterial.activationSeed =
        sourceGeneratedClearingBackstopExactSeed ∧
      HEq sourceGeneratedLossAllocationMaterial.standing
        sourceGeneratedClearingBackstopCreditStanding ∧
      sourceGeneratedLossAllocationMaterial.parentBearer =
        partialOpenB.obligation.bearer ∧
      sourceGeneratedLossAllocationMaterial.childBearerAt =
        existingLossBearerAt ∧
      sourceGeneratedLossAllocationMaterial.childBearerAt .a ≠
        sourceGeneratedLossAllocationMaterial.childBearerAt .b :=
  revisedOccurrence_whole_material_exact_at initialOldVisit current

def revisedVisitAt : Nat → RootVisit revisedAuthoritativeRoot.toRoot :=
  revisedVisitAtFrom initialOldVisit

@[simp] theorem revisedVisitAt_current (index : Nat) :
    (revisedVisitAt index).current = index :=
  revisedVisitAtFrom_current initialOldVisit index

theorem revisedLivingRoot_generatedNextCurrentAt_eq (index : Nat) :
    revisedLivingRoot.generatedNextCurrentAt (.finite (revisedVisitAt index)) =
      ⟨NewV, revisedAuthoritativeRoot,
        .finite (revisedVisitAt (index + 1))⟩ :=
  revisedLivingRoot_generatedNextCurrentAt_eq_at initialOldVisit index

end
end M9ProofCarryingRenewalU8RevisedWorld
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalU8RevisedWorld.generatedTypedRevision
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalU8RevisedWorld.generatedFirstWriteGenuineSplit
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalU8RevisedWorld.typedRevisionSource
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalU8RevisedWorld.revisedEmitter_ne_phaseTrueOldFace
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalU8RevisedWorld.revisedActual_initialLedger_noDormant
#print axioms SaturationMonoid.ProcessGame.Society.M9ProofCarryingRenewalU8RevisedWorld.revisedActual_targetOrigins_covered

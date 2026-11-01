import H0mework.Foundation.Source.AccountedUnfolding
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.SourceAccountedEconomicAtom

/-!
# M14 economic single-generator fold

The exact M14 failure and proof-carrying repair events are exposed through
the repository's sole recursive occurrence constructor,
`RootedAccountedUnfolding.occur`.  The source atom contains no numeric or
qualitative record field.  One fixed algebra generates a synchronized image whose
quantitative and qualitative projections are downstream maps of that same
fold.

The repair exposure is a finite calculation trace, not a second policy
runtime: it cannot select the root's ordinary/U8 branch.  `advance` preserves
the failure parent while exposing its source-generated repair; a second
advance exposes the corresponding repair at the next actual root visit.
No economic AST, second fold, evaluator court, root, ledger, registry, or
completed future is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14EconomicSingleFold

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open RootedAccountedUnfolding
open UBI Policy
open M14TenureCaptureRouteRepairNoGoRegression
open M14ProofCarryingExitRepairRegression
open M14SourceAccountedEconomicAtom
open M14UBIPeriodicRootHistory

/-! ## Opaque sole generator carrier -/

private structure ExactEconomicAtomRepresentation : Type 18 where
  eventEvidence : EconomicEvent
  sourceAnchor : SourceAccountedEconomicAtomAt eventEvidence

/-- The representation, constructors and private eliminators are installed in
one opaque package.  The public carrier is only its abstract `Carrier`
projection, so Lean generates no public atom recursor capable of recovering
the source event. -/
private structure ExactEconomicAtomModel : Type 19 where
  Carrier : Type 18
  ofFailure : ∀ {depth : Nat}, RepairFailureOriginAt depth → Carrier
  ofRepair : ∀ {depth : Nat} {origin : RepairFailureOriginAt depth},
    SourceGeneratedProofCarryingExitRepairAt origin
      (canonicalRepairAt origin) → Carrier
  eventEvidence : Carrier → EconomicEvent
  sourceAnchor : (atom : Carrier) →
    SourceAccountedEconomicAtomAt (eventEvidence atom)
  eventEvidence_ofFailure : ∀ {depth : Nat}
    (origin : RepairFailureOriginAt depth),
      eventEvidence (ofFailure origin) = failureEvent origin
  eventEvidence_ofRepair : ∀ {depth : Nat}
    {origin : RepairFailureOriginAt depth}
    (proof : SourceGeneratedProofCarryingExitRepairAt origin
      (canonicalRepairAt origin)),
      eventEvidence (ofRepair proof) = repairEvent proof

private opaque exactEconomicAtomModel : ExactEconomicAtomModel :=
  { Carrier := ExactEconomicAtomRepresentation
    ofFailure := fun origin =>
      ⟨failureEvent origin,
        SourceAccountedEconomicAtomAt.generateFailure origin⟩
    ofRepair := fun proof =>
      ⟨repairEvent proof,
        SourceAccountedEconomicAtomAt.generateRepair proof⟩
    eventEvidence := ExactEconomicAtomRepresentation.eventEvidence
    sourceAnchor := ExactEconomicAtomRepresentation.sourceAnchor
    eventEvidence_ofFailure := fun _origin => rfl
    eventEvidence_ofRepair := fun _proof => rfl }

/-- The recursive unfolding sees only this genuinely abstract root-accounted
atom.  Before the fold, public consumers can read root/accounting provenance
but cannot eliminate the atom to recover a capacity/cause/repair record. -/
abbrev ExactEconomicAtom : Type 18 := exactEconomicAtomModel.Carrier

namespace ExactEconomicAtom

def ofFailure {depth : Nat}
    (origin : RepairFailureOriginAt depth) : ExactEconomicAtom :=
  exactEconomicAtomModel.ofFailure origin

def ofRepair {depth : Nat}
    {origin : RepairFailureOriginAt depth}
    (proof : SourceGeneratedProofCarryingExitRepairAt origin
      (canonicalRepairAt origin)) : ExactEconomicAtom :=
  exactEconomicAtomModel.ofRepair proof

def ofCanonicalRepair {depth : Nat}
    (origin : RepairFailureOriginAt depth) : ExactEconomicAtom :=
  ofRepair (SourceGeneratedProofCarryingExitRepairAt.generate origin)

private def eventEvidence (atom : ExactEconomicAtom) : EconomicEvent :=
  exactEconomicAtomModel.eventEvidence atom

private def sourceAnchor (atom : ExactEconomicAtom) :
    SourceAccountedEconomicAtomAt atom.eventEvidence :=
  exactEconomicAtomModel.sourceAnchor atom

@[simp] private theorem eventEvidence_ofFailure {depth : Nat}
    (origin : RepairFailureOriginAt depth) :
    (ofFailure origin).eventEvidence = failureEvent origin :=
  exactEconomicAtomModel.eventEvidence_ofFailure origin

@[simp] private theorem eventEvidence_ofRepair {depth : Nat}
    {origin : RepairFailureOriginAt depth}
    (proof : SourceGeneratedProofCarryingExitRepairAt origin
      (canonicalRepairAt origin)) :
    (ofRepair proof).eventEvidence = repairEvent proof :=
  exactEconomicAtomModel.eventEvidence_ofRepair proof

def visit (atom : ExactEconomicAtom) := atom.sourceAnchor.visit

def exactTemporalRootEvent (atom : ExactEconomicAtom) :=
  atom.sourceAnchor.exactTemporalRootEvent

def rootOccurrence (atom : ExactEconomicAtom) :=
  atom.sourceAnchor.rootOccurrence

def installedMandate (atom : ExactEconomicAtom) :=
  atom.sourceAnchor.installedMandate

def installedUBI (atom : ExactEconomicAtom) :=
  atom.sourceAnchor.installedUBI

def sourceEntry (atom : ExactEconomicAtom) := atom.sourceAnchor.sourceEntry

def sourceSelectedRow (atom : ExactEconomicAtom) :=
  atom.sourceAnchor.sourceSelectedRow

def wholeLedgerWriteBack (atom : ExactEconomicAtom) :=
  atom.sourceAnchor.wholeLedgerWriteBack

def generatedNext (atom : ExactEconomicAtom) := atom.sourceAnchor.generatedNext

/-- Public heterogeneous root provenance without access to the sealed source
event. -/
def erasedRootEvent (atom : ExactEconomicAtom) :
    SourceAccountedEconomicAtomAt.AnyExactRootOccurrence :=
  ⟨atom.visit, atom.exactTemporalRootEvent⟩

@[simp] theorem ofFailure_visit {depth : Nat}
    (origin : RepairFailureOriginAt depth) :
    (ofFailure origin).visit = temporalVisitAt depth := by
  unfold visit SourceAccountedEconomicAtomAt.visit
  rw [eventEvidence_ofFailure]
  rfl

@[simp] theorem erasedRootEvent_ofFailure {depth : Nat}
    (origin : RepairFailureOriginAt depth) :
    (ofFailure origin).erasedRootEvent =
      ⟨temporalVisitAt depth,
        (periodicSourceBackedPaymentAt depth).rootOccurrence⟩ := by
  let root :=
    M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toLedgerRoot
  have visit_eq := ofFailure_visit origin
  calc
    (ofFailure origin).erasedRootEvent =
        ⟨(ofFailure origin).visit,
          root.exactTemporalCausalEventAt (ofFailure origin).visit⟩ := rfl
    _ = ⟨temporalVisitAt depth,
          root.exactTemporalCausalEventAt (temporalVisitAt depth)⟩ :=
      congrArg
        (fun visit =>
          (⟨visit, root.exactTemporalCausalEventAt visit⟩ :
            SourceAccountedEconomicAtomAt.AnyExactRootOccurrence)) visit_eq
    _ = ⟨temporalVisitAt depth,
          (periodicSourceBackedPaymentAt depth).rootOccurrence⟩ := by
      apply Sigma.ext
      · rfl
      · exact heq_of_eq origin.exactTemporalPayment.symm

@[simp] theorem ofRepair_visit {depth : Nat}
    {origin : RepairFailureOriginAt depth}
    (proof : SourceGeneratedProofCarryingExitRepairAt origin
      (canonicalRepairAt origin)) :
    (ofRepair proof).visit = temporalVisitAt depth := by
  unfold visit SourceAccountedEconomicAtomAt.visit
  rw [eventEvidence_ofRepair]
  rfl

@[simp] theorem erasedRootEvent_ofRepair {depth : Nat}
    {origin : RepairFailureOriginAt depth}
    (proof : SourceGeneratedProofCarryingExitRepairAt origin
      (canonicalRepairAt origin)) :
    (ofRepair proof).erasedRootEvent =
      ⟨temporalVisitAt depth,
        (periodicSourceBackedPaymentAt depth).rootOccurrence⟩ := by
  let root :=
    M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toLedgerRoot
  have visit_eq := ofRepair_visit proof
  calc
    (ofRepair proof).erasedRootEvent =
        ⟨(ofRepair proof).visit,
          root.exactTemporalCausalEventAt (ofRepair proof).visit⟩ := rfl
    _ = ⟨temporalVisitAt depth,
          root.exactTemporalCausalEventAt (temporalVisitAt depth)⟩ :=
      congrArg
        (fun visit =>
          (⟨visit, root.exactTemporalCausalEventAt visit⟩ :
            SourceAccountedEconomicAtomAt.AnyExactRootOccurrence)) visit_eq
    _ = ⟨temporalVisitAt depth,
          (periodicSourceBackedPaymentAt depth).rootOccurrence⟩ := by
      apply Sigma.ext
      · rfl
      · exact heq_of_eq origin.exactTemporalPayment.symm

theorem rootOccurrence_eq_exactTemporal (atom : ExactEconomicAtom) :
    atom.rootOccurrence = atom.exactTemporalRootEvent.occurrence :=
  atom.sourceAnchor.rootOccurrence_eq_exactTemporal

@[simp] theorem sourceEntry_eq_rootEntry (atom : ExactEconomicAtom) :
    atom.sourceEntry = RootInquiryU8CompletionRegression.entry :=
  atom.sourceAnchor.sourceEntry_eq_rootEntry

theorem sourceSelectedRow_heq_ubi (atom : ExactEconomicAtom) :
    HEq atom.sourceSelectedRow atom.installedUBI.payload.selectedRow :=
  atom.sourceAnchor.sourceSelectedRow_heq_ubi

theorem successor_heq_ubi (atom : ExactEconomicAtom) :
    HEq atom.installedMandate.payload.successor
      atom.installedUBI.payload.successor :=
  atom.sourceAnchor.successor_heq_ubi

theorem wholeLedgerWriteBack_eq (atom : ExactEconomicAtom) :
    atom.wholeLedgerWriteBack =
      (M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit atom.visit).wholeLedgerWriteBack :=
  atom.sourceAnchor.wholeLedgerWriteBack_eq

theorem rootAnswerAndNext_factorizes (atom : ExactEconomicAtom) :
    atom.installedMandate.RootAnswerAndNextFactorizes :=
  atom.sourceAnchor.rootAnswerAndNext_factorizes

@[simp] theorem generatedNext_eq (atom : ExactEconomicAtom) :
    atom.generatedNext =
      M9ProofCarryingRenewalInquiryRoot.jointRoot.generatedNextCurrentAt
        atom.visit :=
  atom.sourceAnchor.generatedNext_eq

end ExactEconomicAtom

def exactFailureAtom {depth : Nat}
    (origin : RepairFailureOriginAt depth) : ExactEconomicAtom :=
  ExactEconomicAtom.ofFailure origin

def exactRepairAtom {depth : Nat}
    (origin : RepairFailureOriginAt depth) : ExactEconomicAtom :=
  ExactEconomicAtom.ofCanonicalRepair origin

def tenureExactEconomicRepairAtomAt (depth : Nat) : ExactEconomicAtom :=
  exactRepairAtom (tenureCaptureOriginAt depth)

def routeExactEconomicRepairAtomAt (depth : Nat) : ExactEconomicAtom :=
  exactRepairAtom (routeBottleneckOriginAt depth)

/-! ## One synchronized algebra image -/

private def economicAtomIsRepair (atom : ExactEconomicAtom) : Bool :=
  match atom.eventEvidence with
  | .inl _ => false
  | .inr _ => true

private noncomputable def economicAtomCapacity
    (atom : ExactEconomicAtom) : Nat :=
  match atom.eventEvidence with
  | .inl failure => failureCapacityReadoutAt failure.1 failure.2
  | .inr repair => repairOutcomeCapacityAt repair.1.1 repair.1.2
      (canonicalRepairAt repair.1.2)

private def economicAtomCause
    (atom : ExactEconomicAtom) : ExactExitFailureKind :=
  atom.eventEvidence.origin.failureKind

private def economicAtomRepair
    (atom : ExactEconomicAtom) : ExactExitRepair :=
  canonicalRepairAt atom.eventEvidence.origin

@[simp] private theorem economicAtomIsRepair_exactFailureAtom
    {depth : Nat} (origin : RepairFailureOriginAt depth) :
    economicAtomIsRepair (exactFailureAtom origin) = false := by
  unfold economicAtomIsRepair exactFailureAtom
  rw [ExactEconomicAtom.eventEvidence_ofFailure]
  rfl

@[simp] private theorem economicAtomIsRepair_exactRepairAtom
    {depth : Nat} (origin : RepairFailureOriginAt depth) :
    economicAtomIsRepair (exactRepairAtom origin) = true := by
  unfold economicAtomIsRepair exactRepairAtom
    ExactEconomicAtom.ofCanonicalRepair
  rw [ExactEconomicAtom.eventEvidence_ofRepair]
  rfl

@[simp] private theorem economicAtomCapacity_exactFailureAtom
    {depth : Nat} (origin : RepairFailureOriginAt depth) :
    economicAtomCapacity (exactFailureAtom origin) =
      failureCapacityReadoutAt depth origin := by
  unfold economicAtomCapacity exactFailureAtom
  rw [ExactEconomicAtom.eventEvidence_ofFailure]
  rfl

@[simp] private theorem economicAtomCapacity_exactRepairAtom
    {depth : Nat} (origin : RepairFailureOriginAt depth) :
    economicAtomCapacity (exactRepairAtom origin) =
      repairOutcomeCapacityAt depth origin (canonicalRepairAt origin) := by
  unfold economicAtomCapacity exactRepairAtom
    ExactEconomicAtom.ofCanonicalRepair
  rw [ExactEconomicAtom.eventEvidence_ofRepair]
  rfl

@[simp] private theorem economicAtomCause_exactFailureAtom
    {depth : Nat} (origin : RepairFailureOriginAt depth) :
    economicAtomCause (exactFailureAtom origin) = origin.failureKind := by
  unfold economicAtomCause exactFailureAtom
  rw [ExactEconomicAtom.eventEvidence_ofFailure]
  rfl

@[simp] private theorem economicAtomCause_exactRepairAtom
    {depth : Nat} (origin : RepairFailureOriginAt depth) :
    economicAtomCause (exactRepairAtom origin) = origin.failureKind := by
  unfold economicAtomCause exactRepairAtom
    ExactEconomicAtom.ofCanonicalRepair
  rw [ExactEconomicAtom.eventEvidence_ofRepair]
  rfl

@[simp] private theorem economicAtomRepair_exactFailureAtom
    {depth : Nat} (origin : RepairFailureOriginAt depth) :
    economicAtomRepair (exactFailureAtom origin) = canonicalRepairAt origin := by
  unfold economicAtomRepair exactFailureAtom
  rw [ExactEconomicAtom.eventEvidence_ofFailure]
  rfl

@[simp] private theorem economicAtomRepair_exactRepairAtom
    {depth : Nat} (origin : RepairFailureOriginAt depth) :
    economicAtomRepair (exactRepairAtom origin) = canonicalRepairAt origin := by
  unfold economicAtomRepair exactRepairAtom
    ExactEconomicAtom.ofCanonicalRepair
  rw [ExactEconomicAtom.eventEvidence_ofRepair]
  rfl

/-- One fold-generated record.  Numeric capacity and the already source-owned
cause/repair authority first become one synchronized public record here. -/
structure GeneratedEconomicImagePoint : Type 18 where
  private mk ::
  atom : ExactEconomicAtom
  isRepair : Bool
  capacity : Nat
  cause : ExactExitFailureKind
  repair : ExactExitRepair

private def generatedEconomicImagePoint
    (atom : ExactEconomicAtom) : GeneratedEconomicImagePoint where
  atom := atom
  isRepair := economicAtomIsRepair atom
  capacity := economicAtomCapacity atom
  cause := economicAtomCause atom
  repair := economicAtomRepair atom

abbrev EconomicFoldImage := List GeneratedEconomicImagePoint

/-- The unique economic algebra: prepend the exact source point, then flatten
the already folded child exposures. -/
private def economicAlgebra (atom : ExactEconomicAtom)
    (children : List EconomicFoldImage) : EconomicFoldImage :=
  generatedEconomicImagePoint atom :: children.flatten

def economicImage
    (occurrence : RootedAccountedUnfolding ExactEconomicAtom) :
    EconomicFoldImage :=
  occurrence.fold economicAlgebra

private theorem candidateValues_economicImage_eq_foldBranches
    (branches : AccountedBranches ExactEconomicAtom) :
    candidateValues economicImage branches =
      foldBranches economicAlgebra branches :=
  AccountedBranches.rec
    (motive_1 := fun occurrence =>
      economicImage occurrence = fold economicAlgebra occurrence)
    (motive_2 := fun branchList =>
      candidateValues economicImage branchList =
        foldBranches economicAlgebra branchList)
    (fun _origin _branches _branchResult => rfl)
    rfl
    (fun _head _tail headResult tailResult =>
      AccountedList.congrArgTwo List.cons headResult tailResult)
    branches

/-- Private implementation of constructor compatibility. -/
private def EconomicConstructorCompatibleImpl
    (candidate : RootedAccountedUnfolding ExactEconomicAtom →
      EconomicFoldImage) : Prop :=
  ∀ origin branches,
    candidate (.occur origin branches) =
      economicAlgebra origin
        (RootedAccountedUnfolding.candidateValues candidate branches)

private theorem economicImage_constructorCompatible_impl :
    EconomicConstructorCompatibleImpl economicImage := by
  intro origin branches
  unfold economicImage
  change economicAlgebra origin (foldBranches economicAlgebra branches) =
    economicAlgebra origin
      (candidateValues (fold economicAlgebra) branches)
  have values_eq :=
    candidateValues_economicImage_eq_foldBranches branches
  unfold economicImage at values_eq
  rw [values_eq]

private theorem constructorCompatibleEvaluator_eq_economicImage_impl
    (candidate : RootedAccountedUnfolding ExactEconomicAtom →
      EconomicFoldImage)
    (compatible : EconomicConstructorCompatibleImpl candidate)
    (occurrence : RootedAccountedUnfolding ExactEconomicAtom) :
    candidate occurrence = economicImage occurrence :=
  RootedAccountedUnfolding.fold_unique
    economicAlgebra candidate compatible occurrence

private structure EconomicCompatibilityModel : Type 19 where
  Compatible :
    (RootedAccountedUnfolding ExactEconomicAtom → EconomicFoldImage) → Prop
  canonical : Compatible economicImage
  unique : ∀ candidate, Compatible candidate → ∀ occurrence,
    candidate occurrence = economicImage occurrence

private opaque economicCompatibilityModel : EconomicCompatibilityModel :=
  { Compatible := EconomicConstructorCompatibleImpl
    canonical := economicImage_constructorCompatible_impl
    unique := constructorCompatibleEvaluator_eq_economicImage_impl }

/-- Opaque public compatibility seal.  It has no generated recursor exposing
the private algebra or its constructor equation. -/
abbrev EconomicConstructorCompatible
    (candidate : RootedAccountedUnfolding ExactEconomicAtom →
      EconomicFoldImage) : Prop :=
  economicCompatibilityModel.Compatible candidate

theorem economicImage_constructorCompatible :
    EconomicConstructorCompatible economicImage :=
  economicCompatibilityModel.canonical

private def quantitativeImage (image : EconomicFoldImage) : List Nat :=
  image.map GeneratedEconomicImagePoint.capacity

private def qualitativeImage (image : EconomicFoldImage) :
    List (Bool × ExactExitFailureKind × ExactExitRepair) :=
  image.map fun point => (point.isRepair, point.cause, point.repair)

def economicQuantitativeImage
    (occurrence : RootedAccountedUnfolding ExactEconomicAtom) : List Nat :=
  quantitativeImage (economicImage occurrence)

def economicQualitativeImage
    (occurrence : RootedAccountedUnfolding ExactEconomicAtom) :
    List (Bool × ExactExitFailureKind × ExactExitRepair) :=
  qualitativeImage (economicImage occurrence)

/-! ## Source occurrences and repair exposure -/

def economicFailureOccurrence (failure : EconomicFailureEvent) :
    RootedAccountedUnfolding ExactEconomicAtom :=
  match failure with
  | ⟨_depth, origin⟩ => .zero (exactFailureAtom origin)

def tenureEconomicFailureOccurrenceAt (depth : Nat) :
    RootedAccountedUnfolding ExactEconomicAtom :=
  economicFailureOccurrence ⟨depth, tenureCaptureOriginAt depth⟩

def routeEconomicFailureOccurrenceAt (depth : Nat) :
    RootedAccountedUnfolding ExactEconomicAtom :=
  economicFailureOccurrence ⟨depth, routeBottleneckOriginAt depth⟩

def canonicalRepairAtomOf (atom : ExactEconomicAtom) : ExactEconomicAtom :=
  exactRepairAtom atom.eventEvidence.origin

@[simp] private theorem canonicalRepairAtomOf_exactFailureAtom
    {depth : Nat} (origin : RepairFailureOriginAt depth) :
    canonicalRepairAtomOf (exactFailureAtom origin) =
      exactRepairAtom origin := by
  unfold canonicalRepairAtomOf exactFailureAtom
  rw [ExactEconomicAtom.eventEvidence_ofFailure]
  rfl

def canonicalRepairPatch (atom : ExactEconomicAtom) :
    RootedAccountedUnfolding ExactEconomicAtom :=
  .zero (canonicalRepairAtomOf atom)

def economicRepairExposure
    (occurrence : RootedAccountedUnfolding ExactEconomicAtom) :
    RootedAccountedUnfolding ExactEconomicAtom :=
  occurrence.advance canonicalRepairPatch

@[simp] theorem economicRepairExposure_failure_eq {depth : Nat}
    (origin : RepairFailureOriginAt depth) :
    economicRepairExposure
        (economicFailureOccurrence ⟨depth, origin⟩) =
      .occur (exactFailureAtom origin)
        (.singleton (.zero (exactRepairAtom origin))) := by
  change
    RootedAccountedUnfolding.occur (exactFailureAtom origin)
      (.singleton (canonicalRepairPatch (exactFailureAtom origin))) = _
  simp [canonicalRepairPatch]

/-- The exact fold occurrence is anchored to the same temporal root event as
the visit-indexed payment authority.  This exposes only accounting
provenance; the sealed economic source event remains inaccessible. -/
@[simp] theorem tenureRepairExposure_rootEvent (depth : Nat) :
    (economicRepairExposure
      (tenureEconomicFailureOccurrenceAt depth)).root.erasedRootEvent =
      ⟨temporalVisitAt depth,
        (periodicSourceBackedPaymentAt depth).rootOccurrence⟩ := by
  have root_eq :
      (economicRepairExposure
        (tenureEconomicFailureOccurrenceAt depth)).root =
        exactFailureAtom (tenureCaptureOriginAt depth) := by
    simp [economicRepairExposure, tenureEconomicFailureOccurrenceAt,
      economicFailureOccurrence, RootedAccountedUnfolding.zero]
    rfl
  rw [root_eq]
  exact ExactEconomicAtom.erasedRootEvent_ofFailure
    (tenureCaptureOriginAt depth)

def nextFailureOrigin {depth : Nat} :
    RepairFailureOriginAt depth → RepairFailureOriginAt (depth + 1)
  | .tenureCapture _ => tenureCaptureOriginAt (depth + 1)
  | .routeBottleneck _ => routeBottleneckOriginAt (depth + 1)

def nextVisitRepairAtomOf (atom : ExactEconomicAtom) : ExactEconomicAtom :=
  match atom.eventEvidence.failure with
  | ⟨_depth, origin⟩ => exactRepairAtom (nextFailureOrigin origin)

@[simp] private theorem nextVisitRepairAtomOf_exactRepairAtom
    {depth : Nat} (origin : RepairFailureOriginAt depth) :
    nextVisitRepairAtomOf (exactRepairAtom origin) =
      exactRepairAtom (nextFailureOrigin origin) := by
  unfold nextVisitRepairAtomOf exactRepairAtom
    ExactEconomicAtom.ofCanonicalRepair
  rw [ExactEconomicAtom.eventEvidence_ofRepair]
  rfl

def nextVisitRepairPatch (atom : ExactEconomicAtom) :
    RootedAccountedUnfolding ExactEconomicAtom :=
  .zero (nextVisitRepairAtomOf atom)

def economicTwoStepExposure
    (occurrence : RootedAccountedUnfolding ExactEconomicAtom) :
    RootedAccountedUnfolding ExactEconomicAtom :=
  (occurrence.advance canonicalRepairPatch).advance nextVisitRepairPatch

theorem economic_frontier_advance
    (occurrence : RootedAccountedUnfolding ExactEconomicAtom) :
    (economicRepairExposure occurrence).frontier =
      occurrence.frontier.flatMap
        (fun atom => (canonicalRepairPatch atom).frontier) :=
  RootedAccountedUnfolding.frontier_advance canonicalRepairPatch occurrence

theorem economic_advance_assoc
    (occurrence : RootedAccountedUnfolding ExactEconomicAtom) :
    economicTwoStepExposure occurrence =
      occurrence.advance (fun atom =>
        (canonicalRepairPatch atom).advance nextVisitRepairPatch) :=
  RootedAccountedUnfolding.advance_assoc
    canonicalRepairPatch nextVisitRepairPatch occurrence

@[simp] theorem tenure_repair_frontier (depth : Nat) :
    (economicRepairExposure
      (tenureEconomicFailureOccurrenceAt depth)).frontier =
        [tenureExactEconomicRepairAtomAt depth] := by
  change (economicRepairExposure
    (economicFailureOccurrence
      ⟨depth, tenureCaptureOriginAt depth⟩)).frontier = _
  rw [economicRepairExposure_failure_eq]
  rfl

@[simp] theorem route_repair_frontier (depth : Nat) :
    (economicRepairExposure
      (routeEconomicFailureOccurrenceAt depth)).frontier =
        [routeExactEconomicRepairAtomAt depth] := by
  change (economicRepairExposure
    (economicFailureOccurrence
      ⟨depth, routeBottleneckOriginAt depth⟩)).frontier = _
  rw [economicRepairExposure_failure_eq]
  rfl

@[simp] theorem tenure_two_step_frontier (depth : Nat) :
    (economicTwoStepExposure
      (tenureEconomicFailureOccurrenceAt depth)).frontier =
        [tenureExactEconomicRepairAtomAt (depth + 1)] := by
  unfold economicTwoStepExposure
  rw [RootedAccountedUnfolding.frontier_advance]
  change (economicRepairExposure
    (tenureEconomicFailureOccurrenceAt depth)).frontier.flatMap
      (fun atom => (nextVisitRepairPatch atom).frontier) = _
  rw [tenure_repair_frontier]
  simp [nextVisitRepairPatch, tenureExactEconomicRepairAtomAt]
  rfl

@[simp] theorem route_two_step_frontier (depth : Nat) :
    (economicTwoStepExposure
      (routeEconomicFailureOccurrenceAt depth)).frontier =
        [routeExactEconomicRepairAtomAt (depth + 1)] := by
  unfold economicTwoStepExposure
  rw [RootedAccountedUnfolding.frontier_advance]
  change (economicRepairExposure
    (routeEconomicFailureOccurrenceAt depth)).frontier.flatMap
      (fun atom => (nextVisitRepairPatch atom).frontier) = _
  rw [route_repair_frontier]
  simp [nextVisitRepairPatch, routeExactEconomicRepairAtomAt]
  rfl

/-! ## Fold uniqueness and fixed cross-occurrence separation -/

theorem constructorCompatibleEvaluator_eq_economicImage
    (candidate : RootedAccountedUnfolding ExactEconomicAtom →
      EconomicFoldImage)
    (compatible : EconomicConstructorCompatible candidate)
    (occurrence : RootedAccountedUnfolding ExactEconomicAtom) :
    candidate occurrence = economicImage occurrence :=
  economicCompatibilityModel.unique candidate compatible occurrence

def tenureRepairExposure : RootedAccountedUnfolding ExactEconomicAtom :=
  economicRepairExposure (tenureEconomicFailureOccurrenceAt 0)

def routeRepairExposure : RootedAccountedUnfolding ExactEconomicAtom :=
  economicRepairExposure (routeEconomicFailureOccurrenceAt 1)

theorem tenure_route_source_occurrences_distinct :
    tenureRepairExposure ≠ routeRepairExposure := by
  intro equality
  have atom_eq := congrArg RootedAccountedUnfolding.root equality
  simp [tenureRepairExposure, routeRepairExposure,
    economicRepairExposure, tenureEconomicFailureOccurrenceAt,
    routeEconomicFailureOccurrenceAt, economicFailureOccurrence,
    RootedAccountedUnfolding.zero] at atom_eq
  change exactFailureAtom (tenureCaptureOriginAt 0) =
    exactFailureAtom (routeBottleneckOriginAt 1) at atom_eq
  have event_eq := congrArg ExactEconomicAtom.eventEvidence atom_eq
  unfold exactFailureAtom at event_eq
  rw [ExactEconomicAtom.eventEvidence_ofFailure,
    ExactEconomicAtom.eventEvidence_ofFailure] at event_eq
  have depth_eq := congrArg EconomicEvent.depth event_eq
  change (0 : Nat) = 1 at depth_eq
  omega

theorem tenure_route_exact_root_occurrences_distinct :
    (tenureFailureAtomAt 0).erasedRootOccurrence ≠
      (routeFailureAtomAt 1).erasedRootOccurrence :=
  SourceAccountedEconomicAtomAt.erasedRootOccurrence_ne_of_depth_ne
    (tenureFailureAtomAt 0) (routeFailureAtomAt 1) (by
      intro equality
      change (0 : Nat) = 1 at equality
      omega)

/-- The visible quantitative label is constant across all generated tenure
occurrences even though their exact temporal root occurrences remain
distinct.  This is the open-depth form used by downstream identity-kernel
consumers. -/
theorem tenure_quantitative_image_at (depth : Nat) :
    economicQuantitativeImage
        (economicRepairExposure (tenureEconomicFailureOccurrenceAt depth)) =
      [0, 1] := by
  unfold tenureEconomicFailureOccurrenceAt
  rw [economicRepairExposure_failure_eq]
  unfold economicQuantitativeImage quantitativeImage economicImage
  change [economicAtomCapacity
      (exactFailureAtom (tenureCaptureOriginAt depth)),
    economicAtomCapacity
      (exactRepairAtom (tenureCaptureOriginAt depth))] = [0, 1]
  rw [economicAtomCapacity_exactFailureAtom,
    economicAtomCapacity_exactRepairAtom,
    tenure_capture_failure_readout_eq_zero,
    canonical_repair_outcome_eq_one]

theorem tenure_quantitative_image :
    economicQuantitativeImage tenureRepairExposure = [0, 1] := by
  unfold tenureRepairExposure tenureEconomicFailureOccurrenceAt
  rw [economicRepairExposure_failure_eq]
  unfold economicQuantitativeImage quantitativeImage economicImage
  change [economicAtomCapacity
      (exactFailureAtom (tenureCaptureOriginAt 0)),
    economicAtomCapacity
      (exactRepairAtom (tenureCaptureOriginAt 0))] = [0, 1]
  rw [economicAtomCapacity_exactFailureAtom,
    economicAtomCapacity_exactRepairAtom,
    tenure_capture_failure_readout_eq_zero,
    canonical_repair_outcome_eq_one]

theorem route_quantitative_image :
    economicQuantitativeImage routeRepairExposure = [0, 1] := by
  unfold routeRepairExposure routeEconomicFailureOccurrenceAt
  rw [economicRepairExposure_failure_eq]
  unfold economicQuantitativeImage quantitativeImage economicImage
  change [economicAtomCapacity
      (exactFailureAtom (routeBottleneckOriginAt 1)),
    economicAtomCapacity
      (exactRepairAtom (routeBottleneckOriginAt 1))] = [0, 1]
  rw [economicAtomCapacity_exactFailureAtom,
    economicAtomCapacity_exactRepairAtom,
    route_bottleneck_failure_readout_eq_zero,
    canonical_repair_outcome_eq_one]

theorem tenure_route_quantitative_images_equal :
    economicQuantitativeImage tenureRepairExposure =
      economicQuantitativeImage routeRepairExposure := by
  rw [tenure_quantitative_image, route_quantitative_image]

theorem tenure_route_qualitative_images_distinct :
    economicQualitativeImage tenureRepairExposure ≠
      economicQualitativeImage routeRepairExposure := by
  intro equality
  unfold tenureRepairExposure tenureEconomicFailureOccurrenceAt at equality
  unfold routeRepairExposure routeEconomicFailureOccurrenceAt at equality
  rw [economicRepairExposure_failure_eq,
    economicRepairExposure_failure_eq] at equality
  have repair_eq := congrArg
    (fun image => (image[0]?).map fun point => point.2.2) equality
  simp [economicQualitativeImage, qualitativeImage, economicImage,
    RootedAccountedUnfolding.fold,
    economicAlgebra, generatedEconomicImagePoint] at repair_eq
  cases repair_eq

/-- Even after quantitative and qualitative evaluation share one fold,
the quantitative projection alone still cannot reconstruct the qualitative
source authority on both exact occurrences. -/
theorem no_quantitative_image_reconstructs_qualitative_image :
    ¬ ∃ reconstruct : List Nat →
        List (Bool × ExactExitFailureKind × ExactExitRepair),
      reconstruct (economicQuantitativeImage tenureRepairExposure) =
          economicQualitativeImage tenureRepairExposure ∧
        reconstruct (economicQuantitativeImage routeRepairExposure) =
          economicQualitativeImage routeRepairExposure := by
  rintro ⟨reconstruct, tenureExact, routeExact⟩
  apply tenure_route_qualitative_images_distinct
  calc
    economicQualitativeImage tenureRepairExposure =
        reconstruct (economicQuantitativeImage tenureRepairExposure) :=
      tenureExact.symm
    _ = reconstruct (economicQuantitativeImage routeRepairExposure) :=
      congrArg reconstruct tenure_route_quantitative_images_equal
    _ = economicQualitativeImage routeRepairExposure := routeExact

end
end M14EconomicSingleFold
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14EconomicSingleFold.constructorCompatibleEvaluator_eq_economicImage
#print axioms SaturationMonoid.ProcessGame.Society.M14EconomicSingleFold.economic_frontier_advance
#print axioms SaturationMonoid.ProcessGame.Society.M14EconomicSingleFold.economic_advance_assoc
#print axioms SaturationMonoid.ProcessGame.Society.M14EconomicSingleFold.tenure_quantitative_image_at
#print axioms SaturationMonoid.ProcessGame.Society.M14EconomicSingleFold.no_quantitative_image_reconstructs_qualitative_image

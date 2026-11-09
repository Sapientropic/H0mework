import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Root.Compile
import H0mework.Versions.R2.Foundation.Inquiry.RevisionRecovery

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open ObstructionGeneratedMinimalCoface TypedSemanticWorldNetworkU8
open Capitalism.Universal.Abolition.Accounting.Root
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint
open Capitalism.Universal.Abolition.Root.Registered.Macro
open Reparation.Actual (First Resident identityWhole)

noncomputable section

variable {N : WorldRelationNetwork.{0}} {OldV : ConstructiveRoot.Vocabulary.{0}}
  {oldWorld : SourceNativeAuthoritativeRootClosure N OldV}
  {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
  {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
  {support : N.Support} {obstruction : N.ObstructionAt support}
  {failure : ActualExpressibilityFailure oldTheory obstruction}
  (rooted : RootedActualExpressibilityFailureAt oldWorld oldVisit U7 failure)

local notation "Coface" => root_obstruction_generates_minimal_coface rooted
local notation "OldSupport" => oldWorld.toRoot.supportAt rooted.oldSuccessor.next
local notation "OldRows" => OpenResponsibilityAt N OldSupport
local notation "NewRows" =>
  OpenResponsibilityAt (GeneratedMinimalCofaceAt.worldNetwork Coface) (GeneratedMinimalCofaceAt.cofaceSupport Coface)

private def cofaceRows : (OldRows ⊕ Unit) ≃ NewRows where
  toFun := Sum.elim (Coface).cofaceLedgerRetract.forward (fun _ => (Coface).obstructionEntry)
  invFun := by
    rintro ⟨responsibility, opened⟩
    cases responsibility with
    | inl old => exact .inl ⟨old, opened⟩
    | inr _ => exact .inr ()
  left_inv := by rintro (row | ⟨⟩) <;> rfl
  right_inv := by
    rintro ⟨responsibility, opened⟩
    cases responsibility with
    | inl _ => rfl
    | inr direction =>
      cases direction
      cases opened
      rfl

private theorem cofaceFinite (finite : Finite OldRows) : Finite NewRows := by
  let _ : Finite OldRows := finite
  exact Finite.of_equiv (OldRows ⊕ Unit) (cofaceRows rooted)

private theorem cofaceFibres (oldFibres : ∀ s row, Subsingleton (N.OpenAt s row)) :
    ∀ s row, Subsingleton ((Coface).worldNetwork.OpenAt s row) := by
  intro s row
  cases s with
  | inl s =>
    cases row with
    | inl row => exact oldFibres s row
    | inr _ => exact ⟨fun impossible _ => nomatch impossible⟩
  | inr s =>
    cases row with
    | inl row => exact oldFibres OldSupport row
    | inr row =>
      constructor
      intro left right
      cases left
      cases right
      rfl

variable (oldFinite : Finite (OpenResponsibilityAt N (oldWorld.toRoot.supportAt rooted.oldSuccessor.next)))
  (oldFibres : ∀ s row, Subsingleton (N.OpenAt s row))

/-- Enumerate the existing ledger and the generated direction on the
canonical coface. The first write carries every row without refilling it. -/
def revisedFirst : First (Coface).worldNetwork where
  before := (Coface).cofaceSupport
  after := (Coface).cofaceSupport
  whole := identityWhole _
  beforeFinite := cofaceFinite rooted oldFinite
  afterFinite := cofaceFinite rooted oldFinite
  openFibres := cofaceFibres rooted oldFibres
  writes := true

local notation "Flow" => First.flow (revisedFirst rooted oldFinite oldFibres)

def oldReads : SourceNativeProjectionLaw (Compiler.ledgerSource Flow) :=
  QueryHistory.freeze oldWorld.source.projectionLaw (oldWorld.emitted rooted.oldSuccessor.next)
    (Compiler.ledgerSource Flow)

variable
  (oldUnique : ∀ actual : oldWorld.toRoot.actual.OccurrenceAt rooted.oldSuccessor.next,
    actual = oldWorld.emitted rooted.oldSuccessor.next)

variable {Payload : Type} (payload : Payload)

def newRead : SourceNativeProjectionLaw (Compiler.ledgerSource Flow) where
  Projection := PUnit
  ActiveAt := fun _ {current} _ => PLift (current = true)
  InactiveAt := fun _ {current} _ => PLift (current ≠ true)
  classify := fun _ {current} _ =>
    letI : Decidable (current = true) := decEq (α := Bool) current true
    if landed : current = true then .inl ⟨landed⟩ else .inr ⟨landed⟩
  PayloadAt := fun _ {_} _ _ => Payload
  project := fun _ {_} _ _ => payload

def revisedRoot : SourceNativeLivingRootClosure (Coface).worldNetwork (Compiler.V Flow) :=
  ((Compiler.livingRoot Flow).withProjectionCoface (oldReads rooted oldFinite oldFibres)).withProjectionCoface
    (newRead rooted oldFinite oldFibres payload)

local notation "Root" => revisedRoot rooted oldFinite oldFibres payload

private def occurrencePresentation :
    ConstructivePresentation (oldWorld.toRoot.actual.OccurrenceAt rooted.oldSuccessor.next)
      ((Root).toAuthoritativeRoot.toRoot.actual.OccurrenceAt
        (Root).toAuthoritativeRoot.toRoot.source.initial) where
  forward := fun _ => (Root).emitted (Root).toAuthoritativeRoot.toRoot.source.initial
  backward := fun _ => oldWorld.emitted rooted.oldSuccessor.next
  backward_forward := fun actual => (oldUnique actual).symm
  forward_backward := fun actual => (Compiler.occurrence_eq_emitted Flow actual).symm

def generated : GeneratedTypedSemanticWorldNetworkRevisionAt rooted where
  NewN := (Coface).worldNetwork
  translation := (Coface).translation
  NewV := Compiler.V Flow
  newLivingRoot := Root
  new_support_restricts := (Coface).firstWrite_targetSupport_is_cofaceRestriction
  oldTargetOpenLedger := (Coface).cofaceLedgerRetract
  oldTargetOpenClaim_commutes := fun _ => rfl
  oldTargetOpenProgressBudget_not_refilled := fun _ => Nat.le_refl _
  occurrencePresentation := occurrencePresentation rooted oldFinite oldFibres oldUnique payload
  occurrence_commutes := rfl
  firstWrite := PUnit.unit
  newOnlyEntry := (Coface).obstructionEntry
  newOnlyProgressBudget_eq_zero := rfl
  revisedClaimHolds := (Coface).obstructionClaimHolds
  semanticChange := (Coface).obstructionSemanticChange
  revisedClaim_hasNoOldPreimage := (Coface).obstructionClaim_hasNoOldPreimage
  newOnlyIncidence_hasNoOldPreimage := (Coface).obstructionIncidence_hasNoOldPreimage
  oldEntryRows := fun row => Compiler.generatedRow Flow (Compiler.initialVisit Flow)
    ((Coface).cofaceLedgerRetract.forward row)
  newOnlyEntry_hasNoOldPreimage := (Coface).obstructionEntry_hasNoOldPreimage
  newOnlyEntryRow := Compiler.generatedRow Flow (Compiler.initialVisit Flow) (Coface).obstructionEntry

private theorem grounded :
    (generated rooted oldFinite oldFibres oldUnique payload).ExactFieldGrounding where
  network_eq := rfl
  lawSurface_heq := HEq.rfl
  translation_heq := HEq.rfl
  initialSupport_heq := HEq.rfl
  oldTargetOpenLedger_heq := HEq.rfl
  newOnlyEntry_heq := HEq.rfl
  revisedClaimHolds_heq := HEq.rfl
  semanticChange_heq := HEq.rfl

/-- The revised source and its first write are built from the old
target ledger. The payload becomes a face of that revised source. -/
def realize : FieldGroundedTypedSemanticWorldNetworkRevisionAt rooted :=
  .ofGeneratedOccurrence (generated rooted oldFinite oldFibres oldUnique payload)
    (grounded rooted oldFinite oldFibres oldUnique payload)

def answerAndNext :=
  TypedSemanticWorldNetworkU8Recovery.factorizesThroughInitialCofaceAnswerAndNext
    (realize rooted oldFinite oldFibres oldUnique payload)

local notation "InitialVisit" => Compiler.initialVisit Flow
local notation "Successor" => Compiler.successor Flow false
local notation "NewEntry" => GeneratedMinimalCofaceAt.obstructionEntry Coface

/-- The returned resident is the generated target of the revised first
write. Its focus is the new direction's own causal row. -/
def landing : Resident (Coface).worldNetwork where
  V := Compiler.V Flow
  root := Root
  visit := (InitialVisit).next (Successor).next_eq
  entry := (Root).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext (Successor).next_eq NewEntry
  authority := (SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    (Root) NewEntry (Compiler.generatedRow Flow InitialVisit NewEntry)).next (Successor).next_eq
  unique := Compiler.occurrence_eq_emitted Flow

theorem landing_is_the_generated_first_target :
    (⟨(Coface).worldNetwork, (Root).generatedNextCurrentAt InitialVisit⟩ : AnyAuthoritativeRootCurrent) =
      (landing rooted oldFinite oldFibres payload).erase :=
  congrArg (fun next => (⟨(Coface).worldNetwork, next⟩ : AnyAuthoritativeRootCurrent))
    (Ingress.next_is_the_same_generated_successor (Root) InitialVisit Successor)

theorem landing_support :
    (landing rooted oldFinite oldFibres payload).support = (Coface).cofaceSupport :=
  congrArg (Flow).support (Compiler.successor_current Flow false)

def landingFace :
    SourceNativeRootSemanticFaceAt (Root) (landing rooted oldFinite oldFibres payload).visit where
  projection := .component PUnit.unit
  active := ⟨Compiler.successor_current Flow false⟩
  classifier_eq := by
    let arrived := (landing rooted oldFinite oldFibres payload).visit.current
    let _ : Decidable (arrived = true) := decEq (α := Bool) arrived true
    change (if landed : arrived = true then Sum.inl (PLift.up landed) else Sum.inr (PLift.up landed)) =
      Sum.inl (PLift.up (Compiler.successor_current Flow false))
    exact dif_pos (Compiler.successor_current Flow false)

theorem landing_reads_the_payload :
    HEq (landingFace rooted oldFinite oldFibres payload).rootRead payload :=
  HEq.rfl

theorem landing_preserves_the_old_dependent_read (projection : oldWorld.source.projectionLaw.Projection) :
    let arrived := landing rooted oldFinite oldFibres payload
    HEq (arrived.root.source.base.projectionLaw.outcomeAt (.inherited (.component projection))
      (arrived.root.emitted arrived.visit.current))
      (oldWorld.source.projectionLaw.outcomeAt projection (oldWorld.emitted rooted.oldSuccessor.next)) := by
  let base := Compiler.livingRoot Flow
  let frozen := oldReads rooted oldFinite oldFibres
  let publish := newRead rooted oldFinite oldFibres payload
  let install := (SourceNativeProjectionLaw.InstallationAt.componentCoface base.source.base frozen).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (base.withProjectionCoface frozen).source.base publish)
  let atTarget := (landing rooted oldFinite oldFibres payload).visit.current
  let occurrence := Compiler.emitted Flow atTarget
  exact (install.outcome_heq occurrence projection).trans
    (QueryHistory.every_frozen_outcome_is_the_same_original_dependent_outcome
      oldWorld.source.projectionLaw (oldWorld.emitted rooted.oldSuccessor.next)
      (Compiler.ledgerSource Flow) occurrence projection)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network

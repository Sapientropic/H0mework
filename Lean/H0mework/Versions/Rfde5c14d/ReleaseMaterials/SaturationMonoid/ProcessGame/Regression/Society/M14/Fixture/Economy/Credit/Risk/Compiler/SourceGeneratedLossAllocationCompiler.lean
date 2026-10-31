import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.SourceGeneratedLossAllocationWorld

/-!
# M14 source-generated loss-allocation compiler

The initial actual event is indexed by the zero-choice C4/C5 economic
material.  Its first finite patch has exactly three generated rows: the same
translated parent is maintained to existing-leg children `a` and `b` with
budget `2 -> 1`, while the canonical obstruction is transferred unchanged
with budget `0 -> 0`.  The target is the complete three-entry ledger; no row,
origin, target, coverage table, or future is accepted from a caller.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedLossAllocationCompiler

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ObstructionGeneratedMinimalCoface TypedSemanticWorldNetworkU8
open Lifecycle Universal Relations Exchange
open M3FiniteExchangeFixture
open M3ExchangeSettlementPriceRegression
open M14ClearingConsumerDeath
open M14SourceGeneratedClearingBackstopActivation
open M14SourceClearingBackstopCreditStanding
open M14SourceGeneratedLossAllocationMaterial
open M14SourceGeneratedLossAllocationWorld

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

/-! ## Material-indexed actual source -/

def lossAllocationSupportAt (rooted : RootedFailure) : Nat -> (LossN rooted).Support
  | 0 => lossAllocationInitialSupport rooted
  | _ + 1 => lossAllocationTargetSupport rooted

structure SourceGeneratedLossAllocationEventAt
    (rooted : RootedFailure) (current : Nat)
    (indexedSupport : (LossN rooted).Support) : Type where
  private mk ::
  supportExact : PLift
    (indexedSupport = lossAllocationSupportAt rooted current)
  materialWitness : ExactSourceGeneratedLossAllocationMaterialWitness
  materialExact : materialWitness =
    exactSourceGeneratedLossAllocationMaterialWitness

abbrev lossAllocationRootVocabulary (rooted : RootedFailure) :
    ConstructiveRoot.Vocabulary where
  Current := Nat
  Anchor := (LossN rooted).Anchor
  Incidence := (LossN rooted).Incidence
  Lineage := (LossN rooted).Lineage
  anchorAt := fun current =>
    (LossN rooted).anchorAt (lossAllocationSupportAt rooted current)
  incidenceAt := fun current =>
    (LossN rooted).incidenceAt (lossAllocationSupportAt rooted current)
  lineageAt := fun current =>
    (LossN rooted).lineageAt (lossAllocationSupportAt rooted current)
  NativeWriteAt := fun _ => Unit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {current} _ => current + 1
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev LossV (rooted : RootedFailure) := lossAllocationRootVocabulary rooted

def lossAllocationEventLaw (rooted : RootedFailure) :
    SourceNativeEventAlgebra (LossN rooted) (LossV rooted) where
  EventAt := SourceGeneratedLossAllocationEventAt rooted
  compile := fun _ => .nativeWrite ()
  AffectedInventoryAt := fun {_} {indexedSupport} _ =>
    OpenResponsibilityAt (LossN rooted) indexedSupport
  affectedInventoryPresentation := fun _ => ConstructivePresentation.refl _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by
    intro current indexedSupport event
    cases event.supportExact.down
    rfl
  incidence_commutes := by
    intro current indexedSupport event
    cases event.supportExact.down
    rfl
  lineage_commutes := by
    intro current indexedSupport event
    cases event.supportExact.down
    rfl

def lossAllocationSource (rooted : RootedFailure) :
    SourceNativeSource (LossN rooted) (LossV rooted) where
  initial := 0
  law := lossAllocationEventLaw rooted

def lossAllocationEmitted (rooted : RootedFailure)
    (current : (LossV rooted).Current) :
    (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt current :=
  ⟨lossAllocationSupportAt rooted current,
    ⟨PLift.up rfl, exactSourceGeneratedLossAllocationMaterialWitness,
      rfl⟩⟩

theorem lossAllocationOccurrence_eq_emitted
    (rooted : RootedFailure)
    {current : (LossV rooted).Current}
    (occurrence :
      (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt current) :
    occurrence = lossAllocationEmitted rooted current := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  cases event.materialExact
  cases event
  rfl

/-- The actual event exposes the entire low-universe material witness.  These
six fields are consumed from the occurrence itself; none is a detached
standing or bearer readout. -/
theorem lossAllocationOccurrence_whole_material_exact
    (rooted : RootedFailure)
    {current : (LossV rooted).Current}
    (occurrence :
      (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt current) :
    sourceGeneratedLossAllocationMaterial.defaultOccurrence =
        M14ClearingConsumerDeath.sourceGeneratedClearingConsumerDeath ∧
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
  ⟨occurrence.2.materialWitness.defaultExact,
    occurrence.2.materialWitness.activationSeedExact,
    occurrence.2.materialWitness.standingExact,
    occurrence.2.materialWitness.parentBearerExact,
    occurrence.2.materialWitness.childBearerExact,
    occurrence.2.materialWitness.childBearersDistinct⟩

/-! ## Exact first-write rows -/

def LossAllocationExactTransitionAt (rooted : RootedFailure) :
    {current : (LossV rooted).Current} ->
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      current) ->
    {targetSupport : (LossN rooted).Support} ->
    OpenResponsibilityAt (LossN rooted)
      ((lossAllocationSource rooted).toRootSource.account.supportOf occurrence) ->
    OpenResponsibilityAt (LossN rooted) targetSupport -> Type :=
  fun {_} _ {_} sourceEntry targetEntry =>
    LedgerEntryEvolutionAt (LossN rooted) sourceEntry targetEntry

def lossAllocationWriteRowSource (rooted : RootedFailure) :
    LedgerWriteRowSourceAt (lossAllocationSource rooted)
      (LossAllocationExactTransitionAt rooted) where
  IncidenceOccurrenceAt := fun {_} _ {_} sourceEntry targetEntry =>
    LedgerEntryEvolutionAt (LossN rooted) sourceEntry targetEntry
  compileEvolution := fun evolution => evolution
  compileExact := fun evolution => evolution

def lossAllocationParentToChildA (rooted : RootedFailure) :
    LedgerEntryEvolutionAt (LossN rooted)
      (lossAllocationInitialParent rooted)
      (lossAllocationTargetChildA rooted) :=
  .maintained rfl rfl rfl rfl rfl (by
    change 1 < 2
    decide)

def lossAllocationParentToChildB (rooted : RootedFailure) :
    LedgerEntryEvolutionAt (LossN rooted)
      (lossAllocationInitialParent rooted)
      (lossAllocationTargetChildB rooted) :=
  .maintained rfl rfl rfl rfl rfl (by
    change 1 < 2
    decide)

/-- `0 -> 0` is continuity only: because support changes, it is an exact
transfer and never a maintenance debit or carried row. -/
def lossAllocationObstructionContinuity (rooted : RootedFailure) :
    LedgerEntryEvolutionAt (LossN rooted)
      (lossAllocationInitialObstruction rooted)
      (lossAllocationTargetObstruction rooted) :=
  .transferred
    (GeneratedMinimalCofaceAt.CofaceTargetDispositionAt.ofTarget ())
    rfl rfl (Nat.le_refl 0)

def lossAllocationFirstSourceEntryAt (rooted : RootedFailure) :
    Fin 3 -> (lossAllocationInitialLedger rooted).Entry :=
  Fin.cases (lossAllocationInitialParent rooted)
    (Fin.cases (lossAllocationInitialParent rooted)
      (fun _ => lossAllocationInitialObstruction rooted))

def lossAllocationFirstTargetEntryAt (rooted : RootedFailure) :
    Fin 3 -> (lossAllocationTargetLedger rooted).Entry :=
  Fin.cases (lossAllocationTargetChildA rooted)
    (Fin.cases (lossAllocationTargetChildB rooted)
      (fun _ => lossAllocationTargetObstruction rooted))

def lossAllocationFirstRows (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) :
    FiniteGeneratedLedgerWriteRowsAt (lossAllocationWriteRowSource rooted)
      occurrence (lossAllocationTargetLedger rooted) := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  exact
    { size := 3
      sourceEntryAt := lossAllocationFirstSourceEntryAt rooted
      targetEntryAt := lossAllocationFirstTargetEntryAt rooted
      rowAt := Fin.cases
        ((lossAllocationWriteRowSource rooted).generate
          (lossAllocationParentToChildA rooted))
        (Fin.cases
          ((lossAllocationWriteRowSource rooted).generate
            (lossAllocationParentToChildB rooted))
          (fun _ => (lossAllocationWriteRowSource rooted).generate
            (lossAllocationObstructionContinuity rooted))) }

def lossAllocationInitialEntryIndex (rooted : RootedFailure) :
    (lossAllocationInitialLedger rooted).Entry -> Fin 3
  | ⟨.inl _, _⟩ => ⟨0, by decide⟩
  | ⟨.inr _, _⟩ => ⟨2, by decide⟩

def lossAllocationTargetEntryIndex (rooted : RootedFailure) :
    (lossAllocationTargetLedger rooted).Entry -> Fin 3
  | ⟨.inl _, ⟨.a, _⟩⟩ => ⟨0, by decide⟩
  | ⟨.inl _, ⟨.b, _⟩⟩ => ⟨1, by decide⟩
  | ⟨.inl _, ⟨.c, impossible⟩⟩ =>
      False.elim (by rcases impossible with h | h <;> cases h)
  | ⟨.inl _, ⟨.d, impossible⟩⟩ =>
      False.elim (by rcases impossible with h | h <;> cases h)
  | ⟨.inr _, _⟩ => ⟨2, by decide⟩

theorem lossAllocationFirstSourceEntryAt_index
    (rooted : RootedFailure)
    (entry : (lossAllocationInitialLedger rooted).Entry) :
    lossAllocationFirstSourceEntryAt rooted
        (lossAllocationInitialEntryIndex rooted entry) = entry := by
  rcases entry with ⟨responsibility, isOpen⟩
  cases responsibility with
  | inl oldResponsibility =>
      cases oldResponsibility
      cases isOpen
      rfl
  | inr direction =>
      cases isOpen
      rfl

theorem lossAllocationFirstTargetEntryAt_index
    (rooted : RootedFailure)
    (entry : (lossAllocationTargetLedger rooted).Entry) :
    lossAllocationFirstTargetEntryAt rooted
        (lossAllocationTargetEntryIndex rooted entry) = entry := by
  rcases entry with ⟨responsibility, isOpen⟩
  cases responsibility with
  | inl oldResponsibility =>
      cases oldResponsibility
      rcases isOpen with ⟨leg, admitted⟩
      cases leg with
      | a => rfl
      | b => rfl
      | c => rcases admitted with h | h <;> cases h
      | d => rcases admitted with h | h <;> cases h
  | inr direction =>
      cases isOpen
      rfl

def lossAllocationFirstPatch (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) :
    FiniteGeneratedLedgerWritePatchAt (lossAllocationWriteRowSource rooted)
      occurrence (lossAllocationTargetLedger rooted) := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  exact .complete
    (lossAllocationFirstRows rooted
      ⟨lossAllocationInitialSupport rooted, event⟩)
    { destinationIndex := lossAllocationInitialEntryIndex rooted
      originIndex := lossAllocationTargetEntryIndex rooted
      destination_sound := lossAllocationFirstSourceEntryAt_index rooted
      origin_sound := lossAllocationFirstTargetEntryAt_index rooted }

def lossAllocationFirstEvolution (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) :
    LedgerWriteEvolutionAt (LossN rooted)
      (lossAllocationInitialLedger rooted)
      (lossAllocationTargetLedger rooted) := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  exact (lossAllocationFirstPatch rooted
    ⟨lossAllocationInitialSupport rooted, event⟩).toLedgerWriteEvolution

@[simp] theorem lossAllocationFirst_origin_childA
    (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) :
    ((lossAllocationFirstEvolution rooted occurrence).origin
      (lossAllocationTargetChildA rooted)).1 =
        lossAllocationInitialParent rooted := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  rfl

@[simp] theorem lossAllocationFirst_origin_childB
    (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) :
    ((lossAllocationFirstEvolution rooted occurrence).origin
      (lossAllocationTargetChildB rooted)).1 =
        lossAllocationInitialParent rooted := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  rfl

@[simp] theorem lossAllocationFirst_origin_obstruction
    (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) :
    ((lossAllocationFirstEvolution rooted occurrence).origin
      (lossAllocationTargetObstruction rooted)).1 =
        lossAllocationInitialObstruction rooted := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  rfl

@[simp] theorem lossAllocationFirst_destination_parent
    (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) :
    ((lossAllocationFirstEvolution rooted occurrence).destination
      (lossAllocationInitialParent rooted)).1 =
        lossAllocationTargetChildA rooted := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  rfl

@[simp] theorem lossAllocationFirst_destination_obstruction
    (rooted : RootedFailure)
    (occurrence : (lossAllocationSource rooted).toRootSource.actual.OccurrenceAt
      0) :
    ((lossAllocationFirstEvolution rooted occurrence).destination
      (lossAllocationInitialObstruction rooted)).1 =
        lossAllocationTargetObstruction rooted := by
  rcases occurrence with ⟨indexedSupport, event⟩
  cases event.supportExact.down
  rfl

/-! ## Whole-ledger compiler -/

def lossAllocationLedgerCompiler (rooted : RootedFailure) :
    SourceNativeLedgerCompiler (lossAllocationSource rooted) where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := LossAllocationExactTransitionAt rooted
  exact_incidence := fun _ => ()
  exact_lineage := by
    intro current occurrence targetSupport sourceEntry targetEntry evolution
    cases evolution with
    | carried support_eq entry_eq =>
        cases support_eq
        cases entry_eq
        rfl
    | maintained _ _ lineage_eq _ _ _ => exact lineage_eq
    | transferred _ lineage_eq _ _ => exact lineage_eq
  writeRowSource := lossAllocationWriteRowSource rooted
  terminalRowSource := LedgerTerminalRowSourceAt.empty
    (lossAllocationSource rooted)
  compile := by
    intro current occurrence
    cases current with
    | zero =>
        rcases occurrence with ⟨indexedSupport, event⟩
        cases event.supportExact.down
        exact .nativeWrite () rfl (lossAllocationEmitted rooted 1)
          (lossAllocationFirstEvolution rooted
            ⟨lossAllocationInitialSupport rooted, event⟩)
    | succ current =>
        rcases occurrence with ⟨indexedSupport, event⟩
        cases event.supportExact.down
        exact .nativeWrite () rfl
          (lossAllocationEmitted rooted (Nat.succ current + 1))
          ((FiniteGeneratedLedgerWritePatchAt.identity
            (lossAllocationWriteRowSource rooted)
              ⟨lossAllocationTargetSupport rooted, event⟩
            ).toLedgerWriteEvolution)
  compilePatch := by
    intro current occurrence
    cases current with
    | zero =>
        rcases occurrence with ⟨indexedSupport, event⟩
        cases event.supportExact.down
        exact ⟨lossAllocationFirstPatch rooted
          ⟨lossAllocationInitialSupport rooted, event⟩, rfl⟩
    | succ current =>
        rcases occurrence with ⟨indexedSupport, event⟩
        cases event.supportExact.down
        exact ⟨FiniteGeneratedLedgerWritePatchAt.identity
          (lossAllocationWriteRowSource rooted)
            ⟨lossAllocationTargetSupport rooted, event⟩, rfl⟩

theorem lossAllocationCompiler_firstWrite_exact
    (rooted : RootedFailure) :
    (lossAllocationLedgerCompiler rooted).compile
        (lossAllocationEmitted rooted 0) =
      .nativeWrite () rfl (lossAllocationEmitted rooted 1)
        (lossAllocationFirstEvolution rooted
          (lossAllocationEmitted rooted 0)) :=
  rfl

theorem lossAllocationCompiler_commutes
    (rooted : RootedFailure)
    (current : (LossV rooted).Current) :
    SourceNativeLedgerEvolutionAt.CommutesWith
      (lossAllocationEmitted rooted)
      ((lossAllocationLedgerCompiler rooted).compile
        (lossAllocationEmitted rooted current)) := by
  cases current with
  | zero => rfl
  | succ current => rfl

theorem lossAllocationSource_is_indexed_by_exact_material
    (rooted : RootedFailure) :
    Nonempty (SourceGeneratedLossAllocationEventAt rooted 0
      (lossAllocationInitialSupport rooted)) :=
  ⟨⟨PLift.up rfl,
    exactSourceGeneratedLossAllocationMaterialWitness, rfl⟩⟩

end
end M14SourceGeneratedLossAllocationCompiler
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedLossAllocationCompiler.lossAllocationFirstEvolution
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedLossAllocationCompiler.lossAllocationLedgerCompiler
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedLossAllocationCompiler.lossAllocationCompiler_firstWrite_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedLossAllocationCompiler.lossAllocationCompiler_commutes
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedLossAllocationCompiler.lossAllocationOccurrence_eq_emitted
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedLossAllocationCompiler.lossAllocationOccurrence_whole_material_exact

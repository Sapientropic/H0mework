import H0mework.Physics.EmpiricalContact.World

/-! The received raw table participates in the first native action. One
complete row preserves the physical account and records its empirical residual. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Empirical.ContactEpoch

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Stage9C.Revision ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource

noncomputable section

def vocabulary : Vocabulary where
  Current := Current
  Anchor := N.Anchor
  Incidence := Support
  Lineage := N.Lineage
  anchorAt := fun _ => positiveSmoothUnifiedSource
  incidenceAt := support
  lineageAt := fun _ => positiveSmoothUnifiedSource
  NativeWriteAt := ActionAt
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := actionTarget
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev V := vocabulary

structure EventAt (current : Current) (where_ : Support) : Type where
  support_eq : where_ = support current
  action : ActionAt current

def eventAlgebra : SourceNativeEventAlgebra N V where
  EventAt := EventAt
  compile := fun event => .nativeWrite event.action
  AffectedInventoryAt := fun _ => PUnit
  affectedInventoryPresentation := by
    intro current where_ event
    cases event.support_eq
    exact ⟨fun _ => entry _, fun _ => PUnit.unit, fun _ => rfl,
      fun candidate => (entry_unique _ candidate).symm⟩
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun event => event.support_eq.symm
  lineage_commutes := fun _ => rfl

def source : SourceNativeSource N V := ⟨.ingress, eventAlgebra⟩

def emitted (current : Current) : source.toRootSource.actual.OccurrenceAt current :=
  ⟨support current, ⟨rfl, actionAt current⟩⟩

theorem occurrence_unique {current : Current}
    (occurrence : source.toRootSource.actual.OccurrenceAt current) : occurrence = emitted current := by
  rcases occurrence with ⟨_, ⟨same, action⟩⟩
  cases same
  cases action_unique action
  rfl

structure ExactTransitionAt (current : Current) (where_ : Support) : Type where
  target_eq : where_ = support (next current)

def writeRowSource : LedgerWriteRowSourceAt source (by
    intro current _ where_ _ _
    exact ExactTransitionAt current where_) where
  IncidenceOccurrenceAt := fun {current} _ where_ _ _ => ExactTransitionAt current where_
  compileEvolution := by
    intro current occurrence where_ oldEntry newEntry event
    cases occurrence_unique occurrence
    cases event.target_eq
    cases entry_unique _ oldEntry
    cases entry_unique _ newEntry
    exact .transferred (.transfer (actionAt current)) rfl rfl (Nat.le_refl _)
  compileExact := fun event => event

def occurrenceEntry {current : Current} (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt N occurrence.1 :=
  (source.law.affectedInventoryPresentation occurrence.2).forward PUnit.unit

def generatedRows {current : Current} (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt writeRowSource occurrence
      (⟨support (next current)⟩ : CompleteLiveLedgerAt N) where
  size := 1
  sourceEntryAt := fun _ => occurrenceEntry occurrence
  targetEntryAt := fun _ => entry (support (next current))
  rowAt := fun _ => writeRowSource.generate ⟨rfl⟩

def generatedCoverage {current : Current} (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    LedgerCompleteFiniteCoverageAt (generatedRows occurrence) where
  destinationIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  originIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  destination_sound := fun candidate =>
    (source.law.affectedInventoryPresentation occurrence.2).forward_backward candidate
  origin_sound := fun candidate => (entry_unique _ candidate).symm

def generatedPatch {current : Current} (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt writeRowSource occurrence
      (⟨support (next current)⟩ : CompleteLiveLedgerAt N) :=
  .complete (generatedRows occurrence) (generatedCoverage occurrence)

def generatedEvolution {current : Current} (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt source occurrence :=
  .nativeWrite (actionAt current) (by cases occurrence_unique occurrence; rfl)
    (emitted (next current)) (generatedPatch occurrence).toLedgerWriteEvolution

def ledgerCompiler : SourceNativeLedgerCompiler source where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := fun {current} _ where_ _ _ => ExactTransitionAt current where_
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := writeRowSource
  terminalRowSource := LedgerTerminalRowSourceAt.empty _
  compile := generatedEvolution
  compilePatch := fun occurrence => ⟨generatedPatch occurrence, rfl⟩

private def restructuringLaw : SourceNativeLedgerRestructuringLaw source :=
  identityOnlyWorldLedgerRestructuringLaw source positiveSmoothUnifiedSource <| by
    intro where_ responsibility
    constructor
    rintro ⟨left⟩ ⟨right⟩
    rfl

private def restructuringCompiler : SourceNativeRestructuringLedgerCompiler source where
  ledgerCompiler := ledgerCompiler
  restructuringLaw := restructuringLaw
  certifyRestructuring := fun _ => ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right _ => (entry_unique _ left).trans (entry_unique _ right).symm)
    (fun left right _ => (entry_unique _ left).trans (entry_unique _ right).symm)

def restructuringSource : SourceNativeRestructuringLedgerSource N V := ⟨source, restructuringCompiler⟩

def fieldAt (current : Current) : Stage9DEF.Source.OccupiedField :=
  Stage9DEF.Source.restrict (materialConfiguration (support current).1)

/-- Actual obstruction generation uses the numerical residual, never a caller verdict. -/
def auditDemand (current : Current) : Option (N.ObstructionAt (support current)) := by
  classical
  cases current with
  | ingress => exact none
  | active physical contact =>
      exact if positive : 0 < contactResidual contact then
        some (.inr ⟨contact, rfl, positive⟩) else none

theorem received_auditDemand : (auditDemand (next .ingress)).isSome = true := by
  simp [auditDemand, next, actionAt, actionTarget, released_contact_residual_positive]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.Empirical.ContactEpoch

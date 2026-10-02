import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Restructuring.Runtime
import H0mework.Versions.R2.Foundation.Cofinal.TemporalAnswer
import H0mework.Realization.Audit.DebtFirstWrite

/-! The existing source-owned handoff selects its next occurrence. Its actual
input inventory supplies a fresh mathematical request. The complete old event,
patch, raw input and paid past are installed before the new emitter. The next
source programme retains its own continuing scope. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Terminal
open SourceOperationEffects SourceOperationExecution DebtActivationWorld DebtActivationLedger
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt old.toAuthoritativeRoot.toLedgerRoot)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable {origin : V.Current}
variable (original : RegisteredAt (Value := Value) (Var := Var) (sort := sort) old.toAuthoritativeRoot.toLedgerRoot origin)
variable (past : EventAt original visit.current)

abbrev next := old.generatedNextCurrentAt visit

/-- The source generated both the whole old write and the exact patch which
folds to it; a terminal therefore remains a complete discharge in this data. -/
abbrev PastMaterial :=
  EventAt original visit.current × RawInputAt (Value := Value) (Var := Var) (sort := sort)
    old.toAuthoritativeRoot.toLedgerRoot origin (old.emitted origin) ×
  Σ generated : SourceNativeLedgerEvolutionAt old.toAuthoritativeRoot.toLedgerRoot.source.source (old.emitted visit.current),
    SourceNativeFiniteLedgerPatchAt old.toAuthoritativeRoot.toLedgerRoot.source.source
      old.toAuthoritativeRoot.toLedgerRoot.source.ledgerCompiler.ExactTransitionAt
      old.toAuthoritativeRoot.toLedgerRoot.source.ledgerCompiler.writeRowSource
      old.toAuthoritativeRoot.toLedgerRoot.source.ledgerCompiler.terminalRowSource generated

def archiveLaw : SourceNativeProjectionLaw (next old visit).root.toLedgerRoot.source where
  Projection := old.source.base.projectionLaw.Projection ⊕ PUnit
  ActiveAt := fun projection {_current} _occurrence => match projection with
    | .inl prior => old.source.base.projectionLaw.ActiveAt prior (old.emitted visit.current)
    | .inr _ => PUnit
  InactiveAt := fun projection {_current} _occurrence => match projection with
    | .inl prior => old.source.base.projectionLaw.InactiveAt prior (old.emitted visit.current)
    | .inr _ => PEmpty
  classify := fun projection {_current} _occurrence => match projection with
    | .inl prior => old.source.base.projectionLaw.classify prior (old.emitted visit.current)
    | .inr _ => .inl PUnit.unit
  PayloadAt := fun projection {_current} _occurrence active => match projection with
    | .inl prior => old.source.base.projectionLaw.PayloadAt prior (old.emitted visit.current) active
    | .inr _ => PastMaterial old visit original
  project := fun projection {_current} _occurrence active => match projection with
    | .inl prior => old.source.base.projectionLaw.project prior (old.emitted visit.current) active
    | .inr _ => ⟨past, original.input, old.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current,
        old.toAuthoritativeRoot.toLedgerRoot.generatedPatchAt visit.current⟩

def archivedSource := (next old visit).root.source.withProjectionCoface (archiveLaw old visit original past)

def observationLaw : SourceNativeProjectionLaw (next old visit).root.toLedgerRoot.source where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} _ _ => (old.source.base.observationAt (old.emitted visit.current)).1
  project := fun _ {_current} _ _ => (old.source.base.observationAt (old.emitted visit.current)).2

def authoritySource := (archivedSource old visit original past).withProjectionCoface (observationLaw old visit)

def authority : SourceNativeAuthoritativeRootClosure N (next old visit).V where
  source := authoritySource old visit original past
  emitted := (next old visit).root.emitted
  compiler_commutes := (next old visit).root.compiler_commutes

def archiveInstallation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
  (next old visit).root.source (archiveLaw old visit original past)).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      (archivedSource old visit original past) (observationLaw old visit))

def nextInstallation := (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (next old visit).root.source (archiveLaw old visit original past)).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      (archivedSource old visit original past) (observationLaw old visit))

def observationInstallation := SourceNativeProjectionLaw.InstallationAt.componentCoface
  (archivedSource old visit original past) (observationLaw old visit)

theorem law_epoch : (authority old visit original past).source.lawSurface = old.source.base.lawSurface :=
  old.generatedNextCurrentAt_lawSurface_eq visit

theorem archived_outcome (projection : old.source.base.projectionLaw.Projection)
    {current : (next old visit).V.Current}
    (occurrence : (next old visit).root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    HEq ((authority old visit original past).source.projectionLaw.outcomeAt
      ((archiveInstallation old visit original past).embed (.inl projection)) occurrence)
      (old.source.base.projectionLaw.outcomeAt projection (old.emitted visit.current)) := by
  have inherited := (archiveInstallation old visit original past).outcome_heq occurrence (.inl projection)
  apply inherited.trans
  unfold SourceNativeProjectionLaw.outcomeAt
  dsimp only [archiveLaw]
  cases old.source.base.projectionLaw.classify projection (old.emitted visit.current) <;> rfl

variable (reader : (occurrence : (next old visit).root.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
    (next old visit).visit.current) → RawInputAt (Value := Value) (Var := Var) (sort := sort)
      (next old visit).root.toLedgerRoot (next old visit).visit.current occurrence)

/-- The owner is read from the actual next source's inventory. It is not a
transported or resurrected copy of an archived old owner. -/
def request : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
    (authority old visit original past).toLedgerRoot (next old visit).visit.current := register reader

variable (programme : (current : (next old visit).V.Current) → Successor.Packet (next old visit).root.toLedgerRoot current)

abbrev mathRoot := Successor.Restructuring.livingRoot (authority old visit original past)
  (request old visit original past reader) programme
abbrev runtime := Successor.Restructuring.initialRuntime (authority old visit original past)
  (request old visit original past reader) programme

/-- Fresh admission is selected by the source action, independent of the old
terminal's discharge. Its support is the actual handoff target occurrence. -/
def admission : SourceOperationExecutionDebt.Settlement (initialEvent (request old visit original past reader)).state ⊕
    (Σ paid : GeneratedStepAt (Successor.CompilerFromPacketSourceLaw.scope (request old visit original past reader))
      (initialEvent (request old visit original past reader)).state,
      PLift (mathAction (initialEvent (request old visit original past reader)) = .inr paid) ×
      DebtAdmissionFirstWrite.SourceGeneratedDebtAdmissionFirstWriteAt
        ((next old visit).root.toRoot.supportAt (next old visit).visit.current)
        (DebtAdmissionFirstWrite.SourceFixedDebtAdmissionEventAt.ofStep (law := Successor.CompilerFromPacketSourceLaw.scope (request old visit original past reader)) paid.2)) := by
  cases action : mathAction (initialEvent (request old visit original past reader)) with
  | inl settled => exact .inl settled
  | inr paid => exact .inr ⟨paid, ⟨rfl⟩, DebtAdmissionFirstWrite.generate _ (.ofStep (law := Successor.CompilerFromPacketSourceLaw.scope (request old visit original past reader)) paid.2)⟩

end RootGeneratedDebtActivationJointSource.Terminal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

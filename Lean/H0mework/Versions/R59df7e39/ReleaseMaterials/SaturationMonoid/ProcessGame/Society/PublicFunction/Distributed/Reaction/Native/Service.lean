import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Source
import H0mework.Foundation.Agency.OriginExit

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot ComplementObservation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument)

abbrev Slot := Fin source.code.task.slots.length

def slot (index : Slot source) := source.code.task.slots.get index

def Paid (depth : Nat) (index : Slot source) : Prop :=
  let actual := source.actualExecution depth
  source.code.task.earliest ≤ actual.before.clock ∧ actual.after.clock ≤ source.code.task.deadline ∧
    Institutions.Capitalism.Universal.Exit.Necessity.BundlePaid source.code.law actual.before
      actual.submitted (slot source index).bearer (slot source index).goods (slot source index).purpose

instance (depth : Nat) (index : Slot source) : Decidable (Paid source depth index) := by
  unfold Paid
  infer_instance

def seat : Fin (ProgrammeSource.registrationSize source.input) := ⟨0, by change 0 < 1; decide⟩
def registrationTarget := ProgrammeSource.targetEntry source.input .bootstrap (.instruction (seat source))

structure RegistrationReceipt where
  write : LedgerEntryEvolutionAt (ProgrammeSource.N source.input)
    ((ProgrammeLedger.evolution source.input .bootstrap).origin (registrationTarget source)).1 (registrationTarget source)
  written : write = ((ProgrammeLedger.evolution source.input .bootstrap).origin (registrationTarget source)).2
  debit : (registrationTarget source).progressBudget <
    (ProgrammeWorld.inheritedEntry (RawCurrent Party Good Technology Instrument)
      (ProgrammeSource.registrationSize source.input)).progressBudget

def registered : RegistrationReceipt source :=
  ⟨((ProgrammeLedger.evolution source.input .bootstrap).origin (registrationTarget source)).2, rfl,
    ProgrammeLedger.first_child_debit source.input (registrationTarget source) (by intro impossible; cases impossible)⟩

structure Event where
  index : Slot source
  ordinal : Nat

structure AdmissionAt (event : Event source) (index : Slot source) where
  registration : RegistrationReceipt source
  at_registration : event.ordinal = 0
  original : event.index = index

structure AssumptionAt (bearer : Fin (ProgrammeSource.registrationSize source.input))
    (event : Event source) (index : Slot source) extends AdmissionAt source event index where
  own_seat : bearer = seat source

structure FulfilledAt (event : Event source) (content scope : Slot source) : Type where
  content_eq : content = event.index
  scope_eq : scope = event.index
  running : 0 < event.ordinal
  paid : Paid source (event.ordinal - 1) event.index

structure RetainedAt (event : Event source) (content scope : Slot source) : Type where
  content_eq : content = event.index
  scope_eq : scope = event.index
  running : 0 < event.ordinal
  unpaid : ¬ Paid source (event.ordinal - 1) event.index

def vocabulary : ResponsibilityLifecycle.Vocabulary where
  SourceEvent := Event source
  Content := Slot source
  Residual := Bundle Good
  Bearer := Fin (ProgrammeSource.registrationSize source.input)
  ProtectedInterest := Party
  Scope := Slot source
  Lineage := Slot source
  Incidence := Slot source
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun event => MinimalRegistrableSourceAnchor.canonical event.index event.index
  sourceIncidence := Event.index
  ObstructionAt := fun _ => Empty
  demandContent := fun impossible => nomatch impossible
  demandResidual := fun impossible => nomatch impossible
  CommitmentAt := fun _ _ => Empty
  MandateOriginAt := fun _ _ => Empty
  AcceptedTaskAt := AdmissionAt source
  ActiveDependencyAt := fun _ _ => Empty
  ProtectedRiskAt := fun _ _ => Empty
  AdmissionAuthorityAt := AdmissionAt source
  AcceptedAt := AssumptionAt source
  StandingMandateAt := fun _ _ _ => Empty
  DischargeJurisdiction := fun content scope => PLift (content = scope)
  ProgressAt := fun _ _ _ _ => Empty
  MaintenanceAt := RetainedAt source
  TypedDeferAt := fun _ _ _ => Empty
  ScopeNarrowingAt := fun _ _ _ => Empty
  TransferAcceptedAt := fun _ _ _ _ => Empty
  FulfilledAt := FulfilledAt source
  WaivedAt := fun _ _ _ => Empty
  InvalidatedAt := fun _ _ _ => Empty
  AbandonedAt := fun _ _ _ => Empty
  ImpossibleResidueAcceptedAt := fun _ _ _ => Empty
  SupersessionAt := fun _ _ _ _ _ _ _ => Empty
  ReopenAt := fun _ _ _ _ _ _ _ => Empty
  JurisdictionEndedAt := fun _ _ _ => Empty
  ConsentRevokedAt := fun _ _ _ => Empty
  CapacityReleasedAt := fun _ _ _ => Empty
  UpperRouteAt := fun _ _ _ => Empty
  NextActorSignal := Nat
  AgeSignal := Nat
  TransferOfferSignal := Empty

abbrev V := vocabulary source

def admission (index : Slot source) : NativeAdmissionPayload (V source) where
  sourceEvent := ⟨index, 0⟩
  content := index
  residual := (slot source index).goods
  bearer := seat source
  beneficiary := (slot source index).bearer
  scope := index
  lineage := index
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .acceptedTask ⟨registered source, rfl, rfl⟩
  authority := ⟨registered source, rfl, rfl⟩
  assumption := .accepted ⟨⟨registered source, rfl, rfl⟩, rfl⟩
  dischargeJurisdiction := ⟨rfl⟩

def obligation (index : Slot source) := (admission source index).toObligation

structure Review (obligation : AdmittedObligation (V source)) where
  index : Slot source
  depth : Nat
  content_eq : obligation.content = index
  scope_eq : obligation.scope = index
  admission_eq : obligation.admission.sourceEvent.index = index

def reviewSource {obligation : AdmittedObligation (V source)} (event : Review source obligation) : Event source :=
  ⟨event.index, event.depth + 1⟩

def disposition {obligation : AdmittedObligation (V source)} (event : Review source obligation) :
    BoundaryDisposition (V source) obligation (reviewSource source event) :=
  if paid : Paid source event.depth event.index then
    .terminal (.final (.fulfilled ⟨event.content_eq, event.scope_eq, Nat.zero_lt_succ _, paid⟩))
  else .carry (.maintained ⟨event.content_eq, event.scope_eq, Nat.zero_lt_succ _, paid⟩)

def process : NativeResponsibilityProcess (V source) where
  AdmissionEvent := Slot source
  admissionPayload := admission source
  BoundaryEvent := Review source
  boundarySource := reviewSource source
  boundary_anchor_eq := by
    intro obligation event
    change MinimalRegistrableSourceAnchor.canonical event.index event.index =
      MinimalRegistrableSourceAnchor.canonical obligation.admission.sourceEvent.index obligation.admission.sourceEvent.index
    rw [event.admission_eq]
  boundary_incidence_eq := fun event => event.admission_eq.symm
  boundaryDisposition := disposition source
  ReopenEvent := fun _ => Empty
  reopenPayload := fun impossible => nomatch impossible

def review (index : Slot source) (depth : Nat) : Review source (obligation source index) :=
  ⟨index, depth, rfl, rfl, rfl⟩

def paidArchive (index : Slot source) (depth : Nat) (paid : Paid source depth index) : TerminalArchive (V source) :=
  ⟨obligation source index, ⟨index, depth + 1⟩, .fulfilled ⟨rfl, rfl, Nat.zero_lt_succ _, paid⟩⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native

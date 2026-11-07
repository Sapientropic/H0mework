import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Occurrence

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.PublicFunction
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program ComplementObservation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (code : SourceCode Party Good Port Technology Instrument)

structure AdmissionAt (event : Event code) (index : Slot code) where
  atBirth : event.ordinal = 0
  originalSlot : event.index = index
  originalInput : event.inputOverride = none
  birth : BirthWrite code

structure AssumptionAt (holder : Fin (ProgrammeSource.registrationSize code.input))
    (event : Event code) (index : Slot code) extends AdmissionAt code event index where
  ownSeat : holder = sourceSeat code

structure FulfilledAt (event : Event code) (content scope : Slot code) where
  content_eq : content = event.index
  scope_eq : scope = event.index
  actual : VisitReceipt code event
  paid : event.Paid code

structure RetainedAt (event : Event code) (content scope : Slot code) where
  content_eq : content = event.index
  scope_eq : scope = event.index
  actual : VisitReceipt code event
  unpaid : ¬ event.Paid code

/-- This is the native vocabulary of this newly created task, compiled
before its admission. The bearer is its original programme seat. -/
def vocabulary : ResponsibilityLifecycle.Vocabulary where
  SourceEvent := Event code
  Content := Slot code
  Residual := Bundle Good
  Bearer := Fin (ProgrammeSource.registrationSize code.input)
  ProtectedInterest := Party
  Scope := Slot code
  Lineage := Slot code
  Incidence := Slot code
  SourceObservation := canonicalComplementPair
  sourceAnchor := fun event => MinimalRegistrableSourceAnchor.canonical event.index event.index
  sourceIncidence := Event.index
  ObstructionAt := fun _ => Empty
  demandContent := fun impossible => nomatch impossible
  demandResidual := fun impossible => nomatch impossible
  CommitmentAt := fun _ _ => Empty
  MandateOriginAt := fun _ _ => Empty
  AcceptedTaskAt := AdmissionAt code
  ActiveDependencyAt := fun _ _ => Empty
  ProtectedRiskAt := fun _ _ => Empty
  AdmissionAuthorityAt := AdmissionAt code
  AcceptedAt := AssumptionAt code
  StandingMandateAt := fun _ _ _ => Empty
  DischargeJurisdiction := fun content scope => PLift (content = scope)
  ProgressAt := fun _ _ _ _ => Empty
  MaintenanceAt := RetainedAt code
  TypedDeferAt := fun _ _ _ => Empty
  ScopeNarrowingAt := fun _ _ _ => Empty
  TransferAcceptedAt := fun _ _ _ _ => Empty
  FulfilledAt := FulfilledAt code
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

abbrev V := vocabulary code

def admissionPayload (index : Slot code) : NativeAdmissionPayload (V code) where
  sourceEvent := ⟨index, 0, none⟩
  content := index
  residual := (serviceSlot code index).goods
  bearer := sourceSeat code
  beneficiary := (serviceSlot code index).bearer
  scope := index
  lineage := index
  anchor_scope_eq := rfl
  anchor_lineage_eq := rfl
  origin := .acceptedTask ⟨rfl, rfl, rfl, originalBirthWrite code⟩
  authority := ⟨rfl, rfl, rfl, originalBirthWrite code⟩
  assumption := .accepted ⟨⟨rfl, rfl, rfl, originalBirthWrite code⟩, rfl⟩
  dischargeJurisdiction := ⟨rfl⟩

def obligation (index : Slot code) := (admissionPayload code index).toObligation

structure Review (obligation : AdmittedObligation (V code)) where
  index : Slot code
  depth : Nat
  content_eq : obligation.content = index
  scope_eq : obligation.scope = index
  admission_index : obligation.admission.sourceEvent.index = index
  inputOverride : Option (SourceInput (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) := none

def reviewSource {obligation : AdmittedObligation (V code)} (event : Review code obligation) : Event code :=
  ⟨event.index, event.depth + 1, event.inputOverride⟩

def disposition {obligation : AdmittedObligation (V code)} (event : Review code obligation) :
    BoundaryDisposition (V code) obligation (reviewSource code event) :=
  if paid : (reviewSource code event).Paid code then
    .terminal (.final (.fulfilled ⟨event.content_eq, event.scope_eq,
      inputReceipt code event.index event.depth event.inputOverride, paid⟩))
  else .carry (.maintained ⟨event.content_eq, event.scope_eq,
    inputReceipt code event.index event.depth event.inputOverride, paid⟩)

def process : NativeResponsibilityProcess (V code) where
  AdmissionEvent := Slot code
  admissionPayload := admissionPayload code
  BoundaryEvent := Review code
  boundarySource := reviewSource code
  boundary_anchor_eq := by
    intro obligation event
    change MinimalRegistrableSourceAnchor.canonical event.index event.index =
      MinimalRegistrableSourceAnchor.canonical obligation.admission.sourceEvent.index obligation.admission.sourceEvent.index
    rw [event.admission_index]
  boundary_incidence_eq := by intro obligation event; exact event.admission_index.symm
  boundaryDisposition := disposition code
  ReopenEvent := fun _ => Empty
  reopenPayload := fun impossible => nomatch impossible

def admitted (index : Slot code) : (process code).GeneratedState :=
  (NativeResponsibilityProcess.GeneratedState.initial (process code)).step (process code) (.admit index)

theorem admitted_slot_is_the_original_task_claim (index : Slot code) :
    (admitted code index).current.slots = [.live (obligation code index)] ∧
      (obligation code index).content = index ∧
      (obligation code index).residual = (serviceSlot code index).goods ∧
      (obligation code index).bearer = sourceSeat code := ⟨rfl, rfl, rfl, rfl⟩

theorem native_admission_and_raw_task_share_the_same_source_birth (index : Slot code) :
    (admissionPayload code index).beneficiary = ((generateBirth code).task.slots.get index).bearer ∧
      (admissionPayload code index).residual = ((generateBirth code).task.slots.get index).goods ∧
      (admitted code index).current.history = (admitted code index).generated.events :=
  ⟨rfl, rfl, (admitted code index).history_eq⟩

#print axioms admissionPayload
#print axioms admitted
#print axioms native_admission_and_raw_task_share_the_same_source_birth

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native

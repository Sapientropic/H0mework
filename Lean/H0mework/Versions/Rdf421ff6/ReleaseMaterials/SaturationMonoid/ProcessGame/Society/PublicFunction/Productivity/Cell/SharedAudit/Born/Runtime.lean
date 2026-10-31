import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Born.Effects

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Born.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Institutions.Capitalism.Universal.Root

structure AtVisit (birth : Birth) (kind : Kind) (ordinal : Nat) where
  arrived : birth.ordinal ≤ ordinal
  birth_item : birth.item ∈ itemsAt birth.ordinal
  admission : Native.Prefix birth kind 0
  admission_generated : admission = Native.initial birth kind
  initially_live : admission.state.LiveAt 0
  service : Native.Prefix birth kind (ordinal + 1 - birth.ordinal)
  generated : service = Native.historyAt birth kind (ordinal + 1 - birth.ordinal)
  exact_history : service.state.history = service.run.events
  old_services : (slot : source.Slot) → OutstandingSource.NativeService.Prefix source slot ordinal
  finance : Financial.BalanceConservation.ledgerClaims source.input (financialAccount (ordinal + 1)).current =
    (source.currentAt (ordinal + 1)).claims
  row : ProgrammeLedger.transferReceiptOf source.input (source.taskWrite (ordinal - 1)).2 =
    some (source.writtenReceipt (ordinal - 1))
  next : (source.actualExecution (ordinal - 1)).after = source.currentAt (ordinal + 1)

def atVisit (birth : Birth) (kind : Kind) (ordinal : Nat) (arrived : birth.ordinal ≤ ordinal) :
    AtVisit birth kind ordinal where
  arrived := arrived
  birth_item := birth.original
  admission := Native.initial birth kind
  admission_generated := rfl
  initially_live := by exact ⟨Native.obligation birth kind, rfl⟩
  service := Native.historyAt birth kind (ordinal + 1 - birth.ordinal)
  generated := rfl
  exact_history := Native.exact_native_history _ _ _
  old_services := fun slot => OutstandingSource.NativeService.historyAt source slot ordinal
  finance := native_financial_matrix (ordinal + 1)
  row := source.receipt_is_in_original_task_write (ordinal - 1)
  next := by
    have positive := birth.running
    have same : ordinal - 1 + 2 = ordinal + 1 := by omega
    exact (source.actualExecution (ordinal - 1)).root_next_exact.trans (congrArg source.currentAt same)

structure Certificate where
  baseline : SharedAudit.Runtime.Certificate
  baseline_generated : baseline = SharedAudit.Runtime.certificate
  births : List Birth
  births_generated : births = Born.births 11
  keys : (births.map birthKey).Nodup
  cells : (index : Fin 4) → ProductionData (born index) (firstVisit index)
  cells_generated : cells = firstProduction
  services : (index : Fin 4) → (kind : Kind) → Native.Prefix (born index) kind (11 - (born index).ordinal)
  services_generated : services = allNewbornServices
  terminal : ∀ index kind, (services index kind).state.TerminalAt 0
  initially_live : ∀ index kind, (Native.initial (born index) kind).state.LiveAt 0
  first_payment : ∀ index kind,
    ∃ (offset : Nat) (paid : Paid (born index) kind ((born index).ordinal + offset)),
      (born index).ordinal + offset = firstVisit index ∧
      (services index kind).state.slots = [.terminal (Native.paidArchive (born index) kind offset paid)]
  future_archive : ∀ index kind later,
    (Native.historyAt (born index) kind (11 - (born index).ordinal + later)).state = (services index kind).state
  row : ProgrammeLedger.transferReceiptOf source.input (source.taskWrite 9).2 = some (source.writtenReceipt 9)
  next : (source.actualExecution 9).after = source.currentAt 11

def certificate : Certificate where
  baseline := SharedAudit.Runtime.certificate
  baseline_generated := rfl
  births := Born.births 11
  births_generated := rfl
  keys := actual_birth_keys_are_distinct
  cells := firstProduction
  cells_generated := rfl
  services := allNewbornServices
  services_generated := rfl
  terminal := actual_newborn_service_is_terminal
  initially_live := newborn_obligation_is_initially_live
  first_payment := actual_archive_is_from_the_first_service
  future_archive := every_finite_successor_keeps_the_first_newborn_archive
  row := source.receipt_is_in_original_task_write 9
  next := (source.actualExecution 9).root_next_exact

abbrev previousRoot := SharedAudit.Runtime.root
abbrev previousFacade := SharedAudit.Runtime.facade

inductive Projection where
  | newborn (birth : Birth) (kind : Kind)
  | family

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource source.input).restructuringSource.toLedgerSource where
  Projection := Projection
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun projection {current} _ _ => match projection with
    | .newborn birth kind => (ordinal : Nat) → birth.ordinal ≤ ordinal →
        current = (ProgrammeHistory.visitAt source.input ordinal).current → AtVisit birth kind ordinal
    | .family => current = (ProgrammeHistory.visitAt source.input 10).current → Certificate
  project := fun projection {_} _ _ => match projection with
    | .newborn birth kind => fun ordinal arrived _canonical => atVisit birth kind ordinal arrived
    | .family => fun _canonical => certificate

def root := previousRoot.withProjectionCoface projectionLaw

theorem original_root_is_preserved : root.toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot source.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N source.input) :=
  ⟨ProgrammeSource.V source.input, root, ProgrammeHistory.temporalVisit source.input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N source.input) where
  State := Nat
  stateAt := stateAt
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N source.input) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt source.input first).current =
        (ProgrammeHistory.visitAt source.input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective source.input currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face (ordinal : Nat) where
  | previous (face : SharedAudit.Runtime.Face)
  | newborn (index : Fin (births (ordinal + 1)).length) (kind : Kind)
  | family

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N source.input) where
  process := process
  FaceAt := fun state => Face state.state
  componentAt := fun _ face => match face with
    | .previous previous => previousFacade.componentAt previousFacade.seed previous
    | .newborn _ _ | .family => projectionLaw
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
      exact (previousFacade.installationAt previousFacade.seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface previousRoot.toAuthoritativeRoot.source projectionLaw)
    | newborn index kind => exact SourceNativeProjectionLaw.InstallationAt.componentCoface previousRoot.toAuthoritativeRoot.source projectionLaw
    | family => exact SourceNativeProjectionLaw.InstallationAt.componentCoface previousRoot.toAuthoritativeRoot.source projectionLaw
  projectionAt := fun state face => match face with
    | .previous previous => previousFacade.projectionAt previousFacade.seed previous
    | .newborn index kind => .newborn (discovered state.state index) kind
    | .family => .family

def activated (ordinal : Nat) : LivingRuntimeState process := facade.seed.advance ordinal

theorem activated_state (ordinal : Nat) : (activated ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => exact congrArg Nat.succ ih

theorem actual_family_payload : projectionLaw.project .family
    (ProgrammeSource.emitted source.input (ProgrammeHistory.visitAt source.input 10).current) () rfl = certificate := rfl

theorem actual_newborn_payload (birth : Birth) (kind : Kind) (ordinal : Nat)
    (arrived : birth.ordinal ≤ ordinal) :
    projectionLaw.project (.newborn birth kind)
      (ProgrammeSource.emitted source.input (ProgrammeHistory.visitAt source.input ordinal).current) () ordinal arrived rfl =
        atVisit birth kind ordinal arrived := rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Born.Runtime

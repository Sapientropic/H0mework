import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.History.NativeHistory
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.History
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.NativeRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.History.Runtime

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  (bound : BoundSource base scope)
  (inputs : List (RawEvent Party Good Port (State Party Technology) Instrument))

abbrev H := OutstandingSource.History.input bound.source inputs
abbrev currentAt (visit : Nat) := OutstandingSource.History.currentAt bound.source inputs (visit + 1)
abbrev wordAt (visit : Nat) := (OutstandingSource.History.actualExecution bound.source inputs visit).submitted

abbrev SlotDisposition (depth : Nat) (index : bound.source.Slot) :=
  OutstandingSource.History.NativeService.Prefix bound.source inputs index (depth + 1)

def slotDisposition (depth : Nat) (index : bound.source.Slot) : SlotDisposition bound inputs depth index :=
  OutstandingSource.History.NativeService.historyAt bound.source inputs index (depth + 1)

structure TracedGrant (birth last : Nat) where
  private mk ::
  admission : AdmittedGrant base scope (currentAt bound inputs birth) (wordAt bound inputs birth)
  continuation : Lifecycle.History base scope (currentAt bound inputs) (wordAt bound inputs) birth admission.grant
  exact : continuation = Lifecycle.through last

def traceGrant (birth last : Nat)
    (grant : Grant base scope (currentAt bound inputs birth) (wordAt bound inputs birth)) :
    TracedGrant bound inputs birth last :=
  ⟨admitGrant base scope _ _ grant, Lifecycle.through last, rfl⟩

def recordsAt (last : Nat) : List (Sigma fun birth : Fin (last + 1) => TracedGrant bound inputs birth.val last) :=
  (List.finRange (last + 1)).flatMap fun birth =>
    (grantsAt base scope (currentAt bound inputs birth.val) (wordAt bound inputs birth.val)).map fun grant =>
      ⟨birth, traceGrant bound inputs birth.val last grant⟩

structure Disposition (depth : Nat) where
  private mk ::
  slots : (index : bound.source.Slot) → SlotDisposition bound inputs depth index
  mandates : List (Sigma fun birth : Fin (depth + 1) => TracedGrant bound inputs birth.val depth)
  mandates_exact : mandates = recordsAt bound inputs depth

def generate (depth : Nat) : Disposition bound inputs depth :=
  ⟨slotDisposition bound inputs depth, recordsAt bound inputs depth, rfl⟩

theorem every_original_service_slot_is_natively_disposed (depth : Nat) (index : bound.source.Slot) :
    ((generate bound inputs depth).slots index).state.LiveAt 0 ↔
      (OutstandingSource.History.trailAt bound.source inputs (depth + 2)).frame.payments index = none :=
  OutstandingSource.History.NativeService.native_live_iff_unpaid bound.source inputs index (depth + 1)

theorem service_completion_is_exact_native_settlement (depth : Nat) :
    bound.source.pendingSlots (OutstandingSource.History.trailAt bound.source inputs (depth + 2)).frame.payments = [] ↔
      ∀ index, ((generate bound inputs depth).slots index).state.TerminalAt 0 :=
  OutstandingSource.History.NativeService.task_complete_iff_all_native_terminal bound.source inputs (depth + 1)

theorem every_original_grant_is_retained (last : Nat) (birth : Fin (last + 1))
    (grant : Grant base scope (currentAt bound inputs birth.val) (wordAt bound inputs birth.val))
    (actual : grant ∈ grantsAt base scope (currentAt bound inputs birth.val) (wordAt bound inputs birth.val)) :
    (⟨birth, traceGrant bound inputs birth.val last grant⟩ :
      Sigma fun birth : Fin (last + 1) => TracedGrant bound inputs birth.val last) ∈ (generate bound inputs last).mandates := by
  apply List.mem_flatMap.mpr
  exact ⟨birth, List.mem_finRange _, List.mem_map.mpr ⟨grant, actual, rfl⟩⟩

theorem own_native_mandate_keeps_its_admission (last : Nat)
    (record : Sigma fun birth : Fin (last + 1) => TracedGrant bound inputs birth.val last) :
    record.2.continuation.state.LiveAt 0 ∧
    HEq record.2.continuation.obligation.admission
      (Lifecycle.original base scope (currentAt bound inputs) (wordAt bound inputs)
        record.1.val record.2.admission.grant).admission :=
  ⟨record.2.continuation.responsibility_remains_live, record.2.continuation.original_admission⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (H bound inputs)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (depth : Nat) →
    current = (ProgrammeHistory.visitAt (H bound inputs) (depth + 1)).current → Disposition bound inputs depth
  project := fun _ {_} _ _ depth _own => generate bound inputs depth

def root := (ProgrammeLiving.livingRoot (H bound inputs)).withProjectionCoface (projectionLaw bound inputs)

theorem root_is_its_own_emitting_source : (root bound inputs).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot (H bound inputs)).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (H bound inputs)) :=
  ⟨ProgrammeSource.V (H bound inputs), root bound inputs, ProgrammeHistory.temporalVisit (H bound inputs) ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (H bound inputs)) where
  State := Nat
  stateAt := stateAt bound inputs
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (H bound inputs)) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (H bound inputs) first).current =
        (ProgrammeHistory.visitAt (H bound inputs) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (H bound inputs) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : ProgrammeLiving.Projection)
  | responsibilities

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (H bound inputs)) where
  process := process bound inputs
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous _ => ProgrammeLiving.projectionLaw (H bound inputs)
    | .responsibilities => projectionLaw bound inputs
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (ProgrammeLiving.livingRoot (H bound inputs)).toAuthoritativeRoot.source (projectionLaw bound inputs)
    | responsibilities =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (ProgrammeLiving.livingRoot (H bound inputs)).toAuthoritativeRoot.source (projectionLaw bound inputs)
  projectionAt := fun _ face => match face with
    | .previous previous => previous
    | .responsibilities => ()

def activated (ordinal : Nat) : LivingRuntimeState (process bound inputs) :=
  (facade bound inputs).seed.advance ordinal

theorem activated_state (ordinal : Nat) : (activated bound inputs ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => exact congrArg Nat.succ ih

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.History.Runtime

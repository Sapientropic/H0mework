import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.RawCertificate
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.LedgerCertificate
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Readiness
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Institutions.Capitalism.Universal.Root

structure AtVisit (birth : Birth) (kind : Kind) (ordinal : Nat) where
  arrived : birth.ordinal ≤ ordinal
  birth_origin : birth.instructionOrigin.instruction? productionSource.input = some birth.item
  service : Newborn.Prefix birth kind (ordinal + 1 - birth.ordinal)
  generated : service = Newborn.historyAt birth kind (ordinal + 1 - birth.ordinal)
  history : service.state.history = service.run.events
  old_service : (slot : productionSource.Slot) → OutstandingSource.NativeService.Prefix productionSource slot ordinal
  finance : Financial.BalanceConservation.ledgerClaims productionSource.input (account true (ordinal + 1)).current =
    (productionSource.currentAt (ordinal + 1)).claims
  row : ProgrammeLedger.transferReceiptOf productionSource.input (productionSource.taskWrite (ordinal - 1)).2 =
    some (productionSource.writtenReceipt (ordinal - 1))
  next : (productionSource.actualExecution (ordinal - 1)).after = productionSource.currentAt (ordinal + 1)

def atVisit (birth : Birth) (kind : Kind) (ordinal : Nat) (arrived : birth.ordinal ≤ ordinal) :
    AtVisit birth kind ordinal where
  arrived := arrived
  birth_origin := birth.instruction_decodes_the_original_item
  service := Newborn.historyAt birth kind (ordinal + 1 - birth.ordinal)
  generated := rfl
  history := Newborn.exact_native_history _ _ _
  old_service := fun slot => OutstandingSource.NativeService.historyAt productionSource slot ordinal
  finance := Participation.financial_matrix true _
  row := productionSource.receipt_is_in_original_task_write _
  next := by
    have positive := birth.running
    have same : ordinal - 1 + 2 = ordinal + 1 := by omega
    exact (productionSource.actualExecution _).root_next_exact.trans (congrArg productionSource.currentAt same)

abbrev previousRoot := Participation.Runtime.root
abbrev previousFacade := Participation.Runtime.facade

inductive Projection where
  | raw | ledger | readiness
  | newborn (birth : Birth) (kind : Kind)

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource productionSource.input).restructuringSource.toLedgerSource where
  Projection := Projection
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun projection {current} _ _ => match projection with
    | .raw => current = (ProgrammeHistory.visitAt productionSource.input 24).current → Raw.Result
    | .ledger => current = (ProgrammeHistory.visitAt productionSource.input 24).current → Ledger.Result
    | .readiness => current = (ProgrammeHistory.visitAt productionSource.input 24).current → (index : Fin 2) → CopyReview index
    | .newborn birth kind => (ordinal : Nat) → birth.ordinal ≤ ordinal →
        current = (ProgrammeHistory.visitAt productionSource.input ordinal).current → AtVisit birth kind ordinal
  project := fun projection {_} _ _ => match projection with
    | .raw => fun _canonical => Raw.run
    | .ledger => fun _canonical => Ledger.run
    | .readiness => fun _canonical => copyReview
    | .newborn birth kind => fun ordinal arrived _canonical => atVisit birth kind ordinal arrived

def root := previousRoot.withProjectionCoface projectionLaw

theorem original_root_is_preserved : root.toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot productionSource.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N productionSource.input) :=
  ⟨ProgrammeSource.V productionSource.input, root, ProgrammeHistory.temporalVisit productionSource.input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N productionSource.input) where
  State := Nat
  stateAt := stateAt
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N productionSource.input) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt productionSource.input first).current =
        (ProgrammeHistory.visitAt productionSource.input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective productionSource.input currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face (ordinal : Nat) where
  | previous (face : Participation.Runtime.Face)
  | raw | ledger | readiness
  | newborn (index : Fin (births (ordinal + 1)).length) (kind : Kind)

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N productionSource.input) where
  process := process
  FaceAt := fun state => Face state.state
  componentAt := fun _ face => match face with
    | .previous previous => previousFacade.componentAt previousFacade.seed previous
    | .raw | .ledger | .readiness | .newborn _ _ => projectionLaw
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
      exact (previousFacade.installationAt previousFacade.seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface previousRoot.toAuthoritativeRoot.source projectionLaw)
    | raw => exact SourceNativeProjectionLaw.InstallationAt.componentCoface previousRoot.toAuthoritativeRoot.source projectionLaw
    | ledger => exact SourceNativeProjectionLaw.InstallationAt.componentCoface previousRoot.toAuthoritativeRoot.source projectionLaw
    | readiness => exact SourceNativeProjectionLaw.InstallationAt.componentCoface previousRoot.toAuthoritativeRoot.source projectionLaw
    | newborn _ _ => exact SourceNativeProjectionLaw.InstallationAt.componentCoface previousRoot.toAuthoritativeRoot.source projectionLaw
  projectionAt := fun state face => match face with
    | .previous previous => previousFacade.projectionAt previousFacade.seed previous
    | .raw => .raw
    | .ledger => .ledger
    | .readiness => .readiness
    | .newborn index kind => .newborn (discovered state.state index) kind

def activated (ordinal : Nat) : LivingRuntimeState process := facade.seed.advance ordinal

theorem activated_state (ordinal : Nat) : (activated ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => exact congrArg Nat.succ ih

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Runtime

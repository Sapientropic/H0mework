import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Effects
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Runtime

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeJointRuntime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Objection.Followup Objection.Opening

variable {fuel : ℚ} {old : Joint.Inventory fuel} (ready : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : ScopeRevision.Pending.Joint.Inventory ready originInputs)
noncomputable section

abbrev nextInventory := ScopeRevision.Pending.Joint.advance ready inventory
abbrev I := OutstandingSource.History.input (ScopeRevision.epochSource ready) (nextInventory ready inventory).inputs

structure Disposition where
  private mk ::
  oldJoint : JointRuntime.Disposition old (ScopeRevision.emit old)
  oldJoint_exact : oldJoint = JointRuntime.generate old (ScopeRevision.emit old)
  oldNative : Runtime.Disposition fuel (ScopeRevision.advance old).inputs old.cut.depth
  oldNative_exact : oldNative = ScopeRevision.legacy ready
  original_financial_state : (ScopeRevision.Pending.Joint.Finance.originalAccount ready).current =
    Financial.Family.Embedding.state ScopeRevision.Pending.Joint.Finance.sources
      (ScopeRevision.Pending.Joint.Finance.originalInput ready) oldNative.account.current
  initial_exact : (I ready inventory).initial = (ScopeRevision.advance old).cut.past.frame.raw
  next : ScopeRevision.Pending.Joint.Inventory ready originInputs
  next_exact : next = nextInventory ready inventory
  serviceRuns : (index : (ScopeRevision.epochSource ready).Slot) →
    (OutstandingSource.History.NativeService.threadProcess (ScopeRevision.epochSource ready) originInputs).Run
      (inventory.services index).state.current (next.services index).state.current
  financialInstructions : List (Financial.Family.InstructionRecord ScopeRevision.Pending.Joint.Finance.sources)
  financialInstructions_exact : financialInstructions = ScopeRevision.Pending.Joint.Finance.appendTrace ready
    inventory.inputs (ScopeRevision.Pending.Joint.emit ready inventory) inventory.finance
  financialRun : (Financial.Family.process ScopeRevision.Pending.Joint.Finance.sources).Run
    inventory.finance.current next.finance.current
  financialMigrations : ∀ index slot, inventory.finance.current.slots[index]? = some slot →
    Financial.Family.Migration.Follow ScopeRevision.Pending.Joint.Finance.sources financialRun index slot
  financial_matrix : Financial.Family.ledgerClaims ScopeRevision.Pending.Joint.Finance.sources next.finance.current =
    (ScopeRevision.Pending.current ready next.inputs).claims
  outcome : ScopeRevision.Pending.Joint.Outcome ready inventory
  outcome_exact : outcome = ScopeRevision.Pending.Joint.outcome ready inventory
  financial_support : ScopeRevision.Pending.SilentPast next.inputs →
    Financial.BalanceConservation.ledgerClaims (Objection.I fuel (ScopeRevision.advance old).inputs) oldNative.account.current =
      (ScopeRevision.Pending.current ready next.inputs).claims

def generate : Disposition ready inventory :=
  ⟨JointRuntime.generate old (ScopeRevision.emit old), rfl, ScopeRevision.legacy ready, rfl,
    ScopeRevision.Pending.Joint.Finance.original_full_state ready,
    ScopeRevision.the_new_source_initial_is_the_actual_old_successor ready,
    nextInventory ready inventory, rfl,
    ScopeRevision.Pending.Joint.every_original_service_has_actual_native_continuation ready inventory
      (ScopeRevision.Pending.Joint.emit ready inventory),
    ScopeRevision.Pending.Joint.Finance.appendTrace ready inventory.inputs (ScopeRevision.Pending.Joint.emit ready inventory)
      inventory.finance, rfl,
    ScopeRevision.Pending.Joint.every_original_financial_slot_has_actual_native_continuation ready inventory
      (ScopeRevision.Pending.Joint.emit ready inventory),
    fun index slot present => Financial.Family.Migration.follow _ _ index slot present,
    ScopeRevision.Pending.Joint.financial_matrix_at_every_actual_cut ready (nextInventory ready inventory),
    ScopeRevision.Pending.Joint.outcome ready inventory, rfl,
    ScopeRevision.Pending.Joint.original_native_finance_supports_the_complete_current_matrix ready (nextInventory ready inventory)⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (I ready inventory)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => current = (ProgrammeHistory.visitAt (I ready inventory) (inventory.inputs.length + 2)).current → Disposition ready inventory
  project := fun _ {_} _ _ _own => generate ready inventory

def root := (ProgrammeLiving.livingRoot (I ready inventory)).withProjectionCoface (projectionLaw ready inventory)

theorem root_is_its_own_emitting_source : (root ready inventory).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot (I ready inventory)).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I ready inventory)) :=
  ⟨ProgrammeSource.V (I ready inventory), root ready inventory, ProgrammeHistory.temporalVisit (I ready inventory) ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (I ready inventory)) where
  State := Nat
  stateAt := stateAt ready inventory
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I ready inventory)) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (I ready inventory) first).current =
        (ProgrammeHistory.visitAt (I ready inventory) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (I ready inventory) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : ProgrammeLiving.Projection)
  | responsibilities

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (I ready inventory)) where
  process := process ready inventory
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous _ => ProgrammeLiving.projectionLaw (I ready inventory)
    | .responsibilities => projectionLaw ready inventory
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (ProgrammeLiving.livingRoot (I ready inventory)).toAuthoritativeRoot.source (projectionLaw ready inventory)
    | responsibilities =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (ProgrammeLiving.livingRoot (I ready inventory)).toAuthoritativeRoot.source (projectionLaw ready inventory)
  projectionAt := fun _ face => match face with
    | .previous previous => previous
    | .responsibilities => ()

def activated (ordinal : Nat) : LivingRuntimeState (process ready inventory) :=
  (facade ready inventory).seed.advance ordinal

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeJointRuntime

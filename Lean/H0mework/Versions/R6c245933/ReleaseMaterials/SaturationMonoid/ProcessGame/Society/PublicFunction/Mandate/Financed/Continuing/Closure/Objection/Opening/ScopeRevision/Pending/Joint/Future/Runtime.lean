import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future.Native
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement.Runtime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Runtime

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future.Runtime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Followup
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (ready : Ready old)
  {originInputs : List (List Action)} (inventory : Inventory ready originInputs) (intent : Intent)
noncomputable section

abbrev I := Future.I ready inventory intent
abbrev nextInventory := Future.advance ready inventory intent

structure Disposition where
  private mk ::
  next : Inventory ready originInputs
  next_exact : next = nextInventory ready inventory intent
  initial_exact : (I ready inventory intent).initial = (ScopeRevision.advance old).cut.past.frame.raw
  actual_word : (Future.execution ready inventory intent).submitted = Future.emit ready inventory intent
  actual_before : (Future.execution ready inventory intent).before = current ready inventory.inputs
  plan : Outcome ready intent (current ready inventory.inputs)
  plan_exact : plan = outcome ready intent (current ready inventory.inputs)
  native : Future.Native ready inventory intent
  native_exact : native = Future.native ready inventory intent
  response : Settlement.Runtime.Disposition ready (staged ready inventory intent)
  response_exact : response = Settlement.Runtime.generate ready (staged ready inventory intent)
  following : Intent
  following_exact : following = nextIntent ready next
  financialInstructions : List (Financial.Family.InstructionRecord Finance.sources)
  financialInstructions_exact : financialInstructions =
    Finance.appendTrace ready inventory.inputs (Future.emit ready inventory intent) inventory.finance ++
      Finance.appendTrace ready (staged ready inventory intent).inputs
        (Settlement.emit ready (staged ready inventory intent)) (staged ready inventory intent).finance

def generate : Disposition ready inventory intent :=
  ⟨nextInventory ready inventory intent, rfl, the_new_source_initial_is_the_actual_old_successor ready,
    (Future.actual_word_and_cut ready inventory intent).1, (Future.actual_word_and_cut ready inventory intent).2,
    outcome ready intent (current ready inventory.inputs), rfl, Future.native ready inventory intent, rfl,
    Settlement.Runtime.generate ready (staged ready inventory intent), rfl,
    nextIntent ready (nextInventory ready inventory intent), rfl,
    Finance.appendTrace ready inventory.inputs (Future.emit ready inventory intent) inventory.finance ++
      Finance.appendTrace ready (staged ready inventory intent).inputs
        (Settlement.emit ready (staged ready inventory intent)) (staged ready inventory intent).finance, rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (I ready inventory intent)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => current = (ProgrammeHistory.visitAt (I ready inventory intent) ((staged ready inventory intent).inputs.length + 2)).current → Disposition ready inventory intent
  project := fun _ {_} _ _ _own => generate ready inventory intent

def root := (ProgrammeLiving.livingRoot (I ready inventory intent)).withProjectionCoface (projectionLaw ready inventory intent)

theorem root_is_its_own_emitting_source : (root ready inventory intent).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot (I ready inventory intent)).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I ready inventory intent)) :=
  ⟨ProgrammeSource.V (I ready inventory intent), root ready inventory intent, ProgrammeHistory.temporalVisit (I ready inventory intent) ordinal⟩

def stateAtFromFrame (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I ready inventory intent)) :=
  ⟨ProgrammeSource.V (I ready inventory intent), root ready inventory intent, .finite (OutstandingSource.History.foldedRootVisitAt (ScopeRevision.epochSource ready) ((Settlement.advance ready (Future.staged ready inventory intent)).inputs) ordinal)⟩

@[csimp] theorem stateAt_eq_frame : @stateAt = @stateAtFromFrame := by
  funext a0 a1 a2 a3 a4 a5 a6
  unfold stateAt stateAtFromFrame ProgrammeHistory.temporalVisit
  rw [OutstandingSource.History.foldedRootVisitAt_is_the_original_visit]
  rfl

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (I ready inventory intent)) where
  State := Nat
  stateAt := stateAt ready inventory intent
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I ready inventory intent)) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (I ready inventory intent) first).current =
        (ProgrammeHistory.visitAt (I ready inventory intent) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (I ready inventory intent) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : ProgrammeLiving.Projection)
  | responsibilities

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (I ready inventory intent)) where
  process := process ready inventory intent
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous _ => ProgrammeLiving.projectionLaw (I ready inventory intent)
    | .responsibilities => projectionLaw ready inventory intent
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (ProgrammeLiving.livingRoot (I ready inventory intent)).toAuthoritativeRoot.source (projectionLaw ready inventory intent)
    | responsibilities =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (ProgrammeLiving.livingRoot (I ready inventory intent)).toAuthoritativeRoot.source (projectionLaw ready inventory intent)
  projectionAt := fun _ face => match face with
    | .previous previous => previous
    | .responsibilities => ()

def activated (ordinal : Nat) : LivingRuntimeState (process ready inventory intent) :=
  (facade ready inventory intent).seed.advance ordinal

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future.Runtime

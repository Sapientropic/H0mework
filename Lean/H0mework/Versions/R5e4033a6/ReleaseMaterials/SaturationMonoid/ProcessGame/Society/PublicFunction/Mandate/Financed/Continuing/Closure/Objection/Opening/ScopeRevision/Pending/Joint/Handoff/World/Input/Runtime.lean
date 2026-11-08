import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge

/-! The actual input and repayment source owns its saved full inventory
and its native after-state. Subsequent epoch generation uses that after-state. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Runtime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch) (intent : Intent)

inductive Projection where
  | saved | completed

def savedOrdinal (_intent : Intent) := inventory.inputs.length + 1
def reviewOrdinal := (Input.staged inventory intent).inputs.length + 2

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (Input.I inventory intent)).restructuringSource.toLedgerSource where
  Projection := Projection
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun projection {current} _ _ => match projection with
    | .saved => current = (ProgrammeHistory.visitAt (Input.I inventory intent) (savedOrdinal inventory intent)).current → Inventory epoch
    | .completed => current = (ProgrammeHistory.visitAt (Input.I inventory intent) (reviewOrdinal inventory intent)).current → Disposition inventory intent
  project := fun projection {_} _ _ => by
    cases projection with
    | saved => exact fun _own => inventory
    | completed => exact fun _own => Input.produce inventory intent

def root := (ProgrammeLiving.livingRoot (Input.I inventory intent)).withProjectionCoface (projectionLaw inventory intent)

theorem root_is_its_own_source : (root inventory intent).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot (Input.I inventory intent)).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Input.I inventory intent)) :=
  ⟨ProgrammeSource.V (Input.I inventory intent),root inventory intent,ProgrammeHistory.temporalVisit (Input.I inventory intent) ordinal⟩

def stateAtFromFrame (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Input.I inventory intent)) :=
  ⟨ProgrammeSource.V (Input.I inventory intent),root inventory intent,.finite (OutstandingSource.History.foldedRootVisitAt (epoch.source) ((Input.advance inventory intent).inputs) ordinal)⟩

@[csimp] theorem stateAt_eq_frame : @stateAt = @stateAtFromFrame := by
  funext a0 a1 a2 a3
  unfold stateAt stateAtFromFrame ProgrammeHistory.temporalVisit
  rw [OutstandingSource.History.foldedRootVisitAt_is_the_original_visit]
  rfl

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (Input.I inventory intent)) where
  State := Nat
  stateAt := stateAt inventory intent
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Input.I inventory intent)) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (Input.I inventory intent) first).current =
        (ProgrammeHistory.visitAt (Input.I inventory intent) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (Input.I inventory intent) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : ProgrammeLiving.Projection)
  | joint (projection : Projection)

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (Input.I inventory intent)) where
  process := process inventory intent
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous _ => ProgrammeLiving.projectionLaw (Input.I inventory intent)
    | .joint _ => projectionLaw inventory intent
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (ProgrammeLiving.livingRoot (Input.I inventory intent)).toAuthoritativeRoot.source (projectionLaw inventory intent)
    | joint projection =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (ProgrammeLiving.livingRoot (Input.I inventory intent)).toAuthoritativeRoot.source (projectionLaw inventory intent)
  projectionAt := fun _ face => match face with
    | .previous previous => previous
    | .joint projection => projection

def activated (ordinal : Nat) : LivingRuntimeState (process inventory intent) := (facade inventory intent).seed.advance ordinal

def savedFromRoot : Inventory epoch :=
  (projectionLaw inventory intent).project .saved
    (ProgrammeSource.emitted (Input.I inventory intent) (ProgrammeHistory.visitAt (Input.I inventory intent) (savedOrdinal inventory intent)).current) () rfl

def resultFromRoot : Disposition inventory intent :=
  (projectionLaw inventory intent).project .completed
    (ProgrammeSource.emitted (Input.I inventory intent) (ProgrammeHistory.visitAt (Input.I inventory intent) (reviewOrdinal inventory intent)).current) () rfl

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Runtime

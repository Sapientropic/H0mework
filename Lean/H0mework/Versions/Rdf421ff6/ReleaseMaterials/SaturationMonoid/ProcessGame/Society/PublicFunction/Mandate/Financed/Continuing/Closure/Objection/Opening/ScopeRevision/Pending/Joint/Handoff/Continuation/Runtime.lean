import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Continuation.Effects
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.EpochRuntime

/-! The joint continuation is installed on the actual source that emitted
both its authority/service word and its debt response. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Continuation.Runtime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Followup
noncomputable section
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} {authority : ScopeRevision.Ready old}
  {originInputs : List (List Action)} {inventory : Pending.Joint.Inventory authority originInputs}
  {fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs}

def fromEpoch (authority : ScopeRevision.Ready old) (inventory : Pending.Joint.Inventory authority originInputs)
    (fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs) :=
  Continuation.initial authority inventory fresh ((EpochRuntime.projectionLaw authority inventory fresh).project ()
    (ProgrammeSource.emitted (Handoff.I fresh) (ProgrammeHistory.visitAt (Handoff.I fresh) 3).current) () rfl)

variable (saved : Inventory authority inventory fresh)
def responseOrdinal := (staged saved).inputs.length + 2

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (Continuation.I saved)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (Continuation.I saved) (responseOrdinal saved)).current → Inventory authority inventory fresh
  project := fun _ {_} _ _ _own => advance saved

def root := (ProgrammeLiving.livingRoot (Continuation.I saved)).withProjectionCoface (projectionLaw saved)

theorem root_is_its_own_emitting_source : (root saved).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot (Continuation.I saved)).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Continuation.I saved)) :=
  ⟨ProgrammeSource.V (Continuation.I saved),root saved,ProgrammeHistory.temporalVisit (Continuation.I saved) ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (Continuation.I saved)) where
  State := Nat
  stateAt := stateAt saved
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Continuation.I saved)) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (Continuation.I saved) first).current =
        (ProgrammeHistory.visitAt (Continuation.I saved) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (Continuation.I saved) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : ProgrammeLiving.Projection)
  | jointContinuation

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (Continuation.I saved)) where
  process := process saved
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous _ => ProgrammeLiving.projectionLaw (Continuation.I saved)
    | .jointContinuation => projectionLaw saved
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (ProgrammeLiving.livingRoot (Continuation.I saved)).toAuthoritativeRoot.source (projectionLaw saved)
    | jointContinuation =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (ProgrammeLiving.livingRoot (Continuation.I saved)).toAuthoritativeRoot.source (projectionLaw saved)
  projectionAt := fun _ face => match face with
    | .previous previous => previous
    | .jointContinuation => ()

def activated (ordinal : Nat) : LivingRuntimeState (process saved) := (facade saved).seed.advance ordinal

def fromActualRoot : Inventory authority inventory fresh :=
  (projectionLaw saved).project ()
    (ProgrammeSource.emitted (Continuation.I saved) (ProgrammeHistory.visitAt (Continuation.I saved) (responseOrdinal saved)).current) () rfl

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Continuation.Runtime

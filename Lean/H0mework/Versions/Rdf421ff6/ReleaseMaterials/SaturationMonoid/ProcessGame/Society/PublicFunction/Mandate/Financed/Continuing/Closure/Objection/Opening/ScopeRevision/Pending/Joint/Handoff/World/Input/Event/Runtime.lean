import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event

/-! The actual response root consumes the incoming event, native evolution,
full original responsibilities and its own literal next. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Runtime
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch) (word : List Action)

def ordinal := Replacement.Runtime.ordinal (observed inventory word)
def baseRoot := Replacement.Runtime.root (observed inventory word)

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (Programme.Completion.I (observed inventory word))).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (Programme.Completion.I (observed inventory word)) (ordinal inventory word)).current → Disposition inventory word
  project := fun _ {_} _ _ _own => Event.produce inventory word

def root := (baseRoot inventory word).withProjectionCoface (projectionLaw inventory word)

theorem root_is_the_original_response_root :
    (root inventory word).toAuthoritativeRoot.toRoot = (baseRoot inventory word).toAuthoritativeRoot.toRoot := rfl

def stateAt (index : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Programme.Completion.I (observed inventory word))) :=
  ⟨ProgrammeSource.V (Programme.Completion.I (observed inventory word)),root inventory word,
    ProgrammeHistory.temporalVisit (Programme.Completion.I (observed inventory word)) index⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (Programme.Completion.I (observed inventory word))) where
  State := Nat
  stateAt := stateAt inventory word
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Programme.Completion.I (observed inventory word))) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (Programme.Completion.I (observed inventory word)) first).current =
        (ProgrammeHistory.visitAt (Programme.Completion.I (observed inventory word)) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (Programme.Completion.I (observed inventory word)) currents
  initial := 0
  successorAt := fun index => ⟨index+1,rfl,HEq.rfl⟩

abbrev Face := Sum Replacement.Runtime.Face Unit

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (Programme.Completion.I (observed inventory word))) where
  process := process inventory word
  FaceAt := fun _ => Face
  componentAt := fun _state face => match face with
    | .inl previous => (Replacement.Runtime.facade (observed inventory word)).componentAt (Replacement.Runtime.activated (observed inventory word) 0) previous
    | .inr _ => projectionLaw inventory word
  installationAt := by
    intro state face
    have inherited := SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      (baseRoot inventory word).toAuthoritativeRoot.source (projectionLaw inventory word)
    cases face with
    | inl previous => exact ((Replacement.Runtime.facade (observed inventory word)).installationAt (Replacement.Runtime.activated (observed inventory word) 0) previous).trans inherited
    | inr own =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (baseRoot inventory word).toAuthoritativeRoot.source (projectionLaw inventory word)
  projectionAt := fun _state face => match face with
    | .inl previous => (Replacement.Runtime.facade (observed inventory word)).projectionAt (Replacement.Runtime.activated (observed inventory word) 0) previous
    | .inr _ => ()

def activated (index : Nat) : LivingRuntimeState (process inventory word) := (facade inventory word).seed.advance index

def fromRoot : Disposition inventory word :=
  (projectionLaw inventory word).project ()
    (ProgrammeSource.emitted (Programme.Completion.I (observed inventory word))
      (ProgrammeHistory.visitAt (Programme.Completion.I (observed inventory word)) (ordinal inventory word)).current) () rfl

theorem consumes_the_actual_incoming_event_and_response :
    fromRoot inventory word = Event.produce inventory word := rfl

theorem raw_generated_next_is_the_original_complete_after :
    ProgrammeSource.rawCurrent (Programme.Completion.I (observed inventory word))
      (ProgrammeHistory.visitAt (Programme.Completion.I (observed inventory word)) (ordinal inventory word+1)).current =
      current epoch (Programme.produce (observed inventory word)).finalInventory.inputs :=
  Replacement.Runtime.raw_generated_next_is_the_original_complete_after (observed inventory word)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Runtime

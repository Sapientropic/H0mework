import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Replacement

/-! The last actual input root consumes the replacement material verdict
alongside its original completion; every face has the same literal next. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Replacement.Runtime
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

def ordinal := Programme.Completion.Runtime.ordinal inventory
def baseRoot := Programme.Completion.Runtime.root inventory

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (Programme.Completion.I inventory)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (Programme.Completion.I inventory) (ordinal inventory)).current → Disposition inventory
  project := fun _ {_} _ _ _own => Replacement.produce inventory

def root := (baseRoot inventory).withProjectionCoface (projectionLaw inventory)

theorem root_is_the_original_direct_completion_root :
    (root inventory).toAuthoritativeRoot.toRoot = (baseRoot inventory).toAuthoritativeRoot.toRoot := rfl

def stateAt (index : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Programme.Completion.I inventory)) :=
  ⟨ProgrammeSource.V (Programme.Completion.I inventory),root inventory,
    ProgrammeHistory.temporalVisit (Programme.Completion.I inventory) index⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (Programme.Completion.I inventory)) where
  State := Nat
  stateAt := stateAt inventory
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Programme.Completion.I inventory)) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (Programme.Completion.I inventory) first).current =
        (ProgrammeHistory.visitAt (Programme.Completion.I inventory) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (Programme.Completion.I inventory) currents
  initial := 0
  successorAt := fun index => ⟨index+1,rfl,HEq.rfl⟩

abbrev Face := Sum Programme.Completion.Runtime.Face Unit

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (Programme.Completion.I inventory)) where
  process := process inventory
  FaceAt := fun _ => Face
  componentAt := fun _state face => match face with
    | .inl previous => (Programme.Completion.Runtime.facade inventory).componentAt (Programme.Completion.Runtime.activated inventory 0) previous
    | .inr _ => projectionLaw inventory
  installationAt := by
    intro state face
    have inherited := SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      (baseRoot inventory).toAuthoritativeRoot.source (projectionLaw inventory)
    cases face with
    | inl previous => exact ((Programme.Completion.Runtime.facade inventory).installationAt (Programme.Completion.Runtime.activated inventory 0) previous).trans inherited
    | inr own =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (baseRoot inventory).toAuthoritativeRoot.source (projectionLaw inventory)
  projectionAt := fun _state face => match face with
    | .inl previous => (Programme.Completion.Runtime.facade inventory).projectionAt (Programme.Completion.Runtime.activated inventory 0) previous
    | .inr _ => ()

def activated (index : Nat) : LivingRuntimeState (process inventory) := (facade inventory).seed.advance index

def fromRoot : Disposition inventory :=
  (projectionLaw inventory).project ()
    (ProgrammeSource.emitted (Programme.Completion.I inventory)
      (ProgrammeHistory.visitAt (Programme.Completion.I inventory) (ordinal inventory)).current) () rfl

theorem consumes_the_actual_completion_and_its_source_material_verdict :
    (fromRoot inventory).original = Programme.Completion.Runtime.fromRoot inventory ∧
    (fromRoot inventory).replacement = Replacement.generate inventory := ⟨rfl,rfl⟩

theorem the_packet_includes_the_actual_service_and_debt_response :
    (fromRoot inventory).packet =
      (World.generate (Programme.produce inventory).finalInventory).packet _ :=
  (fromRoot inventory).original.decision.packet_is_the_actual_direct_handoff

theorem raw_generated_next_is_the_original_complete_after :
    ProgrammeSource.rawCurrent (Programme.Completion.I inventory)
      (ProgrammeHistory.visitAt (Programme.Completion.I inventory) (ordinal inventory+1)).current =
      current epoch (Programme.produce inventory).finalInventory.inputs :=
  Programme.Completion.Runtime.raw_generated_next_is_the_complete_programme_after inventory

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Replacement.Runtime

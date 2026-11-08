import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Programme

/-! This is a coface of the existing root of the final actual history.
Every generated trial is a prefix of that root's own emitted input. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Programme.Runtime
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

def ordinal := World.Runtime.reviewOrdinal (Programme.finalInventory inventory)
def baseRoot := World.Runtime.root (Programme.finalInventory inventory)

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (Programme.I inventory)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => current = (ProgrammeHistory.visitAt (Programme.I inventory) (ordinal inventory)).current → Execution inventory
  project := fun _ {_} _ _ _own => Programme.produce inventory

def root := (baseRoot inventory).withProjectionCoface (projectionLaw inventory)

theorem root_is_the_existing_root_of_its_actual_final_history :
    (root inventory).toAuthoritativeRoot.toRoot = (baseRoot inventory).toAuthoritativeRoot.toRoot := rfl

def stateAt (index : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Programme.I inventory)) :=
  ⟨ProgrammeSource.V (Programme.I inventory),root inventory,ProgrammeHistory.temporalVisit (Programme.I inventory) index⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (Programme.I inventory)) where
  State := Nat
  stateAt := stateAt inventory
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Programme.I inventory)) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (Programme.I inventory) first).current =
        (ProgrammeHistory.visitAt (Programme.I inventory) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (Programme.I inventory) currents
  initial := 0
  successorAt := fun index => ⟨index+1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : ProgrammeLiving.Projection)
  | joint (face : World.Runtime.Projection)
  | programme

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (Programme.I inventory)) where
  process := process inventory
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous _ => ProgrammeLiving.projectionLaw (Programme.I inventory)
    | .joint _ => World.Runtime.projectionLaw (Programme.finalInventory inventory)
    | .programme => projectionLaw inventory
  installationAt := by
    intro state face
    have inherited := SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      (baseRoot inventory).toAuthoritativeRoot.source (projectionLaw inventory)
    cases face with
    | previous previous =>
        exact (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (ProgrammeLiving.livingRoot (Programme.I inventory)).toAuthoritativeRoot.source
          (World.Runtime.projectionLaw (Programme.finalInventory inventory))).trans inherited
    | joint joint =>
        exact (SourceNativeProjectionLaw.InstallationAt.componentCoface
          (ProgrammeLiving.livingRoot (Programme.I inventory)).toAuthoritativeRoot.source
          (World.Runtime.projectionLaw (Programme.finalInventory inventory))).trans inherited
    | programme =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (baseRoot inventory).toAuthoritativeRoot.source (projectionLaw inventory)
  projectionAt := fun _ face => match face with
    | .previous previous => previous
    | .joint joint => joint
    | .programme => ()

def activated (index : Nat) : LivingRuntimeState (process inventory) := (facade inventory).seed.advance index

def fromRoot : Execution inventory :=
  (projectionLaw inventory).project ()
    (ProgrammeSource.emitted (Programme.I inventory) (ProgrammeHistory.visitAt (Programme.I inventory) (ordinal inventory)).current) () rfl

theorem consumes_the_generated_execution : fromRoot inventory = Programme.produce inventory := rfl

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Programme.Runtime

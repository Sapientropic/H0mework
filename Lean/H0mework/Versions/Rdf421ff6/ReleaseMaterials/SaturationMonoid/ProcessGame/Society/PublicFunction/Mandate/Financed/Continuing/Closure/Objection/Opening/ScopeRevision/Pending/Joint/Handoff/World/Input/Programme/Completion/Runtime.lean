import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Programme.Completion

/-! A coface of the last Input root jointly consumes phase effects and
the source-generated direct closure, with its own native next. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Programme.Completion.Runtime
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

def attempt := lastAttempt (Programme.produce inventory)
def ordinal := Input.Runtime.reviewOrdinal (attempt inventory).1 (attempt inventory).2
def baseRoot := Input.Runtime.root (attempt inventory).1 (attempt inventory).2

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (Completion.I inventory)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (Completion.I inventory) (ordinal inventory)).current → Disposition inventory
  project := fun _ {_} _ _ _own => Completion.produce inventory

def root := (baseRoot inventory).withProjectionCoface (projectionLaw inventory)

theorem root_is_the_original_last_input_root :
    (root inventory).toAuthoritativeRoot.toRoot = (baseRoot inventory).toAuthoritativeRoot.toRoot := rfl

def stateAt (index : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Completion.I inventory)) :=
  ⟨ProgrammeSource.V (Completion.I inventory),root inventory,ProgrammeHistory.temporalVisit (Completion.I inventory) index⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (Completion.I inventory)) where
  State := Nat
  stateAt := stateAt inventory
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Completion.I inventory)) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (Completion.I inventory) first).current =
        (ProgrammeHistory.visitAt (Completion.I inventory) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (Completion.I inventory) currents
  initial := 0
  successorAt := fun index => ⟨index+1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : ProgrammeLiving.Projection)
  | input (face : Input.Runtime.Projection)
  | completion

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (Completion.I inventory)) where
  process := process inventory
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous _ => ProgrammeLiving.projectionLaw (Completion.I inventory)
    | .input _ => Input.Runtime.projectionLaw (attempt inventory).1 (attempt inventory).2
    | .completion => projectionLaw inventory
  installationAt := by
    intro state face
    have inherited := SourceNativeProjectionLaw.InstallationAt.inheritedCoface
      (baseRoot inventory).toAuthoritativeRoot.source (projectionLaw inventory)
    cases face with
    | previous previous =>
      exact (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
        (ProgrammeLiving.livingRoot (Completion.I inventory)).toAuthoritativeRoot.source
        (Input.Runtime.projectionLaw (attempt inventory).1 (attempt inventory).2)).trans inherited
    | input input =>
      exact (SourceNativeProjectionLaw.InstallationAt.componentCoface
        (ProgrammeLiving.livingRoot (Completion.I inventory)).toAuthoritativeRoot.source
        (Input.Runtime.projectionLaw (attempt inventory).1 (attempt inventory).2)).trans inherited
    | completion =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (baseRoot inventory).toAuthoritativeRoot.source (projectionLaw inventory)
  projectionAt := fun _ face => match face with
    | .previous previous => previous
    | .input input => input
    | .completion => ()

def activated (index : Nat) : LivingRuntimeState (process inventory) := (facade inventory).seed.advance index

def fromRoot : Disposition inventory :=
  (projectionLaw inventory).project ()
    (ProgrammeSource.emitted (Completion.I inventory) (ProgrammeHistory.visitAt (Completion.I inventory) (ordinal inventory)).current) () rfl

theorem consumes_the_actual_direct_handoff : (fromRoot inventory).decision = Completion.generate (Programme.produce inventory) := rfl

theorem raw_generated_next_is_the_complete_programme_after :
    ProgrammeSource.rawCurrent (Completion.I inventory)
      (ProgrammeHistory.visitAt (Completion.I inventory) (ordinal inventory + 1)).current =
      current epoch (Programme.produce inventory).finalInventory.inputs := by
  rw [← last_attempt_has_the_complete_final_inventory (Programme.produce inventory)]
  change OutstandingSource.History.currentAt epoch.source
    (Input.advance (attempt inventory).1 (attempt inventory).2).inputs
      (Input.Runtime.reviewOrdinal (attempt inventory).1 (attempt inventory).2 + 1) =
    OutstandingSource.History.currentAt epoch.source (Input.advance (attempt inventory).1 (attempt inventory).2).inputs
      ((Input.advance (attempt inventory).1 (attempt inventory).2).inputs.length + 2)
  congr 1
  change ((attempt inventory).1.inputs ++ [Input.emit (attempt inventory).1 (attempt inventory).2]).length + 2 + 1 = _
  rw [Input.inputs_exact]
  simp

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Programme.Completion.Runtime

import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Continuation

/-! A single source root consumes both its saved after-cut and its actual
review/repayment result. A generated later packet has its own such root. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Runtime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

inductive Projection where
  | saved | reviewed | continued

def savedOrdinal := inventory.inputs.length + 1
def reviewOrdinal := (staged inventory).inputs.length + 2

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (reviewInput inventory)).restructuringSource.toLedgerSource where
  Projection := Projection
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun projection {current} _ _ => match projection with
    | .saved => current = (ProgrammeHistory.visitAt (reviewInput inventory) (savedOrdinal inventory)).current → Inventory epoch
    | .reviewed => current = (ProgrammeHistory.visitAt (reviewInput inventory) (reviewOrdinal inventory)).current → Result (reviewed inventory)
    | .continued => current = (ProgrammeHistory.visitAt (reviewInput inventory) (reviewOrdinal inventory)).current → ContinuationDisposition inventory
  project := fun projection {_} _ _ => by
    cases projection with
    | saved => exact fun _own => inventory
    | reviewed => exact fun _own => cycleResult inventory
    | continued => exact fun _own => produceContinuation inventory

def root := (ProgrammeLiving.livingRoot (reviewInput inventory)).withProjectionCoface (projectionLaw inventory)

theorem root_is_its_own_source : (root inventory).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot (reviewInput inventory)).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (reviewInput inventory)) :=
  ⟨ProgrammeSource.V (reviewInput inventory),root inventory,ProgrammeHistory.temporalVisit (reviewInput inventory) ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (reviewInput inventory)) where
  State := Nat
  stateAt := stateAt inventory
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (reviewInput inventory)) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (reviewInput inventory) first).current =
        (ProgrammeHistory.visitAt (reviewInput inventory) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (reviewInput inventory) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : ProgrammeLiving.Projection)
  | joint (projection : Projection)

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (reviewInput inventory)) where
  process := process inventory
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous _ => ProgrammeLiving.projectionLaw (reviewInput inventory)
    | .joint _ => projectionLaw inventory
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (ProgrammeLiving.livingRoot (reviewInput inventory)).toAuthoritativeRoot.source (projectionLaw inventory)
    | joint projection =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (ProgrammeLiving.livingRoot (reviewInput inventory)).toAuthoritativeRoot.source (projectionLaw inventory)
  projectionAt := fun _ face => match face with
    | .previous previous => previous
    | .joint projection => projection

def activated (ordinal : Nat) : LivingRuntimeState (process inventory) := (facade inventory).seed.advance ordinal

def savedFromRoot : Inventory epoch :=
  (projectionLaw inventory).project .saved
    (ProgrammeSource.emitted (reviewInput inventory) (ProgrammeHistory.visitAt (reviewInput inventory) (savedOrdinal inventory)).current) () rfl

def resultFromRoot : Result (reviewed inventory) :=
  (projectionLaw inventory).project .reviewed
    (ProgrammeSource.emitted (reviewInput inventory) (ProgrammeHistory.visitAt (reviewInput inventory) (reviewOrdinal inventory)).current) () rfl

def continuationFromRoot : ContinuationDisposition inventory :=
  (projectionLaw inventory).project .continued
    (ProgrammeSource.emitted (reviewInput inventory) (ProgrammeHistory.visitAt (reviewInput inventory) (reviewOrdinal inventory)).current) () rfl

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Runtime

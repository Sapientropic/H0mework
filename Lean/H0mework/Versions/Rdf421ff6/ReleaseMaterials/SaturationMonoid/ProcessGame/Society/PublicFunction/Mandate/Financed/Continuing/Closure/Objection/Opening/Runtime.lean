import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Progress

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.OpeningRuntime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

open Objection.Followup Objection.Opening

variable {fuel : ℚ} (inventory : Joint.Inventory fuel)

noncomputable section

abbrev I := JointRuntime.I inventory (Opening.emit inventory)
abbrev previousRoot := JointRuntime.root inventory (Opening.emit inventory)
abbrev previousFacade := JointRuntime.facade inventory (Opening.emit inventory)

structure Disposition where
  private mk ::
  inherited : JointRuntime.Disposition inventory (Opening.emit inventory)
  inherited_exact : inherited = JointRuntime.generate inventory (Opening.emit inventory)
  opening : Opening.Receipt inventory
  opening_exact : opening = Opening.generate inventory
  nativeProgress : ∀ (row : Joint.Row inventory.cut) (inside : row ∈ inventory.frame.rows),
    Mandate.Response.Active inventory.cut.past.frame.raw → row.isPending = true →
    (row.2.history.state.current.history.map LifecycleEvent.kind ++ [.progressed]) <+:
      (inherited.carried row inside).thread.history.state.current.history.map LifecycleEvent.kind

def generate : Disposition inventory :=
  ⟨JointRuntime.generate inventory (Opening.emit inventory), rfl, Opening.generate inventory, rfl,
    Opening.every_carried_pending_row_keeps_its_source_progress inventory⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (I inventory)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (I inventory) (inventory.cut.depth + 2)).current → Disposition inventory
  project := fun _ {_} _ _ _own => generate inventory

def root := (previousRoot inventory).withProjectionCoface (projectionLaw inventory)

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I inventory)) :=
  ⟨ProgrammeSource.V (I inventory), root inventory, ProgrammeHistory.temporalVisit (I inventory) ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (I inventory)) where
  State := Nat
  stateAt := stateAt inventory
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I inventory)) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (I inventory) first).current =
        (ProgrammeHistory.visitAt (I inventory) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (I inventory) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : JointRuntime.Face)
  | opening

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (I inventory)) where
  process := process inventory
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (previousFacade inventory).componentAt (previousFacade inventory).seed previous
    | .opening => projectionLaw inventory
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact ((previousFacade inventory).installationAt (previousFacade inventory).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (previousRoot inventory).toAuthoritativeRoot.source (projectionLaw inventory))
    | opening =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (previousRoot inventory).toAuthoritativeRoot.source (projectionLaw inventory)
  projectionAt := fun _ face => match face with
    | .previous previous => (previousFacade inventory).projectionAt (previousFacade inventory).seed previous
    | .opening => ()

def activated (ordinal : Nat) : LivingRuntimeState (process inventory) :=
  (facade inventory).seed.advance ordinal

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.OpeningRuntime

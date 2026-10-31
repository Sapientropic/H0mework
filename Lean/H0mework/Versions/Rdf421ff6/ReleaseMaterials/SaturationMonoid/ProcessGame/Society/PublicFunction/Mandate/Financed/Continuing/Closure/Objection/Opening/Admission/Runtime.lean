import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Admission.Source

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.AdmissionRuntime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

open Objection.Followup Objection.Opening

variable {fuel : ℚ} (inventory : Joint.Inventory fuel)

noncomputable section

abbrev I := JointRuntime.I inventory (Admission.emit inventory)
abbrev previousRoot := JointRuntime.root inventory (Admission.emit inventory)
abbrev previousFacade := JointRuntime.facade inventory (Admission.emit inventory)

structure Disposition where
  private mk ::
  inherited : JointRuntime.Disposition inventory (Admission.emit inventory)
  inherited_exact : inherited = JointRuntime.generate inventory (Admission.emit inventory)
  opening : Admission.Receipt inventory
  opening_exact : opening = Admission.generate inventory
  native : Runtime.Disposition fuel (Admission.inputs inventory) inventory.cut.depth
  native_exact : native = Admission.native inventory
  new_admission : Admission.Quiet inventory.cut.past.frame.raw →
    (ready : Admission.Ready inventory.cut.past.frame.raw) →
    Admission.choose inventory.cut.past.frame.raw = some ready → (Admission.newGrants inventory).isEmpty = false
  releases : (birth : Fin (inventory.cut.depth + 1)) →
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel (branchInputs inventory.cut (Admission.emit inventory)) birth.val)
      (Runtime.mandateWordAt fuel (branchInputs inventory.cut (Admission.emit inventory)) birth.val)) →
    (index : Fin (Admission.inputItems inventory).length) → Option (Admission.ReleaseAt inventory birth grant index)
  releases_exact : ∀ birth grant index, releases birth grant index = Admission.readRelease inventory birth grant index
  nativeProgress : ∀ (row : Joint.Row inventory.cut) (inside : row ∈ inventory.frame.rows),
    Mandate.Response.Active inventory.cut.past.frame.raw → row.isPending = true →
    (row.2.history.state.current.history.map LifecycleEvent.kind ++ [.progressed]) <+:
      (inherited.carried row inside).thread.history.state.current.history.map LifecycleEvent.kind

def generate : Disposition inventory :=
  ⟨JointRuntime.generate inventory (Admission.emit inventory), rfl, Admission.generate inventory, rfl, Admission.native inventory, rfl, Admission.selected_pair_creates_a_new_native_grant inventory, Admission.readRelease inventory, fun _ _ _ => rfl,
    Admission.every_active_pending_row_keeps_actual_progress inventory⟩

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
  | admission

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (I inventory)) where
  process := process inventory
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (previousFacade inventory).componentAt (previousFacade inventory).seed previous
    | .admission => projectionLaw inventory
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact ((previousFacade inventory).installationAt (previousFacade inventory).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (previousRoot inventory).toAuthoritativeRoot.source (projectionLaw inventory))
    | admission =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (previousRoot inventory).toAuthoritativeRoot.source (projectionLaw inventory)
  projectionAt := fun _ face => match face with
    | .previous previous => (previousFacade inventory).projectionAt (previousFacade inventory).seed previous
    | .admission => ()

def activated (ordinal : Nat) : LivingRuntimeState (process inventory) :=
  (facade inventory).seed.advance ordinal

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.AdmissionRuntime

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Renewal.Nonclosure

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.RenewalRuntime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

open Objection.Followup Objection.Opening

variable {fuel : ℚ} (inventory : Joint.Inventory fuel)

noncomputable section

abbrev I := JointRuntime.I inventory (Renewal.emit inventory)
abbrev previousRoot := JointRuntime.root inventory (Renewal.emit inventory)
abbrev previousFacade := JointRuntime.facade inventory (Renewal.emit inventory)

structure Disposition where
  private mk ::
  inherited : JointRuntime.Disposition inventory (Renewal.emit inventory)
  inherited_exact : inherited = JointRuntime.generate inventory (Renewal.emit inventory)
  renewal : Renewal.Receipt inventory
  renewal_exact : renewal = Renewal.generate inventory
  native : Runtime.Disposition fuel (Renewal.inputs inventory) inventory.cut.depth
  native_exact : native = Renewal.native inventory
  nativeProgress : ∀ (row : Joint.Row inventory.cut) (inside : row ∈ inventory.frame.rows),
    Mandate.Response.Active inventory.cut.past.frame.raw → row.isPending = true →
    (row.2.history.state.current.history.map LifecycleEvent.kind ++ [.progressed]) <+:
      (inherited.carried row inside).thread.history.state.current.history.map LifecycleEvent.kind
  nativeGrowth : Mandate.Response.Active inventory.cut.past.frame.raw →
    Joint.volume inherited.before.rows < Joint.volume inherited.after.rows
  legalNonclosure : Mandate.Response.Active inventory.cut.past.frame.raw → ¬ Renewal.LegalNativeSink inventory

def generate : Disposition inventory :=
  ⟨JointRuntime.generate inventory (Renewal.emit inventory), rfl, Renewal.generate inventory, rfl, Renewal.native inventory, rfl,
    Renewal.every_active_pending_row_keeps_actual_progress inventory, fun active => by
      change Joint.volume (Joint.before inventory (Renewal.emit inventory)).rows <
        Joint.volume (Renewal.advance inventory).frame.rows
      rw [Joint.before_volume]
      exact Renewal.every_active_emission_strictly_grows_the_native_ledger inventory active,
    Renewal.no_active_actual_cut_is_a_legal_native_sink inventory⟩

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
  | renewal

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (I inventory)) where
  process := process inventory
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (previousFacade inventory).componentAt (previousFacade inventory).seed previous
    | .renewal => projectionLaw inventory
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact ((previousFacade inventory).installationAt (previousFacade inventory).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (previousRoot inventory).toAuthoritativeRoot.source (projectionLaw inventory))
    | renewal =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (previousRoot inventory).toAuthoritativeRoot.source (projectionLaw inventory)
  projectionAt := fun _ face => match face with
    | .previous previous => (previousFacade inventory).projectionAt (previousFacade inventory).seed previous
    | .renewal => ()

def activated (ordinal : Nat) : LivingRuntimeState (process inventory) :=
  (facade inventory).seed.advance ordinal

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.RenewalRuntime

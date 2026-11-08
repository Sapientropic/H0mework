import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Epoch

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Runtime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Followup
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (authority : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : Pending.Joint.Inventory authority originInputs)
noncomputable section

abbrev I := Future.I authority inventory .revision
abbrev previousRoot := Future.Runtime.root authority inventory .revision
abbrev previousFacade := Future.Runtime.facade authority inventory .revision

structure Disposition where
  private mk ::
  inherited : Future.Runtime.Disposition authority inventory .revision
  inherited_exact : inherited = Future.Runtime.generate authority inventory .revision
  handoff : Handoff.Result authority inventory
  handoff_exact : handoff = Handoff.generate authority inventory

def generate : Disposition authority inventory :=
  ⟨Future.Runtime.generate authority inventory .revision,rfl,Handoff.generate authority inventory,rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (I authority inventory)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (I authority inventory) ((Future.advance authority inventory .revision).inputs.length + 2)).current → Disposition authority inventory
  project := fun _ {_} _ _ _own => generate authority inventory

def root := (previousRoot authority inventory).withProjectionCoface (projectionLaw authority inventory)

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I authority inventory)) :=
  ⟨ProgrammeSource.V (I authority inventory), root authority inventory, ProgrammeHistory.temporalVisit (I authority inventory) ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (I authority inventory)) where
  State := Nat
  stateAt := stateAt authority inventory
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I authority inventory)) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (I authority inventory) first).current =
        (ProgrammeHistory.visitAt (I authority inventory) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (I authority inventory) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : Future.Runtime.Face)
  | revision

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (I authority inventory)) where
  process := process authority inventory
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (previousFacade authority inventory).componentAt (previousFacade authority inventory).seed previous
    | .revision => projectionLaw authority inventory
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact ((previousFacade authority inventory).installationAt (previousFacade authority inventory).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (previousRoot authority inventory).toAuthoritativeRoot.source (projectionLaw authority inventory))
    | revision =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (previousRoot authority inventory).toAuthoritativeRoot.source (projectionLaw authority inventory)
  projectionAt := fun _ face => match face with
    | .previous previous => (previousFacade authority inventory).projectionAt (previousFacade authority inventory).seed previous
    | .revision => ()

def activated (ordinal : Nat) : LivingRuntimeState (process authority inventory) :=
  (facade authority inventory).seed.advance ordinal


end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Runtime

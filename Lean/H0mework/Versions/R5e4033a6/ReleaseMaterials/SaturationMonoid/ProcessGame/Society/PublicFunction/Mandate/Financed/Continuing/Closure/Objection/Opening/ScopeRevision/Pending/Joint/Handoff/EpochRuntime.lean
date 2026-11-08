import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Runtime

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.EpochRuntime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Followup
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (authority : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : Pending.Joint.Inventory authority originInputs)
  (fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs)
noncomputable section

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (Handoff.I fresh)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => current = (ProgrammeHistory.visitAt (Handoff.I fresh) 3).current → Handoff.EpochDisposition authority inventory fresh
  project := fun _ {_} _ _ _own => Handoff.generateEpoch authority inventory fresh

def root := (ProgrammeLiving.livingRoot (Handoff.I fresh)).withProjectionCoface (projectionLaw authority inventory fresh)

theorem root_is_its_own_emitting_source : (root authority inventory fresh).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot (Handoff.I fresh)).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Handoff.I fresh)) :=
  ⟨ProgrammeSource.V (Handoff.I fresh), root authority inventory fresh, ProgrammeHistory.temporalVisit (Handoff.I fresh) ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (Handoff.I fresh)) where
  State := Nat
  stateAt := stateAt authority inventory fresh
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Handoff.I fresh)) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (Handoff.I fresh) first).current =
        (ProgrammeHistory.visitAt (Handoff.I fresh) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (Handoff.I fresh) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : ProgrammeLiving.Projection)
  | responsibilities

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (Handoff.I fresh)) where
  process := process authority inventory fresh
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous _ => ProgrammeLiving.projectionLaw (Handoff.I fresh)
    | .responsibilities => projectionLaw authority inventory fresh
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (ProgrammeLiving.livingRoot (Handoff.I fresh)).toAuthoritativeRoot.source (projectionLaw authority inventory fresh)
    | responsibilities =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (ProgrammeLiving.livingRoot (Handoff.I fresh)).toAuthoritativeRoot.source (projectionLaw authority inventory fresh)
  projectionAt := fun _ face => match face with
    | .previous previous => previous
    | .responsibilities => ()

def activated (ordinal : Nat) : LivingRuntimeState (process authority inventory fresh) :=
  (facade authority inventory fresh).seed.advance ordinal


end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.EpochRuntime

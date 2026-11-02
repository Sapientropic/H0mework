import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeEpochRuntime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Objection.Followup Objection.Opening
variable {fuel : ℚ} {inventory : Joint.Inventory fuel} (ready : ScopeRevision.Ready inventory)
noncomputable section

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (ScopeRevision.epochInput ready)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => current = (ProgrammeHistory.visitAt (ScopeRevision.epochInput ready) 2).current → ScopeRevision.EpochDisposition ready
  project := fun _ {_} _ _ _own => ScopeRevision.generateEpoch ready

def root := (ProgrammeLiving.livingRoot (ScopeRevision.epochInput ready)).withProjectionCoface (projectionLaw ready)

theorem root_is_its_own_emitting_source : (root ready).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot (ScopeRevision.epochInput ready)).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (ScopeRevision.epochInput ready)) :=
  ⟨ProgrammeSource.V (ScopeRevision.epochInput ready), root ready, ProgrammeHistory.temporalVisit (ScopeRevision.epochInput ready) ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (ScopeRevision.epochInput ready)) where
  State := Nat
  stateAt := stateAt ready
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (ScopeRevision.epochInput ready)) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (ScopeRevision.epochInput ready) first).current =
        (ProgrammeHistory.visitAt (ScopeRevision.epochInput ready) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (ScopeRevision.epochInput ready) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : ProgrammeLiving.Projection)
  | responsibilities

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (ScopeRevision.epochInput ready)) where
  process := process ready
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous _ => ProgrammeLiving.projectionLaw (ScopeRevision.epochInput ready)
    | .responsibilities => projectionLaw ready
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (ProgrammeLiving.livingRoot (ScopeRevision.epochInput ready)).toAuthoritativeRoot.source (projectionLaw ready)
    | responsibilities =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (ProgrammeLiving.livingRoot (ScopeRevision.epochInput ready)).toAuthoritativeRoot.source (projectionLaw ready)
  projectionAt := fun _ face => match face with
    | .previous previous => previous
    | .responsibilities => ()

def activated (ordinal : Nat) : LivingRuntimeState (process ready) :=
  (facade ready).seed.advance ordinal

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeEpochRuntime

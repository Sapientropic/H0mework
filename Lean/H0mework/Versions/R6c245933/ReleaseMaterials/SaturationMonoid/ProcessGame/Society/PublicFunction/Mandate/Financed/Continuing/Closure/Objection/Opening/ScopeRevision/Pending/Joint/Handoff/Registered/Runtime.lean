import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Runtime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Followup
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (authority : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : Pending.Joint.Inventory authority originInputs)
  (fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs)
  (word : List Action)
noncomputable section

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (Registered.input authority inventory fresh word)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => current = (ProgrammeHistory.visitAt (Registered.input authority inventory fresh word) 3).current → Registered.Receipt authority inventory fresh word
  project := fun _ {_} _ _ _own => Registered.produce authority inventory fresh word

def root := (ProgrammeLiving.livingRoot (Registered.input authority inventory fresh word)).withProjectionCoface (projectionLaw authority inventory fresh word)

theorem root_is_its_own_emitting_source : (root authority inventory fresh word).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot (Registered.input authority inventory fresh word)).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Registered.input authority inventory fresh word)) :=
  ⟨ProgrammeSource.V (Registered.input authority inventory fresh word), root authority inventory fresh word, ProgrammeHistory.temporalVisit (Registered.input authority inventory fresh word) ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (Registered.input authority inventory fresh word)) where
  State := Nat
  stateAt := stateAt authority inventory fresh word
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (Registered.input authority inventory fresh word)) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (Registered.input authority inventory fresh word) first).current =
        (ProgrammeHistory.visitAt (Registered.input authority inventory fresh word) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (Registered.input authority inventory fresh word) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : ProgrammeLiving.Projection)
  | registeredInput

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (Registered.input authority inventory fresh word)) where
  process := process authority inventory fresh word
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous _ => ProgrammeLiving.projectionLaw (Registered.input authority inventory fresh word)
    | .registeredInput => projectionLaw authority inventory fresh word
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (ProgrammeLiving.livingRoot (Registered.input authority inventory fresh word)).toAuthoritativeRoot.source (projectionLaw authority inventory fresh word)
    | registeredInput =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (ProgrammeLiving.livingRoot (Registered.input authority inventory fresh word)).toAuthoritativeRoot.source (projectionLaw authority inventory fresh word)
  projectionAt := fun _ face => match face with
    | .previous previous => previous
    | .registeredInput => ()

def activated (ordinal : Nat) : LivingRuntimeState (process authority inventory fresh word) :=
  (facade authority inventory fresh word).seed.advance ordinal


end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Runtime

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Runtime
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (authority : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : Pending.Joint.Inventory authority originInputs)
  (fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs) (word : List Action)
def fromRoot : Registered.Receipt authority inventory fresh word :=
  (projectionLaw authority inventory fresh word).project ()
    (ProgrammeSource.emitted (Registered.input authority inventory fresh word)
      (ProgrammeHistory.visitAt (Registered.input authority inventory fresh word) 3).current) () rfl
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Runtime

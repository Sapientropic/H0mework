import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Response.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Cuts

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.FollowupRuntime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {fuel : ℚ} {inputs : List (List Action)} (cut : Cut fuel inputs)

noncomputable section

abbrev I := ResponseRuntime.I cut
abbrev previousRoot := ResponseRuntime.root cut
abbrev previousFacade := ResponseRuntime.facade cut

structure Transfer (original : Response.Pending cut) where
  private mk ::
  before : Followup.History fuel (Response.nextInputs cut) (Response.transportedClaim cut original)
  before_exact : before = Followup.History.inherit fuel (Response.nextInputs cut) (Response.newBefore cut original)
  after : Followup.History fuel (Response.nextInputs cut) (Response.transportedClaim cut original)
  after_exact : after = Followup.continueFrom before (cut.depth + 2) 1
  crossing : (Followup.process fuel (Response.nextInputs cut) (Response.transportedClaim cut original)).Run
    before.state.current after.state.current

def transfer (original : Response.Pending cut) : Transfer cut original :=
  let before := Followup.History.inherit fuel (Response.nextInputs cut) (Response.newBefore cut original)
  ⟨before, rfl, Followup.continueFrom before (cut.depth + 2) 1, rfl,
    Followup.continuationRun before (cut.depth + 2) 1⟩

structure Disposition where
  private mk ::
  inherited : ResponseRuntime.Disposition cut
  inherited_exact : inherited = ResponseRuntime.generate cut
  transfers : (original : Response.Pending cut) → Transfer cut original
  transfers_exact : ∀ original, transfers original = transfer cut original

def generate : Disposition cut :=
  ⟨ResponseRuntime.generate cut, rfl, transfer cut, fun _ => rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (I cut)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (I cut) (cut.depth + 2)).current → Disposition cut
  project := fun _ {_} _ _ _own => generate cut

def root := (previousRoot cut).withProjectionCoface (projectionLaw cut)

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I cut)) :=
  ⟨ProgrammeSource.V (I cut), root cut, ProgrammeHistory.temporalVisit (I cut) ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (I cut)) where
  State := Nat
  stateAt := stateAt cut
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I cut)) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (I cut) first).current =
        (ProgrammeHistory.visitAt (I cut) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (I cut) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : ResponseRuntime.Face)
  | followup

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (I cut)) where
  process := process cut
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (previousFacade cut).componentAt (previousFacade cut).seed previous
    | .followup => projectionLaw cut
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact ((previousFacade cut).installationAt (previousFacade cut).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (previousRoot cut).toAuthoritativeRoot.source (projectionLaw cut))
    | followup =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (previousRoot cut).toAuthoritativeRoot.source (projectionLaw cut)
  projectionAt := fun _ face => match face with
    | .previous previous => (previousFacade cut).projectionAt (previousFacade cut).seed previous
    | .followup => ()

def activated (ordinal : Nat) : LivingRuntimeState (process cut) :=
  (facade cut).seed.advance ordinal

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.FollowupRuntime

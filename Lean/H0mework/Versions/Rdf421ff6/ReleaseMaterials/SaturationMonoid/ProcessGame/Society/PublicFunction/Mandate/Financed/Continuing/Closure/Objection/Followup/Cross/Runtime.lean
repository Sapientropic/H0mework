import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Cross.Continuation

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.CrossRuntime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {fuel : ℚ} {originInputs : List (List Action)} {original : Claim fuel originInputs} (stage : Cross.Stage original)

noncomputable section

abbrev I := TransportRuntime.I stage.cut (Cross.emit stage)
abbrev previousRoot := TransportRuntime.root stage.cut (Cross.emit stage)
abbrev previousFacade := TransportRuntime.facade stage.cut (Cross.emit stage)

structure Disposition where
  private mk ::
  inherited : TransportRuntime.Disposition stage.cut (Cross.emit stage)
  inherited_exact : inherited = TransportRuntime.generate stage.cut (Cross.emit stage)
  before : Cross.History original (Cross.advance stage).inputs
  before_exact : before = Cross.before stage (Cross.emit stage)
  original_state : before.state = stage.history.state
  after : Cross.History original (Cross.advance stage).inputs
  after_exact : after = (Cross.advance stage).history
  crossing : (Cross.process original).Run stage.history.state.current after.state.current
  complete : (Cross.process original).Run (ResponsibilityState.empty (V fuel originInputs)) after.state.current

def generate : Disposition stage :=
  ⟨TransportRuntime.generate stage.cut (Cross.emit stage), rfl,
    Cross.before stage (Cross.emit stage), rfl,
    Cross.transport_preserves_the_entire_generated_state stage.cut (Cross.emit stage) stage.history stage.within,
    (Cross.advance stage).history, rfl, Cross.crossing stage (Cross.emit stage), (Cross.advance stage).history.state.generated⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (I stage)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (I stage) (stage.cut.depth + 2)).current → Disposition stage
  project := fun _ {_} _ _ _own => generate stage

def root := (previousRoot stage).withProjectionCoface (projectionLaw stage)

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I stage)) :=
  ⟨ProgrammeSource.V (I stage), root stage, ProgrammeHistory.temporalVisit (I stage) ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (I stage)) where
  State := Nat
  stateAt := stateAt stage
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I stage)) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (I stage) first).current =
        (ProgrammeHistory.visitAt (I stage) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (I stage) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : TransportRuntime.Face)
  | followup

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (I stage)) where
  process := process stage
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (previousFacade stage).componentAt (previousFacade stage).seed previous
    | .followup => projectionLaw stage
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact ((previousFacade stage).installationAt (previousFacade stage).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (previousRoot stage).toAuthoritativeRoot.source (projectionLaw stage))
    | followup =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (previousRoot stage).toAuthoritativeRoot.source (projectionLaw stage)
  projectionAt := fun _ face => match face with
    | .previous previous => (previousFacade stage).projectionAt (previousFacade stage).seed previous
    | .followup => ()

def activated (ordinal : Nat) : LivingRuntimeState (process stage) :=
  (facade stage).seed.advance ordinal

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.CrossRuntime

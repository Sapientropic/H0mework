import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Future.Source
import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Runtime

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.FutureRuntime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {fuel : ℚ} {inputs : List (List Action)}
  (cut : Cut fuel inputs) (word : List Action)

abbrev I := input fuel (branchInputs cut word)
abbrev previousRoot := Closure.Runtime.root fuel (branchInputs cut word)
abbrev previousFacade := Closure.Runtime.facade fuel (branchInputs cut word)

noncomputable section

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (I cut word)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (I cut word) (cut.depth + 2)).current → FutureAttempt cut word
  project := fun _ {_} _ _ _own => attemptFutureInput cut word

def root := (previousRoot cut word).withProjectionCoface (projectionLaw cut word)

theorem root_is_the_new_actual_emitter : (root cut word).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot (I cut word)).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I cut word)) :=
  ⟨ProgrammeSource.V (I cut word), root cut word, ProgrammeHistory.temporalVisit (I cut word) ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (I cut word)) where
  State := Nat
  stateAt := stateAt cut word
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I cut word)) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (I cut word) first).current =
        (ProgrammeHistory.visitAt (I cut word) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (I cut word) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : Closure.Runtime.Face)
  | inputTransport

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (I cut word)) where
  process := process cut word
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (previousFacade cut word).componentAt (previousFacade cut word).seed previous
    | .inputTransport => projectionLaw cut word
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact ((previousFacade cut word).installationAt (previousFacade cut word).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (previousRoot cut word).toAuthoritativeRoot.source (projectionLaw cut word))
    | inputTransport =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (previousRoot cut word).toAuthoritativeRoot.source (projectionLaw cut word)
  projectionAt := fun _ face => match face with
    | .previous previous => (previousFacade cut word).projectionAt (previousFacade cut word).seed previous
    | .inputTransport => ()

def activated (ordinal : Nat) : LivingRuntimeState (process cut word) :=
  (facade cut word).seed.advance ordinal

theorem current_payload_is_the_actual_input_attempt :
    (projectionLaw cut word).project ()
      (ProgrammeSource.emitted (I cut word) (ProgrammeHistory.visitAt (I cut word) (cut.depth + 2)).current) () rfl =
      attemptFutureInput cut word := rfl

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.FutureRuntime

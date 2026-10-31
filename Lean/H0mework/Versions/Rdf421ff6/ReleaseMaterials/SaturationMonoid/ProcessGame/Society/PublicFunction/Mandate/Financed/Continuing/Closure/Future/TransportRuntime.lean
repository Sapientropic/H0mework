import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Future.FinanceTransport
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Future.MandateTransport
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Future.Runtime

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.TransportRuntime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {fuel : ℚ} {inputs : List (List Action)} (cut : Cut fuel inputs) (word : List Action)

structure Disposition where
  private mk ::
  response : FutureAttempt cut word
  response_exact : response = attemptFutureInput cut word
  mandates : (birth : Fin (cut.depth + 1)) →
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel inputs birth.val)
      (Runtime.mandateWordAt fuel inputs birth.val)) → MandateTransport cut word birth grant
  mandates_exact : ∀ birth grant, mandates birth grant = transportMandate cut word birth grant
  finance : (birth : Fin (cut.depth + 1)) →
    (index : Fin (financialItems fuel inputs (birth.val + 1)).length) →
      Option (Sigma fun original : Financial.IssuedClaim (input fuel inputs) => IssueTransport cut word birth index original)
  finance_exact : ∀ birth index, finance birth index = attemptIssueTransport cut word birth index

noncomputable section

def generate : Disposition cut word :=
  ⟨attemptFutureInput cut word, rfl, transportMandate cut word, fun _ _ => rfl,
    attemptIssueTransport cut word, fun _ _ => rfl⟩

abbrev I := FutureRuntime.I cut word
abbrev previousRoot := FutureRuntime.root cut word
abbrev previousFacade := FutureRuntime.facade cut word

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (I cut word)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (I cut word) (cut.depth + 2)).current → Disposition cut word
  project := fun _ {_} _ _ _own => generate cut word

def root := (previousRoot cut word).withProjectionCoface (projectionLaw cut word)

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
  | previous (face : FutureRuntime.Face)
  | responsibilityTransport

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (I cut word)) where
  process := process cut word
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (previousFacade cut word).componentAt (previousFacade cut word).seed previous
    | .responsibilityTransport => projectionLaw cut word
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact ((previousFacade cut word).installationAt (previousFacade cut word).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (previousRoot cut word).toAuthoritativeRoot.source (projectionLaw cut word))
    | responsibilityTransport =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (previousRoot cut word).toAuthoritativeRoot.source (projectionLaw cut word)
  projectionAt := fun _ face => match face with
    | .previous previous => (previousFacade cut word).projectionAt (previousFacade cut word).seed previous
    | .responsibilityTransport => ()

def activated (ordinal : Nat) : LivingRuntimeState (process cut word) :=
  (facade cut word).seed.advance ordinal

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.TransportRuntime
